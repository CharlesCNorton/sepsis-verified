(******************************************************************************)
(*                                                                            *)
(*                 Sepsis Protocol: Total Triage Decision Logic               *)
(*                                                                            *)
(*     Formalizes qSOFA/SOFA-style scoring on vital signs and labs, defines   *)
(*     a stepwise escalation plan (fluids, antibiotics, pressors, ICU), and   *)
(*     proves determinism, monotonicity, and escalation guarantees.            *)
(*                                                                            *)
(*     "Medicine is a science of uncertainty and an art of probability."      *)
(*     - William Osler                                                         *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import Bool Arith Lia.

Set Implicit Arguments.

(** Vital signs and labs, discretized. Units: tenths for temp/bilirubin/creatinine, MAP/SBP mmHg, FiO2 as percent (1-100). *)
Record Vitals := {
  temp10    : nat;   (* tenths of °C, e.g., 383 = 38.3°C *)
  hr        : nat;   (* bpm *)
  rr        : nat;   (* breaths/min *)
  sbp       : nat;   (* systolic BP mmHg *)
  map_mm    : nat;   (* mean arterial pressure mmHg *)
  lact10    : nat;   (* lactate, mmol/L * 10 *)
  gcs       : nat;   (* Glasgow Coma Scale, 3..15 *)
  platelets : nat;   (* count x10^3/µL *)
  bilir10   : nat;   (* bilirubin mg/dL * 10 *)
  creat10   : nat;   (* creatinine mg/dL * 10 *)
  urine_ml_hr : nat; (* urine output mL/hour *)
  pao2      : nat;   (* PaO2 mmHg *)
  fio2_pct  : nat;   (* FiO2 percent, clipped to [1,100] *)
  infection : bool   (* suspected/confirmed infection *)
}.

Record Therapy := {
  fluids_on       : bool;
  antibiotics_on  : bool;
  pressor_low_on  : bool;
  pressor_high_on : bool;
  icu_transfer    : bool
}.

Definition init_therapy : Therapy :=
  {| fluids_on := false; antibiotics_on := false; pressor_low_on := false; pressor_high_on := false; icu_transfer := false |}.

Record State := {
  vit : Vitals;
  th  : Therapy
}.

(** Helpers *)
Definition ge_bool x y := Nat.leb y x.
Definition le_bool := Nat.leb.
Definition max1 (n:nat) := if n =? 0 then 1 else n.

(** Tiered scoring helpers (0/1/2) and (0/2) *)
Definition tier_ge (x hi lo : nat) : nat :=
  if ge_bool x hi then 2 else if ge_bool x lo then 1 else 0.

Definition tier_map (m : nat) : nat :=
  if le_bool m 65 then 2 else 0.

Lemma tier_ge_mono : forall x y hi lo, x <= y -> tier_ge x hi lo <= tier_ge y hi lo.
Proof.
  intros x y hi lo Hxy.
  unfold tier_ge, ge_bool.
  destruct (Nat.leb lo x) eqn:Hxlo, (Nat.leb hi x) eqn:Hxhi;
  destruct (Nat.leb lo y) eqn:Hylo, (Nat.leb hi y) eqn:Hyhi; try lia.
  all: try (apply Nat.leb_le in Hxhi; apply Nat.leb_nle in Hyhi; lia).
  all: try (apply Nat.leb_le in Hxlo; apply Nat.leb_nle in Hylo; lia).
Qed.

Lemma tier_map_mono : forall m1 m2, m2 <= m1 -> tier_map m2 >= tier_map m1.
Proof.
  intros m1 m2 Hle; unfold tier_map.
  destruct (le_bool m1 65) eqn:Hm1.
  - destruct (le_bool m2 65) eqn:Hm2.
    + lia.
    + apply Nat.leb_le in Hm1. apply Nat.leb_gt in Hm2. lia.
  - destruct (le_bool m2 65) eqn:Hm2.
    + apply Nat.leb_gt in Hm1. apply Nat.leb_le in Hm2. lia.
    + lia.
Qed.

(** SOFA organ subscores (0..4), simplified) *)
Definition resp_bucket (ratio:nat) : nat :=
  if ratio <=? 100 then 4
  else if ratio <=? 200 then 3
  else if ratio <=? 300 then 2
  else if ratio <=? 400 then 1
  else 0.

Definition resp_score (v:Vitals) : nat :=
  let fio2 := max1 (fio2_pct v) in
  resp_bucket ((pao2 v * 100) / fio2).

Definition coag_score (v:Vitals) : nat :=
  let p := platelets v in
  if p <? 20 then 4
  else if p <? 50 then 3
  else if p <? 100 then 2
  else if p <? 150 then 1
  else 0.

Definition liver_score (v:Vitals) : nat :=
  let b := bilir10 v in
  if b <? 12 then 0
  else if b <? 20 then 1
  else if b <? 60 then 2
  else if b <? 120 then 3
  else 4.

Definition cns_score (v:Vitals) : nat :=
  let g := gcs v in
  if g <? 6 then 4
  else if g <? 10 then 3
  else if g <? 13 then 2
  else if g <? 15 then 1
  else 0.

Definition creat_score (c:nat) : nat :=
  if ge_bool c 53 then 4
  else if ge_bool c 34 then 3
  else if ge_bool c 21 then 2
  else if ge_bool c 11 then 1
  else 0.

Definition urine_score (u:nat) : nat :=
  if u <=? 20 then 4
  else if u <=? 50 then 3
  else if u <=? 120 then 2
  else if u <=? 200 then 1
  else 0.

Definition renal_score (v:Vitals) : nat :=
  Nat.max (creat_score (creat10 v)) (urine_score (urine_ml_hr v)).

Definition cv_score (v:Vitals) (t:Therapy) : nat :=
  if pressor_high_on t then 4
  else if pressor_low_on t then 3
  else if map_mm v <? 70 then 1
  else 0.

Definition sofa (s:State) : nat :=
  resp_score (vit s) +
  coag_score (vit s) +
  liver_score (vit s) +
  cns_score (vit s) +
  renal_score (vit s) +
  cv_score (vit s) (th s).

(** qSOFA (0..3), using RR>=22, SBP<=100, GCS<15 *)
Definition qsofa (v:Vitals) : nat :=
  (if ge_bool (rr v) 22 then 1 else 0) +
  (if sbp v <=? 100 then 1 else 0) +
  (if gcs v <? 15 then 1 else 0).

(** NEWS-like quick score (subset) *)
Definition news_rr (v:Vitals) : nat :=
  if ge_bool (rr v) 30 then 3 else if ge_bool (rr v) 25 then 2 else if ge_bool (rr v) 21 then 1 else if rr v <=? 8 then 3 else 0.

Definition news_hr (v:Vitals) : nat :=
  if ge_bool (hr v) 130 then 3 else if ge_bool (hr v) 111 then 2 else if ge_bool (hr v) 91 then 1 else if hr v <=? 40 then 2 else 0.

Definition news_temp (v:Vitals) : nat :=
  if ge_bool (temp10 v) 400 then 2 else if ge_bool (temp10 v) 391 then 1 else if temp10 v <=? 351 then 1 else 0.

Definition news_sbp (v:Vitals) : nat :=
  if sbp v <=? 90 then 3 else if sbp v <=? 100 then 2 else if sbp v <=? 110 then 1 else 0.

Definition news_gcs (v:Vitals) : nat := if gcs v <? 15 then 3 else 0.

Definition news (v:Vitals) : nat :=
  news_rr v + news_hr v + news_temp v + news_sbp v + news_gcs v.

(** Sepsis / shock predicates *)
Definition sepsis (s:State) : bool :=
  infection (vit s) && ge_bool (sofa s) 2.

Definition septic_shock (s:State) : bool :=
  infection (vit s) &&
  ge_bool (sofa s) 2 &&
  (map_mm (vit s) <=? 65) &&
  (ge_bool (lact10 (vit s)) 20).

(** Plan/decision: deterministic escalation policy *)
Record Plan := {
  p_fluids      : bool;
  p_antibiotics : bool;
  p_pressor_lo  : bool;
  p_pressor_hi  : bool;
  p_icu         : bool
}.

Definition plan_false : Plan :=
  {| p_fluids := false; p_antibiotics := false; p_pressor_lo := false; p_pressor_hi := false; p_icu := false |}.

Definition decide_plan (s:State) : Plan :=
  let v := vit s in
  let base := plan_false in
  let flu := (map_mm v <=? 65) || (ge_bool (lact10 v) 20) || fluids_on (th s) in
  let abx := infection v || antibiotics_on (th s) in
  let plo := (map_mm v <=? 65) && (fluids_on (th s) || flu) || pressor_low_on (th s) in
  let phi := (map_mm v <=? 60) && (plo || pressor_low_on (th s)) || pressor_high_on (th s) in
  let icu := (map_mm v <=? 60) && (phi || pressor_high_on (th s)) in
  {| p_fluids := flu;
     p_antibiotics := abx;
     p_pressor_lo := plo;
     p_pressor_hi := phi;
     p_icu := icu |}.

(** Determinism / totality *)
Lemma decide_plan_total : forall s, exists p, decide_plan s = p.
Proof. intros; now eexists. Qed.

Lemma decide_plan_deterministic : forall s p1 p2, decide_plan s = p1 -> decide_plan s = p2 -> p1 = p2.
Proof. intros; congruence. Qed.

(** Monotonicity of SOFA with worsening inputs *)
Definition worse_or_equal (v w : Vitals) : Prop :=
  temp10 w >= temp10 v /\
  hr w >= hr v /\
  rr w >= rr v /\
  sbp w <= sbp v /\
  map_mm w <= map_mm v /\
  lact10 w >= lact10 v /\
  gcs w <= gcs v /\
  platelets w <= platelets v /\
  bilir10 w >= bilir10 v /\
  creat10 w >= creat10 v /\
  urine_ml_hr w <= urine_ml_hr v /\
  pao2 w <= pao2 v /\
  fio2_pct w >= fio2_pct v.

Lemma resp_bucket_mono : forall r1 r2, r2 <= r1 -> resp_bucket r2 >= resp_bucket r1.
Proof.
  intros r1 r2 Hr.
  unfold resp_bucket.
  destruct (le_lt_dec r1 100) as [H1|H1].
  - assert (E1 : r1 <=? 100 = true) by (apply Nat.leb_le; lia).
    assert (E2 : r2 <=? 100 = true) by (apply Nat.leb_le; lia).
    rewrite E1, E2. lia.
  - destruct (le_lt_dec r1 200) as [H2|H2].
    + assert (E100 : r1 <=? 100 = false) by (apply Nat.leb_gt; lia).
      assert (E200 : r1 <=? 200 = true) by (apply Nat.leb_le; lia).
      destruct (le_lt_dec r2 100) as [Hr2a|Hr2a].
      * assert (E2 : r2 <=? 100 = true) by (apply Nat.leb_le; lia).
        rewrite E100, E200, E2. lia.
      * assert (E2_100 : r2 <=? 100 = false) by (apply Nat.leb_gt; lia).
        assert (E2_200 : r2 <=? 200 = true) by (apply Nat.leb_le; lia).
        rewrite E100, E200, E2_100, E2_200. lia.
    + destruct (le_lt_dec r1 300) as [H3|H3].
      * assert (E100 : r1 <=? 100 = false) by (apply Nat.leb_gt; lia).
        assert (E200 : r1 <=? 200 = false) by (apply Nat.leb_gt; lia).
        assert (E300 : r1 <=? 300 = true) by (apply Nat.leb_le; lia).
        destruct (le_lt_dec r2 200) as [Hr2b|Hr2b].
        -- destruct (le_lt_dec r2 100) as [Hr2c|Hr2c].
           ++ assert (E2_100 : r2 <=? 100 = true) by (apply Nat.leb_le; lia).
              rewrite E100, E200, E300, E2_100. lia.
           ++ assert (E2_100 : r2 <=? 100 = false) by (apply Nat.leb_gt; lia).
              assert (E2_200 : r2 <=? 200 = true) by (apply Nat.leb_le; lia).
              rewrite E100, E200, E300, E2_100, E2_200. lia.
        -- assert (E2_100 : r2 <=? 100 = false) by (apply Nat.leb_gt; lia).
           assert (E2_200 : r2 <=? 200 = false) by (apply Nat.leb_gt; lia).
           assert (E2_300 : r2 <=? 300 = true) by (apply Nat.leb_le; lia).
           rewrite E100, E200, E300, E2_100, E2_200, E2_300. lia.
      * destruct (le_lt_dec r1 400) as [H4|H4].
        -- assert (E100 : r1 <=? 100 = false) by (apply Nat.leb_gt; lia).
           assert (E200 : r1 <=? 200 = false) by (apply Nat.leb_gt; lia).
           assert (E300 : r1 <=? 300 = false) by (apply Nat.leb_gt; lia).
           assert (E400 : r1 <=? 400 = true) by (apply Nat.leb_le; lia).
           destruct (le_lt_dec r2 300) as [Hr2c|Hr2c].
               ++ destruct (le_lt_dec r2 200) as [Hr2d|Hr2d].
                  ** destruct (le_lt_dec r2 100) as [Hr2e|Hr2e].
                     --- assert (E2_100 : r2 <=? 100 = true) by (apply Nat.leb_le; lia).
                         rewrite E100, E200, E300, E400, E2_100. lia.
                  --- assert (E2_100 : r2 <=? 100 = false) by (apply Nat.leb_gt; lia).
                      assert (E2_200 : r2 <=? 200 = true) by (apply Nat.leb_le; lia).
                      rewrite E100, E200, E300, E400, E2_100, E2_200. lia.
               ** assert (E2_100 : r2 <=? 100 = false) by (apply Nat.leb_gt; lia).
                  assert (E2_200 : r2 <=? 200 = false) by (apply Nat.leb_gt; lia).
                  assert (E2_300 : r2 <=? 300 = true) by (apply Nat.leb_le; lia).
                 rewrite E100, E200, E300, E400, E2_100, E2_200, E2_300. lia.
           ++ assert (E2_100 : r2 <=? 100 = false) by (apply Nat.leb_gt; lia).
              assert (E2_200 : r2 <=? 200 = false) by (apply Nat.leb_gt; lia).
              assert (E2_300 : r2 <=? 300 = false) by (apply Nat.leb_gt; lia).
              assert (E2_400 : r2 <=? 400 = true) by (apply Nat.leb_le; lia).
              rewrite E100, E200, E300, E400, E2_100, E2_200, E2_300, E2_400. lia.
        -- assert (E100 : r1 <=? 100 = false) by (apply Nat.leb_gt; lia).
           assert (E200 : r1 <=? 200 = false) by (apply Nat.leb_gt; lia).
           assert (E300 : r1 <=? 300 = false) by (apply Nat.leb_gt; lia).
           assert (E400 : r1 <=? 400 = false) by (apply Nat.leb_gt; lia).
           rewrite E100, E200, E300, E400. lia.
Qed.

Lemma resp_score_mono : forall v w, worse_or_equal v w -> resp_score w >= resp_score v.
Proof.
  intros v w Hw.
  unfold worse_or_equal in Hw.
  destruct Hw as [Htemp [Hhr [Hrr [Hsbp [Hmap [Hlact [Hgcs [Hplt [Hbil [Hcre [Hur [Hpao2 Hfio2]]]]]]]]]]]].
  unfold resp_score.
  set (d1 := max1 (fio2_pct v)).
  set (d2 := max1 (fio2_pct w)).
  assert (Hd1pos : d1 > 0) by (unfold d1, max1; destruct (fio2_pct v); simpl; lia).
  assert (Hd1le : d1 <= d2).
  { unfold d1, d2, max1 in *.
    destruct (fio2_pct v) eqn:Hv; destruct (fio2_pct w) eqn:Hw; simpl in *; lia. }
  set (r1 := (pao2 v * 100) / d1).
  set (r2 := (pao2 w * 100) / d2).
  assert (Hd1nz : d1 <> 0) by lia.
  assert (Hstep1 : r2 <= (pao2 w * 100) / d1).
  { unfold r2. apply Nat.div_le_compat_l; lia. }
  assert (Hstep2 : (pao2 w * 100) / d1 <= r1).
  { unfold r1.
    apply Nat.Div0.div_le_mono; try lia. }
  apply resp_bucket_mono. lia.
Qed.

Lemma coag_score_mono : forall v w, worse_or_equal v w -> coag_score w >= coag_score v.
Proof.
  intros v w Hw; unfold coag_score.
  destruct Hw as [_ [_ [_ [_ [_ [_ [_ [Hplt [_ [_ [_ _]]]]]]]]]]].
  set (pv := platelets v) in *.
  set (pw := platelets w) in *.
  assert (Hpwle : pw <= pv) by lia.
  clear Hplt.
  clearbody pv pw.
  destruct (lt_dec pv 20) as [Hp20|Hp20].
  - assert (Epv20 : pv <? 20 = true) by (apply Nat.ltb_lt; lia).
    assert (Epw20 : pw <? 20 = true) by (apply Nat.ltb_lt; lia).
    rewrite Epv20, Epw20. lia.
  - assert (Epv20 : pv <? 20 = false) by (apply Nat.ltb_ge; lia).
    destruct (lt_dec pv 50) as [Hp50|Hp50].
    + assert (Epv50 : pv <? 50 = true) by (apply Nat.ltb_lt; lia).
      rewrite Epv20, Epv50.
      destruct (lt_dec pw 20) as [Hw20|Hw20].
      * assert (Epw20 : pw <? 20 = true) by (apply Nat.ltb_lt; lia).
        rewrite Epw20. lia.
      * assert (Epw20 : pw <? 20 = false) by (apply Nat.ltb_ge; lia).
        assert (Epw50 : pw <? 50 = true) by (apply Nat.ltb_lt; lia).
        rewrite Epw20, Epw50. lia.
    + assert (Epv50 : pv <? 50 = false) by (apply Nat.ltb_ge; lia).
      destruct (lt_dec pv 100) as [Hp100|Hp100].
      * assert (Epv100 : pv <? 100 = true) by (apply Nat.ltb_lt; lia).
        rewrite Epv20, Epv50, Epv100.
        destruct (lt_dec pw 50) as [Hw50|Hw50].
        -- destruct (lt_dec pw 20) as [Hw20|Hw20].
           ++ assert (Epw20 : pw <? 20 = true) by (apply Nat.ltb_lt; lia).
              rewrite Epw20. lia.
           ++ assert (Epw20 : pw <? 20 = false) by (apply Nat.ltb_ge; lia).
              assert (Epw50 : pw <? 50 = true) by (apply Nat.ltb_lt; lia).
              rewrite Epw20, Epw50. lia.
        -- assert (Epw50 : pw <? 50 = false) by (apply Nat.ltb_ge; lia).
           assert (Epw20 : pw <? 20 = false) by (apply Nat.ltb_ge; lia).
           assert (Epw100 : pw <? 100 = true) by (apply Nat.ltb_lt; lia).
           rewrite Epw20, Epw50, Epw100. lia.
      * assert (Epv100 : pv <? 100 = false) by (apply Nat.ltb_ge; lia).
        destruct (lt_dec pv 150) as [Hp150|Hp150].
        -- assert (Epv150 : pv <? 150 = true) by (apply Nat.ltb_lt; lia).
           rewrite Epv20, Epv50, Epv100, Epv150.
           destruct (lt_dec pw 100) as [Hw100|Hw100].
           ++ destruct (lt_dec pw 50) as [Hw50|Hw50].
              ** destruct (lt_dec pw 20) as [Hw20|Hw20].
                 --- assert (Epw20 : pw <? 20 = true) by (apply Nat.ltb_lt; lia).
                     rewrite Epw20. lia.
                 --- assert (Epw20 : pw <? 20 = false) by (apply Nat.ltb_ge; lia).
                     assert (Epw50 : pw <? 50 = true) by (apply Nat.ltb_lt; lia).
                     rewrite Epw20, Epw50. lia.
              ** assert (Epw50 : pw <? 50 = false) by (apply Nat.ltb_ge; lia).
                 assert (Epw20 : pw <? 20 = false) by (apply Nat.ltb_ge; lia).
                 assert (Epw100 : pw <? 100 = true) by (apply Nat.ltb_lt; lia).
                 rewrite Epw20, Epw50, Epw100. lia.
           ++ assert (Epw100 : pw <? 100 = false) by (apply Nat.ltb_ge; lia).
              assert (Epw50 : pw <? 50 = false) by (apply Nat.ltb_ge; lia).
              assert (Epw20 : pw <? 20 = false) by (apply Nat.ltb_ge; lia).
              assert (Epw150 : pw <? 150 = true) by (apply Nat.ltb_lt; lia).
              rewrite Epw20, Epw50, Epw100, Epw150. lia.
        -- assert (Epv150 : pv <? 150 = false) by (apply Nat.ltb_ge; lia).
           rewrite Epv20, Epv50, Epv100, Epv150. lia.
Qed.

Lemma liver_score_mono : forall v w, worse_or_equal v w -> liver_score w >= liver_score v.
Proof.
  intros v w Hw; unfold liver_score.
  destruct Hw as [_ [_ [_ [_ [_ [_ [_ [_ [Hbil [_ [_ [_ _]]]]]]]]]]]].
  set (bv := bilir10 v) in *.
  set (bw := bilir10 w) in *.
  assert (Hge : bw >= bv) by lia.
  clear Hbil; clearbody bv bw.
  destruct (lt_dec bv 12) as [Hv12|Hv12].
  - assert (E12v : bv <? 12 = true) by (apply Nat.ltb_lt; lia).
    rewrite E12v. lia.
  - assert (Hv12ge : bv >= 12) by lia.
    destruct (lt_dec bv 20) as [Hv20|Hv20].
    + assert (E12v : bv <? 12 = false) by (apply Nat.ltb_ge; lia).
      assert (E20v : bv <? 20 = true) by (apply Nat.ltb_lt; lia).
      rewrite E12v, E20v.
      assert (E12w : bw <? 12 = false) by (apply Nat.ltb_ge; lia).
      rewrite E12w.
      destruct (bw <? 20) eqn:E20w.
      * apply Nat.ltb_lt in E20w. lia.
      * apply Nat.ltb_ge in E20w.
        destruct (bw <? 60) eqn:E60w.
        -- apply Nat.ltb_lt in E60w. lia.
        -- apply Nat.ltb_ge in E60w.
           destruct (bw <? 120) eqn:E120w.
           ++ apply Nat.ltb_lt in E120w. lia.
           ++ apply Nat.ltb_ge in E120w. lia.
    + assert (Hv20ge : bv >= 20) by lia.
      destruct (lt_dec bv 60) as [Hv60|Hv60].
      * assert (E12v : bv <? 12 = false) by (apply Nat.ltb_ge; lia).
        assert (E20v : bv <? 20 = false) by (apply Nat.ltb_ge; lia).
        assert (E60v : bv <? 60 = true) by (apply Nat.ltb_lt; lia).
        rewrite E12v, E20v, E60v.
        assert (E12w : bw <? 12 = false) by (apply Nat.ltb_ge; lia).
        assert (E20w : bw <? 20 = false) by (apply Nat.ltb_ge; lia).
        rewrite E12w, E20w.
        destruct (bw <? 60) eqn:E60w.
        -- apply Nat.ltb_lt in E60w. lia.
        -- apply Nat.ltb_ge in E60w.
           destruct (bw <? 120) eqn:E120w.
           ++ apply Nat.ltb_lt in E120w. lia.
           ++ apply Nat.ltb_ge in E120w. lia.
      * assert (Hv60ge : bv >= 60) by lia.
        destruct (lt_dec bv 120) as [Hv120|Hv120].
        -- assert (E12v : bv <? 12 = false) by (apply Nat.ltb_ge; lia).
           assert (E20v : bv <? 20 = false) by (apply Nat.ltb_ge; lia).
           assert (E60v : bv <? 60 = false) by (apply Nat.ltb_ge; lia).
           assert (E120v : bv <? 120 = true) by (apply Nat.ltb_lt; lia).
           rewrite E12v, E20v, E60v, E120v.
           assert (E12w : bw <? 12 = false) by (apply Nat.ltb_ge; lia).
           assert (E20w : bw <? 20 = false) by (apply Nat.ltb_ge; lia).
           assert (E60w : bw <? 60 = false) by (apply Nat.ltb_ge; lia).
           rewrite E12w, E20w, E60w.
           destruct (bw <? 120) eqn:E120w.
           ++ apply Nat.ltb_lt in E120w. lia.
           ++ apply Nat.ltb_ge in E120w. lia.
        -- assert (E12v : bv <? 12 = false) by (apply Nat.ltb_ge; lia).
           assert (E20v : bv <? 20 = false) by (apply Nat.ltb_ge; lia).
           assert (E60v : bv <? 60 = false) by (apply Nat.ltb_ge; lia).
           assert (E120v : bv <? 120 = false) by (apply Nat.ltb_ge; lia).
           rewrite E12v, E20v, E60v, E120v.
           assert (E12w : bw <? 12 = false) by (apply Nat.ltb_ge; lia).
           assert (E20w : bw <? 20 = false) by (apply Nat.ltb_ge; lia).
           assert (E60w : bw <? 60 = false) by (apply Nat.ltb_ge; lia).
           assert (E120w : bw <? 120 = false) by (apply Nat.ltb_ge; lia).
           rewrite E12w, E20w, E60w, E120w. lia.
Qed.


Lemma cns_score_mono : forall v w, worse_or_equal v w -> cns_score w >= cns_score v.
Proof.
  intros v w Hw; unfold cns_score.
  destruct Hw as [Htemp [Hhr [Hrr [Hsbp [Hmap [Hlact [Hgcs [Hplt [Hbil [Hcre [Hur [Hpao2 Hfio2]]]]]]]]]]]].
  set (gv := gcs v) in *.
  set (gw := gcs w) in *.
  assert (Hgwle : gw <= gv) by lia.
  clear Htemp Hhr Hrr Hsbp Hmap Hlact Hplt Hbil Hcre Hur Hpao2 Hfio2.
  clearbody gv gw.
  destruct (lt_dec gv 6) as [Hv6|Hv6].
  - assert (Egv6 : gv <? 6 = true) by (apply Nat.ltb_lt; lia).
    assert (Egw6 : gw <? 6 = true) by (apply Nat.ltb_lt; lia).
    rewrite Egw6, Egv6. lia.
  - assert (Egv6 : gv <? 6 = false) by (apply Nat.ltb_ge; lia).
    destruct (lt_dec gv 10) as [Hv10|Hv10].
    + assert (Egv10 : gv <? 10 = true) by (apply Nat.ltb_lt; lia).
      rewrite Egv6, Egv10.
      destruct (lt_dec gw 6) as [Hw6|Hw6].
      * assert (Egw6 : gw <? 6 = true) by (apply Nat.ltb_lt; lia).
        rewrite Egw6. lia.
      * assert (Egw6 : gw <? 6 = false) by (apply Nat.ltb_ge; lia).
        assert (Egw10 : gw <? 10 = true) by (apply Nat.ltb_lt; lia).
        rewrite Egw6, Egw10. lia.
    + assert (Hv10ge : gv >= 10) by lia.
      destruct (lt_dec gv 13) as [Hv13|Hv13].
      * assert (Egv10 : gv <? 10 = false) by (apply Nat.ltb_ge; lia).
        assert (Egv13 : gv <? 13 = true) by (apply Nat.ltb_lt; lia).
        rewrite Egv6, Egv10, Egv13.
        destruct (lt_dec gw 10) as [Hw10|Hw10].
        -- destruct (lt_dec gw 6) as [Hw6|Hw6].
           ++ assert (Egw6 : gw <? 6 = true) by (apply Nat.ltb_lt; lia).
              rewrite Egw6. lia.
           ++ assert (Egw6 : gw <? 6 = false) by (apply Nat.ltb_ge; lia).
              assert (Egw10 : gw <? 10 = true) by (apply Nat.ltb_lt; lia).
              rewrite Egw6, Egw10. lia.
        -- assert (Egw6 : gw <? 6 = false) by (apply Nat.ltb_ge; lia).
           assert (Egw10 : gw <? 10 = false) by (apply Nat.ltb_ge; lia).
           assert (Egw13 : gw <? 13 = true) by (apply Nat.ltb_lt; lia).
           rewrite Egw6, Egw10, Egw13. lia.
      * assert (Hv13ge : gv >= 13) by lia.
        destruct (lt_dec gv 15) as [Hv15|Hv15].
        -- assert (Egv10 : gv <? 10 = false) by (apply Nat.ltb_ge; lia).
           assert (Egv13 : gv <? 13 = false) by (apply Nat.ltb_ge; lia).
           assert (Egv15 : gv <? 15 = true) by (apply Nat.ltb_lt; lia).
           rewrite Egv6, Egv10, Egv13, Egv15.
           destruct (lt_dec gw 13) as [Hw13|Hw13].
           ++ destruct (lt_dec gw 10) as [Hw10|Hw10].
              ** destruct (lt_dec gw 6) as [Hw6|Hw6].
                 --- assert (Egw6 : gw <? 6 = true) by (apply Nat.ltb_lt; lia).
                     rewrite Egw6. lia.
                 --- assert (Egw6 : gw <? 6 = false) by (apply Nat.ltb_ge; lia).
                     assert (Egw10 : gw <? 10 = true) by (apply Nat.ltb_lt; lia).
                     rewrite Egw6, Egw10. lia.
              ** assert (Egw6 : gw <? 6 = false) by (apply Nat.ltb_ge; lia).
                 assert (Egw10 : gw <? 10 = false) by (apply Nat.ltb_ge; lia).
                 assert (Egw13 : gw <? 13 = true) by (apply Nat.ltb_lt; lia).
                 rewrite Egw6, Egw10, Egw13. lia.
           ++ assert (Egw6 : gw <? 6 = false) by (apply Nat.ltb_ge; lia).
              assert (Egw10 : gw <? 10 = false) by (apply Nat.ltb_ge; lia).
              assert (Egw13 : gw <? 13 = false) by (apply Nat.ltb_ge; lia).
              assert (Egw15 : gw <? 15 = true) by (apply Nat.ltb_lt; lia).
              rewrite Egw6, Egw10, Egw13, Egw15. lia.
        -- assert (Egv10 : gv <? 10 = false) by (apply Nat.ltb_ge; lia).
           assert (Egv13 : gv <? 13 = false) by (apply Nat.ltb_ge; lia).
           assert (Egv15 : gv <? 15 = false) by (apply Nat.ltb_ge; lia).
           rewrite Egv6, Egv10, Egv13, Egv15. lia.
Qed.


Lemma creat_score_mono : forall c1 c2, c1 <= c2 -> creat_score c2 >= creat_score c1.
Proof.
  intros c1 c2 Hle; unfold creat_score, ge_bool.
  destruct (lt_dec c1 11) as [H11|H11].
  - assert (Ec1_53 : 53 <=? c1 = false) by (apply Nat.leb_gt; lia).
    assert (Ec1_34 : 34 <=? c1 = false) by (apply Nat.leb_gt; lia).
    assert (Ec1_21 : 21 <=? c1 = false) by (apply Nat.leb_gt; lia).
    assert (Ec1_11 : 11 <=? c1 = false) by (apply Nat.leb_gt; lia).
    rewrite Ec1_53, Ec1_34, Ec1_21, Ec1_11. lia.
  - assert (H11ge : c1 >= 11) by lia.
    destruct (lt_dec c1 21) as [H21|H21].
    + assert (Ec1_53 : 53 <=? c1 = false) by (apply Nat.leb_gt; lia).
      assert (Ec1_34 : 34 <=? c1 = false) by (apply Nat.leb_gt; lia).
      assert (Ec1_21 : 21 <=? c1 = false) by (apply Nat.leb_gt; lia).
      assert (Ec1_11 : 11 <=? c1 = true) by (apply Nat.leb_le; lia).
      rewrite Ec1_53, Ec1_34, Ec1_21, Ec1_11.
      destruct (lt_dec c2 21) as [Hc2_21|Hc2_21].
      * assert (Ec2_53 : 53 <=? c2 = false) by (apply Nat.leb_gt; lia).
        assert (Ec2_34 : 34 <=? c2 = false) by (apply Nat.leb_gt; lia).
        assert (Ec2_21 : 21 <=? c2 = false) by (apply Nat.leb_gt; lia).
        assert (Ec2_11 : 11 <=? c2 = true) by (apply Nat.leb_le; lia).
        rewrite Ec2_53, Ec2_34, Ec2_21, Ec2_11. lia.
      * destruct (lt_dec c2 34) as [Hc2_34|Hc2_34].
        -- assert (Ec2_53 : 53 <=? c2 = false) by (apply Nat.leb_gt; lia).
           assert (Ec2_34 : 34 <=? c2 = false) by (apply Nat.leb_gt; lia).
           assert (Ec2_21 : 21 <=? c2 = true) by (apply Nat.leb_le; lia).
           rewrite Ec2_53, Ec2_34, Ec2_21. lia.
        -- destruct (lt_dec c2 53) as [Hc2_53|Hc2_53].
           ++ assert (Ec2_53 : 53 <=? c2 = false) by (apply Nat.leb_gt; lia).
              assert (Ec2_34 : 34 <=? c2 = true) by (apply Nat.leb_le; lia).
              rewrite Ec2_53, Ec2_34. lia.
           ++ assert (Ec2_53 : 53 <=? c2 = true) by (apply Nat.leb_le; lia).
              rewrite Ec2_53. lia.
    + assert (H21ge : c1 >= 21) by lia.
      destruct (lt_dec c1 34) as [H34|H34].
      * assert (Ec1_53 : 53 <=? c1 = false) by (apply Nat.leb_gt; lia).
        assert (Ec1_34 : 34 <=? c1 = false) by (apply Nat.leb_gt; lia).
        assert (Ec1_21 : 21 <=? c1 = true) by (apply Nat.leb_le; lia).
        rewrite Ec1_53, Ec1_34, Ec1_21.
        destruct (lt_dec c2 34) as [Hc2_34|Hc2_34].
        -- assert (Ec2_53 : 53 <=? c2 = false) by (apply Nat.leb_gt; lia).
           assert (Ec2_34 : 34 <=? c2 = false) by (apply Nat.leb_gt; lia).
           assert (Ec2_21 : 21 <=? c2 = true) by (apply Nat.leb_le; lia).
           rewrite Ec2_53, Ec2_34, Ec2_21. lia.
        -- destruct (lt_dec c2 53) as [Hc2_53|Hc2_53].
           ++ assert (Ec2_53 : 53 <=? c2 = false) by (apply Nat.leb_gt; lia).
              assert (Ec2_34 : 34 <=? c2 = true) by (apply Nat.leb_le; lia).
              rewrite Ec2_53, Ec2_34. lia.
           ++ assert (Ec2_53 : 53 <=? c2 = true) by (apply Nat.leb_le; lia).
              rewrite Ec2_53. lia.
      * assert (H34ge : c1 >= 34) by lia.
        destruct (lt_dec c1 53) as [H53|H53].
        -- assert (Ec1_53 : 53 <=? c1 = false) by (apply Nat.leb_gt; lia).
           assert (Ec1_34 : 34 <=? c1 = true) by (apply Nat.leb_le; lia).
           rewrite Ec1_53, Ec1_34.
           destruct (lt_dec c2 53) as [Hc2_53|Hc2_53].
           ++ assert (Ec2_53 : 53 <=? c2 = false) by (apply Nat.leb_gt; lia).
              assert (Ec2_34 : 34 <=? c2 = true) by (apply Nat.leb_le; lia).
              rewrite Ec2_53, Ec2_34. lia.
           ++ assert (Ec2_53 : 53 <=? c2 = true) by (apply Nat.leb_le; lia).
              rewrite Ec2_53. lia.
        -- assert (Ec1_53 : 53 <=? c1 = true) by (apply Nat.leb_le; lia).
           assert (Ec2_53 : 53 <=? c2 = true) by (apply Nat.leb_le; lia).
           rewrite Ec1_53, Ec2_53. lia.
Qed.

Lemma urine_score_mono : forall u1 u2, u2 <= u1 -> urine_score u2 >= urine_score u1.
Proof.
  intros u1 u2 Hle; unfold urine_score.
  destruct (le_lt_dec u1 20) as [Hu20|Hu20].
  - assert (Eu1_20 : u1 <=? 20 = true) by (apply Nat.leb_le; lia).
    assert (Eu2_20 : u2 <=? 20 = true) by (apply Nat.leb_le; lia).
    rewrite Eu1_20, Eu2_20. lia.
  - assert (Eu1_20 : u1 <=? 20 = false) by (apply Nat.leb_gt; lia).
    destruct (le_lt_dec u1 50) as [Hu50|Hu50].
    + assert (Eu1_50 : u1 <=? 50 = true) by (apply Nat.leb_le; lia).
      rewrite Eu1_20, Eu1_50.
      destruct (le_lt_dec u2 20) as [Hu2_20|Hu2_20].
      * assert (Eu2_20 : u2 <=? 20 = true) by (apply Nat.leb_le; lia).
        rewrite Eu2_20. lia.
      * assert (Eu2_20 : u2 <=? 20 = false) by (apply Nat.leb_gt; lia).
        assert (Eu2_50 : u2 <=? 50 = true) by (apply Nat.leb_le; lia).
        rewrite Eu2_20, Eu2_50. lia.
    + assert (Eu1_50 : u1 <=? 50 = false) by (apply Nat.leb_gt; lia).
      destruct (le_lt_dec u1 120) as [Hu120|Hu120].
      * assert (Eu1_120 : u1 <=? 120 = true) by (apply Nat.leb_le; lia).
        rewrite Eu1_20, Eu1_50, Eu1_120.
        destruct (le_lt_dec u2 50) as [Hu2_50|Hu2_50].
        -- destruct (le_lt_dec u2 20) as [Hu2_20|Hu2_20].
           ++ assert (Eu2_20 : u2 <=? 20 = true) by (apply Nat.leb_le; lia).
              rewrite Eu2_20. lia.
           ++ assert (Eu2_20 : u2 <=? 20 = false) by (apply Nat.leb_gt; lia).
              assert (Eu2_50 : u2 <=? 50 = true) by (apply Nat.leb_le; lia).
              rewrite Eu2_20, Eu2_50. lia.
        -- assert (Eu2_50 : u2 <=? 50 = false) by (apply Nat.leb_gt; lia).
           assert (Eu2_120 : u2 <=? 120 = true) by (apply Nat.leb_le; lia).
           assert (Eu2_20 : u2 <=? 20 = false) by (apply Nat.leb_gt; lia).
           rewrite Eu2_20, Eu2_50, Eu2_120. lia.
      * assert (Eu1_120 : u1 <=? 120 = false) by (apply Nat.leb_gt; lia).
        destruct (le_lt_dec u1 200) as [Hu200|Hu200].
        -- assert (Eu1_200 : u1 <=? 200 = true) by (apply Nat.leb_le; lia).
           rewrite Eu1_20, Eu1_50, Eu1_120, Eu1_200.
           destruct (le_lt_dec u2 120) as [Hu2_120|Hu2_120].
           ++ destruct (le_lt_dec u2 50) as [Hu2_50|Hu2_50].
              ** destruct (le_lt_dec u2 20) as [Hu2_20|Hu2_20].
                 --- assert (Eu2_20 : u2 <=? 20 = true) by (apply Nat.leb_le; lia).
                     rewrite Eu2_20. lia.
                 --- assert (Eu2_20 : u2 <=? 20 = false) by (apply Nat.leb_gt; lia).
                     assert (Eu2_50 : u2 <=? 50 = true) by (apply Nat.leb_le; lia).
                     rewrite Eu2_20, Eu2_50. lia.
              ** assert (Eu2_50 : u2 <=? 50 = false) by (apply Nat.leb_gt; lia).
                 assert (Eu2_120 : u2 <=? 120 = true) by (apply Nat.leb_le; lia).
                 assert (Eu2_20 : u2 <=? 20 = false) by (apply Nat.leb_gt; lia).
                 rewrite Eu2_20, Eu2_50, Eu2_120. lia.
           ++ assert (Eu2_120 : u2 <=? 120 = false) by (apply Nat.leb_gt; lia).
              assert (Eu2_200 : u2 <=? 200 = true) by (apply Nat.leb_le; lia).
              assert (Eu2_50 : u2 <=? 50 = false) by (apply Nat.leb_gt; lia).
              assert (Eu2_20 : u2 <=? 20 = false) by (apply Nat.leb_gt; lia).
              rewrite Eu2_20, Eu2_50, Eu2_120, Eu2_200. lia.
        -- assert (Eu1_200 : u1 <=? 200 = false) by (apply Nat.leb_gt; lia).
           rewrite Eu1_20, Eu1_50, Eu1_120, Eu1_200. lia.
Qed.

Lemma renal_score_mono : forall v w, worse_or_equal v w -> renal_score w >= renal_score v.
Proof.
  intros v w Hw; unfold renal_score.
  destruct Hw as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hcreat [Hur [_ _]]]]]]]]]]]].
  assert (Hc : creat_score (creat10 w) >= creat_score (creat10 v)).
  { apply (@creat_score_mono (creat10 v) (creat10 w)); lia. }
  assert (Hu : urine_score (urine_ml_hr w) >= urine_score (urine_ml_hr v)).
  { apply (@urine_score_mono (urine_ml_hr v) (urine_ml_hr w)); lia. }
  apply Nat.max_lub.
  - eapply Nat.le_trans; [apply Hc | apply Nat.le_max_l].
  - eapply Nat.le_trans; [apply Hu | apply Nat.le_max_r].
Qed.

Lemma cv_score_mono : forall v w t, map_mm w <= map_mm v -> cv_score w t >= cv_score v t.
Proof.
  intros v w t Hm; unfold cv_score.
  destruct (pressor_high_on t); destruct (pressor_low_on t); try lia.
  destruct (map_mm v <? 70) eqn:Hv.
  - apply Nat.ltb_lt in Hv as Hvlt.
    assert (Hwlt : map_mm w <? 70 = true) by (apply Nat.ltb_lt; lia).
    rewrite Hwlt. lia.
  - assert (Hvge : map_mm v >= 70) by (apply Nat.ltb_ge; exact Hv).
    destruct (map_mm w <? 70) eqn:Hw.
    + apply Nat.ltb_lt in Hw as Hwlt. lia.
    + assert (Hwge : map_mm w >= 70) by (apply Nat.ltb_ge; exact Hw). lia.
Qed.

Lemma sofa_monotone : forall v w t, worse_or_equal v w -> sofa {| vit := w; th := t |} >= sofa {| vit := v; th := t |}.
Proof.
  intros v w t Hw; unfold sofa; simpl.
  pose proof (resp_score_mono (v:=v) (w:=w) Hw) as Hr1.
  pose proof (coag_score_mono (v:=v) (w:=w) Hw) as Hr2.
  pose proof (liver_score_mono (v:=v) (w:=w) Hw) as Hr3.
  pose proof (cns_score_mono (v:=v) (w:=w) Hw) as Hr4.
  pose proof (renal_score_mono (v:=v) (w:=w) Hw) as Hr5.
  destruct Hw as [Ht [Hhr [Hrr [Hsbp [Hmap [Hlact [Hgcs [Hplt [Hbil [Hcreat [Hur [Hpao2 Hfio]]]]]]]]]]]].
  pose proof (cv_score_mono v w t Hmap) as Hr6.
  lia.
Qed.

(** Escalation properties of the plan *)
Lemma plan_antibiotics_if_infection :
  forall s, infection (vit s) = true -> p_antibiotics (decide_plan s) = true.
Proof. intros; unfold decide_plan; simpl; rewrite H; reflexivity. Qed.

Lemma plan_fluids_if_hypotension_or_lactate :
  forall s, (map_mm (vit s) <= 65 \/ lact10 (vit s) >= 20) -> p_fluids (decide_plan s) = true.
Proof.
  intros s [Hm|Hl]; unfold decide_plan; cbn -[ge_bool].
  - assert (Hmm : map_mm (vit s) <=? 65 = true) by (apply Nat.leb_le; lia).
    rewrite Hmm. reflexivity.
  - assert (Hll : ge_bool (lact10 (vit s)) 20 = true) by (unfold ge_bool; apply Nat.leb_le; lia).
    rewrite Hll; simpl; repeat rewrite Bool.orb_true_r; reflexivity.
Qed.

Lemma plan_escalates_on_shock :
  forall s, septic_shock s = true -> p_pressor_lo (decide_plan s) = true.
Proof.
  intros s Hshock.
  unfold septic_shock in Hshock.
  apply andb_prop in Hshock as [Hinf Hlac20].
  apply andb_prop in Hinf as [Hinf Hmap].
  apply andb_prop in Hinf as [Hinf Hsofa].
  unfold decide_plan; cbn -[ge_bool].
  rewrite Hmap, Hlac20. cbn. rewrite Bool.orb_true_r. reflexivity.
Qed.

(** Examples *)
Definition v_norm : Vitals :=
  {| temp10 := 370; hr := 72; rr := 14; sbp := 120; map_mm := 85; lact10 := 12;
     gcs := 15; platelets := 250; bilir10 := 8; creat10 := 10; urine_ml_hr := 80;
     pao2 := 90; fio2_pct := 21; infection := false |}.

Definition v_shock : Vitals :=
  {| temp10 := 392; hr := 140; rr := 32; sbp := 85; map_mm := 55; lact10 := 45;
     gcs := 13; platelets := 90; bilir10 := 25; creat10 := 40; urine_ml_hr := 20;
     pao2 := 60; fio2_pct := 50; infection := true |}.

Example decide_norm_monitor :
  p_fluids (decide_plan {| vit := v_norm; th := init_therapy |}) = false /\
  p_antibiotics (decide_plan {| vit := v_norm; th := init_therapy |}) = false /\
  p_pressor_lo (decide_plan {| vit := v_norm; th := init_therapy |}) = false /\
  p_pressor_hi (decide_plan {| vit := v_norm; th := init_therapy |}) = false /\
  p_icu (decide_plan {| vit := v_norm; th := init_therapy |}) = false.
Proof. repeat split; reflexivity. Qed.

Example decide_shock_escalates :
  p_fluids (decide_plan {| vit := v_shock; th := init_therapy |}) = true /\
  p_antibiotics (decide_plan {| vit := v_shock; th := init_therapy |}) = true /\
  p_pressor_lo (decide_plan {| vit := v_shock; th := init_therapy |}) = true /\
  p_pressor_hi (decide_plan {| vit := v_shock; th := init_therapy |}) = true /\
  p_icu (decide_plan {| vit := v_shock; th := init_therapy |}) = true.
Proof. repeat split; reflexivity. Qed.

Eval compute in sofa {| vit := v_norm; th := init_therapy |}.
Eval compute in sofa {| vit := v_shock; th := init_therapy |}.
Eval compute in decide_plan {| vit := v_shock; th := init_therapy |}.
