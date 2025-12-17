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

From Coq Require Import Bool Arith Lia List.

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

(** Time representation: minutes since presentation. *)
Definition Time := nat.

Record Therapy := {
  fluids_on         : bool;
  fluids_start_time : option Time;
  antibiotics_on    : bool;
  abx_start_time    : option Time;
  pressor_low_on    : bool;
  pressor_high_on   : bool;
  icu_transfer      : bool
}.

Definition init_therapy : Therapy :=
  {| fluids_on := false; fluids_start_time := None;
     antibiotics_on := false; abx_start_time := None;
     pressor_low_on := false; pressor_high_on := false;
     icu_transfer := false |}.

Record State := {
  vit          : Vitals;
  th           : Therapy;
  current_time : Time;
  presentation_time : Time
}.

(** Time elapsed since presentation. *)
Definition time_since_presentation (s : State) : Time :=
  current_time s - presentation_time s.

(** Sepsis-3 Hour-1 Bundle compliance windows (in minutes). *)
Definition hour_1_window : Time := 60.
Definition hour_3_window : Time := 180.
Definition hour_6_window : Time := 360.

(** Check if intervention was started within time window. *)
Definition started_within (start : option Time) (deadline : Time) : bool :=
  match start with
  | None => false
  | Some t => t <=? deadline
  end.

(** Hour-1 bundle: antibiotics and fluids started within 60 minutes. *)
Definition hour1_bundle_compliant (s : State) : bool :=
  let deadline := presentation_time s + hour_1_window in
  started_within (abx_start_time (th s)) deadline &&
  started_within (fluids_start_time (th s)) deadline.

(** Reassessment due predicates. *)
Definition reassessment_due_3hr (s : State) : bool :=
  hour_3_window <=? time_since_presentation s.

Definition reassessment_due_6hr (s : State) : bool :=
  hour_6_window <=? time_since_presentation s.

(** Time-related lemmas. *)
Lemma started_within_monotone :
  forall start t1 t2, t1 <= t2 -> started_within start t1 = true -> started_within start t2 = true.
Proof.
  intros start t1 t2 Hle Hstart.
  unfold started_within in *.
  destruct start as [t|].
  - apply Nat.leb_le in Hstart.
    apply Nat.leb_le.
    lia.
  - discriminate.
Qed.

Lemma bundle_compliance_preserved :
  forall s t_extra,
    hour1_bundle_compliant s = true ->
    hour1_bundle_compliant {| vit := vit s;
                              th := th s;
                              current_time := current_time s + t_extra;
                              presentation_time := presentation_time s |} = true.
Proof.
  intros s t_extra Hcomp.
  unfold hour1_bundle_compliant in *.
  simpl.
  exact Hcomp.
Qed.

(** Helper to create State with default times (for time-independent lemmas). *)
Definition make_state (v : Vitals) (t : Therapy) : State :=
  {| vit := v; th := t; current_time := 0; presentation_time := 0 |}.

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

(** Generic threshold-based scoring with monotonicity. *)
Fixpoint score_below_thresholds (v : nat) (thresholds : list (nat * nat)) : nat :=
  match thresholds with
  | nil => 0
  | (thresh, sc) :: rest =>
      if v <? thresh then sc else score_below_thresholds v rest
  end.

Fixpoint scores_decreasing (ths : list (nat * nat)) : Prop :=
  match ths with
  | nil => True
  | (_, s) :: rest =>
      (forall t' s', In (t', s') rest -> s >= s') /\ scores_decreasing rest
  end.

Lemma score_below_bound (v : nat) (ths : list (nat * nat)) (t s : nat)
  : scores_decreasing ((t, s) :: ths) -> score_below_thresholds v ths <= s.
Proof.
  intro Hdec.
  simpl in Hdec.
  destruct Hdec as [Hdom _].
  induction ths as [| [t' s'] rest IH].
  - simpl.
    lia.
  - simpl.
    destruct (v <? t') eqn:E.
    + assert (Hin : In (t', s') ((t', s') :: rest)) by (left; reflexivity).
      specialize (Hdom t' s' Hin).
      lia.
    + apply IH.
      intros t'' s'' Hin.
      apply (Hdom t'' s'').
      right.
      exact Hin.
Qed.

Lemma score_below_mono (v1 v2 : nat) (ths : list (nat * nat))
  : scores_decreasing ths -> v2 <= v1 -> score_below_thresholds v2 ths >= score_below_thresholds v1 ths.
Proof.
  intros Hdec Hle.
  induction ths as [| [t s] rest IH].
  - simpl.
    lia.
  - simpl.
    destruct (v2 <? t) eqn:E2.
    + destruct (v1 <? t) eqn:E1.
      * lia.
      * pose proof (@score_below_bound v1 rest t s Hdec) as Hb.
        lia.
    + destruct (v1 <? t) eqn:E1.
      * apply Nat.ltb_lt in E1.
        apply Nat.ltb_ge in E2.
        lia.
      * simpl in Hdec.
        destruct Hdec as [_ Hrest].
        apply IH.
        exact Hrest.
Qed.

Fixpoint score_above_thresholds (v : nat) (thresholds : list (nat * nat)) : nat :=
  match thresholds with
  | nil => 0
  | (thresh, sc) :: rest =>
      if thresh <=? v then sc else score_above_thresholds v rest
  end.

Lemma score_above_bound (v : nat) (ths : list (nat * nat)) (t s : nat)
  : scores_decreasing ((t, s) :: ths) -> score_above_thresholds v ths <= s.
Proof.
  intro Hdec.
  simpl in Hdec.
  destruct Hdec as [Hdom _].
  induction ths as [| [t' s'] rest IH].
  - simpl.
    lia.
  - simpl.
    destruct (t' <=? v) eqn:E.
    + assert (Hin : In (t', s') ((t', s') :: rest)) by (left; reflexivity).
      specialize (Hdom t' s' Hin).
      lia.
    + apply IH.
      intros t'' s'' Hin.
      apply (Hdom t'' s'').
      right.
      exact Hin.
Qed.

Lemma score_above_mono (v1 v2 : nat) (ths : list (nat * nat))
  : scores_decreasing ths -> v1 <= v2 -> score_above_thresholds v2 ths >= score_above_thresholds v1 ths.
Proof.
  intros Hdec Hle.
  induction ths as [| [t s] rest IH].
  - simpl.
    lia.
  - simpl.
    destruct (t <=? v2) eqn:E2.
    + destruct (t <=? v1) eqn:E1.
      * lia.
      * pose proof (@score_above_bound v1 rest t s Hdec) as Hb.
        lia.
    + destruct (t <=? v1) eqn:E1.
      * apply Nat.leb_le in E1.
        apply Nat.leb_gt in E2.
        lia.
      * simpl in Hdec.
        destruct Hdec as [_ Hrest].
        apply IH.
        exact Hrest.
Qed.

(** SOFA organ subscores (0..4), simplified. *)
Definition resp_bucket (ratio:nat) : nat :=
  if ratio <=? 100 then 4
  else if ratio <=? 200 then 3
  else if ratio <=? 300 then 2
  else if ratio <=? 400 then 1
  else 0.

Definition resp_thresholds : list (nat * nat) :=
  (101, 4) :: (201, 3) :: (301, 2) :: (401, 1) :: nil.

Lemma resp_bucket_eq : forall r, resp_bucket r = score_below_thresholds r resp_thresholds.
Proof.
  intro r.
  unfold resp_bucket, resp_thresholds, score_below_thresholds.
  destruct (r <=? 100) eqn:E100.
  - apply Nat.leb_le in E100.
    assert (r <? 101 = true) by (apply Nat.ltb_lt; lia).
    rewrite H.
    reflexivity.
  - apply Nat.leb_gt in E100.
    assert (r <? 101 = false) by (apply Nat.ltb_ge; lia).
    rewrite H.
    destruct (r <=? 200) eqn:E200.
    + apply Nat.leb_le in E200.
      assert (r <? 201 = true) by (apply Nat.ltb_lt; lia).
      rewrite H0.
      reflexivity.
    + apply Nat.leb_gt in E200.
      assert (r <? 201 = false) by (apply Nat.ltb_ge; lia).
      rewrite H0.
      destruct (r <=? 300) eqn:E300.
      * apply Nat.leb_le in E300.
        assert (r <? 301 = true) by (apply Nat.ltb_lt; lia).
        rewrite H1.
        reflexivity.
      * apply Nat.leb_gt in E300.
        assert (r <? 301 = false) by (apply Nat.ltb_ge; lia).
        rewrite H1.
        destruct (r <=? 400) eqn:E400.
        -- apply Nat.leb_le in E400.
           assert (r <? 401 = true) by (apply Nat.ltb_lt; lia).
           rewrite H2.
           reflexivity.
        -- apply Nat.leb_gt in E400.
           assert (r <? 401 = false) by (apply Nat.ltb_ge; lia).
           rewrite H2.
           reflexivity.
Qed.

Lemma resp_thresholds_decreasing : scores_decreasing resp_thresholds.
Proof.
  unfold resp_thresholds.
  simpl.
  repeat split.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | [Heq | Hin]]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | Hin]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | Hin].
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    contradiction.
Qed.

Definition resp_score (v:Vitals) : nat :=
  let fio2 := max1 (fio2_pct v) in
  resp_bucket ((pao2 v * 100) / fio2).

Definition coag_score_raw (p : nat) : nat :=
  if p <? 20 then 4
  else if p <? 50 then 3
  else if p <? 100 then 2
  else if p <? 150 then 1
  else 0.

Definition coag_score (v:Vitals) : nat := coag_score_raw (platelets v).

Definition coag_thresholds : list (nat * nat) :=
  (20, 4) :: (50, 3) :: (100, 2) :: (150, 1) :: nil.

Lemma coag_score_raw_eq : forall p, coag_score_raw p = score_below_thresholds p coag_thresholds.
Proof.
  intro p.
  unfold coag_score_raw, coag_thresholds, score_below_thresholds.
  reflexivity.
Qed.

Lemma coag_thresholds_decreasing : scores_decreasing coag_thresholds.
Proof.
  unfold coag_thresholds.
  simpl.
  repeat split.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | [Heq | Hin]]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | Hin]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | Hin].
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    contradiction.
Qed.

Lemma coag_score_raw_mono : forall p1 p2, p2 <= p1 -> coag_score_raw p2 >= coag_score_raw p1.
Proof.
  intros p1 p2 Hp.
  rewrite !coag_score_raw_eq.
  apply score_below_mono.
  - exact coag_thresholds_decreasing.
  - exact Hp.
Qed.

Definition liver_score_raw (b : nat) : nat :=
  if b <? 12 then 0
  else if b <? 20 then 1
  else if b <? 60 then 2
  else if b <? 120 then 3
  else 4.

Definition liver_score (v:Vitals) : nat := liver_score_raw (bilir10 v).

Definition liver_thresholds : list (nat * nat) :=
  (120, 4) :: (60, 3) :: (20, 2) :: (12, 1) :: nil.

Lemma liver_score_raw_eq : forall b, liver_score_raw b = score_above_thresholds b liver_thresholds.
Proof.
  intro b.
  unfold liver_score_raw, liver_thresholds, score_above_thresholds.
  destruct (b <? 12) eqn:E12.
  - apply Nat.ltb_lt in E12.
    assert (120 <=? b = false) by (apply Nat.leb_gt; lia).
    assert (60 <=? b = false) by (apply Nat.leb_gt; lia).
    assert (20 <=? b = false) by (apply Nat.leb_gt; lia).
    assert (12 <=? b = false) by (apply Nat.leb_gt; lia).
    rewrite H, H0, H1, H2.
    reflexivity.
  - apply Nat.ltb_ge in E12.
    destruct (b <? 20) eqn:E20.
    + apply Nat.ltb_lt in E20.
      assert (120 <=? b = false) by (apply Nat.leb_gt; lia).
      assert (60 <=? b = false) by (apply Nat.leb_gt; lia).
      assert (20 <=? b = false) by (apply Nat.leb_gt; lia).
      assert (12 <=? b = true) by (apply Nat.leb_le; lia).
      rewrite H, H0, H1, H2.
      reflexivity.
    + apply Nat.ltb_ge in E20.
      destruct (b <? 60) eqn:E60.
      * apply Nat.ltb_lt in E60.
        assert (120 <=? b = false) by (apply Nat.leb_gt; lia).
        assert (60 <=? b = false) by (apply Nat.leb_gt; lia).
        assert (20 <=? b = true) by (apply Nat.leb_le; lia).
        rewrite H, H0, H1.
        reflexivity.
      * apply Nat.ltb_ge in E60.
        destruct (b <? 120) eqn:E120.
        -- apply Nat.ltb_lt in E120.
           assert (120 <=? b = false) by (apply Nat.leb_gt; lia).
           assert (60 <=? b = true) by (apply Nat.leb_le; lia).
           rewrite H, H0.
           reflexivity.
        -- apply Nat.ltb_ge in E120.
           assert (120 <=? b = true) by (apply Nat.leb_le; lia).
           rewrite H.
           reflexivity.
Qed.

Lemma liver_thresholds_decreasing : scores_decreasing liver_thresholds.
Proof.
  unfold liver_thresholds.
  simpl.
  repeat split.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | [Heq | Hin]]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | Hin]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | Hin].
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    contradiction.
Qed.

Lemma liver_score_raw_mono : forall b1 b2, b1 <= b2 -> liver_score_raw b2 >= liver_score_raw b1.
Proof.
  intros b1 b2 Hb.
  rewrite !liver_score_raw_eq.
  apply score_above_mono.
  - exact liver_thresholds_decreasing.
  - exact Hb.
Qed.

Definition cns_score_raw (g : nat) : nat :=
  if g <? 6 then 4
  else if g <? 10 then 3
  else if g <? 13 then 2
  else if g <? 15 then 1
  else 0.

Definition cns_score (v:Vitals) : nat := cns_score_raw (gcs v).

Definition cns_thresholds : list (nat * nat) :=
  (6, 4) :: (10, 3) :: (13, 2) :: (15, 1) :: nil.

Lemma cns_score_raw_eq : forall g, cns_score_raw g = score_below_thresholds g cns_thresholds.
Proof.
  intro g.
  unfold cns_score_raw, cns_thresholds, score_below_thresholds.
  reflexivity.
Qed.

Lemma cns_thresholds_decreasing : scores_decreasing cns_thresholds.
Proof.
  unfold cns_thresholds.
  simpl.
  repeat split.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | [Heq | Hin]]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | Hin]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | Hin].
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    contradiction.
Qed.

Lemma cns_score_raw_mono : forall g1 g2, g2 <= g1 -> cns_score_raw g2 >= cns_score_raw g1.
Proof.
  intros g1 g2 Hg.
  rewrite !cns_score_raw_eq.
  apply score_below_mono.
  - exact cns_thresholds_decreasing.
  - exact Hg.
Qed.

Definition creat_score (c:nat) : nat :=
  if ge_bool c 53 then 4
  else if ge_bool c 34 then 3
  else if ge_bool c 21 then 2
  else if ge_bool c 11 then 1
  else 0.

Definition creat_thresholds : list (nat * nat) :=
  (53, 4) :: (34, 3) :: (21, 2) :: (11, 1) :: nil.

Lemma creat_score_eq : forall c, creat_score c = score_above_thresholds c creat_thresholds.
Proof.
  intro c.
  unfold creat_score, creat_thresholds, score_above_thresholds, ge_bool.
  reflexivity.
Qed.

Lemma creat_thresholds_decreasing : scores_decreasing creat_thresholds.
Proof.
  unfold creat_thresholds.
  simpl.
  repeat split.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | [Heq | Hin]]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | Hin]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | Hin].
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    contradiction.
Qed.

Definition urine_score (u:nat) : nat :=
  if u <=? 20 then 4
  else if u <=? 50 then 3
  else if u <=? 120 then 2
  else if u <=? 200 then 1
  else 0.

Definition urine_thresholds : list (nat * nat) :=
  (21, 4) :: (51, 3) :: (121, 2) :: (201, 1) :: nil.

Lemma urine_score_eq : forall u, urine_score u = score_below_thresholds u urine_thresholds.
Proof.
  intro u.
  unfold urine_score, urine_thresholds, score_below_thresholds.
  destruct (u <=? 20) eqn:E20.
  - apply Nat.leb_le in E20.
    assert (u <? 21 = true) by (apply Nat.ltb_lt; lia).
    rewrite H.
    reflexivity.
  - apply Nat.leb_gt in E20.
    assert (u <? 21 = false) by (apply Nat.ltb_ge; lia).
    rewrite H.
    destruct (u <=? 50) eqn:E50.
    + apply Nat.leb_le in E50.
      assert (u <? 51 = true) by (apply Nat.ltb_lt; lia).
      rewrite H0.
      reflexivity.
    + apply Nat.leb_gt in E50.
      assert (u <? 51 = false) by (apply Nat.ltb_ge; lia).
      rewrite H0.
      destruct (u <=? 120) eqn:E120.
      * apply Nat.leb_le in E120.
        assert (u <? 121 = true) by (apply Nat.ltb_lt; lia).
        rewrite H1.
        reflexivity.
      * apply Nat.leb_gt in E120.
        assert (u <? 121 = false) by (apply Nat.ltb_ge; lia).
        rewrite H1.
        destruct (u <=? 200) eqn:E200.
        -- apply Nat.leb_le in E200.
           assert (u <? 201 = true) by (apply Nat.ltb_lt; lia).
           rewrite H2.
           reflexivity.
        -- apply Nat.leb_gt in E200.
           assert (u <? 201 = false) by (apply Nat.ltb_ge; lia).
           rewrite H2.
           reflexivity.
Qed.

Lemma urine_thresholds_decreasing : scores_decreasing urine_thresholds.
Proof.
  unfold urine_thresholds.
  simpl.
  repeat split.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | [Heq | Hin]]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | [Heq | Hin]].
    + injection Heq; intros; lia.
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    destruct Hin as [Heq | Hin].
    + injection Heq; intros; lia.
    + contradiction.
  - intros t' s' Hin.
    contradiction.
Qed.

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
  rewrite !resp_bucket_eq.
  apply score_below_mono.
  - exact resp_thresholds_decreasing.
  - exact Hr.
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
  intros v w Hw.
  unfold coag_score.
  apply coag_score_raw_mono.
  destruct Hw as [_ [_ [_ [_ [_ [_ [_ [Hplt _]]]]]]]].
  lia.
Qed.

Lemma liver_score_mono : forall v w, worse_or_equal v w -> liver_score w >= liver_score v.
Proof.
  intros v w Hw.
  unfold liver_score.
  apply liver_score_raw_mono.
  destruct Hw as [_ [_ [_ [_ [_ [_ [_ [_ [Hbil _]]]]]]]]].
  lia.
Qed.

Lemma cns_score_mono : forall v w, worse_or_equal v w -> cns_score w >= cns_score v.
Proof.
  intros v w Hw.
  unfold cns_score.
  apply cns_score_raw_mono.
  destruct Hw as [_ [_ [_ [_ [_ [_ [Hgcs _]]]]]]].
  lia.
Qed.

Lemma creat_score_mono : forall c1 c2, c1 <= c2 -> creat_score c2 >= creat_score c1.
Proof.
  intros c1 c2 Hle.
  rewrite !creat_score_eq.
  apply score_above_mono.
  - exact creat_thresholds_decreasing.
  - exact Hle.
Qed.

Lemma urine_score_mono : forall u1 u2, u2 <= u1 -> urine_score u2 >= urine_score u1.
Proof.
  intros u1 u2 Hle.
  rewrite !urine_score_eq.
  apply score_below_mono.
  - exact urine_thresholds_decreasing.
  - exact Hle.
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

Lemma sofa_monotone : forall v w t, worse_or_equal v w -> sofa (make_state w t) >= sofa (make_state v t).
Proof.
  intros v w t Hw; unfold sofa, make_state; simpl.
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

Definition s_norm : State := make_state v_norm init_therapy.
Definition s_shock : State := make_state v_shock init_therapy.

Example decide_norm_monitor :
  p_fluids (decide_plan s_norm) = false /\
  p_antibiotics (decide_plan s_norm) = false /\
  p_pressor_lo (decide_plan s_norm) = false /\
  p_pressor_hi (decide_plan s_norm) = false /\
  p_icu (decide_plan s_norm) = false.
Proof. repeat split; reflexivity. Qed.

Example decide_shock_escalates :
  p_fluids (decide_plan s_shock) = true /\
  p_antibiotics (decide_plan s_shock) = true /\
  p_pressor_lo (decide_plan s_shock) = true /\
  p_pressor_hi (decide_plan s_shock) = true /\
  p_icu (decide_plan s_shock) = true.
Proof. repeat split; reflexivity. Qed.

Example sofa_norm_is_2 : sofa s_norm = 2.
Proof. reflexivity. Qed.

Example sofa_shock_is_13 : sofa s_shock = 13.
Proof. reflexivity. Qed.
