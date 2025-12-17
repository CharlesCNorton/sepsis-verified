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

(** Vital signs and labs, discretized. *)
Record Vitals := {
  temp10      : nat;   (* temperature: tenths of °C, e.g., 383 = 38.3°C *)
  hr          : nat;   (* heart rate: beats per minute *)
  rr          : nat;   (* respiratory rate: breaths per minute *)
  sbp         : nat;   (* systolic blood pressure: mmHg *)
  map_mm      : nat;   (* mean arterial pressure: mmHg *)
  lact10      : nat;   (* lactate: mmol/L × 10, e.g., 20 = 2.0 mmol/L *)
  gcs         : nat;   (* Glasgow Coma Scale: 3-15 *)
  platelets   : nat;   (* platelet count: ×10³/µL *)
  bilir10     : nat;   (* bilirubin: mg/dL × 10, e.g., 12 = 1.2 mg/dL *)
  creat10     : nat;   (* creatinine: mg/dL × 10, e.g., 11 = 1.1 mg/dL *)
  urine_ml_6hr : nat;  (* urine output: mL in last 6 hours (SOFA standard window) *)
  pao2        : nat;   (* arterial O2 pressure: mmHg *)
  fio2_pct    : nat;   (* fraction inspired O2: percent 1-100 *)
  infection   : bool;  (* suspected or confirmed infection *)
  weight_kg   : nat    (* patient weight: kilograms *)
}.

(** GCS validity: must be in range [3,15]. *)
Definition gcs_valid (g : nat) : bool := (3 <=? g) && (g <=? 15).

Definition vitals_valid (v : Vitals) : bool :=
  gcs_valid (gcs v) &&
  (1 <=? fio2_pct v) && (fio2_pct v <=? 100) &&
  (0 <? weight_kg v).

Lemma gcs_valid_bounds : forall g, gcs_valid g = true -> 3 <= g /\ g <= 15.
Proof.
  intros g Hv.
  unfold gcs_valid in Hv.
  apply andb_prop in Hv as [Hlo Hhi].
  apply Nat.leb_le in Hlo.
  apply Nat.leb_le in Hhi.
  lia.
Qed.

(** Time representation: minutes since presentation. *)
Definition Time := nat.

Record Therapy := {
  fluids_on         : bool;
  fluids_start_time : option Time;
  fluids_ml         : nat;   (* total crystalloid volume administered: mL *)
  antibiotics_on    : bool;
  abx_start_time    : option Time;
  dopamine_mcg      : nat;   (* dopamine dose: mcg/kg/min × 10 *)
  dobutamine_on     : bool;  (* any dobutamine *)
  norepinephrine_mcg : nat;  (* norepinephrine dose: mcg/kg/min × 100 *)
  epinephrine_mcg   : nat;   (* epinephrine dose: mcg/kg/min × 100 *)
  icu_transfer      : bool
}.

Definition init_therapy : Therapy :=
  {| fluids_on := false; fluids_start_time := None; fluids_ml := 0;
     antibiotics_on := false; abx_start_time := None;
     dopamine_mcg := 0; dobutamine_on := false;
     norepinephrine_mcg := 0; epinephrine_mcg := 0;
     icu_transfer := false |}.

(** Vasopressor categories per SOFA CV criteria. *)
Definition on_low_dose_pressor (t : Therapy) : bool :=
  (dopamine_mcg t <=? 50) && (0 <? dopamine_mcg t) || dobutamine_on t.

Definition on_medium_dose_pressor (t : Therapy) : bool :=
  (50 <? dopamine_mcg t) ||
  ((0 <? norepinephrine_mcg t) && (norepinephrine_mcg t <=? 10)) ||
  ((0 <? epinephrine_mcg t) && (epinephrine_mcg t <=? 10)).

Definition on_high_dose_pressor (t : Therapy) : bool :=
  (150 <? dopamine_mcg t) ||
  (10 <? norepinephrine_mcg t) ||
  (10 <? epinephrine_mcg t).

(** Sepsis-3 fluid resuscitation target: 30 mL/kg crystalloid. *)
Definition fluid_target_ml (v : Vitals) : nat := weight_kg v * 30.

Definition fluid_resuscitation_complete (v : Vitals) (t : Therapy) : bool :=
  fluid_target_ml v <=? fluids_ml t.

Definition fluid_resuscitation_progress (v : Vitals) (t : Therapy) : nat :=
  let target := fluid_target_ml v in
  if target =? 0 then 100 else (fluids_ml t * 100) / target.

Lemma fluid_complete_iff_target_met :
  forall v t, fluid_resuscitation_complete v t = true <-> fluids_ml t >= fluid_target_ml v.
Proof.
  intros v t.
  unfold fluid_resuscitation_complete.
  split.
  - intro H.
    apply Nat.leb_le in H.
    exact H.
  - intro H.
    apply Nat.leb_le.
    exact H.
Qed.

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

(** Tactic to prove scores_decreasing for concrete threshold lists. *)
Ltac prove_scores_decreasing :=
  simpl;
  repeat split;
  intros t' s' Hin;
  repeat match goal with
  | Hin : _ \/ _ |- _ => destruct Hin as [Hin | Hin]
  | Hin : ?x = ?y |- _ => injection Hin; intros; lia
  | Hin : False |- _ => contradiction
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

(** P/F ratio calculation. FiO2 is given as percent (1-100), so the formula
    (pao2 * 100) / fio2_pct yields the standard P/F ratio. Integer division
    truncates; maximum error is < 1 unit (clinically negligible vs 100-unit
    threshold granularity). *)
Definition pf_ratio (pao2_val fio2_val : nat) : nat :=
  let fio2 := max1 fio2_val in
  (pao2_val * 100) / fio2.

Definition resp_score (v:Vitals) : nat :=
  resp_bucket (pf_ratio (pao2 v) (fio2_pct v)).

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

(** Urine output scoring per SOFA using 6-hour windows.
    SOFA criteria: <200 mL/day = 4, <500 mL/day = 3.
    6-hour equivalents: <50 mL/6hr = 4, <125 mL/6hr = 3, <200 mL/6hr = 2. *)
Definition urine_score (u:nat) : nat :=
  if u <? 50 then 4
  else if u <? 125 then 3
  else if u <? 200 then 2
  else if u <? 300 then 1
  else 0.

Definition urine_thresholds : list (nat * nat) :=
  (50, 4) :: (125, 3) :: (200, 2) :: (300, 1) :: nil.

Lemma urine_score_eq : forall u, urine_score u = score_below_thresholds u urine_thresholds.
Proof.
  intro u.
  unfold urine_score, urine_thresholds, score_below_thresholds.
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
  Nat.max (creat_score (creat10 v)) (urine_score (urine_ml_6hr v)).

(** SOFA CV score using vasopressor dose thresholds. *)
Definition cv_score (v:Vitals) (t:Therapy) : nat :=
  if on_high_dose_pressor t then 4
  else if on_medium_dose_pressor t then 3
  else if on_low_dose_pressor t then 2
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

(** NEWS-based clinical response thresholds. *)
Definition news_low_risk (v : Vitals) : bool := news v <=? 4.
Definition news_medium_risk (v : Vitals) : bool := (5 <=? news v) && (news v <=? 6).
Definition news_high_risk (v : Vitals) : bool := 7 <=? news v.

(** NEWS triggers urgent review if score >= 5 or any single parameter scores 3. *)
Definition news_triggers_urgent_review (v : Vitals) : bool :=
  (5 <=? news v) ||
  (news_rr v =? 3) || (news_hr v =? 3) || (news_sbp v =? 3) || (news_gcs v =? 3).

Lemma news_high_implies_urgent :
  forall v, news_high_risk v = true -> news_triggers_urgent_review v = true.
Proof.
  intros v Hhigh.
  unfold news_triggers_urgent_review, news_high_risk in *.
  apply Nat.leb_le in Hhigh.
  assert (H : 5 <=? news v = true).
  { apply Nat.leb_le. lia. }
  rewrite H.
  reflexivity.
Qed.

(** Sepsis / shock predicates *)
Definition sepsis (s:State) : bool :=
  infection (vit s) && ge_bool (sofa s) 2.

Definition septic_shock (s:State) : bool :=
  infection (vit s) &&
  ge_bool (sofa s) 2 &&
  (map_mm (vit s) <=? 65) &&
  (ge_bool (lact10 (vit s)) 20).

(** Witness: patient meeting all septic shock criteria. *)
Definition v_shock_witness : Vitals :=
  {| temp10 := 390; hr := 120; rr := 28; sbp := 80; map_mm := 60; lact10 := 25;
     gcs := 14; platelets := 80; bilir10 := 15; creat10 := 25; urine_ml_6hr := 30;
     pao2 := 70; fio2_pct := 40; infection := true; weight_kg := 70 |}.

Lemma septic_shock_witness_satisfies :
  septic_shock (make_state v_shock_witness init_therapy) = true.
Proof. reflexivity. Qed.

Lemma septic_shock_witness_has_infection :
  infection v_shock_witness = true.
Proof. reflexivity. Qed.

Lemma septic_shock_witness_has_hypotension :
  map_mm v_shock_witness <= 65.
Proof. simpl. lia. Qed.

Lemma septic_shock_witness_has_elevated_lactate :
  lact10 v_shock_witness >= 20.
Proof. simpl. lia. Qed.

(** Counterexample: high lactate and hypotension but NO infection => not septic shock. *)
Definition v_not_septic : Vitals :=
  {| temp10 := 390; hr := 120; rr := 28; sbp := 80; map_mm := 60; lact10 := 25;
     gcs := 14; platelets := 80; bilir10 := 15; creat10 := 25; urine_ml_6hr := 30;
     pao2 := 70; fio2_pct := 40; infection := false; weight_kg := 70 |}.

Lemma not_septic_despite_shock_physiology :
  septic_shock (make_state v_not_septic init_therapy) = false.
Proof. reflexivity. Qed.

Lemma not_septic_counterexample_reason :
  infection v_not_septic = false /\
  map_mm v_not_septic <= 65 /\
  lact10 v_not_septic >= 20.
Proof.
  unfold v_not_septic.
  simpl.
  lia.
Qed.

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

(** Helper: any vasopressor currently running. *)
Definition any_pressor (t : Therapy) : bool :=
  on_low_dose_pressor t || on_medium_dose_pressor t || on_high_dose_pressor t.

(** Clinical indications based purely on vitals (independent of current therapy). *)
Definition fluids_indicated (v : Vitals) : bool :=
  (map_mm v <=? 65) || (20 <=? lact10 v).

Definition antibiotics_indicated (v : Vitals) : bool :=
  infection v.

Definition pressor_indicated (v : Vitals) : bool :=
  map_mm v <=? 65.

Definition icu_indicated (v : Vitals) : bool :=
  map_mm v <=? 60.

(** Final plan: indication OR already receiving therapy (no de-escalation). *)
Definition decide_plan (s:State) : Plan :=
  let v := vit s in
  let t := th s in
  let flu := fluids_indicated v || fluids_on t in
  let abx := antibiotics_indicated v || antibiotics_on t in
  let plo := (pressor_indicated v && flu) || any_pressor t in
  let phi := (icu_indicated v && plo) || on_medium_dose_pressor t || on_high_dose_pressor t in
  let icu := (icu_indicated v && phi) || on_high_dose_pressor t in
  {| p_fluids := flu;
     p_antibiotics := abx;
     p_pressor_lo := plo;
     p_pressor_hi := phi;
     p_icu := icu |}.

Lemma fluids_indicated_correct :
  forall v, fluids_indicated v = true <-> map_mm v <= 65 \/ lact10 v >= 20.
Proof.
  intro v.
  unfold fluids_indicated.
  split.
  - intro H.
    apply Bool.orb_true_iff in H.
    destruct H as [Hmap | Hlact].
    + left.
      apply Nat.leb_le in Hmap.
      exact Hmap.
    + right.
      apply Nat.leb_le in Hlact.
      exact Hlact.
  - intro H.
    apply Bool.orb_true_iff.
    destruct H as [Hmap | Hlact].
    + left.
      apply Nat.leb_le.
      exact Hmap.
    + right.
      apply Nat.leb_le.
      exact Hlact.
Qed.

(** Determinism / totality *)
Lemma decide_plan_total : forall s, exists p, decide_plan s = p.
Proof.
  intros.
  eexists.
  reflexivity.
Qed.

Lemma decide_plan_deterministic : forall s p1 p2, decide_plan s = p1 -> decide_plan s = p2 -> p1 = p2.
Proof.
  intros s p1 p2 H1 H2.
  congruence.
Qed.

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
  urine_ml_6hr w <= urine_ml_6hr v /\
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
  unfold resp_score, pf_ratio.
  set (d1 := max1 (fio2_pct v)).
  set (d2 := max1 (fio2_pct w)).
  assert (Hd1pos : d1 > 0) by (unfold d1, max1; destruct (fio2_pct v); simpl; lia).
  assert (Hd1le : d1 <= d2).
  { unfold d1, d2, max1 in *.
    destruct (fio2_pct v) eqn:Hv; destruct (fio2_pct w) eqn:Hw'; simpl in *; lia. }
  set (r1 := (pao2 v * 100) / d1).
  set (r2 := (pao2 w * 100) / d2).
  assert (Hd1nz : d1 <> 0) by lia.
  assert (Hstep1 : r2 <= (pao2 w * 100) / d1).
  { unfold r2.
    apply Nat.div_le_compat_l.
    lia. }
  assert (Hstep2 : (pao2 w * 100) / d1 <= r1).
  { unfold r1.
    apply Nat.Div0.div_le_mono.
    lia. }
  apply resp_bucket_mono.
  lia.
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
  assert (Hu : urine_score (urine_ml_6hr w) >= urine_score (urine_ml_6hr v)).
  { apply (@urine_score_mono (urine_ml_6hr v) (urine_ml_6hr w)); lia. }
  apply Nat.max_lub.
  - eapply Nat.le_trans; [apply Hc | apply Nat.le_max_l].
  - eapply Nat.le_trans; [apply Hu | apply Nat.le_max_r].
Qed.

Lemma cv_score_mono : forall v w t, map_mm w <= map_mm v -> cv_score w t >= cv_score v t.
Proof.
  intros v w t Hm.
  unfold cv_score.
  destruct (on_high_dose_pressor t).
  - lia.
  - destruct (on_medium_dose_pressor t).
    + lia.
    + destruct (on_low_dose_pressor t).
      * lia.
      * destruct (map_mm v <? 70) eqn:Hv.
        -- apply Nat.ltb_lt in Hv as Hvlt.
           assert (Hwlt : map_mm w <? 70 = true).
           { apply Nat.ltb_lt. lia. }
           rewrite Hwlt.
           lia.
        -- assert (Hvge : map_mm v >= 70).
           { apply Nat.ltb_ge. exact Hv. }
           destruct (map_mm w <? 70) eqn:Hw.
           ++ apply Nat.ltb_lt in Hw as Hwlt.
              lia.
           ++ assert (Hwge : map_mm w >= 70).
              { apply Nat.ltb_ge. exact Hw. }
              lia.
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
Proof.
  intros s H.
  unfold decide_plan, antibiotics_indicated.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma plan_fluids_if_hypotension_or_lactate :
  forall s, (map_mm (vit s) <= 65 \/ lact10 (vit s) >= 20) -> p_fluids (decide_plan s) = true.
Proof.
  intros s Hind.
  unfold decide_plan.
  simpl.
  assert (Hfi : fluids_indicated (vit s) = true).
  { apply fluids_indicated_correct. exact Hind. }
  rewrite Hfi.
  reflexivity.
Qed.

Lemma plan_escalates_on_shock :
  forall s, septic_shock s = true -> p_pressor_lo (decide_plan s) = true.
Proof.
  intros s Hshock.
  unfold septic_shock in Hshock.
  apply andb_prop in Hshock as [Hinf Hlac20].
  apply andb_prop in Hinf as [Hinf Hmap].
  apply andb_prop in Hinf as [Hinf Hsofa].
  unfold decide_plan, pressor_indicated, fluids_indicated.
  simpl.
  rewrite Hmap.
  simpl.
  reflexivity.
Qed.

(** Examples *)
Definition v_norm : Vitals :=
  {| temp10 := 370; hr := 72; rr := 14; sbp := 120; map_mm := 85; lact10 := 12;
     gcs := 15; platelets := 250; bilir10 := 8; creat10 := 10; urine_ml_6hr := 300;
     pao2 := 90; fio2_pct := 21; infection := false; weight_kg := 70 |}.

Definition v_shock : Vitals :=
  {| temp10 := 392; hr := 140; rr := 32; sbp := 85; map_mm := 55; lact10 := 45;
     gcs := 13; platelets := 90; bilir10 := 25; creat10 := 40; urine_ml_6hr := 30;
     pao2 := 60; fio2_pct := 50; infection := true; weight_kg := 70 |}.

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

Example sofa_norm_low : sofa s_norm <= 2.
Proof. vm_compute. lia. Qed.

Example sofa_shock_high : sofa s_shock >= 10.
Proof. vm_compute. lia. Qed.

Example fluid_target_70kg : fluid_target_ml v_norm = 2100.
Proof. reflexivity. Qed.

Example fluid_complete_after_bolus :
  let t := {| fluids_on := true; fluids_start_time := Some 0; fluids_ml := 2100;
              antibiotics_on := false; abx_start_time := None;
              dopamine_mcg := 0; dobutamine_on := false;
              norepinephrine_mcg := 0; epinephrine_mcg := 0;
              icu_transfer := false |} in
  fluid_resuscitation_complete v_norm t = true.
Proof. reflexivity. Qed.

Example fluid_incomplete_partial :
  let t := {| fluids_on := true; fluids_start_time := Some 0; fluids_ml := 1000;
              antibiotics_on := false; abx_start_time := None;
              dopamine_mcg := 0; dobutamine_on := false;
              norepinephrine_mcg := 0; epinephrine_mcg := 0;
              icu_transfer := false |} in
  fluid_resuscitation_complete v_norm t = false.
Proof. reflexivity. Qed.
