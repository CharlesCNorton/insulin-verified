(******************************************************************************)
(*                                                                            *)
(*                         Insulin Bolus Calculator                           *)
(*                    Verified Glycemic Control Arithmetic                    *)
(*                                                                            *)
(*     Formalizes the standard insulin bolus calculation used in insulin      *)
(*     pumps and dosing applications. Verifies correctness of carbohydrate    *)
(*     coverage, correction bolus, and insulin-on-board subtraction against   *)
(*     FDA Class III safety requirements and clinical guideline arithmetic.   *)
(*                                                                            *)
(*     "The dose makes the poison."                                           *)
(*     - Paracelsus, 1538                                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Lia.

(** ========================================================================= *)
(** PART I: BLOOD GLUCOSE                                                     *)
(** Units: mg/dL (US standard). Clinical thresholds per ADA guidelines.       *)
(** ========================================================================= *)

Module BloodGlucose.

  Definition BG_mg_dL := nat.

  Definition BG_SEVERE_HYPO : nat := 54.
  Definition BG_HYPO : nat := 70.
  Definition BG_NORMAL_LOW : nat := 70.
  Definition BG_NORMAL_HIGH : nat := 100.
  Definition BG_TARGET_DEFAULT : nat := 100.
  Definition BG_HYPER : nat := 180.
  Definition BG_SEVERE_HYPER : nat := 250.
  Definition BG_DKA_RISK : nat := 300.
  Definition BG_METER_MAX : nat := 600.

End BloodGlucose.

Export BloodGlucose.

(** Sanity: thresholds are clinically ordered. *)
Lemma thresholds_ordered :
  BG_SEVERE_HYPO < BG_HYPO /\
  BG_HYPO <= BG_NORMAL_LOW /\
  BG_NORMAL_LOW < BG_NORMAL_HIGH /\
  BG_NORMAL_HIGH <= BG_TARGET_DEFAULT /\
  BG_TARGET_DEFAULT < BG_HYPER /\
  BG_HYPER < BG_SEVERE_HYPER /\
  BG_SEVERE_HYPER < BG_DKA_RISK /\
  BG_DKA_RISK < BG_METER_MAX.
Proof. unfold BG_SEVERE_HYPO, BG_HYPO, BG_NORMAL_LOW, BG_NORMAL_HIGH,
              BG_TARGET_DEFAULT, BG_HYPER, BG_SEVERE_HYPER, BG_DKA_RISK,
              BG_METER_MAX. lia. Qed.

(** Counterexample attempt: 54 is NOT in normal range. *)
Lemma counterex_severe_hypo_not_normal :
  ~ (BG_NORMAL_LOW <= BG_SEVERE_HYPO <= BG_NORMAL_HIGH).
Proof. unfold BG_NORMAL_LOW, BG_SEVERE_HYPO, BG_NORMAL_HIGH. lia. Qed.

(** Counterexample attempt: 300 is NOT below hyperglycemia threshold. *)
Lemma counterex_dka_is_hyper :
  ~ (BG_DKA_RISK < BG_HYPER).
Proof. unfold BG_DKA_RISK, BG_HYPER. lia. Qed.

(** Clinical classification predicates. *)
Definition is_severe_hypo (bg : BG_mg_dL) : bool := bg <? BG_SEVERE_HYPO.
Definition is_hypo (bg : BG_mg_dL) : bool := bg <? BG_HYPO.
Definition is_normal (bg : BG_mg_dL) : bool := (BG_NORMAL_LOW <=? bg) && (bg <=? BG_NORMAL_HIGH).
Definition is_hyper (bg : BG_mg_dL) : bool := BG_HYPER <? bg.
Definition is_severe_hyper (bg : BG_mg_dL) : bool := BG_SEVERE_HYPER <? bg.
Definition is_dka_risk (bg : BG_mg_dL) : bool := BG_DKA_RISK <=? bg.

(** Witness: BG of 50 is severe hypoglycemia. *)
Lemma witness_50_severe_hypo : is_severe_hypo 50 = true.
Proof. reflexivity. Qed.

(** Witness: BG of 50 is also hypoglycemia (less severe includes more severe). *)
Lemma witness_50_hypo : is_hypo 50 = true.
Proof. reflexivity. Qed.

(** Witness: BG of 90 is normal. *)
Lemma witness_90_normal : is_normal 90 = true.
Proof. reflexivity. Qed.

(** Witness: BG of 200 is hyperglycemia. *)
Lemma witness_200_hyper : is_hyper 200 = true.
Proof. reflexivity. Qed.

(** Witness: BG of 350 is DKA risk. *)
Lemma witness_350_dka : is_dka_risk 350 = true.
Proof. reflexivity. Qed.

(** Counterexample: BG of 90 is NOT hypoglycemia. *)
Lemma counterex_90_not_hypo : is_hypo 90 = false.
Proof. reflexivity. Qed.

(** Counterexample: BG of 150 is NOT hyperglycemia (it's elevated but not >180). *)
Lemma counterex_150_not_hyper : is_hyper 150 = false.
Proof. reflexivity. Qed.

(** Critical safety property: severe hypo implies hypo. *)
Lemma severe_hypo_implies_hypo : forall bg,
  is_severe_hypo bg = true -> is_hypo bg = true.
Proof.
  intros bg H.
  unfold is_severe_hypo, is_hypo, BG_SEVERE_HYPO, BG_HYPO in *.
  rewrite Nat.ltb_lt in *. lia.
Qed.

(** ========================================================================= *)
(** PART II: CARBOHYDRATES                                                    *)
(** Units: grams. Typical meal range 0-150g.                                  *)
(** ========================================================================= *)

Module Carbohydrates.

  Definition Carbs_g := nat.

  Definition CARBS_ZERO : nat := 0.
  Definition CARBS_SNACK_MAX : nat := 20.
  Definition CARBS_SMALL_MEAL : nat := 30.
  Definition CARBS_MEDIUM_MEAL : nat := 60.
  Definition CARBS_LARGE_MEAL : nat := 90.
  Definition CARBS_VERY_LARGE : nat := 120.
  Definition CARBS_SANITY_MAX : nat := 200.

End Carbohydrates.

Export Carbohydrates.

(** Sanity: carb thresholds are ordered. *)
Lemma carb_thresholds_ordered :
  CARBS_ZERO < CARBS_SNACK_MAX /\
  CARBS_SNACK_MAX < CARBS_SMALL_MEAL /\
  CARBS_SMALL_MEAL < CARBS_MEDIUM_MEAL /\
  CARBS_MEDIUM_MEAL < CARBS_LARGE_MEAL /\
  CARBS_LARGE_MEAL < CARBS_VERY_LARGE /\
  CARBS_VERY_LARGE < CARBS_SANITY_MAX.
Proof. unfold CARBS_ZERO, CARBS_SNACK_MAX, CARBS_SMALL_MEAL, CARBS_MEDIUM_MEAL,
              CARBS_LARGE_MEAL, CARBS_VERY_LARGE, CARBS_SANITY_MAX. lia. Qed.

(** Witness: 45g is a reasonable meal. *)
Lemma witness_45g_reasonable :
  CARBS_SMALL_MEAL <= 45 /\ 45 <= CARBS_MEDIUM_MEAL.
Proof. unfold CARBS_SMALL_MEAL, CARBS_MEDIUM_MEAL. lia. Qed.

(** Counterexample: 250g in one meal is unreasonable. *)
Lemma counterex_250g_unreasonable :
  ~ (250 <= CARBS_SANITY_MAX).
Proof. unfold CARBS_SANITY_MAX. lia. Qed.

(** ========================================================================= *)
(** PART III: INSULIN AND PATIENT PARAMETERS                                  *)
(** Units: insulin in units (U), ICR in g/U, ISF in mg/dL per U.              *)
(** ========================================================================= *)

Module InsulinParams.

  Definition Insulin_U := nat.

  Definition ICR_MIN : nat := 5.
  Definition ICR_MAX : nat := 25.
  Definition ISF_MIN : nat := 20.
  Definition ISF_MAX : nat := 100.

  Definition BOLUS_SANITY_MAX : nat := 25.

  Record PatientParams := mkPatientParams {
    pp_icr : nat;
    pp_isf : nat;
    pp_target_bg : BG_mg_dL
  }.

  Definition params_valid (p : PatientParams) : bool :=
    (ICR_MIN <=? pp_icr p) && (pp_icr p <=? ICR_MAX) &&
    (ISF_MIN <=? pp_isf p) && (pp_isf p <=? ISF_MAX) &&
    (BG_HYPO <=? pp_target_bg p) && (pp_target_bg p <=? BG_HYPER) &&
    (1 <=? pp_icr p) && (1 <=? pp_isf p).

End InsulinParams.

Export InsulinParams.

(** Sanity: parameter bounds are ordered. *)
Lemma param_bounds_ordered :
  ICR_MIN < ICR_MAX /\ ISF_MIN < ISF_MAX.
Proof. unfold ICR_MIN, ICR_MAX, ISF_MIN, ISF_MAX. lia. Qed.

(** Witness: typical Type 1 adult params (ICR=10, ISF=50, target=100). *)
Definition witness_typical_params : PatientParams :=
  mkPatientParams 10 50 100.

Lemma witness_typical_params_valid : params_valid witness_typical_params = true.
Proof. reflexivity. Qed.

(** Witness: insulin-sensitive patient (ICR=20, ISF=80, target=100). *)
Definition witness_sensitive_params : PatientParams :=
  mkPatientParams 20 80 100.

Lemma witness_sensitive_params_valid : params_valid witness_sensitive_params = true.
Proof. reflexivity. Qed.

(** Witness: insulin-resistant patient (ICR=6, ISF=25, target=100). *)
Definition witness_resistant_params : PatientParams :=
  mkPatientParams 6 25 100.

Lemma witness_resistant_params_valid : params_valid witness_resistant_params = true.
Proof. reflexivity. Qed.

(** Counterexample: ICR of 0 is invalid (division by zero). *)
Definition counterex_zero_icr : PatientParams :=
  mkPatientParams 0 50 100.

Lemma counterex_zero_icr_invalid : params_valid counterex_zero_icr = false.
Proof. reflexivity. Qed.

(** Counterexample: ISF of 0 is invalid (division by zero). *)
Definition counterex_zero_isf : PatientParams :=
  mkPatientParams 10 0 100.

Lemma counterex_zero_isf_invalid : params_valid counterex_zero_isf = false.
Proof. reflexivity. Qed.

(** Counterexample: target BG of 50 is hypoglycemic and invalid. *)
Definition counterex_hypo_target : PatientParams :=
  mkPatientParams 10 50 50.

Lemma counterex_hypo_target_invalid : params_valid counterex_hypo_target = false.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART IV: CARB BOLUS CALCULATION                                           *)
(** Formula: carb_bolus = carbs / ICR                                         *)
(** ========================================================================= *)

Module CarbBolus.

  Definition carb_bolus (carbs : Carbs_g) (icr : nat) : nat :=
    carbs / icr.

  Definition carb_bolus_safe (carbs : Carbs_g) (icr : nat) : option nat :=
    if icr =? 0 then None
    else Some (carbs / icr).

End CarbBolus.

Export CarbBolus.

(** Witness: 60g carbs with ICR=10 yields 6 units. *)
Lemma witness_carb_bolus_60g_icr10 :
  carb_bolus 60 10 = 6.
Proof. reflexivity. Qed.

(** Witness: 45g carbs with ICR=15 yields 3 units. *)
Lemma witness_carb_bolus_45g_icr15 :
  carb_bolus 45 15 = 3.
Proof. reflexivity. Qed.

(** Witness: 0g carbs yields 0 units regardless of ICR. *)
Lemma witness_zero_carbs_zero_bolus : forall icr,
  carb_bolus 0 icr = 0.
Proof. intro icr. unfold carb_bolus. destruct icr; reflexivity. Qed.

(** Witness: safe version returns Some for valid ICR. *)
Lemma witness_carb_bolus_safe_valid :
  carb_bolus_safe 60 10 = Some 6.
Proof. reflexivity. Qed.

(** Counterexample: ICR of 0 is division by zero, safe version returns None. *)
Lemma counterex_carb_bolus_icr_zero :
  carb_bolus_safe 60 0 = None.
Proof. reflexivity. Qed.

(** Critical property: carb bolus is monotonic in carbs. *)
Lemma carb_bolus_monotonic_carbs : forall c1 c2 icr,
  icr > 0 -> c1 <= c2 -> carb_bolus c1 icr <= carb_bolus c2 icr.
Proof.
  intros c1 c2 icr Hicr Hle.
  unfold carb_bolus.
  apply Nat.div_le_mono. lia. exact Hle.
Qed.

(** Critical property: carb bolus is bounded by carbs (since ICR >= 1). *)
Lemma carb_bolus_bounded : forall carbs icr,
  icr >= 1 -> carb_bolus carbs icr <= carbs.
Proof.
  intros carbs icr Hicr.
  unfold carb_bolus.
  apply Nat.div_le_upper_bound. lia.
  nia.
Qed.

(** Critical property: more insulin-sensitive (higher ICR) means less insulin. *)
Lemma carb_bolus_antimonotonic_icr : forall carbs icr1 icr2,
  icr1 > 0 -> icr2 > 0 -> icr1 <= icr2 ->
  carb_bolus carbs icr2 <= carb_bolus carbs icr1.
Proof.
  intros carbs icr1 icr2 H1 H2 Hle.
  unfold carb_bolus.
  apply Nat.div_le_compat_l. split. exact H1. exact Hle.
Qed.

(** ========================================================================= *)
(** PART V: CORRECTION BOLUS CALCULATION                                      *)
(** Formula: correction = (current_bg - target_bg) / ISF, if bg > target.     *)
(** ========================================================================= *)

Module CorrectionBolus.

  Definition correction_bolus (current_bg target_bg : BG_mg_dL) (isf : nat) : nat :=
    if current_bg <=? target_bg then 0
    else (current_bg - target_bg) / isf.

  Definition correction_bolus_safe (current_bg target_bg : BG_mg_dL) (isf : nat) : option nat :=
    if isf =? 0 then None
    else Some (correction_bolus current_bg target_bg isf).

End CorrectionBolus.

Export CorrectionBolus.

(** Witness: BG 200, target 100, ISF 50 yields 2 units correction. *)
Lemma witness_correction_200_100_50 :
  correction_bolus 200 100 50 = 2.
Proof. reflexivity. Qed.

(** Witness: BG 150, target 100, ISF 25 yields 2 units correction. *)
Lemma witness_correction_150_100_25 :
  correction_bolus 150 100 25 = 2.
Proof. reflexivity. Qed.

(** Witness: BG at target yields 0 correction. *)
Lemma witness_correction_at_target :
  correction_bolus 100 100 50 = 0.
Proof. reflexivity. Qed.

(** Witness: BG below target yields 0 correction (no negative insulin). *)
Lemma witness_correction_below_target :
  correction_bolus 80 100 50 = 0.
Proof. reflexivity. Qed.

(** Counterexample: ISF of 0 returns None in safe version. *)
Lemma counterex_correction_isf_zero :
  correction_bolus_safe 200 100 0 = None.
Proof. reflexivity. Qed.

(** Critical safety: correction is 0 when BG <= target. *)
Lemma correction_zero_when_at_or_below_target : forall bg target isf,
  bg <= target -> correction_bolus bg target isf = 0.
Proof.
  intros bg target isf Hle.
  unfold correction_bolus.
  destruct (bg <=? target) eqn:E.
  - reflexivity.
  - rewrite Nat.leb_gt in E. lia.
Qed.

(** Critical property: correction is monotonic in BG. *)
Lemma correction_monotonic_bg : forall bg1 bg2 target isf,
  isf > 0 -> bg1 <= bg2 ->
  correction_bolus bg1 target isf <= correction_bolus bg2 target isf.
Proof.
  intros bg1 bg2 target isf Hisf Hle.
  unfold correction_bolus.
  destruct (bg1 <=? target) eqn:E1; destruct (bg2 <=? target) eqn:E2.
  - lia.
  - apply Nat.le_0_l.
  - apply Nat.leb_nle in E1. apply Nat.leb_le in E2. lia.
  - apply Nat.leb_nle in E1. apply Nat.leb_nle in E2.
    apply Nat.div_le_mono. lia. lia.
Qed.

(** Critical property: higher ISF (more sensitive) means less correction. *)
Lemma correction_antimonotonic_isf : forall bg target isf1 isf2,
  isf1 > 0 -> isf2 > 0 -> isf1 <= isf2 ->
  correction_bolus bg target isf2 <= correction_bolus bg target isf1.
Proof.
  intros bg target isf1 isf2 H1 H2 Hle.
  unfold correction_bolus.
  destruct (bg <=? target); [lia|].
  apply Nat.div_le_compat_l. split. exact H1. exact Hle.
Qed.

(** ========================================================================= *)
(** PART VI: INSULIN ON BOARD (IOB)                                           *)
(** Active insulin from previous doses, modeled as simple subtraction.        *)
(** ========================================================================= *)

Module InsulinOnBoard.

  Definition IOB := nat.

  Definition subtract_iob (bolus iob : nat) : nat :=
    if bolus <=? iob then 0 else bolus - iob.

End InsulinOnBoard.

Export InsulinOnBoard.

(** Witness: 5 units bolus minus 2 IOB yields 3 units. *)
Lemma witness_iob_subtraction :
  subtract_iob 5 2 = 3.
Proof. reflexivity. Qed.

(** Witness: IOB >= bolus yields 0 (no insulin given). *)
Lemma witness_iob_exceeds_bolus :
  subtract_iob 3 5 = 0.
Proof. reflexivity. Qed.

(** Witness: zero IOB means full bolus. *)
Lemma witness_zero_iob :
  subtract_iob 5 0 = 5.
Proof. reflexivity. Qed.

(** Critical safety: result is always <= original bolus. *)
Lemma iob_subtraction_bounded : forall bolus iob,
  subtract_iob bolus iob <= bolus.
Proof.
  intros bolus iob.
  unfold subtract_iob.
  destruct (bolus <=? iob) eqn:E; lia.
Qed.

(** Critical safety: result is always non-negative (guaranteed by nat). *)
Lemma iob_subtraction_nonneg : forall bolus iob,
  0 <= subtract_iob bolus iob.
Proof. intros. lia. Qed.

(** ========================================================================= *)
(** PART VII: COMPLETE BOLUS CALCULATOR                                       *)
(** total_bolus = carb_bolus + correction_bolus - IOB                         *)
(** ========================================================================= *)

Module BolusCalculator.

  Record BolusInput := mkBolusInput {
    bi_carbs : Carbs_g;
    bi_current_bg : BG_mg_dL;
    bi_iob : IOB
  }.

  Definition calculate_bolus (input : BolusInput) (params : PatientParams) : nat :=
    let carb := carb_bolus (bi_carbs input) (pp_icr params) in
    let corr := correction_bolus (bi_current_bg input) (pp_target_bg params) (pp_isf params) in
    let total := carb + corr in
    subtract_iob total (bi_iob input).

  Definition calculate_bolus_safe (input : BolusInput) (params : PatientParams) : option nat :=
    if negb (params_valid params) then None
    else Some (calculate_bolus input params).

End BolusCalculator.

Export BolusCalculator.

(** Witness: 60g carbs, BG 150, target 100, ICR 10, ISF 50, IOB 0. *)
(** Expected: 6 (carb) + 1 (correction) - 0 (IOB) = 7 units. *)
Definition witness_input_1 : BolusInput := mkBolusInput 60 150 0.

Lemma witness_bolus_calculation_1 :
  calculate_bolus witness_input_1 witness_typical_params = 7.
Proof. reflexivity. Qed.

(** Witness: 45g carbs, BG 100 (at target), ICR 10, ISF 50, IOB 0. *)
(** Expected: 4 (carb) + 0 (no correction) - 0 = 4 units. *)
Definition witness_input_2 : BolusInput := mkBolusInput 45 100 0.

Lemma witness_bolus_calculation_2 :
  calculate_bolus witness_input_2 witness_typical_params = 4.
Proof. reflexivity. Qed.

(** Witness: 60g carbs, BG 200, ICR 10, ISF 50, IOB 3. *)
(** Expected: 6 (carb) + 2 (correction) - 3 (IOB) = 5 units. *)
Definition witness_input_3 : BolusInput := mkBolusInput 60 200 3.

Lemma witness_bolus_calculation_3 :
  calculate_bolus witness_input_3 witness_typical_params = 5.
Proof. reflexivity. Qed.

(** Witness: IOB exceeds calculated bolus, result is 0. *)
Definition witness_input_high_iob : BolusInput := mkBolusInput 30 100 10.

Lemma witness_high_iob_yields_zero :
  calculate_bolus witness_input_high_iob witness_typical_params = 0.
Proof. reflexivity. Qed.

(** Counterexample: invalid params returns None. *)
Lemma counterex_invalid_params_none :
  calculate_bolus_safe witness_input_1 counterex_zero_icr = None.
Proof. reflexivity. Qed.

(** Critical safety: bolus is bounded when IOB is subtracted. *)
Lemma bolus_never_exceeds_raw : forall input params,
  calculate_bolus input params <=
    carb_bolus (bi_carbs input) (pp_icr params) +
    correction_bolus (bi_current_bg input) (pp_target_bg params) (pp_isf params).
Proof.
  intros input params.
  unfold calculate_bolus.
  apply iob_subtraction_bounded.
Qed.

(** ========================================================================= *)
(** PART VIII: HYPOGLYCEMIA SAFETY                                            *)
(** The critical theorem: correction bolus cannot push BG below target.       *)
(** ========================================================================= *)

Module HypoglycemiaSafety.

  Definition predicted_bg_after_correction (current_bg target_bg isf : nat) : nat :=
    let corr := correction_bolus current_bg target_bg isf in
    current_bg - corr * isf.

  Definition correction_is_safe (current_bg target_bg isf : nat) : Prop :=
    predicted_bg_after_correction current_bg target_bg isf >= target_bg.

End HypoglycemiaSafety.

Export HypoglycemiaSafety.

(** Witness: BG 200, target 100, ISF 50. Correction = 2. Predicted = 200 - 100 = 100. *)
Lemma witness_predicted_bg_200_100_50 :
  predicted_bg_after_correction 200 100 50 = 100.
Proof. reflexivity. Qed.

(** Witness: BG 150, target 100, ISF 50. Correction = 1. Predicted = 150 - 50 = 100. *)
Lemma witness_predicted_bg_150_100_50 :
  predicted_bg_after_correction 150 100 50 = 100.
Proof. reflexivity. Qed.

(** Witness: BG at target, no correction, predicted = current. *)
Lemma witness_predicted_bg_at_target :
  predicted_bg_after_correction 100 100 50 = 100.
Proof. reflexivity. Qed.

(** Witness: BG below target, no correction, predicted = current. *)
Lemma witness_predicted_bg_below_target :
  predicted_bg_after_correction 80 100 50 = 80.
Proof. reflexivity. Qed.

(** CRITICAL SAFETY THEOREM: Correction bolus never pushes BG below target. *)
Theorem correction_never_causes_hypoglycemia : forall current_bg target_bg isf,
  isf > 0 ->
  target_bg > 0 ->
  predicted_bg_after_correction current_bg target_bg isf >= target_bg \/
  current_bg <= target_bg.
Proof.
  intros current_bg target_bg isf Hisf Htarget.
  unfold predicted_bg_after_correction, correction_bolus.
  destruct (current_bg <=? target_bg) eqn:E.
  - right. apply Nat.leb_le in E. exact E.
  - left. apply Nat.leb_nle in E.
    assert (Hdiv : isf * ((current_bg - target_bg) / isf) <= current_bg - target_bg).
    { apply Nat.mul_div_le. lia. }
    lia.
Qed.

(** Corollary: If BG >= target and params valid, predicted BG >= target. *)
Corollary correction_safe_when_above_target : forall current_bg target_bg isf,
  isf > 0 ->
  current_bg >= target_bg ->
  predicted_bg_after_correction current_bg target_bg isf >= target_bg.
Proof.
  intros current_bg target_bg isf Hisf Habove.
  unfold predicted_bg_after_correction, correction_bolus.
  destruct (current_bg <=? target_bg) eqn:E.
  - apply Nat.leb_le in E. lia.
  - apply Nat.leb_nle in E.
    assert (Hdiv : isf * ((current_bg - target_bg) / isf) <= current_bg - target_bg).
    { apply Nat.mul_div_le. lia. }
    lia.
Qed.

(** Corollary: With valid params, target >= BG_HYPO, so predicted >= BG_HYPO. *)
Corollary correction_never_causes_severe_hypo : forall current_bg params,
  params_valid params = true ->
  current_bg >= pp_target_bg params ->
  predicted_bg_after_correction current_bg (pp_target_bg params) (pp_isf params) >= BG_HYPO.
Proof.
  intros current_bg params Hvalid Habove.
  unfold params_valid in Hvalid.
  repeat rewrite andb_true_iff in Hvalid.
  destruct Hvalid as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  apply Nat.leb_le in H5. apply Nat.leb_le in H8.
  assert (Hisf_pos : pp_isf params > 0) by lia.
  assert (Hpred : predicted_bg_after_correction current_bg (pp_target_bg params) (pp_isf params)
                  >= pp_target_bg params).
  { apply correction_safe_when_above_target. exact Hisf_pos. exact Habove. }
  lia.
Qed.
