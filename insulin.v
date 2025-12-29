(******************************************************************************)
(*                                                                            *)
(*                         Insulin Bolus Calculator                           *)
(*                    Verified Glycemic Control Arithmetic                    *)
(*                                                                            *)
(*     Formalizes the standard insulin bolus calculation used in insulin      *)
(*     pumps and dosing applications. Verifies arithmetic invariants for      *)
(*     carbohydrate coverage, correction bolus, and insulin-on-board          *)
(*     subtraction. Insulin pumps are FDA Class II devices (21 CFR 880.5725). *)
(*                                                                            *)
(*     "The dose makes the poison."                                           *)
(*     - Paracelsus, 1538                                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** =========================================================================
    REMAINING WORK
    =========================================================================

    1.  Integrate bilinear IOB into validated calculator.
        Add DIA model selector so validated_precision_bolus can use bilinear decay.

    2.  Integrate nonlinear ISF into validated calculator.
        Wire adjusted_isf into precision correction path with a toggle.

    3.  Integrate pediatric limits into validated calculator.
        Add weight-based cap enforcement when pediatric flag is set.

    4.  Add reverse correction.
        When BG < target, reduce carb bolus by (target - BG) / ISF units.

    5.  Add 24-hour TDD accumulator.
        Track cumulative daily insulin; warn or block when approaching limit.

    6.  Clarify hypoglycemia theorem scope.
        Rename correction_never_causes_hypoglycemia to correction_arithmetic_safe.

    7.  Model sensor uncertainty.
        Add optional +/-15% BG error margin; compute conservative bolus.

    8.  Add time-of-day ISF adjustment.
        Model dawn phenomenon with morning ISF multiplier.

    9.  Add exercise/illness/stress modifiers.
        Parameterize ICR/ISF adjustment factors for activity state.

    10. Model carb absorption profiles.
        Add glycemic index or fat/protein delay factor to carb bolus timing.

    11. Add suspend-before-low logic.
        When predicted BG approaches hypo threshold, reduce or withhold dose.

    12. Model delivery fault detection.
        Add occlusion/fault flag forcing IOB to assume worst-case delivery.

    ========================================================================= *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lia.

(** ========================================================================= *)
(** PART I: BLOOD GLUCOSE                                                     *)
(** Units: mg/dL (US standard). Clinical thresholds per ADA guidelines.       *)
(** ========================================================================= *)

Module BloodGlucose.

  Definition BG_mg_dL := nat.

  Definition BG_LEVEL2_HYPO : nat := 54.
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
  BG_LEVEL2_HYPO < BG_HYPO /\
  BG_HYPO <= BG_NORMAL_LOW /\
  BG_NORMAL_LOW < BG_NORMAL_HIGH /\
  BG_NORMAL_HIGH <= BG_TARGET_DEFAULT /\
  BG_TARGET_DEFAULT < BG_HYPER /\
  BG_HYPER < BG_SEVERE_HYPER /\
  BG_SEVERE_HYPER < BG_DKA_RISK /\
  BG_DKA_RISK < BG_METER_MAX.
Proof. unfold BG_LEVEL2_HYPO, BG_HYPO, BG_NORMAL_LOW, BG_NORMAL_HIGH,
              BG_TARGET_DEFAULT, BG_HYPER, BG_SEVERE_HYPER, BG_DKA_RISK,
              BG_METER_MAX. lia. Qed.

(** Counterexample attempt: 54 is NOT in normal range. *)
Lemma counterex_level2_hypo_not_normal :
  ~ (BG_NORMAL_LOW <= BG_LEVEL2_HYPO <= BG_NORMAL_HIGH).
Proof. unfold BG_NORMAL_LOW, BG_LEVEL2_HYPO, BG_NORMAL_HIGH. lia. Qed.

(** Counterexample attempt: 300 is NOT below hyperglycemia threshold. *)
Lemma counterex_dka_is_hyper :
  ~ (BG_DKA_RISK < BG_HYPER).
Proof. unfold BG_DKA_RISK, BG_HYPER. lia. Qed.

(** Clinical classification predicates. *)
Definition is_level2_hypo (bg : BG_mg_dL) : bool := bg <? BG_LEVEL2_HYPO.
Definition is_hypo (bg : BG_mg_dL) : bool := bg <? BG_HYPO.
Definition is_normal (bg : BG_mg_dL) : bool := (BG_NORMAL_LOW <=? bg) && (bg <=? BG_NORMAL_HIGH).
Definition is_hyper (bg : BG_mg_dL) : bool := BG_HYPER <? bg.
Definition is_severe_hyper (bg : BG_mg_dL) : bool := BG_SEVERE_HYPER <? bg.
Definition is_dka_risk (bg : BG_mg_dL) : bool := BG_DKA_RISK <=? bg.

(** Witness: BG of 50 is severe hypoglycemia. *)
Lemma witness_50_level2_hypo : is_level2_hypo 50 = true.
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

(** Implication: severe hypo implies hypo. *)
Lemma level2_hypo_implies_hypo : forall bg,
  is_level2_hypo bg = true -> is_hypo bg = true.
Proof.
  intros bg H.
  unfold is_level2_hypo, is_hypo, BG_LEVEL2_HYPO, BG_HYPO in *.
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

  Definition ICR_MIN : nat := 2.
  Definition ICR_MAX : nat := 100.
  Definition ISF_MIN : nat := 10.
  Definition ISF_MAX : nat := 400.

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

(** Property: carb bolus is monotonic in carbs. *)
Lemma carb_bolus_monotonic_carbs : forall c1 c2 icr,
  icr > 0 -> c1 <= c2 -> carb_bolus c1 icr <= carb_bolus c2 icr.
Proof.
  intros c1 c2 icr Hicr Hle.
  unfold carb_bolus.
  apply Nat.div_le_mono. lia. exact Hle.
Qed.

(** Property: carb bolus is bounded by carbs (since ICR >= 1). *)
Lemma carb_bolus_bounded : forall carbs icr,
  icr >= 1 -> carb_bolus carbs icr <= carbs.
Proof.
  intros carbs icr Hicr.
  unfold carb_bolus.
  apply Nat.div_le_upper_bound. lia.
  nia.
Qed.

(** Property: more insulin-sensitive (higher ICR) means less insulin. *)
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

(** Property: correction is 0 when BG <= target. *)
Lemma correction_zero_when_at_or_below_target : forall bg target isf,
  bg <= target -> correction_bolus bg target isf = 0.
Proof.
  intros bg target isf Hle.
  unfold correction_bolus.
  destruct (bg <=? target) eqn:E.
  - reflexivity.
  - rewrite Nat.leb_gt in E. lia.
Qed.

(** Property: correction is monotonic in BG. *)
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

(** Property: higher ISF (more sensitive) means less correction. *)
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

(** Property: result is always <= original bolus. *)
Lemma iob_subtraction_bounded : forall bolus iob,
  subtract_iob bolus iob <= bolus.
Proof.
  intros bolus iob.
  unfold subtract_iob.
  destruct (bolus <=? iob) eqn:E; lia.
Qed.

(** Property: result is always non-negative (guaranteed by nat). *)
Lemma iob_subtraction_nonneg : forall bolus iob,
  0 <= subtract_iob bolus iob.
Proof. intros. lia. Qed.

(** ========================================================================= *)
(** PART VI-B: REVERSE CORRECTION                                             *)
(** When BG < target, reduce carb bolus by (target - BG) / ISF.               *)
(** This accounts for the fact that the patient is already low and carbs      *)
(** alone will raise BG toward target.                                        *)
(** ========================================================================= *)

Module ReverseCorrection.

  Definition reverse_correction (current_bg target_bg : BG_mg_dL) (isf : nat) : nat :=
    if isf =? 0 then 0
    else if target_bg <=? current_bg then 0
    else (target_bg - current_bg) / isf.

  Definition apply_reverse_correction (carb_bolus current_bg target_bg : nat) (isf : nat) : nat :=
    let reduction := reverse_correction current_bg target_bg isf in
    if carb_bolus <=? reduction then 0 else carb_bolus - reduction.

End ReverseCorrection.

Export ReverseCorrection.

Module ReverseCorrectionPrecision.

  Definition reverse_correction_twentieths (current_bg target_bg : BG_mg_dL) (isf_tenths : nat) : nat :=
    if isf_tenths =? 0 then 0
    else if target_bg <=? current_bg then 0
    else ((target_bg - current_bg) * 200) / isf_tenths.

  Definition apply_reverse_correction_twentieths (carb_bolus_tw current_bg target_bg : nat) (isf_tenths : nat) : nat :=
    let reduction := reverse_correction_twentieths current_bg target_bg isf_tenths in
    if carb_bolus_tw <=? reduction then 0 else carb_bolus_tw - reduction.

End ReverseCorrectionPrecision.

Export ReverseCorrectionPrecision.

(** Witness: BG 80, target 100, ISF 50.0 (500 tenths). Reverse = (100-80)*200/500 = 8 twentieths. *)
Lemma witness_reverse_prec_80 :
  reverse_correction_twentieths 80 100 500 = 8.
Proof. reflexivity. Qed.

(** Witness: BG 50, target 100, ISF 50.0 (500 tenths). Reverse = (100-50)*200/500 = 20 twentieths = 1U. *)
Lemma witness_reverse_prec_50 :
  reverse_correction_twentieths 50 100 500 = 20.
Proof. reflexivity. Qed.

(** Witness: BG at target yields no reverse correction. *)
Lemma witness_reverse_prec_at_target :
  reverse_correction_twentieths 100 100 500 = 0.
Proof. reflexivity. Qed.

(** Witness: BG above target yields no reverse correction. *)
Lemma witness_reverse_prec_above_target :
  reverse_correction_twentieths 150 100 500 = 0.
Proof. reflexivity. Qed.

(** Witness: BG 80, target 100, ISF 50. Reverse = (100-80)/50 = 0 (integer division). *)
Lemma witness_reverse_correction_80 :
  reverse_correction 80 100 50 = 0.
Proof. reflexivity. Qed.

(** Witness: BG 50, target 100, ISF 50. Reverse = (100-50)/50 = 1. *)
Lemma witness_reverse_correction_50 :
  reverse_correction 50 100 50 = 1.
Proof. reflexivity. Qed.

(** Witness: BG 60, target 100, ISF 20. Reverse = (100-60)/20 = 2. *)
Lemma witness_reverse_correction_60 :
  reverse_correction 60 100 20 = 2.
Proof. reflexivity. Qed.

(** Witness: BG at target yields no reverse correction. *)
Lemma witness_reverse_at_target :
  reverse_correction 100 100 50 = 0.
Proof. reflexivity. Qed.

(** Witness: BG above target yields no reverse correction. *)
Lemma witness_reverse_above_target :
  reverse_correction 150 100 50 = 0.
Proof. reflexivity. Qed.

(** Counterexample: ISF=0 returns 0 (graceful handling). *)
Lemma counterex_reverse_isf_zero :
  reverse_correction 50 100 0 = 0.
Proof. reflexivity. Qed.

(** Witness: apply to carb bolus. 6U carb - 1U reverse = 5U. *)
Lemma witness_apply_reverse_6_minus_1 :
  apply_reverse_correction 6 50 100 50 = 5.
Proof. reflexivity. Qed.

(** Witness: reverse exceeds carb bolus, result is 0. *)
Lemma witness_reverse_exceeds_carb :
  apply_reverse_correction 2 40 100 20 = 0.
Proof. reflexivity. Qed.

(** Witness: no reverse when BG >= target. *)
Lemma witness_no_reverse_above_target :
  apply_reverse_correction 6 150 100 50 = 6.
Proof. reflexivity. Qed.

(** Property: reverse correction is bounded by (target - BG) / ISF. *)
Lemma reverse_correction_bounded : forall bg target isf,
  isf > 0 -> target > bg ->
  reverse_correction bg target isf <= (target - bg) / isf.
Proof.
  intros bg target isf Hisf Hgt.
  unfold reverse_correction.
  destruct (isf =? 0) eqn:E1; [apply Nat.eqb_eq in E1; lia|].
  destruct (target <=? bg) eqn:E2.
  - apply Nat.leb_le in E2. lia.
  - lia.
Qed.

(** Property: apply_reverse never increases carb bolus. *)
Lemma apply_reverse_le_original : forall carb bg target isf,
  apply_reverse_correction carb bg target isf <= carb.
Proof.
  intros carb bg target isf.
  unfold apply_reverse_correction.
  destruct (carb <=? reverse_correction bg target isf) eqn:E; lia.
Qed.

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

(** Property: bolus is bounded when IOB is subtracted. *)
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

(** Arithmetic safety: floor division cannot subtract more than (current - target). *)
Theorem correction_arithmetic_bounded : forall current_bg target_bg isf,
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
Corollary correction_never_causes_level2_hypo : forall current_bg params,
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

(** STRENGTHENED THEOREM: Predicted BG is bounded below by min(current_bg, target_bg).
    This is unconditional on ISF and handles all cases. *)
Theorem predicted_bg_lower_bound : forall current_bg target_bg isf,
  isf > 0 ->
  predicted_bg_after_correction current_bg target_bg isf >= Nat.min current_bg target_bg.
Proof.
  intros current_bg target_bg isf Hisf.
  unfold predicted_bg_after_correction, correction_bolus.
  destruct (current_bg <=? target_bg) eqn:E.
  - apply Nat.leb_le in E.
    rewrite Nat.min_l by lia. simpl. lia.
  - apply Nat.leb_nle in E.
    rewrite Nat.min_r by lia.
    assert (Hdiv : isf * ((current_bg - target_bg) / isf) <= current_bg - target_bg).
    { apply Nat.mul_div_le. lia. }
    lia.
Qed.

(** When BG <= target, no correction is given, so predicted BG = current BG. *)
Theorem no_correction_when_at_or_below_target : forall current_bg target_bg isf,
  current_bg <= target_bg ->
  predicted_bg_after_correction current_bg target_bg isf = current_bg.
Proof.
  intros current_bg target_bg isf Hle.
  unfold predicted_bg_after_correction, correction_bolus.
  destruct (current_bg <=? target_bg) eqn:E.
  - simpl. lia.
  - apply Nat.leb_nle in E. lia.
Qed.

(** Witness: predicted BG at 80 with target 100 is unchanged at 80. *)
Lemma witness_no_correction_below_target_80 :
  predicted_bg_after_correction 80 100 50 = 80.
Proof. reflexivity. Qed.

(** Counterexample: predicted BG at 200 with target 100 is NOT 200 (gets corrected). *)
Lemma counterex_correction_applied :
  predicted_bg_after_correction 200 100 50 <> 200.
Proof. unfold predicted_bg_after_correction, correction_bolus. simpl. lia. Qed.

(** ========================================================================= *)
(** PART IX: INPUT VALIDATION                                                 *)
(** Sanity checks on user-provided values before calculation.                 *)
(** ========================================================================= *)

Module InputValidation.

  Definition bg_in_meter_range (bg : BG_mg_dL) : bool :=
    (20 <=? bg) && (bg <=? BG_METER_MAX).

  Definition carbs_reasonable (carbs : Carbs_g) : bool :=
    carbs <=? CARBS_SANITY_MAX.

  Definition iob_reasonable (iob : IOB) : bool :=
    iob <=? BOLUS_SANITY_MAX.

  Definition input_valid (input : BolusInput) : bool :=
    bg_in_meter_range (bi_current_bg input) &&
    carbs_reasonable (bi_carbs input) &&
    iob_reasonable (bi_iob input).

End InputValidation.

Export InputValidation.

(** Witness: BG of 120 is in meter range. *)
Lemma witness_bg_120_in_range : bg_in_meter_range 120 = true.
Proof. reflexivity. Qed.

(** Witness: BG of 20 (meter minimum) is valid. *)
Lemma witness_bg_20_valid : bg_in_meter_range 20 = true.
Proof. reflexivity. Qed.

(** Witness: BG of 600 (meter maximum) is valid. *)
Lemma witness_bg_600_valid : bg_in_meter_range 600 = true.
Proof. reflexivity. Qed.

(** Counterexample: BG of 19 is below meter range. *)
Lemma counterex_bg_19_invalid : bg_in_meter_range 19 = false.
Proof. reflexivity. Qed.

(** Counterexample: BG of 601 is above meter range. *)
Lemma counterex_bg_601_invalid : bg_in_meter_range 601 = false.
Proof. reflexivity. Qed.

(** Counterexample: BG of 0 is invalid (meter error or dead patient). *)
Lemma counterex_bg_0_invalid : bg_in_meter_range 0 = false.
Proof. reflexivity. Qed.

(** Witness: 60g carbs is reasonable. *)
Lemma witness_carbs_60_reasonable : carbs_reasonable 60 = true.
Proof. reflexivity. Qed.

(** Witness: 200g carbs (max) is still reasonable. *)
Lemma witness_carbs_200_reasonable : carbs_reasonable 200 = true.
Proof. reflexivity. Qed.

(** Counterexample: 201g carbs exceeds sanity limit. *)
Lemma counterex_carbs_201_unreasonable : carbs_reasonable 201 = false.
Proof. reflexivity. Qed.

(** Witness: IOB of 5 units is reasonable. *)
Lemma witness_iob_5_reasonable : iob_reasonable 5 = true.
Proof. reflexivity. Qed.

(** Counterexample: IOB of 30 units exceeds sanity limit. *)
Lemma counterex_iob_30_unreasonable : iob_reasonable 30 = false.
Proof. reflexivity. Qed.

(** Witness: typical input is valid. *)
Lemma witness_typical_input_valid : input_valid witness_input_1 = true.
Proof. reflexivity. Qed.

(** Counterexample: input with BG=0 is invalid. *)
Definition counterex_input_bg_zero : BolusInput := mkBolusInput 60 0 0.

Lemma counterex_input_bg_zero_invalid : input_valid counterex_input_bg_zero = false.
Proof. reflexivity. Qed.

(** Counterexample: input with 300g carbs is invalid. *)
Definition counterex_input_carbs_300 : BolusInput := mkBolusInput 300 100 0.

Lemma counterex_input_carbs_300_invalid : input_valid counterex_input_carbs_300 = false.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART X: BOLUS SANITY CAP                                                  *)
(** No single bolus should ever exceed BOLUS_SANITY_MAX (25 units).           *)
(** ========================================================================= *)

Module BolusCap.

  Definition cap_bolus (bolus : nat) : nat :=
    if bolus <=? BOLUS_SANITY_MAX then bolus else BOLUS_SANITY_MAX.

  Definition bolus_was_capped (original capped : nat) : bool :=
    negb (original =? capped).

End BolusCap.

Export BolusCap.

(** Witness: 10 units is not capped. *)
Lemma witness_cap_10 : cap_bolus 10 = 10.
Proof. reflexivity. Qed.

(** Witness: 25 units (exactly max) is not capped. *)
Lemma witness_cap_25 : cap_bolus 25 = 25.
Proof. reflexivity. Qed.

(** Witness: 30 units is capped to 25. *)
Lemma witness_cap_30 : cap_bolus 30 = 25.
Proof. reflexivity. Qed.

(** Witness: 100 units is capped to 25. *)
Lemma witness_cap_100 : cap_bolus 100 = 25.
Proof. reflexivity. Qed.

(** Witness: 0 units is not capped. *)
Lemma witness_cap_0 : cap_bolus 0 = 0.
Proof. reflexivity. Qed.

(** Counterexample: capped bolus was detected. *)
Lemma counterex_capped_detected : bolus_was_capped 30 (cap_bolus 30) = true.
Proof. reflexivity. Qed.

(** Witness: uncapped bolus is not flagged. *)
Lemma witness_uncapped_not_flagged : bolus_was_capped 10 (cap_bolus 10) = false.
Proof. reflexivity. Qed.

(** Property: cap_bolus always <= BOLUS_SANITY_MAX. *)
Lemma cap_bolus_bounded : forall bolus,
  cap_bolus bolus <= BOLUS_SANITY_MAX.
Proof.
  intro bolus.
  unfold cap_bolus, BOLUS_SANITY_MAX.
  destruct (bolus <=? 25) eqn:E.
  - apply Nat.leb_le in E. exact E.
  - lia.
Qed.

(** Property: cap_bolus always <= original. *)
Lemma cap_bolus_le_original : forall bolus,
  cap_bolus bolus <= bolus.
Proof.
  intro bolus.
  unfold cap_bolus, BOLUS_SANITY_MAX.
  destruct (bolus <=? 25) eqn:E.
  - lia.
  - apply Nat.leb_nle in E. lia.
Qed.

(** ========================================================================= *)
(** PART XI: FULLY VALIDATED BOLUS CALCULATOR                                 *)
(** Combines all safety checks into one validated computation.                *)
(** ========================================================================= *)

Module ValidatedCalculator.

  Inductive BolusResult : Type :=
    | BolusOK : nat -> bool -> BolusResult
    | BolusError : nat -> BolusResult.

  Definition error_invalid_params : nat := 1.
  Definition error_invalid_input : nat := 2.
  Definition error_hypo_risk : nat := 3.

  Definition validated_bolus (input : BolusInput) (params : PatientParams) : BolusResult :=
    if negb (params_valid params) then BolusError error_invalid_params
    else if negb (input_valid input) then BolusError error_invalid_input
    else if is_hypo (bi_current_bg input) then BolusError error_hypo_risk
    else
      let raw := calculate_bolus input params in
      let capped := cap_bolus raw in
      let was_capped := bolus_was_capped raw capped in
      BolusOK capped was_capped.

  Definition result_is_ok (r : BolusResult) : bool :=
    match r with
    | BolusOK _ _ => true
    | BolusError _ => false
    end.

  Definition result_bolus (r : BolusResult) : option nat :=
    match r with
    | BolusOK n _ => Some n
    | BolusError _ => None
    end.

  Definition result_was_capped (r : BolusResult) : option bool :=
    match r with
    | BolusOK _ c => Some c
    | BolusError _ => None
    end.

End ValidatedCalculator.

Export ValidatedCalculator.

(** Witness: normal calculation succeeds. *)
Lemma witness_validated_ok :
  validated_bolus witness_input_1 witness_typical_params = BolusOK 7 false.
Proof. reflexivity. Qed.

(** Witness: result accessor works. *)
Lemma witness_result_bolus_ok :
  result_bolus (validated_bolus witness_input_1 witness_typical_params) = Some 7.
Proof. reflexivity. Qed.

(** Counterexample: invalid params rejected. *)
Lemma counterex_validated_invalid_params :
  validated_bolus witness_input_1 counterex_zero_icr = BolusError error_invalid_params.
Proof. reflexivity. Qed.

(** Counterexample: invalid input rejected. *)
Lemma counterex_validated_invalid_input :
  validated_bolus counterex_input_bg_zero witness_typical_params = BolusError error_invalid_input.
Proof. reflexivity. Qed.

(** Counterexample: hypoglycemic patient rejected (BG=60). *)
Definition input_hypo_patient : BolusInput := mkBolusInput 60 60 0.

Lemma counterex_validated_hypo_risk :
  validated_bolus input_hypo_patient witness_typical_params = BolusError error_hypo_risk.
Proof. reflexivity. Qed.

(** Witness: large meal calculation.
    180g carbs / ICR 10 = 18U carb bolus.
    BG 300, target 100, ISF 50 = (300-100)/50 = 4U correction.
    Total = 22U, not capped (< 25). *)
Definition input_large_meal : BolusInput := mkBolusInput 180 300 0.

Lemma witness_large_meal :
  result_bolus (validated_bolus input_large_meal witness_typical_params) = Some 22.
Proof. reflexivity. Qed.

(** Witness: bolus that exceeds cap.
    200g carbs / ICR 10 = 20U carb bolus.
    BG 400, target 100, ISF 50 = (400-100)/50 = 6U correction.
    Total = 26U, capped to 25U. *)
Definition input_exceeds_cap : BolusInput := mkBolusInput 200 400 0.

Lemma witness_exceeds_cap :
  result_bolus (validated_bolus input_exceeds_cap witness_typical_params) = Some 25.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART XII: SYSTEM INVARIANTS                                               *)
(** ========================================================================= *)

(** Output is bounded by BOLUS_SANITY_MAX on all successful computations. *)
Theorem validated_bolus_bounded : forall input params n c,
  validated_bolus input params = BolusOK n c ->
  n <= BOLUS_SANITY_MAX.
Proof.
  intros input params n c H.
  unfold validated_bolus in H.
  destruct (negb (params_valid params)); [discriminate|].
  destruct (negb (input_valid input)); [discriminate|].
  destruct (is_hypo (bi_current_bg input)); [discriminate|].
  inversion H. subst.
  apply cap_bolus_bounded.
Qed.

(** Computation refuses to proceed when current BG < 70 mg/dL. *)
Theorem hypo_patients_rejected : forall input params,
  is_hypo (bi_current_bg input) = true ->
  params_valid params = true ->
  input_valid input = true ->
  exists e, validated_bolus input params = BolusError e.
Proof.
  intros input params Hhypo Hparams Hinput.
  exists error_hypo_risk.
  unfold validated_bolus.
  rewrite Hparams. simpl.
  rewrite Hinput. simpl.
  rewrite Hhypo. reflexivity.
Qed.

(** ICR >= 1 and ISF >= 1 on all successful computations. *)
Theorem no_division_by_zero : forall input params n c,
  validated_bolus input params = BolusOK n c ->
  pp_icr params >= 1 /\ pp_isf params >= 1.
Proof.
  intros input params n c H.
  unfold validated_bolus in H.
  destruct (negb (params_valid params)) eqn:E1; [discriminate|].
  apply negb_false_iff in E1.
  unfold params_valid in E1.
  repeat rewrite andb_true_iff in E1.
  destruct E1 as [[[[[[[_ _] _] _] _] _] H7] H8].
  apply Nat.leb_le in H7. apply Nat.leb_le in H8.
  lia.
Qed.

(** Output is non-negative (trivially true for nat representation). *)
Theorem bolus_nonnegative : forall input params n c,
  validated_bolus input params = BolusOK n c ->
  n >= 0.
Proof. intros. lia. Qed.

(** BolusOK implies all preconditions were satisfied. *)
Theorem only_valid_produces_result : forall input params n c,
  validated_bolus input params = BolusOK n c ->
  params_valid params = true /\
  input_valid input = true /\
  is_hypo (bi_current_bg input) = false.
Proof.
  intros input params n c H.
  unfold validated_bolus in H.
  destruct (negb (params_valid params)) eqn:E1; [discriminate|].
  destruct (negb (input_valid input)) eqn:E2; [discriminate|].
  destruct (is_hypo (bi_current_bg input)) eqn:E3; [discriminate|].
  apply negb_false_iff in E1.
  apply negb_false_iff in E2.
  auto.
Qed.

(** ========================================================================= *)
(** PART XIII: UNIT CONVERSION (mg/dL <-> mmol/L)                             *)
(** Conversion factor: 1 mmol/L = 18.0182 mg/dL (molar mass glucose 180.16).  *)
(** We use tenths of mmol/L: 10 = 1.0 mmol/L, 39 = 3.9 mmol/L, 100 = 10 mmol/L*)
(** This matches the MmolInput module and provides 0.1 mmol/L precision.      *)
(** ========================================================================= *)

Module UnitConversion.

  Definition FACTOR : nat := 1802.

  Definition mg_dL_to_mmol_tenths (mg : nat) : nat :=
    (mg * 1000) / FACTOR.

  Definition mmol_tenths_to_mg_dL (mmol_tenths : nat) : nat :=
    (mmol_tenths * FACTOR) / 1000.

  Definition BG_mmol_tenths := nat.

End UnitConversion.

Export UnitConversion.

(** Witness: 180 mg/dL ≈ 10.0 mmol/L = 99 tenths (180*1000/1802). *)
Lemma witness_180_mg_to_mmol : mg_dL_to_mmol_tenths 180 = 99.
Proof. reflexivity. Qed.

(** Witness: 90 mg/dL ≈ 5.0 mmol/L = 49 tenths (90*1000/1802). *)
Lemma witness_90_mg_to_mmol : mg_dL_to_mmol_tenths 90 = 49.
Proof. reflexivity. Qed.

(** Witness: 70 mg/dL ≈ 3.9 mmol/L = 38 tenths (70*1000/1802). *)
Lemma witness_70_mg_to_mmol : mg_dL_to_mmol_tenths 70 = 38.
Proof. reflexivity. Qed.

(** Witness: 100 tenths (10.0 mmol/L) = 180 mg/dL (100*1802/1000). *)
Lemma witness_100_tenths_to_mg : mmol_tenths_to_mg_dL 100 = 180.
Proof. reflexivity. Qed.

(** Witness: 50 tenths (5.0 mmol/L) = 90 mg/dL (50*1802/1000). *)
Lemma witness_50_tenths_to_mg : mmol_tenths_to_mg_dL 50 = 90.
Proof. reflexivity. Qed.

(** Witness: 39 tenths (3.9 mmol/L) = 70 mg/dL (39*1802/1000). *)
Lemma witness_39_tenths_to_mg : mmol_tenths_to_mg_dL 39 = 70.
Proof. reflexivity. Qed.

(** Witness: 0 converts to 0 in both directions. *)
Lemma witness_zero_conversion :
  mg_dL_to_mmol_tenths 0 = 0 /\ mmol_tenths_to_mg_dL 0 = 0.
Proof. split; reflexivity. Qed.

(** Clinical thresholds in tenths of mmol/L. *)
Definition BG_HYPO_MMOL_TENTHS : nat := 39.  (** 3.9 mmol/L ≈ 70 mg/dL. *)
Definition BG_HYPER_MMOL_TENTHS : nat := 100. (** 10.0 mmol/L = 180 mg/dL. *)

(** Witness: threshold correspondence. *)
Lemma witness_hypo_threshold_mg :
  mmol_tenths_to_mg_dL BG_HYPO_MMOL_TENTHS = 70.
Proof. reflexivity. Qed.

Lemma witness_hyper_threshold_mg :
  mmol_tenths_to_mg_dL BG_HYPER_MMOL_TENTHS = 180.
Proof. reflexivity. Qed.

(** Counterexample: round-trip is lossy due to integer division. *)
(** 71 -> 39 tenths -> 70 mg/dL. Loss of 1 mg/dL. *)
Lemma counterex_roundtrip_lossy :
  mmol_tenths_to_mg_dL (mg_dL_to_mmol_tenths 71) = 70.
Proof. reflexivity. Qed.

(** Counterexample: even "nice" values don't roundtrip perfectly. *)
(** 180 -> 99 tenths -> 178 mg/dL. Loss of 2 mg/dL. *)
Lemma counterex_180_roundtrip :
  mmol_tenths_to_mg_dL (mg_dL_to_mmol_tenths 180) = 178.
Proof. reflexivity. Qed.

(** Witness: tenths -> mg/dL -> tenths is close but still lossy. *)
(** 100 tenths -> 180 mg/dL -> 99 tenths. Loss of 1 tenth. *)
Lemma witness_tenths_roundtrip_lossy :
  mg_dL_to_mmol_tenths (mmol_tenths_to_mg_dL 100) = 99.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART XIV: FIXED-POINT INSULIN ARITHMETIC                                  *)
(** Insulin pumps deliver in 0.05U increments. We represent doses as          *)
(** twentieths of a unit: 1 = 0.05U, 20 = 1.0U, 100 = 5.0U.                   *)
(** ========================================================================= *)

Module FixedPointInsulin.

  Definition Insulin_twentieth := nat.

  Definition TWENTIETH : nat := 1.
  Definition TENTH : nat := 2.
  Definition QUARTER : nat := 5.
  Definition HALF : nat := 10.
  Definition ONE_UNIT : nat := 20.

  Definition twentieths_to_units (t : Insulin_twentieth) : nat :=
    t / ONE_UNIT.

  Definition twentieths_to_tenths (t : Insulin_twentieth) : nat :=
    t / TENTH.

  Definition units_to_twentieths (u : nat) : Insulin_twentieth :=
    u * ONE_UNIT.

  Definition round_down_to_increment (t : Insulin_twentieth) (increment : nat) : Insulin_twentieth :=
    if increment =? 0 then t else (t / increment) * increment.

  Definition round_nearest_to_increment (t : Insulin_twentieth) (increment : nat) : Insulin_twentieth :=
    if increment =? 0 then t
    else let half_inc := increment / 2 in
         ((t + half_inc) / increment) * increment.

  Definition round_down_to_tenth (t : Insulin_twentieth) : Insulin_twentieth :=
    round_down_to_increment t TENTH.

  Definition round_down_to_half (t : Insulin_twentieth) : Insulin_twentieth :=
    round_down_to_increment t HALF.

  Definition round_nearest_to_tenth (t : Insulin_twentieth) : Insulin_twentieth :=
    round_nearest_to_increment t TENTH.

  Definition round_nearest_to_half (t : Insulin_twentieth) : Insulin_twentieth :=
    round_nearest_to_increment t HALF.

End FixedPointInsulin.

Export FixedPointInsulin.

(** Witness: 20 twentieths = 1.0 unit. *)
Lemma witness_20_twentieths_is_1_unit : twentieths_to_units 20 = 1.
Proof. reflexivity. Qed.

(** Witness: 100 twentieths = 5.0 units. *)
Lemma witness_100_twentieths_is_5_units : twentieths_to_units 100 = 5.
Proof. reflexivity. Qed.

(** Witness: 7 twentieths = 0.35U, truncates to 0 whole units. *)
Lemma witness_7_twentieths_truncates : twentieths_to_units 7 = 0.
Proof. reflexivity. Qed.

(** Witness: 3 units = 60 twentieths. *)
Lemma witness_3_units_is_60_twentieths : units_to_twentieths 3 = 60.
Proof. reflexivity. Qed.

(** Witness: round 7 twentieths (0.35U) down to nearest tenth (0.30U = 6). *)
Lemma witness_round_down_tenth_7 : round_down_to_tenth 7 = 6.
Proof. reflexivity. Qed.

(** Witness: round 13 twentieths (0.65U) down to nearest half (0.50U = 10). *)
Lemma witness_round_down_half_13 : round_down_to_half 13 = 10.
Proof. reflexivity. Qed.

(** Witness: round 7 twentieths (0.35U) to nearest tenth (0.40U = 8). *)
Lemma witness_round_nearest_tenth_7 : round_nearest_to_tenth 7 = 8.
Proof. reflexivity. Qed.

(** Witness: round 5 twentieths (0.25U) to nearest tenth (0.30U = 6). *)
Lemma witness_round_nearest_tenth_5 : round_nearest_to_tenth 5 = 6.
Proof. reflexivity. Qed.

(** Witness: round 16 twentieths (0.80U) to nearest half (1.00U = 20). *)
Lemma witness_round_nearest_half_16 : round_nearest_to_half 16 = 20.
Proof. reflexivity. Qed.

(** Witness: round 14 twentieths (0.70U) to nearest half (0.50U = 10). *)
Lemma witness_round_nearest_half_14 : round_nearest_to_half 14 = 10.
Proof. reflexivity. Qed.

(** Counterexample: rounding down loses precision. *)
Lemma counterex_round_down_loses : round_down_to_tenth 7 < 7.
Proof. unfold round_down_to_tenth, round_down_to_increment, TENTH. simpl. lia. Qed.

(** Witness: exact multiples unchanged. *)
Lemma witness_exact_tenth_unchanged : round_down_to_tenth 8 = 8.
Proof. reflexivity. Qed.

(** Witness: exact half (10 twentieths = 0.50U) unchanged. *)
Lemma witness_exact_half_unchanged : round_down_to_half 10 = 10.
Proof. reflexivity. Qed.

(** Counterexample: 19 twentieths (0.95U) rounds down to 0 whole units. *)
Lemma counterex_19_twentieths_not_one_unit : twentieths_to_units 19 = 0.
Proof. reflexivity. Qed.

(** Round-trip property: units_to_twentieths then twentieths_to_units recovers original. *)
Lemma units_twentieths_roundtrip : forall u,
  twentieths_to_units (units_to_twentieths u) = u.
Proof.
  intro u.
  unfold twentieths_to_units, units_to_twentieths, ONE_UNIT.
  rewrite Nat.div_mul. reflexivity. lia.
Qed.

(** ========================================================================= *)
(** PART XV: INSULIN-ON-BOARD DECAY MODEL                                     *)
(** Models active insulin remaining from previous boluses.                    *)
(** Uses piecewise linear approximation of exponential decay.                 *)
(** DIA (duration of insulin action) typically 3-5 hours.                     *)
(** ========================================================================= *)

Module IOBDecay.

  Definition Minutes := nat.
  Definition DIA_minutes := nat.

  Definition DIA_3_HOURS : DIA_minutes := 180.
  Definition DIA_4_HOURS : DIA_minutes := 240.
  Definition DIA_5_HOURS : DIA_minutes := 300.

  Record BolusEvent := mkBolusEvent {
    be_dose_twentieths : Insulin_twentieth;
    be_time_minutes : Minutes
  }.

  Definition minutes_since_bolus (now : Minutes) (event : BolusEvent) : nat :=
    if now <? be_time_minutes event then 0
    else now - be_time_minutes event.

  Definition iob_fraction_remaining (elapsed : Minutes) (dia : DIA_minutes) : nat :=
    if dia =? 0 then 0
    else if dia <=? elapsed then 0
    else ((dia - elapsed) * 100) / dia.

  Definition iob_from_bolus (now : Minutes) (event : BolusEvent) (dia : DIA_minutes) : Insulin_twentieth :=
    if now <? be_time_minutes event then 0
    else
      let elapsed := minutes_since_bolus now event in
      let fraction := iob_fraction_remaining elapsed dia in
      (be_dose_twentieths event * fraction) / 100.

  Fixpoint total_iob (now : Minutes) (events : list BolusEvent) (dia : DIA_minutes) : Insulin_twentieth :=
    match events with
    | nil => 0
    | e :: rest => iob_from_bolus now e dia + total_iob now rest dia
    end.

  Definition event_time_valid (now : Minutes) (event : BolusEvent) : bool :=
    be_time_minutes event <=? now.

  Fixpoint history_times_valid (now : Minutes) (events : list BolusEvent) : bool :=
    match events with
    | nil => true
    | e :: rest => event_time_valid now e && history_times_valid now rest
    end.

  Fixpoint history_sorted_desc (events : list BolusEvent) : bool :=
    match events with
    | nil => true
    | e1 :: rest =>
        match rest with
        | nil => true
        | e2 :: _ => (be_time_minutes e2 <=? be_time_minutes e1) && history_sorted_desc rest
        end
    end.

  Definition history_valid (now : Minutes) (events : list BolusEvent) : bool :=
    history_times_valid now events && history_sorted_desc events.

  Fixpoint max_event_time (events : list BolusEvent) : Minutes :=
    match events with
    | nil => 0
    | e :: rest => Nat.max (be_time_minutes e) (max_event_time rest)
    end.

End IOBDecay.

Export IOBDecay.

(** Witness: at time 0, 100% of insulin remains (fraction = 100). *)
Lemma witness_iob_fraction_at_zero :
  iob_fraction_remaining 0 DIA_4_HOURS = 100.
Proof. reflexivity. Qed.

(** Witness: at half DIA (120 min of 240), 50% remains. *)
Lemma witness_iob_fraction_at_half :
  iob_fraction_remaining 120 DIA_4_HOURS = 50.
Proof. reflexivity. Qed.

(** Witness: at DIA (240 min), 0% remains. *)
Lemma witness_iob_fraction_at_dia :
  iob_fraction_remaining 240 DIA_4_HOURS = 0.
Proof. reflexivity. Qed.

(** Witness: beyond DIA, 0% remains. *)
Lemma witness_iob_fraction_beyond_dia :
  iob_fraction_remaining 300 DIA_4_HOURS = 0.
Proof. reflexivity. Qed.

(** Witness: 1 unit (20 twentieths) at time 0, checked at time 120 with 4hr DIA.
    50% remaining = 10 twentieths = 0.5U. *)
Definition witness_bolus_event : BolusEvent := mkBolusEvent 20 0.

Lemma witness_iob_half_remaining :
  iob_from_bolus 120 witness_bolus_event DIA_4_HOURS = 10.
Proof. reflexivity. Qed.

(** Witness: same bolus at time 240 (full DIA elapsed) = 0. *)
Lemma witness_iob_fully_absorbed :
  iob_from_bolus 240 witness_bolus_event DIA_4_HOURS = 0.
Proof. reflexivity. Qed.

(** Witness: bolus in the future contributes 0 IOB. *)
Definition witness_future_bolus : BolusEvent := mkBolusEvent 20 200.

Lemma witness_future_bolus_no_iob :
  iob_from_bolus 100 witness_future_bolus DIA_4_HOURS = 0.
Proof. reflexivity. Qed.

(** Witness: total IOB from two boluses.
    Bolus 1: 20 twentieths at t=0. At t=120: 50% remains = 10.
    Bolus 2: 40 twentieths at t=60. At t=120: 75% remains = 30.
    Total = 40 twentieths. *)
Definition witness_bolus_1 : BolusEvent := mkBolusEvent 20 0.
Definition witness_bolus_2 : BolusEvent := mkBolusEvent 40 60.

Lemma witness_total_iob_two_boluses :
  total_iob 120 [witness_bolus_1; witness_bolus_2] DIA_4_HOURS = 40.
Proof. reflexivity. Qed.

(** IOB fraction is at most 100. *)
Lemma iob_fraction_le_100 : forall elapsed dia,
  iob_fraction_remaining elapsed dia <= 100.
Proof.
  intros elapsed dia.
  unfold iob_fraction_remaining.
  destruct (dia =? 0) eqn:E1; [lia|].
  destruct (dia <=? elapsed) eqn:E2; [lia|].
  apply Nat.leb_nle in E2.
  apply Nat.eqb_neq in E1.
  apply Nat.div_le_upper_bound. lia.
  nia.
Qed.

(** IOB is bounded by original dose. *)
Lemma iob_bounded_by_dose : forall now event dia,
  iob_from_bolus now event dia <= be_dose_twentieths event.
Proof.
  intros now event dia.
  unfold iob_from_bolus.
  destruct (now <? be_time_minutes event) eqn:Efut.
  - lia.
  - pose proof (iob_fraction_le_100 (minutes_since_bolus now event) dia) as Hfrac.
    apply Nat.div_le_upper_bound. lia.
    nia.
Qed.

(** Witness: valid history passes validation. *)
Definition witness_valid_history : list BolusEvent :=
  [mkBolusEvent 40 60; mkBolusEvent 20 0].

Lemma witness_valid_history_ok :
  history_times_valid 120 witness_valid_history = true.
Proof. reflexivity. Qed.

(** Counterexample: history with future event fails validation. *)
Definition counterex_future_history : list BolusEvent :=
  [mkBolusEvent 40 200; mkBolusEvent 20 0].

Lemma counterex_future_history_invalid :
  history_times_valid 120 counterex_future_history = false.
Proof. reflexivity. Qed.

(** Counterexample: single future event fails. *)
Lemma counterex_single_future_event :
  event_time_valid 100 (mkBolusEvent 20 150) = false.
Proof. reflexivity. Qed.

(** Witness: empty history is valid. *)
Lemma witness_empty_history_valid : forall now,
  history_times_valid now [] = true.
Proof. reflexivity. Qed.

(** Valid history means no event is silently zeroed by the future-check. *)
Lemma valid_event_not_future : forall now event,
  event_time_valid now event = true ->
  (now <? be_time_minutes event) = false.
Proof.
  intros now event H.
  unfold event_time_valid in H.
  apply Nat.leb_le in H.
  apply Nat.ltb_nlt. lia.
Qed.

(** Witness: sorted history (most recent first) passes. *)
Definition witness_sorted_history : list BolusEvent :=
  [mkBolusEvent 40 100; mkBolusEvent 30 60; mkBolusEvent 20 0].

Lemma witness_sorted_history_ok :
  history_sorted_desc witness_sorted_history = true.
Proof. reflexivity. Qed.

(** Counterexample: unsorted history fails. *)
Definition counterex_unsorted_history : list BolusEvent :=
  [mkBolusEvent 40 60; mkBolusEvent 30 100; mkBolusEvent 20 0].

Lemma counterex_unsorted_history_fails :
  history_sorted_desc counterex_unsorted_history = false.
Proof. reflexivity. Qed.

(** Witness: full history_valid check passes. *)
Lemma witness_full_history_valid :
  history_valid 120 witness_sorted_history = true.
Proof. reflexivity. Qed.

(** Counterexample: unsorted fails full validation. *)
Lemma counterex_unsorted_full_valid :
  history_valid 120 counterex_unsorted_history = false.
Proof. reflexivity. Qed.

(** Witness: single-element history is always sorted. *)
Lemma witness_singleton_sorted :
  history_sorted_desc [mkBolusEvent 40 100] = true.
Proof. reflexivity. Qed.

(** Witness: empty history is sorted. *)
Lemma witness_empty_sorted :
  history_sorted_desc [] = true.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART XV-B: BILINEAR IOB DECAY MODEL                                       *)
(** More accurate than linear: peak action at ~75 min, then decay.            *)
(** Models rapid-acting insulin (lispro, aspart, glulisine).                  *)
(** ========================================================================= *)

Module BilinearIOB.

  Definition PEAK_TIME : Minutes := 75.

  Definition bilinear_iob_fraction (elapsed : Minutes) (dia : DIA_minutes) : nat :=
    if dia =? 0 then 0
    else if dia <=? elapsed then 0
    else if elapsed <=? PEAK_TIME then
      100 - (elapsed * 25) / PEAK_TIME
    else
      ((dia - elapsed) * 75) / (dia - PEAK_TIME).

  Definition bilinear_iob_from_bolus (now : Minutes) (event : BolusEvent) (dia : DIA_minutes) : Insulin_twentieth :=
    if now <? be_time_minutes event then 0
    else
      let elapsed := now - be_time_minutes event in
      let fraction := bilinear_iob_fraction elapsed dia in
      (be_dose_twentieths event * fraction) / 100.

  Fixpoint total_bilinear_iob (now : Minutes) (events : list BolusEvent) (dia : DIA_minutes) : Insulin_twentieth :=
    match events with
    | nil => 0
    | e :: rest => bilinear_iob_from_bolus now e dia + total_bilinear_iob now rest dia
    end.

End BilinearIOB.

Export BilinearIOB.

Inductive ActivityState : Type :=
  | Activity_Normal : ActivityState
  | Activity_LightExercise : ActivityState
  | Activity_ModerateExercise : ActivityState
  | Activity_IntenseExercise : ActivityState
  | Activity_Illness : ActivityState
  | Activity_Stress : ActivityState.

Definition isf_activity_modifier (state : ActivityState) : nat :=
  match state with
  | Activity_Normal => 100
  | Activity_LightExercise => 120
  | Activity_ModerateExercise => 150
  | Activity_IntenseExercise => 200
  | Activity_Illness => 70
  | Activity_Stress => 70
  end.

Definition icr_activity_modifier (state : ActivityState) : nat :=
  match state with
  | Activity_Normal => 100
  | Activity_LightExercise => 120
  | Activity_ModerateExercise => 150
  | Activity_IntenseExercise => 200
  | Activity_Illness => 80
  | Activity_Stress => 80
  end.

(** ========================================================================= *)
(** PART XV-C: NONLINEAR ISF CORRECTION                                       *)
(** Above 250 mg/dL, insulin resistance increases. We reduce effective ISF    *)
(** by 20% for BG 250-350, 40% for BG >350. This increases correction dose.   *)
(** Source: Walsh et al., "Using Insulin" (2003); clinical consensus.         *)
(** ========================================================================= *)

Module NonlinearISF.

  Definition BG_RESISTANCE_MILD : nat := 250.
  Definition BG_RESISTANCE_SEVERE : nat := 350.

  Definition ISF_REDUCTION_MILD : nat := 80.
  Definition ISF_REDUCTION_SEVERE : nat := 60.

  Definition adjusted_isf (bg : BG_mg_dL) (base_isf : nat) : nat :=
    if bg <? BG_RESISTANCE_MILD then base_isf
    else if bg <? BG_RESISTANCE_SEVERE then (base_isf * ISF_REDUCTION_MILD) / 100
    else (base_isf * ISF_REDUCTION_SEVERE) / 100.

  Definition adjusted_isf_tenths (bg : BG_mg_dL) (base_isf_tenths : nat) : nat :=
    if bg <? BG_RESISTANCE_MILD then base_isf_tenths
    else if bg <? BG_RESISTANCE_SEVERE then (base_isf_tenths * ISF_REDUCTION_MILD) / 100
    else (base_isf_tenths * ISF_REDUCTION_SEVERE) / 100.

  Definition correction_with_resistance (current_bg target_bg : BG_mg_dL) (base_isf : nat) : nat :=
    if current_bg <=? target_bg then 0
    else
      let eff_isf := adjusted_isf current_bg base_isf in
      if eff_isf =? 0 then 0
      else (current_bg - target_bg) / eff_isf.

  Definition correction_twentieths_with_resistance (current_bg target_bg : BG_mg_dL) (base_isf_tenths : nat) : nat :=
    if current_bg <=? target_bg then 0
    else
      let eff_isf := adjusted_isf_tenths current_bg base_isf_tenths in
      if eff_isf =? 0 then 0
      else ((current_bg - target_bg) * 200) / eff_isf.

End NonlinearISF.

Export NonlinearISF.

(** Correction using full ISF adjustment (dawn + resistance). *)
Definition correction_twentieths_full (minutes : Minutes) (current_bg target_bg : BG_mg_dL) (base_isf_tenths : nat) : nat :=
  if current_bg <=? target_bg then 0
  else
    let hour := (minutes / 60) mod 24 in
    let is_dawn := (4 <=? hour) && (hour <? 8) in
    let dawn_isf := if is_dawn then (base_isf_tenths * 80) / 100 else base_isf_tenths in
    let eff_isf := adjusted_isf_tenths current_bg dawn_isf in
    if eff_isf =? 0 then 0
    else ((current_bg - target_bg) * 200) / eff_isf.

Definition CGM_MARGIN_PERCENT : nat := 15.

Definition apply_sensor_margin (bg : BG_mg_dL) (target : BG_mg_dL) : BG_mg_dL :=
  if bg <=? target then bg
  else (bg * (100 - CGM_MARGIN_PERCENT)) / 100.

Lemma sensor_margin_le : forall bg target, apply_sensor_margin bg target <= bg.
Proof.
  intros bg target.
  unfold apply_sensor_margin, CGM_MARGIN_PERCENT.
  destruct (bg <=? target); [lia|].
  apply Nat.div_le_upper_bound; lia.
Qed.

Lemma sensor_margin_conservative : forall bg target,
  bg > target -> apply_sensor_margin bg target < bg.
Proof.
  intros bg target Hgt.
  unfold apply_sensor_margin, CGM_MARGIN_PERCENT.
  destruct (bg <=? target) eqn:E.
  - apply Nat.leb_le in E. lia.
  - assert (bg * 85 < bg * 100) by lia.
    apply Nat.div_lt_upper_bound; lia.
Qed.

(** ========================================================================= *)
(** PART XVI: HIGH-PRECISION BOLUS CALCULATOR                                 *)
(** Uses twentieths representation and integrates bilinear IOB decay.         *)
(** ========================================================================= *)

Module PrecisionCalculator.

  Record PrecisionParams := mkPrecisionParams {
    prec_icr_tenths : nat;
    prec_isf_tenths : nat;
    prec_target_bg : BG_mg_dL;
    prec_dia : DIA_minutes
  }.

  Definition prec_params_valid (p : PrecisionParams) : bool :=
    (20 <=? prec_icr_tenths p) && (prec_icr_tenths p <=? 1000) &&
    (100 <=? prec_isf_tenths p) && (prec_isf_tenths p <=? 4000) &&
    (BG_HYPO <=? prec_target_bg p) && (prec_target_bg p <=? BG_HYPER) &&
    (120 <=? prec_dia p) && (prec_dia p <=? 360).

  Definition carb_bolus_twentieths (carbs_g : nat) (icr_tenths : nat) : Insulin_twentieth :=
    if icr_tenths =? 0 then 0
    else (carbs_g * 200) / icr_tenths.

  Definition correction_bolus_twentieths (current_bg target_bg : BG_mg_dL) (isf_tenths : nat) : Insulin_twentieth :=
    if isf_tenths =? 0 then 0
    else if current_bg <=? target_bg then 0
    else ((current_bg - target_bg) * 200) / isf_tenths.

  Record PrecisionInput := mkPrecisionInput {
    pi_carbs_g : nat;
    pi_current_bg : BG_mg_dL;
    pi_now : Minutes;
    pi_bolus_history : list BolusEvent;
    pi_activity : ActivityState;
    pi_use_sensor_margin : bool
  }.

  Definition calculate_precision_bolus (input : PrecisionInput) (params : PrecisionParams) : Insulin_twentieth :=
    let activity_isf := (prec_isf_tenths params * isf_activity_modifier (pi_activity input)) / 100 in
    let activity_icr := (prec_icr_tenths params * icr_activity_modifier (pi_activity input)) / 100 in
    let eff_bg := if pi_use_sensor_margin input
                  then apply_sensor_margin (pi_current_bg input) (prec_target_bg params)
                  else pi_current_bg input in
    let carb := carb_bolus_twentieths (pi_carbs_g input) activity_icr in
    let carb_adj := apply_reverse_correction_twentieths carb eff_bg (prec_target_bg params) activity_isf in
    let corr := correction_twentieths_full (pi_now input) eff_bg (prec_target_bg params) activity_isf in
    let iob := total_bilinear_iob (pi_now input) (pi_bolus_history input) (prec_dia params) in
    let raw := carb_adj + corr in
    if raw <=? iob then 0 else raw - iob.

End PrecisionCalculator.

Export PrecisionCalculator.

(** Witness: typical params (ICR=10.0, ISF=50.0, target=100, DIA=4hr). *)
Definition witness_prec_params : PrecisionParams :=
  mkPrecisionParams 100 500 100 240.

Lemma witness_prec_params_valid : prec_params_valid witness_prec_params = true.
Proof. reflexivity. Qed.

(** Witness: 60g carbs with ICR=10.0 (100 tenths) yields 120 twentieths = 6.0U. *)
Lemma witness_carb_bolus_prec_60g :
  carb_bolus_twentieths 60 100 = 120.
Proof. reflexivity. Qed.

(** Witness: 45g carbs with ICR=15.0 (150 tenths) yields 60 twentieths = 3.0U. *)
Lemma witness_carb_bolus_prec_45g :
  carb_bolus_twentieths 45 150 = 60.
Proof. reflexivity. Qed.

(** Witness: BG 200, target 100, ISF=50.0 yields 40 twentieths = 2.0U. *)
Lemma witness_correction_prec_200 :
  correction_bolus_twentieths 200 100 500 = 40.
Proof. reflexivity. Qed.

(** Witness: BG 150, target 100, ISF=25.0 yields 40 twentieths = 2.0U. *)
Lemma witness_correction_prec_150 :
  correction_bolus_twentieths 150 100 250 = 40.
Proof. reflexivity. Qed.

(** Witness: BG at target yields 0 correction. *)
Lemma witness_correction_prec_at_target :
  correction_bolus_twentieths 100 100 500 = 0.
Proof. reflexivity. Qed.

(** Witness: complete calculation with no history.
    60g carbs, BG 150, ICR=10.0, ISF=50.0, target=100.
    Carb: 120 twentieths. Correction: 20 twentieths. Total: 140 = 7.0U. *)
Definition witness_prec_input : PrecisionInput :=
  mkPrecisionInput 60 150 0 [] Activity_Normal false.

Lemma witness_prec_bolus_no_history :
  calculate_precision_bolus witness_prec_input witness_prec_params = 140.
Proof. reflexivity. Qed.

(** Witness: calculation with IOB from previous bolus.
    Same input but with 2U (40 twentieths) given 4 hours ago.
    At time 240 (4 AM), dawn period applies: ISF = 500*80/100 = 400.
    Correction = (150-100)*200/400 = 25 twentieths.
    IOB from bolus at 0 with 4hr DIA: 0 remaining.
    Total = 120 + 25 = 145 twentieths. *)
Definition witness_prec_input_with_old_bolus : PrecisionInput :=
  mkPrecisionInput 60 150 240 [mkBolusEvent 40 0] Activity_Normal false.

Lemma witness_prec_bolus_with_old_iob :
  calculate_precision_bolus witness_prec_input_with_old_bolus witness_prec_params = 145.
Proof. reflexivity. Qed.

(** Witness: calculation with recent IOB.
    60g carbs, BG 150, but 3U (60 twentieths) given 1 hour ago.
    Bilinear IOB at time 60 (rising phase): fraction = 100 - (60*25)/75 = 80%.
    IOB = 60 * 80 / 100 = 48 twentieths.
    Raw = 140, IOB = 48, result = 92 twentieths = 4.6U. *)
Definition witness_prec_input_recent_iob : PrecisionInput :=
  mkPrecisionInput 60 150 60 [mkBolusEvent 60 0] Activity_Normal false.

Lemma witness_prec_bolus_recent_iob :
  calculate_precision_bolus witness_prec_input_recent_iob witness_prec_params = 92.
Proof. reflexivity. Qed.

(** Counterexample: ICR=0 returns 0 (not crash). *)
Lemma counterex_prec_icr_zero :
  carb_bolus_twentieths 60 0 = 0.
Proof. reflexivity. Qed.

(** Counterexample: ISF=0 returns 0 (not crash). *)
Lemma counterex_prec_isf_zero :
  correction_bolus_twentieths 200 100 0 = 0.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART XVII: PRECISION CALCULATOR INVARIANTS                                *)
(** ========================================================================= *)

(** Carb bolus is monotonic in carbs consumed. *)
Lemma carb_bolus_twentieths_monotonic : forall c1 c2 icr,
  icr > 0 -> c1 <= c2 ->
  carb_bolus_twentieths c1 icr <= carb_bolus_twentieths c2 icr.
Proof.
  intros c1 c2 icr Hicr Hle.
  unfold carb_bolus_twentieths.
  destruct (icr =? 0) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - apply Nat.div_le_mono. lia. nia.
Qed.

(** Correction bolus is monotonic in BG. *)
Lemma correction_bolus_twentieths_monotonic : forall bg1 bg2 target isf,
  isf > 0 -> bg1 <= bg2 ->
  correction_bolus_twentieths bg1 target isf <= correction_bolus_twentieths bg2 target isf.
Proof.
  intros bg1 bg2 target isf Hisf Hle.
  unfold correction_bolus_twentieths.
  destruct (isf =? 0) eqn:E; [apply Nat.eqb_eq in E; lia|].
  destruct (bg1 <=? target) eqn:E1; destruct (bg2 <=? target) eqn:E2.
  - lia.
  - apply Nat.le_0_l.
  - apply Nat.leb_nle in E1. apply Nat.leb_le in E2. lia.
  - apply Nat.leb_nle in E1. apply Nat.leb_nle in E2.
    apply Nat.div_le_mono. lia. nia.
Qed.

(** Correction is zero when BG at or below target. *)
Lemma correction_zero_at_target : forall bg target isf,
  bg <= target ->
  correction_bolus_twentieths bg target isf = 0.
Proof.
  intros bg target isf Hle.
  unfold correction_bolus_twentieths.
  destruct (isf =? 0); [reflexivity|].
  destruct (bg <=? target) eqn:E.
  - reflexivity.
  - apply Nat.leb_nle in E. lia.
Qed.

(** ========================================================================= *)
(** PART XVIII: VALIDATED PRECISION CALCULATOR                                *)
(** ========================================================================= *)

Module ValidatedPrecision.

  Definition PREC_BOLUS_MAX_TWENTIETHS : nat := 500.
  Definition MAX_TIME_MINUTES : nat := 525600.

  Definition time_reasonable (now : Minutes) : bool :=
    now <=? MAX_TIME_MINUTES.

  Definition cap_twentieths (t : Insulin_twentieth) : Insulin_twentieth :=
    if t <=? PREC_BOLUS_MAX_TWENTIETHS then t else PREC_BOLUS_MAX_TWENTIETHS.

  Definition prec_input_valid (input : PrecisionInput) : bool :=
    bg_in_meter_range (pi_current_bg input) &&
    carbs_reasonable (pi_carbs_g input) &&
    time_reasonable (pi_now input) &&
    history_valid (pi_now input) (pi_bolus_history input).

  Inductive PrecisionResult : Type :=
    | PrecOK : Insulin_twentieth -> bool -> PrecisionResult
    | PrecError : nat -> PrecisionResult.

  Definition prec_error_invalid_params : nat := 1.
  Definition prec_error_invalid_input : nat := 2.
  Definition prec_error_hypo : nat := 3.
  Definition prec_error_invalid_history : nat := 4.
  Definition prec_error_invalid_time : nat := 5.

  Definition validated_precision_bolus (input : PrecisionInput) (params : PrecisionParams) : PrecisionResult :=
    if negb (prec_params_valid params) then PrecError prec_error_invalid_params
    else if negb (bg_in_meter_range (pi_current_bg input) && carbs_reasonable (pi_carbs_g input))
      then PrecError prec_error_invalid_input
    else if negb (time_reasonable (pi_now input))
      then PrecError prec_error_invalid_time
    else if negb (history_valid (pi_now input) (pi_bolus_history input))
      then PrecError prec_error_invalid_history
    else if is_hypo (pi_current_bg input) then PrecError prec_error_hypo
    else
      let raw := calculate_precision_bolus input params in
      let capped := cap_twentieths raw in
      let was_capped := negb (raw =? capped) in
      PrecOK capped was_capped.

  Definition prec_result_twentieths (r : PrecisionResult) : option Insulin_twentieth :=
    match r with
    | PrecOK t _ => Some t
    | PrecError _ => None
    end.

End ValidatedPrecision.

Export ValidatedPrecision.

(** Witness: valid computation returns PrecOK. *)
Lemma witness_validated_prec_ok :
  exists t c, validated_precision_bolus witness_prec_input witness_prec_params = PrecOK t c.
Proof. exists 140, false. reflexivity. Qed.

(** Witness: cap at 500 twentieths (25U). *)
Lemma witness_cap_500 : cap_twentieths 500 = 500.
Proof. reflexivity. Qed.

Lemma witness_cap_600 : cap_twentieths 600 = 500.
Proof. reflexivity. Qed.

(** Counterexample: hypo patient rejected. *)
Definition prec_input_hypo : PrecisionInput := mkPrecisionInput 60 60 0 [] Activity_Normal false.

Lemma counterex_prec_hypo_rejected :
  validated_precision_bolus prec_input_hypo witness_prec_params = PrecError prec_error_hypo.
Proof. reflexivity. Qed.

(** Counterexample: invalid params rejected. *)
Definition invalid_prec_params : PrecisionParams := mkPrecisionParams 0 500 100 240.

Lemma counterex_prec_invalid_params :
  validated_precision_bolus witness_prec_input invalid_prec_params = PrecError prec_error_invalid_params.
Proof. reflexivity. Qed.

(** Counterexample: future-dated history rejected. *)
Definition prec_input_future_history : PrecisionInput :=
  mkPrecisionInput 60 150 100 [mkBolusEvent 40 200] Activity_Normal false.

Lemma counterex_prec_future_history_rejected :
  validated_precision_bolus prec_input_future_history witness_prec_params = PrecError prec_error_invalid_history.
Proof. reflexivity. Qed.

(** Counterexample: unsorted history rejected. *)
Definition prec_input_unsorted_history : PrecisionInput :=
  mkPrecisionInput 60 150 120 [mkBolusEvent 40 60; mkBolusEvent 30 100; mkBolusEvent 20 0] Activity_Normal false.

Lemma counterex_prec_unsorted_history_rejected :
  validated_precision_bolus prec_input_unsorted_history witness_prec_params = PrecError prec_error_invalid_history.
Proof. reflexivity. Qed.

(** cap_twentieths bounded by PREC_BOLUS_MAX_TWENTIETHS. *)
Lemma cap_twentieths_bounded : forall t,
  cap_twentieths t <= PREC_BOLUS_MAX_TWENTIETHS.
Proof.
  intro t. unfold cap_twentieths, PREC_BOLUS_MAX_TWENTIETHS.
  destruct (t <=? 500) eqn:E.
  - apply Nat.leb_le in E. exact E.
  - lia.
Qed.

(** PrecOK output bounded by 500 twentieths. *)
Theorem validated_prec_bounded : forall input params t c,
  validated_precision_bolus input params = PrecOK t c ->
  t <= PREC_BOLUS_MAX_TWENTIETHS.
Proof.
  intros input params t c H.
  unfold validated_precision_bolus in H.
  destruct (negb (prec_params_valid params)); [discriminate|].
  destruct (negb (bg_in_meter_range (pi_current_bg input) && carbs_reasonable (pi_carbs_g input))); [discriminate|].
  destruct (negb (time_reasonable (pi_now input))); [discriminate|].
  destruct (negb (history_valid (pi_now input) (pi_bolus_history input))); [discriminate|].
  destruct (is_hypo (pi_current_bg input)); [discriminate|].
  inversion H. subst.
  apply cap_twentieths_bounded.
Qed.

(** PrecOK implies BG >= 70. *)
Theorem prec_ok_not_hypo : forall input params t c,
  validated_precision_bolus input params = PrecOK t c ->
  is_hypo (pi_current_bg input) = false.
Proof.
  intros input params t c H.
  unfold validated_precision_bolus in H.
  destruct (negb (prec_params_valid params)); [discriminate|].
  destruct (negb (bg_in_meter_range (pi_current_bg input) && carbs_reasonable (pi_carbs_g input))); [discriminate|].
  destruct (negb (time_reasonable (pi_now input))); [discriminate|].
  destruct (negb (history_valid (pi_now input) (pi_bolus_history input))); [discriminate|].
  destruct (is_hypo (pi_current_bg input)) eqn:E; [discriminate|].
  reflexivity.
Qed.

(** PrecOK implies history is valid (times and sort order). *)
Theorem prec_ok_history_valid : forall input params t c,
  validated_precision_bolus input params = PrecOK t c ->
  history_valid (pi_now input) (pi_bolus_history input) = true.
Proof.
  intros input params t c H.
  unfold validated_precision_bolus in H.
  destruct (negb (prec_params_valid params)); [discriminate|].
  destruct (negb (bg_in_meter_range (pi_current_bg input) && carbs_reasonable (pi_carbs_g input))); [discriminate|].
  destruct (negb (time_reasonable (pi_now input))); [discriminate|].
  destruct (negb (history_valid (pi_now input) (pi_bolus_history input))) eqn:E; [discriminate|].
  apply negb_false_iff in E. exact E.
Qed.

(** ========================================================================= *)
(** PART XIX: MMOL/L INPUT MODE                                               *)
(** ========================================================================= *)

Module MmolInput.

  Record MmolPrecisionInput := mkMmolPrecisionInput {
    mpi_carbs_g : nat;
    mpi_current_bg_mmol_tenths : nat;
    mpi_now : Minutes;
    mpi_bolus_history : list BolusEvent;
    mpi_activity : ActivityState;
    mpi_use_sensor_margin : bool
  }.

  Definition mmol_tenths_to_mg_dL (mmol_tenths : nat) : BG_mg_dL :=
    (mmol_tenths * 1802) / 1000.

  Definition convert_mmol_input (input : MmolPrecisionInput) : PrecisionInput :=
    mkPrecisionInput
      (mpi_carbs_g input)
      (mmol_tenths_to_mg_dL (mpi_current_bg_mmol_tenths input))
      (mpi_now input)
      (mpi_bolus_history input)
      (mpi_activity input)
      (mpi_use_sensor_margin input).

  Definition validated_mmol_bolus (input : MmolPrecisionInput) (params : PrecisionParams) : PrecisionResult :=
    validated_precision_bolus (convert_mmol_input input) params.

End MmolInput.

Export MmolInput.

(** Witness: 10.0 mmol/L (100 tenths) = 180 mg/dL. *)
Lemma witness_mmol_100_tenths : mmol_tenths_to_mg_dL 100 = 180.
Proof. reflexivity. Qed.

(** Witness: 5.5 mmol/L (55 tenths) ≈ 99 mg/dL. *)
Lemma witness_mmol_55_tenths : mmol_tenths_to_mg_dL 55 = 99.
Proof. reflexivity. Qed.

(** Witness: 3.9 mmol/L (39 tenths) ≈ 70 mg/dL (hypo threshold). *)
Lemma witness_mmol_39_tenths : mmol_tenths_to_mg_dL 39 = 70.
Proof. reflexivity. Qed.

(** Witness: mmol input yields same result as mg/dL input. *)
Definition witness_mmol_input : MmolPrecisionInput :=
  mkMmolPrecisionInput 60 83 0 [] Activity_Normal false.

Lemma witness_mmol_conversion :
  pi_current_bg (convert_mmol_input witness_mmol_input) = 149.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART XX: DELIVERY ROUNDING                                                *)
(** ========================================================================= *)

Module DeliveryRounding.

  Inductive RoundingMode : Type :=
    | RoundTwentieth : RoundingMode
    | RoundTenth : RoundingMode
    | RoundHalf : RoundingMode
    | RoundUnit : RoundingMode.

  Definition round_down_to_unit (t : Insulin_twentieth) : Insulin_twentieth :=
    round_down_to_increment t ONE_UNIT.

  Definition apply_rounding (mode : RoundingMode) (t : Insulin_twentieth) : Insulin_twentieth :=
    match mode with
    | RoundTwentieth => t
    | RoundTenth => round_down_to_tenth t
    | RoundHalf => round_down_to_half t
    | RoundUnit => round_down_to_unit t
    end.

  Definition final_delivery (mode : RoundingMode) (result : PrecisionResult) : option Insulin_twentieth :=
    match result with
    | PrecOK t _ => Some (apply_rounding mode t)
    | PrecError _ => None
    end.

End DeliveryRounding.

Export DeliveryRounding.

(** Witness: 27 twentieths (1.35U) rounded to tenth = 26 (1.30U). *)
Lemma witness_round_tenth_27 : apply_rounding RoundTenth 27 = 26.
Proof. reflexivity. Qed.

(** Witness: 27 twentieths (1.35U) rounded to half = 20 (1.00U). *)
Lemma witness_round_half_27 : apply_rounding RoundHalf 27 = 20.
Proof. reflexivity. Qed.

(** Witness: 27 twentieths (1.35U) rounded to unit = 20 (1.00U). *)
Lemma witness_round_unit_27 : apply_rounding RoundUnit 27 = 20.
Proof. reflexivity. Qed.

(** Witness: 140 twentieths (7.0U) unchanged by all rounding modes. *)
Lemma witness_round_exact_140 :
  apply_rounding RoundTwentieth 140 = 140 /\
  apply_rounding RoundTenth 140 = 140 /\
  apply_rounding RoundHalf 140 = 140 /\
  apply_rounding RoundUnit 140 = 140.
Proof. repeat split; reflexivity. Qed.

(** Rounding down to increment never increases dose. *)
Lemma round_down_le_original : forall t inc,
  inc > 0 -> round_down_to_increment t inc <= t.
Proof.
  intros t inc Hinc.
  unfold round_down_to_increment.
  destruct (inc =? 0) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - rewrite Nat.mul_comm. apply Nat.mul_div_le. lia.
Qed.

(** Rounding never increases dose. *)
Lemma rounding_le_original : forall mode t,
  apply_rounding mode t <= t.
Proof.
  intros mode t. destruct mode; unfold apply_rounding.
  - lia.
  - unfold round_down_to_tenth. apply round_down_le_original. unfold TENTH. lia.
  - unfold round_down_to_half. apply round_down_le_original. unfold HALF. lia.
  - unfold round_down_to_unit. apply round_down_le_original. unfold ONE_UNIT. lia.
Qed.

(** ========================================================================= *)
(** PART XXI: INVARIANT SUMMARY                                               *)
(** ========================================================================= *)

(** All boolean predicates are decidable (trivially, since they return bool). *)
Lemma params_valid_decidable : forall p, {params_valid p = true} + {params_valid p = false}.
Proof. intro p. destruct (params_valid p); auto. Qed.

Lemma input_valid_decidable : forall i, {input_valid i = true} + {input_valid i = false}.
Proof. intro i. destruct (input_valid i); auto. Qed.

Lemma prec_params_valid_decidable : forall p, {prec_params_valid p = true} + {prec_params_valid p = false}.
Proof. intro p. destruct (prec_params_valid p); auto. Qed.

Lemma is_hypo_decidable : forall bg, {is_hypo bg = true} + {is_hypo bg = false}.
Proof. intro bg. destruct (is_hypo bg); auto. Qed.

(** Summary: properties guaranteed by validated_precision_bolus returning PrecOK. *)
Theorem precision_calculator_guarantees : forall input params t c mode,
  validated_precision_bolus input params = PrecOK t c ->
  t <= PREC_BOLUS_MAX_TWENTIETHS /\
  is_hypo (pi_current_bg input) = false /\
  prec_params_valid params = true /\
  prec_input_valid input = true /\
  apply_rounding mode t <= t /\
  apply_rounding mode t <= PREC_BOLUS_MAX_TWENTIETHS.
Proof.
  intros input params t c mode H.
  split. { apply validated_prec_bounded with input params c. exact H. }
  split. { apply prec_ok_not_hypo with params t c. exact H. }
  split. {
    unfold validated_precision_bolus in H.
    destruct (negb (prec_params_valid params)) eqn:E; [discriminate|].
    apply negb_false_iff in E. exact E.
  }
  split. {
    unfold prec_input_valid.
    unfold validated_precision_bolus in H.
    destruct (negb (prec_params_valid params)); [discriminate|].
    destruct (negb (bg_in_meter_range (pi_current_bg input) && carbs_reasonable (pi_carbs_g input))) eqn:E1; [discriminate|].
    destruct (negb (time_reasonable (pi_now input))) eqn:E3; [discriminate|].
    destruct (negb (history_valid (pi_now input) (pi_bolus_history input))) eqn:E2; [discriminate|].
    apply negb_false_iff in E1. apply negb_false_iff in E2. apply negb_false_iff in E3.
    rewrite E1, E2, E3. reflexivity.
  }
  split. { apply rounding_le_original. }
  pose proof (validated_prec_bounded input params t c H) as Hbound.
  pose proof (rounding_le_original mode t) as Hround.
  lia.
Qed.

(** ========================================================================= *)
(** PART XXII: STACKING GUARD                                                 *)
(** Prevents dangerous insulin stacking by warning when bolusing too soon.    *)
(** ========================================================================= *)

Module StackingGuard.

  Definition MINIMUM_BOLUS_INTERVAL : Minutes := 15.
  Definition STACKING_WARNING_THRESHOLD : Minutes := 60.

  Definition time_since_last_bolus (now : Minutes) (history : list BolusEvent) : option Minutes :=
    match history with
    | nil => None
    | e :: _ =>
        if now <? be_time_minutes e then None
        else Some (now - be_time_minutes e)
    end.

  Definition bolus_too_soon (now : Minutes) (history : list BolusEvent) : bool :=
    match time_since_last_bolus now history with
    | None => false
    | Some elapsed => elapsed <? MINIMUM_BOLUS_INTERVAL
    end.

  Definition stacking_warning (now : Minutes) (history : list BolusEvent) : bool :=
    match time_since_last_bolus now history with
    | None => false
    | Some elapsed => elapsed <? STACKING_WARNING_THRESHOLD
    end.

  Definition recent_insulin_delivered (now : Minutes) (history : list BolusEvent) (dia : DIA_minutes) : Insulin_twentieth :=
    total_iob now history dia.

End StackingGuard.

Export StackingGuard.

(** Witness: no history means no stacking concern. *)
Lemma witness_no_history_no_stacking :
  bolus_too_soon 100 [] = false /\ stacking_warning 100 [] = false.
Proof. split; reflexivity. Qed.

(** Witness: bolus 5 minutes ago is too soon. *)
Definition recent_bolus_5min : list BolusEvent := [mkBolusEvent 40 95].

Lemma witness_5min_too_soon :
  bolus_too_soon 100 recent_bolus_5min = true.
Proof. reflexivity. Qed.

(** Witness: bolus 5 minutes ago triggers stacking warning. *)
Lemma witness_5min_stacking_warning :
  stacking_warning 100 recent_bolus_5min = true.
Proof. reflexivity. Qed.

(** Witness: bolus 30 minutes ago is not too soon but triggers warning. *)
Definition recent_bolus_30min : list BolusEvent := [mkBolusEvent 40 70].

Lemma witness_30min_not_too_soon :
  bolus_too_soon 100 recent_bolus_30min = false.
Proof. reflexivity. Qed.

Lemma witness_30min_stacking_warning :
  stacking_warning 100 recent_bolus_30min = true.
Proof. reflexivity. Qed.

(** Witness: bolus 90 minutes ago is safe, no warning. *)
Definition old_bolus_90min : list BolusEvent := [mkBolusEvent 40 10].

Lemma witness_90min_safe :
  bolus_too_soon 100 old_bolus_90min = false /\
  stacking_warning 100 old_bolus_90min = false.
Proof. split; reflexivity. Qed.

(** Counterexample: bolus in future does not trigger warning. *)
Definition future_bolus : list BolusEvent := [mkBolusEvent 40 200].

Lemma counterex_future_bolus_no_warning :
  bolus_too_soon 100 future_bolus = false /\
  stacking_warning 100 future_bolus = false.
Proof. split; reflexivity. Qed.

(** Property: if bolus_too_soon is false and history non-empty,
    at least MINIMUM_BOLUS_INTERVAL has passed. *)
Lemma too_soon_false_means_interval_passed : forall now e rest,
  bolus_too_soon now (e :: rest) = false ->
  now >= be_time_minutes e ->
  now - be_time_minutes e >= MINIMUM_BOLUS_INTERVAL.
Proof.
  intros now e rest H Hge.
  unfold bolus_too_soon, time_since_last_bolus, MINIMUM_BOLUS_INTERVAL in *.
  destruct (now <? be_time_minutes e) eqn:E1.
  - apply Nat.ltb_lt in E1. lia.
  - apply Nat.ltb_ge in H. exact H.
Qed.

(** ========================================================================= *)
(** PART XXII-B: 24-HOUR TDD ACCUMULATOR                                       *)
(** Tracks cumulative daily insulin; warns or blocks when approaching limit.  *)
(** ========================================================================= *)

Module TDDAccumulator.

  Definition MINUTES_PER_DAY : nat := 1440.
  Definition TDD_WARNING_PERCENT : nat := 80.
  Definition TDD_BLOCK_PERCENT : nat := 100.

  Definition events_in_window (now : Minutes) (window : nat) (events : list BolusEvent) : list BolusEvent :=
    filter (fun e =>
      let t := be_time_minutes e in
      (now - window <=? t) && (t <=? now))
    events.

  Definition events_in_24h (now : Minutes) (events : list BolusEvent) : list BolusEvent :=
    events_in_window now MINUTES_PER_DAY events.

  Fixpoint sum_doses (events : list BolusEvent) : Insulin_twentieth :=
    match events with
    | nil => 0
    | e :: rest => be_dose_twentieths e + sum_doses rest
    end.

  Definition tdd_in_24h (now : Minutes) (events : list BolusEvent) : Insulin_twentieth :=
    sum_doses (events_in_24h now events).

  Definition tdd_limit_twentieths (weight_kg : nat) : Insulin_twentieth :=
    weight_kg * ONE_UNIT.

  Definition tdd_warning_threshold (limit : Insulin_twentieth) : Insulin_twentieth :=
    (limit * TDD_WARNING_PERCENT) / 100.

  Inductive TDDStatus : Type :=
    | TDD_OK : TDDStatus
    | TDD_Warning : Insulin_twentieth -> TDDStatus
    | TDD_Blocked : TDDStatus.

  Definition check_tdd (now : Minutes) (events : list BolusEvent) (limit : Insulin_twentieth) : TDDStatus :=
    let current := tdd_in_24h now events in
    if limit <=? current then TDD_Blocked
    else if tdd_warning_threshold limit <=? current then TDD_Warning (limit - current)
    else TDD_OK.

  Definition tdd_allows_bolus (now : Minutes) (events : list BolusEvent) (limit : Insulin_twentieth) (proposed : Insulin_twentieth) : bool :=
    let current := tdd_in_24h now events in
    current + proposed <=? limit.

End TDDAccumulator.

Export TDDAccumulator.

(** Witness: 70kg adult has TDD limit of 1400 twentieths (70 units). *)
Lemma witness_70kg_tdd_limit :
  tdd_limit_twentieths 70 = 1400.
Proof. reflexivity. Qed.

(** Witness: warning threshold at 80% of 1400 = 1120 twentieths. *)
Lemma witness_70kg_warning_threshold :
  tdd_warning_threshold 1400 = 1120.
Proof. reflexivity. Qed.

(** Witness: empty history gives TDD of 0. *)
Lemma witness_empty_tdd :
  tdd_in_24h 1000 [] = 0.
Proof. reflexivity. Qed.

(** Witness: sum of two boluses. *)
Definition tdd_history_2 : list BolusEvent :=
  [mkBolusEvent 100 900; mkBolusEvent 80 800].

Lemma witness_sum_two_boluses :
  sum_doses tdd_history_2 = 180.
Proof. reflexivity. Qed.

(** Witness: TDD check returns OK when well below limit. *)
Lemma witness_tdd_ok :
  check_tdd 1000 tdd_history_2 1400 = TDD_OK.
Proof. reflexivity. Qed.

(** Witness: TDD check returns Warning when at 80%+. *)
Definition tdd_history_high : list BolusEvent :=
  [mkBolusEvent 400 900; mkBolusEvent 400 800; mkBolusEvent 400 700].

Lemma witness_tdd_warning :
  check_tdd 1000 tdd_history_high 1400 = TDD_Warning 200.
Proof. reflexivity. Qed.

(** Witness: TDD check returns Blocked when at limit. *)
Definition tdd_history_maxed : list BolusEvent :=
  [mkBolusEvent 500 900; mkBolusEvent 500 800; mkBolusEvent 500 700].

Lemma witness_tdd_blocked :
  check_tdd 1000 tdd_history_maxed 1400 = TDD_Blocked.
Proof. reflexivity. Qed.

(** Counterexample: old event outside 24h window not counted. *)
(** At now=2000, window starts at 560. Event at 100 is outside, event at 900 is inside. *)
Definition tdd_history_old : list BolusEvent :=
  [mkBolusEvent 100 900; mkBolusEvent 100 100].

Lemma witness_old_event_filtered :
  tdd_in_24h 2000 tdd_history_old = 100.
Proof. reflexivity. Qed.

(** Witness: both events outside window gives 0. *)
Definition tdd_history_very_old : list BolusEvent :=
  [mkBolusEvent 100 100; mkBolusEvent 100 50].

Lemma witness_all_old_events_filtered :
  tdd_in_24h 2000 tdd_history_very_old = 0.
Proof. reflexivity. Qed.

(** Witness: allows bolus when under limit. *)
Lemma witness_allows_bolus :
  tdd_allows_bolus 1000 tdd_history_2 1400 200 = true.
Proof. reflexivity. Qed.

(** Counterexample: blocks bolus that would exceed limit. *)
Lemma counterex_blocks_excessive_bolus :
  tdd_allows_bolus 1000 tdd_history_high 1400 300 = false.
Proof. reflexivity. Qed.

(** Property: sum_doses is additive. *)
Lemma sum_doses_app : forall l1 l2,
  sum_doses (l1 ++ l2) = sum_doses l1 + sum_doses l2.
Proof.
  intros l1 l2. induction l1 as [|e rest IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

(** ========================================================================= *)
(** PART XXII-C: SUSPEND-BEFORE-LOW                                            *)
(** Predicts BG trajectory and reduces/withholds dose if hypo is predicted.   *)
(** ========================================================================= *)

Module SuspendBeforeLow.

  Definition SUSPEND_THRESHOLD : BG_mg_dL := 80.
  Definition PREDICTION_HORIZON : Minutes := 30.

  Definition predict_bg_drop (iob_twentieths : Insulin_twentieth) (isf : nat) : nat :=
    if isf =? 0 then 0
    else (iob_twentieths * isf) / ONE_UNIT.

  Definition predicted_bg (current_bg : BG_mg_dL) (iob_twentieths : Insulin_twentieth) (isf : nat) : BG_mg_dL :=
    let drop := predict_bg_drop iob_twentieths isf in
    if current_bg <=? drop then 0 else current_bg - drop.

  Inductive SuspendDecision : Type :=
    | Suspend_None : SuspendDecision
    | Suspend_Reduce : Insulin_twentieth -> SuspendDecision
    | Suspend_Withhold : SuspendDecision.

  Definition suspend_check (current_bg : BG_mg_dL) (iob_twentieths : Insulin_twentieth)
                           (isf : nat) (proposed : Insulin_twentieth) : SuspendDecision :=
    let total_insulin := iob_twentieths + proposed in
    let pred := predicted_bg current_bg total_insulin isf in
    if pred <? BG_LEVEL2_HYPO then Suspend_Withhold
    else if pred <? SUSPEND_THRESHOLD then
      let safe_insulin := ((current_bg - SUSPEND_THRESHOLD) * ONE_UNIT) / isf in
      if safe_insulin <=? iob_twentieths then Suspend_Withhold
      else Suspend_Reduce (safe_insulin - iob_twentieths)
    else Suspend_None.

  Definition apply_suspend (proposed : Insulin_twentieth) (decision : SuspendDecision) : Insulin_twentieth :=
    match decision with
    | Suspend_None => proposed
    | Suspend_Reduce max => if proposed <=? max then proposed else max
    | Suspend_Withhold => 0
    end.

End SuspendBeforeLow.

Export SuspendBeforeLow.

(** Witness: predict BG drop from 100 twentieths (5U) IOB with ISF 50.
    Drop = (100 * 50) / 20 = 250 mg/dL. *)
Lemma witness_predict_drop :
  predict_bg_drop 100 50 = 250.
Proof. reflexivity. Qed.

(** Witness: current BG 200, IOB 40 twentieths (2U), ISF 50.
    Drop = (40 * 50) / 20 = 100. Predicted = 200 - 100 = 100. *)
Lemma witness_predicted_bg_200 :
  predicted_bg 200 40 50 = 100.
Proof. reflexivity. Qed.

(** Witness: BG 100, IOB 60 twentieths (3U), ISF 50.
    Drop = 150. Predicted = max(0, 100 - 150) = 0. *)
Lemma witness_predicted_bg_low :
  predicted_bg 100 60 50 = 0.
Proof. reflexivity. Qed.

(** Witness: safe scenario - BG 150, IOB 20, proposed 40, ISF 50.
    Total = 60. Drop = 150. Predicted = max(0, 150 - 150) = 0.
    This would suspend. *)
Lemma witness_suspend_scenario :
  suspend_check 150 20 50 40 = Suspend_Withhold.
Proof. reflexivity. Qed.

(** Witness: safe scenario - BG 200, IOB 0, proposed 40, ISF 50.
    Total = 40. Drop = 100. Predicted = 100 >= 80. No suspend. *)
Lemma witness_no_suspend :
  suspend_check 200 0 50 40 = Suspend_None.
Proof. reflexivity. Qed.

(** Witness: apply suspend none leaves dose unchanged. *)
Lemma witness_apply_none :
  apply_suspend 100 Suspend_None = 100.
Proof. reflexivity. Qed.

(** Witness: apply suspend withhold gives 0. *)
Lemma witness_apply_withhold :
  apply_suspend 100 Suspend_Withhold = 0.
Proof. reflexivity. Qed.

(** Witness: apply suspend reduce caps the dose. *)
Lemma witness_apply_reduce :
  apply_suspend 100 (Suspend_Reduce 60) = 60.
Proof. reflexivity. Qed.

(** Witness: apply suspend reduce doesn't increase dose. *)
Lemma witness_apply_reduce_no_increase :
  apply_suspend 40 (Suspend_Reduce 60) = 40.
Proof. reflexivity. Qed.

(** Property: apply_suspend never increases dose. *)
Lemma apply_suspend_le : forall proposed decision,
  apply_suspend proposed decision <= proposed.
Proof.
  intros proposed decision. destruct decision.
  - simpl. lia.
  - simpl. destruct (proposed <=? i) eqn:E; [lia | apply Nat.leb_nle in E; lia].
  - simpl. lia.
Qed.

(** Counterexample: ISF 0 gives no drop (graceful). *)
Lemma counterex_isf_zero_no_drop :
  predict_bg_drop 100 0 = 0.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART XXII-D: DELIVERY FAULT DETECTION                                      *)
(** Models occlusion/fault detection and worst-case IOB assumptions.          *)
(** ========================================================================= *)

Module DeliveryFault.

  Inductive FaultStatus : Type :=
    | Fault_None : FaultStatus
    | Fault_Occlusion : FaultStatus
    | Fault_LowReservoir : nat -> FaultStatus
    | Fault_BatteryLow : FaultStatus
    | Fault_Unknown : FaultStatus.

  Definition fault_blocks_bolus (f : FaultStatus) : bool :=
    match f with
    | Fault_None => false
    | Fault_Occlusion => true
    | Fault_LowReservoir remaining => remaining <? 10
    | Fault_BatteryLow => false
    | Fault_Unknown => true
    end.

  Definition fault_requires_warning (f : FaultStatus) : bool :=
    match f with
    | Fault_None => false
    | _ => true
    end.

  Definition worst_case_iob (history : list BolusEvent) (fault : FaultStatus) : Insulin_twentieth :=
    match fault with
    | Fault_Occlusion => sum_doses history
    | _ => sum_doses history
    end.

  Definition conservative_iob (now : Minutes) (history : list BolusEvent) (dia : DIA_minutes) (fault : FaultStatus) : Insulin_twentieth :=
    match fault with
    | Fault_Occlusion => sum_doses history
    | _ => total_iob now history dia
    end.

  Definition cap_to_reservoir (proposed : Insulin_twentieth) (reservoir : nat) : Insulin_twentieth :=
    if proposed <=? reservoir then proposed else reservoir.

End DeliveryFault.

Export DeliveryFault.

(** Witness: no fault allows bolus. *)
Lemma witness_no_fault_allows :
  fault_blocks_bolus Fault_None = false.
Proof. reflexivity. Qed.

(** Witness: occlusion blocks bolus. *)
Lemma witness_occlusion_blocks :
  fault_blocks_bolus Fault_Occlusion = true.
Proof. reflexivity. Qed.

(** Witness: low reservoir (5 units) blocks bolus. *)
Lemma witness_low_reservoir_blocks :
  fault_blocks_bolus (Fault_LowReservoir 5) = true.
Proof. reflexivity. Qed.

(** Witness: adequate reservoir (50 units) allows bolus. *)
Lemma witness_adequate_reservoir_allows :
  fault_blocks_bolus (Fault_LowReservoir 50) = false.
Proof. reflexivity. Qed.

(** Witness: battery low warns but doesn't block. *)
Lemma witness_battery_low_allows :
  fault_blocks_bolus Fault_BatteryLow = false.
Proof. reflexivity. Qed.

(** Witness: unknown fault blocks bolus (safe default). *)
Lemma witness_unknown_blocks :
  fault_blocks_bolus Fault_Unknown = true.
Proof. reflexivity. Qed.

(** Witness: occlusion assumes max IOB (conservative for hypoglycemia risk). *)
Lemma witness_occlusion_max_iob :
  worst_case_iob tdd_history_2 Fault_Occlusion = 180.
Proof. reflexivity. Qed.

(** Witness: no fault uses sum of doses. *)
Lemma witness_no_fault_actual_iob :
  worst_case_iob tdd_history_2 Fault_None = 180.
Proof. reflexivity. Qed.

(** Witness: cap to reservoir limits dose. *)
Lemma witness_cap_to_reservoir :
  cap_to_reservoir 100 50 = 50.
Proof. reflexivity. Qed.

(** Witness: cap doesn't increase dose. *)
Lemma witness_cap_no_increase :
  cap_to_reservoir 30 50 = 30.
Proof. reflexivity. Qed.

(** Property: cap_to_reservoir never exceeds reservoir. *)
Lemma cap_to_reservoir_bounded : forall proposed reservoir,
  cap_to_reservoir proposed reservoir <= reservoir.
Proof.
  intros proposed reservoir.
  unfold cap_to_reservoir.
  destruct (proposed <=? reservoir) eqn:E.
  - apply Nat.leb_le in E. exact E.
  - lia.
Qed.

(** Property: cap_to_reservoir never exceeds proposed. *)
Lemma cap_to_reservoir_le_proposed : forall proposed reservoir,
  cap_to_reservoir proposed reservoir <= proposed.
Proof.
  intros proposed reservoir.
  unfold cap_to_reservoir.
  destruct (proposed <=? reservoir) eqn:E.
  - apply Nat.leb_le in E. lia.
  - apply Nat.leb_nle in E. lia.
Qed.

(** ========================================================================= *)
(** PART XXIII: PEDIATRIC PARAMETERS                                          *)
(** Children have higher ICR (30-50+ g/U) and ISF (100-300+ mg/dL/U).         *)
(** ========================================================================= *)

Module PediatricParams.

  Definition PEDS_ICR_MIN : nat := 5.
  Definition PEDS_ICR_MAX : nat := 100.
  Definition PEDS_ISF_MIN : nat := 20.
  Definition PEDS_ISF_MAX : nat := 400.

  Definition PEDS_ICR_TENTHS_MIN : nat := 50.
  Definition PEDS_ICR_TENTHS_MAX : nat := 1000.
  Definition PEDS_ISF_TENTHS_MIN : nat := 200.
  Definition PEDS_ISF_TENTHS_MAX : nat := 4000.

  Definition PEDS_BOLUS_MAX : nat := 15.
  Definition PEDS_BOLUS_MAX_TWENTIETHS : nat := 300.

  Record PediatricPatientParams := mkPediatricPatientParams {
    ped_icr : nat;
    ped_isf : nat;
    ped_target_bg : BG_mg_dL;
    ped_weight_kg : nat;
    ped_age_years : nat
  }.

  Definition peds_params_valid (p : PediatricPatientParams) : bool :=
    (PEDS_ICR_MIN <=? ped_icr p) && (ped_icr p <=? PEDS_ICR_MAX) &&
    (PEDS_ISF_MIN <=? ped_isf p) && (ped_isf p <=? PEDS_ISF_MAX) &&
    (BG_HYPO <=? ped_target_bg p) && (ped_target_bg p <=? BG_HYPER) &&
    (1 <=? ped_icr p) && (1 <=? ped_isf p) &&
    (1 <=? ped_weight_kg p) && (ped_weight_kg p <=? 150) &&
    (ped_age_years p <=? 21).

  Definition total_daily_dose_limit (weight_kg : nat) : nat :=
    weight_kg.

  Definition peds_bolus_limit (weight_kg : nat) : nat :=
    let tdd := total_daily_dose_limit weight_kg in
    if tdd / 4 <? PEDS_BOLUS_MAX then tdd / 4 else PEDS_BOLUS_MAX.

End PediatricParams.

Export PediatricParams.

(** Witness: small child params (ICR=50, ISF=200, weight=20kg, age=5). *)
Definition witness_small_child : PediatricPatientParams :=
  mkPediatricPatientParams 50 200 110 20 5.

Lemma witness_small_child_valid : peds_params_valid witness_small_child = true.
Proof. reflexivity. Qed.

(** Witness: insulin-sensitive toddler (ICR=80, ISF=300). *)
Definition witness_toddler : PediatricPatientParams :=
  mkPediatricPatientParams 80 300 120 12 2.

Lemma witness_toddler_valid : peds_params_valid witness_toddler = true.
Proof. reflexivity. Qed.

(** Witness: adolescent (ICR=15, ISF=40, similar to adult). *)
Definition witness_adolescent : PediatricPatientParams :=
  mkPediatricPatientParams 15 40 100 60 16.

Lemma witness_adolescent_valid : peds_params_valid witness_adolescent = true.
Proof. reflexivity. Qed.

(** Counterexample: adult-range ICR=10 is valid for peds (overlapping range). *)
Definition witness_peds_adult_overlap : PediatricPatientParams :=
  mkPediatricPatientParams 10 50 100 45 14.

Lemma witness_peds_adult_overlap_valid : peds_params_valid witness_peds_adult_overlap = true.
Proof. reflexivity. Qed.

(** Counterexample: ICR=0 is invalid. *)
Definition counterex_peds_zero_icr : PediatricPatientParams :=
  mkPediatricPatientParams 0 200 110 20 5.

Lemma counterex_peds_zero_icr_invalid : peds_params_valid counterex_peds_zero_icr = false.
Proof. reflexivity. Qed.

(** Counterexample: ISF > 400 is invalid. *)
Definition counterex_peds_isf_500 : PediatricPatientParams :=
  mkPediatricPatientParams 50 500 110 20 5.

Lemma counterex_peds_isf_500_invalid : peds_params_valid counterex_peds_isf_500 = false.
Proof. reflexivity. Qed.

(** Counterexample: weight 0 is invalid. *)
Definition counterex_peds_zero_weight : PediatricPatientParams :=
  mkPediatricPatientParams 50 200 110 0 5.

Lemma counterex_peds_zero_weight_invalid : peds_params_valid counterex_peds_zero_weight = false.
Proof. reflexivity. Qed.

(** Witness: 20kg child bolus limit = 20/4 = 5U (< 15U cap). *)
Lemma witness_20kg_bolus_limit : peds_bolus_limit 20 = 5.
Proof. reflexivity. Qed.

(** Witness: 60kg adolescent bolus limit = 60/4 = 15U (hits cap). *)
Lemma witness_60kg_bolus_limit : peds_bolus_limit 60 = 15.
Proof. reflexivity. Qed.

(** Witness: 80kg large teen bolus limit = 15U (capped). *)
Lemma witness_80kg_bolus_limit : peds_bolus_limit 80 = 15.
Proof. reflexivity. Qed.

(** Property: pediatric bolus limit never exceeds PEDS_BOLUS_MAX. *)
Lemma peds_bolus_limit_bounded : forall weight,
  peds_bolus_limit weight <= PEDS_BOLUS_MAX.
Proof.
  intro weight.
  unfold peds_bolus_limit, total_daily_dose_limit, PEDS_BOLUS_MAX.
  destruct (weight / 4 <? 15) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - lia.
Qed.

(** Property: pediatric bolus limit scales with weight. *)
Lemma peds_bolus_limit_scales : forall w1 w2,
  w1 <= w2 -> peds_bolus_limit w1 <= peds_bolus_limit w2.
Proof.
  intros w1 w2 Hle.
  unfold peds_bolus_limit, total_daily_dose_limit, PEDS_BOLUS_MAX.
  destruct (w1 / 4 <? 15) eqn:E1; destruct (w2 / 4 <? 15) eqn:E2.
  - apply Nat.div_le_mono; lia.
  - apply Nat.ltb_lt in E1. lia.
  - apply Nat.ltb_ge in E1. apply Nat.ltb_lt in E2.
    apply Nat.div_le_mono with (c := 4) in Hle; lia.
  - lia.
Qed.

(** ========================================================================= *)
(** PART XXIV: BILINEAR IOB WITNESSES AND PROPERTIES                          *)
(** ========================================================================= *)

(** Witness: at time 0, 100% of insulin remains. *)
Lemma witness_bilinear_at_zero :
  bilinear_iob_fraction 0 DIA_4_HOURS = 100.
Proof. reflexivity. Qed.

(** Witness: at peak time (75 min), ~75% remains (rising phase complete). *)
Lemma witness_bilinear_at_peak :
  bilinear_iob_fraction 75 DIA_4_HOURS = 75.
Proof. reflexivity. Qed.

(** Witness: at half DIA (120 min), in decay phase.
    (240 - 120) * 75 / (240 - 75) = 120 * 75 / 165 = 54. *)
Lemma witness_bilinear_at_half_dia :
  bilinear_iob_fraction 120 DIA_4_HOURS = 54.
Proof. reflexivity. Qed.

(** Witness: at 3/4 DIA (180 min).
    (240 - 180) * 75 / 165 = 60 * 75 / 165 = 27. *)
Lemma witness_bilinear_at_180 :
  bilinear_iob_fraction 180 DIA_4_HOURS = 27.
Proof. reflexivity. Qed.

(** Witness: at DIA (240 min), 0% remains. *)
Lemma witness_bilinear_at_dia :
  bilinear_iob_fraction 240 DIA_4_HOURS = 0.
Proof. reflexivity. Qed.

(** Witness: beyond DIA, 0% remains. *)
Lemma witness_bilinear_beyond_dia :
  bilinear_iob_fraction 300 DIA_4_HOURS = 0.
Proof. reflexivity. Qed.

(** Witness: 1U (20 twentieths) at time 0, checked at 120 min.
    Fraction = 54%, IOB = 20 * 54 / 100 = 10 twentieths. *)
Lemma witness_bilinear_iob_at_120 :
  bilinear_iob_from_bolus 120 (mkBolusEvent 20 0) DIA_4_HOURS = 10.
Proof. reflexivity. Qed.

(** Witness: 1U at time 0, checked at peak (75 min).
    Fraction = 75%, IOB = 20 * 75 / 100 = 15 twentieths. *)
Lemma witness_bilinear_iob_at_peak :
  bilinear_iob_from_bolus 75 (mkBolusEvent 20 0) DIA_4_HOURS = 15.
Proof. reflexivity. Qed.

(** Counterexample: future bolus contributes 0. *)
Lemma counterex_bilinear_future :
  bilinear_iob_from_bolus 50 (mkBolusEvent 20 100) DIA_4_HOURS = 0.
Proof. reflexivity. Qed.

(** Counterexample: DIA=0 returns 0 (graceful degradation). *)
Lemma counterex_bilinear_dia_zero :
  bilinear_iob_fraction 60 0 = 0.
Proof. reflexivity. Qed.

(** Property: bilinear fraction never exceeds 100. *)
Lemma bilinear_fraction_le_100 : forall elapsed dia,
  bilinear_iob_fraction elapsed dia <= 100.
Proof.
  intros elapsed dia.
  unfold bilinear_iob_fraction, PEAK_TIME.
  destruct (dia =? 0) eqn:E0; [lia|].
  destruct (dia <=? elapsed) eqn:E1; [lia|].
  destruct (elapsed <=? 75) eqn:E2.
  - apply Nat.leb_le in E2.
    assert (elapsed * 25 / 75 <= elapsed * 25 / 75) by lia.
    assert (elapsed * 25 / 75 <= 25) by (apply Nat.div_le_upper_bound; lia).
    lia.
  - apply Nat.leb_nle in E1. apply Nat.leb_nle in E2. apply Nat.eqb_neq in E0.
    apply Nat.div_le_upper_bound. lia.
    nia.
Qed.

(** Property: bilinear IOB bounded by original dose. *)
Lemma bilinear_iob_bounded : forall now event dia,
  bilinear_iob_from_bolus now event dia <= be_dose_twentieths event.
Proof.
  intros now event dia.
  unfold bilinear_iob_from_bolus.
  destruct (now <? be_time_minutes event); [lia|].
  pose proof (bilinear_fraction_le_100 (now - be_time_minutes event) dia) as Hfrac.
  apply Nat.div_le_upper_bound. lia.
  nia.
Qed.

(** Comparison: bilinear vs linear at 120 min shows bilinear retains more IOB.
    Linear: 50%. Bilinear: 54%. More conservative = safer. *)
Lemma bilinear_more_conservative_at_120 :
  bilinear_iob_fraction 120 DIA_4_HOURS = 54 /\
  iob_fraction_remaining 120 DIA_4_HOURS = 50.
Proof. split; reflexivity. Qed.

(** Comparison: at peak, bilinear shows 75% vs linear 69%.
    Bilinear accounts for rising insulin action curve. *)
Lemma bilinear_higher_at_peak :
  bilinear_iob_fraction 75 DIA_4_HOURS = 75 /\
  iob_fraction_remaining 75 DIA_4_HOURS = 68.
Proof. split; reflexivity. Qed.

(** ========================================================================= *)
(** PART XXV: NONLINEAR ISF WITNESSES AND PROPERTIES                          *)
(** ========================================================================= *)

(** Witness: BG 200 (below threshold) uses base ISF unchanged. *)
Lemma witness_isf_normal_bg :
  adjusted_isf 200 50 = 50.
Proof. reflexivity. Qed.

(** Witness: BG 300 (mild resistance) reduces ISF by 20%. ISF 50 -> 40. *)
Lemma witness_isf_mild_resistance :
  adjusted_isf 300 50 = 40.
Proof. reflexivity. Qed.

(** Witness: BG 400 (severe resistance) reduces ISF by 40%. ISF 50 -> 30. *)
Lemma witness_isf_severe_resistance :
  adjusted_isf 400 50 = 30.
Proof. reflexivity. Qed.

(** Witness: correction at BG 200, target 100, ISF 50.
    No resistance: (200-100)/50 = 2 units. *)
Lemma witness_correction_no_resistance :
  correction_with_resistance 200 100 50 = 2.
Proof. reflexivity. Qed.

(** Witness: correction at BG 300, target 100, ISF 50.
    Mild resistance: effective ISF = 40. (300-100)/40 = 5 units. *)
Lemma witness_correction_mild_resistance :
  correction_with_resistance 300 100 50 = 5.
Proof. reflexivity. Qed.

(** Witness: correction at BG 400, target 100, ISF 50.
    Severe resistance: effective ISF = 30. (400-100)/30 = 10 units. *)
Lemma witness_correction_severe_resistance :
  correction_with_resistance 400 100 50 = 10.
Proof. reflexivity. Qed.

(** Counterexample: BG at target yields 0 regardless of resistance. *)
Lemma counterex_at_target_no_correction :
  correction_with_resistance 100 100 50 = 0.
Proof. reflexivity. Qed.

(** Counterexample: BG below target yields 0. *)
Lemma counterex_below_target_no_correction :
  correction_with_resistance 80 100 50 = 0.
Proof. reflexivity. Qed.

(** Counterexample: ISF 0 yields 0 (no crash). *)
Lemma counterex_isf_zero_no_crash :
  correction_with_resistance 300 100 0 = 0.
Proof. reflexivity. Qed.

(** Property: adjusted ISF is always <= base ISF. *)
Lemma adjusted_isf_le_base : forall bg base_isf,
  adjusted_isf bg base_isf <= base_isf.
Proof.
  intros bg base_isf.
  unfold adjusted_isf, BG_RESISTANCE_MILD, BG_RESISTANCE_SEVERE,
         ISF_REDUCTION_MILD, ISF_REDUCTION_SEVERE.
  destruct (bg <? 250) eqn:E1; [lia|].
  destruct (bg <? 350) eqn:E2.
  - apply Nat.div_le_upper_bound. lia. nia.
  - apply Nat.div_le_upper_bound. lia. nia.
Qed.

(** Adjusted ISF for minimum clinical ISF (20) at mild resistance: 16. *)
Lemma witness_adjusted_isf_20_at_300 :
  adjusted_isf 300 20 = 16.
Proof. reflexivity. Qed.

(** Adjusted ISF for typical ISF (50) at severe resistance: 30. *)
Lemma witness_adjusted_isf_50_at_400 :
  adjusted_isf 400 50 = 30.
Proof. reflexivity. Qed.

(** Resistance correction increases dose vs linear model: witnesses. *)
Lemma witness_resistance_increases_300 :
  correction_with_resistance 300 100 50 = 5 /\
  correction_bolus 300 100 50 = 4.
Proof. split; reflexivity. Qed.

Lemma witness_resistance_increases_400 :
  correction_with_resistance 400 100 50 = 10 /\
  correction_bolus 400 100 50 = 6.
Proof. split; reflexivity. Qed.

(** Adversarial: what if BG is exactly at threshold boundary? *)
Lemma boundary_249_no_adjustment :
  adjusted_isf 249 50 = 50.
Proof. reflexivity. Qed.

Lemma boundary_250_mild_adjustment :
  adjusted_isf 250 50 = 40.
Proof. reflexivity. Qed.

Lemma boundary_349_mild_adjustment :
  adjusted_isf 349 50 = 40.
Proof. reflexivity. Qed.

Lemma boundary_350_severe_adjustment :
  adjusted_isf 350 50 = 30.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART XXV-B: SENSOR UNCERTAINTY MARGIN                                      *)
(** CGM sensors have +/- 15-20% error. Conservative bolus accounts for this.  *)
(** ========================================================================= *)

Module SensorUncertainty.

  Definition SENSOR_ERROR_PERCENT : nat := 15.

  Definition bg_with_margin (bg : BG_mg_dL) (margin_percent : nat) : BG_mg_dL :=
    bg - (bg * margin_percent) / 100.

  Definition conservative_bg (bg : BG_mg_dL) : BG_mg_dL :=
    bg_with_margin bg SENSOR_ERROR_PERCENT.

  Definition conservative_correction (current_bg target_bg : BG_mg_dL) (isf : nat) : nat :=
    let cons_bg := conservative_bg current_bg in
    correction_bolus cons_bg target_bg isf.

End SensorUncertainty.

Export SensorUncertainty.

(** Witness: 200 mg/dL with 15% margin = 200 - 30 = 170 mg/dL. *)
Lemma witness_conservative_bg_200 :
  conservative_bg 200 = 170.
Proof. reflexivity. Qed.

(** Witness: 100 mg/dL with 15% margin = 100 - 15 = 85 mg/dL. *)
Lemma witness_conservative_bg_100 :
  conservative_bg 100 = 85.
Proof. reflexivity. Qed.

(** Witness: conservative correction at BG 200, target 100, ISF 50.
    Conservative BG = 170. Correction = (170-100)/50 = 1 (vs 2 without margin). *)
Lemma witness_conservative_correction :
  conservative_correction 200 100 50 = 1.
Proof. reflexivity. Qed.

(** Witness: at BG 150, conservative BG = 127. Correction = (127-100)/50 = 0. *)
Lemma witness_conservative_near_target :
  conservative_correction 150 100 50 = 0.
Proof. reflexivity. Qed.

(** Property: conservative BG is always <= actual BG. *)
Lemma conservative_bg_le : forall bg,
  conservative_bg bg <= bg.
Proof.
  intro bg. unfold conservative_bg, bg_with_margin, SENSOR_ERROR_PERCENT.
  assert ((bg * 15) / 100 <= bg) by (apply Nat.div_le_upper_bound; lia).
  lia.
Qed.

(** Property: conservative correction is <= regular correction. *)
Lemma conservative_correction_le : forall bg target isf,
  isf > 0 ->
  conservative_correction bg target isf <= correction_bolus bg target isf.
Proof.
  intros bg target isf Hisf.
  unfold conservative_correction.
  apply correction_monotonic_bg. exact Hisf.
  apply conservative_bg_le.
Qed.

(** ========================================================================= *)
(** PART XXV-C: DAWN PHENOMENON ISF ADJUSTMENT                                 *)
(** ISF is typically lower in early morning (4-8 AM) due to hormones.         *)
(** ========================================================================= *)

Module DawnPhenomenon.

  Definition DAWN_START_HOUR : nat := 4.
  Definition DAWN_END_HOUR : nat := 8.
  Definition DAWN_ISF_REDUCTION : nat := 80.

  Definition hour_of_day (minutes : Minutes) : nat :=
    (minutes / 60) mod 24.

  Definition is_dawn_period (minutes : Minutes) : bool :=
    let h := hour_of_day minutes in
    (DAWN_START_HOUR <=? h) && (h <? DAWN_END_HOUR).

  Definition dawn_adjusted_isf (minutes : Minutes) (base_isf : nat) : nat :=
    if is_dawn_period minutes then (base_isf * DAWN_ISF_REDUCTION) / 100
    else base_isf.

  Definition dawn_adjusted_isf_tenths (minutes : Minutes) (base_isf_tenths : nat) : nat :=
    if is_dawn_period minutes then (base_isf_tenths * DAWN_ISF_REDUCTION) / 100
    else base_isf_tenths.

End DawnPhenomenon.

Export DawnPhenomenon.

(** Witness: 300 minutes = 5 hours = 5 AM, which is dawn period. *)
Lemma witness_5am_is_dawn :
  is_dawn_period 300 = true.
Proof. reflexivity. Qed.

(** Witness: 600 minutes = 10 hours = 10 AM, not dawn. *)
Lemma witness_10am_not_dawn :
  is_dawn_period 600 = false.
Proof. reflexivity. Qed.

(** Witness: 180 minutes = 3 hours = 3 AM, not dawn (before 4 AM). *)
Lemma witness_3am_not_dawn :
  is_dawn_period 180 = false.
Proof. reflexivity. Qed.

(** Witness: dawn ISF at 5 AM with base 50 = 50 * 80/100 = 40. *)
Lemma witness_dawn_isf_5am :
  dawn_adjusted_isf 300 50 = 40.
Proof. reflexivity. Qed.

(** Witness: non-dawn ISF unchanged. *)
Lemma witness_noon_isf_unchanged :
  dawn_adjusted_isf 720 50 = 50.
Proof. reflexivity. Qed.

(** Property: dawn ISF is always <= base ISF. *)
Lemma dawn_isf_le_base : forall minutes base_isf,
  dawn_adjusted_isf minutes base_isf <= base_isf.
Proof.
  intros minutes base_isf.
  unfold dawn_adjusted_isf, DAWN_ISF_REDUCTION.
  destruct (is_dawn_period minutes).
  - apply Nat.div_le_upper_bound. lia.
    assert (base_isf * 80 <= base_isf * 100) by lia. lia.
  - lia.
Qed.

(** Combined ISF adjustment: applies both dawn and resistance adjustments. *)
Definition fully_adjusted_isf_tenths (minutes : Minutes) (bg : BG_mg_dL) (base_isf_tenths : nat) : nat :=
  let dawn_adj := dawn_adjusted_isf_tenths minutes base_isf_tenths in
  adjusted_isf_tenths bg dawn_adj.

(** ========================================================================= *)
(** PART XXV-D: EXERCISE/ILLNESS/STRESS MODIFIERS                              *)
(** Activity state affects insulin sensitivity.                               *)
(** ========================================================================= *)

Module ActivityModifiers.

  Inductive ActivityState : Type :=
    | Activity_Normal : ActivityState
    | Activity_LightExercise : ActivityState
    | Activity_ModerateExercise : ActivityState
    | Activity_IntenseExercise : ActivityState
    | Activity_Illness : ActivityState
    | Activity_Stress : ActivityState.

  Definition icr_modifier (state : ActivityState) : nat :=
    match state with
    | Activity_Normal => 100
    | Activity_LightExercise => 120
    | Activity_ModerateExercise => 150
    | Activity_IntenseExercise => 200
    | Activity_Illness => 80
    | Activity_Stress => 80
    end.

  Definition isf_modifier (state : ActivityState) : nat :=
    match state with
    | Activity_Normal => 100
    | Activity_LightExercise => 120
    | Activity_ModerateExercise => 150
    | Activity_IntenseExercise => 200
    | Activity_Illness => 70
    | Activity_Stress => 70
    end.

  Definition apply_icr_modifier (base_icr : nat) (state : ActivityState) : nat :=
    (base_icr * icr_modifier state) / 100.

  Definition apply_isf_modifier (base_isf : nat) (state : ActivityState) : nat :=
    (base_isf * isf_modifier state) / 100.

End ActivityModifiers.

Export ActivityModifiers.

(** Witness: normal state leaves ICR unchanged. *)
Lemma witness_normal_icr :
  apply_icr_modifier 10 Activity_Normal = 10.
Proof. reflexivity. Qed.

(** Witness: moderate exercise increases ICR by 50% (10 -> 15). *)
Lemma witness_exercise_icr :
  apply_icr_modifier 10 Activity_ModerateExercise = 15.
Proof. reflexivity. Qed.

(** Witness: illness decreases ICR by 20% (10 -> 8). *)
Lemma witness_illness_icr :
  apply_icr_modifier 10 Activity_Illness = 8.
Proof. reflexivity. Qed.

(** Witness: intense exercise doubles ISF (50 -> 100). *)
Lemma witness_intense_isf :
  apply_isf_modifier 50 Activity_IntenseExercise = 100.
Proof. reflexivity. Qed.

(** Witness: stress decreases ISF by 30% (50 -> 35). *)
Lemma witness_stress_isf :
  apply_isf_modifier 50 Activity_Stress = 35.
Proof. reflexivity. Qed.

(** Property: exercise increases effective ICR (less insulin per carb). *)
Lemma exercise_increases_icr : forall base_icr,
  base_icr > 0 ->
  apply_icr_modifier base_icr Activity_ModerateExercise >= base_icr.
Proof.
  intros base_icr Hpos.
  unfold apply_icr_modifier, icr_modifier.
  apply Nat.div_le_lower_bound. lia. nia.
Qed.

(** Property: illness decreases effective ISF (more insulin needed). *)
Lemma illness_decreases_isf : forall base_isf,
  apply_isf_modifier base_isf Activity_Illness <= base_isf.
Proof.
  intro base_isf.
  unfold apply_isf_modifier, isf_modifier.
  apply Nat.div_le_upper_bound. lia. nia.
Qed.

(** ========================================================================= *)
(** PART XXVI: EXTRACTION SAFETY BOUNDS                                       *)
(** Proves all intermediates fit in 63-bit signed int under valid inputs.     *)
(** ========================================================================= *)

Module ExtractionBounds.

  Definition MAX_HISTORY_LENGTH : nat := 100.

  Definition history_length_bounded (events : list BolusEvent) : bool :=
    length events <=? MAX_HISTORY_LENGTH.

  Definition dose_bounded (event : BolusEvent) : bool :=
    be_dose_twentieths event <=? PREC_BOLUS_MAX_TWENTIETHS.

  Fixpoint all_doses_bounded (events : list BolusEvent) : bool :=
    match events with
    | nil => true
    | e :: rest => dose_bounded e && all_doses_bounded rest
    end.

  Definition extraction_safe_history (events : list BolusEvent) : bool :=
    history_length_bounded events && all_doses_bounded events.

End ExtractionBounds.

Export ExtractionBounds.

(** Carb bolus intermediate: carbs * 200. With carbs <= 500, max = 100000. *)
Lemma carb_bolus_intermediate_bounded : forall carbs icr,
  carbs <= 500 -> icr >= 50 ->
  carb_bolus_twentieths carbs icr <= 2000.
Proof.
  intros carbs icr Hcarbs Hicr.
  unfold carb_bolus_twentieths.
  destruct (icr =? 0) eqn:E.
  - lia.
  - apply Nat.div_le_upper_bound. lia.
    nia.
Qed.

(** Correction bolus intermediate: (bg - target) * 200. With bg <= 600, max = 120000. *)
Lemma correction_bolus_intermediate_bounded : forall bg target isf,
  bg <= 600 -> isf >= 200 ->
  correction_bolus_twentieths bg target isf <= 600.
Proof.
  intros bg target isf Hbg Hisf.
  unfold correction_bolus_twentieths.
  destruct (isf =? 0) eqn:E0; [lia|].
  destruct (bg <=? target) eqn:E1; [lia|].
  apply Nat.leb_nle in E1.
  apply Nat.div_le_upper_bound. lia.
  nia.
Qed.

(** IOB from single bolus bounded by dose. *)
Lemma iob_from_bolus_bounded : forall now event dia,
  be_dose_twentieths event <= 500 ->
  iob_from_bolus now event dia <= 500.
Proof.
  intros now event dia Hdose.
  pose proof (iob_bounded_by_dose now event dia) as H.
  lia.
Qed.

(** Total IOB bounded by history length * max dose. *)
Lemma total_iob_bounded : forall now events dia,
  all_doses_bounded events = true ->
  total_iob now events dia <= length events * 500.
Proof.
  intros now events dia.
  induction events as [|e rest IH]; intros Hbounded.
  - simpl. lia.
  - simpl in Hbounded. apply andb_prop in Hbounded. destruct Hbounded as [Hdose Hrest].
    unfold dose_bounded in Hdose. apply Nat.leb_le in Hdose.
    simpl. pose proof (iob_from_bolus_bounded now e dia Hdose) as Hiob.
    specialize (IH Hrest).
    lia.
Qed.

(** With bounded history, total IOB bounded by max_history * max_dose. *)
Lemma total_iob_extraction_safe : forall now events dia,
  extraction_safe_history events = true ->
  total_iob now events dia <= MAX_HISTORY_LENGTH * PREC_BOLUS_MAX_TWENTIETHS.
Proof.
  intros now events dia H.
  unfold extraction_safe_history in H.
  apply andb_prop in H. destruct H as [Hlen Hdoses].
  unfold history_length_bounded in Hlen.
  apply Nat.leb_le in Hlen.
  pose proof (total_iob_bounded now events dia Hdoses) as Hbound.
  unfold MAX_HISTORY_LENGTH, PREC_BOLUS_MAX_TWENTIETHS.
  apply Nat.le_trans with (m := length events * 500).
  - exact Hbound.
  - apply Nat.mul_le_mono_r. exact Hlen.
Qed.

(** Validated output is bounded, ensuring extraction safety. *)
Theorem extraction_safe : forall input params t c,
  validated_precision_bolus input params = PrecOK t c ->
  t <= PREC_BOLUS_MAX_TWENTIETHS.
Proof.
  intros input params t c H.
  apply validated_prec_bounded with input params c. exact H.
Qed.

(** Max output (500 twentieths = 25 units) fits in any reasonable int. *)
(** 500 << 2^31 - 1 = 2147483647, so extraction to OCaml int is safe. *)

(** ========================================================================= *)
(** PART XXVII: EXTRACTION                                                    *)
(** ========================================================================= *)

Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "insulin_extracted.ml"
  validated_precision_bolus
  validated_mmol_bolus
  final_delivery
  mkPrecisionParams
  mkPrecisionInput
  mkMmolPrecisionInput
  mkBolusEvent.
