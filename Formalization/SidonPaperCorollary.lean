import Formalization.SidonDiameter
import Formalization.Cardinality
import Formalization.Centering

/-!
# Paper-facing corollaries for shifted Sidon labels

The quantitative shifted-Sidon theorem is naturally stated for targets that
have first been centered. This file packages the elementary change of
coordinates back to the original target list and then connects the resulting
double sumset to the interval-family language used in the paper.
-/

namespace IntervalBases

/-- Center a target list before translating the constructed basis by `shift`.
For double sumsets, the corresponding target translation is `2 * shift`. -/
def centerTargetsH2 (shift : Int) (targets : List Int) : List Int :=
  targets.map fun target => target - 2 * shift

@[simp]
theorem length_centerTargetsH2 (shift : Int) (targets : List Int) :
    (centerTargetsH2 shift targets).length = targets.length := by
  simp [centerTargetsH2]

/-- The centered index corresponding to an index of the original list. -/
def centerTargetsH2Index {targets : List Int} (shift : Int)
    (index : Fin targets.length) :
    Fin (centerTargetsH2 shift targets).length :=
  Fin.cast (by simp) index

@[simp]
theorem get_centerTargetsH2_centerTargetsH2Index {targets : List Int}
    (shift : Int) (index : Fin targets.length) :
    (centerTargetsH2 shift targets).get (centerTargetsH2Index shift index) =
      targets.get index - 2 * shift := by
  simp [centerTargetsH2Index, centerTargetsH2]

/-- Membership in the centered target set is exactly membership in the
original target set after undoing the double-sumset translation. -/
theorem mem_prescribedTargets_centerTargetsH2_sub_iff
    {targets : List Int} {shift x : Int} :
    Membership.mem (prescribedTargets (centerTargetsH2 shift targets))
        (x - 2 * shift) <->
      Membership.mem (prescribedTargets targets) x := by
  rw [mem_prescribedTargets_iff_mem, mem_prescribedTargets_iff_mem]
  simp [centerTargetsH2]

/-- A translated isolated pattern for centered targets is an ordinary
isolated pattern for the original target list. -/
theorem hasIsolatedExceptionalPatternH2_of_centered_translation
    {targets : List Int} {basis : Set Int} {shift : Int} {d : Nat}
    (hpattern :
      HasTranslatedIsolatedExceptionalPatternH2
        (centerTargetsH2 shift targets) basis shift d) :
    HasIsolatedExceptionalPatternH2 targets basis d := by
  rw [HasTranslatedIsolatedExceptionalPatternH2] at hpattern
  rw [HasIsolatedExceptionalPatternH2]
  obtain ⟨htargets, htargetGaps, hexceptionalGaps⟩ := hpattern
  refine ⟨?_, ?_, ?_⟩
  · intro index
    have htarget := htargets (centerTargetsH2Index shift index)
    rw [get_centerTargetsH2_centerTargetsH2Index] at htarget
    simpa using htarget
  · intro x hx hxExceptional index
    have hxCentered :
        Not (Membership.mem
          (prescribedTargets (centerTargetsH2 shift targets))
          (x - 2 * shift)) := by
      rwa [mem_prescribedTargets_centerTargetsH2_sub_iff]
    have hgap :=
      htargetGaps x hx hxCentered (centerTargetsH2Index shift index)
    rw [get_centerTargetsH2_centerTargetsH2Index] at hgap
    simpa using hgap
  · intro x hx hxExceptional y hy hne
    have hxCentered :
        Not (Membership.mem
          (prescribedTargets (centerTargetsH2 shift targets))
          (x - 2 * shift)) := by
      rwa [mem_prescribedTargets_centerTargetsH2_sub_iff]
    exact hexceptionalGaps x hx hxCentered y hy hne

/-- Any isolated-target double-sumset pattern on a flattened separated
interval family has exactly the listed nontrivial intervals. -/
theorem hasIsolatedExceptionalPatternH2_hasExactlyNontrivialIntervals
    {starts : List Int} {n d : Nat} {basis : Set Int}
    (hsep : SeparatedStarts starts n) (hd : 2 <= d)
    (hpattern :
      HasIsolatedExceptionalPatternH2 (intervalTargets starts n) basis d) :
    HasExactlyNontrivialIntervals (hFoldSumset basis 2) starts n := by
  rw [HasIsolatedExceptionalPatternH2] at hpattern
  constructor
  · intro start hstart x hx
    have hxTarget :
        Membership.mem (prescribedTargets (intervalTargets starts n)) x := by
      rw [prescribedTargets_intervalTargets]
      exact ⟨start, hstart, hx.1, hx.2⟩
    have hxList :
        x ∈ intervalTargets starts n :=
      mem_prescribedTargets_iff_mem.mp hxTarget
    obtain ⟨index, hindex⟩ := List.get_of_mem hxList
    simpa only [hindex] using hpattern.1 index
  · intro x hx hxSucc
    have hxTarget :
        Membership.mem (prescribedTargets (intervalTargets starts n)) x := by
      by_contra hxExceptional
      have hgap := hpattern.2.2 x hx hxExceptional (x + 1) hxSucc (by omega)
      norm_num at hgap
      omega
    have hxSuccTarget :
        Membership.mem (prescribedTargets (intervalTargets starts n)) (x + 1) := by
      by_contra hxSuccExceptional
      have hgap := hpattern.2.2 (x + 1) hxSucc hxSuccExceptional x hx (by omega)
      norm_num at hgap
      omega
    rw [prescribedTargets_intervalTargets] at hxTarget hxSuccTarget
    exact exists_interval_of_mem_intervalUnion_of_succ_mem hsep hxTarget hxSuccTarget

/-- The basis obtained by centering a target list, applying shifted-Sidon
labels, and translating back. -/
def centeredShiftedSidonBasis (targets : List Int) (shift : Int)
    (M p : Nat) : Set Int :=
  translateIntegerSet shift
    (genericConstructedBasis 2 (centerTargetsH2 shift targets)
      (fun index => (M : Int) * shiftedSidonLabel p index.val))

/-- The translated shifted-Sidon basis retains the quadratic lower bound
already visible among its negative generators. -/
theorem centeredShiftedSidonBasis_diameter_lower_bound
    {targets : List Int} {shift : Int} {M p D : Nat}
    (hlength : 1 <= targets.length) (hm : targets.length <= p)
    (hdiameter : SetDiameterAtMost
      (centeredShiftedSidonBasis targets shift M p) D) :
    2 * M * targets.length * (targets.length - 1) <= D := by
  have hinternal :
      SetDiameterAtMost
        (genericConstructedBasis 2 (centerTargetsH2 shift targets)
          (fun index => (M : Int) * shiftedSidonLabel p index.val)) D :=
    setDiameterAtMost_of_translateIntegerSet shift (by
      simpa [centeredShiftedSidonBasis] using hdiameter)
  simpa using
    (shiftedSidonBasis_diameter_lower_bound
      (targets := centerTargetsH2 shift targets) (p := p) (M := M)
      (D := D) (by simpa using hlength) (by simpa using hm) hinternal)

/-- Distinct scaled shifted-Sidon labels remain at least `M` apart. -/
theorem scaledShiftedSidonLabel_gap
    {m p M : Nat} (hprime : Nat.Prime p) (hodd : Not (p = 2))
    (hm : m <= p) {left right : Fin m} (hne : Not (left = right)) :
    M <=
      ((M : Int) * shiftedSidonLabel p left.val -
        (M : Int) * shiftedSidonLabel p right.val).natAbs := by
  have hlabelNe :
      Not (shiftedSidonLabel p left.val = shiftedSidonLabel p right.val) := by
    intro heq
    apply hne
    apply Fin.ext
    apply shiftedSidonNatLabel_injective_of_lt_prime hprime hodd
      (left.isLt.trans_le hm) (right.isLt.trans_le hm)
    have heqNatCast :
        ((shiftedSidonNatLabel p left.val : Nat) : Int) =
          ((shiftedSidonNatLabel p right.val : Nat) : Int) := by
      simpa only [shiftedSidonLabel] using heq
    exact_mod_cast heqNatCast
  rw [← mul_sub, Int.natAbs_mul, Int.natAbs_natCast]
  calc
    M = M * 1 := by omega
    _ <= M * (shiftedSidonLabel p left.val -
        shiftedSidonLabel p right.val).natAbs :=
      Nat.mul_le_mul_left M (Int.natAbs_pos.mpr (sub_ne_zero.mpr hlabelNe))

/-- A positive tagged generator in the shifted-Sidon construction is
strictly positive when the scale dominates the target radius. -/
theorem shiftedSidon_positive_genericValue_pos
    {targets : List Int} {p M T : Nat} (hp : 0 < p)
    (hM : T + 1 <= M)
    (htarget : forall index, (targets.get index).natAbs <= T)
    (index : Fin targets.length) :
    0 <
      (SignedGenerator.positive index).genericValue 2
        (fun labelIndex => (M : Int) * shiftedSidonLabel p labelIndex.val) := by
  have htargetLower : -(T : Int) <= targets.get index := by
    have hlower := Int.le_natAbs (a := -(targets.get index))
    rw [Int.natAbs_neg] at hlower
    have hbound := htarget index
    omega
  have hlabelLowerNat := shiftedSidonNatLabel_lower_bound p index.val
  have hlabelLower :
      (1 : Int) <= shiftedSidonLabel p index.val := by
    simp only [shiftedSidonLabel]
    exact_mod_cast (show 1 <= shiftedSidonNatLabel p index.val by
      have : 1 <= 2 * p ^ 2 := by nlinarith
      omega)
  have hMInt : (T : Int) + 1 <= (M : Int) := by exact_mod_cast hM
  have hscaledLower :
      (T : Int) + 1 <=
        (M : Int) * shiftedSidonLabel p index.val := by
    calc
      (T : Int) + 1 <= (M : Int) := hMInt
      _ = (M : Int) * 1 := by ring
      _ <= (M : Int) * shiftedSidonLabel p index.val :=
        mul_le_mul_of_nonneg_left hlabelLower (by positivity)
  have hpositive :
      0 < targets.get index +
        (M : Int) * shiftedSidonLabel p index.val := by
    calc
      0 < -(T : Int) + ((T : Int) + 1) := by omega
      _ <= targets.get index +
          (M : Int) * shiftedSidonLabel p index.val :=
        add_le_add htargetLower hscaledLower
  simpa [SignedGenerator.genericValue] using hpositive

/-- A negative tagged generator in the shifted-Sidon construction is
strictly negative. -/
theorem shiftedSidon_negative_genericValue_neg
    {targets : List Int} {p M : Nat} (hp : 0 < p) (hM : 1 <= M)
    (index : Fin targets.length) :
    (SignedGenerator.negative index).genericValue 2
        (fun labelIndex => (M : Int) * shiftedSidonLabel p labelIndex.val) < 0 := by
  have hlabelLowerNat := shiftedSidonNatLabel_lower_bound p index.val
  have hlabelPositive : 0 < shiftedSidonLabel p index.val := by
    simp only [shiftedSidonLabel]
    exact_mod_cast (show 0 < shiftedSidonNatLabel p index.val by
      have : 0 < 2 * p ^ 2 := by positivity
      omega)
  have hMPositive : (0 : Int) < (M : Int) := by exact_mod_cast hM
  simp only [SignedGenerator.genericValue]
  exact neg_neg_of_pos (mul_pos hMPositive hlabelPositive)

/-- The tagged-generator value map is injective for scaled shifted-Sidon
labels. -/
theorem shiftedSidon_genericValue_injective
    {targets : List Int} {p M T : Nat}
    (hprime : Nat.Prime p) (hodd : Not (p = 2))
    (hm : targets.length <= p) (hM : 2 * T + 1 <= M)
    (htarget : forall index, (targets.get index).natAbs <= T) :
    Function.Injective
      (SignedGenerator.genericValue (targets := targets) 2
        (fun index => (M : Int) * shiftedSidonLabel p index.val)) := by
  intro left right heq
  cases left with
  | positive leftIndex =>
      cases right with
      | positive rightIndex =>
          congr 1
          by_contra hne
          have hlabelGap :=
            scaledShiftedSidonLabel_gap (M := M) hprime hodd hm hne
          have htargetGap :=
            target_sub_target_natAbs_le htarget leftIndex rightIndex
          simp only [SignedGenerator.genericValue] at heq
          norm_num at heq
          have hlabelEq :
              (M : Int) * shiftedSidonLabel p leftIndex.val -
                  (M : Int) * shiftedSidonLabel p rightIndex.val =
                targets.get rightIndex - targets.get leftIndex := by
            linear_combination heq
          rw [hlabelEq] at hlabelGap
          omega
      | negative rightIndex =>
          have hpositive :=
            shiftedSidon_positive_genericValue_pos (T := T) (M := M)
              hprime.pos (by omega)
              htarget leftIndex
          have hnegative :=
            shiftedSidon_negative_genericValue_neg (M := M)
              hprime.pos (by omega) rightIndex
          exact ((ne_of_gt (hnegative.trans hpositive)) heq).elim
  | negative leftIndex =>
      cases right with
      | positive rightIndex =>
          have hnegative :=
            shiftedSidon_negative_genericValue_neg (M := M)
              hprime.pos (by omega) leftIndex
          have hpositive :=
            shiftedSidon_positive_genericValue_pos (T := T) (M := M)
              hprime.pos (by omega)
              htarget rightIndex
          exact ((ne_of_lt (hnegative.trans hpositive)) heq).elim
      | negative rightIndex =>
          congr 1
          by_contra hne
          have hlabelGap :=
            scaledShiftedSidonLabel_gap (M := M) hprime hodd hm hne
          simp only [SignedGenerator.genericValue] at heq
          have hscaledEq :
              (M : Int) * shiftedSidonLabel p leftIndex.val =
                (M : Int) * shiftedSidonLabel p rightIndex.val := by
            linarith
          rw [hscaledEq, sub_self, Int.natAbs_zero] at hlabelGap
          omega

/-- The generic integer-valued basis is the range of its tagged-generator
value map. -/
theorem genericConstructedBasis_eq_range_genericValue
    {targets : List Int} {h : Nat} {labels : Fin targets.length -> Int} :
    genericConstructedBasis h targets labels =
      Set.range (SignedGenerator.genericValue h labels) := by
  ext x
  rw [mem_genericConstructedBasis_iff_exists_generator]
  rfl

/-- Exact cardinality of an unshifted scaled shifted-Sidon basis. -/
theorem ncard_genericConstructedBasis_shiftedSidon
    {targets : List Int} {p M T : Nat}
    (hprime : Nat.Prime p) (hodd : Not (p = 2))
    (hm : targets.length <= p) (hM : 2 * T + 1 <= M)
    (htarget : forall index, (targets.get index).natAbs <= T) :
    (genericConstructedBasis 2 targets
      (fun index => (M : Int) * shiftedSidonLabel p index.val)).ncard =
        2 * targets.length := by
  rw [genericConstructedBasis_eq_range_genericValue,
    Set.ncard_range_of_injective
      (shiftedSidon_genericValue_injective hprime hodd hm hM htarget),
    natCard_signedGenerator]

/-- Translation preserves the exact cardinality of an integer set. -/
theorem ncard_translateIntegerSet (shift : Int) (basis : Set Int) :
    (translateIntegerSet shift basis).ncard = basis.ncard := by
  have hset :
      translateIntegerSet shift basis = (fun x : Int => x + shift) '' basis := by
    ext x
    constructor
    · intro hx
      exact ⟨x - shift, hx, by ring⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [translateIntegerSet] using hy
  rw [hset, Set.ncard_image_of_injective]
  intro left right heq
  exact add_right_cancel heq

/-- Exact cardinality of the translated shifted-Sidon basis. -/
theorem ncard_centeredShiftedSidonBasis
    {targets : List Int} {shift : Int} {p M T : Nat}
    (hprime : Nat.Prime p) (hodd : Not (p = 2))
    (hm : targets.length <= p) (hM : 2 * T + 1 <= M)
    (htarget :
      forall index : Fin (centerTargetsH2 shift targets).length,
        ((centerTargetsH2 shift targets).get index).natAbs <= T) :
    (centeredShiftedSidonBasis targets shift M p).ncard =
      2 * targets.length := by
  rw [centeredShiftedSidonBasis, ncard_translateIntegerSet]
  have hcenteredLength : (centerTargetsH2 shift targets).length <= p := by
    simpa using hm
  rw [ncard_genericConstructedBasis_shiftedSidon
    hprime hodd hcenteredLength hM htarget, length_centerTargetsH2]

/-- Closed finite-list wrapper: Bertrand's postulate selects the prime, the
translated construction realizes the original target list, and the same
quadratic diameter estimate is retained. -/
theorem exists_centeredShiftedSidonBasis_has_pattern_and_quadratic_diameter
    {targets : List Int} {M T d : Nat} (shift : Int)
    (hlength : 2 <= targets.length)
    (htarget :
      forall index : Fin (centerTargetsH2 shift targets).length,
        ((centerTargetsH2 shift targets).get index).natAbs <= T)
    (hbudget : 4 * T + d <= M) :
    Exists fun p =>
      Nat.Prime p /\ Not (p = 2) /\
        targets.length < p /\ p < 2 * targets.length /\
          And
            (HasIsolatedExceptionalPatternH2 targets
              (centeredShiftedSidonBasis targets shift M p) d)
            (SetDiameterAtMost
              (centeredShiftedSidonBasis targets shift M p)
              (T + 8 * M * (2 * targets.length - 1) ^ 2)) := by
  have hcenteredLength : 2 <= (centerTargetsH2 shift targets).length := by
    simpa using hlength
  obtain ⟨p, hprime, hodd, htargetLengthLt, hpLt, hpattern, hdiameter⟩ :=
    exists_shiftedSidonLabels_have_translated_pattern_and_quadratic_diameter
      shift hcenteredLength htarget hbudget
  refine ⟨p, hprime, hodd, ?_, ?_, ?_, ?_⟩
  · simpa using htargetLengthLt
  · simpa using hpLt
  · exact
      hasIsolatedExceptionalPatternH2_of_centered_translation
        (by simpa [centeredShiftedSidonBasis] using hpattern)
  · simpa [centeredShiftedSidonBasis] using hdiameter

/-- Paper-facing interval wrapper for the translated shifted-Sidon
construction. The maximal nontrivial intervals are exactly the listed ones,
and the chosen basis retains a quadratic diameter estimate. -/
theorem exists_centeredShiftedSidonBasis_has_exactly_intervals_and_quadratic_diameter
    {starts : List Int} {n M T d : Nat} (shift : Int)
    (hsep : SeparatedStarts starts n) (hn : 1 <= n) (hd : 2 <= d)
    (hlength : 2 <= (intervalTargets starts n).length)
    (htarget :
      forall index :
        Fin (centerTargetsH2 shift (intervalTargets starts n)).length,
          ((centerTargetsH2 shift (intervalTargets starts n)).get index).natAbs <= T)
    (hbudget : 4 * T + d <= M) :
    Exists fun p =>
      Nat.Prime p /\ Not (p = 2) /\
        (intervalTargets starts n).length < p /\
        p < 2 * (intervalTargets starts n).length /\
          And
            (HasExactlyNontrivialIntervals
              (hFoldSumset
                (centeredShiftedSidonBasis (intervalTargets starts n) shift M p) 2)
              starts n)
            (And
              (forall lower upper : Int,
                IsMaximalNontrivialInterval
                  (hFoldSumset
                    (centeredShiftedSidonBasis
                      (intervalTargets starts n) shift M p) 2)
                  lower upper <->
                    Exists fun start =>
                      Membership.mem starts start /\
                        lower = start /\ upper = start + n)
              (And
                (SetDiameterAtMost
                  (centeredShiftedSidonBasis (intervalTargets starts n) shift M p)
                  (T + 8 * M *
                    (2 * (intervalTargets starts n).length - 1) ^ 2))
                ((centeredShiftedSidonBasis
                  (intervalTargets starts n) shift M p).ncard =
                    2 * (intervalTargets starts n).length))) := by
  obtain ⟨p, hprime, hodd, htargetLengthLt, hpLt, hpattern, hdiameter⟩ :=
    exists_centeredShiftedSidonBasis_has_pattern_and_quadratic_diameter
      shift hlength htarget hbudget
  refine ⟨p, hprime, hodd, htargetLengthLt, hpLt, ?_, ?_, hdiameter, ?_⟩
  · exact
      hasIsolatedExceptionalPatternH2_hasExactlyNontrivialIntervals
        hsep hd hpattern
  · intro lower upper
    exact isMaximalNontrivialInterval_iff hsep hn
      (hasIsolatedExceptionalPatternH2_hasExactlyNontrivialIntervals
        hsep hd hpattern)
  · exact ncard_centeredShiftedSidonBasis
      hprime hodd htargetLengthLt.le (by omega) htarget

/-- Radius of a target list after centering it for a translated double
sumset construction. -/
def centeredTargetRadiusH2 (targets : List Int) (shift : Int) : Nat :=
  targetRadius (centerTargetsH2 shift targets)

/-- The automatically selected scale for the shifted-Sidon construction. -/
def paperSidonScaleH2 (targets : List Int) (shift : Int) (d : Nat) : Nat :=
  4 * centeredTargetRadiusH2 targets shift + d

/-- Shifted-Sidon basis with the target radius and scale selected
automatically. -/
def explicitCenteredShiftedSidonBasis (targets : List Int) (shift : Int)
    (d p : Nat) : Set Int :=
  centeredShiftedSidonBasis targets shift (paperSidonScaleH2 targets shift d) p

/-- The fully instantiated shifted-Sidon basis has quadratic diameter from
below as well as from above. -/
theorem explicitCenteredShiftedSidonBasis_diameter_lower_bound
    {targets : List Int} {shift : Int} {d p D : Nat}
    (hlength : 1 <= targets.length) (hm : targets.length <= p)
    (hdiameter : SetDiameterAtMost
      (explicitCenteredShiftedSidonBasis targets shift d p) D) :
    2 * paperSidonScaleH2 targets shift d *
      targets.length * (targets.length - 1) <= D := by
  apply centeredShiftedSidonBasis_diameter_lower_bound hlength hm
  simpa [explicitCenteredShiftedSidonBasis] using hdiameter

/-- Closed finite-list theorem: after a translation is supplied, the target
radius and scale are selected automatically. -/
theorem exists_explicitCenteredShiftedSidonBasis_has_pattern_and_quadratic_diameter
    {targets : List Int} {d : Nat} (shift : Int)
    (hd : 1 <= d) (hlength : 2 <= targets.length) :
    Exists fun p =>
      Nat.Prime p /\ Not (p = 2) /\
        targets.length < p /\ p < 2 * targets.length /\
          And
            (HasIsolatedExceptionalPatternH2 targets
              (explicitCenteredShiftedSidonBasis targets shift d p) d)
            (And
              (SetDiameterAtMost
                (explicitCenteredShiftedSidonBasis targets shift d p)
                (centeredTargetRadiusH2 targets shift +
                  8 * paperSidonScaleH2 targets shift d *
                    (2 * targets.length - 1) ^ 2))
              ((explicitCenteredShiftedSidonBasis targets shift d p).ncard =
                2 * targets.length)) := by
  have htarget :
      forall index : Fin (centerTargetsH2 shift targets).length,
        ((centerTargetsH2 shift targets).get index).natAbs <=
          centeredTargetRadiusH2 targets shift := by
    intro index
    exact natAbs_get_le_targetRadius index
  obtain ⟨p, hprime, hodd, htargetLengthLt, hpLt, hpattern, hdiameter⟩ :=
    exists_centeredShiftedSidonBasis_has_pattern_and_quadratic_diameter
      (M := paperSidonScaleH2 targets shift d)
      (T := centeredTargetRadiusH2 targets shift)
      (d := d)
      shift hlength htarget (by
        simp [paperSidonScaleH2])
  refine ⟨p, hprime, hodd, htargetLengthLt, hpLt, ?_, ?_, ?_⟩
  · simpa [explicitCenteredShiftedSidonBasis] using hpattern
  · simpa [explicitCenteredShiftedSidonBasis] using hdiameter
  · simpa [explicitCenteredShiftedSidonBasis] using
      (ncard_centeredShiftedSidonBasis
        hprime hodd htargetLengthLt.le (by
          simp [paperSidonScaleH2]
          omega) htarget)

/-- Closed interval-family theorem: after a translation is supplied, Lean
selects the radius, scale, and Bertrand prime automatically. -/
theorem exists_explicitCenteredShiftedSidonBasis_has_exactly_intervals
    {starts : List Int} {n d : Nat} (shift : Int)
    (hsep : SeparatedStarts starts n) (hn : 1 <= n) (hd : 2 <= d)
    (hlength : 2 <= (intervalTargets starts n).length) :
    Exists fun p =>
      Nat.Prime p /\ Not (p = 2) /\
        (intervalTargets starts n).length < p /\
        p < 2 * (intervalTargets starts n).length /\
          And
            (HasExactlyNontrivialIntervals
              (hFoldSumset
                (explicitCenteredShiftedSidonBasis
                  (intervalTargets starts n) shift d p) 2)
              starts n)
            (And
              (forall lower upper : Int,
                IsMaximalNontrivialInterval
                  (hFoldSumset
                    (explicitCenteredShiftedSidonBasis
                      (intervalTargets starts n) shift d p) 2)
                  lower upper <->
                    Exists fun start =>
                      Membership.mem starts start /\
                        lower = start /\ upper = start + n)
              (And
                (SetDiameterAtMost
                  (explicitCenteredShiftedSidonBasis
                    (intervalTargets starts n) shift d p)
                  (centeredTargetRadiusH2 (intervalTargets starts n) shift +
                    8 * paperSidonScaleH2 (intervalTargets starts n) shift d *
                      (2 * (intervalTargets starts n).length - 1) ^ 2))
                ((explicitCenteredShiftedSidonBasis
                  (intervalTargets starts n) shift d p).ncard =
                    2 * (intervalTargets starts n).length))) := by
  obtain ⟨p, hprime, hodd, htargetLengthLt, hpLt, hpattern, hdiameter, hcardinality⟩ :=
    exists_explicitCenteredShiftedSidonBasis_has_pattern_and_quadratic_diameter
      (targets := intervalTargets starts n) (d := d) shift (by omega) hlength
  refine ⟨p, hprime, hodd, htargetLengthLt, hpLt, ?_, ?_, hdiameter, hcardinality⟩
  · exact
      hasIsolatedExceptionalPatternH2_hasExactlyNontrivialIntervals
        hsep hd hpattern
  · intro lower upper
    exact isMaximalNontrivialInterval_iff hsep hn
      (hasIsolatedExceptionalPatternH2_hasExactlyNontrivialIntervals
        hsep hd hpattern)

/-- Position-independent target radius for the double-sumset construction. -/
def enclosedSidonTargetRadiusBound (lower upper : Int) : Nat :=
  natHalfCeil ((upper - lower).natAbs + 2)

/-- Position-independent quadratic diameter bound for the shifted-Sidon
construction. -/
def enclosedSidonDiameterBound (targets : List Int) (d : Nat)
    (lower upper : Int) : Nat :=
  let T := enclosedSidonTargetRadiusBound lower upper
  T + 8 * (4 * T + d) * (2 * targets.length - 1) ^ 2

/-- A target list inside an enclosing interval admits a double-sumset
centering shift with the expected midpoint radius bound. -/
theorem exists_shift_centeredTargetRadiusH2_le_natHalfCeil
    (targets : List Int) (lower upper : Int)
    (hbounds : forall target, target ∈ targets ->
      lower <= target /\ target <= upper) :
    Exists fun shift : Int =>
      centeredTargetRadiusH2 targets shift <=
        enclosedSidonTargetRadiusBound lower upper := by
  obtain ⟨shift, hshift⟩ :=
    exists_shift_targetRadius_centerTargets_le_natHalfCeil
      targets 2 (by omega) lower upper hbounds
  refine ⟨shift, ?_⟩
  simpa [centeredTargetRadiusH2, enclosedSidonTargetRadiusBound,
    centerTargetsH2, centerTargets] using hshift

/-- Closed finite-list shifted-Sidon theorem with automatic midpoint
centering and a position-independent quadratic diameter estimate. -/
theorem exists_explicitCenteredShiftedSidonBasis_has_pattern_and_diameter_enclosed
    {targets : List Int} {d : Nat}
    (hd : 1 <= d) (hlength : 2 <= targets.length)
    (lower upper : Int)
    (hbounds : forall target, target ∈ targets ->
      lower <= target /\ target <= upper) :
    Exists fun shift : Int =>
      Exists fun p =>
        Nat.Prime p /\ Not (p = 2) /\
          targets.length < p /\ p < 2 * targets.length /\
            And
              (HasIsolatedExceptionalPatternH2 targets
                (explicitCenteredShiftedSidonBasis targets shift d p) d)
              (And
                (SetDiameterAtMost
                  (explicitCenteredShiftedSidonBasis targets shift d p)
                  (enclosedSidonDiameterBound targets d lower upper))
                ((explicitCenteredShiftedSidonBasis
                  targets shift d p).ncard = 2 * targets.length)) := by
  obtain ⟨shift, htargetRadius⟩ :=
    exists_shift_centeredTargetRadiusH2_le_natHalfCeil
      targets lower upper hbounds
  obtain ⟨p, hprime, hodd, htargetLengthLt, hpLt, hpattern,
      hdiameter, hcardinality⟩ :=
    exists_explicitCenteredShiftedSidonBasis_has_pattern_and_quadratic_diameter
      (targets := targets) (d := d) shift hd hlength
  refine ⟨shift, p, hprime, hodd, htargetLengthLt, hpLt,
    hpattern, ?_, hcardinality⟩
  apply setDiameterAtMost_mono hdiameter
  rw [enclosedSidonDiameterBound, enclosedSidonTargetRadiusBound,
    paperSidonScaleH2]
  apply Nat.add_le_add htargetRadius
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left 8
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 4 htargetRadius) d

/-- Closed interval-family shifted-Sidon theorem with automatic midpoint
centering. -/
theorem exists_explicitCenteredShiftedSidonBasis_has_exactly_intervals_enclosed
    {starts : List Int} {n d : Nat}
    (lower upper : Int)
    (hbounds : forall target, target ∈ intervalTargets starts n ->
      lower <= target /\ target <= upper)
    (hsep : SeparatedStarts starts n) (hn : 1 <= n) (hd : 2 <= d)
    (hlength : 2 <= (intervalTargets starts n).length) :
    Exists fun shift : Int =>
      Exists fun p =>
        Nat.Prime p /\ Not (p = 2) /\
          (intervalTargets starts n).length < p /\
          p < 2 * (intervalTargets starts n).length /\
            And
              (HasExactlyNontrivialIntervals
                (hFoldSumset
                  (explicitCenteredShiftedSidonBasis
                    (intervalTargets starts n) shift d p) 2)
                starts n)
              (And
                (forall intervalLower intervalUpper : Int,
                  IsMaximalNontrivialInterval
                    (hFoldSumset
                      (explicitCenteredShiftedSidonBasis
                        (intervalTargets starts n) shift d p) 2)
                    intervalLower intervalUpper <->
                      Exists fun start =>
                        Membership.mem starts start /\
                          intervalLower = start /\ intervalUpper = start + n)
                (And
                  (SetDiameterAtMost
                    (explicitCenteredShiftedSidonBasis
                      (intervalTargets starts n) shift d p)
                    (enclosedSidonDiameterBound
                      (intervalTargets starts n) d lower upper))
                  ((explicitCenteredShiftedSidonBasis
                    (intervalTargets starts n) shift d p).ncard =
                      2 * (intervalTargets starts n).length))) := by
  obtain ⟨shift, p, hprime, hodd, htargetLengthLt, hpLt, hpattern,
      hdiameter, hcardinality⟩ :=
    exists_explicitCenteredShiftedSidonBasis_has_pattern_and_diameter_enclosed
      (targets := intervalTargets starts n) (d := d) (by omega)
      hlength lower upper hbounds
  refine ⟨shift, p, hprime, hodd, htargetLengthLt, hpLt,
    ?_, ?_, hdiameter, hcardinality⟩
  · exact
      hasIsolatedExceptionalPatternH2_hasExactlyNontrivialIntervals
        hsep hd hpattern
  · intro intervalLower intervalUpper
    exact isMaximalNontrivialInterval_iff hsep hn
      (hasIsolatedExceptionalPatternH2_hasExactlyNontrivialIntervals
        hsep hd hpattern)

end IntervalBases
