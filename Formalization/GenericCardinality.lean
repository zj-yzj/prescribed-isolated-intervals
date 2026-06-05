import Formalization.GenericLabels
import Formalization.Cardinality

/-!
# Exact cardinality for abstract separated labels

The separated-label principle already contains enough information to show
that the two tagged generators attached to each target have distinct integer
values. This file packages that argument independently of the concrete label
formula.
-/

namespace IntervalBases

/-- A one-term tagged representation remembers its tag and index when
`h >= 2`. -/
theorem labelCoefficient_singleton_injective {targets : List Int} {h : Nat}
    (hh : 2 <= h) :
    Function.Injective
      (fun generator : SignedGenerator targets => labelCoefficient h [generator]) := by
  intro left right heq
  cases left with
  | positive leftIndex =>
      cases right with
      | positive rightIndex =>
          congr 1
          by_contra hne
          have hpoint := congrFun heq leftIndex
          simp [labelCoefficient, positiveCount, negativeCount, Ne.symm hne] at hpoint
          omega
      | negative rightIndex =>
          have hpoint := congrFun heq leftIndex
          by_cases hindex : leftIndex = rightIndex
          · subst rightIndex
            simp [labelCoefficient, positiveCount, negativeCount] at hpoint
            omega
          · simp [labelCoefficient, positiveCount, negativeCount, Ne.symm hindex] at hpoint
            omega
  | negative leftIndex =>
      cases right with
      | positive rightIndex =>
          have hpoint := congrFun heq leftIndex
          by_cases hindex : leftIndex = rightIndex
          · subst rightIndex
            simp [labelCoefficient, positiveCount, negativeCount] at hpoint
            omega
          · simp [labelCoefficient, positiveCount, negativeCount, Ne.symm hindex] at hpoint
      | negative rightIndex =>
          congr 1
          by_contra hne
          have hpoint := congrFun heq leftIndex
          simp [labelCoefficient, positiveCount, negativeCount, Ne.symm hne] at hpoint

/-- Distinct tagged generators have distinct values for any sufficiently
separated abstract label family. -/
theorem genericValue_injective
    {targets : List Int} {h M T : Nat}
    {labels : Fin targets.length -> Int}
    (hh : 2 <= h)
    (htarget : forall index, (targets.get index).natAbs <= T)
    (hseparate :
      BoundedLabelSeparation labels (2 * ((h - 1) * h)) M)
    (hbudget : 2 * T + 1 <= M) :
    Function.Injective (SignedGenerator.genericValue h labels) := by
  intro left right heq
  by_contra hne
  have hcoefficients :
      Not (labelCoefficient h [left] = labelCoefficient h [right]) := by
    intro hcoefficientEq
    apply hne
    exact labelCoefficient_singleton_injective hh hcoefficientEq
  have hnorm :
      functionL1Norm (labelCoefficient h [left]) +
          functionL1Norm (labelCoefficient h [right]) <=
        2 * ((h - 1) * h) := by
    have hleft := functionL1Norm_labelCoefficient_le_generic hh [left]
    have hright := functionL1Norm_labelCoefficient_le_generic hh [right]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one] at hleft hright
    have hfactor : h - 1 <= (h - 1) * h :=
      Nat.le_mul_of_pos_right (h - 1) (by omega)
    calc
      functionL1Norm (labelCoefficient h [left]) +
          functionL1Norm (labelCoefficient h [right]) <=
        (h - 1) + (h - 1) :=
          Nat.add_le_add hleft hright
      _ <= (h - 1) * h + (h - 1) * h :=
        Nat.add_le_add hfactor hfactor
      _ = 2 * ((h - 1) * h) := by omega
  have hoffset :
      (representationOffset [left] - representationOffset [right]).natAbs <=
        2 * T := by
    calc
      (representationOffset [left] - representationOffset [right]).natAbs <=
          (representationOffset [left]).natAbs +
            (representationOffset [right]).natAbs :=
        Int.natAbs_sub_le _ _
      _ <= [left].length * T + [right].length * T :=
        Nat.add_le_add
          (natAbs_representationOffset_le [left] htarget)
          (natAbs_representationOffset_le [right] htarget)
      _ = 2 * T := by simp; omega
  have hgap :
      1 <=
        ((representationOffset [left] +
            linearLabelValue labels (labelCoefficient h [left])) -
          (representationOffset [right] +
            linearLabelValue labels (labelCoefficient h [right]))).natAbs :=
    offset_gap (hseparate hcoefficients hnorm) hoffset hbudget
  have hleftValue :
      representationOffset [left] +
          linearLabelValue labels (labelCoefficient h [left]) =
        left.genericValue h labels := by
    rw [← genericRepresentationLabelValue_eq_linearLabelValue]
    symm
    simpa using sum_genericGeneratorValue_eq_offset_add_labelValue h labels [left]
  have hrightValue :
      representationOffset [right] +
          linearLabelValue labels (labelCoefficient h [right]) =
        right.genericValue h labels := by
    rw [← genericRepresentationLabelValue_eq_linearLabelValue]
    symm
    simpa using sum_genericGeneratorValue_eq_offset_add_labelValue h labels [right]
  rw [hleftValue, hrightValue, heq, sub_self, Int.natAbs_zero] at hgap
  omega

/-- The generic integer-valued basis is the range of its tagged-generator
value map. -/
theorem genericConstructedBasis_eq_range_genericValue'
    {targets : List Int} {h : Nat} {labels : Fin targets.length -> Int} :
    genericConstructedBasis h targets labels =
      Set.range (SignedGenerator.genericValue h labels) := by
  ext x
  rw [mem_genericConstructedBasis_iff_exists_generator]
  rfl

/-- Exact cardinality of a generic basis under the separated-label
hypothesis. -/
theorem ncard_genericConstructedBasis
    {targets : List Int} {h M T : Nat}
    {labels : Fin targets.length -> Int}
    (hh : 2 <= h)
    (htarget : forall index, (targets.get index).natAbs <= T)
    (hseparate :
      BoundedLabelSeparation labels (2 * ((h - 1) * h)) M)
    (hbudget : 2 * T + 1 <= M) :
    (genericConstructedBasis h targets labels).ncard =
      2 * targets.length := by
  rw [genericConstructedBasis_eq_range_genericValue',
    Set.ncard_range_of_injective
      (genericValue_injective hh htarget hseparate hbudget),
    natCard_signedGenerator]

end IntervalBases
