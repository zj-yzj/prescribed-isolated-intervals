import Formalization.MomentConstruction

/-!
# Tagged representations for finite moment labels

The count vectors and target offsets are independent of the label family.
This file proves the moment-label analogues of the representation identities
used by the set-level isolation argument.
-/

namespace IntervalBases

/-- Sum of the moment-label parts in a tagged representation. -/
def momentRepresentationLabelValue {targets : List Int} (h M L Q : Nat)
    (generators : List (SignedGenerator targets)) : Int :=
  (generators.map fun generator =>
    generator.momentValue h M L Q - generator.offset).sum

theorem sum_momentGeneratorValue_eq_offset_add_labelValue {targets : List Int}
    (h M L Q : Nat) (generators : List (SignedGenerator targets)) :
    (generators.map (SignedGenerator.momentValue h M L Q)).sum =
      representationOffset generators +
        momentRepresentationLabelValue h M L Q generators := by
  induction generators with
  | nil =>
      rfl
  | cons generator generators ih =>
      simp only [List.map_cons, List.sum_cons, representationOffset,
        momentRepresentationLabelValue, ih]
      ring

/-- The extracted moment-label part is the scaled encoded value of the
usual count coefficient function. -/
theorem momentRepresentationLabelValue_eq_scaledMomentLabelValue
    {targets : List Int} (h M L Q : Nat)
    (generators : List (SignedGenerator targets)) :
    momentRepresentationLabelValue h M L Q generators =
      (M : Int) * momentLabelValue L Q (labelCoefficient h generators) := by
  calc
    momentRepresentationLabelValue h M L Q generators =
        Finset.univ.sum fun index =>
          labelCoefficient h generators index * scaledMomentLabel M L Q index.val := by
      rw [sum_labelCoefficient_mul_eq_sum_generator_weights]
      simp only [momentRepresentationLabelValue]
      apply congrArg List.sum
      apply List.map_congr_left
      intro generator _
      cases generator <;> simp [SignedGenerator.momentValue, SignedGenerator.offset]
    _ = (M : Int) * momentLabelValue L Q (labelCoefficient h generators) := by
      rw [momentLabelValue, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      simp only [scaledMomentLabel]
      ring

/-- Function-level version of the existing count-vector l1 bound. -/
theorem functionL1Norm_labelCoefficient_le {targets : List Int} {h : Nat}
    (hh : 2 <= h) (generators : List (SignedGenerator targets)) :
    functionL1Norm (labelCoefficient h generators) <=
      (h - 1) * generators.length := by
  rw [functionL1Norm, ← l1Norm_ofFn]
  exact l1Norm_labelCoefficients_le hh generators

/-- A zero-label moment representation is one of the prescribed target
points. -/
theorem exists_target_eq_sum_momentGeneratorValue_of_labelCoefficients_eq_zero
    {targets : List Int} {h M L Q : Nat} (hh : 1 <= h)
    (generators : List (SignedGenerator targets)) (hlength : generators.length = h)
    (hzero : labelCoefficients h generators = List.replicate targets.length 0) :
    Exists fun index : Fin targets.length =>
      (generators.map (SignedGenerator.momentValue h M L Q)).sum =
        targets.get index := by
  have htotal :
      (Finset.univ.sum fun index =>
        positiveCount generators index + negativeCount generators index) = h := by
    rw [sum_positiveCount_add_negativeCount, hlength]
  have hmatched :
      ∀ index, negativeCount generators index =
        (h - 1) * positiveCount generators index :=
    negativeCount_eq_mul_positiveCount_of_labelCoefficients_eq_zero hh hzero
  obtain ⟨index, hpositive, _⟩ :=
    exists_matched_index hh (positiveCount generators) (negativeCount generators)
      htotal hmatched
  have hpositiveSum :
      (Finset.univ.sum fun index => positiveCount generators index) = 1 :=
    sum_positive_counts_eq_one hh (positiveCount generators) (negativeCount generators)
      htotal hmatched
  have hcoefficientZero : labelCoefficient h generators = 0 := by
    funext index
    exact labelCoefficients_eq_replicate_zero_iff.mp hzero index
  refine ⟨index, ?_⟩
  rw [sum_momentGeneratorValue_eq_offset_add_labelValue,
    representationOffset_eq_target_of_sum_positiveCount_eq_one generators index
      hpositive hpositiveSum,
    momentRepresentationLabelValue_eq_scaledMomentLabelValue, hcoefficientZero]
  simp [momentLabelValue]

end IntervalBases
