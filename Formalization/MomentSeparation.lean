import Formalization.Representation
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Finite moment labels

This file develops the arithmetic core of the polynomial-diameter refinement.
For a bounded integer coefficient vector, finitely many power moments cannot
all vanish. Encoding those moments in a sufficiently large base gives labels
whose nonzero bounded combinations are separated from zero.
-/

open scoped BigOperators

namespace IntervalBases

/-- The `j`th power moment of an integer coefficient function. -/
def powerMoment {m : Nat} (coefficients : Fin m -> Int) (j : Nat) : Int :=
  Finset.univ.sum fun r => coefficients r * (r.val : Int) ^ j

/-- Sum of the absolute values of an integer coefficient function. -/
def functionL1Norm {m : Nat} (coefficients : Fin m -> Int) : Nat :=
  Finset.univ.sum fun r => (coefficients r).natAbs

/-- Indices carrying a nonzero coefficient. -/
def coefficientSupport {m : Nat} (coefficients : Fin m -> Int) : Finset (Fin m) :=
  Finset.univ.filter fun r => Not (coefficients r = 0)

/-- The finite moment label attached to index `r`. -/
def momentLabel (L Q r : Nat) : Int :=
  Finset.univ.sum fun j : Fin L => (r : Int) ^ j.val * (Q : Int) ^ j.val

/-- Evaluation of a coefficient function against finite moment labels. -/
def momentLabelValue {m : Nat} (L Q : Nat) (coefficients : Fin m -> Int) : Int :=
  Finset.univ.sum fun r => coefficients r * momentLabel L Q r.val

/-- The support of a coefficient function has cardinality at most its l1 norm. -/
theorem card_coefficientSupport_le_functionL1Norm {m : Nat}
    (coefficients : Fin m -> Int) :
    (coefficientSupport coefficients).card <= functionL1Norm coefficients := by
  classical
  rw [functionL1Norm]
  calc
    (coefficientSupport coefficients).card =
        (coefficientSupport coefficients).sum (fun _ => 1) := by simp
    _ <= (coefficientSupport coefficients).sum
        (fun r => (coefficients r).natAbs) := by
      apply Finset.sum_le_sum
      intro r hr
      have hne : Not (coefficients r = 0) := by
        simpa [coefficientSupport] using hr
      exact Int.natAbs_pos.mpr hne
    _ <= Finset.univ.sum (fun r => (coefficients r).natAbs) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- A nonzero coefficient function has nonempty support. -/
theorem coefficientSupport_nonempty_of_ne_zero {m : Nat}
    {coefficients : Fin m -> Int} (hne : Not (coefficients = 0)) :
    (coefficientSupport coefficients).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hne
  funext r
  simp only [Pi.zero_apply]
  by_contra hr
  have : r ∈ coefficientSupport coefficients := by
    simp [coefficientSupport, hr]
  rw [hempty] at this
  simp at this

/-- Vandermonde wrapper: distinct evaluation points and a nonzero coefficient
function force at least one nonzero power moment. -/
theorem exists_power_sum_ne_zero_of_injective {s : Nat}
    {points coefficients : Fin s -> Int} (hpoints : Function.Injective points)
    (hne : Not (coefficients = 0)) :
    Exists fun j : Fin s =>
      Not (Finset.univ.sum (fun r => coefficients r * points r ^ j.val) = 0) := by
  classical
  by_contra hall
  push Not at hall
  apply hne
  exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hpoints hall

/-- Restricting a power moment to the nonzero support does not change it. -/
theorem powerMoment_eq_sum_coefficientSupport {m : Nat}
    (coefficients : Fin m -> Int) (j : Nat) :
    powerMoment coefficients j =
      (coefficientSupport coefficients).sum
        fun r => coefficients r * (r.val : Int) ^ j := by
  rw [powerMoment]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro r _ hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
  simp only [not_not] at hr
  simp [hr]

/-- A nonzero integer coefficient function has a nonzero power moment below
the cardinality of its support. -/
theorem exists_powerMoment_ne_zero_lt_support_card {m : Nat}
    {coefficients : Fin m -> Int} (hne : Not (coefficients = 0)) :
    Exists fun j : Nat =>
      j < (coefficientSupport coefficients).card /\
        Not (powerMoment coefficients j = 0) := by
  classical
  let support := coefficientSupport coefficients
  let points : Fin support.card -> Int :=
    fun i => ((support.equivFin.symm i).val.val : Int)
  let restricted : Fin support.card -> Int :=
    fun i => coefficients (support.equivFin.symm i).val
  have hpoints : Function.Injective points := by
    intro i k hik
    simp only [points, Int.ofNat_inj] at hik
    exact support.equivFin.symm.injective (Subtype.ext (Fin.ext hik))
  have hrestricted : Not (restricted = 0) := by
    intro hzero
    obtain ⟨r, hr⟩ := coefficientSupport_nonempty_of_ne_zero hne
    have hvalue := congrFun hzero (support.equivFin ⟨r, hr⟩)
    simp only [restricted, Equiv.symm_apply_apply, Pi.zero_apply] at hvalue
    have hrne : Not (coefficients r = 0) := by
      simpa [support, coefficientSupport] using hr
    exact hrne hvalue
  obtain ⟨j, hj⟩ := exists_power_sum_ne_zero_of_injective hpoints hrestricted
  refine ⟨j.val, j.isLt, ?_⟩
  rw [powerMoment_eq_sum_coefficientSupport]
  intro hzero
  apply hj
  calc
    (Finset.univ.sum fun i : Fin support.card =>
        restricted i * points i ^ j.val) =
        Finset.univ.sum fun r : support =>
          coefficients r.val * (r.val.val : Int) ^ j.val := by
      simpa [restricted, points] using
        support.equivFin.symm.sum_comp
          (fun r : support => coefficients r.val * (r.val.val : Int) ^ j.val)
    _ = Finset.sum support (fun r =>
          coefficients r * (r.val : Int) ^ j.val) := by
      simpa using (support.sum_attach
        (fun r => coefficients r * (r.val : Int) ^ j.val))
    _ = 0 := by
      simpa [support] using hzero

/-- If the coefficient l1 norm is at most `L`, some power moment below `L`
is nonzero. -/
theorem exists_powerMoment_ne_zero_lt_of_functionL1Norm_le {m L : Nat}
    {coefficients : Fin m -> Int} (hne : Not (coefficients = 0))
    (hnorm : functionL1Norm coefficients <= L) :
    Exists fun j : Nat => j < L /\ Not (powerMoment coefficients j = 0) := by
  obtain ⟨j, hjcard, hj⟩ := exists_powerMoment_ne_zero_lt_support_card hne
  refine ⟨j, ?_, hj⟩
  exact hjcard.trans_le <|
    (card_coefficientSupport_le_functionL1Norm coefficients).trans hnorm

/-- A convenient uniform upper bound for target indices. -/
def labelRadius (m : Nat) : Nat :=
  max 1 (m - 1)

/-- Uniform bound for all power moments below order `L` when the coefficient
l1 norm is at most `L`. -/
def momentBound (m L : Nat) : Nat :=
  L * labelRadius m ^ (L - 1)

/-- The deliberately coarse positional base used by the formal proof. It is
the l1 bound for the full moment vector, so the existing positional
separation theorem applies without a second geometric-tail argument. -/
def momentEncodingBase (m L : Nat) : Nat :=
  L * momentBound m L

theorem fin_val_le_labelRadius {m : Nat} (r : Fin m) :
    r.val <= labelRadius m := by
  simp only [labelRadius]
  omega

/-- Triangle inequality for finite integer sums, stated with `natAbs`. -/
theorem natAbs_finset_sum_le_sum_natAbs {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α -> Int) :
    (s.sum f).natAbs <= s.sum fun a => (f a).natAbs := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- A power moment is bounded by the coefficient l1 norm times the
corresponding power of the index radius. -/
theorem natAbs_powerMoment_le {m : Nat} (coefficients : Fin m -> Int) (j : Nat) :
    (powerMoment coefficients j).natAbs <=
      functionL1Norm coefficients * labelRadius m ^ j := by
  rw [powerMoment, functionL1Norm]
  calc
    (Finset.univ.sum fun r => coefficients r * (r.val : Int) ^ j).natAbs <=
        Finset.univ.sum fun r =>
          (coefficients r * (r.val : Int) ^ j).natAbs :=
      natAbs_finset_sum_le_sum_natAbs _ _
    _ <= Finset.univ.sum fun r =>
          (coefficients r).natAbs * labelRadius m ^ j := by
      apply Finset.sum_le_sum
      intro r _
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      exact Nat.mul_le_mul_left _ <| Nat.pow_le_pow_left (fin_val_le_labelRadius r) j
    _ = (Finset.univ.sum fun r => (coefficients r).natAbs) *
          labelRadius m ^ j := by
      rw [Finset.sum_mul]

/-- The vector of the first `L` power moments. -/
def momentVector {m : Nat} (L : Nat) (coefficients : Fin m -> Int) : List Int :=
  List.ofFn fun j : Fin L => powerMoment coefficients j.val

/-- The full moment vector has l1 norm at most the chosen encoding base. -/
theorem l1Norm_momentVector_le_momentEncodingBase {m L : Nat}
    (coefficients : Fin m -> Int) (hnorm : functionL1Norm coefficients <= L) :
    l1Norm (momentVector L coefficients) <= momentEncodingBase m L := by
  rw [momentVector, l1Norm_ofFn, momentEncodingBase]
  calc
    (Finset.univ.sum fun j : Fin L =>
        (powerMoment coefficients j.val).natAbs) <=
        Finset.univ.sum fun _ : Fin L => momentBound m L := by
      apply Finset.sum_le_sum
      intro j _
      calc
        (powerMoment coefficients j.val).natAbs <=
            functionL1Norm coefficients * labelRadius m ^ j.val :=
          natAbs_powerMoment_le coefficients j.val
        _ <= L * labelRadius m ^ (L - 1) := by
          apply Nat.mul_le_mul hnorm
          apply Nat.pow_le_pow_right
          · simp [labelRadius]
          · omega
        _ = momentBound m L := rfl
    _ = L * momentBound m L := by simp

/-- A nonzero coefficient function with l1 norm at most `L` produces a
nonzero vector among the first `L` power moments. -/
theorem momentVector_ne_replicate_zero_of_functionL1Norm_le {m L : Nat}
    {coefficients : Fin m -> Int} (hne : Not (coefficients = 0))
    (hnorm : functionL1Norm coefficients <= L) :
    Not (momentVector L coefficients =
      List.replicate (momentVector L coefficients).length 0) := by
  obtain ⟨j, hjlt, hj⟩ :=
    exists_powerMoment_ne_zero_lt_of_functionL1Norm_le hne hnorm
  rw [momentVector, List.length_ofFn, ← List.ofFn_const]
  intro hzero
  have hpoint := congrFun (List.ofFn_inj.mp hzero) (⟨j, hjlt⟩ : Fin L)
  exact hj (by simpa using hpoint)

/-- Evaluating a coefficient function against moment labels is exactly the
positional evaluation of its moment vector. -/
theorem momentLabelValue_eq_positionalValue {m L Q : Nat}
    (coefficients : Fin m -> Int) :
    momentLabelValue L Q coefficients =
      positionalValue Q (momentVector L coefficients) := by
  rw [momentLabelValue, momentVector, positionalValue_ofFn]
  calc
    (Finset.univ.sum fun r =>
        coefficients r * momentLabel L Q r.val) =
        Finset.univ.sum fun r =>
          Finset.univ.sum fun j : Fin L =>
            coefficients r * ((r.val : Int) ^ j.val * (Q : Int) ^ j.val) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [momentLabel, Finset.mul_sum]
    _ = Finset.univ.sum fun j : Fin L =>
          Finset.univ.sum fun r =>
            coefficients r * ((r.val : Int) ^ j.val * (Q : Int) ^ j.val) := by
      rw [Finset.sum_comm]
    _ = Finset.univ.sum fun j : Fin L =>
          powerMoment coefficients j.val * (Q ^ j.val : Nat) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [powerMoment, Finset.sum_mul]
      push_cast
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- Every nonzero coefficient combination with l1 norm at most `L` remains
nonzero after moment encoding in a base at least `momentEncodingBase m L`. -/
theorem momentLabelValue_ne_zero_of_functionL1Norm_le {m L Q : Nat}
    {coefficients : Fin m -> Int}
    (hQ : momentEncodingBase m L <= Q)
    (hne : Not (coefficients = 0))
    (hnorm : functionL1Norm coefficients <= L) :
    Not (momentLabelValue L Q coefficients = 0) := by
  rw [momentLabelValue_eq_positionalValue]
  apply positionalValue_ne_zero_of_l1Norm_le_base
  · exact (l1Norm_momentVector_le_momentEncodingBase coefficients hnorm).trans hQ
  · exact momentVector_ne_replicate_zero_of_functionL1Norm_le hne hnorm

/-- Scaled form of moment separation, suitable for the interval-isolation
construction. -/
theorem scale_le_natAbs_mul_momentLabelValue {m L Q M : Nat}
    {coefficients : Fin m -> Int}
    (hQ : momentEncodingBase m L <= Q)
    (hne : Not (coefficients = 0))
    (hnorm : functionL1Norm coefficients <= L) :
    M <= ((M : Int) * momentLabelValue L Q coefficients).natAbs := by
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.le_mul_of_pos_right M <|
    Int.natAbs_pos.mpr <| momentLabelValue_ne_zero_of_functionL1Norm_le hQ hne hnorm

/-- Pointwise difference of two coefficient functions. -/
def functionDifference {m : Nat} (xs ys : Fin m -> Int) : Fin m -> Int :=
  fun r => xs r - ys r

theorem functionL1Norm_functionDifference_le {m : Nat} (xs ys : Fin m -> Int) :
    functionL1Norm (functionDifference xs ys) <=
      functionL1Norm xs + functionL1Norm ys := by
  rw [functionL1Norm, functionL1Norm, functionL1Norm]
  calc
    (Finset.univ.sum fun r => (functionDifference xs ys r).natAbs) <=
        Finset.univ.sum fun r => (xs r).natAbs + (ys r).natAbs := by
      apply Finset.sum_le_sum
      intro r _
      exact Int.natAbs_sub_le _ _
    _ = (Finset.univ.sum fun r => (xs r).natAbs) +
        Finset.univ.sum fun r => (ys r).natAbs := by
      rw [Finset.sum_add_distrib]

theorem functionDifference_ne_zero_of_ne {m : Nat} {xs ys : Fin m -> Int}
    (hne : Not (xs = ys)) :
    Not (functionDifference xs ys = 0) := by
  intro hzero
  apply hne
  funext r
  have hpoint := congrFun hzero r
  simpa [functionDifference] using sub_eq_zero.mp hpoint

theorem momentLabelValue_functionDifference {m L Q : Nat}
    (xs ys : Fin m -> Int) :
    momentLabelValue L Q (functionDifference xs ys) =
      momentLabelValue L Q xs - momentLabelValue L Q ys := by
  rw [momentLabelValue, momentLabelValue, momentLabelValue]
  calc
    (Finset.univ.sum fun r => functionDifference xs ys r * momentLabel L Q r.val) =
        Finset.univ.sum fun r =>
          xs r * momentLabel L Q r.val - ys r * momentLabel L Q r.val := by
      apply Finset.sum_congr rfl
      intro r _
      rw [functionDifference]
      ring
    _ = (Finset.univ.sum fun r => xs r * momentLabel L Q r.val) -
        Finset.univ.sum fun r => ys r * momentLabel L Q r.val := by
      rw [Finset.sum_sub_distrib]

/-- Pairwise moment separation for two bounded coefficient functions. -/
theorem scale_le_natAbs_sub_scaledMomentLabelValue {m L Q M : Nat}
    {xs ys : Fin m -> Int} (hQ : momentEncodingBase m L <= Q)
    (hne : Not (xs = ys))
    (hnorm : functionL1Norm xs + functionL1Norm ys <= L) :
    M <= ((M : Int) * momentLabelValue L Q xs -
      (M : Int) * momentLabelValue L Q ys).natAbs := by
  rw [← mul_sub, ← momentLabelValue_functionDifference]
  apply scale_le_natAbs_mul_momentLabelValue hQ
  · exact functionDifference_ne_zero_of_ne hne
  · exact (functionL1Norm_functionDifference_le xs ys).trans hnorm

/-- Distinct bounded moment-label vectors remain separated after adding
bounded offsets. -/
theorem offset_gap_of_distinct_scaledMomentLabelValues {m L Q M R d : Nat}
    {xs ys : Fin m -> Int} {u v : Int}
    (hQ : momentEncodingBase m L <= Q) (hne : Not (xs = ys))
    (hnorm : functionL1Norm xs + functionL1Norm ys <= L)
    (hoffset : (u - v).natAbs <= R) (hbudget : R + d <= M) :
    d <= ((u + (M : Int) * momentLabelValue L Q xs) -
      (v + (M : Int) * momentLabelValue L Q ys)).natAbs := by
  apply offset_gap
  · exact scale_le_natAbs_sub_scaledMomentLabelValue hQ hne hnorm
  · exact hoffset
  · exact hbudget

end IntervalBases
