import Formalization.Representation

/-!
# Uniqueness of exceptional count vectors

Two `h`-term tagged representations with the same nonzero label vector have
the same positive and negative counts. If one positive count changed, the
matching negative counts forced by the coefficient equation would already
consume the full `h`-term budget and make that representation a target.
-/

open scoped BigOperators

namespace IntervalBases

/-- If one representation has a strictly larger positive count at an index,
the coefficient equation forces that representation to be fully matched. -/
theorem matched_of_positiveCount_lt {index : Type*} [Fintype index]
    [DecidableEq index] {h : Nat} (hh : 1 <= h)
    (positive negative otherPositive otherNegative : index -> Nat)
    (htotal : (∑ i, (positive i + negative i)) = h)
    (hcoefficient : ∀ i,
      (h - 1) * positive i + otherNegative i =
        (h - 1) * otherPositive i + negative i)
    {chosen : index} (hlt : otherPositive chosen < positive chosen) :
    ∀ i, negative i = (h - 1) * positive i := by
  classical
  have hchosenLe :
      positive chosen + negative chosen <= ∑ i, (positive i + negative i) :=
    Finset.single_le_sum (f := fun i => positive i + negative i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ chosen)
  have hchosenCoefficient := hcoefficient chosen
  have hsplit : 1 + (h - 1) = h := by omega
  have hchosenEq : positive chosen + negative chosen = h := by
    nlinarith
  have hpositiveChosen : positive chosen = 1 := by
    nlinarith
  have hnegativeChosen : negative chosen = h - 1 := by
    omega
  intro i
  by_cases hi : i = chosen
  · subst i
    rw [hpositiveChosen, hnegativeChosen, Nat.mul_one]
  · have hsumSplit :
        (∑ j, (positive j + negative j)) =
          positive chosen + negative chosen +
            ∑ j ∈ (Finset.univ : Finset index) \ {chosen},
              (positive j + negative j) := by
      exact Finset.sum_eq_add_sum_diff_singleton_of_mem
        (f := fun j => positive j + negative j) (Finset.mem_univ chosen)
    have hrest :
        (∑ j ∈ (Finset.univ : Finset index) \ {chosen},
          (positive j + negative j)) = 0 := by
      omega
    have htermLe :
        positive i + negative i <=
          ∑ j ∈ (Finset.univ : Finset index) \ {chosen},
            (positive j + negative j) :=
      Finset.single_le_sum (f := fun j => positive j + negative j)
        (fun _ _ => Nat.zero_le _) (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
            true_and]
          exact hi)
    have hpositiveZero : positive i = 0 := by omega
    have hnegativeZero : negative i = 0 := by omega
    rw [hpositiveZero, hnegativeZero, mul_zero]

/-- Equal coefficient equations and equal `h`-term budgets give equal total
positive counts. -/
theorem sum_positive_eq_of_coefficient_eq {index : Type*} [Fintype index]
    {h : Nat} (hh : 1 <= h)
    (positive negative otherPositive otherNegative : index -> Nat)
    (htotal : (∑ i, (positive i + negative i)) = h)
    (hotherTotal : (∑ i, (otherPositive i + otherNegative i)) = h)
    (hcoefficient : ∀ i,
      (h - 1) * positive i + otherNegative i =
        (h - 1) * otherPositive i + negative i) :
    (∑ i, positive i) = ∑ i, otherPositive i := by
  classical
  have htotal' : (∑ i, positive i) + ∑ i, negative i = h := by
    rw [← Finset.sum_add_distrib]
    exact htotal
  have hotherTotal' :
      (∑ i, otherPositive i) + ∑ i, otherNegative i = h := by
    rw [← Finset.sum_add_distrib]
    exact hotherTotal
  have hcoefficientSum :
      (h - 1) * (∑ i, positive i) + ∑ i, otherNegative i =
        (h - 1) * (∑ i, otherPositive i) + ∑ i, negative i := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hcoefficient i)
  have hsplit : 1 + (h - 1) = h := by omega
  nlinarith

/-- Outside the fully matched case, a coefficient vector uniquely determines
the positive counts. -/
theorem positiveCounts_eq_of_coefficient_eq_of_not_matched
    {index : Type*} [Fintype index] [DecidableEq index]
    {h : Nat} (hh : 1 <= h)
    (positive negative otherPositive otherNegative : index -> Nat)
    (htotal : (∑ i, (positive i + negative i)) = h)
    (hotherTotal : (∑ i, (otherPositive i + otherNegative i)) = h)
    (hcoefficient : ∀ i,
      (h - 1) * positive i + otherNegative i =
        (h - 1) * otherPositive i + negative i)
    (hnotMatched : ¬ ∀ i, negative i = (h - 1) * positive i)
    (hotherNotMatched : ¬ ∀ i, otherNegative i = (h - 1) * otherPositive i) :
    positive = otherPositive := by
  classical
  have hsum :
      (∑ i, positive i) = ∑ i, otherPositive i :=
    sum_positive_eq_of_coefficient_eq hh positive negative otherPositive otherNegative
      htotal hotherTotal hcoefficient
  apply funext
  intro i
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmatched :
        ∀ j, otherNegative j = (h - 1) * otherPositive j :=
      matched_of_positiveCount_lt hh otherPositive otherNegative positive negative
        hotherTotal (fun j => (hcoefficient j).symm) hlt
    exact hotherNotMatched hmatched
  · have hmatched :
        ∀ j, negative j = (h - 1) * positive j :=
      matched_of_positiveCount_lt hh positive negative otherPositive otherNegative
        htotal hcoefficient hgt
    exact hnotMatched hmatched

/-- Outside the fully matched case, a coefficient vector also uniquely
determines the negative counts. -/
theorem negativeCounts_eq_of_coefficient_eq_of_not_matched
    {index : Type*} [Fintype index] [DecidableEq index]
    {h : Nat} (hh : 1 <= h)
    (positive negative otherPositive otherNegative : index -> Nat)
    (htotal : (∑ i, (positive i + negative i)) = h)
    (hotherTotal : (∑ i, (otherPositive i + otherNegative i)) = h)
    (hcoefficient : ∀ i,
      (h - 1) * positive i + otherNegative i =
        (h - 1) * otherPositive i + negative i)
    (hnotMatched : ¬ ∀ i, negative i = (h - 1) * positive i)
    (hotherNotMatched : ¬ ∀ i, otherNegative i = (h - 1) * otherPositive i) :
    negative = otherNegative := by
  have hpositive :
      positive = otherPositive :=
    positiveCounts_eq_of_coefficient_eq_of_not_matched hh positive negative
      otherPositive otherNegative htotal hotherTotal hcoefficient hnotMatched
      hotherNotMatched
  apply funext
  intro i
  have hi := hcoefficient i
  rw [hpositive] at hi
  omega

end IntervalBases
