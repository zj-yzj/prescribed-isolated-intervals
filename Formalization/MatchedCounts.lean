import Mathlib

/-!
# Counting matched labels

For the higher-fold construction, a positive term with index `r` carries
label coefficient `h - 1`, while a negative term with the same index carries
coefficient `-1`. This file checks the counting step for a zero-label sum.
-/

open scoped BigOperators

namespace IntervalBases

/-- If an `h`-term sum has zero label coefficient at every index, then it uses
exactly one positive term in total. -/
theorem sum_positive_counts_eq_one {index : Type*} [Fintype index]
    {h : Nat} (hh : 1 <= h) (positive negative : index -> Nat)
    (htotal : (∑ i, (positive i + negative i)) = h)
    (hmatched : ∀ i, negative i = (h - 1) * positive i) :
    (∑ i, positive i) = 1 := by
  classical
  have hnegative :
      (∑ i, negative i) = (h - 1) * (∑ i, positive i) := by
    calc
      (∑ i, negative i) = ∑ i, (h - 1) * positive i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hmatched i
      _ = (h - 1) * (∑ i, positive i) := by
        rw [Finset.mul_sum]
  have htotal' : (∑ i, positive i) + (∑ i, negative i) = h := by
    rw [← Finset.sum_add_distrib]
    exact htotal
  rw [hnegative] at htotal'
  have hsplit : 1 + (h - 1) = h := by omega
  have hfactor : h * (∑ i, positive i) = h := by
    calc
      h * (∑ i, positive i) = (1 + (h - 1)) * (∑ i, positive i) := by
        rw [hsplit]
      _ = (∑ i, positive i) + (h - 1) * (∑ i, positive i) := by
        rw [Nat.add_mul, one_mul]
      _ = h := htotal'
  nlinarith

/-- A zero-label `h`-term sum contains a positive term at some index together
with exactly `h - 1` negative terms at that same index. These terms already
account for the full `h`-term budget. -/
theorem exists_matched_index {index : Type*} [Fintype index]
    {h : Nat} (hh : 1 <= h) (positive negative : index -> Nat)
    (htotal : (∑ i, (positive i + negative i)) = h)
    (hmatched : ∀ i, negative i = (h - 1) * positive i) :
    ∃ i, positive i = 1 ∧ negative i = h - 1 := by
  classical
  have hsum : (∑ i, positive i) = 1 :=
    sum_positive_counts_eq_one hh positive negative htotal hmatched
  have hsumNe : Not ((∑ i, positive i) = 0) := by omega
  obtain ⟨i, hi, hpositiveNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumNe
  have hpositiveOne : positive i = 1 := by
    have hle : positive i <= ∑ j, positive j :=
      Finset.single_le_sum (fun j hj => Nat.zero_le (positive j)) hi
    omega
  refine ⟨i, hpositiveOne, ?_⟩
  rw [hmatched i, hpositiveOne, Nat.mul_one]

end IntervalBases
