import Formalization.Construction

/-!
# Small audit examples

This file records the direct machine-checkable part of the counterexample to
the strict inequality proposed in Problem 7(2) of Nathanson's problem list.
-/

namespace IntervalBases

/-- The signed three-element basis used in the Problem 7(2) audit note. -/
def problemSevenCounterexample : Set Int :=
  {-1, 1, 2}

/-- A two-term sum of basis elements belongs to the double sumset. -/
theorem add_mem_hFoldSumset_two {basis : Set Int} {left right : Int}
    (hleft : Membership.mem basis left) (hright : Membership.mem basis right) :
    Membership.mem (hFoldSumset basis 2) (left + right) := by
  refine ⟨[left, right], by simp, ?_, by simp⟩
  intro term hterm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
  rcases hterm with hterm | hterm
  · simpa only [hterm] using hleft
  · simpa only [hterm] using hright

/-- The audit basis really has three elements. -/
theorem ncard_problemSevenCounterexample :
    problemSevenCounterexample.ncard = 3 := by
  norm_num [problemSevenCounterexample]

/-- The audit basis contains a negative element. -/
theorem neg_one_mem_problemSevenCounterexample :
    Membership.mem problemSevenCounterexample (-1) := by
  simp [problemSevenCounterexample]

/-- The full initial interval `[0, 4]` lies in the double sumset of
`{-1, 1, 2}`. -/
theorem Icc_zero_four_subset_two_problemSevenCounterexample :
    Set.Icc (0 : Int) 4 ⊆ hFoldSumset problemSevenCounterexample 2 := by
  intro x hx
  have hneg : Membership.mem problemSevenCounterexample (-1) := by
    simp [problemSevenCounterexample]
  have hone : Membership.mem problemSevenCounterexample 1 := by
    simp [problemSevenCounterexample]
  have htwo : Membership.mem problemSevenCounterexample 2 := by
    simp [problemSevenCounterexample]
  have hxLower : 0 <= x := hx.1
  have hxUpper : x <= 4 := hx.2
  rcases (show x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 by omega) with
    rfl | rfl | rfl | rfl | rfl
  · simpa using add_mem_hFoldSumset_two hneg hone
  · simpa using add_mem_hFoldSumset_two hneg htwo
  · simpa using add_mem_hFoldSumset_two hone hone
  · simpa using add_mem_hFoldSumset_two hone htwo
  · simpa using add_mem_hFoldSumset_two htwo htwo

end IntervalBases
