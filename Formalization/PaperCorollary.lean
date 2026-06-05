import Formalization.SetLevelPackaging

/-!
# Paper-facing interval families

The generic set-level theorem works with an arbitrary list of target points.
This file flattens a separated family of integer intervals into such a list
and packages the resulting statement in interval language.
-/

namespace IntervalBases

/-- Flatten the intervals `[start, start + n]` into the target-point list used
by the explicit construction. -/
def intervalTargets (starts : List Int) (n : Nat) : List Int :=
  starts.flatMap fun start =>
    (List.range (n + 1)).map fun offset : Nat => start + (offset : Int)

/-- Each listed interval contributes exactly `n + 1` target points before
duplicate removal. -/
theorem length_intervalTargets (starts : List Int) (n : Nat) :
    (intervalTargets starts n).length = starts.length * (n + 1) := by
  induction starts with
  | nil =>
      simp [intervalTargets]
  | cons start starts ih =>
      simp [intervalTargets, Nat.add_mul, Nat.add_comm]

/-- Maximum absolute value in a finite target list, with radius zero for the
empty list. -/
def targetRadius : List Int -> Nat
  | [] => 0
  | target :: targets => max target.natAbs (targetRadius targets)

/-- Every list member is bounded by `targetRadius`. -/
theorem natAbs_le_targetRadius_of_mem {targets : List Int} {target : Int}
    (htarget : target ∈ targets) :
    target.natAbs <= targetRadius targets := by
  induction targets with
  | nil =>
      simp at htarget
  | cons head targets ih =>
      simp only [List.mem_cons] at htarget
      simp only [targetRadius]
      rcases htarget with htarget | htarget
      · subst target
        exact le_max_left _ _
      · exact (ih htarget).trans (le_max_right _ _)

/-- Every indexed list member is bounded by `targetRadius`. -/
theorem natAbs_get_le_targetRadius {targets : List Int} (index : Fin targets.length) :
    (targets.get index).natAbs <= targetRadius targets :=
  natAbs_le_targetRadius_of_mem (List.get_mem targets index)

/-- Radius of the flattened target intervals. -/
def intervalTargetRadius (starts : List Int) (n : Nat) : Nat :=
  targetRadius (intervalTargets starts n)

/-- The union of the closed integer intervals `[start, start + n]`. -/
def intervalUnion (starts : List Int) (n : Nat) : Set Int :=
  {x | ∃ start ∈ starts, start <= x ∧ x <= start + n}

/-- The list representation of prescribed targets is ordinary list
membership. -/
theorem mem_prescribedTargets_iff_mem {targets : List Int} {x : Int} :
    x ∈ prescribedTargets targets ↔ x ∈ targets := by
  constructor
  · rintro ⟨index, rfl⟩
    exact List.get_mem targets index
  · intro hx
    obtain ⟨index, hindex⟩ := List.get_of_mem hx
    exact ⟨index, hindex.symm⟩

/-- Flattening intervals gives exactly their union as a set of integers. -/
theorem prescribedTargets_intervalTargets (starts : List Int) (n : Nat) :
    prescribedTargets (intervalTargets starts n) = intervalUnion starts n := by
  ext x
  rw [mem_prescribedTargets_iff_mem]
  constructor
  · intro hx
    rw [intervalTargets, List.mem_flatMap] at hx
    obtain ⟨start, hstart, hx⟩ := hx
    obtain ⟨offset, hoffset, hoffsetValue⟩ := List.mem_map.mp hx
    have hoffsetLt : offset < n + 1 := List.mem_range.mp hoffset
    rw [← hoffsetValue]
    refine ⟨start, hstart, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨start, hstart, hleft, hright⟩
    rw [intervalTargets, List.mem_flatMap]
    refine ⟨start, hstart, ?_⟩
    refine List.mem_map.mpr ⟨(x - start).toNat, ?_, ?_⟩
    · have hnonnegative : 0 <= x - start := by omega
      have hdifferenceLe : x - start <= n := by omega
      have htoNatLe : (x - start).toNat <= n := by
        rw [Int.toNat_le]
        exact hdifferenceLe
      exact List.mem_range.mpr (by omega)
    · have hnonnegative : 0 <= x - start := by omega
      rw [Int.toNat_of_nonneg hnonnegative]
      omega

/-- Pairwise separation condition for a family of interval starts. -/
def SeparatedStarts (starts : List Int) (n : Nat) : Prop :=
  starts.Nodup ∧
    ∀ ⦃left⦄, left ∈ starts -> ∀ ⦃right⦄, right ∈ starts -> left ≠ right ->
      left + (n : Int) + 2 <= right ∨ right + (n : Int) + 2 <= left

/-- Every listed interval start belongs to its own interval union. -/
theorem start_mem_intervalUnion {starts : List Int} {n : Nat} {start : Int}
    (hstart : start ∈ starts) :
    start ∈ intervalUnion starts n := by
  exact ⟨start, hstart, le_rfl, by omega⟩

/-- Every endpoint belongs to its listed interval union. -/
theorem end_mem_intervalUnion {starts : List Int} {n : Nat} {start : Int}
    (hstart : start ∈ starts) :
    start + n ∈ intervalUnion starts n := by
  exact ⟨start, hstart, by omega, le_rfl⟩

/-- Two adjacent points in a separated interval union belong to the same
listed interval. -/
theorem exists_interval_of_mem_intervalUnion_of_succ_mem
    {starts : List Int} {n : Nat} (hsep : SeparatedStarts starts n) {x : Int}
    (hx : x ∈ intervalUnion starts n) (hxSucc : x + 1 ∈ intervalUnion starts n) :
    ∃ start ∈ starts, start <= x ∧ x + 1 <= start + n := by
  obtain ⟨left, hleft, hleftLower, hleftUpper⟩ := hx
  obtain ⟨right, hright, hrightLower, hrightUpper⟩ := hxSucc
  by_cases heq : left = right
  · subst right
    exact ⟨left, hleft, hleftLower, hrightUpper⟩
  · rcases hsep.2 hleft hright heq with hleftRight | hrightLeft
    · omega
    · omega

/-- Paper-facing description of the nontrivial consecutive intervals: every
listed interval is covered, and every adjacent pair in the ambient set lies
inside one listed interval. -/
def HasExactlyNontrivialIntervals (A : Set Int) (starts : List Int) (n : Nat) : Prop :=
  (∀ start ∈ starts, Set.Icc start (start + n) ⊆ A) ∧
    ∀ x ∈ A, x + 1 ∈ A ->
      ∃ start ∈ starts, start <= x ∧ x + 1 <= start + n

/-- A maximal nontrivial closed integer interval in `A`. -/
def IsMaximalNontrivialInterval (A : Set Int) (lower upper : Int) : Prop :=
  lower < upper ∧ Set.Icc lower upper ⊆ A ∧ lower - 1 ∉ A ∧ upper + 1 ∉ A

/-- The integer immediately before a listed interval cannot belong to a set
with exactly the listed nontrivial intervals. -/
theorem left_boundary_not_mem_of_hasExactlyNontrivialIntervals
    {A : Set Int} {starts : List Int} {n : Nat}
    (hsep : SeparatedStarts starts n) (hpattern : HasExactlyNontrivialIntervals A starts n)
    {start : Int} (hstart : start ∈ starts) :
    start - 1 ∉ A := by
  intro hboundary
  have hstartA : start ∈ A :=
    hpattern.1 start hstart ⟨le_rfl, by omega⟩
  obtain ⟨other, hother, hlower, hupper⟩ :=
    hpattern.2 (start - 1) hboundary (by simpa only [sub_add_cancel] using hstartA)
  by_cases heq : other = start
  · subst other
    omega
  · rcases hsep.2 hother hstart heq with hotherStart | hstartOther
    · omega
    · omega

/-- The integer immediately after a listed interval cannot belong to a set
with exactly the listed nontrivial intervals. -/
theorem right_boundary_not_mem_of_hasExactlyNontrivialIntervals
    {A : Set Int} {starts : List Int} {n : Nat}
    (hsep : SeparatedStarts starts n) (hpattern : HasExactlyNontrivialIntervals A starts n)
    {start : Int} (hstart : start ∈ starts) :
    start + n + 1 ∉ A := by
  intro hboundary
  have hendA : start + n ∈ A :=
    hpattern.1 start hstart ⟨by omega, le_rfl⟩
  obtain ⟨other, hother, hlower, hupper⟩ :=
    hpattern.2 (start + n) hendA hboundary
  by_cases heq : other = start
  · subst other
    omega
  · rcases hsep.2 hstart hother (Ne.symm heq) with hstartOther | hotherStart
    · omega
    · omega

/-- Under the adjacent-pair characterization, the maximal nontrivial
intervals are exactly the listed intervals. -/
theorem isMaximalNontrivialInterval_iff
    {A : Set Int} {starts : List Int} {n : Nat}
    (hsep : SeparatedStarts starts n) (hn : 1 <= n)
    (hpattern : HasExactlyNontrivialIntervals A starts n)
    {lower upper : Int} :
    IsMaximalNontrivialInterval A lower upper ↔
      ∃ start ∈ starts, lower = start ∧ upper = start + n := by
  constructor
  · rintro ⟨hlowerUpper, hsubset, hleftBoundary, hrightBoundary⟩
    have hlowerA : lower ∈ A := hsubset ⟨le_rfl, hlowerUpper.le⟩
    have hlowerSuccA : lower + 1 ∈ A := hsubset ⟨by omega, by omega⟩
    obtain ⟨start, hstart, hstartLower, hlowerSuccUpper⟩ :=
      hpattern.2 lower hlowerA hlowerSuccA
    have hlowerEq : lower = start := by
      by_contra hne
      have hleftInside : lower - 1 ∈ Set.Icc start (start + n) := by
        constructor <;> omega
      exact hleftBoundary (hpattern.1 start hstart hleftInside)
    have hupperEq : upper = start + n := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hupperLt | hupperGt
      · have hrightInside : upper + 1 ∈ Set.Icc start (start + n) := by
          constructor <;> omega
        exact hrightBoundary (hpattern.1 start hstart hrightInside)
      · have hlistedBoundaryA : start + n + 1 ∈ A := by
          apply hsubset
          constructor <;> omega
        exact (right_boundary_not_mem_of_hasExactlyNontrivialIntervals
          hsep hpattern hstart) hlistedBoundaryA
    exact ⟨start, hstart, hlowerEq, hupperEq⟩
  · rintro ⟨start, hstart, hlower, hupper⟩
    subst lower
    subst upper
    refine ⟨by omega, hpattern.1 start hstart, ?_, ?_⟩
    · exact left_boundary_not_mem_of_hasExactlyNontrivialIntervals hsep hpattern hstart
    · exact right_boundary_not_mem_of_hasExactlyNontrivialIntervals hsep hpattern hstart

/-- The generic isolated-target theorem gives exactly the requested
nontrivial interval pattern after flattening a separated interval family. -/
theorem constructedBasis_has_exactly_nontrivial_intervals
    {starts : List Int} {n h M B T d : Nat}
    (hsep : SeparatedStarts starts n) (hh : 2 <= h) (hd : 2 <= d)
    (htarget : ∀ index : Fin (intervalTargets starts n).length,
      ((intervalTargets starts n).get index).natAbs <= T)
    (hbase : 2 * ((h - 1) * h) <= B) (hbudget : 2 * (h * T) + d <= M) :
    HasExactlyNontrivialIntervals
      (hFoldSumset (constructedBasis h M B (intervalTargets starts n)) h) starts n := by
  have hpattern :=
    constructedBasis_has_isolated_exceptional_pattern hh htarget hbase hbudget
  constructor
  · intro start hstart x hx
    have hxTarget :
        x ∈ prescribedTargets (intervalTargets starts n) := by
      rw [prescribedTargets_intervalTargets]
      exact ⟨start, hstart, hx.1, hx.2⟩
    have hxList :
        x ∈ intervalTargets starts n :=
      mem_prescribedTargets_iff_mem.mp hxTarget
    obtain ⟨index, hindex⟩ := List.get_of_mem hxList
    rw [← hindex]
    exact hpattern.1 index
  · intro x hx hxSucc
    have hxTarget :
        x ∈ prescribedTargets (intervalTargets starts n) := by
      by_contra hxExceptional
      have hgap := hpattern.2.2 x hx hxExceptional (x + 1) hxSucc (by omega)
      norm_num at hgap
      omega
    have hxSuccTarget :
        x + 1 ∈ prescribedTargets (intervalTargets starts n) := by
      by_contra hxSuccExceptional
      have hgap := hpattern.2.2 (x + 1) hxSucc hxSuccExceptional x hx (by omega)
      norm_num at hgap
      omega
    rw [prescribedTargets_intervalTargets] at hxTarget hxSuccTarget
    exact exists_interval_of_mem_intervalUnion_of_succ_mem hsep hxTarget hxSuccTarget

/-- For the explicit basis, the maximal nontrivial intervals are exactly the
listed intervals. -/
theorem constructedBasis_isMaximalNontrivialInterval_iff
    {starts : List Int} {n h M B T d : Nat}
    (hsep : SeparatedStarts starts n) (hn : 1 <= n) (hh : 2 <= h) (hd : 2 <= d)
    (htarget : ∀ index : Fin (intervalTargets starts n).length,
      ((intervalTargets starts n).get index).natAbs <= T)
    (hbase : 2 * ((h - 1) * h) <= B) (hbudget : 2 * (h * T) + d <= M)
    {lower upper : Int} :
    IsMaximalNontrivialInterval
      (hFoldSumset (constructedBasis h M B (intervalTargets starts n)) h) lower upper ↔
      ∃ start ∈ starts, lower = start ∧ upper = start + n := by
  apply isMaximalNontrivialInterval_iff hsep hn
  exact constructedBasis_has_exactly_nontrivial_intervals
    hsep hh hd htarget hbase hbudget

end IntervalBases
