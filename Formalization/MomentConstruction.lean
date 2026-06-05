import Formalization.MomentSeparation

/-!
# The polynomial-diameter moment-label construction

This file instantiates the signed-generator construction with finite moment
labels. The tags and count vectors are the same as in the positional-label
construction, so the combinatorial uniqueness layer can be reused.
-/

namespace IntervalBases

/-- The scaled finite moment label used by a tagged generator. -/
def scaledMomentLabel (M L Q r : Nat) : Int :=
  M * momentLabel L Q r

/-- Integer value represented by a signed generator in the moment-label
construction. -/
def SignedGenerator.momentValue {targets : List Int} (h M L Q : Nat) :
    SignedGenerator targets -> Int
  | .positive r => targets.get r + (h - 1) * scaledMomentLabel M L Q r.val
  | .negative r => -scaledMomentLabel M L Q r.val

/-- The moment-label basis. -/
def momentConstructedBasis (h M L Q : Nat) (targets : List Int) : Set Int :=
  {x | Exists fun r : Fin targets.length =>
    x = targets.get r + (h - 1) * scaledMomentLabel M L Q r.val \/
      x = -scaledMomentLabel M L Q r.val}

theorem mem_momentConstructedBasis_iff_exists_generator {h M L Q : Nat}
    {targets : List Int} {x : Int} :
    x ∈ momentConstructedBasis h M L Q targets ↔
      Exists fun generator : SignedGenerator targets =>
        generator.momentValue h M L Q = x := by
  constructor
  · rintro ⟨r, hpositive | hnegative⟩
    · exact ⟨.positive r, hpositive.symm⟩
    · exact ⟨.negative r, hnegative.symm⟩
  · rintro ⟨generator, rfl⟩
    cases generator with
    | positive r =>
        exact ⟨r, Or.inl rfl⟩
    | negative r =>
        exact ⟨r, Or.inr rfl⟩

theorem exists_moment_generator_list_of_terms {h M L Q : Nat}
    {targets : List Int} (terms : List Int)
    (hterms : ∀ term ∈ terms, term ∈ momentConstructedBasis h M L Q targets) :
    Exists fun generators : List (SignedGenerator targets) =>
      generators.map (SignedGenerator.momentValue h M L Q) = terms := by
  induction terms with
  | nil =>
      exact ⟨[], rfl⟩
  | cons term terms ih =>
      obtain ⟨generator, hgenerator⟩ :=
        mem_momentConstructedBasis_iff_exists_generator.mp (hterms term (by simp))
      obtain ⟨generators, hgenerators⟩ := ih (by
        intro tailTerm htailTerm
        exact hterms tailTerm (by simp only [List.mem_cons, htailTerm, or_true]))
      refine ⟨generator :: generators, ?_⟩
      simp only [List.map_cons, hgenerator, hgenerators]

theorem exists_moment_generator_list_of_mem_hFoldSumset {h M L Q : Nat}
    {targets : List Int} {x : Int}
    (hx : x ∈ hFoldSumset (momentConstructedBasis h M L Q targets) h) :
    Exists fun generators : List (SignedGenerator targets) =>
      generators.length = h /\
        (generators.map (SignedGenerator.momentValue h M L Q)).sum = x := by
  obtain ⟨terms, hlength, hterms, hsum⟩ := hx
  obtain ⟨generators, hgenerators⟩ :=
    exists_moment_generator_list_of_terms terms hterms
  refine ⟨generators, ?_, ?_⟩
  · rw [← List.length_map (f := SignedGenerator.momentValue h M L Q), hgenerators]
    exact hlength
  · rw [hgenerators]
    exact hsum

/-- Every prescribed target has its intended matched `h`-term
representation in the moment-label basis. -/
theorem target_mem_hFoldSumset_momentConstructedBasis {h M L Q : Nat}
    (targets : List Int) (hh : 1 <= h) (r : Fin targets.length) :
    targets.get r ∈ hFoldSumset (momentConstructedBasis h M L Q targets) h := by
  let a := scaledMomentLabel M L Q r.val
  refine ⟨(targets.get r + (h - 1) * a) :: List.replicate (h - 1) (-a), ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_replicate]
    omega
  · intro term hterm
    simp only [List.mem_cons, List.mem_replicate] at hterm
    rcases hterm with hterm | hterm
    · subst term
      exact ⟨r, Or.inl rfl⟩
    · rcases hterm with ⟨_, hterm⟩
      subst term
      exact ⟨r, Or.inr rfl⟩
  · simp only [List.sum_cons, List.sum_replicate]
    dsimp only [a]
    have hsplit : h = (h - 1) + 1 := by omega
    rw [hsplit]
    push_cast
    ring

end IntervalBases
