import Formalization.MatchedCounts
import Formalization.OffsetSeparation

/-!
# The explicit basis and its target representations

This file begins the set-level packaging of the paper proof. It defines the
`h`-fold sumset API and the explicit signed basis, then checks that every
prescribed target point belongs to the resulting sumset.
-/

namespace IntervalBases

/-- The set of sums of exactly `h` terms from `A`, with repetition allowed. -/
def hFoldSumset (A : Set Int) (h : Nat) : Set Int :=
  {x | ∃ terms : List Int,
    terms.length = h ∧ (∀ term ∈ terms, term ∈ A) ∧ terms.sum = x}

/-- The positional label `M * B ^ r`. -/
def positionalLabel (M B r : Nat) : Int :=
  M * B ^ r

/-- A tagged generator remembers whether a basis element is the positive or
negative term associated with an index. The integer-valued basis intentionally
forgets this tag, while the proof layer keeps it available for counting. -/
inductive SignedGenerator (targets : List Int) where
  | positive (index : Fin targets.length)
  | negative (index : Fin targets.length)
  deriving DecidableEq

/-- The integer represented by a tagged generator. -/
def SignedGenerator.value {targets : List Int} (h M B : Nat) :
    SignedGenerator targets -> Int
  | .positive r => targets.get r + (h - 1) * positionalLabel M B r.val
  | .negative r => -positionalLabel M B r.val

/-- The explicit signed basis used in the paper. A target `t_r` contributes
the positive term `t_r + (h - 1) * a_r` and the negative term `-a_r`. -/
def constructedBasis (h M B : Nat) (targets : List Int) : Set Int :=
  {x | ∃ r : Fin targets.length,
    x = targets.get r + (h - 1) * positionalLabel M B r.val ∨
      x = -positionalLabel M B r.val}

/-- Membership in the integer-valued basis can be decoded to a tagged
generator. -/
theorem mem_constructedBasis_iff_exists_generator {h M B : Nat}
    {targets : List Int} {x : Int} :
    x ∈ constructedBasis h M B targets ↔
      ∃ generator : SignedGenerator targets, generator.value h M B = x := by
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

/-- A list of terms from the integer-valued basis can be lifted to a list of
tagged generators with exactly the same values. -/
theorem exists_generator_list_of_terms {h M B : Nat} {targets : List Int}
    (terms : List Int) (hterms : ∀ term ∈ terms, term ∈ constructedBasis h M B targets) :
    ∃ generators : List (SignedGenerator targets),
      generators.map (SignedGenerator.value h M B) = terms := by
  induction terms with
  | nil =>
      exact ⟨[], rfl⟩
  | cons term terms ih =>
      obtain ⟨generator, hgenerator⟩ :=
        mem_constructedBasis_iff_exists_generator.mp (hterms term (by simp))
      obtain ⟨generators, hgenerators⟩ := ih (by
        intro tailTerm htailTerm
        exact hterms tailTerm (by simp only [List.mem_cons, htailTerm, or_true]))
      refine ⟨generator :: generators, ?_⟩
      simp only [List.map_cons, hgenerator, hgenerators]

/-- Every element of the constructed `h`-fold sumset has an exact tagged
representation of length `h`. -/
theorem exists_generator_list_of_mem_hFoldSumset_constructedBasis {h M B : Nat}
    {targets : List Int} {x : Int}
    (hx : x ∈ hFoldSumset (constructedBasis h M B targets) h) :
    ∃ generators : List (SignedGenerator targets),
      generators.length = h ∧
      (generators.map (SignedGenerator.value h M B)).sum = x := by
  obtain ⟨terms, hlength, hterms, hsum⟩ := hx
  obtain ⟨generators, hgenerators⟩ :=
    exists_generator_list_of_terms terms hterms
  refine ⟨generators, ?_, ?_⟩
  · rw [← List.length_map (f := SignedGenerator.value h M B), hgenerators]
    exact hlength
  · rw [hgenerators]
    exact hsum

/-- Every prescribed target has its intended matched representation in the
`h`-fold sumset of the constructed basis. -/
theorem target_mem_hFoldSumset_constructedBasis {h M B : Nat}
    (targets : List Int) (hh : 1 <= h) (r : Fin targets.length) :
    targets.get r ∈ hFoldSumset (constructedBasis h M B targets) h := by
  let a := positionalLabel M B r.val
  refine ⟨(targets.get r + (h - 1) * a) :: List.replicate (h - 1) (-a), ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_replicate]
    omega
  · intro term hterm
    simp only [List.mem_cons, List.mem_replicate] at hterm
    rcases hterm with hterm | hterm
    · subst term
      exact ⟨r, Or.inl rfl⟩
    · rcases hterm with ⟨hrepetitions, hterm⟩
      subst term
      exact ⟨r, Or.inr rfl⟩
  · simp only [List.sum_cons, List.sum_replicate]
    dsimp only [a]
    have hsplit : h = (h - 1) + 1 := by omega
    rw [hsplit]
    push_cast
    ring

end IntervalBases
