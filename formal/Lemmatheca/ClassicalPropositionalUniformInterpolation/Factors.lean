import Lemmatheca.ClassicalPropositionalUniformInterpolation.Projection
import Lemmatheca.PropositionalResolution.PropositionalResolution

namespace Lemmatheca.ProofTheory.ClassicalPropositional.UniformInterpolation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

omit [DecidableEq α] in
private theorem singleton_satisfies (v : Valuation α) (A : PropFormula α) :
    SatisfiesContext v {A} ↔ eval v A = true := by
  simp [SatisfiesContext, Satisfies]

private theorem clause_support (Γ : Resolution.ClauseSet α) :
    Resolution.Supported (Resolution.support Γ) Γ := by
  intro C hC l hl
  exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩

/-- Every source entails its specified existential projection. -/
theorem entails_existsList (L : List α) (A : PropFormula α) :
    Entails {A} (existsList L A) := by
  intro v hv
  exact (existsList_projection L A v).mpr
    ⟨v, (singleton_satisfies v A).mp hv, fun _ _ => rfl⟩

/-- Every universal projection entails its source. -/
theorem forallList_entails (L : List α) (A : PropFormula α) :
    Entails {forallList L A} A := by
  intro v hv
  exact (forallList_projection L A v).mp
    ((singleton_satisfies v _).mp hv) v (fun _ _ => rfl)

/-- All permitted future consequences are retained; fresh atoms are allowed. -/
theorem strongest_consequence (L : List α) (A B : PropFormula α)
    (h : Disjoint (atoms B) L.toFinset) :
    Entails {A} B ↔ Entails {existsList L A} B := by
  constructor
  · intro hAB v hv
    obtain ⟨w, hw, hagree⟩ := (existsList_projection L A v).mp
      ((singleton_satisfies v _).mp hv)
    have hB := hAB w ((singleton_satisfies w A).mpr hw)
    have he : eval w B = eval v B := eval_congr B w v (fun q hq =>
      hagree q (fun hm => Finset.disjoint_left.mp h hq hm))
    change eval v B = true
    change eval w B = true at hB
    exact he ▸ hB
  · intro hEB v hv
    exact hEB v ((singleton_satisfies v _).mpr (entails_existsList L A v hv))

/-- The universal formula is the weakest retained-vocabulary sufficient premise. -/
theorem weakest_premise (L : List α) (A B : PropFormula α)
    (h : Disjoint (atoms B) L.toFinset) :
    Entails {B} A ↔ Entails {B} (forallList L A) := by
  constructor
  · intro hBA v hv
    apply (forallList_projection L A v).mpr
    intro w hagree
    apply hBA w
    apply (singleton_satisfies w B).mpr
    have he : eval w B = eval v B := eval_congr B w v (fun q hq =>
      hagree q (fun hm => Finset.disjoint_left.mp h hq hm))
    exact he.symm ▸ (singleton_satisfies v B).mp hv
  · intro hBU v hv
    exact forallList_entails L A v ((singleton_satisfies v _).mpr (hBU v hv))

/-- The displayed list recursion itself is the uniform interpolant, independent of B. -/
theorem uniform_interpolant (A : PropFormula α) (S : Finset α) (L : List α)
    (hS : S ⊆ atoms A) (hL : L.toFinset = atoms A \ S) : Uniform A S (existsList L A) := by
  refine ⟨entails_existsList L A, ?_, ?_⟩
  · intro q hq
    have ht := Finset.mem_sdiff.mp ((list_support L A).1 hq)
    have hqS : q ∈ S := by
      by_contra hn
      exact ht.2 (by rw [hL]; exact Finset.mem_sdiff.mpr ⟨ht.1, hn⟩)
    rw [← Finset.inter_eq_left.mpr hS]
    exact Finset.mem_inter.mpr ⟨hqS, ht.1⟩
  · intro B hB hAB
    apply (strongest_consequence L A B ?_).mp hAB
    apply Finset.disjoint_left.mpr
    intro q hqB hqL
    obtain ⟨hqA, hqS⟩ := Finset.mem_sdiff.mp (hL ▸ hqL)
    exact hqS (hB (Finset.mem_inter.mpr ⟨hqB, hqA⟩))

/-- Any two formulas satisfying the full uniform property are equivalent. -/
theorem uniform_unique (A I J : PropFormula α) (S : Finset α)
    (hI : Uniform A S I) (hJ : Uniform A S J) : SemEquivalent I J := by
  have hIJ : Entails {I} J := hI.2.2 J
    (fun _ h => hJ.2.1 (Finset.mem_inter.mp h).1) hJ.1
  have hJI : Entails {J} I := hJ.2.2 I
    (fun _ h => hI.2.1 (Finset.mem_inter.mp h).1) hI.1
  intro v
  apply Bool.eq_iff_iff.mpr
  exact ⟨fun h => hIJ v ((singleton_satisfies v I).mpr h),
    fun h => hJI v ((singleton_satisfies v J).mpr h)⟩

/-- The semantic factors give proofs in the exact existing native calculus. -/
theorem native_unconditional (L : List α) (A : PropFormula α) :
    Derives {A} (existsList L A) ∧ Derives {forallList L A} A := by
  exact ⟨derives_complete (entails_existsList L A), derives_complete (forallList_entails L A)⟩

/-- Native classical consequences have exactly the same uniform factor. -/
theorem native_existential (L : List α) (A B : PropFormula α)
    (h : Disjoint (atoms B) L.toFinset) :
    Derives {A} B ↔ Derives {existsList L A} B := by
  rw [derives_iff_entails, derives_iff_entails]
  exact strongest_consequence L A B h

/-- The dual factor also belongs to the exact existing native calculus. -/
theorem native_universal (L : List α) (A B : PropFormula α)
    (h : Disjoint (atoms B) L.toFinset) :
    Derives {B} A ↔ Derives {B} (forallList L A) := by
  rw [derives_iff_entails, derives_iff_entails]
  exact weakest_premise L A B h

/-- Clause elimination and native formula elimination have identical projection semantics. -/
theorem resolution_projection (p : α) (Γ : Resolution.ClauseSet α) (C : PropFormula α)
    (hC : ∀ v, eval v C = true ↔ Resolution.Models v Γ) (v : Valuation α) :
    eval v (existsAtom p C) = true ↔ Resolution.Models v (Resolution.eliminate p Γ) := by
  rw [existsAtom_projection]
  constructor
  · rintro ⟨w, hw, hagree⟩
    have hmodels := Resolution.elimination_models p Γ w ((hC w).mp hw)
    have hs := Resolution.elimination_support (clause_support Γ) p
    intro D hD
    obtain ⟨l, hl, hsat⟩ := hmodels D hD
    refine ⟨l, hl, ?_⟩
    change v l.atom = l.positive
    change w l.atom = l.positive at hsat
    have hp := (Finset.mem_erase.mp (hs D hD l hl)).1
    exact (hagree l.atom (by simpa using hp)).symm.trans hsat
  · intro hv
    obtain ⟨w, hw, hagree⟩ := Resolution.elimination_extend p Γ v hv
    exact ⟨w, (hC w).mpr hw, fun q hq => hagree q (by simpa using hq)⟩

/-- Any native formula reading the eliminated clauses is equivalent to the projection. -/
theorem resolution_formula (p : α) (Γ : Resolution.ClauseSet α) (C D : PropFormula α)
    (hC : ∀ v, eval v C = true ↔ Resolution.Models v Γ)
    (hD : ∀ v, eval v D = true ↔ Resolution.Models v (Resolution.eliminate p Γ)) :
    SemEquivalent (existsAtom p C) D := by
  intro v
  apply Bool.eq_iff_iff.mpr
  exact (resolution_projection p Γ C hC v).trans (hD v).symm

end Lemmatheca.ProofTheory.ClassicalPropositional.UniformInterpolation
