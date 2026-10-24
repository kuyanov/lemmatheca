import Lemmatheca.SaturatedExtensions.Chains

/-! Boundary cases for simultaneous requests and saturated extensions. -/
namespace Lemmatheca.Entry.SaturatedExtensions

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory
open Types CountableSaturatedModels

universe u v w w'

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]

/-- Over a singleton structure there is exactly one one-type over each parameter set. -/
theorem singleton_types_unique [Subsingleton M] (A : Set M) :
    Subsingleton ((L[[A]].completeTheory M).CompleteType (Fin 1)) := by
  constructor
  intro p q
  obtain ⟨a, ha⟩ := finite_realization (formulas p)
    ((partial_iff_finitelyRealized_completeTheory _).mp (partial_formulas p))
  obtain ⟨b, hb⟩ := finite_realization (formulas q)
    ((partial_iff_finitelyRealized_completeTheory _).mp (partial_formulas q))
  rw [(realizes_complete_iff p a).mp ha, (realizes_complete_iff q b).mp hb]
  congr 1
  exact Subsingleton.elim a b

/-- Empty and singleton parameter bases nevertheless give two distinct request labels. -/
theorem singleton_distinct_requests [Subsingleton M] (m : M) :
    ∃ r s : Request L M, r.1 = ∅ ∧ s.1 = {m} ∧ r ≠ s := by
  classical
  let r : Request L M := ⟨∅, (L[[(↑(∅ : Finset M) : Set M)]].completeTheory M).typeOf
    (fun _ : Fin 1 => m)⟩
  let s : Request L M := ⟨{m}, (L[[(↑({m} : Finset M) : Set M)]].completeTheory M).typeOf
    (fun _ : Fin 1 => m)⟩
  refine ⟨r, s, rfl, rfl, fun h => ?_⟩
  have he : (∅ : Finset M) = {m} := congrArg Sigma.fst h
  have hm : m ∈ (∅ : Finset M) := he.symm ▸ Finset.mem_singleton_self m
  exact Finset.notMem_empty m hm

/-- The same sole old point answers every request, without distinct witness values. -/
theorem singleton_answers_all [Subsingleton M] (m : M) (r : Request L M) :
    RealizesThrough (ElementaryEmbedding.refl L M) r.2 (fun _ => m) := by
  obtain ⟨b, hb⟩ := finite_realization (formulas r.2)
    ((partial_iff_finitelyRealized_completeTheory _).mp (partial_formulas r.2))
  have he : b = (fun _ : Fin 1 => m) := Subsingleton.elim _ _
  rw [he] at hb
  intro φ hφ
  convert (parameter_type_transport (ElementaryEmbedding.refl L M)
    (↑r.1 : Set M) (fun _ : Fin 1 => m) φ).mp (hb φ hφ) using 1
  rfl

omit [Nonempty M] in
/-- An elementary extension of a singleton cannot supply distinct request values. -/
theorem singleton_extension_values_equal [Nonempty M] [Subsingleton M]
    {N : Type w'} [L.Structure N] (f : M ↪ₑ[L] N) (b c : N) : b = c := by
  have hf := Diagrams.finite_elementary_embedding_surjective f
  obtain ⟨a, rfl⟩ := hf b
  obtain ⟨a', rfl⟩ := hf c
  exact congrArg f (Subsingleton.elim _ _)

/-- The conditions asking for a point unequal to every named original point. -/
def oldPointExclusions (L : Language.{u, v}) (M : Type w) :
    Set (L[[M]].Formula (Fin 1)) :=
  Set.range fun m : M =>
    ((Term.var (0 : Fin 1)).equal (L.con m).term).not

/-- For finite M, those exclusions are not a consistent type over its named complete theory. -/
theorem finite_exclusions_not_partial [Finite M] :
    ¬IsPartial (L[[M]].completeTheory M) (oldPointExclusions L M) := by
  intro hp
  obtain ⟨b, hb⟩ := finite_realization (oldPointExclusions L M)
    ((partial_iff_finitelyRealized_completeTheory _).mp hp)
  have hn := hb _ (Set.mem_range_self (b 0))
  apply Formula.realize_not.mp hn
  exact Formula.realize_equal.mpr rfl

/-- Countably many stagewise parameters need not have a common stage. -/
theorem countable_parameters_not_stage_bounded :
    ∃ (A : Set ℕ) (S : ℕ → Set ℕ),
      A.Countable ∧ Monotone S ∧ A ⊆ ⋃ n, S n ∧ ¬∃ n, A ⊆ S n := by
  refine ⟨Set.univ, fun n => Set.Iic n, Set.to_countable _, ?_, ?_, ?_⟩
  · intro i j hij x hx
    exact hx.trans hij
  · intro x _
    exact Set.mem_iUnion.mpr ⟨x, le_refl x⟩
  · rintro ⟨n, hn⟩
    exact Nat.not_succ_le_self n (hn (Set.mem_univ (n+1)))

end Lemmatheca.Entry.SaturatedExtensions
