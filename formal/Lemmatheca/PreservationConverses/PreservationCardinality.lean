import Lemmatheca.PreservationConverses.PreservationUniversal
import Lemmatheca.FirstOrderStructures.FirstOrderSemantics
import Lemmatheca.LogicalCompactness.Compactness

open Lemmatheca.MathematicalLogic

/-! Preservation results in the shared first-order syntax. -/
namespace Lemmatheca.ModelTheory.Preservation
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Theories
universe u v w
variable {L : Language.{u, v}}

/-- The standard sentence asserting that a tuple of length one greater than the bound repeats. -/
def atMostSentence (L : Language.{u, v}) (n : ℕ) : L.Sentence :=
  ((((List.finRange (n + 1) ×ˢ List.finRange (n + 1)).filter
      fun ij : Fin (n + 1) × Fin (n + 1) => ij.1 ≠ ij.2).map
      fun ij => (BoundedFormula.equal (.var (.inr ij.1)) (.var (.inr ij.2)) :
        L.BoundedFormula Empty (n + 1))).foldr (· ⊔ ·) ⊥).alls

private theorem isUniversal_alls {α : Type*} {k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsUniversal) : φ.alls.IsUniversal := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih h.all

private theorem isQF_foldr_sup {α : Type*} {k : ℕ}
    (s : List (L.BoundedFormula α k)) (h : ∀ ψ ∈ s, ψ.IsQF) :
    (s.foldr (· ⊔ ·) ⊥).IsQF := by
  induction s with
  | nil => exact .falsum
  | cons φ s ih => exact (h _ (by simp)).sup (ih (fun ψ hψ => h _ (by simp [hψ])))

theorem atMostSentence_universal (n : ℕ) : (atMostSentence L n).IsUniversal := by
  apply isUniversal_alls
  apply BoundedFormula.IsQF.isUniversal
  apply isQF_foldr_sup
  intro φ hφ
  obtain ⟨ij, _, rfl⟩ := List.mem_map.mp hφ
  exact (BoundedFormula.IsAtomic.equal _ _).isQF

theorem realize_atMostSentence {M : Type w} [L.Structure M] (n : ℕ) :
    M ⊨ atMostSentence L n ↔ Cardinal.mk M ≤ n := by
  classical
  rw [← Cardinal.lt_natCast_add_one_iff, ← not_le, ← Nat.cast_add_one,
    ← Sentence.realize_cardGe L (n + 1)]
  simp [atMostSentence, Sentence.cardGe, Sentence.Realize,
    BoundedFormula.realize_alls, BoundedFormula.realize_exs,
    BoundedFormula.realize_foldr_sup, BoundedFormula.realize_foldr_inf,
    not_forall, not_imp]
  simp [BoundedFormula.Realize, Term.realize]


/-- The displayed singleton-domain sentence has a quantifier-free matrix
and two universal quantifiers in the actual shared syntax. -/
theorem allPairEqual_universal : (FirstOrderSemantics.allPairEqual L).IsUniversal :=
  (BoundedFormula.IsAtomic.equal _ _).isQF.isUniversal.all.all

private theorem isExistential_exs {α : Type*} {k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsExistential) : φ.exs.IsExistential := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih h.ex

private theorem isQF_foldr_inf {α : Type*} {k : ℕ}
    (s : List (L.BoundedFormula α k)) (h : ∀ ψ ∈ s, ψ.IsQF) :
    (s.foldr (· ⊓ ·) ⊤).IsQF := by
  induction s with
  | nil => exact .top
  | cons φ s ih => exact (h _ (by simp)).inf (ih (fun ψ hψ => h _ (by simp [hψ])))

/-- The actual finite-size lower-bound sentence is existential, including
its quantifier-free empty-tuple case. -/
theorem cardGe_existential (n : ℕ) : (Sentence.cardGe L n).IsExistential := by
  apply isExistential_exs
  apply BoundedFormula.IsQF.isExistential
  apply isQF_foldr_inf
  intro φ hφ
  obtain ⟨ij, _, rfl⟩ := List.mem_map.mp hφ
  exact (BoundedFormula.IsAtomic.equal _ _).isQF.not

/-- A single sentence defining infinitude would make its negation an
axiomatization of all finite nonempty structures, contrary to compactness. -/
theorem infinitude_not_sentence (L : Language.{u, v}) :
    ¬ ∃ σ : L.Sentence, ∀ (M : Type (max u v)) (_ : L.Structure M),
      Nonempty M → (M ⊨ σ ↔ Infinite M) := by
  rintro ⟨σ, hσ⟩
  apply Compactness.finitude_not_axiomatizable L
  refine ⟨{σ.not}, ?_⟩
  intro M hM hne
  rw [Theory.model_singleton_iff, Sentence.realize_not, hσ M hM hne]
  exact not_infinite_iff_finite


/-- The exact-size theory cannot have universal axioms when its size exceeds one. -/
theorem exact_size_not_universal (n : ℕ) (hn : 1 < n) :
    ¬ HasUniversalAxiomatization
      ({Sentence.cardGe Language.empty n ⊓
        (Sentence.cardGe Language.empty (n + 1)).not} : Language.empty.Theory) := by
  intro hU
  let T : Language.empty.Theory :=
    {Sentence.cardGe Language.empty n ⊓ (Sentence.cardGe Language.empty (n + 1)).not}
  have hpres : SubstructurePreserved.{0, 0, 0} T :=
    (substructure_preserved_iff_universal T).mpr hU
  have : NeZero n := ⟨by omega⟩
  let : Language.empty.Structure (Fin n) := Language.emptyStructure
  let : Language.empty.Structure (Fin 1) := Language.emptyStructure
  have hN : Fin n ⊨ T := by
    simp only [T, Theory.model_singleton_iff, Sentence.realize_inf,
      Sentence.realize_not, Sentence.realize_cardGe, Cardinal.mk_fin]
    norm_cast
    omega
  let f : Fin 1 ↪ Fin n := ⟨fun _ => ⟨0, by omega⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  have hA : Fin 1 ⊨ T :=
    hpres (Theory.ModelType.of _ (Fin 1)) (Theory.ModelType.of _ (Fin n))
      hN (StrongHomClass.toEmbedding f)
  have hcard : (n : Cardinal.{0}) ≤ 1 := by
    let := hA
    have hs : Fin 1 ⊨ Sentence.cardGe Language.empty n ⊓
        (Sentence.cardGe Language.empty (n + 1)).not :=
      Theory.realize_sentence_of_mem T (by simp [T])
    have hh := ((Sentence.realize_inf (Fin 1)).mp hs).1
    simpa using (Sentence.realize_cardGe Language.empty n).mp hh
  have : n ≤ 1 := by exact_mod_cast hcard
  omega

private theorem finite_witness_model {k : ℕ} {φ : Language.empty.BoundedFormula Empty k}
    (hφ : φ.IsExistential) {M : Type w} [Language.empty.Structure M] [Nonempty M]
    (xs : Fin k → M) (hM : φ.Realize Empty.elim xs) :
    ∃ (N : Type w) (_ : Language.empty.Structure N) (_ : Nonempty N),
      Finite N ∧ ∃ (f : N ↪ M) (ys : Fin k → N),
        f ∘ ys = xs ∧ φ.Realize Empty.elim ys := by
  classical
  induction hφ with
  | @of_isQF k φ hq =>
    let d : M := Classical.choice inferInstance
    let S : Finset M := insert d (Finset.univ.image xs)
    let : Language.empty.Structure ↥S := Language.emptyStructure
    let : Nonempty ↥S := ⟨⟨d, by simp [S]⟩⟩
    let ys : Fin k → S := fun i => ⟨xs i, by simp [S]⟩
    let f : S ↪ M := ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨S, inferInstance, inferInstance, inferInstance, f, ys, rfl, ?_⟩
    have he := hq.realize_embedding f (v := (Empty.elim : Empty → S)) (xs := ys)
    have hf : f ∘ (Empty.elim : Empty → S) = (Empty.elim : Empty → M) := by
      funext i
      exact Empty.elim i
    rw [hf] at he
    exact he.mp hM
  | @ex k φ he ih =>
    obtain ⟨a, ha⟩ := (BoundedFormula.realize_ex).mp hM
    obtain ⟨N, hN, hne, hf, f, ys, hys, ht⟩ := ih (Fin.snoc xs a) ha
    let := hN
    let := hne
    refine ⟨N, hN, hne, hf, f, ys ∘ Fin.castSucc, ?_, ?_⟩
    · funext i
      have hi := congrFun hys i.castSucc
      simpa using hi
    · apply (BoundedFormula.realize_ex).mpr
      refine ⟨ys (Fin.last k), ?_⟩
      change φ.Realize Empty.elim (Fin.snoc (Fin.init ys) (ys (Fin.last k)))
      rw [Fin.snoc_init_self]
      exact ht

/-- A finite witness set in the equality language carries a nonempty finite model. -/
theorem existential_empty_language_finite_model (σ : Language.empty.Sentence)
    (hσ : σ.IsExistential) {M : Type w} [Language.empty.Structure M] [Nonempty M]
    (hM : M ⊨ σ) :
    ∃ (N : Type w) (_ : Language.empty.Structure N) (_ : Nonempty N), Finite N ∧ N ⊨ σ := by
  obtain ⟨N, hN, hne, hf, f, ys, _, ht⟩ :=
    finite_witness_model hσ (default : Fin 0 → M) (by
      simpa only [Sentence.Realize, Formula.Realize,
        Subsingleton.elim (default : Empty → M) (Empty.elim : Empty → M)] using hM)
  let := hN
  let := hne
  refine ⟨N, hN, hne, hf, ?_⟩
  simpa only [Sentence.Realize, Formula.Realize,
    Subsingleton.elim (default : Empty → N) (Empty.elim : Empty → N),
    Subsingleton.elim ys (default : Fin 0 → N)] using ht

/-- In particular, no single existential equality sentence defines infinitude. -/
theorem infinitude_not_existential :
    ¬ ∃ σ : Language.empty.Sentence, σ.IsExistential ∧
      ∀ (M : Type) (_ : Language.empty.Structure M) (_ : Nonempty M),
        (M ⊨ σ ↔ Infinite M) := by
  rintro ⟨σ, hσ, hall⟩
  let : Language.empty.Structure ℕ := Language.emptyStructure
  have hn : ℕ ⊨ σ := (hall ℕ inferInstance inferInstance).mpr inferInstance
  obtain ⟨N, hN, hne, hf, ht⟩ := existential_empty_language_finite_model σ hσ hn
  let := hN
  let := hne
  let := hf
  have hi : Infinite N := (hall N hN hne).mp ht
  exact not_finite N

end Lemmatheca.ModelTheory.Preservation
