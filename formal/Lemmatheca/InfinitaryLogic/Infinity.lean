import Lemmatheca.InfinitaryLogic.Syntax
import Lemmatheca.LogicalCompactness.Compactness

/-! Cardinality sentences, their countable conjunction, and the compactness boundary. -/
namespace Lemmatheca.MathematicalLogic.InfinitaryLogic

open FirstOrder FirstOrder.Language

universe u v w
variable {L : Language.{u, v}}

private theorem embedded_sentence_realize (θ : L.Sentence) (M : Type w) [L.Structure M] :
    Sentence.Realize (Formula.ofFirstOrder θ) M ↔ M ⊨ θ := by
  simpa only [Sentence.Realize, FirstOrder.Language.Sentence.Realize,
    FirstOrder.Language.Formula.Realize, Unique.eq_default (Empty.elim : Empty → M),
    Unique.eq_default (Fin.elim0 : Fin 0 → M)] using
    realize_ofFirstOrder θ (Empty.elim : Empty → M) Fin.elim0

/-- One sentence conjoins the actual shared first-order cardinality sentences. -/
def infinitySentence (L : Language.{u, v}) : Sentence L :=
  .conj fun n => Formula.ofFirstOrder (FirstOrder.Language.Sentence.cardGe L n)

theorem infinitySentence_realize (M : Type w) [L.Structure M] :
    Sentence.Realize (infinitySentence L) M ↔ Infinite M := by
  change (∀ n, Sentence.Realize (Formula.ofFirstOrder
    (FirstOrder.Language.Sentence.cardGe L n)) M) ↔ _
  simp_rw [embedded_sentence_realize]
  have h := FirstOrder.Language.model_infiniteTheory_iff (L := L) (M := M)
  simpa only [FirstOrder.Language.Theory.model_iff, FirstOrder.Language.infiniteTheory,
    Set.forall_mem_range] using h

theorem not_infinitySentence_realize (M : Type w) [L.Structure M] :
    Sentence.Realize (infinitySentence L).neg M ↔ Finite M := by
  rw [Sentence.Realize, realize_neg]
  change (¬ Sentence.Realize (infinitySentence L) M) ↔ _
  rw [infinitySentence_realize, not_infinite_iff_finite]

/-- All the individual size requirements together with the negation of their conjunction. -/
def noncompactTheory (L : Language.{u, v}) : Theory L :=
  Set.range (fun n => Formula.ofFirstOrder (FirstOrder.Language.Sentence.cardGe L n)) ∪
    {(infinitySentence L).neg}

theorem noncompactTheory_countable (L : Language.{u, v}) : (noncompactTheory L).Countable := by
  exact (Set.countable_range _).union (Set.countable_singleton _)

theorem noncompact_finite_models (F : Finset (Sentence L))
    (hF : (↑F : Set (Sentence L)) ⊆ noncompactTheory L) :
    ∃ k : ℕ, @Models L (ULift.{max u v} (Fin (k + 1)))
      (Compactness.constantStructure L _) (↑F) := by
  classical
  let index (φ : Sentence L) : ℕ :=
    if h : φ ∈ Set.range (fun n => Formula.ofFirstOrder
        (FirstOrder.Language.Sentence.cardGe L n)) then Classical.choose h else 0
  let k := F.sup index
  let M := ULift.{max u v} (Fin (k + 1))
  let : L.Structure M := Compactness.constantStructure L M
  refine ⟨k, ?_⟩
  intro φ hφ
  rcases hF hφ with hs | hn
  · have hi : Formula.ofFirstOrder
        (FirstOrder.Language.Sentence.cardGe L (index φ)) = φ := by
      simpa only [index, dite_eq_left hs] using Classical.choose_spec hs
    have hb : index φ ≤ k := Finset.le_sup hφ
    rw [← hi]
    rw [embedded_sentence_realize, FirstOrder.Language.Sentence.realize_cardGe]
    have hc : Cardinal.mk M = k + 1 := by simp [M]
    rw [hc]
    exact_mod_cast hb.trans (Nat.le_succ k)
  · obtain rfl := Set.mem_singleton_iff.mp hn
    exact (not_infinitySentence_realize M).mpr inferInstance

theorem noncompact_no_model (M : Type w) [L.Structure M] :
    ¬ Models M (noncompactTheory L) := by
  intro h
  have hinf : Sentence.Realize (infinitySentence L) M := by
    intro n
    exact h _ (Or.inl ⟨n, rfl⟩)
  have hneg := h (infinitySentence L).neg (Or.inr (Set.mem_singleton _))
  exact hneg hinf

theorem noncompactness (L : Language.{u, v}) :
    IsFinitelySatisfiable (noncompactTheory L) ∧ ¬ IsSatisfiable (noncompactTheory L) := by
  constructor
  · intro F hF
    obtain ⟨k, hk⟩ := noncompact_finite_models F hF
    exact ⟨ULift.{max u v} (Fin (k + 1)), Compactness.constantStructure L _,
      inferInstance, hk⟩
  · rintro ⟨M, s, _, hM⟩
    let := s
    exact noncompact_no_model M hM

theorem infinity_not_firstOrder (L : Language.{u, v}) :
    ¬ ∃ θ : L.Sentence, ∀ (M : Type (max u v)) (_ : L.Structure M),
      Nonempty M → (M ⊨ θ ↔ Infinite M) := by
  rintro ⟨θ, hθ⟩
  apply Compactness.finitude_not_axiomatizable L
  refine ⟨{θ.not}, ?_⟩
  intro M s hM
  let := s
  simp only [FirstOrder.Language.Theory.model_iff, Set.mem_singleton_iff, forall_eq,
    FirstOrder.Language.Sentence.realize_not, hθ M s hM, not_infinite_iff_finite]

end Lemmatheca.MathematicalLogic.InfinitaryLogic
