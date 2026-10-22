import Lemmatheca.InductiveTheories.Diagrams
import Lemmatheca.QuantifierElimination.QuantifierEliminationShared

/-! Concrete order examples for ordinary union closure. -/
namespace Lemmatheca.Entry.InductiveTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.ModelTheory.InductiveTheories
open Lemmatheca.ModelTheory.QuantifierElimination.Shared
universe w

/-- Strict linear orders in which every point has a larger point. -/
def noGreatestOrderTheory : binaryRelLanguage.Theory :=
  {strictIrreflexive, strictTransitive, strictTotal, strictNoMaximum}

/-- The same strict order language, with a point at or above every point. -/
def greatestSentence : binaryRelLanguage.Sentence :=
  ((ltAtom (n := 2) 1 0 ⊔ eqAtom 1 0).all).ex

def greatestOrderTheory : binaryRelLanguage.Theory :=
  {strictIrreflexive, strictTransitive, strictTotal, greatestSentence}

/-- A point strictly between the two supplied parameters. -/
def between : binaryRelLanguage.Formula (Fin 2) :=
  ((Relations.boundedFormula₂ BinaryRelationSymbol.rel (.var (.inl 0)) (.var (.inr 0))) ⊓
    (Relations.boundedFormula₂ BinaryRelationSymbol.rel (.var (.inr 0)) (.var (.inl 1)))).ex

private theorem order_axioms_true (M : Type*) [LinearOrder M] :
    letI := binaryRelStructure M (fun a b => a < b)
    (M ⊨ strictIrreflexive) ∧ (M ⊨ strictTransitive) ∧ (M ⊨ strictTotal) := by
  let := binaryRelStructure M (fun a b => a < b)
  refine ⟨?_, ?_, ?_⟩
  · simp only [strictIrreflexive, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_not, ltAtom_realize]
    change ∀ a : M, ¬ a < a
    exact lt_irrefl
  · simp only [strictTransitive, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
      ltAtom_realize]
    change ∀ a b c : M, (a < b ∧ b < c) → a < c
    exact fun _ _ _ h => lt_trans h.1 h.2
  · simp only [strictTotal, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_sup, ltAtom_realize]
    change ∀ a b : M, (a < b ∨ a = b) ∨ b < a
    exact fun a b => (lt_trichotomy a b).elim (fun h => Or.inl (Or.inl h))
      (fun h => h.elim (fun h => Or.inl (Or.inr h)) Or.inr)

private theorem noGreatest_model (M : Type*) [LinearOrder M] [NoMaxOrder M] :
    letI := binaryRelStructure M (fun a b => a < b)
    M ⊨ noGreatestOrderTheory := by
  let := binaryRelStructure M (fun a b => a < b)
  rw [Theory.model_iff]
  intro σ hσ
  obtain ⟨hi, ht, ho⟩ := order_axioms_true M
  rcases hσ with rfl | rfl | rfl | rfl
  · exact hi
  · exact ht
  · exact ho
  · simp only [strictNoMaximum, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_ex, ltAtom_realize]
    change ∀ a : M, ∃ b, a < b
    exact exists_gt

theorem noGreatest_universalExistential : IsUniversalExistentialTheory noGreatestOrderTheory := by
  intro σ hσ
  rcases hσ with rfl | rfl | rfl | rfl
  · exact universal_isUniversalExistential (.all (.of_isQF (BoundedFormula.IsAtomic.rel _ _).isQF.not))
  · exact universal_isUniversalExistential (.all (.all (.all (.of_isQF
      (((BoundedFormula.IsAtomic.rel _ _).isQF.inf (BoundedFormula.IsAtomic.rel _ _).isQF).imp
        (BoundedFormula.IsAtomic.rel _ _).isQF)))))
  · exact universal_isUniversalExistential (.all (.all (.of_isQF
      (((BoundedFormula.IsAtomic.rel _ _).isQF.sup (BoundedFormula.IsAtomic.equal _ _).isQF).sup
        (BoundedFormula.IsAtomic.rel _ _).isQF))))
  · exact .all (.of_existential (.ex (.of_isQF (BoundedFormula.IsAtomic.rel _ _).isQF)))

theorem noGreatest_inductive : IsInductive.{0, 0, w} noGreatestOrderTheory := by
  exact directed_implies_inductive _
    (axiomatization_implies_directed _ ⟨_, noGreatest_universalExistential, rfl⟩)

/-- Both actual standard orders satisfy the same stated universal-existential axiom set. -/
theorem natural_rational_models :
    letI := binaryRelStructure ℕ (fun a b => a < b)
    letI := binaryRelStructure ℚ (fun a b => a < b)
    (ℕ ⊨ noGreatestOrderTheory) ∧ (ℚ ⊨ noGreatestOrderTheory) := by
  let := binaryRelStructure ℕ (fun a b => a < b)
  let := binaryRelStructure ℚ (fun a b => a < b)
  exact ⟨noGreatest_model ℕ, noGreatest_model ℚ⟩

/-- The specified map is the ordinary natural-to-rational inclusion. -/
theorem natural_rational_embedding :
    letI := binaryRelStructure ℕ (fun a b => a < b)
    letI := binaryRelStructure ℚ (fun a b => a < b)
    ∃ f : ℕ ↪[binaryRelLanguage] ℚ, ∀ n, f n = (n : ℚ) := by
  let := binaryRelStructure ℕ (fun a b => a < b)
  let := binaryRelStructure ℚ (fun a b => a < b)
  refine ⟨{ toFun := fun n => (n : ℚ), inj' := ?_, map_fun' := ?_, map_rel' := ?_ }, fun _ => rfl⟩
  · intro a b h
    change (a : ℚ) = (b : ℚ) at h
    exact_mod_cast h
  · intro n f
    exact f.elim
  · intro n R a
    cases R
    change (a 0 : ℚ) < (a 1 : ℚ) ↔ a 0 < a 1
    exact Nat.cast_lt

/-- The actual formula separates the old parameter tuple; the rational witness is one half. -/
theorem between_zero_one :
    letI := binaryRelStructure ℕ (fun a b => a < b)
    letI := binaryRelStructure ℚ (fun a b => a < b)
    ¬ between.Realize (![0, 1] : Fin 2 → ℕ) ∧
      between.Realize (![0, 1] : Fin 2 → ℚ) := by
  let := binaryRelStructure ℕ (fun a b => a < b)
  let := binaryRelStructure ℚ (fun a b => a < b)
  simp only [between, FirstOrder.Language.Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf]
  change (¬ ∃ z : ℕ, 0 < z ∧ z < 1) ∧ ∃ z : ℚ, 0 < z ∧ z < 1
  constructor
  · omega
  · exact ⟨1 / 2, by norm_num, by norm_num⟩

/-- No elementary embedding has the supplied inclusion's values. -/
theorem natural_rational_not_elementary :
    letI := binaryRelStructure ℕ (fun a b => a < b)
    letI := binaryRelStructure ℚ (fun a b => a < b)
    ¬ ∃ e : ℕ ↪ₑ[binaryRelLanguage] ℚ, ∀ n, e n = (n : ℚ) := by
  let := binaryRelStructure ℕ (fun a b => a < b)
  let := binaryRelStructure ℚ (fun a b => a < b)
  rintro ⟨e, he⟩
  obtain ⟨hn, hq⟩ := between_zero_one
  apply hn
  have eeq : e ∘ (![0, 1] : Fin 2 → ℕ) = (![0, 1] : Fin 2 → ℚ) := by
    funext i
    fin_cases i <;> simp [he]
  exact (e.map_formula between (![0, 1] : Fin 2 → ℕ)).mp (eeq ▸ hq)

theorem greatestSentence_realize {M : Type*} [LinearOrder M] :
    letI := binaryRelStructure M (fun a b => a < b)
    (M ⊨ greatestSentence) ↔ ∃ z : M, ∀ x, x < z ∨ x = z := by
  let := binaryRelStructure M (fun a b => a < b)
  simp only [greatestSentence, Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.realize_ex, BoundedFormula.realize_all, BoundedFormula.realize_sup,
    ltAtom_realize]
  rfl

/-- Each finite initial segment is a nonempty model, including the one-point case. -/
theorem finite_greatest_models (n : ℕ) :
    letI := binaryRelStructure (Fin (n + 1)) (fun a b => a < b)
    Fin (n + 1) ⊨ greatestOrderTheory := by
  let := binaryRelStructure (Fin (n + 1)) (fun a b => a < b)
  rw [Theory.model_iff]
  intro σ hσ
  obtain ⟨hi, ht, ho⟩ := order_axioms_true (Fin (n + 1))
  rcases hσ with rfl | rfl | rfl | rfl
  · exact hi
  · exact ht
  · exact ho
  · apply greatestSentence_realize.mpr
    exact ⟨Fin.last n, fun x => lt_or_eq_of_le (Fin.le_last x)⟩

theorem natural_not_greatest_model :
    letI := binaryRelStructure ℕ (fun a b => a < b)
    ¬ ℕ ⊨ greatestOrderTheory := by
  let := binaryRelStructure ℕ (fun a b => a < b)
  intro h
  rw [Theory.model_iff] at h
  have hg : ℕ ⊨ greatestSentence := h greatestSentence (by simp [greatestOrderTheory])
  obtain ⟨z, hz⟩ := greatestSentence_realize.mp hg
  have hbad := hz (z + 1)
  omega

/-- The finite-initial-segment chain has union the natural order, so closure fails. -/
theorem greatest_not_inductive : ¬ IsInductive.{0, 0, 0} greatestOrderTheory := by
  classical
  let := binaryRelStructure ℕ (fun a b => a < b)
  let S : ℕ → binaryRelLanguage.Substructure ℕ := fun n =>
    { carrier := {x | x ≤ n}
      fun_mem := fun f => f.elim }
  have hs : Monotone S := by
    intro i j hij x hx
    exact hx.trans hij
  have hm (n : ℕ) : S n ⊨ greatestOrderTheory := by
    rw [Theory.model_iff]
    intro σ hσ
    obtain ⟨hi, ht, ho⟩ := order_axioms_true (S n)
    rcases hσ with rfl | rfl | rfl | rfl
    · exact hi
    · exact ht
    · exact ho
    · apply greatestSentence_realize.mpr
      exact ⟨⟨n, show n ≤ n from le_rfl⟩, fun x => lt_or_eq_of_le x.property⟩
  have hne (n : ℕ) : Nonempty (S n) := ⟨⟨0, Nat.zero_le n⟩⟩
  intro h
  have hu := h (Theory.ModelType.of ∅ ℕ) (Set.range S) (Set.range_nonempty S)
    hs.isChain_range (by rintro A ⟨n, rfl⟩; exact ⟨hne n, hm n⟩)
  have heq : sSup (Set.range S) = (⊤ : binaryRelLanguage.Substructure ℕ) := by
    apply top_unique
    intro x _
    exact (le_sSup (Set.mem_range_self x) : S x ≤ sSup (Set.range S))
      (show x ∈ S x from Nat.le_refl x)
  let e : (sSup (Set.range S) : binaryRelLanguage.Substructure ℕ) ≃[binaryRelLanguage]
      (⊤ : binaryRelLanguage.Substructure ℕ) :=
    heq ▸ FirstOrder.Language.Equiv.refl binaryRelLanguage
      (sSup (Set.range S) : binaryRelLanguage.Substructure ℕ)
  let : (sSup (Set.range S) : binaryRelLanguage.Substructure ℕ) ⊨ greatestOrderTheory := hu
  let : (⊤ : binaryRelLanguage.Substructure ℕ) ⊨ greatestOrderTheory :=
    StrongHomClass.theory_model e
  have hn : ℕ ⊨ greatestOrderTheory :=
    StrongHomClass.theory_model (Substructure.topEquiv (L := binaryRelLanguage) (M := ℕ))
  exact natural_not_greatest_model hn

theorem greatest_no_universalExistential_axiomatization :
    ¬ HasUniversalExistentialAxiomatization greatestOrderTheory := by
  intro h
  exact greatest_not_inductive (directed_implies_inductive _
    (axiomatization_implies_directed _ h))

end Lemmatheca.Entry.InductiveTheories
