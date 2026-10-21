import Lemmatheca.HenkinCompleteness.HenkinExtensions
import Mathlib.ModelTheory.Quotients
import Mathlib.ModelTheory.Satisfiability

/-! Henkin construction for countable first-order languages.
Auxiliary names `ℕ` represent added constants using `Formula.equivSentence`.
Terms in `L.Term ℕ` thus represent closed terms of `L[[ℕ]]`. -/
namespace Lemmatheca.MathematicalLogic.HenkinCompleteness
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w
variable {L : Language.{u, v}} {α : Type w} {n : ℕ}
noncomputable section
local instance : DecidableEq (L.Formula α) := Classical.decEq _

variable {S T : Set (L.Formula ℕ)}

/-- Equality classes for a complete consistent theory. -/
def termSetoid (S : Set (L.Formula ℕ)) (hS : Consistent S) (hC : Complete S) :
    Setoid (L.Term ℕ) := ⟨TermEquivalent S, termEquivalent_equivalence hS hC⟩
/-- Congruence supplies the representative-independent quotient interpretations. -/
@[instance_reducible]
def termPrestructure (S : Set (L.Formula ℕ)) (hS : Consistent S) (hC : Complete S) :
    L.Prestructure (termSetoid S hS hC) where
  toStructure := termStructure S
  fun_equiv ts us h := function_congruence hS hC _ ts us fun i => h i
  rel_equiv ts us h := propext (relation_congruence hS hC _ ts us fun i => h i)
/-- The quotient of expanded closed terms. -/
abbrev TermModel (S : Set (L.Formula ℕ)) (hS : Consistent S) (hC : Complete S) :=
  Quotient (termSetoid S hS hC)
instance termModelStructure (S : Set (L.Formula ℕ)) (hS : Consistent S)
    (hC : Complete S) : L.Structure (TermModel S hS hC) :=
  letI := termPrestructure S hS hC
  quotientStructure
/-- An auxiliary constant names its own term class. -/
def nameValue (S : Set (L.Formula ℕ)) (hS : Consistent S) (hC : Complete S)
    (i : ℕ) : TermModel S hS hC := Quotient.mk (termSetoid S hS hC) (.var i)

/-- Supply the new constants with the canonical name interpretation. -/
instance expandedTermModelStructure (S : Set (L.Formula ℕ)) (hS : Consistent S)
    (hC : Complete S) : L[[ℕ]].Structure (TermModel S hS hC) :=
  letI := constantsOn.structure (nameValue S hS hC)
  withConstantsStructure L ℕ

theorem term_model_nonempty (hS : Consistent S) (hC : Complete S) :
    Nonempty (TermModel S hS hC) := ⟨nameValue S hS hC 0⟩

theorem term_value (hS : Consistent S) (hC : Complete S) (t : L.Term ℕ) :
    t.realize (nameValue S hS hC) = (Quotient.mk (termSetoid S hS hC) t : TermModel S hS hC) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    simp only [Term.realize_func, ih]
    let := termPrestructure S hS hC
    exact funMap_quotient_mk' (termSetoid S hS hC) f ts

private def formulaSize : {n : ℕ} → L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp A B => formulaSize A + formulaSize B + 1
  | _, .all A => formulaSize A + 1

private theorem formulaSize_castLE (A : L.BoundedFormula α n) {m : ℕ} (h : n ≤ m) :
    formulaSize (A.castLE h) = formulaSize A := by
  induction A generalizing m with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp _ _ ihA ihB => simp [BoundedFormula.castLE, formulaSize, ihA, ihB]
  | all _ ih => simp [BoundedFormula.castLE, formulaSize, ih]

private theorem formulaSize_map {β : Type*} {g : ℕ → ℕ}
    (ft : ∀ n, L.Term (α ⊕ Fin n) → L.Term (β ⊕ Fin (g n)))
    (h : ∀ n, L.BoundedFormula β (g (n + 1)) → L.BoundedFormula β (g n + 1))
    (hh : ∀ n A, formulaSize (h n A) = formulaSize A)
    (A : L.BoundedFormula α n) :
    formulaSize (A.mapTermRel ft (fun _ => id) h) = formulaSize A := by
  induction A with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp _ _ ihA ihB => simp [BoundedFormula.mapTermRel, formulaSize, ihA, ihB]
  | all _ ih => simp [BoundedFormula.mapTermRel, formulaSize, hh, ih]

private theorem formulaSize_relabel {β : Type*} {m : ℕ}
    (A : L.BoundedFormula α n) (g : α → β ⊕ Fin m) :
    formulaSize (A.relabel g) = formulaSize A := by
  apply formulaSize_map
  intro k B
  exact formulaSize_castLE B _

private theorem formulaSize_subst {β : Type*} (A : L.BoundedFormula α n)
    (σ : α → L.Term β) : formulaSize (A.subst σ) = formulaSize A := by
  apply formulaSize_map
  intros
  rfl

private theorem formulaSize_toFormula (A : L.BoundedFormula α n) :
    formulaSize A.toFormula = formulaSize A := by
  induction A with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp _ _ ihA ihB => simp [BoundedFormula.toFormula, formulaSize, ihA, ihB]
  | all _ ih => simp [BoundedFormula.toFormula, formulaSize, formulaSize_relabel, ih]

private def stripTerm (t : L.Term (ℕ ⊕ Fin 0)) : L.Term ℕ :=
  t.relabel (Sum.elim id Fin.elim0)

private theorem stripTerm_relabel (t : L.Term (ℕ ⊕ Fin 0)) :
    (stripTerm t).relabel Sum.inl = t := by
  rw [stripTerm, Term.relabel_relabel]
  have he : Sum.inl ∘ Sum.elim id Fin.elim0 = (id : ℕ ⊕ Fin 0 → ℕ ⊕ Fin 0) := by
    funext x
    cases x with
    | inl x => rfl
    | inr x => exact Fin.elim0 x
  rw [he, Term.relabel_id]

private theorem snoc_zero {M : Type*} (m : M) :
    Fin.snoc (default : Fin 0 → M) m = (fun _ : Fin 1 => m) := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

private theorem formula_truth_aux (hS : Consistent S) (hC : Complete S) (hH : Henkin S)
    (A : L.Formula ℕ) : A.Realize (nameValue S hS hC) ↔ A ∈ S := by
  classical
  induction hs : formulaSize A using Nat.strong_induction_on generalizing A with
  | h k ih =>
    cases A with
    | falsum =>
      exact iff_of_false id (bot_not_mem hS)
    | equal t r =>
      have he : (stripTerm t).equal (stripTerm r) = BoundedFormula.equal t r := by
        simp only [Term.equal, Term.bdEqual, stripTerm_relabel]
      rw [← he]
      simp only [Term.equal, Term.bdEqual, Formula.Realize, BoundedFormula.Realize,
        Term.realize_relabel, Sum.elim_comp_inl]
      rw [term_value, term_value, Quotient.eq]
      rfl
    | rel R ts =>
      have he : R.formula (fun i => stripTerm (ts i)) = BoundedFormula.rel R ts := by
        simp only [Relations.formula, Relations.boundedFormula, stripTerm_relabel]
      rw [← he]
      simp only [Relations.formula, Relations.boundedFormula, Formula.Realize,
        BoundedFormula.Realize, Term.realize_relabel, Sum.elim_comp_inl]
      simp only [term_value]
      let := termPrestructure S hS hC
      exact relMap_quotient_mk' (termSetoid S hS hC) R _
    | imp B C =>
      have hB := ih (formulaSize B) (by simp [formulaSize] at hs; omega) B rfl
      have hC' := ih (formulaSize C) (by simp [formulaSize] at hs; omega) C rfl
      rw [Formula.Realize, BoundedFormula.realize_imp, ← Formula.Realize,
        ← Formula.Realize, hB, hC', imp_mem_iff hS hC]
      exact imp_iff_not_or
    | all B =>
      rw [Formula.Realize, BoundedFormula.realize_all, all_mem_iff hS hC hH]
      have hinst : ∀ t : L.Term ℕ,
          (instantiate B t).Realize (nameValue S hS hC) ↔ instantiate B t ∈ S := by
        intro t
        apply ih (formulaSize (instantiate B t))
        · simp only [instantiate, formulaSize_subst, formulaSize_toFormula]
          simp [formulaSize] at hs
          omega
        · rfl
      constructor
      · intro hall t
        apply (hinst t).mp
        apply (instantiate_realize B t _).mpr
        simpa only [snoc_zero] using hall (t.realize (nameValue S hS hC))
      · intro hall x
        obtain ⟨t, rfl⟩ := Quotient.exists_rep x
        have ht := (instantiate_realize B t _).mp ((hinst t).mpr (hall t))
        simpa only [term_value, snoc_zero] using ht

theorem truth_lemma (hS : Consistent S) (hC : Complete S) (hH : Henkin S)
    {n : ℕ} (φ : L.BoundedFormula ℕ n) (ts : Fin n → L.Term ℕ) :
    φ.Realize (nameValue S hS hC) (fun i => Quotient.mk (termSetoid S hS hC) (ts i)) ↔ closeSlots φ ts ∈ S := by
  rw [← formula_truth_aux hS hC hH]
  symm
  rw [closeSlots, Formula.Realize, BoundedFormula.realize_subst,
    ← Formula.Realize, BoundedFormula.realize_toFormula]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, term_value]
  rfl

theorem formula_truth (hS : Consistent S) (hC : Complete S) (hH : Henkin S)
    (A : L.Formula ℕ) : A.Realize (nameValue S hS hC) ↔ A ∈ S := formula_truth_aux hS hC hH A

theorem expanded_sentence_truth (hS : Consistent S) (hC : Complete S) (hH : Henkin S)
    (A : L[[ℕ]].Sentence) :
    (TermModel S hS hC) ⊨ A ↔ Formula.equivSentence.symm A ∈ S := by
  exact (Formula.realize_equivSentence_symm (TermModel S hS hC) A
    (nameValue S hS hC)).symm.trans (formula_truth hS hC hH _)

theorem countable_term_model [Countable L.Symbols] (hS : Consistent S) (hC : Complete S) :
    Countable (TermModel S hS hC) := inferInstance

theorem countable_model_existence [Countable L.Symbols] {T : L.Theory} (hT : Consistent T) :
    ∃ M : Type (max u v), ∃ _ : L.Structure M, Nonempty M ∧ Countable M ∧ M ⊨ T := by
  obtain ⟨H, hTH, hH, hHenkin⟩ := consistent_henkin_extension hT
  obtain ⟨S, hHS, hS, hC⟩ := lindenbaum_extension hH
  have hHenkinS : Henkin S := by
    intro φ
    obtain ⟨c, hc⟩ := hHenkin φ
    exact ⟨c, hHS hc⟩
  let : Nonempty (TermModel S hS hC) := term_model_nonempty hS hC
  let : Countable (TermModel S hS hC) := countable_term_model hS hC
  have hmodel : (TermModel S hS hC) ⊨ T := by
    constructor
    intro A hA
    have hp := (formula_truth hS hC hHenkinS (A.relabel Empty.elim)).mpr
      (hHS (hTH ⟨A, hA, rfl⟩))
    simpa only [Formula.realize_relabel, Unique.eq_default, Sentence.Realize] using hp
  let e : TermModel S hS hC ≃ ULift.{v} (TermModel S hS hC) := Equiv.ulift.symm
  let : L.Structure (ULift.{v} (TermModel S hS hC)) := e.inducedStructure
  exact ⟨ULift.{v} (TermModel S hS hC), inferInstance, inferInstance, inferInstance,
    (StrongHomClass.elementarilyEquivalent (L := L) e.inducedStructureEquiv).theory_model_iff.mp hmodel⟩

theorem deductive_completeness [Countable L.Symbols] {T : L.Theory} {A : L.Sentence}
    (h : T ⊨ᵇ A) : Derives T A := by
  classical
  apply Classical.byContradiction
  intro hn
  have hcon : Consistent (insert A.not T) := by
    by_contra hbad
    exact hn (derives_iff_not_consistent_neg.mpr hbad)
  obtain ⟨M, hM, hne, _, hmodel⟩ := countable_model_existence hcon
  let := hM
  let := hne
  let hT : M ⊨ T := hmodel.mono (Set.subset_insert _ _)
  have hA : M ⊨ A := Theory.models_sentence_iff.mp h (Theory.ModelType.of T M)
  exact hmodel.realize_of_mem A.not (Set.mem_insert _ _) hA

theorem consequence_iff_derives [Countable L.Symbols] {T : L.Theory} {A : L.Sentence} :
    T ⊨ᵇ A ↔ Derives T A := by
  constructor
  · exact deductive_completeness
  · intro h
    apply Theory.models_sentence_iff.mpr
    intro M
    exact derives_sound h (default : Empty → M)
      (fun B hB => Theory.realize_sentence_of_mem T hB)

theorem name_terms_injective (L : Language.{u, v}) :
    Function.Injective (Term.var : ℕ → L.Term ℕ) := by
  intro i j h
  exact Term.var.inj h

theorem term_model_subsingleton (hS : Consistent S) (hC : Complete S) (hH : Henkin S)
    (hAll : (Lemmatheca.MathematicalLogic.FirstOrderSemantics.allPairEqual L).relabel
      Empty.elim ∈ S) : Subsingleton (TermModel S hS hC) := by
  apply (Lemmatheca.MathematicalLogic.FirstOrderSemantics.allPairEqual_realize (L := L)).mp
  have hp := (formula_truth hS hC hH _).mpr hAll
  simpa only [Formula.realize_relabel, Unique.eq_default, Sentence.Realize] using hp

theorem consequence_finite_support [Countable L.Symbols] {T : L.Theory} {A : L.Sentence}
    (h : T ⊨ᵇ A) :
    ∃ Γ : Finset L.Sentence, (↑Γ : L.Theory) ⊆ T ∧ Derives (↑Γ) A ∧ (↑Γ : L.Theory) ⊨ᵇ A := by
  obtain ⟨Γ, hΓ, hp⟩ := derives_finite_support (deductive_completeness h)
  exact ⟨Γ, hΓ, hp, consequence_iff_derives.mpr hp⟩

end
end Lemmatheca.MathematicalLogic.HenkinCompleteness
