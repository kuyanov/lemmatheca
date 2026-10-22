import Lemmatheca.CountableModels.Spectrum
import Lemmatheca.CountableSaturatedModels.Constructions
import Mathlib.Tactic.FinCases

/-! A third countable model for small noncategorical theories. -/
namespace Lemmatheca.ModelTheory.CountableModels

open FirstOrder FirstOrder.Language
open Types IsolatedTypes CountableCategoricity CountableSaturatedModels

variable {L : Language.{0, 0}} {T : L.Theory}

private theorem iff_in_complete_model (hT : T.IsComplete) (S : Type)
    [L.Structure S] [Nonempty S] [S ⊨ T] {n : ℕ} (φ ψ : L.Formula (Fin n)) :
    T.Iff φ ψ ↔ ∀ a : Fin n → S, φ.Realize a ↔ ψ.Realize a := by
  constructor
  · intro h a
    exact h.realize_iff
  · intro h
    let σ : L.Sentence :=
      ((φ.iff ψ).relabel (Sum.inr : Fin n → Empty ⊕ Fin n)).iAlls (Fin n)
    have hσ (N : T.ModelType.{0, 0, 0}) :
        (N ⊨ σ) ↔ ∀ a : Fin n → N, φ.Realize a ↔ ψ.Realize a := by
      simp only [σ, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
        Function.comp_def, Sum.elim_inr, Formula.realize_iff]
    apply Theory.models_formula_iff.mpr
    intro N a
    exact Formula.realize_iff.mpr ((hσ N).mp
      ((hT.models_elementarily_equivalent (Theory.ModelType.of T S) N).realize_sentence σ
        |>.mp ((hσ (Theory.ModelType.of T S)).mpr h)) a)

theorem named_formula_equivalence (hT : T.IsComplete) (S : T.ModelType.{0, 0, 0})
    (A : Set S) {n : ℕ} (φ ψ : L.Formula (Fin n)) :
    T.Iff φ ψ ↔ (L[[A]].completeTheory S).Iff
      ((L.lhomWithConstants A).onFormula φ) ((L.lhomWithConstants A).onFormula ψ) := by
  rw [iff_in_complete_model hT S,
    iff_in_complete_model (completeTheory.isComplete L[[A]] S) S]
  apply forall_congr'
  intro a
  exact iff_congr (LHom.realize_onFormula (L.lhomWithConstants A) φ).symm
    (LHom.realize_onFormula (L.lhomWithConstants A) ψ).symm

/-- The actual map sends a shared-syntax old formula to that same formula in the named language. -/
def namedClassMap (hT : T.IsComplete) (S : T.ModelType.{0, 0, 0}) (A : Set S) (n : ℕ) :
    FormulaClass T (Fin n) → FormulaClass (L[[A]].completeTheory S) (Fin n) :=
  Quotient.lift (fun φ => classOf (L[[A]].completeTheory S)
      ((L.lhomWithConstants A).onFormula φ))
    (fun φ ψ h => Quotient.sound ((named_formula_equivalence hT S A φ ψ).mp h))

theorem namedClassMap_injective (hT : T.IsComplete) (S : T.ModelType.{0, 0, 0})
    (A : Set S) (n : ℕ) : Function.Injective (namedClassMap hT S A n) := by
  intro c d h
  induction c using Quotient.inductionOn with
  | h φ =>
    induction d using Quotient.inductionOn with
    | h ψ =>
      apply Quotient.sound
      exact (named_formula_equivalence hT S A φ ψ).mpr (Quotient.exact h)

theorem naming_preserves_noncategoricity [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : T.ModelType.{0, 0, 0}, Infinite N)
    (hcat : ¬ (Cardinal.aleph0 : Cardinal.{0}).Categorical T)
    (S : T.ModelType.{0, 0, 0}) (A : Set S) (hA : A.Finite) :
    ¬ (Cardinal.aleph0 : Cardinal.{0}).Categorical (L[[A]].completeTheory S) := by
  let : Finite A := hA.to_subtype
  let : Infinite S := models_infinite hT hInf
  have hInfA : ∃ N : (L[[A]].completeTheory S).ModelType.{0, 0, 0}, Infinite N :=
    ⟨Theory.ModelType.of _ S, by change Infinite S; infer_instance⟩
  intro hcatA
  apply hcat
  apply (categorical_iff_finite_formulaClasses hT hInf).mpr
  intro n
  let := (categorical_iff_finite_formulaClasses (completeTheory.isComplete L[[A]] S)
    hInfA).mp hcatA n
  exact Finite.of_injective _ (namedClassMap_injective hT S A n)

theorem atomic_saturated_categorical [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : T.ModelType.{0, 0, 0}, Infinite N)
    (M : T.ModelType.{0, 0, 0}) (hA : AtomicAndPrimeModels.IsAtomic T M)
    (hS : Saturation.OmegaSaturated L M) :
    (Cardinal.aleph0 : Cardinal.{0}).Categorical T := by
  apply (categorical_iff_isolated hT hInf).mpr
  intro n p
  obtain ⟨a, ha⟩ := saturated_realizes_types hT hS n p
  rw [(realizes_complete_iff p a).mp ha]
  exact hA n a

theorem third_countable_model [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : T.ModelType.{0, 0, 0}, Infinite N) (hSmall : CountableSaturatedModels.Small T)
    (hcat : ¬ (Cardinal.aleph0 : Cardinal.{0}).Categorical T) :
    ∃ P S N : CountableModel T,
      AtomicAndPrimeModels.IsAtomic T P.model ∧ Saturation.OmegaSaturated L S.model ∧
      ¬ Saturation.OmegaSaturated L N.model ∧
      ¬ Nonempty (P.model ≃[L] S.model) ∧ ¬ Nonempty (P.model ≃[L] N.model) ∧
      ¬ Nonempty (S.model ≃[L] N.model) := by
  classical
  obtain ⟨P, hPc, hPa⟩ := small_exists_countable_atomic hT hSmall
  obtain ⟨S, hSc, hSs⟩ := exists_countable_saturated hT hSmall
  let := hPc
  let := hSc
  let : Infinite P := models_infinite hT hInf
  let : Infinite S := models_infinite hT hInf
  have hniso : ¬ ∀ n (p : T.CompleteType (Fin n)), Isolated T p :=
    fun hall => hcat ((categorical_iff_isolated hT hInf).mpr hall)
  push Not at hniso
  obtain ⟨n, p, hp⟩ := hniso
  obtain ⟨a, ha⟩ := saturated_realizes_types hT hSs n p
  have homit : ¬ ∃ b : Fin n → P, Realizes (formulas p) b := by
    rintro ⟨b, hb⟩
    exact hp ((realizes_complete_iff p b).mp hb |>.symm ▸ hPa n b)
  let A : Set S := Set.range a
  have hA : A.Finite := Set.finite_range a
  let : Finite A := hA.to_subtype
  let U := L[[A]].completeTheory S
  have hU : U.IsComplete := completeTheory.isComplete L[[A]] S
  have hUS : Saturation.OmegaSaturated L[[A]] S := Saturation.finite_names hSs A hA
  have hsmallU : CountableSaturatedModels.Small U := small_of_saturated hU hUS
  obtain ⟨Np, hNpc, hNpa⟩ := small_exists_countable_atomic hU hsmallU
  let := hNpc
  have hincl : (L.lhomWithConstants A).onTheory T ⊆ U := by
    rintro σ ⟨τ, hτ, rfl⟩
    exact (LHom.realize_onSentence S (L.lhomWithConstants A) τ).mpr
      (T.realize_sentence_of_mem hτ)
  have hNpT : Np ⊨ (L.lhomWithConstants A).onTheory T := Np.is_model.mono hincl
  let : L.Structure Np := (L.lhomWithConstants A).reduct Np
  let : (L.lhomWithConstants A).IsExpansionOn Np := LHom.isExpansionOn_reduct _ _
  let : Np ⊨ T := (LHom.onTheory_model (L.lhomWithConstants A) T).mp hNpT
  let N : T.ModelType.{0, 0, 0} := Theory.ModelType.of T Np
  let : Countable N := by change Countable Np; infer_instance
  let : Infinite N := models_infinite hT hInf
  let b : Fin n → Np := fun i => (L.con (⟨a i, Set.mem_range_self i⟩ : A) : Np)
  have hb : Realizes (formulas p) b := by
    intro φ hφ
    let cs : Fin n → L[[A]].Term Empty := fun i =>
      (L.con (⟨a i, Set.mem_range_self i⟩ : A)).term
    let σ : L[[A]].Sentence := ((L.lhomWithConstants A).onFormula φ).subst cs
    have hσ : S ⊨ σ := by
      change BoundedFormula.Realize σ (default : Empty → S) (default : Fin 0 → S)
      dsimp only [σ]
      rw [BoundedFormula.realize_subst]
      have hv : (fun i => (cs i).realize (default : Empty → S)) = a := by
        funext i
        simp only [cs, Term.realize_constants, coe_con]
      rw [hv]
      exact (LHom.realize_onFormula (L.lhomWithConstants A) φ).mpr (ha φ hφ)
    have hn : Np ⊨ σ := Np.is_model.realize_of_mem _ hσ
    have hr := BoundedFormula.realize_subst.mp hn
    simp only [cs, Term.realize_constants] at hr
    change ((L.lhomWithConstants A).onFormula φ).Realize b at hr
    exact (LHom.realize_onFormula (L.lhomWithConstants A) φ).mp hr
  have hInfU : ∃ K : U.ModelType.{0, 0, 0}, Infinite K :=
    ⟨Theory.ModelType.of U S, by change Infinite S; infer_instance⟩
  have hnotNp : ¬ Saturation.OmegaSaturated L[[A]] Np := by
    intro hs
    exact naming_preserves_noncategoricity hT hInf hcat S A hA
      (atomic_saturated_categorical hU hInfU Np hNpa hs)
  have hnotN : ¬ Saturation.OmegaSaturated L N := by
    change ¬ Saturation.OmegaSaturated L Np
    intro hs
    exact hnotNp (Saturation.finite_constant_expansion hs A)
  refine ⟨⟨P⟩, ⟨S⟩, ⟨N⟩, hPa, hSs, hnotN, ?_, ?_, ?_⟩
  · rintro ⟨e⟩
    apply homit
    exact ⟨e.symm ∘ a, fun φ hφ =>
      (e.symm.toElementaryEmbedding.map_formula φ a).mpr (ha φ hφ)⟩
  · rintro ⟨e⟩
    apply homit
    exact ⟨e.symm ∘ b, fun φ hφ =>
      (e.symm.toElementaryEmbedding.map_formula φ b).mpr (hb φ hφ)⟩
  · rintro ⟨e⟩
    exact hnotN ((Saturation.isomorphism_invariant e).mp hSs)

theorem never_two [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : T.ModelType.{0, 0, 0}, Infinite N) : spectrum T ≠ 2 := by
  classical
  intro h
  obtain ⟨E⟩ := Cardinal.mk_eq_nat_iff.mp h
  let : Finite (ModelClass T) := Finite.of_injective E E.injective
  have hSmall := finite_spectrum_small hT hInf inferInstance
  have hcat : ¬ (Cardinal.aleph0 : Cardinal.{0}).Categorical T := by
    intro hc
    have hone := (categorical_iff_spectrum_one hT hInf).mp hc
    rw [hone] at h
    norm_num at h
  obtain ⟨P, S, N, _, _, _, hPS, hPN, hSN⟩ := third_countable_model hT hInf hSmall hcat
  have hcPS : modelClass T P ≠ modelClass T S := fun h => hPS ((modelClass_eq_iff _ _).mp h)
  have hcPN : modelClass T P ≠ modelClass T N := fun h => hPN ((modelClass_eq_iff _ _).mp h)
  have hcSN : modelClass T S ≠ modelClass T N := fun h => hSN ((modelClass_eq_iff _ _).mp h)
  let f : Fin 3 → ModelClass T := ![modelClass T P, modelClass T S, modelClass T N]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hbound := Fintype.card_le_of_injective (E ∘ f) (E.injective.comp hf)
  norm_num at hbound

end Lemmatheca.ModelTheory.CountableModels
