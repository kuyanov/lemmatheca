import Lemmatheca.CountableModels.SequenceOrders
import Lemmatheca.CountableModels.Representatives
import Lemmatheca.CountableModels.NamedQuantifierElimination

namespace Lemmatheca.ModelTheory.CountableModels

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open QuantifierElimination.Shared



theorem named_formula_elimination {n : ℕ} (φ : sequenceLanguage.Formula (Fin n)) :
    ∃ ψ : sequenceLanguage.Formula (Fin n), ψ.IsQF ∧ sequenceTheory.Iff φ ψ := by
  exact expanded_dlo_formula_elimination sequenceTheory Set.subset_union_left φ

private theorem closed_term_constant (t : sequenceLanguage.Term (Fin 0 ⊕ Fin 0)) :
    ∃ k : ℕ, t = .func (Sum.inr k : sequenceLanguage.Functions 0) Fin.elim0 := by
  cases t with
  | var x => exact isEmptyElim x
  | @func n f ts =>
    cases f with
    | inl f => exact f.elim
    | inr f =>
      cases n with
      | zero =>
        refine ⟨f, ?_⟩
        congr 1
        exact Subsingleton.elim _ _
      | succ n => exact f.elim

private theorem constant_term_realize {M : Type} [sequenceLanguage.Structure M]
    (i : ℕ) (v : Fin 0 ⊕ Fin 0 → M) :
    (Term.func (L := sequenceLanguage) (Sum.inr i : sequenceLanguage.Functions 0) Fin.elim0).realize v =
      namedValue M i :=
  funMap_eq_coe_constants (L := sequenceLanguage) (M := M)

private theorem qf_closed_agreement {M N : Type}
    [sequenceLanguage.Structure M] [sequenceLanguage.Structure N]
    [M ⊨ sequenceTheory] [N ⊨ sequenceTheory]
    {φ : sequenceLanguage.Formula (Fin 0)} (hφ : φ.IsQF) :
    φ.Realize (Fin.elim0 : Fin 0 → M) ↔ φ.Realize (Fin.elim0 : Fin 0 → N) := by
  let : LinearOrder M := orderOfAxioms (sequenceRelation M) (sequence_axioms M).1
  let : LinearOrder N := orderOfAxioms (sequenceRelation N) (sequence_axioms N).1
  have hM : StrictMono (namedValue M) := strictMono_nat_of_lt_succ (sequence_axioms M).2
  have hN : StrictMono (namedValue N) := strictMono_nat_of_lt_succ (sequence_axioms N).2
  induction hφ with
  | falsum => exact Iff.rfl
  | of_isAtomic h =>
    cases h with
    | equal t s =>
      obtain ⟨i, rfl⟩ := closed_term_constant t
      obtain ⟨j, rfl⟩ := closed_term_constant s
      change ((Term.func (L := sequenceLanguage) (Sum.inr i : sequenceLanguage.Functions 0) Fin.elim0).realize
        (Sum.elim Fin.elim0 (default : Fin 0 → M)) =
        (Term.func (L := sequenceLanguage) (Sum.inr j : sequenceLanguage.Functions 0) Fin.elim0).realize
          (Sum.elim Fin.elim0 (default : Fin 0 → M))) ↔
        ((Term.func (L := sequenceLanguage) (Sum.inr i : sequenceLanguage.Functions 0) Fin.elim0).realize
          (Sum.elim Fin.elim0 (default : Fin 0 → N)) =
        (Term.func (L := sequenceLanguage) (Sum.inr j : sequenceLanguage.Functions 0) Fin.elim0).realize
          (Sum.elim Fin.elim0 (default : Fin 0 → N)))
      rw [constant_term_realize, constant_term_realize, constant_term_realize,
        constant_term_realize]
      exact hM.injective.eq_iff.trans hN.injective.eq_iff.symm
    | @rel n R ts =>
      cases R with
      | inl R =>
        cases R with
        | rel =>
          obtain ⟨i, hi⟩ := closed_term_constant (ts 0)
          obtain ⟨j, hj⟩ := closed_term_constant (ts 1)
          have ht : ts = ![.func (Sum.inr i : sequenceLanguage.Functions 0) Fin.elim0,
              .func (Sum.inr j : sequenceLanguage.Functions 0) Fin.elim0] := by
            ext k
            fin_cases k
            · exact hi
            · exact hj
          subst ts
          have hv (X : Type) [sequenceLanguage.Structure X] :
              (fun k : Fin 2 =>
                ((![Term.func (L := sequenceLanguage) (Sum.inr i : sequenceLanguage.Functions 0) Fin.elim0,
                  Term.func (L := sequenceLanguage) (Sum.inr j : sequenceLanguage.Functions 0) Fin.elim0] k :
                  sequenceLanguage.Term (Fin 0 ⊕ Fin 0))).realize
                    (Sum.elim Fin.elim0 (default : Fin 0 → X))) =
                ![namedValue X i, namedValue X j] := by
            funext k
            fin_cases k <;> exact constant_term_realize _ _
          change Structure.RelMap (L := sequenceLanguage) (.inl .rel)
              (fun k : Fin 2 =>
                ((![Term.func (L := sequenceLanguage) (Sum.inr i : sequenceLanguage.Functions 0) Fin.elim0,
                  Term.func (L := sequenceLanguage) (Sum.inr j : sequenceLanguage.Functions 0) Fin.elim0] k :
                  sequenceLanguage.Term (Fin 0 ⊕ Fin 0))).realize
                    (Sum.elim Fin.elim0 (default : Fin 0 → M))) ↔
            Structure.RelMap (L := sequenceLanguage) (.inl .rel)
              (fun k : Fin 2 =>
                ((![Term.func (L := sequenceLanguage) (Sum.inr i : sequenceLanguage.Functions 0) Fin.elim0,
                  Term.func (L := sequenceLanguage) (Sum.inr j : sequenceLanguage.Functions 0) Fin.elim0] k :
                  sequenceLanguage.Term (Fin 0 ⊕ Fin 0))).realize
                    (Sum.elim Fin.elim0 (default : Fin 0 → N)))
          rw [hv M, hv N]
          change namedValue M i < namedValue M j ↔ namedValue N i < namedValue N j
          exact hM.lt_iff_lt.trans hN.lt_iff_lt.symm
      | inr R => exact R.elim
  | imp _ _ ihφ ihψ => exact imp_congr ihφ ihψ

theorem sequenceTheory_complete : sequenceTheory.IsComplete := by
  apply (Theory.IsComplete.isComplete_iff_models_elementarily_equivalent
    (T := sequenceTheory)).mpr
  refine ⟨Theory.Model.isSatisfiable (representative 0).model, fun M N => ?_⟩
  apply elementarilyEquivalent_iff.mpr
  intro σ
  obtain ⟨ψ, hψ, he⟩ := named_formula_elimination (σ.relabel (Empty.elim : Empty → Fin 0))
  have hM : (M ⊨ σ) ↔ ψ.Realize (Fin.elim0 : Fin 0 → M) := by
    have hh := he.realize_iff (M := M) (v := (Fin.elim0 : Fin 0 → M))
    simpa only [Formula.realize_relabel, Sentence.Realize, Unique.eq_default] using hh
  have hN : (N ⊨ σ) ↔ ψ.Realize (Fin.elim0 : Fin 0 → N) := by
    have hh := he.realize_iff (M := N) (v := (Fin.elim0 : Fin 0 → N))
    simpa only [Formula.realize_relabel, Sentence.Realize, Unique.eq_default] using hh
  exact hM.trans ((qf_closed_agreement hψ).trans hN.symm)



theorem sequenceSpectrum_three : spectrum sequenceTheory = 3 := by
  classical
  apply (spectrum_eq_nat_iff 3).mpr
  have hshape (i : Fin 3) : tailShape (representative i).model = representativeShape i :=
    representative_shape i
  have hinj : Function.Injective representativeShape := by decide
  refine ⟨representative, ?_, fun N => ?_⟩
  · intro i j hij ⟨e⟩
    apply hij
    apply hinj
    exact (hshape i).symm.trans ((tailShape_iso (representative i).model e).trans (hshape j))
  · have hex : ∃ i : Fin 3, representativeShape i = tailShape N.model := by
      cases h : tailShape N.model with
      | empty => exact ⟨0, rfl⟩
      | noLeast => exact ⟨1, rfl⟩
      | least => exact ⟨2, rfl⟩
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, (same_tail_isomorphism (representative i).model).mpr ((hshape i).trans hi)⟩

private theorem tail_empty_iff {M : Type} [sequenceLanguage.Structure M] :
    tailShape M = .empty ↔ ¬ (upperTail M).Nonempty := by
  classical
  simp only [tailShape]
  split_ifs <;> simp_all

theorem no_upper_bound_sentence : ¬ ∃ σ : sequenceLanguage.Sentence,
    ∀ M : sequenceTheory.ModelType.{0, 0, 0}, (M ⊨ σ ↔ (upperTail M).Nonempty) := by
  rintro ⟨σ, hσ⟩
  have h0 : ¬ (upperTail (representative 0).model).Nonempty :=
    tail_empty_iff.mp (representative_shape 0)
  have h1 : (upperTail (representative 1).model).Nonempty := by
    by_contra hn
    have hh := tail_empty_iff.mpr hn
    rw [show tailShape (representative 1).model = .noLeast from representative_shape 1] at hh
    cases hh
  have he : ElementarilyEquivalent sequenceLanguage (representative 0).model
      (representative 1).model :=
    (Theory.IsComplete.isComplete_iff_models_elementarily_equivalent.mp
      sequenceTheory_complete).2 _ _
  exact h0 ((hσ _).mp ((elementarilyEquivalent_iff.mp he σ).mpr ((hσ _).mpr h1)))

end Lemmatheca.ModelTheory.CountableModels
