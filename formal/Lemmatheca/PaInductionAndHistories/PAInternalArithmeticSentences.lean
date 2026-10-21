import Lemmatheca.PaInductionAndHistories.PACollectionModels
import Lemmatheca.PaInductionAndHistories.PALeastWitnessSentences
import Lemmatheca.PaInductionAndHistories.PAChineseRemainder

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section

def coprimeFormula {α : Type} (a b : language.Term α) : language.Formula α :=
  ((dividesFormula (.var (.inr ())) (a.relabel Sum.inl)).imp
    ((dividesFormula (.var (.inr ())) (b.relabel Sum.inl)).imp
      ((Term.var (.inr ())).equal (numeralTerm 1)))).iAlls Unit

theorem realize_coprimeFormula {α : Type} {M : Type*} [language.Structure M]
    (a b : language.Term α) (v : α → M) :
    (coprimeFormula a b).Realize v ↔ CoprimeModel M (a.realize v) (b.realize v) := by
  simp only [coprimeFormula, Formula.realize_iAlls, Formula.realize_imp,
    realize_dividesFormula, Term.realize_var, Term.realize_relabel,
    Formula.realize_equal, realize_numeralTerm, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr, CoprimeModel]
  exact ⟨fun h r => h (fun _ => r), fun h r => h (r ())⟩

def bezoutSentence : language.Sentence :=
  let matrix : language.Formula (Fin 2 ⊕ Fin 4) :=
    (addTerm (mulTerm (.var (.inl 0)) (.var (.inr 0)))
      (mulTerm (.var (.inl 1)) (.var (.inr 1)))).equal
      (addTerm (numeralTerm 1)
        (addTerm (mulTerm (.var (.inl 0)) (.var (.inr 2)))
          (mulTerm (.var (.inl 1)) (.var (.inr 3)))))
  allClose (((Term.var 0).equal zeroTerm).not.imp
    ((coprimeFormula (.var 0) (.var 1)).imp (matrix.iExs (Fin 4))))

theorem bezout_derives : Derives PA bezoutSentence := by
  apply derives_allClose_of_models
  intro M x
  simp only [Formula.realize_imp, Formula.realize_not, Formula.realize_equal,
    Term.realize_var, realize_zeroTerm, realize_coprimeFormula]
  intro hm hcop
  obtain ⟨v, hv⟩ := bezout_model (x 0) (x 1) hm hcop
  apply Formula.realize_iExs.mpr
  refine ⟨v, ?_⟩
  simpa only [Formula.realize_equal, realize_addTerm, realize_mulTerm,
    realize_numeralTerm, Term.realize_var, Sum.elim_inl, Sum.elim_inr] using hv

def divisionSentence : language.Sentence :=
  let φ : language.Formula (Fin 2 ⊕ Fin 2) :=
    ((Term.var (.inl 1)).equal
      (addTerm (mulTerm (.var (.inl 0)) (.var (.inr 0))) (.var (.inr 1)))) ⊓
      ltFormula (.var (.inr 1)) (.var (.inl 0))
  allClose (((Term.var 0).equal zeroTerm).not.imp (φ.iExsUnique (Fin 2)))

theorem division_derives : Derives PA divisionSentence := by
  apply derives_allClose_of_models
  intro M x
  simp only [Formula.realize_imp, Formula.realize_not, Formula.realize_equal,
    Term.realize_var, realize_zeroTerm]
  intro hm
  rw [Formula.realize_iExsUnique]
  obtain ⟨qr, hqr, hu⟩ := division_model (x 0) hm (x 1)
  refine ⟨![qr.1, qr.2], ?_, ?_⟩
  · simpa only [Formula.realize_inf, Formula.realize_equal, realize_addTerm,
      realize_mulTerm, ltFormula, realize_leFormula, realize_succTerm, Term.realize_var,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one] using hqr
  · intro y hy
    have h := hu (y 0, y 1) (by simpa only [Formula.realize_inf,
      Formula.realize_equal, realize_addTerm, realize_mulTerm, ltFormula,
      realize_leFormula, realize_succTerm, Term.realize_var, Sum.elim_inl, Sum.elim_inr] using hy)
    funext j
    fin_cases j
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

def coprimeCancellationSentence : language.Sentence :=
  allClose ((coprimeFormula (.var 0) (.var 1)).imp
    ((dividesFormula (.var 0) (mulTerm (.var 1) (.var 2))).imp
      (dividesFormula (.var 0) (.var (2 : Fin 3)))))

theorem coprime_cancellation_derives : Derives PA coprimeCancellationSentence := by
  apply derives_allClose_of_models
  intro M x
  simp only [Formula.realize_imp, realize_coprimeFormula, realize_dividesFormula,
    realize_mulTerm, Term.realize_var]
  intro hcop hdiv
  exact coprime_cancellation_model (x 0) (x 1) (x 2) hcop hdiv

def twoModulusSentence : language.Sentence :=
  let φ : language.Formula (Fin 4 ⊕ Fin 3) :=
    ((Term.var (.inr 0)).equal
      (addTerm (mulTerm (.var (.inl 0)) (.var (.inr 1))) (.var (.inl 2)))) ⊓
    ((Term.var (.inr 0)).equal
      (addTerm (mulTerm (.var (.inl 1)) (.var (.inr 2))) (.var (.inl 3))))
  allClose (((Term.var 0).equal zeroTerm).not.imp
    (((Term.var 1).equal zeroTerm).not.imp
      ((coprimeFormula (.var 0) (.var 1)).imp
        ((ltFormula (.var 2) (.var 0)).imp
          ((ltFormula (.var 3) (.var 1)).imp (φ.iExs (Fin 3)))))))

theorem two_modulus_derives : Derives PA twoModulusSentence := by
  apply derives_allClose_of_models
  intro M x
  simp only [Formula.realize_imp, Formula.realize_not, Formula.realize_equal,
    Term.realize_var, realize_zeroTerm, realize_coprimeFormula, ltFormula,
    realize_leFormula, realize_succTerm]
  intro hm hn hcop ha hb
  obtain ⟨c, q, r, hc, hd⟩ := two_modulus_model (x 0) (x 1) (x 2) (x 3) hm hn hcop ha hb
  apply Formula.realize_iExs.mpr
  refine ⟨![c, q, r], ?_⟩
  simpa only [Formula.realize_inf, Formula.realize_equal, realize_addTerm,
    realize_mulTerm, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using And.intro hc hd

def betaExtensionSentence : language.Sentence :=
  let endpoint : language.Formula (Fin 4 ⊕ Fin 2) := graphAt betaGraph
    ![.var (.inr 0), .var (.inr 1), .var (.inl 2)] (.var (.inl 3))
  let same : language.Formula ((Fin 4 ⊕ Fin 2) ⊕ Fin 2) :=
    (ltFormula (.var (.inr 0)) (.var (.inl (.inl 2)))).imp
      ((graphAt betaGraph ![.var (.inl (.inr 0)), .var (.inl (.inr 1)), .var (.inr 0)]
        (.var (.inr 1))).iff
       (graphAt betaGraph ![.var (.inl (.inl 0)), .var (.inl (.inl 1)), .var (.inr 0)]
        (.var (.inr 1))))
  allClose ((endpoint ⊓ same.iAlls (Fin 2)).iExs (Fin 2))

theorem beta_extension_derives : Derives PA betaExtensionSentence := by
  apply derives_allClose_of_models
  intro M x
  obtain ⟨c, d, hn, hi⟩ := beta_extension_model (x 0) (x 1) (x 2) (x 3)
  apply Formula.realize_iExs.mpr
  refine ⟨![c, d], Formula.realize_inf.mpr ⟨?_, ?_⟩⟩
  · rw [realize_graphAt]
    have he : (fun i : Fin 3 => Term.realize (Sum.elim x ![c, d])
        ((![.var (.inr 0), .var (.inr 1), .var (.inl 2)] : Fin 3 → language.Term (Fin 4 ⊕ Fin 2)) i)) = ![c, d, x 2] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact hn
  · apply Formula.realize_iAlls.mpr
    intro w
    simp only [Formula.realize_imp, Formula.realize_iff, ltFormula,
      realize_leFormula, realize_succTerm, realize_graphAt, Term.realize_var,
      Sum.elim_inl, Sum.elim_inr]
    intro h
    have he : (fun i : Fin 3 => Term.realize (Sum.elim (Sum.elim x ![c, d]) w)
        ((![.var (.inl (.inr 0)), .var (.inl (.inr 1)), .var (.inr 0)] : Fin 3 → language.Term ((Fin 4 ⊕ Fin 2) ⊕ Fin 2)) i)) = ![c, d, w 0] := by
      funext i
      fin_cases i <;> rfl
    have hf : (fun i : Fin 3 => Term.realize (Sum.elim (Sum.elim x ![c, d]) w)
        ((![.var (.inl (.inl 0)), .var (.inl (.inl 1)), .var (.inr 0)] : Fin 3 → language.Term ((Fin 4 ⊕ Fin 2) ⊕ Fin 2)) i)) = ![x 0, x 1, w 0] := by
      funext i
      fin_cases i <;> rfl
    rw [he, hf]
    exact hi (w 0) h (w 1)

end
end Lemmatheca.ProofTheory.PAComputations
