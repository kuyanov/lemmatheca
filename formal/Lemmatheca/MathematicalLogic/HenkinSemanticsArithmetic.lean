import Lemmatheca.MathematicalLogic.HenkinSemanticsTransfer
import Lemmatheca.MathematicalLogic.SecondOrderArithmetic

/-! Full comprehension can coexist with nonstandard general arithmetic models. -/
namespace Lemmatheca.MathematicalLogic.HenkinSemantics
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.SecondOrderLogic
noncomputable section
namespace GeneralArithmetic
abbrev AL := ArithmeticTheories.expandedLanguage

def nonstandardSentences : Theory AL :=
  {σ | σ.val ∈ SecondOrderArithmetic.noncompactTheory}

def numeralRelation (H : GeneralModel AL) : (Fin 1 → H.Carrier) → Prop :=
  fun xs => ∃ n : ℕ, (ArithmeticTheories.expansionMap.onTerm
    (ArithmeticTheories.numeral n)).realize Empty.elim = xs 0

theorem exists_nonstandard_comprehension_model :
    ∃ H : GeneralModel AL, H.FullComprehension ∧
      ∀ φ ∈ SecondOrderArithmetic.noncompactTheory, H.Models φ := by
  classical
  have hs : Satisfiable (nonstandardSentences ∪ comprehensionTheory AL) := by
    apply compactness_with_scheme
    intro F hF
    let Δ : Finset (Formula AL) := F.image Subtype.val
    have hΔ : (↑Δ : Set (Formula AL)) ⊆ SecondOrderArithmetic.noncompactTheory := by
      intro φ hφ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hφ
      exact hF hσ
    obtain ⟨I, hI⟩ := SecondOrderArithmetic.noncompact_finite_standard_models Δ hΔ
    let : AL.Structure ℕ := I
    refine ⟨fullGeneralModel AL ℕ, ?_⟩
    intro σ hσ
    rcases hσ with hσ | hσ
    · intro a r _
      exact hI σ.val (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩) a r
    · exact full_models_comprehensionTheory ℕ σ hσ
  obtain ⟨H, hH⟩ := hs
  refine ⟨H, (models_comprehensionTheory_iff H).mp ?_, ?_⟩
  · intro σ hσ
    exact hH σ (Or.inr hσ)
  · intro φ hφ
    exact hH ⟨φ, SecondOrderArithmetic.noncompact_sentences φ hφ⟩ (Or.inl hφ)


theorem numeralRelation_unavailable (H : GeneralModel AL)
    (h : ∀ φ ∈ SecondOrderArithmetic.noncompactTheory, H.Models φ) :
    numeralRelation H ∉ H.domains 1 := by
  classical
  let : ArithmeticTheories.language.Structure H.Carrier :=
    ArithmeticTheories.expansionMap.reduct H.Carrier
  intro hR
  let a : ℕ → H.Carrier := fun _ => Classical.choice H.nonempty
  let r : RelationAssignment H.Carrier := fun n _ => (H.domains_nonempty n).choose
  have hr : ∀ n X, r n X ∈ H.domains n := fun n _ => (H.domains_nonempty n).choose_spec
  have hn (n : ℕ) : (ArithmeticTheories.expansionMap.onTerm
      (ArithmeticTheories.numeral n)).realize (M := H.Carrier) Empty.elim =
      ArithmeticTheories.numeralValue H.Carrier n :=
    ArithmeticTheories.expansionMap.realize_onTerm _ _
  let z : AL.Functions 0 := Sum.inl ArithmeticTheories.FunctionSymbol.zero
  let s : AL.Functions 1 := Sum.inl ArithmeticTheories.FunctionSymbol.succ
  have hi := h _ (Or.inl (Or.inr rfl)) a r hr
  change realize H.domains a r (inductionSentence z s) at hi
  simp only [inductionSentence, realize, realize_and, realize_tuple_one,
    Term.realize_var, Term.realize_func, Function.update_self, updateRelation_same] at hi
  have hz : (fun i : Fin 0 => (Fin.elim0 i : AL.Term ℕ).realize a) =
      (Fin.elim0 : Fin 0 → H.Carrier) := Subsingleton.elim _ _
  rw [hz] at hi
  have hzero : numeralRelation H ![Structure.funMap (L := AL)
      z Fin.elim0] := by
    refine ⟨0, ?_⟩
    rw [hn, ArithmeticTheories.numeral_value_zero]
    rfl
  have hstep (x : H.Carrier) (hx : numeralRelation H ![x]) :
      numeralRelation H ![Structure.funMap (L := AL)
        s (fun _ => x)] := by
    obtain ⟨n, hnx⟩ := hx
    refine ⟨n+1, ?_⟩
    rw [hn] at hnx
    rw [hn, ArithmeticTheories.numeral_value_succ, hnx]
    rfl
  have hall := hi (numeralRelation H) hR ⟨hzero, hstep⟩
  let c : H.Carrier := ArithmeticTheories.freshConstant.realize Empty.elim
  obtain ⟨n, hnc⟩ := hall c
  have hc := h _ (Or.inr ⟨n, rfl⟩) a r hr
  rw [realize_ofSentence, ArithmeticTheories.realize_avoidsNumeral] at hc
  rw [hn] at hnc
  exact hc hnc.symm


end GeneralArithmetic
end
end Lemmatheca.MathematicalLogic.HenkinSemantics
