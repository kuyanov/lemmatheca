import Lemmatheca.ChangingLanguages.ChangingLanguages

namespace Lemmatheca.Entry.ChangingLanguages
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs

abbrev TwoConstants := Language.constantsOn Bool
abbrev OneConstant := Language.constantsOn Unit

def collapse : TwoConstants →ᴸ OneConstant where
  onFunction {n} := match n with
    | 0 => fun _ => ()
    | _ + 1 => isEmptyElim
  onRelation := fun {_} R => isEmptyElim R

def distinctSentence : TwoConstants.Sentence :=
  ((Constants.term false : TwoConstants.Term Empty).equal (Constants.term true)).not

@[instance_reducible] def twoPointStructure : TwoConstants.Structure Bool :=
  Language.constantsOn.structure id

theorem identifying_constants_destroys_consistency :
    Consistent ({distinctSentence} : TwoConstants.Theory) ∧
      ¬ Consistent (collapse.onTheory {distinctSentence}) := by
  classical
  constructor
  · let : TwoConstants.Structure Bool := twoPointStructure
    apply consistent_of_model (M := Bool) (default : Empty → Bool)
    intro A hA
    obtain rfl := Set.mem_singleton_iff.mp hA
    change ¬ (false = true)
    exact Bool.false_ne_true
  · intro hcon
    apply hcon
    let B := collapse.onSentence distinctSentence
    refine ⟨{B}, ?_, ?_⟩
    · intro A hA
      obtain rfl := Finset.mem_singleton.mp hA
      exact ⟨distinctSentence, by simp, rfl⟩
    · let t : OneConstant.Term Empty := collapse.onTerm (Constants.term false)
      have he : B = (t.equal t).not := by
        simp [B, distinctSentence, t, LHom.onSentence, LHom.onFormula,
          BoundedFormula.not, Term.equal, Term.bdEqual, Constants.term,
          Term.relabel, collapse]
        rfl
      exact Proof.negElim (Proof.equalIntro t)
        (by rw [← he]; exact Proof.assumption (Finset.mem_singleton_self _))

theorem distinct_interpretations_have_no_expansion :
    ¬ ∃ s : OneConstant.Structure Bool,
      @LHom.IsExpansionOn TwoConstants OneConstant collapse Bool twoPointStructure s := by
  rintro ⟨s, hs⟩
  have hc := @LHom.IsExpansionOn.map_onFunction TwoConstants OneConstant collapse Bool
    twoPointStructure s hs 0 false (fun i => Fin.elim0 i)
  have hd := @LHom.IsExpansionOn.map_onFunction TwoConstants OneConstant collapse Bool
    twoPointStructure s hs 0 true (fun i => Fin.elim0 i)
  have hbad : false = true := hc.symm.trans hd
  exact Bool.false_ne_true hbad

end Lemmatheca.Entry.ChangingLanguages
