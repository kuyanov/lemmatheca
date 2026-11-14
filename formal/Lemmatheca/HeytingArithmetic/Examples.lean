import Lemmatheca.HeytingArithmetic.Correspondence

namespace Lemmatheca.ProofTheory.HeytingArithmetic
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
noncomputable section

/-- The precise equality instance of the moving-parameter question. -/
def movingBase : Sentence :=
  exUnit (termEqual zeroTerm (.var (.inr ()) : LA.Term (Empty ⊕ Unit)))

def movingStep : Sentence :=
  close (.impl
    (termEqual (.var (0 : Fin 2)) (.var (1 : Fin 2)))
    (exUnit (termEqual (succTerm (.var (.inl (0 : Fin 2)))) (.var (.inr ())))))

def movingConclusion : Sentence :=
  exUnit (allUnit (termEqual (.var (.inr ()))
    (.var (.inl (.inr ())) : LA.Term ((Empty ⊕ Unit) ⊕ Unit))))

theorem moving_parameter_counterexample :
    @Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds LA Empty ℕ
        Lemmatheca.ModelTheory.ArithmeticTheories.natStructure movingBase Empty.elim ∧
    @Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds LA Empty ℕ
        Lemmatheca.ModelTheory.ArithmeticTheories.natStructure movingStep Empty.elim ∧
    ¬ @Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds LA Empty ℕ
        Lemmatheca.ModelTheory.ArithmeticTheories.natStructure movingConclusion Empty.elim := by
  have hc (A : Sentence) :
      Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds A (Empty.elim : Empty → ℕ) ↔
        @FirstOrder.Language.Sentence.Realize LA ℕ
          Lemmatheca.ModelTheory.ArithmeticTheories.natStructure A.toClassical := by
    unfold Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds
      _root_.FirstOrder.Language.Sentence.Realize _root_.FirstOrder.Language.Formula.Realize
    convert (toClassical_realize A (Empty.elim : Empty → ℕ) Fin.elim0).symm using 1
    exact Iff.of_eq (congrArg₂ (fun (a : Empty → ℕ) (b : Fin 0 → ℕ) =>
      @FirstOrder.Language.BoundedFormula.Realize LA ℕ
        Lemmatheca.ModelTheory.ArithmeticTheories.natStructure Empty 0 A.toClassical a b)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _))
  rw [hc, hc, hc]
  simp only [movingBase, movingStep, movingConclusion, exUnit_toClassical,
    allUnit_toClassical, close_toClassical,
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual, toClassical,
    Lemmatheca.ModelTheory.ArithmeticTheories.realize_close]
  simp only [_root_.FirstOrder.Language.Sentence.Realize,
    _root_.FirstOrder.Language.Formula.realize_iExs,
    Lemmatheca.ModelTheory.ArithmeticTheories.realize_allUnit,
    _root_.FirstOrder.Language.Formula.realize_imp]
  simp [_root_.FirstOrder.Language.Formula.Realize,
    _root_.FirstOrder.Language.BoundedFormula.Realize,
    Term.realize, zeroTerm, succTerm,
    Lemmatheca.ModelTheory.ArithmeticTheories.zeroTerm,
    Lemmatheca.ModelTheory.ArithmeticTheories.succTerm]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ => Lemmatheca.ModelTheory.ArithmeticTheories.zeroValue ℕ, ?_⟩
    change Structure.funMap (L := LA) .zero _ = Structure.funMap (L := LA) .zero Fin.elim0
    congr 1
    funext i
    exact i.elim0
  · intro a h
    exact ⟨fun _ => _, rfl⟩
  · intro x
    exact ⟨x () + 1, Nat.succ_ne_self (x ())⟩


end
end Lemmatheca.ProofTheory.HeytingArithmetic
