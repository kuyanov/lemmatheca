import Lemmatheca.FirstOrderNormalForms.FirstOrderNormalForms
import Lemmatheca.FirstOrderStructures.BasicStructures
import Mathlib.Tactic.FinCases

/-! Worked normal-form conversions and concrete boundary examples. -/

namespace Lemmatheca.Entry.FirstOrderNormalForms

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderNormalForms
local instance twoStrictStructure : binaryRelLanguage.Structure (Fin 2) :=
  Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure (Fin 2) (· < ·)

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

def uncapturedEquality (L : Language) : L.Formula ℕ :=
  ((.var (.inr (0 : Fin 1)) : L.Term (ℕ ⊕ Fin 1)).bdEqual (.var (.inl 0))).all

def capturedEquality (L : Language) : L.Formula ℕ :=
  ((.var (.inr (0 : Fin 1)) : L.Term (ℕ ⊕ Fin 1)).bdEqual (.var (.inr 0))).all

theorem capture_counterexample (a : ℕ → Fin 2) :
    ¬ (uncapturedEquality binaryRelLanguage).Realize a ∧
      (capturedEquality binaryRelLanguage).Realize a := by
  simp only [uncapturedEquality, capturedEquality, Formula.Realize,
    BoundedFormula.realize_all]
  change (¬ ∀ x : Fin 2, x = a 0) ∧ ∀ x : Fin 2, x = x
  constructor
  · intro h
    have hc : (0 : Fin 2) = 1 := (h 0).trans (h 1).symm
    exact (by decide : (0 : Fin 2) ≠ 1) hc
  · exact fun _ => rfl

theorem capture_support :
    (uncapturedEquality binaryRelLanguage).freeVarFinset = {0} ∧
    (capturedEquality binaryRelLanguage).freeVarFinset = ∅ := by
  simp [uncapturedEquality, capturedEquality, Term.bdEqual, Term.varFinsetLeft]

def negatedUniversalImplication (P : L.Relations 1) (R : L.Relations 2) : L.Sentence :=
  ((P.boundedFormula₁ (.var (.inr (0 : Fin 1)))).imp
    (R.boundedFormula₂ (.var (.inr (0 : Fin 2))) (.var (.inr 1))).ex).all.not

def negatedUniversalNnf (P : L.Relations 1) (R : L.Relations 2) : L.Sentence :=
  ((P.boundedFormula₁ (.var (.inr (0 : Fin 1)))) ⊓
    (R.boundedFormula₂ (.var (.inr (0 : Fin 2))) (.var (.inr 1))).not.all).ex

theorem negated_universal_conversion (P : L.Relations 1) (R : L.Relations 2) :
    negatedUniversalImplication P R ⇔[(∅ : L.Theory)] negatedUniversalNnf P R := by
  classical
  intro N a b
  simp [BoundedFormula.realize_iff, negatedUniversalImplication,
    negatedUniversalNnf, BoundedFormula.realize_not, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_inf]

theorem negated_universal_isNnf (P : L.Relations 1) (R : L.Relations 2) :
    IsNnf (negatedUniversalNnf P R) := by
  apply IsNnf.ex
  apply IsNnf.inf
  · exact IsNnf.atom (BoundedFormula.IsAtomic.rel _ _)
  · exact IsNnf.all (IsNnf.negAtom (BoundedFormula.IsAtomic.rel _ _))

def quantifiedImplication (R : L.Relations 2) : L.Formula ℕ :=
  (R.boundedFormula₂ (.var (.inr (0 : Fin 1))) (.var (.inr 0))).all.imp
    (R.boundedFormula₂ (.var (.inr (0 : Fin 1))) (.var (.inl 0))).ex

def quantifiedImplicationNnf (R : L.Relations 2) : L.Formula ℕ :=
  (R.boundedFormula₂ (.var (.inr (0 : Fin 1))) (.var (.inr 0))).not.ex ⊔
    (R.boundedFormula₂ (.var (.inr (0 : Fin 1))) (.var (.inl 0))).ex

def quantifiedImplicationPrenex (R : L.Relations 2) : L.Formula ℕ :=
  ((R.boundedFormula₂ (.var (.inr (0 : Fin 2))) (.var (.inr 0))).not ⊔
    R.boundedFormula₂ (.var (.inr (1 : Fin 2))) (.var (.inl 0))).ex.ex

theorem quantified_implication_conversion (R : L.Relations 2) :
    (quantifiedImplication R ⇔[(∅ : L.Theory)] quantifiedImplicationNnf R) ∧
    (quantifiedImplicationNnf R ⇔[(∅ : L.Theory)] quantifiedImplicationPrenex R) := by
  classical
  constructor
  · intro N a b
    simp [BoundedFormula.realize_iff, quantifiedImplication,
      quantifiedImplicationNnf, BoundedFormula.realize_imp,
      BoundedFormula.realize_all, BoundedFormula.realize_ex,
      BoundedFormula.realize_sup, BoundedFormula.realize_not, imp_iff_not_or]
  · intro N a b
    rw [BoundedFormula.realize_iff]
    simp only [quantifiedImplicationNnf, quantifiedImplicationPrenex,
      BoundedFormula.realize_sup, BoundedFormula.realize_ex,
      BoundedFormula.realize_not]
    have hr {k : ℕ} (i j : ℕ ⊕ Fin k) (xs : Fin k → N) :
        (R.boundedFormula₂ (.var i) (.var j)).Realize a xs ↔
          Structure.RelMap R ![Sum.elim a xs i, Sum.elim a xs j] := by
      rw [Relations.boundedFormula₂, BoundedFormula.realize_rel]
      have he : (fun l : Fin 2 =>
          Term.realize (Sum.elim a xs) (![(Term.var i : L.Term (ℕ ⊕ Fin k)), Term.var j] l)) =
          ![Sum.elim a xs i, Sum.elim a xs j] := by
        funext l
        fin_cases l <;> rfl
      rw [he]
    obtain ⟨d⟩ : Nonempty N := inferInstance
    constructor
    · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
      · refine ⟨x, d, Or.inl ?_⟩
        simpa [hr, Fin.snoc] using hx
      · refine ⟨d, y, Or.inr ?_⟩
        simpa [hr, Fin.snoc] using hy
    · rintro ⟨x, y, hx | hy⟩
      · refine Or.inl ⟨x, ?_⟩
        simpa [hr, Fin.snoc] using hx
      · refine Or.inr ⟨y, ?_⟩
        simpa [hr, Fin.snoc] using hy

theorem quantified_implication_shapes (R : L.Relations 2) :
    IsNnf (quantifiedImplicationNnf R) ∧ IsPrenexNnf (quantifiedImplicationPrenex R) ∧
    ¬ (quantifiedImplication R).IsPrenex ∧ ¬ IsNnf (quantifiedImplication R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IsNnf.sup (IsNnf.ex (IsNnf.negAtom (BoundedFormula.IsAtomic.rel _ _)))
      (IsNnf.ex (IsNnf.atom (BoundedFormula.IsAtomic.rel _ _)))
  · apply IsPrenexNnf.ex
    apply IsPrenexNnf.ex
    apply IsPrenexNnf.matrix
    · exact (BoundedFormula.IsAtomic.rel _ _).isQF.not.sup
        (BoundedFormula.IsAtomic.rel _ _).isQF
    · exact IsNnf.sup (IsNnf.negAtom (BoundedFormula.IsAtomic.rel _ _))
        (IsNnf.atom (BoundedFormula.IsAtomic.rel _ _))
  · intro h
    cases h with
    | of_isQF h =>
      cases h with
      | of_isAtomic h => cases h
      | imp hA _hB => exact BoundedFormula.not_all_isQF _ hA
  · intro h
    cases h with
    | atom h => cases h

theorem quantified_implication_support (R : L.Relations 2) :
    (quantifiedImplication R).freeVarFinset = {0} ∧
    (quantifiedImplicationPrenex R).freeVarFinset = {0} := by
  constructor
  · ext x
    simp [quantifiedImplication, Relations.boundedFormula₂, Relations.boundedFormula,
      BoundedFormula.ex, BoundedFormula.not, Fin.exists_fin_two]
  · change
      (R.boundedFormula₂ (.var (.inr (0 : Fin 2))) (.var (.inr 0))).freeVarFinset ∪
      (R.boundedFormula₂ (.var (.inr (1 : Fin 2))) (.var (.inl 0))).freeVarFinset = {0}
    ext x
    simp [Relations.boundedFormula₂, Relations.boundedFormula, Fin.exists_fin_two]

theorem example_prenex_nnf (R : L.Relations 2) :
    IsPrenexNnf
      (((R.boundedFormula₂ (.var (.inr (0 : Fin 2))) (.var (.inr 1))).not ⊔
        (.var (.inr (0 : Fin 2)) : L.Term (Empty ⊕ Fin 2)).bdEqual
          (.var (.inr 1))).ex.all) := by
  apply IsPrenexNnf.all
  apply IsPrenexNnf.ex
  apply IsPrenexNnf.matrix
  · exact (BoundedFormula.IsAtomic.rel _ _).isQF.not.sup
      (BoundedFormula.IsAtomic.equal _ _).isQF
  · exact IsNnf.sup (IsNnf.negAtom (BoundedFormula.IsAtomic.rel _ _))
      (IsNnf.atom (BoundedFormula.IsAtomic.equal _ _))

theorem empty_scope_failures :
    ¬ (Empty ⊨ (((⊤ : Language.empty.BoundedFormula Empty 1).all) ⊓ ⊥)) ∧
    (Empty ⊨ ((⊤ : Language.empty.BoundedFormula Empty 1) ⊓ ⊥).all) ∧
    (Empty ⊨ (((⊥ : Language.empty.BoundedFormula Empty 1).ex) ⊔ ⊤)) ∧
    ¬ (Empty ⊨ ((⊥ : Language.empty.BoundedFormula Empty 1) ⊔ ⊤).ex) := by
  simp [Sentence.Realize, Formula.Realize, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, BoundedFormula.realize_all, BoundedFormula.realize_ex]

theorem two_element_quantifier_order :
    (Fin 2 ⊨ eachHasEqual binaryRelLanguage) ∧
    ¬ (Fin 2 ⊨ commonEqual binaryRelLanguage) := by
  constructor
  · exact eachHasEqual_realize
  · rw [commonEqual_realize]
    rintro ⟨h, _⟩
    have hc := h.allEq (0 : Fin 2) 1
    exact (by decide : (0 : Fin 2) ≠ 1) hc

end Lemmatheca.Entry.FirstOrderNormalForms
