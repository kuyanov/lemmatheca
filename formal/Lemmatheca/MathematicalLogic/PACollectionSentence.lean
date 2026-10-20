import Lemmatheca.MathematicalLogic.PAComputationsSentences
import Lemmatheca.MathematicalLogic.ArithmeticBoundedFormulas

namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section
universe u

def formulaAtTwo {k : ℕ} {α : Type}
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit))
    (x : Fin k → language.Term α) (i y : language.Term α) : language.Formula α :=
  φ.subst (Sum.elim (Sum.elim x (fun _ => i)) (fun _ => y))

theorem realize_formulaAtTwo {k : ℕ} {α : Type} {M : Type u} [language.Structure M]
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit))
    (x : Fin k → language.Term α) (i y : language.Term α) (v : α → M) :
    (formulaAtTwo φ x i y).Realize v ↔
      φ.Realize (extend (extend (fun j => (x j).realize v) (i.realize v)) (y.realize v)) := by
  simp only [formulaAtTwo, Formula.Realize, BoundedFormula.realize_subst]
  have he : (fun a => Term.realize v (Sum.elim (Sum.elim x (fun _ => i)) (fun _ => y) a)) =
      extend (extend (fun j => (x j).realize v) (i.realize v)) (y.realize v) := by
    funext j
    cases j with
    | inl j => cases j <;> rfl
    | inr j => rfl
  rw [he]

def boundedCollectionSentence {k : ℕ}
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit)) : language.Sentence :=
  let hypMatrix : language.Formula (((Fin k ⊕ Unit) ⊕ Unit) ⊕ Unit) :=
    formulaAtTwo φ (fun j => .var (.inl (.inl (.inl j))))
      (.var (.inl (.inr ()))) (.var (.inr ()))
  let hypothesis := strictAll (.var (.inr ())) (hypMatrix.iExs Unit)
  let matrix : language.Formula (((Fin k ⊕ Unit) ⊕ Fin 2) ⊕ Fin 2) :=
    (ltFormula (.var (.inr 0)) (.var (.inl (.inl (.inr ()))))).imp
      ((graphAt betaGraph ![.var (.inl (.inr 0)), .var (.inl (.inr 1)), .var (.inr 0)]
        (.var (.inr 1))).imp
        (formulaAtTwo φ (fun j => .var (.inl (.inl (.inl j))))
          (.var (.inr 0)) (.var (.inr 1))))
  allClose (hypothesis.imp ((matrix.iAlls (Fin 2)).iExs (Fin 2)))

theorem bounded_collection_derives {k : ℕ}
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit)) :
    Derives PA (boundedCollectionSentence φ) := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, realize_strictAll, Term.realize_var, realize_formulaAtTwo,
    Formula.realize_iExs, Sum.elim_inl, Sum.elim_inr]
  intro h
  let x : Fin k → M := fun j => v (.inl j)
  have hh : ∀ i, leValue M (succValue M i) (v (.inr ())) → ∃ y,
      φ.Realize (extend (extend x i) y) := by
    intro i hi
    obtain ⟨y, hy⟩ := h i hi
    exact ⟨y (), hy⟩
  obtain ⟨c, d, hcd⟩ := bounded_witness_collection φ x (v (.inr ())) hh
  refine ⟨![c, d], ?_⟩
  apply Formula.realize_iAlls.mpr
  intro w
  simp only [Formula.realize_imp, ltFormula, realize_leFormula, realize_succTerm,
    Term.realize_var, realize_graphAt, realize_formulaAtTwo,
    Sum.elim_inl, Sum.elim_inr]
  intro hi hb
  have he : (fun i : Fin 3 => Term.realize (Sum.elim (Sum.elim v ![c, d]) w)
      ((![.var (.inl (.inr 0)), .var (.inl (.inr 1)), .var (.inr 0)] :
        Fin 3 → language.Term (((Fin k ⊕ Unit) ⊕ Fin 2) ⊕ Fin 2)) i)) = ![c, d, w 0] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at hb
  exact hcd (w 0) hi (w 1) hb

/-- The exact single-witness matrix displayed in the exposition. -/
def collectionHypothesis {k : ℕ}
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit)) : language.Formula (Fin k ⊕ Unit) :=
  let matrix : language.Formula (((Fin k ⊕ Unit) ⊕ Unit) ⊕ Unit) :=
    formulaAtTwo φ (fun j => .var (.inl (.inl (.inl j))))
      (.var (.inl (.inr ()))) (.var (.inr ()))
  strictAll (.var (.inr ())) (matrix.iExs Unit)

def collectionMatrix {k : ℕ}
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit)) :
    language.Formula ((Fin k ⊕ Unit) ⊕ Fin 2) :=
  let matrix : language.Formula ((((Fin k ⊕ Unit) ⊕ Fin 2) ⊕ Unit) ⊕ Unit) :=
    (graphAt betaGraph ![.var (.inl (.inl (.inr 0))), .var (.inl (.inl (.inr 1))),
      .var (.inl (.inr ()))] (.var (.inr ()))) ⊓
    (formulaAtTwo φ (fun j => .var (.inl (.inl (.inl (.inl j)))))
      (.var (.inl (.inr ()))) (.var (.inr ())))
  strictAll (.var (.inl (.inr ())))
    (boundedEx (.var (.inl (.inr 0))) matrix)

private theorem realize_term_vec3 {α : Type} {M : Type u} [language.Structure M]
    (a b c : language.Term α) (v : α → M) :
    (fun i : Fin 3 => ((![a,b,c] : Fin 3 → language.Term α) i).realize v) =
      ![a.realize v, b.realize v, c.realize v] := by
  funext i
  fin_cases i <;> rfl

theorem realize_collectionHypothesis {k : ℕ} {M : Type u} [language.Structure M]
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit)) (x : Fin k → M) (n : M) :
    (collectionHypothesis φ).Realize (extend x n) ↔
      ∀ i, leValue M (succValue M i) n → ∃ y, φ.Realize (extend (extend x i) y) := by
  simp only [collectionHypothesis, realize_strictAll, Term.realize_var,
    Formula.realize_iExs, realize_formulaAtTwo, extend, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h i hi
    obtain ⟨y, hy⟩ := h i hi
    exact ⟨y (), hy⟩
  · intro h i hi
    obtain ⟨y, hy⟩ := h i hi
    exact ⟨fun _ => y, hy⟩

theorem realize_collectionMatrix {k : ℕ} {M : Type u} [language.Structure M]
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit)) (x : Fin k → M) (n c d : M) :
    (collectionMatrix φ).Realize (Sum.elim (extend x n) ![c,d]) ↔
      ∀ i, leValue M (succValue M i) n → ∃ y, leValue M y c ∧
        decodeRealizes betaGraph c d i y ∧ φ.Realize (extend (extend x i) y) := by
  simp only [collectionMatrix, realize_strictAll, realize_boundedEx,
    Formula.realize_inf, realize_graphAt, realize_term_vec3, realize_formulaAtTwo,
    Term.realize_var, extend, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

theorem collection_matrix_equivalence {k : ℕ}
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit)) :
    PAEquivalent (collectionHypothesis φ) ((collectionMatrix φ).iExs (Fin 2)) := by
  apply derives_allClose_of_models
  intro M v
  rw [Formula.realize_iff, Formula.realize_iExs]
  let x : Fin k → M := fun i => v (.inl i)
  let n := v (.inr ())
  have hv : extend x n = v := by
    funext j
    cases j with
    | inl j => rfl
    | inr j => cases j; rfl
  rw [← hv, realize_collectionHypothesis]
  constructor
  · intro h
    obtain ⟨c,d,hcd⟩ := bounded_witness_collection φ x n h
    refine ⟨![c,d], (realize_collectionMatrix φ x n c d).mpr ?_⟩
    intro i hi
    refine ⟨betaValue ![c,d,i], betaValue_le c d i, ?_, ?_⟩
    · exact betaValue_graph _
    · exact hcd i hi _ (betaValue_graph _)
  · rintro ⟨cd,hcd⟩
    have hshape : cd = ![cd 0,cd 1] := by funext i; fin_cases i <;> rfl
    rw [hshape] at hcd
    have h := (realize_collectionMatrix φ x n (cd 0) (cd 1)).mp hcd
    intro i hi
    obtain ⟨y, _, _, hy⟩ := h i hi
    exact ⟨y, hy⟩

theorem collection_matrix_bounded {k : ℕ}
    {φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit)} (hφ : BoundedArithmetic φ) :
    BoundedArithmetic (collectionMatrix φ) := by
  apply BoundedArithmetic.strictAll
  apply BoundedArithmetic.ex
  have hβ : DeltaZero betaGraph := deltaZero_betaFormula _ _ _ _
  exact .imp (.imp (.core (hβ.subst _)) (.imp (hφ.subst _) (.core .falsum))) (.core .falsum)

end
end Lemmatheca.MathematicalLogic.PAComputations
