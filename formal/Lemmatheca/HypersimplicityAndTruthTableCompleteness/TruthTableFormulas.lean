import Lemmatheca.HypersimplicityAndTruthTableCompleteness.PropositionalCodes

namespace Lemmatheca.ComputabilityTheory.HypersimplicityAndTruthTableCompleteness
open Lemmatheca.MathematicalLogic.Propositional
open StrongReductions

/-- A literal selecting one position of one finite row. -/
def rowLiteralCode (row : List ℕ) (i : ℕ) : ℕ :=
  if row[i]?.getD 0 = 1 then atomCode i else negCode (atomCode i)

def rowFormulaCode (n : ℕ) (row : List ℕ) : ℕ :=
  ((List.range n).map (rowLiteralCode row)).foldr conjCode verumCode

/-- DNF of the zero-output rows of this actual native truth-table scheme. -/
def tableFormulaCode (s : TableData) (e : ℕ) : ℕ :=
  (((binaryRows (s.bound e)).filter (fun row =>
    s.table e (FiniteSequenceCoding.code row) == 0)).map
      (rowFormulaCode (s.bound e))).foldr disjCode falsumCode

private theorem atom_primitive : Primrec atomCode :=
  Primrec.nat_mul.comp (Primrec.const 4) Primrec.id
private theorem neg_primitive : Primrec negCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.id) (Primrec.const 2)
private theorem conj_primitive : Primrec₂ conjCode :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)) (Primrec.const 3)).to₂
private theorem disj_primitive : Primrec₂ disjCode :=
  (neg_primitive.comp (conj_primitive.comp (neg_primitive.comp Primrec.fst)
    (neg_primitive.comp Primrec.snd))).to₂

private theorem row_literal_primitive : Primrec (fun p : List ℕ × ℕ => rowLiteralCode p.1 p.2) := by
  have hv := Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd) (Primrec.const 0)
  exact Primrec.ite (Primrec.eq.comp hv (Primrec.const 1))
    (atom_primitive.comp Primrec.snd) (neg_primitive.comp (atom_primitive.comp Primrec.snd))

private theorem row_formula_primitive : Primrec (fun p : ℕ × List ℕ => rowFormulaCode p.1 p.2) := by
  have hl := Primrec.list_map (Primrec.list_range.comp (Primrec.fst : Primrec (Prod.fst : ℕ × List ℕ → ℕ)))
    (row_literal_primitive.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂
  exact Primrec.list_foldr hl (Primrec.const verumCode)
    (conj_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

private theorem computable_filter {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) : Computable (fun a => (f a).filter (p a)) := by
  have hm := computable_list_map hf
    (Computable.cond (hp.comp Computable.fst Computable.snd)
      (Computable.list_cons.comp Computable.snd (Computable.const [])) (Computable.const [])).to₂
  have hj : Primrec (fun ls : List (List β) => ls.flatten) := Primrec.list_flatten
  apply (hj.to_comp.comp hm).of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons x xs ih =>
    simp only [Bool.cond_eq_ite] at ih ⊢
    cases h : p a x <;> simp [h, ih]

private theorem conjunction_code (l : List ℕ) (h : ∀ c ∈ l, validCode c = true) (v : Valuation ℕ) :
    validCode (l.foldr conjCode verumCode) = true ∧
      (Satisfies v (readFormula (l.foldr conjCode verumCode)) ↔ ∀ c ∈ l, Satisfies v (readFormula c)) := by
  induction l with
  | nil => exact ⟨valid_neg _ valid_falsum, by simp [verumCode, read_neg, read_falsum, Satisfies, eval]⟩
  | cons c l ih =>
    obtain ⟨hv, ht⟩ := ih (fun d hd => h d (by simp [hd]))
    refine ⟨valid_conj _ _ (h c (by simp)) hv, ?_⟩
    simp only [List.foldr_cons, read_conj, Satisfies, eval, Bool.and_eq_true]
    simpa only [List.mem_cons, forall_eq_or_imp, Satisfies] using and_congr Iff.rfl ht

private theorem disjunction_code (l : List ℕ) (h : ∀ c ∈ l, validCode c = true) (v : Valuation ℕ) :
    validCode (l.foldr disjCode falsumCode) = true ∧
      (Satisfies v (readFormula (l.foldr disjCode falsumCode)) ↔ ∃ c ∈ l, Satisfies v (readFormula c)) := by
  induction l with
  | nil => exact ⟨valid_falsum, by simp [read_falsum, Satisfies, eval]⟩
  | cons c l ih =>
    obtain ⟨hv, ht⟩ := ih (fun d hd => h d (by simp [hd]))
    refine ⟨valid_neg _ (valid_conj _ _ (valid_neg _ (h c (by simp))) (valid_neg _ hv)), ?_⟩
    simp only [List.foldr_cons, disjCode, read_neg, read_conj, Satisfies, eval,
      Bool.not_and, Bool.not_not, Bool.or_eq_true]
    simpa only [List.mem_cons, exists_eq_or_imp, Satisfies] using or_congr Iff.rfl ht

private theorem row_formula (n : ℕ) (row : List ℕ) (v : Valuation ℕ) :
    validCode (rowFormulaCode n row) = true ∧
      (Satisfies v (readFormula (rowFormulaCode n row)) ↔
        ∀ i < n, v i = (row[i]?.getD 0 == 1)) := by
  have hv : ∀ c ∈ (List.range n).map (rowLiteralCode row), validCode c = true := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    unfold rowLiteralCode
    split
    · exact valid_atom _
    · exact valid_neg _ (valid_atom _)
  refine ⟨(conjunction_code _ hv v).1, ?_⟩
  rw [rowFormulaCode, (conjunction_code _ hv v).2]
  simp only [List.forall_mem_map, List.mem_range]
  apply forall₂_congr
  intro i hi
  unfold rowLiteralCode
  split <;> rename_i hr
  · simp only [read_atom, Satisfies, eval, hr, beq_self_eq_true]
  · simp only [read_neg, read_atom, Satisfies, eval, Bool.not_eq_true']
    have hb : (row[i]?.getD 0 == 1) = false := beq_eq_false_iff_ne.mpr hr
    rw [hb]

theorem table_formula_computable (s : TableData) (hs : IsScheme s) :
    Computable (tableFormulaCode s) := by
  have hrows := binaryRows_primrec.to_comp.comp hs.1
  have hfilter := computable_filter hrows
    (Primrec.beq.to_comp.comp (hs.2.1.comp (Computable.fst.pair
      (Primrec.encode.to_comp.comp Computable.snd))) (Computable.const 0)).to₂
  have hmap := computable_list_map hfilter
    (row_formula_primitive.to_comp.comp ((hs.1.comp Computable.fst).pair Computable.snd)).to₂
  have hfold : Primrec (fun l : List ℕ => l.foldr disjCode falsumCode) :=
    Primrec.list_foldr Primrec.id (Primrec.const falsumCode)
      (disj_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact hfold.to_comp.comp hmap

private theorem row_formula_actual (n : ℕ) (row : List ℕ)
    (hb : IncomparableTuringDegrees.BinaryWord row) (hl : row.length = n) (A : Set ℕ) :
    Satisfies (setValuation A) (readFormula (rowFormulaCode n row)) ↔
      FiniteSequenceCoding.code row = PostsTheorem.prefixCode A n := by
  classical
  rw [(row_formula n row (setValuation A)).2]
  constructor
  · intro h
    apply congrArg FiniteSequenceCoding.code
    apply List.ext_getElem (by simpa using hl)
    intro i hi hj
    have hin : i < n := by simpa only [hl] using hi
    have he := h i hin
    rw [List.getElem?_eq_getElem hi, Option.getD_some] at he
    have hbit := hb row[i] (List.getElem_mem hi)
    simp only [List.getElem_map, List.getElem_range]
    rcases hbit with hz | ho
    · rw [hz]
      by_cases ha : i ∈ A <;> simp [setValuation, UniversalComputation.indicator, ha, hz] at he ⊢
    · rw [ho]
      by_cases ha : i ∈ A <;> simp [setValuation, UniversalComputation.indicator, ha, ho] at he ⊢
  · intro h i hi
    have hr := congrArg FiniteSequenceCoding.decode h
    simp only [FiniteSequenceCoding.decode_code] at hr
    rw [hr]
    have hn : (List.range n)[i]? = some i := by
      rw [List.getElem?_eq_getElem (by simpa using hi)]
      simp only [List.getElem_range]
    by_cases ha : i ∈ A <;>
      simp [PostsTheorem.prefixCode, hn, setValuation, UniversalComputation.indicator, ha]

theorem table_formula_correct (s : TableData) (_hs : IsScheme s) (A : Set ℕ) (e : ℕ) :
    validCode (tableFormulaCode s e) = true ∧
      (Satisfies (setValuation A) (readFormula (tableFormulaCode s e)) ↔
        s.table e (PostsTheorem.prefixCode A (s.bound e)) = 0) := by
  let rows := (binaryRows (s.bound e)).filter (fun row => s.table e (FiniteSequenceCoding.code row) == 0)
  have hv : ∀ c ∈ rows.map (rowFormulaCode (s.bound e)), validCode c = true := by
    intro c hc
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp hc
    exact (row_formula _ _ (setValuation A)).1
  refine ⟨(disjunction_code _ hv (setValuation A)).1, ?_⟩
  rw [tableFormulaCode, (disjunction_code _ hv (setValuation A)).2]
  constructor
  · rintro ⟨c, hc, hr⟩
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hrow, hzero⟩ := List.mem_filter.mp hrow
    have hzero : s.table e (FiniteSequenceCoding.code row) = 0 := beq_iff_eq.mp hzero
    obtain ⟨hb, hl⟩ := (binaryRows_spec (s.bound e)).1 row |>.mp hrow
    have heq := (row_formula_actual _ _ hb hl A).mp hr
    rwa [heq] at hzero
  · intro hz
    let row := FiniteSequenceCoding.decode (PostsTheorem.prefixCode A (s.bound e))
    have hb : IncomparableTuringDegrees.BinaryWord row := ComputableTreesAndPaths.prefix_code_valid A _
    have hl : row.length = s.bound e := (PostsTheorem.prefixCode_spec A _).1
    have heq : FiniteSequenceCoding.code row = PostsTheorem.prefixCode A (s.bound e) :=
      FiniteSequenceCoding.code_decode _
    refine ⟨rowFormulaCode (s.bound e) row, List.mem_map.mpr ⟨row, ?_, rfl⟩, ?_⟩
    · apply List.mem_filter.mpr
      refine ⟨(binaryRows_spec _).1 row |>.mpr ⟨hb, hl⟩, ?_⟩
      apply beq_iff_eq.mpr
      rwa [heq]
    · exact (row_formula_actual _ _ hb hl A).mpr heq

theorem nonhalting_formula (s : TableData) (A : Set ℕ)
    (hs : Presents s UniversalComputation.haltingDiagonal A) :
    Computable (tableFormulaCode s) ∧ (∀ e, validCode (tableFormulaCode s e) = true) ∧
      ∀ e, e ∉ UniversalComputation.haltingDiagonal ↔
        Satisfies (setValuation A) (readFormula (tableFormulaCode s e)) := by
  refine ⟨table_formula_computable s hs.1, fun e => (table_formula_correct s hs.1 A e).1, ?_⟩
  intro e
  rw [(table_formula_correct s hs.1 A e).2, hs.2 e]
  classical
  simp [UniversalComputation.indicator]
end Lemmatheca.ComputabilityTheory.HypersimplicityAndTruthTableCompleteness
