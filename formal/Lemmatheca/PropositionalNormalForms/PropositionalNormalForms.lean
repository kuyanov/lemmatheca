import Lemmatheca.PropositionalLogic.Propositional
import Mathlib.Data.List.FinRange

/-! Finite literal-list normal forms and explicit connective/gate syntax.
Empty folds give constants; singleton folds give their member. -/
namespace Lemmatheca.MathematicalLogic.Propositional
universe u
abbrev TruthFunction (n : ℕ) := (Fin n → Bool) → Bool
structure PropLiteral (α : Type u) where
  atom : α
  positive : Bool
  deriving DecidableEq
def literalFormula {α : Type u} (l : PropLiteral α) : PropFormula α :=
  if l.positive then .atom l.atom else .neg (.atom l.atom)
def finiteConj {α : Type u} : List (PropFormula α) → PropFormula α
  | [] => verum
  | [A] => A
  | A :: B :: rest => .conj A (finiteConj (B :: rest))
def finiteDisj {α : Type u} : List (PropFormula α) → PropFormula α
  | [] => .falsum
  | [A] => A
  | A :: B :: rest => .disj A (finiteDisj (B :: rest))
def termFormula {α : Type u} (l : List (PropLiteral α)) : PropFormula α :=
  finiteConj (l.map literalFormula)
def clauseFormula {α : Type u} (l : List (PropLiteral α)) : PropFormula α :=
  finiteDisj (l.map literalFormula)
def dnfFormula {α : Type u} (l : List (List (PropLiteral α))) : PropFormula α :=
  finiteDisj (l.map termFormula)
def cnfFormula {α : Type u} (l : List (List (PropLiteral α))) : PropFormula α :=
  finiteConj (l.map clauseFormula)
def IsDnf {α : Type u} (A : PropFormula α) : Prop := ∃ l, dnfFormula l = A
def IsCnf {α : Type u} (A : PropFormula α) : Prop := ∃ l, cnfFormula l = A
def Represents {α : Type u} [DecidableEq α] {n : ℕ}
    (p : Fin n → α) (f : TruthFunction n) (A : PropFormula α) : Prop :=
  (∀ a ∈ atoms A, ∃ i, p i = a) ∧ ∀ v, eval v A = f (v ∘ p)
noncomputable def normalTruthRows (n : ℕ) : List (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).toList
def rowTerm {α : Type u} {n : ℕ} (p : Fin n → α) (r : Fin n → Bool) :
    List (PropLiteral α) := (List.finRange n).map (fun i => ⟨p i, r i⟩)
def rowClause {α : Type u} {n : ℕ} (p : Fin n → α) (r : Fin n → Bool) :
    List (PropLiteral α) := (List.finRange n).map (fun i => ⟨p i, !(r i)⟩)
noncomputable def canonicalDnf {α : Type u} {n : ℕ} (p : Fin n → α) (f : TruthFunction n) :
    List (List (PropLiteral α)) := ((normalTruthRows n).filter f).map (rowTerm p)
noncomputable def canonicalCnf {α : Type u} {n : ℕ} (p : Fin n → α) (f : TruthFunction n) :
    List (List (PropLiteral α)) :=
  ((normalTruthRows n).filter (fun r => !(f r))).map (rowClause p)
theorem normalTruthRows_length (n : ℕ) : (normalTruthRows n).length = 2 ^ n := by
  simp [normalTruthRows]

theorem eval_finiteConj {α : Type u} (v : Valuation α) (l : List (PropFormula α)) :
    eval v (finiteConj l) = true ↔ ∀ A ∈ l, eval v A = true := by
  induction l with
  | nil => simp [finiteConj, verum, eval]
  | cons A rest ih =>
    cases rest with
    | nil => simp [finiteConj]
    | cons B tail => simp [finiteConj, eval, ih]
theorem eval_finiteDisj_false {α : Type u} (v : Valuation α) (l : List (PropFormula α)) :
    eval v (finiteDisj l) = false ↔ ∀ A ∈ l, eval v A = false := by
  induction l with
  | nil => simp [finiteDisj, eval]
  | cons A rest ih =>
    cases rest with
    | nil => simp [finiteDisj]
    | cons B tail => simp [finiteDisj, eval, ih]

private theorem eval_finiteDisj_true {α : Type u} (v : Valuation α)
    (l : List (PropFormula α)) :
    eval v (finiteDisj l) = true ↔ ∃ A ∈ l, eval v A = true := by
  induction l with
  | nil => simp [finiteDisj, eval]
  | cons A rest ih =>
    cases rest with
    | nil => simp [finiteDisj]
    | cons B tail => simp [finiteDisj, eval, ih]

private theorem finiteConj_support {α : Type u} [DecidableEq α]
    (l : List (PropFormula α)) (S : Finset α)
    (h : ∀ A ∈ l, atoms A ⊆ S) : atoms (finiteConj l) ⊆ S := by
  induction l with
  | nil => simp [finiteConj, verum, atoms]
  | cons A rest ih =>
    cases rest with
    | nil => exact h A (by simp)
    | cons B tail =>
      change atoms A ∪ atoms (finiteConj (B :: tail)) ⊆ S
      exact Finset.union_subset (h A (by simp))
        (ih (fun C hC => h C (by simp [hC])))

private theorem finiteDisj_support {α : Type u} [DecidableEq α]
    (l : List (PropFormula α)) (S : Finset α)
    (h : ∀ A ∈ l, atoms A ⊆ S) : atoms (finiteDisj l) ⊆ S := by
  induction l with
  | nil => simp [finiteDisj, atoms]
  | cons A rest ih =>
    cases rest with
    | nil => exact h A (by simp)
    | cons B tail =>
      change atoms A ∪ atoms (finiteDisj (B :: tail)) ⊆ S
      exact Finset.union_subset (h A (by simp))
        (ih (fun C hC => h C (by simp [hC])))

private theorem literalFormula_support {α : Type u} [DecidableEq α]
    (l : PropLiteral α) : atoms (literalFormula l) = {l.atom} := by
  cases h : l.positive <;> simp [literalFormula, atoms, h]

private theorem rowTerm_support {α : Type u} [DecidableEq α] {n : ℕ}
    (p : Fin n → α) (r : Fin n → Bool) :
    atoms (termFormula (rowTerm p r)) ⊆ Finset.univ.image p := by
  apply finiteConj_support
  intro A hA
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hA
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
  simp [literalFormula_support]

private theorem rowClause_support {α : Type u} [DecidableEq α] {n : ℕ}
    (p : Fin n → α) (r : Fin n → Bool) :
    atoms (clauseFormula (rowClause p r)) ⊆ Finset.univ.image p := by
  apply finiteDisj_support
  intro A hA
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hA
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
  simp [literalFormula_support]

theorem eval_rowTerm {α : Type u} {n : ℕ} (p : Fin n → α)
    (r : Fin n → Bool) (v : Valuation α) :
    eval v (termFormula (rowTerm p r)) = true ↔ v ∘ p = r := by
  have hl (i : Fin n) : eval v (literalFormula ⟨p i, r i⟩) = true ↔ v (p i) = r i := by
    cases hr : r i <;> cases hv : v (p i) <;> simp [literalFormula, eval, hv]
  simp [termFormula, eval_finiteConj, rowTerm, hl, funext_iff]
theorem eval_rowClause {α : Type u} {n : ℕ} (p : Fin n → α)
    (r : Fin n → Bool) (v : Valuation α) :
    eval v (clauseFormula (rowClause p r)) = false ↔ v ∘ p = r := by
  have hl (i : Fin n) : eval v (literalFormula ⟨p i, !(r i)⟩) = false ↔ v (p i) = r i := by
    cases hr : r i <;> cases hv : v (p i) <;> simp [literalFormula, eval, hv]
  simp [clauseFormula, eval_finiteDisj_false, rowClause, hl, funext_iff]
theorem canonicalDnf_represents {α : Type u} [DecidableEq α] {n : ℕ}
    (p : Fin n → α) (f : TruthFunction n) :
    Represents p f (dnfFormula (canonicalDnf p f)) := by
  constructor
  · have hs : atoms (dnfFormula (canonicalDnf p f)) ⊆ Finset.univ.image p := by
      apply finiteDisj_support
      intro A hA
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hA
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hl
      exact rowTerm_support p r
    intro a ha
    simpa using hs ha
  · intro v
    apply Bool.eq_iff_iff.mpr
    simp [dnfFormula, eval_finiteDisj_true, canonicalDnf, normalTruthRows,
      eval_rowTerm]
theorem canonicalCnf_represents {α : Type u} [DecidableEq α] {n : ℕ}
    (p : Fin n → α) (f : TruthFunction n) :
    Represents p f (cnfFormula (canonicalCnf p f)) := by
  constructor
  · have hs : atoms (cnfFormula (canonicalCnf p f)) ⊆ Finset.univ.image p := by
      apply finiteConj_support
      intro A hA
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hA
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hl
      exact rowClause_support p r
    intro a ha
    simpa using hs ha
  · intro v
    have hf : eval v (cnfFormula (canonicalCnf p f)) = false ↔ f (v ∘ p) = false := by
      change eval v (finiteConj ((canonicalCnf p f).map clauseFormula)) = false ↔ _
      simp only [Bool.eq_false_iff, ne_eq, eval_finiteConj]
      simp only [not_forall, Bool.not_eq_true]
      simp [canonicalCnf, normalTruthRows, eval_rowClause]
    cases hE : eval v (cnfFormula (canonicalCnf p f)) <;>
      cases hF : f (v ∘ p) <;> simp_all
theorem formula_normal_forms {α : Type u} [DecidableEq α] (A : PropFormula α) :
    ∃ B C, IsDnf B ∧ IsCnf C ∧ SemEquivalent A B ∧ SemEquivalent A C ∧
      atoms B ⊆ atoms A ∧ atoms C ⊆ atoms A := by
  classical
  let e := Fintype.equivFin ↥(atoms A)
  let p : Fin (Fintype.card ↥(atoms A)) → α := fun i => (e.symm i).val
  let f : TruthFunction (Fintype.card ↥(atoms A)) :=
    fun r => eval (extendRow (atoms A) (r ∘ e)) A
  let B := dnfFormula (canonicalDnf p f)
  let C := cnfFormula (canonicalCnf p f)
  have hB := canonicalDnf_represents p f
  have hC := canonicalCnf_represents p f
  have hf (v : Valuation α) : f (v ∘ p) = eval v A := by
    apply eval_congr
    intro a ha
    simp [extendRow, ha, p, Function.comp_def]
  refine ⟨B, C, ⟨canonicalDnf p f, rfl⟩, ⟨canonicalCnf p f, rfl⟩,
    (fun v => (hB.2 v).trans (hf v) |>.symm),
    (fun v => (hC.2 v).trans (hf v) |>.symm), ?_, ?_⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := hB.1 a ha
    exact (e.symm i).property
  · intro a ha
    obtain ⟨i, rfl⟩ := hC.1 a ha
    exact (e.symm i).property
theorem canonical_normal_form_lengths {α : Type u} {n : ℕ}
    (p : Fin n → α) (f : TruthFunction n) :
    (canonicalDnf p f).length ≤ 2 ^ n ∧ (canonicalCnf p f).length ≤ 2 ^ n ∧
      (∀ l ∈ canonicalDnf p f, l.length = n) ∧
      (∀ l ∈ canonicalCnf p f, l.length = n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [canonicalDnf, normalTruthRows_length] using
      List.length_filter_le f (normalTruthRows n)
  · simpa [canonicalCnf, normalTruthRows_length] using
      List.length_filter_le (fun r => !(f r)) (normalTruthRows n)
  · intro l hl
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hl
    simp [rowTerm]
  · intro l hl
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hl
    simp [rowClause]
theorem constant_normal_forms {α : Type u} :
    IsDnf (.falsum : PropFormula α) ∧ IsCnf (.falsum : PropFormula α) ∧
      IsDnf (verum : PropFormula α) ∧ IsCnf (verum : PropFormula α) := by
  exact ⟨⟨[], rfl⟩, ⟨[[]], rfl⟩, ⟨[[]], rfl⟩, ⟨[], rfl⟩⟩
theorem atomless_constant {α : Type u} [DecidableEq α] (A : PropFormula α)
    (h : atoms A = ∅) :
    SemEquivalent A .falsum ∨ SemEquivalent A verum := by
  have hv (v : Valuation α) : eval v A = eval (fun _ => false) A := by
    apply eval_congr
    simp [h]
  cases he : eval (fun _ => false) A with
  | false => exact Or.inl (fun v => (hv v).trans he)
  | true => exact Or.inr (fun v => (hv v).trans he)
theorem canonical_false_true {α : Type u} [DecidableEq α] {n : ℕ} (p : Fin n → α) :
    dnfFormula (canonicalDnf p (fun _ => false)) = .falsum ∧
      cnfFormula (canonicalCnf p (fun _ => true)) = verum ∧
      SemEquivalent (cnfFormula (canonicalCnf p (fun _ => false))) .falsum ∧
      SemEquivalent (dnfFormula (canonicalDnf p (fun _ => true))) verum := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [canonicalDnf, dnfFormula, finiteDisj]
  · simp [canonicalCnf, cnfFormula, finiteConj]
  · exact (canonicalCnf_represents p (fun _ => false)).2
  · exact (canonicalDnf_represents p (fun _ => true)).2
theorem zero_input_normal_forms {α : Type u} [DecidableEq α]
    (p : Fin 0 → α) (f : TruthFunction 0) :
    let K : PropFormula α := if f (fun i => Fin.elim0 i) then verum else .falsum
    SemEquivalent (dnfFormula (canonicalDnf p f)) K ∧
      SemEquivalent (cnfFormula (canonicalCnf p f)) K := by
  have he (v : Valuation α) : v ∘ p = (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  constructor <;> intro v
  · rw [(canonicalDnf_represents p f).2 v, he v]
    cases h : f (fun i => Fin.elim0 i) <;> simp [verum, eval]
  · rw [(canonicalCnf_represents p f).2 v, he v]
    cases h : f (fun i => Fin.elim0 i) <;> simp [verum, eval]

inductive PropBasis where
  | negOr | negAnd | negImp | impFalse
  deriving DecidableEq
def InBasis {α : Type u} (b : PropBasis) : PropFormula α → Prop
  | .atom _ | .falsum => True
  | .neg A => b ≠ .impFalse ∧ InBasis b A
  | .conj A B => b = .negAnd ∧ InBasis b A ∧ InBasis b B
  | .disj A B => b = .negOr ∧ InBasis b A ∧ InBasis b B
  | .impl A B => (b = .negImp ∨ b = .impFalse) ∧ InBasis b A ∧ InBasis b B
def toBasis {α : Type u} (b : PropBasis) : PropFormula α → PropFormula α
  | .atom a => .atom a
  | .falsum => .falsum
  | .neg A => let X := toBasis b A
              if b = .impFalse then .impl X .falsum else .neg X
  | .conj A B =>
      let X := toBasis b A; let Y := toBasis b B
      match b with
      | .negOr => .neg (.disj (.neg X) (.neg Y))
      | .negAnd => .conj X Y
      | .negImp => .neg (.impl X (.neg Y))
      | .impFalse => .impl (.impl X (.impl Y .falsum)) .falsum
  | .disj A B =>
      let X := toBasis b A; let Y := toBasis b B
      match b with
      | .negOr => .disj X Y
      | .negAnd => .neg (.conj (.neg X) (.neg Y))
      | .negImp => .impl (.neg X) Y
      | .impFalse => .impl (.impl X .falsum) Y
  | .impl A B =>
      let X := toBasis b A; let Y := toBasis b B
      match b with
      | .negOr => .disj (.neg X) Y
      | .negAnd => .neg (.conj X (.neg Y))
      | .negImp | .impFalse => .impl X Y
def BasisComplete (b : PropBasis) : Prop :=
  ∀ n (f : TruthFunction n), ∃ A : PropFormula (Fin n), InBasis b A ∧ Represents id f A
theorem toBasis_correct {α : Type u} (b : PropBasis) (A : PropFormula α) :
    InBasis b (toBasis b A) ∧ SemEquivalent (toBasis b A) A := by
  constructor
  · induction A generalizing b with
    | atom a => simp [toBasis, InBasis]
    | falsum => simp [toBasis, InBasis]
    | neg A ih => cases b <;> simp [toBasis, InBasis, ih]
    | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      cases b <;> simp [toBasis, InBasis, ihA, ihB]
  · intro v
    induction A generalizing b with
    | atom a => rfl
    | falsum => rfl
    | neg A ih => cases b <;> simp [toBasis, eval, ih]
    | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      cases b <;> simp only [toBasis, eval, ihA, ihB] <;>
        cases hA : eval v A <;> cases hB : eval v B <;> rfl
theorem standard_bases_complete (b : PropBasis) : BasisComplete b := by
  intro n f
  let A := dnfFormula (canonicalDnf (id : Fin n → Fin n) f)
  have h := toBasis_correct b A
  refine ⟨toBasis b A, h.1, (fun a _ => ⟨a, rfl⟩), ?_⟩
  intro v
  exact (h.2 v).trans ((canonicalDnf_represents id f).2 v)
inductive GateKind where
  | nand | nor
  deriving DecidableEq
inductive SingleGateFormula (α : Type u) where
  | atom : α → SingleGateFormula α
  | falsum : SingleGateFormula α
  | gate : SingleGateFormula α → SingleGateFormula α → SingleGateFormula α
  deriving DecidableEq
def gateOperation : GateKind → Bool → Bool → Bool
  | .nand, a, b => !(a && b)
  | .nor, a, b => !(a || b)
def gateEval {α : Type u} (k : GateKind) (v : Valuation α) : SingleGateFormula α → Bool
  | .atom a => v a
  | .falsum => false
  | .gate A B => gateOperation k (gateEval k v A) (gateEval k v B)
def gateNeg {α : Type u} (A : SingleGateFormula α) : SingleGateFormula α := .gate A A
def gateConj {α : Type u} (k : GateKind) (A B : SingleGateFormula α) : SingleGateFormula α :=
  match k with
  | .nand => gateNeg (.gate A B)
  | .nor => .gate (gateNeg A) (gateNeg B)
def gateDisj {α : Type u} (k : GateKind) (A B : SingleGateFormula α) : SingleGateFormula α :=
  match k with
  | .nand => .gate (gateNeg A) (gateNeg B)
  | .nor => gateNeg (.gate A B)
def toGate {α : Type u} (k : GateKind) : PropFormula α → SingleGateFormula α
  | .atom a => .atom a
  | .falsum => .falsum
  | .neg A => gateNeg (toGate k A)
  | .conj A B => gateConj k (toGate k A) (toGate k B)
  | .disj A B => gateDisj k (toGate k A) (toGate k B)
  | .impl A B => gateDisj k (gateNeg (toGate k A)) (toGate k B)
def GateNoConstants {α : Type u} : SingleGateFormula α → Prop
  | .atom _ => True
  | .falsum => False
  | .gate A B => GateNoConstants A ∧ GateNoConstants B
def gateFalse {α : Type u} (k : GateKind) (a : α) : SingleGateFormula α :=
  let p : SingleGateFormula α := .atom a
  match k with
  | .nand => let T := .gate p (gateNeg p); .gate T T
  | .nor => .gate p (gateNeg p)
def removeGateConstants {α : Type u} (k : GateKind) (a : α) :
    SingleGateFormula α → SingleGateFormula α
  | .atom b => .atom b
  | .falsum => gateFalse k a
  | .gate A B => .gate (removeGateConstants k a A) (removeGateConstants k a B)
theorem single_gate_identities {α : Type u} (k : GateKind) (v : Valuation α)
    (A B : SingleGateFormula α) :
    gateEval k v (gateNeg A) = !(gateEval k v A) ∧
      gateEval k v (gateConj k A B) = (gateEval k v A && gateEval k v B) ∧
      gateEval k v (gateDisj k A B) = (gateEval k v A || gateEval k v B) := by
  cases k with
  | nand =>
    cases hA : gateEval .nand v A <;> cases hB : gateEval .nand v B <;>
      simp [gateNeg, gateConj, gateDisj, gateEval, gateOperation, hA, hB]
  | nor =>
    cases hA : gateEval .nor v A <;> cases hB : gateEval .nor v B <;>
      simp [gateNeg, gateConj, gateDisj, gateEval, gateOperation, hA, hB]
theorem toGate_correct {α : Type u} (k : GateKind) (A : PropFormula α)
    (v : Valuation α) : gateEval k v (toGate k A) = eval v A := by
  have hn (A : SingleGateFormula α) := (single_gate_identities k v A A).1
  have hc (A B : SingleGateFormula α) := (single_gate_identities k v A B).2.1
  have hd (A B : SingleGateFormula α) := (single_gate_identities k v A B).2.2
  induction A with
  | atom a => rfl
  | falsum => rfl
  | neg A ih => simp [toGate, eval, hn, ih]
  | conj A B ihA ihB => simp [toGate, eval, hc, ihA, ihB]
  | disj A B ihA ihB => simp [toGate, eval, hd, ihA, ihB]
  | impl A B ihA ihB => simp [toGate, eval, hd, hn, ihA, ihB]
theorem gateFalse_correct {α : Type u} (k : GateKind) (a : α) (v : Valuation α) :
    GateNoConstants (gateFalse k a) ∧ gateEval k v (gateFalse k a) = false := by
  cases k <;> cases h : v a <;>
    simp [gateFalse, gateNeg, GateNoConstants, gateEval, gateOperation, h]
theorem gate_constant_witnesses {α : Type u} (a : α) (v : Valuation α) :
    let p : SingleGateFormula α := .atom a
    let T := .gate p (gateNeg p)
    gateEval .nand v T = true ∧ gateEval .nand v (.gate T T) = false ∧
      gateEval .nor v T = false ∧ gateEval .nor v (.gate T T) = true := by
  cases h : v a <;> simp [gateNeg, gateEval, gateOperation, h]

theorem gate_truth_constant {α : Type u} (k : GateKind) (v : Valuation α) :
    gateEval k v (.gate .falsum .falsum) = true := by
  cases k <;> rfl

theorem removeGateConstants_correct {α : Type u} (k : GateKind) (a : α)
    (A : SingleGateFormula α) (v : Valuation α) :
    GateNoConstants (removeGateConstants k a A) ∧
      gateEval k v (removeGateConstants k a A) = gateEval k v A := by
  induction A with
  | atom b => simp [removeGateConstants, GateNoConstants]
  | falsum => exact gateFalse_correct k a v
  | gate A B ihA ihB => simp_all [removeGateConstants, GateNoConstants, gateEval]
theorem single_gate_complete (k : GateKind) (n : ℕ) (f : TruthFunction n) :
    ∃ A : SingleGateFormula (Fin n), ∀ v, gateEval k v A = f v := by
  refine ⟨toGate k (dnfFormula (canonicalDnf id f)), ?_⟩
  intro v
  exact (toGate_correct k _ v).trans ((canonicalDnf_represents id f).2 v)
theorem single_gate_constant_free_complete (k : GateKind) (n : ℕ) (h : 0 < n)
    (f : TruthFunction n) :
    ∃ A : SingleGateFormula (Fin n), GateNoConstants A ∧
      ∀ v, gateEval k v A = f v := by
  obtain ⟨A, hA⟩ := single_gate_complete k n f
  let a : Fin n := ⟨0, h⟩
  refine ⟨removeGateConstants k a A, (removeGateConstants_correct k a A (fun _ => false)).1, ?_⟩
  intro v
  exact (removeGateConstants_correct k a A v).2.trans (hA v)
theorem no_atomless_constant_free_gate :
    ¬ ∃ A : SingleGateFormula (Fin 0), GateNoConstants A := by
  have hn (A : SingleGateFormula (Fin 0)) : ¬ GateNoConstants A := by
    induction A with
    | atom a => exact Fin.elim0 a
    | falsum => exact id
    | gate A B ihA _ihB => exact fun h => ihA h.1
  rintro ⟨A, hA⟩
  exact hn A hA
inductive PositiveFormula {α : Type u} : PropFormula α → Prop
  | atom (a : α) : PositiveFormula (.atom a)
  | falsum : PositiveFormula .falsum
  | verum : PositiveFormula verum
  | conj {A B} : PositiveFormula A → PositiveFormula B → PositiveFormula (.conj A B)
  | disj {A B} : PositiveFormula A → PositiveFormula B → PositiveFormula (.disj A B)
def MonotoneTruth {α : Type u} (A : PropFormula α) : Prop :=
  ∀ v w : Valuation α, (∀ a, v a ≤ w a) → eval v A ≤ eval w A
theorem positiveFormula_monotone {α : Type u} (A : PropFormula α)
    (h : PositiveFormula A) : MonotoneTruth A := by
  induction h with
  | atom a => exact fun v w h => h a
  | falsum => exact fun _ _ _ => le_rfl
  | verum => exact fun _ _ _ => le_rfl
  | @conj A B hA hB ihA ihB | @disj A B hA hB ihA ihB =>
    intro v w hvw
    have h1 := ihA v w hvw
    have h2 := ihB v w hvw
    cases hx : eval v A <;> cases hy : eval w A <;>
      cases hz : eval v B <;> cases ht : eval w B <;> simp_all [eval]
theorem positive_basis_not_complete :
    ¬ ∃ A : PropFormula (Fin 1), PositiveFormula A ∧
      ∀ v, eval v A = !(v 0) := by
  rintro ⟨A, h, he⟩
  have hm := positiveFormula_monotone A h (fun _ => false) (fun _ => true)
    (fun _ => Bool.false_le true)
  rw [he, he] at hm
  exact (by decide : ¬ ((true : Bool) ≤ false)) hm
end Lemmatheca.MathematicalLogic.Propositional
