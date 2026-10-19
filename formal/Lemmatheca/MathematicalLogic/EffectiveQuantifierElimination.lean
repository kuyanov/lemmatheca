import Lemmatheca.MathematicalLogic.QuantifierEliminationShared
import Lemmatheca.MathematicalLogic.EffectiveQuantifierPrograms
import Mathlib.Computability.Partrec
import Lemmatheca.MathematicalLogic.FiniteSequenceCoding

/-! Executable finite-list elimination algorithms with shared scoped-syntax endpoints. -/

set_option backward.isDefEq.respectTransparency false

namespace Lemmatheca.MathematicalLogic.EffectiveQuantifierElimination

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.QuantifierElimination
open Lemmatheca.MathematicalLogic.QuantifierElimination.Formula

abbrev RelFormula := Lemmatheca.MathematicalLogic.QuantifierElimination.Formula

abbrev Literal (o : Bool) (n : ℕ) := Bool × Atom o n
abbrev Clause (o : Bool) (n : ℕ) := List (Literal o n)
abbrev DNF (o : Bool) (n : ℕ) := List (Clause o n)

def literalFormula {o n} (l : Literal o n) : RelFormula o n :=
  if l.1 then .atom l.2 else (QuantifierElimination.Formula.atom l.2).neg

def clauseFormula {o n} (c : Clause o n) : RelFormula o n :=
  andList (c.map literalFormula)

def dnfFormula {o n} (d : DNF o n) : RelFormula o n :=
  orList (d.map clauseFormula)

def cross {α : Type*} (xs ys : List (List α)) : List (List α) :=
  xs.flatMap fun x => ys.map fun y => x ++ y

/-- Quantifier input is an unused default; the caller supplies a QF formula. -/
def normalForm {o} : {n : ℕ} → RelFormula o n → Bool → DNF o n
  | _, .bot, true => []
  | _, .bot, false => [ [] ]
  | _, .atom a, b => [ [(b, a)] ]
  | _, .imp φ ψ, true => normalForm φ false ++ normalForm ψ true
  | _, .imp φ ψ, false => cross (normalForm φ true) (normalForm ψ false)
  | _, .ex _, _ => []

def oldIndex {n} (i : Fin (n + 1)) : Option (Fin n) :=
  if h : i.val < n then some ⟨i.val, h⟩ else none

def replaceIndex {n} (w : Fin n) (i : Fin (n + 1)) : Fin n :=
  (oldIndex i).getD w

def mapAtom {o n m} (f : Fin n → Fin m) : Atom o n → Atom o m
  | .inl (i, j) => .inl (f i, f j)
  | .inr (r, i, j) => .inr (r, f i, f j)

def fixedAtom {o n} : Atom o (n + 1) → Option (Fin n)
  | .inl (i, j) =>
    match oldIndex i, oldIndex j with
    | none, some j => some j
    | some i, none => some i
    | _, _ => none
  | .inr _ => none

def fixedLiteral {o n} (l : Literal o (n + 1)) : Option (Fin n) :=
  if l.1 then fixedAtom l.2 else none

def substituteLiteral {o n} (w : Fin n) (l : Literal o (n + 1)) : RelFormula o n :=
  literalFormula (l.1, mapAtom (replaceIndex w) l.2)

def freshEqualityAtom {n} : Atom false (n + 1) → RelFormula false n
  | .inl (i, j) =>
    match oldIndex i, oldIndex j with
    | some i, some j => .atom (.inl (i, j))
    | none, none => .top
    | _, _ => .bot
  | .inr (r, _, _) => isEmptyElim r

def freshEqualityLiteral {n} (l : Literal false (n + 1)) : RelFormula false n :=
  if l.1 then freshEqualityAtom l.2 else (freshEqualityAtom l.2).neg

def equalityClause {n} (c : Clause false (n + 1)) : RelFormula false n :=
  match c.findSome? fixedLiteral with
  | some w => andList (c.map (substituteLiteral w))
  | none => andList (c.map freshEqualityLiteral)

def positiveLiteral {n} (l : Literal true n) : List (List (Atom true n)) :=
  match l with
  | (true, a) => [ [a] ]
  | (false, .inl (i, j)) => [ [.inr ((), i, j)], [.inr ((), j, i)] ]
  | (false, .inr (_, i, j)) => [ [.inl (i, j)], [.inr ((), j, i)] ]

def positiveClause {n} : Clause true n → List (List (Atom true n))
  | [] => [ [] ]
  | l :: c => cross (positiveLiteral l) (positiveClause c)

def independentAtom {n} : Atom true (n + 1) → RelFormula true n
  | .inl (i, j) =>
    match oldIndex i, oldIndex j with
    | some i, some j => .atom (.inl (i, j))
    | _, _ => .top
  | .inr (_, i, j) =>
    match oldIndex i, oldIndex j with
    | some i, some j => .atom (.inr ((), i, j))
    | _, _ => .top

def lowerBound {n} : Atom true (n + 1) → Option (Fin n)
  | .inr (_, i, j) =>
    match oldIndex i, oldIndex j with
    | some i, none => some i
    | _, _ => none
  | _ => none

def upperBound {n} : Atom true (n + 1) → Option (Fin n)
  | .inr (_, i, j) =>
    match oldIndex i, oldIndex j with
    | none, some j => some j
    | _, _ => none
  | _ => none

def selfStrict {n} : Atom true (n + 1) → Bool
  | .inr (_, i, j) => decide (i = Fin.last n ∧ j = Fin.last n)
  | _ => false

def orderClause {n} (c : List (Atom true (n + 1))) : RelFormula true n :=
  if c.any selfStrict then .bot else
    match c.findSome? fixedAtom with
    | some w => andList (c.map fun a => .atom (mapAtom (replaceIndex w) a))
    | none =>
      andList (c.map independentAtom ++
        (c.filterMap lowerBound).flatMap fun i =>
          (c.filterMap upperBound).map fun j => .atom (.inr ((), i, j)))

def oneExistential : {o : Bool} → {n : ℕ} → RelFormula o (n + 1) → RelFormula o n
  | false, _, φ => orList ((normalForm φ true).map equalityClause)
  | true, _, φ => orList (((normalForm φ true).flatMap positiveClause).map orderClause)

def eliminate {o : Bool} : {n : ℕ} → RelFormula o n → RelFormula o n
  | _, .bot => .bot
  | _, .atom a => .atom a
  | _, .imp φ ψ => (eliminate φ).imp (eliminate ψ)
  | _, .ex φ => oneExistential (eliminate φ)

/-- The specified executable algorithm on the shared syntax. -/
def algorithm {o n} (φ : (Shared.Lang o).BoundedFormula Empty n) :
    (Shared.Lang o).BoundedFormula Empty n :=
  Shared.toShared (eliminate (Shared.fromShared φ))

def evaluateClosed {o} : RelFormula o 0 → Bool
  | .bot => false
  | .atom (.inl (i, _)) => i.elim0
  | .atom (.inr (_, i, _)) => i.elim0
  | .imp φ ψ => !(evaluateClosed φ) || evaluateClosed ψ
  | .ex _ => false

def decideSentence {o} (φ : (Shared.Lang o).Sentence) : Bool :=
  evaluateClosed (eliminate (Shared.fromShared φ))

abbrev nodeCode := EffectiveQuantifierPrograms.node

def termCode {o n} (t : (Shared.Lang o).Term (Empty ⊕ Fin n)) : ℕ :=
  nodeCode 1 [(Shared.termIndex t).val]

/-- The existing tagged shared-syntax code, restricted to the two relational
languages. In particular, an existential is encoded by its fixed abbreviation. -/
def syntaxCode {o} : {n : ℕ} → (Shared.Lang o).BoundedFormula Empty n → ℕ
  | _, .falsum => nodeCode 3 []
  | _, .equal t u => nodeCode 4 [termCode t, termCode u]
  | _, .rel R ts => by
    cases o with
    | false => exact R.elim
    | true =>
      cases R
      exact nodeCode 5 [0, termCode (ts 0), termCode (ts 1)]
  | _, .imp φ ψ => nodeCode 6 [syntaxCode φ, syntaxCode ψ]
  | _, .all φ => nodeCode 7 [syntaxCode φ]

def readTerm {o} (n c : ℕ) : Option ((Shared.Lang o).Term (Empty ⊕ Fin n)) :=
  if c = 0 then none else
    match (c - 1).unpair.1, FiniteSequenceCoding.decode (c - 1).unpair.2 with
    | 1, [i] => if h : i < n then some (.var (.inr ⟨i, h⟩)) else none
    | _, _ => none

def readFuel {o} : ℕ → (n : ℕ) → ℕ → Option ((Shared.Lang o).BoundedFormula Empty n)
  | 0, _, _ => none
  | fuel + 1, n, c =>
    if c = 0 then none else
      match (c - 1).unpair.1, FiniteSequenceCoding.decode (c - 1).unpair.2 with
      | 3, [] => some .falsum
      | 4, [a, b] => do
        let t ← readTerm n a
        let u ← readTerm n b
        pure (.equal t u)
      | 5, [0, a, b] => by
        cases o with
        | false => exact none
        | true => exact do
          let t ← readTerm n a
          let u ← readTerm n b
          pure (.rel .rel ![t, u])
      | 6, [a, b] => do
        let φ ← readFuel fuel n a
        let ψ ← readFuel fuel n b
        pure (.imp φ ψ)
      | 7, [a] => (readFuel fuel (n + 1) a).map BoundedFormula.all
      | _, _ => none

def readSyntax {o} (n c : ℕ) : Option ((Shared.Lang o).BoundedFormula Empty n) :=
  (readFuel c n c).filter (fun φ => syntaxCode φ = c)

def codeEliminate (o : Bool) (n c : ℕ) : ℕ :=
  match readSyntax (o := o) n c with
  | none => 0
  | some φ => syntaxCode (algorithm φ)

def codeDecide (o : Bool) (c : ℕ) : Bool :=
  match readSyntax (o := o) 0 c with
  | none => false
  | some φ => decideSentence φ

universe u

@[simp] private theorem oldIndex_castSucc {n} (i : Fin n) :
    oldIndex i.castSucc = some i := by simp [oldIndex, i.isLt]

@[simp] private theorem oldIndex_last (n : ℕ) : oldIndex (Fin.last n) = none := by
  simp [oldIndex]

private theorem literal_realize {o n} {M : Type u} (r : M → M → Prop)
    (l : Literal o n) (x : Fin n → M) :
    (literalFormula l).Realize r x ↔ if l.1 then realizeAtom r l.2 x else ¬ realizeAtom r l.2 x := by
  rcases l with ⟨b,a⟩
  cases b <;> rfl

private theorem clause_realize {o n} {M : Type u} (r : M → M → Prop)
    (c : Clause o n) (x : Fin n → M) :
    (clauseFormula c).Realize r x ↔ ∀ l ∈ c, (literalFormula l).Realize r x := by
  simp only [clauseFormula, realize_andList, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

private theorem dnf_realize {o n} {M : Type u} (r : M → M → Prop)
    (d : DNF o n) (x : Fin n → M) :
    (dnfFormula d).Realize r x ↔ ∃ c ∈ d, (clauseFormula c).Realize r x := by
  simp only [dnfFormula, realize_orList, List.mem_map, exists_exists_and_eq_and]

private theorem cross_realize {o n} {M : Type u} (r : M → M → Prop)
    (a b : DNF o n) (x : Fin n → M) :
    (dnfFormula (cross a b)).Realize r x ↔
      (dnfFormula a).Realize r x ∧ (dnfFormula b).Realize r x := by
  simp only [dnf_realize]
  constructor
  · rintro ⟨c,hc,h⟩
    obtain ⟨u,hu,hv⟩ := List.mem_flatMap.mp hc
    obtain ⟨v,hv_mem,rfl⟩ := List.mem_map.mp hv
    rw [clause_realize] at h
    exact ⟨⟨u,hu,(clause_realize r u x).mpr (fun l hl => h l (List.mem_append_left _ hl))⟩,
      ⟨v,hv_mem,(clause_realize r v x).mpr (fun l hl => h l (List.mem_append_right _ hl))⟩⟩
  · rintro ⟨⟨u,hu,hh⟩,⟨v,hv,hv'⟩⟩
    refine ⟨u ++ v,List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr ⟨v,hv,rfl⟩⟩,?_⟩
    rw [clause_realize] at hh hv' ⊢
    intro l hl
    exact (List.mem_append.mp hl).elim (hh l) (hv' l)

private theorem append_realize {o n} {M : Type u} (r : M → M → Prop)
    (a b : DNF o n) (x : Fin n → M) :
    (dnfFormula (a ++ b)).Realize r x ↔
      (dnfFormula a).Realize r x ∨ (dnfFormula b).Realize r x := by
  simp only [dnf_realize, List.mem_append, or_and_right, exists_or]

private theorem literal_isQF {o n} (l : Literal o n) : (literalFormula l).IsQF := by
  rcases l with ⟨b,a⟩
  cases b
  · exact .imp (.atom a) .bot
  · exact .atom a

private theorem clause_isQF {o n} (c : Clause o n) : (clauseFormula c).IsQF := by
  apply isQF_andList
  intro φ hφ
  obtain ⟨l,_,rfl⟩ := List.mem_map.mp hφ
  exact literal_isQF l

private theorem oldIndex_spec {n} (i : Fin (n+1)) :
    (∀ j, oldIndex i = some j → i = j.castSucc) ∧
    (oldIndex i = none → i = Fin.last n) := by
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

private theorem replaceIndex_value {n} {M : Type u} (x : Fin n → M) (w : Fin n)
    (i : Fin (n+1)) : x (replaceIndex w i) = (Fin.snoc x (x w) : Fin (n+1) → M) i := by
  induction i using Fin.lastCases with
  | last => simp [replaceIndex]
  | cast i => simp [replaceIndex]

private theorem mapAtom_realize {o n m} {M : Type u} (r : M → M → Prop)
    (f : Fin n → Fin m) (a : Atom o n) (x : Fin m → M) :
    realizeAtom r (mapAtom f a) x ↔ realizeAtom r a (x ∘ f) := by
  rcases a with ⟨i,j⟩ | ⟨q,i,j⟩ <;> rfl

private theorem substituteLiteral_realize {o n} {M : Type u} (r : M → M → Prop)
    (w : Fin n) (l : Literal o (n+1)) (x : Fin n → M) :
    (substituteLiteral w l).Realize r x ↔
      (literalFormula l).Realize r (Fin.snoc x (x w)) := by
  rw [substituteLiteral, literal_realize, literal_realize]
  simp only [mapAtom_realize]
  have he : x ∘ replaceIndex w = Fin.snoc x (x w) := funext (replaceIndex_value x w)
  rw [he]

private theorem fixedLiteral_witness {o n} {M : Type u} (r : M → M → Prop)
    (l : Literal o (n+1)) (w : Fin n) (h : fixedLiteral l = some w)
    (x : Fin n → M) (a : M) (hl : (literalFormula l).Realize r (Fin.snoc x a)) :
    a = x w := by
  rcases l with ⟨b,t⟩
  cases b with
  | false => simp [fixedLiteral] at h
  | true =>
    rcases t with ⟨i,j⟩ | ⟨q,i,j⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [fixedLiteral, fixedAtom] at h
        | cast j =>
          simp [fixedLiteral, fixedAtom] at h
          subst w
          simpa [literalFormula, Realize, realizeAtom] using hl
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp [fixedLiteral, fixedAtom] at h
          subst w
          simpa [literalFormula, Realize, realizeAtom, eq_comm] using hl
        | cast j => simp [fixedLiteral, fixedAtom] at h
    · simp [fixedLiteral, fixedAtom] at h

private theorem freshEqualityLiteral_forward {n} {M : Type u}
    (l : Literal false (n+1)) (h : fixedLiteral l = none)
    (x : Fin n → M) (a : M)
    (hl : (literalFormula l).Realize noRelation (Fin.snoc x a)) :
    (freshEqualityLiteral l).Realize noRelation x := by
  rcases l with ⟨b,t⟩
  rcases t with ⟨i,j⟩ | ⟨q,i,j⟩
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => cases b <;> simp_all [freshEqualityLiteral, freshEqualityAtom, literalFormula,
          Realize, realizeAtom, top, neg]
      | cast j => cases b <;> simp_all [freshEqualityLiteral, freshEqualityAtom, fixedLiteral,
          fixedAtom, literalFormula, Realize, realizeAtom, neg]
    | cast i =>
      induction j using Fin.lastCases with
      | last => cases b <;> simp_all [freshEqualityLiteral, freshEqualityAtom, fixedLiteral,
          fixedAtom, literalFormula, Realize, realizeAtom, neg]
      | cast j => cases b <;> simpa [freshEqualityLiteral, freshEqualityAtom, literalFormula,
          Realize, realizeAtom] using hl
  · exact isEmptyElim q

private theorem freshEqualityLiteral_realize {n} {M : Type u}
    (l : Literal false (n+1)) (x : Fin n → M) (a : M) (ha : ∀ i, a ≠ x i) :
    (freshEqualityLiteral l).Realize noRelation x ↔
      (literalFormula l).Realize noRelation (Fin.snoc x a) := by
  rcases l with ⟨b,t⟩
  rcases t with ⟨i,j⟩ | ⟨q,i,j⟩
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => cases b <;> simp [freshEqualityLiteral, freshEqualityAtom, literalFormula,
          Realize, realizeAtom, top, neg]
      | cast j => cases b <;> simp [freshEqualityLiteral, freshEqualityAtom, literalFormula,
          Realize, realizeAtom, neg, ha j]
    | cast i =>
      induction j using Fin.lastCases with
      | last => cases b <;> simp [freshEqualityLiteral, freshEqualityAtom, literalFormula,
          Realize, realizeAtom, neg, Ne.symm (ha i)]
      | cast j => cases b <;> simp [freshEqualityLiteral, freshEqualityAtom, literalFormula,
          Realize, realizeAtom]
  · exact isEmptyElim q

theorem normalForm_correct {o n} {M : Type u} (r : M → M → Prop)
    (φ : RelFormula o n) (hφ : φ.IsQF) (b : Bool) (x : Fin n → M) :
    (dnfFormula (normalForm φ b)).Realize r x ↔
      if b then φ.Realize r x else ¬ φ.Realize r x := by
  classical
  induction hφ generalizing b with
  | bot => cases b <;> simp [normalForm, dnfFormula, clauseFormula, Realize]
  | atom a => cases b <;> simp [normalForm, dnfFormula, clauseFormula, literalFormula, Realize]
  | imp hφ hψ ihφ ihψ =>
    cases b
    · rw [normalForm, cross_realize, ihφ true, ihψ false]
      simp only [Bool.false_eq_true, ↓reduceIte, Realize]
      tauto
    · rw [normalForm, append_realize, ihφ false, ihψ true]
      simp only [Bool.false_eq_true, ↓reduceIte, Realize]
      tauto

theorem equalityClause_correct {n} {M : Type u} [Infinite M]
    (c : Clause false (n + 1)) (x : Fin n → M) :
    (equalityClause c).Realize noRelation x ↔
      ∃ a, (clauseFormula c).Realize noRelation (Fin.snoc x a) := by
  classical
  unfold equalityClause
  split
  · rename_i w hw
    obtain ⟨c₁,l,c₂,hc,hl,_⟩ := List.findSome?_eq_some_iff.mp hw
    have hmem : l ∈ c := by simp [hc]
    simp only [realize_andList, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, substituteLiteral_realize, clause_realize]
    constructor
    · intro h
      exact ⟨x w,h⟩
    · rintro ⟨a,ha⟩
      have he := fixedLiteral_witness noRelation l w hl x a (ha l hmem)
      simpa [he] using ha
  · rename_i hc
    have hn := List.findSome?_eq_none_iff.mp hc
    simp only [realize_andList, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, clause_realize]
    constructor
    · intro h
      obtain ⟨a,ha⟩ := (Set.finite_range x).exists_notMem
      refine ⟨a,fun l hl => ?_⟩
      apply (freshEqualityLiteral_realize l x a (fun i hi => ha ⟨i,hi.symm⟩)).mp
      exact h l hl
    · rintro ⟨a,ha⟩ l hl
      exact freshEqualityLiteral_forward l (hn l hl) x a (ha l hl)


private theorem positive_cross {n} {M : Type u} (r : M → M → Prop)
    (a b : List (List (Atom true n))) (x : Fin n → M) :
    (∃ c ∈ cross a b, ∀ t ∈ c, realizeAtom r t x) ↔
      (∃ c ∈ a, ∀ t ∈ c, realizeAtom r t x) ∧
      (∃ c ∈ b, ∀ t ∈ c, realizeAtom r t x) := by
  constructor
  · rintro ⟨c,hc,h⟩
    obtain ⟨u,hu,hv⟩ := List.mem_flatMap.mp hc
    obtain ⟨v,hv_mem,rfl⟩ := List.mem_map.mp hv
    exact ⟨⟨u,hu,fun t ht => h t (List.mem_append_left _ ht)⟩,
      ⟨v,hv_mem,fun t ht => h t (List.mem_append_right _ ht)⟩⟩
  · rintro ⟨⟨u,hu,hh⟩,⟨v,hv,hv'⟩⟩
    refine ⟨u ++ v,List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr ⟨v,hv,rfl⟩⟩,?_⟩
    intro t ht
    exact (List.mem_append.mp ht).elim (hh t) (hv' t)

private theorem positiveLiteral_correct {n} {M : Type u} [LinearOrder M]
    (l : Literal true n) (x : Fin n → M) :
    (literalFormula l).Realize (fun a b => a < b) x ↔
      ∃ c ∈ positiveLiteral l, ∀ a ∈ c, realizeAtom (fun a b => a < b) a x := by
  rcases l with ⟨b,t⟩
  cases b with
  | true => simp only [literalFormula, ↓reduceIte, Realize, positiveLiteral,
      List.mem_singleton, exists_eq_left, forall_eq]
  | false =>
    rcases t with ⟨i,j⟩ | ⟨q,i,j⟩
    · simpa only [literalFormula, Bool.false_eq_true, ↓reduceIte, realize_neg, Realize,
        realizeAtom, positiveLiteral, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false, or_and_right, exists_or, exists_eq_left, forall_eq] using
        (dlo_negated_atoms (x i) (x j)).1
    · simpa only [literalFormula, Bool.false_eq_true, ↓reduceIte, realize_neg, Realize,
        realizeAtom, positiveLiteral, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false, or_and_right, exists_or, exists_eq_left, forall_eq] using
        (dlo_negated_atoms (x i) (x j)).2

theorem positiveClause_correct {n} {M : Type u} [LinearOrder M]
    (c : Clause true n) (x : Fin n → M) :
    (clauseFormula c).Realize (fun a b => a < b) x ↔
      ∃ d ∈ positiveClause c,
        ∀ a ∈ d, realizeAtom (fun a b => a < b) a x  := by
  induction c with
  | nil => simp [clauseFormula, positiveClause]
  | cons l c ih =>
    change ((literalFormula l).conj (clauseFormula c)).Realize _ x ↔ _
    rw [realize_conj, positiveClause, positive_cross, ← ih, ← positiveLiteral_correct]


private theorem order_atom_classify {n} {M : Type u} [LinearOrder M]
    (t : Atom true (n+1)) (hf : fixedAtom t = none) (hs : selfStrict t = false)
    (x : Fin n → M) (a : M) :
    realizeAtom (fun u v => u < v) t (Fin.snoc x a) ↔
      (independentAtom t).Realize (fun u v => u < v) x ∧
      (∀ i, lowerBound t = some i → x i < a) ∧
      (∀ j, upperBound t = some j → a < x j) := by
  rcases t with ⟨i,j⟩ | ⟨q,i,j⟩
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [realizeAtom, independentAtom, lowerBound, upperBound, top, neg, Realize]
      | cast j => simp [fixedAtom] at hf
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [fixedAtom] at hf
      | cast j => simp [realizeAtom, independentAtom, lowerBound, upperBound, Realize]
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [selfStrict] at hs
      | cast j => simp [realizeAtom, independentAtom, lowerBound, upperBound, top, neg, Realize]
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [realizeAtom, independentAtom, lowerBound, upperBound, top, neg, Realize]
      | cast j => simp [realizeAtom, independentAtom, lowerBound, upperBound, Realize]

private theorem strict_self_false {n} {M : Type u} [LinearOrder M]
    (t : Atom true (n+1)) (h : selfStrict t = true) (x : Fin n → M) (a : M) :
    ¬ realizeAtom (fun u v => u < v) t (Fin.snoc x a) := by
  rcases t with ⟨i,j⟩ | ⟨q,i,j⟩
  · simp [selfStrict] at h
  · have h' : i = Fin.last n ∧ j = Fin.last n := by simpa [selfStrict] using h
    rcases h' with ⟨rfl,rfl⟩
    simp [realizeAtom]

theorem orderClause_correct {n} {M : Type u} [LinearOrder M]
    [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    (c : List (Atom true (n + 1))) (x : Fin n → M) :
    (orderClause c).Realize (fun a b => a < b) x ↔
      ∃ a, ∀ t ∈ c, realizeAtom (fun a b => a < b) t (Fin.snoc x a)  := by
  classical
  unfold orderClause
  split
  · rename_i hs
    change False ↔ _
    constructor
    · exact False.elim
    · rintro ⟨a,ha⟩
      obtain ⟨t,ht,hh⟩ := List.any_eq_true.mp hs
      exact strict_self_false t hh x a (ha t ht)
  · rename_i hs
    have hself : ∀ t ∈ c, selfStrict t = false := by
      intro t ht
      apply Bool.eq_false_iff.mpr
      intro hh
      exact hs (List.any_eq_true.mpr ⟨t,ht,hh⟩)
    split
    · rename_i w hw
      obtain ⟨c₁,t,c₂,hc,ht,_⟩ := List.findSome?_eq_some_iff.mp hw
      have hmem : t ∈ c := by simp [hc]
      simp only [realize_andList, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      have hmap (a : Atom true (n+1)) :
          realizeAtom (fun u v => u < v) (mapAtom (replaceIndex w) a) x ↔
            realizeAtom (fun u v => u < v) a (Fin.snoc x (x w)) := by
        rw [mapAtom_realize]
        exact Iff.of_eq (congrArg (realizeAtom (fun u v => u < v) a)
          (funext (replaceIndex_value x w)))
      constructor
      · intro h
        exact ⟨x w,fun a ha => (hmap a).mp (h a ha)⟩
      · rintro ⟨a,ha⟩
        have hw' : a = x w := fixedLiteral_witness (fun u v => u < v)
          (true,t) w (by simpa [fixedLiteral] using ht) x a (ha t hmem)
        intro t ht
        exact (hmap t).mpr (by simpa [hw'] using ha t ht)
    · rename_i hw
      have hfixed := List.findSome?_eq_none_iff.mp hw
      let lower : Finset M := (c.filterMap lowerBound).toFinset.image x
      let upper : Finset M := (c.filterMap upperBound).toFinset.image x
      have hlow (t : Atom true (n+1)) (ht : t ∈ c) (i : Fin n)
          (hi : lowerBound t = some i) : x i ∈ lower :=
        Finset.mem_image.mpr ⟨i,by simpa using List.mem_filterMap.mpr ⟨t,ht,hi⟩,rfl⟩
      have hupp (t : Atom true (n+1)) (ht : t ∈ c) (i : Fin n)
          (hi : upperBound t = some i) : x i ∈ upper :=
        Finset.mem_image.mpr ⟨i,by simpa using List.mem_filterMap.mpr ⟨t,ht,hi⟩,rfl⟩
      simp only [realize_andList]
      constructor
      · intro h
        have hcross : ∀ a ∈ lower, ∀ b ∈ upper, a < b := by
          intro a ha b hb
          obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
          exact h _ (List.mem_append_right _ (List.mem_flatMap.mpr
            ⟨i,by simpa using hi,List.mem_map.mpr ⟨j,by simpa using hj,rfl⟩⟩))
        obtain ⟨a,ha,hb⟩ := finite_bounds lower upper hcross
        refine ⟨a,fun t ht => (order_atom_classify t (hfixed t ht) (hself t ht) x a).mpr ?_⟩
        exact ⟨h _ (List.mem_append_left _ (List.mem_map.mpr ⟨t,ht,rfl⟩)),
          fun i hi => ha _ (hlow t ht i hi),fun j hj => hb _ (hupp t ht j hj)⟩
      · rintro ⟨a,ha⟩ φ hφ
        rcases List.mem_append.mp hφ with hi | hc
        · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
          exact ((order_atom_classify t (hfixed t ht) (hself t ht) x a).mp (ha t ht)).1
        · obtain ⟨i,hi,hj⟩ := List.mem_flatMap.mp hc
          obtain ⟨j,hj_mem,rfl⟩ := List.mem_map.mp hj
          obtain ⟨t,ht,hi⟩ := List.mem_filterMap.mp hi
          obtain ⟨u,hu,hj⟩ := List.mem_filterMap.mp hj_mem
          exact (((order_atom_classify t (hfixed t ht) (hself t ht) x a).mp
            (ha t ht)).2.1 i hi).trans
              (((order_atom_classify u (hfixed u hu) (hself u hu) x a).mp
                (ha u hu)).2.2 j hj)


private theorem freshEqualityAtom_isQF {n} (a : Atom false (n+1)) :
    (freshEqualityAtom a).IsQF := by
  rcases a with ⟨i,j⟩ | ⟨q,i,j⟩
  · cases hi : oldIndex i <;> cases hj : oldIndex j <;>
      simp only [freshEqualityAtom, hi, hj] <;>
        first | exact .atom _ | exact .bot | exact .imp .bot .bot
  · exact isEmptyElim q

private theorem equalityClause_isQF {n} (c : Clause false (n+1)) :
    (equalityClause c).IsQF := by
  unfold equalityClause
  split
  · apply isQF_andList
    intro φ hφ
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hφ
    exact literal_isQF _
  · apply isQF_andList
    intro φ hφ
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hφ
    unfold freshEqualityLiteral
    split
    · exact freshEqualityAtom_isQF _
    · exact .imp (freshEqualityAtom_isQF _) .bot

private theorem independentAtom_isQF {n} (a : Atom true (n+1)) :
    (independentAtom a).IsQF := by
  rcases a with ⟨i,j⟩ | ⟨q,i,j⟩
  all_goals cases hi : oldIndex i <;> cases hj : oldIndex j <;>
    simp only [independentAtom, hi, hj] <;> first | exact .atom _ | exact .imp .bot .bot

private theorem orderClause_isQF {n} (c : List (Atom true (n+1))) :
    (orderClause c).IsQF := by
  unfold orderClause
  split
  · exact .bot
  · split
    · apply isQF_andList
      intro φ hφ
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hφ
      exact .atom _
    · apply isQF_andList
      intro φ hφ
      rcases List.mem_append.mp hφ with hi | hc
      · obtain ⟨t,_,rfl⟩ := List.mem_map.mp hi
        exact independentAtom_isQF t
      · obtain ⟨i,_,hj⟩ := List.mem_flatMap.mp hc
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hj
        exact .atom _

private theorem oneExistential_isQF {o n} (φ : RelFormula o (n+1)) :
    (oneExistential φ).IsQF := by
  cases o
  · apply isQF_orList
    intro ψ hψ
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hψ
    exact equalityClause_isQF c
  · apply isQF_orList
    intro ψ hψ
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hψ
    exact orderClause_isQF c

theorem eliminate_isQF {o n} (φ : RelFormula o n) : (eliminate φ).IsQF := by
  induction φ with
  | bot => exact .bot
  | atom a => exact .atom a
  | imp φ ψ ihφ ihψ => exact .imp ihφ ihψ
  | ex φ _ => exact oneExistential_isQF _


theorem equality_eliminate_correct {n} {M : Type u} [Infinite M]
    (φ : RelFormula false n) (x : Fin n → M) :
    (eliminate φ).Realize noRelation x ↔ φ.Realize noRelation x := by
  induction φ with
  | bot => rfl
  | atom a => rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ x) (ihψ x)
  | ex φ ih =>
    simp only [eliminate, oneExistential, realize_orList, List.mem_map,
      exists_exists_and_eq_and, equalityClause_correct, Realize]
    constructor
    · rintro ⟨c,hc,a,ha⟩
      refine ⟨a,(ih _).mp ?_⟩
      exact (normalForm_correct noRelation _ (eliminate_isQF φ) true _).mp
        ((dnf_realize noRelation _ _).mpr ⟨c,hc,ha⟩)
    · rintro ⟨a,ha⟩
      have hh := (normalForm_correct noRelation _ (eliminate_isQF φ) true _).mpr
        ((ih _).mpr ha)
      obtain ⟨c,hc,hc'⟩ := (dnf_realize noRelation _ _).mp hh
      exact ⟨c,hc,a,hc'⟩


theorem order_eliminate_correct {n} {M : Type u} [LinearOrder M]
    [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    (φ : RelFormula true n) (x : Fin n → M) :
    (eliminate φ).Realize (fun a b => a < b) x ↔
      φ.Realize (fun a b => a < b) x := by
  induction φ with
  | bot => rfl
  | atom a => rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ x) (ihψ x)
  | ex φ ih =>
    simp only [eliminate, oneExistential, realize_orList, List.mem_map,
      exists_exists_and_eq_and, orderClause_correct, Realize]
    constructor
    · rintro ⟨d,hd,a,ha⟩
      obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp hd
      refine ⟨a,(ih _).mp ?_⟩
      apply (normalForm_correct (fun a b => a < b) _ (eliminate_isQF φ) true _).mp
      apply (dnf_realize _ _ _).mpr
      exact ⟨c,hc,(positiveClause_correct c _).mpr ⟨d,hd,ha⟩⟩
    · rintro ⟨a,ha⟩
      have hh := (normalForm_correct (fun a b => a < b) _ (eliminate_isQF φ) true _).mpr
        ((ih _).mpr ha)
      obtain ⟨c,hc,hc'⟩ := (dnf_realize _ _ _).mp hh
      obtain ⟨d,hd,hd'⟩ := (positiveClause_correct c _).mp hc'
      exact ⟨d,List.mem_flatMap.mpr ⟨c,hc,hd⟩,a,hd'⟩


theorem algorithm_isQF {o n} (φ : (Shared.Lang o).BoundedFormula Empty n) :
    (algorithm φ).IsQF := by
  exact Shared.toShared_isQF (eliminate_isQF _)


theorem equality_algorithm_correct {n}
    (φ : Language.empty.BoundedFormula Empty n) :
    Language.empty.infiniteTheory.Iff φ (algorithm (o := false) φ) := by
  intro M v xs
  have : Infinite M := Language.empty.model_infiniteTheory_iff.mp M.is_model
  have hv : v = Empty.elim := Subsingleton.elim _ _
  subst v
  rw [BoundedFormula.realize_iff]
  exact (Shared.fromShared_realize (o := false) φ xs).symm.trans
    ((equality_eliminate_correct _ xs).symm.trans
      (Shared.toShared_realize (o := false) _ xs).symm)


theorem order_algorithm_correct {n}
    (φ : binaryRelLanguage.BoundedFormula Empty n) :
    Shared.strictDloTheory.Iff φ (algorithm (o := true) φ) := by
  classical
  intro M v xs
  have h := Shared.model_strictDloTheory_iff.mp M.is_model
  let r := Shared.relation (o := true) (M := M)
  let : IsStrictTotalOrder M r :=
    { irrefl := h.irrefl, trans := h.trans,
      trichotomous := fun a b hab hba => ((h.total a b).resolve_left hab).resolve_right hba }
  let : LinearOrder M := linearOrderOfSTO r
  let : DenselyOrdered M := ⟨h.dense⟩
  let : NoMinOrder M := ⟨h.noMin⟩
  let : NoMaxOrder M := ⟨h.noMax⟩
  have hv : v = Empty.elim := Subsingleton.elim _ _
  subst v
  rw [BoundedFormula.realize_iff]
  exact (Shared.fromShared_realize (o := true) φ xs).symm.trans
    ((order_eliminate_correct _ xs).symm.trans
      (Shared.toShared_realize (o := true) _ xs).symm)


private theorem closedValue_correct {o} {M : Type u} (r : M → M → Prop)
    (φ : RelFormula o 0) (h : φ.IsQF) :
    evaluateClosed φ = true ↔ φ.Realize r Fin.elim0 := by
  cases φ with
  | bot => simp [evaluateClosed, Realize]
  | atom a => rcases a with ⟨i,j⟩ | ⟨q,i,j⟩ <;> exact Fin.elim0 i
  | imp φ ψ =>
    cases h with
    | imp hφ hψ =>
      have hp := closedValue_correct r φ hφ
      have hq := closedValue_correct r ψ hψ
      cases heφ : evaluateClosed φ <;> cases heψ : evaluateClosed ψ <;>
        simp_all [evaluateClosed, Realize]
  | ex φ => cases h
termination_by φ

theorem equality_sentence_decision (φ : Language.empty.Sentence) :
    decideSentence (o := false) φ = true ↔ Language.empty.infiniteTheory ⊨ᵇ φ := by
  let : Language.empty.Structure ℕ := Language.emptyStructure
  have h₁ := closedValue_correct (noRelation (M := ℕ))
    (eliminate (Shared.fromShared (o := false) φ)) (eliminate_isQF _)
  have h₂ := equality_eliminate_correct (M := ℕ) (Shared.fromShared (o := false) φ) Fin.elim0
  exact (h₁.trans (h₂.trans (Shared.fromShared_realize (o := false) φ Fin.elim0))).trans
    (by simpa only [Sentence.Realize, Language.Formula.Realize, Unique.eq_default] using
      Shared.equality_isComplete.realize_sentence_iff φ ℕ)


theorem order_sentence_decision (φ : binaryRelLanguage.Sentence) :
    decideSentence (o := true) φ = true ↔ Shared.strictDloTheory ⊨ᵇ φ := by
  let : binaryRelLanguage.Structure ℚ := FirstOrderSemantics.binaryRelStructure ℚ (fun a b => a < b)
  let : ℚ ⊨ Shared.strictDloTheory := Shared.model_strictDloTheory
  have h₁ := closedValue_correct (fun a b : ℚ => a < b)
    (eliminate (Shared.fromShared (o := true) φ)) (eliminate_isQF _)
  have h₂ := order_eliminate_correct (M := ℚ) (Shared.fromShared (o := true) φ) Fin.elim0
  exact (h₁.trans (h₂.trans (Shared.fromShared_realize (o := true) φ Fin.elim0))).trans
    (by simpa only [Sentence.Realize, Language.Formula.Realize, Unique.eq_default] using
      Shared.strictDlo_isComplete.realize_sentence_iff φ ℚ)


private theorem nodeCode_pos (t : ℕ) (aa : List ℕ) : 0 < nodeCode t aa := by
  unfold nodeCode EffectiveQuantifierPrograms.node
  omega

private theorem nodeCode_tag (t : ℕ) (aa : List ℕ) : (nodeCode t aa - 1).unpair.1 = t := by
  simp [nodeCode, EffectiveQuantifierPrograms.node, Nat.add_comm]

private theorem nodeCode_args (t : ℕ) (aa : List ℕ) :
    FiniteSequenceCoding.decode (nodeCode t aa - 1).unpair.2 = aa := by
  simp [nodeCode, EffectiveQuantifierPrograms.node, Nat.add_comm]

private theorem nodeCode_child {t a : ℕ} {aa : List ℕ} (ha : a ∈ aa) :
    a < nodeCode t aa := by
  have h := FiniteSequenceCoding.member_lt_code ha
  have hp := Nat.right_le_pair t (FiniteSequenceCoding.code aa)
  unfold nodeCode EffectiveQuantifierPrograms.node
  omega

private theorem term_eq_index {o n} (t : (Shared.Lang o).Term (Empty ⊕ Fin n)) :
    t = .var (.inr (Shared.termIndex t)) := by
  cases t with
  | var i => cases i with
    | inl i => exact i.elim
    | inr i => rfl
  | func f ts => cases o <;> exact f.elim

private theorem readTerm_code {o n} (t : (Shared.Lang o).Term (Empty ⊕ Fin n)) :
    readTerm (o := o) n (termCode t) = some t := by
  cases t with
  | var i => cases i with
    | inl i => exact i.elim
    | inr i => simp [termCode, Shared.termIndex, readTerm, nodeCode, EffectiveQuantifierPrograms.node, i.isLt]
  | func f ts => cases o <;> exact f.elim

private theorem syntaxCode_pos {o n} (φ : (Shared.Lang o).BoundedFormula Empty n) :
    0 < syntaxCode φ := by
  cases φ with
  | falsum => exact nodeCode_pos _ _
  | equal t u => exact nodeCode_pos _ _
  | rel R ts => cases o with
    | false => exact R.elim
    | true => cases R; exact nodeCode_pos _ _
  | imp φ ψ => exact nodeCode_pos _ _
  | all φ => exact nodeCode_pos _ _

set_option maxHeartbeats 1200000 in
private theorem readFuel_code {o n} (φ : (Shared.Lang o).BoundedFormula Empty n)
    (fuel : ℕ) (hf : syntaxCode φ ≤ fuel) : readFuel (o := o) fuel n (syntaxCode φ) = some φ := by
  cases o <;> induction φ generalizing fuel with
  | falsum =>
    cases fuel with
    | zero => exact False.elim (Nat.not_le_of_gt (nodeCode_pos 3 []) hf)
    | succ fuel =>
      simp only [syntaxCode, readFuel]
      simp only [ite_eq_right (Nat.ne_of_gt (nodeCode_pos _ _)),nodeCode_tag,nodeCode_args]
  | equal t u =>
    cases fuel with
    | zero => exact False.elim (Nat.not_le_of_gt (nodeCode_pos _ _) hf)
    | succ fuel =>
      simp only [syntaxCode, readFuel]
      simp only [ite_eq_right (Nat.ne_of_gt (nodeCode_pos _ _)),nodeCode_tag,nodeCode_args]
      rw [readTerm_code, readTerm_code]
      rfl
  | @rel n k R ts =>
    cases R <;> cases fuel with
    | zero => exact False.elim (Nat.not_le_of_gt (nodeCode_pos _ _) hf)
    | succ fuel =>
      simp only [syntaxCode, readFuel]
      simp only [ite_eq_right (Nat.ne_of_gt (nodeCode_pos _ _)),nodeCode_tag,nodeCode_args]
      rw [readTerm_code,readTerm_code]
      have ht : ![ts 0,ts 1] = ts := by
        funext i
        fin_cases i <;> rfl
      change some (BoundedFormula.rel BinaryRelationSymbol.rel ![ts 0,ts 1]) = _
      rw [ht]
  | imp φ ψ ihφ ihψ =>
    cases fuel with
    | zero => exact False.elim (Nat.not_le_of_gt (nodeCode_pos _ _) hf)
    | succ fuel =>
      have hφ := nodeCode_child (t := 6) ((show syntaxCode φ ∈ [syntaxCode φ,syntaxCode ψ] from by simp))
      have hψ := nodeCode_child (t := 6) (List.mem_cons_of_mem (syntaxCode φ)
        (List.mem_singleton_self (syntaxCode ψ)))
      have hfφ : syntaxCode φ ≤ fuel := by change nodeCode _ _ ≤ fuel+1 at hf; omega
      have hfψ : syntaxCode ψ ≤ fuel := by change nodeCode _ _ ≤ fuel+1 at hf; omega
      simp only [syntaxCode, readFuel]
      simp only [ite_eq_right (Nat.ne_of_gt (nodeCode_pos _ _)),nodeCode_tag,nodeCode_args]
      rw [ihφ _ hfφ, ihψ _ hfψ]
      rfl
  | all φ ih =>
    cases fuel with
    | zero => exact False.elim (Nat.not_le_of_gt (nodeCode_pos _ _) hf)
    | succ fuel =>
      have hφ := nodeCode_child (t := 7) (List.mem_singleton_self (syntaxCode φ))
      have hfφ : syntaxCode φ ≤ fuel := by change nodeCode _ _ ≤ fuel+1 at hf; omega
      simp only [syntaxCode, readFuel]
      simp only [ite_eq_right (Nat.ne_of_gt (nodeCode_pos _ _)),nodeCode_tag,nodeCode_args]
      simp only [ih _ hfφ, Option.map_some]

theorem readSyntax_code {o n} (φ : (Shared.Lang o).BoundedFormula Empty n) :
    readSyntax (o := o) n (syntaxCode φ) = some φ := by
  simp only [readSyntax, readFuel_code φ _ le_rfl]
  simp

theorem readSyntax_exact {o n c} {φ : (Shared.Lang o).BoundedFormula Empty n}
    (h : readSyntax n c = some φ) : syntaxCode φ = c := by
  have hh := (Option.filter_eq_some_iff.mp h).2
  simpa using hh

namespace Prog
export Lemmatheca.MathematicalLogic.EffectiveQuantifierPrograms
  (Atom Literal Clause DNF node tag args arg bot neg top conj disj andList orList varCode
    atomCode literalCode fromAtom cross normalFuel normal fixed fixedLiteral replace freshAtom
    equalityClause positiveLiteral positiveClause independent lower upper selfStrict orderClause
    oneExistential readIndex runStep runFuel eliminate evalFuel decideCode eliminate_primitive decideCode_primitive)
end Prog

private def rawAtom {o n} : Atom o n → Prog.Atom
  | .inl (i,j) => (false,i.val,j.val)
  | .inr (_,i,j) => (true,i.val,j.val)
private def rawLiteral {o n} (l : Literal o n) : Prog.Literal := (l.1,rawAtom l.2)
private def localCode {o n} (φ : RelFormula o n) := syntaxCode (Shared.toShared φ)

@[simp] private theorem prog_tag (t : ℕ) (aa : List ℕ) : Prog.tag (nodeCode t aa) = t := by
  exact nodeCode_tag t aa
@[simp] private theorem prog_args (t : ℕ) (aa : List ℕ) : Prog.args (nodeCode t aa) = aa := by
  exact nodeCode_args t aa
@[simp] private theorem prog_arg (t : ℕ) (aa : List ℕ) (i : ℕ) :
    Prog.arg (nodeCode t aa) i = aa[i]?.getD 0 := by simp [Prog.arg]
@[simp] private theorem local_bot (o : Bool) (n : ℕ) : localCode (.bot : RelFormula o n) = Prog.bot := rfl
@[simp] private theorem local_imp {o n} (φ ψ : RelFormula o n) :
    localCode (φ.imp ψ) = Prog.node 6 [localCode φ,localCode ψ] := rfl
@[simp] private theorem local_neg {o n} (φ : RelFormula o n) : localCode φ.neg = Prog.neg (localCode φ) := rfl
@[simp] private theorem local_top {o n} : localCode (.top : RelFormula o n) = Prog.top := rfl
@[simp] private theorem local_conj {o n} (φ ψ : RelFormula o n) :
    localCode (φ.conj ψ) = Prog.conj (localCode φ) (localCode ψ) := rfl
@[simp] private theorem local_disj {o n} (φ ψ : RelFormula o n) :
    localCode (φ.disj ψ) = Prog.disj (localCode φ) (localCode ψ) := rfl
@[simp] private theorem local_atom {o n} (a : Atom o n) :
    localCode (.atom a) = Prog.atomCode (rawAtom a) := by
  cases a with
  | inl p => rfl
  | inr p => cases o with
    | false => exact isEmptyElim p.1
    | true => rcases p with ⟨⟨⟩,i,j⟩; rfl
@[simp] private theorem local_literal {o n} (l : Literal o n) :
    localCode (literalFormula l) = Prog.literalCode (rawLiteral l) := by
  rcases l with ⟨b,a⟩; cases b <;> simp [literalFormula,Prog.literalCode,rawLiteral]
@[simp] private theorem prog_andList_cons (a : ℕ) (l : List ℕ) :
    Prog.andList (a::l) = Prog.conj a (Prog.andList l) := rfl
@[simp] private theorem prog_orList_cons (a : ℕ) (l : List ℕ) :
    Prog.orList (a::l) = Prog.disj a (Prog.orList l) := rfl
@[simp] private theorem fin_value_ne {n} (i : Fin n) : i.val ≠ n := Nat.ne_of_lt i.isLt
private theorem fold_hom {α β : Type*} (F : α → β) (f : α → α → α) (g : β → β → β)
    (a : α) (b : β) (ha : F a = b) (hf : ∀ x y, F (f x y) = g (F x) (F y))
    (l : List α) : F (l.foldr f a) = (l.map F).foldr g b := by
  induction l with
  | nil => exact ha
  | cons x l ih =>
    simp only [List.foldr_cons,List.map_cons,hf,ih]
private theorem andList_fold {o n} (l : List (RelFormula o n)) :
    andList l = l.foldr QuantifierElimination.Formula.conj QuantifierElimination.Formula.top := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [andList,List.foldr_cons,ih]
private theorem prog_andList_fold (l : List ℕ) :
    Prog.andList l = l.foldr Prog.conj Prog.top := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [Prog.andList,List.foldr_cons,ih]
@[simp] private theorem local_andList {o n} (l : List (RelFormula o n)) :
    localCode (andList l) = Prog.andList (l.map localCode) := by
  rw [andList_fold,prog_andList_fold]
  exact fold_hom localCode QuantifierElimination.Formula.conj Prog.conj QuantifierElimination.Formula.top Prog.top
    local_top local_conj l
@[simp] private theorem local_orList {o n} (l : List (RelFormula o n)) :
    localCode (orList l) = Prog.orList (l.map localCode) := by
  induction l with
  | nil => exact local_bot o n
  | cons a l ih =>
    rw [orList,local_disj,List.map_cons,prog_orList_cons]
    exact congrArg (Prog.disj (localCode a)) ih

@[simp] private theorem raw_fixed {o n} (a : Atom o (n+1)) :
    Prog.fixed n (rawAtom a) = (fixedAtom a).map Fin.val := by
  cases a with
  | inl p =>
    rcases p with ⟨i,j⟩
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [rawAtom,Prog.fixed,fixedAtom,oldIndex]
  | inr p => simp [rawAtom,Prog.fixed,fixedAtom]
@[simp] private theorem raw_fixedLiteral {o n} (l : Literal o (n+1)) :
    Prog.fixedLiteral n (rawLiteral l) = (fixedLiteral l).map Fin.val := by
  rcases l with ⟨b,a⟩; cases b <;> simp [rawLiteral,Prog.fixedLiteral,fixedLiteral]
@[simp] private theorem raw_replace {o n} (w : Fin n) (a : Atom o (n+1)) :
    Prog.replace n w.val (rawAtom a) = rawAtom (mapAtom (replaceIndex w) a) := by
  cases a with
  | inl p =>
    rcases p with ⟨i,j⟩
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [rawAtom,Prog.replace,mapAtom,replaceIndex]
  | inr p =>
    rcases p with ⟨r,i,j⟩
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [rawAtom,Prog.replace,mapAtom,replaceIndex]
@[simp] private theorem raw_fresh {n} (a : Atom false (n+1)) :
    Prog.freshAtom n (rawAtom a) = localCode (freshEqualityAtom a) := by
  cases a with
  | inl p =>
    rcases p with ⟨i,j⟩
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [rawAtom,Prog.freshAtom,freshEqualityAtom]
  | inr p => exact isEmptyElim p.1

private theorem findSome_map {α β γ δ} (f : α → Option β) (g : α → γ)
    (h : γ → Option δ) (k : β → δ) (H : ∀ a,h (g a) = (f a).map k) (l : List α) :
    (l.map g).findSome? h = (l.findSome? f).map k := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,List.findSome?_cons,H,ih]; cases f a <;> rfl

@[simp] private theorem raw_equalityClause {n} (c : Clause false (n+1)) :
    Prog.equalityClause n (c.map rawLiteral) = localCode (equalityClause c) := by
  unfold Prog.equalityClause equalityClause
  rw [findSome_map fixedLiteral rawLiteral (Prog.fixedLiteral n) Fin.val raw_fixedLiteral]
  cases h : c.findSome? fixedLiteral with
  | none =>
    simp only [Option.map_none,Option.elim_none,local_andList,List.map_map]
    congr 1
    apply List.map_congr_left
    intro l hl
    rcases l with ⟨b,a⟩; cases b <;>
      simp [rawLiteral,freshEqualityLiteral,raw_fresh]
  | some w =>
    simp only [Option.map_some,Option.elim_some,local_andList,List.map_map]
    congr 1
    apply List.map_congr_left
    intro l hl
    simp [substituteLiteral,rawLiteral,← raw_replace,local_literal]
@[simp] private theorem raw_positiveLiteral {n} (l : Literal true n) :
    Prog.positiveLiteral (rawLiteral l) = (positiveLiteral l).map (List.map rawAtom) := by
  rcases l with ⟨b,a⟩
  cases b <;> cases a <;> rfl
private theorem map_cross {α β} (f : α → β) (a b : List (List α)) :
    (cross a b).map (List.map f) = Prog.cross (a.map (List.map f)) (b.map (List.map f)) := by
  simp [cross,Prog.cross,List.map_flatMap,List.map_map,List.map_append,List.flatMap_map,Function.comp_def]
@[simp] private theorem raw_positiveClause {n} (c : Clause true n) :
    Prog.positiveClause (c.map rawLiteral) = (positiveClause c).map (List.map rawAtom) := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    change Prog.cross (Prog.positiveLiteral (rawLiteral l)) (Prog.positiveClause (c.map rawLiteral)) =
      (cross (positiveLiteral l) (positiveClause c)).map (List.map rawAtom)
    rw [ih,raw_positiveLiteral,map_cross]
@[simp] private theorem raw_independent {n} (a : Atom true (n+1)) :
    Prog.independent n (rawAtom a) = localCode (independentAtom a) := by
  cases a with
  | inl p =>
    rcases p with ⟨i,j⟩
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [rawAtom,Prog.independent,independentAtom]
  | inr p =>
    rcases p with ⟨r,i,j⟩
    cases r
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [rawAtom,Prog.independent,independentAtom]
@[simp] private theorem raw_lower {n} (a : Atom true (n+1)) :
    Prog.lower n (rawAtom a) = (lowerBound a).map Fin.val := by
  cases a with
  | inl p => simp [rawAtom,Prog.lower,lowerBound]
  | inr p =>
    rcases p with ⟨r,i,j⟩
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [rawAtom,Prog.lower,lowerBound]
@[simp] private theorem raw_upper {n} (a : Atom true (n+1)) :
    Prog.upper n (rawAtom a) = (upperBound a).map Fin.val := by
  cases a with
  | inl p => simp [rawAtom,Prog.upper,upperBound]
  | inr p =>
    rcases p with ⟨r,i,j⟩
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [rawAtom,Prog.upper,upperBound]
@[simp] private theorem raw_selfStrict {n} (a : Atom true (n+1)) :
    Prog.selfStrict n (rawAtom a) = selfStrict a := by
  cases a with
  | inl p => rfl
  | inr p =>
    rcases p with ⟨r,i,j⟩
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [rawAtom,Prog.selfStrict,selfStrict]
private theorem filterMap_map {α β γ δ} (f : α → Option β) (g : α → γ)
    (h : γ → Option δ) (k : β → δ) (H : ∀ a,h (g a) = (f a).map k) (l : List α) :
    (l.map g).filterMap h = (l.filterMap f).map k := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,List.filterMap_cons,H,ih]; cases f a <;> rfl
@[simp] private theorem raw_orderClause {n} (c : List (Atom true (n+1))) :
    Prog.orderClause n (c.map rawAtom) = localCode (orderClause c) := by
  unfold Prog.orderClause orderClause
  simp only [List.any_map,Function.comp_def,raw_selfStrict]
  split
  · rfl
  · rw [findSome_map fixedAtom rawAtom (Prog.fixed n) Fin.val raw_fixed]
    cases h : c.findSome? fixedAtom with
    | some w =>
      simp only [Option.map_some,Option.elim_some,local_andList,List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      simp only [Function.comp_def,local_atom]
      exact congrArg Prog.atomCode (raw_replace w a)
    | none =>
      simp only [Option.map_none,Option.elim_none,local_andList,List.map_map,List.map_append,Function.comp_def]
      congr 1
      congr 1
      · apply List.map_congr_left; intro a ha; exact raw_independent a
      · rw [filterMap_map lowerBound rawAtom (Prog.lower n) Fin.val raw_lower,
          filterMap_map upperBound rawAtom (Prog.upper n) Fin.val raw_upper]
        simp [List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,rawAtom]

private theorem raw_normalFuel {o n} (φ : RelFormula o n) (hφ : φ.IsQF)
    (fuel : ℕ) (hf : localCode φ ≤ fuel) :
    Prog.normalFuel fuel (localCode φ) =
      ((normalForm φ true).map (List.map rawLiteral),
       (normalForm φ false).map (List.map rawLiteral)) := by
  induction hφ generalizing fuel with
  | bot =>
    cases fuel with
    | zero => exact False.elim (Nat.not_le_of_gt (syntaxCode_pos _) hf)
    | succ fuel => simp [Prog.normalFuel,localCode,Shared.toShared,syntaxCode,
        Nat.ne_of_gt (nodeCode_pos 3 []),normalForm]
  | atom a =>
    cases fuel with
    | zero => exact False.elim (Nat.not_le_of_gt (syntaxCode_pos _) hf)
    | succ fuel =>
      rw [local_atom]
      cases a with
      | inl p =>
        rcases p with ⟨i,j⟩
        simp [Prog.normalFuel,Prog.atomCode,Prog.fromAtom,Prog.varCode,
          normalForm,rawLiteral,rawAtom,Prog.node,Prog.tag,Prog.arg,Prog.args]
      | inr p =>
        cases o with
        | false => exact isEmptyElim p.1
        | true =>
          rcases p with ⟨⟨⟩,i,j⟩
          simp [Prog.normalFuel,Prog.atomCode,Prog.fromAtom,Prog.varCode,
            normalForm,rawLiteral,rawAtom,Prog.node,Prog.tag,Prog.arg,Prog.args]
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases fuel with
    | zero => exact False.elim (Nat.not_le_of_gt (syntaxCode_pos _) hf)
    | succ fuel =>
      have hp := nodeCode_child (t:=6) (show localCode φ ∈ [localCode φ,localCode ψ] by simp)
      have hq := nodeCode_child (t:=6) (show localCode ψ ∈ [localCode φ,localCode ψ] by simp)
      rw [local_imp] at hf
      change nodeCode 6 [localCode φ,localCode ψ] ≤ fuel+1 at hf
      have fp : localCode φ ≤ fuel := by omega
      have fq : localCode ψ ≤ fuel := by omega
      simp only [local_imp]
      simp only [Prog.normalFuel,Nat.ne_of_gt (nodeCode_pos _ _),↓reduceIte,
        prog_tag,prog_arg,List.getElem?_cons_zero,Option.getD_some,
        List.getElem?_cons_succ,List.getElem?_cons_zero]
      simp [ihφ _ fp,ihψ _ fq,normalForm,List.map_append,map_cross]

@[simp] private theorem raw_normal {o n} (φ : RelFormula o n) (hφ : φ.IsQF) :
    (Prog.normal (localCode φ)).1 = (normalForm φ true).map (List.map rawLiteral) := by
  exact congrArg Prod.fst (raw_normalFuel φ hφ _ le_rfl)
private theorem raw_oneExistential {o n} (φ : RelFormula o (n+1)) (hφ : φ.IsQF) :
    Prog.oneExistential o n (localCode φ) = localCode (oneExistential φ) := by
  cases o <;> simp [Prog.oneExistential,oneExistential,raw_normal φ hφ,
    List.map_map,List.map_flatMap,List.flatMap_map,Function.comp_def]
private theorem raw_readIndex {o} (n c : ℕ) :
    Prog.readIndex n c = (readTerm (o:=o) n c).map (fun t => (Shared.termIndex t).val) := by
  by_cases h0 : c = 0
  · simp [Prog.readIndex,readTerm,h0]
  · unfold readTerm
    simp only [h0,↓reduceIte]
    generalize ht : (c-1).unpair.1 = t
    generalize ha : FiniteSequenceCoding.decode (c-1).unpair.2 = aa
    cases aa with
    | nil => simp [Prog.readIndex,Prog.tag,Prog.args,Prog.arg,ht,ha]
    | cons i aa =>
      cases aa with
      | nil =>
        by_cases h1 : t = 1
        · subst t
          by_cases hi : i < n <;>
            simp [Prog.readIndex,Prog.tag,Prog.args,Prog.arg,h1,ha,h0,hi,Shared.termIndex]
        · simp [Prog.readIndex,Prog.tag,Prog.args,Prog.arg,ht,ha,h1]
      | cons j aa =>
        simp [Prog.readIndex,Prog.tag,Prog.args,Prog.arg,ht,ha]

private theorem raw_runFuel {o} (fuel n c : ℕ) :
    Prog.runFuel o fuel n c =
      (readFuel (o:=o) fuel n c).map (fun φ => (syntaxCode φ,syntaxCode (algorithm φ))) := by
  induction fuel generalizing n c with
  | zero => rfl
  | succ fuel ih =>
    by_cases h0 : c = 0
    · simp [Prog.runFuel,Prog.runStep,readFuel,h0]
    · simp only [Prog.runFuel,Prog.runStep,readFuel,h0,↓reduceIte]
      simp only [Prog.tag,Prog.args,Prog.arg]
      generalize ht : (c-1).unpair.1 = t
      generalize ha : FiniteSequenceCoding.decode (c-1).unpair.2 = aa
      have finish_imp (a b : ℕ) :
          ((Prog.runFuel o fuel n a).elim none fun a =>
            (Prog.runFuel o fuel n b).elim none fun b =>
              some (Prog.node 6 [a.1,b.1],Prog.node 6 [a.2,b.2])) =
          ((readFuel (o:=o) fuel n a).bind fun φ =>
            (readFuel fuel n b).bind fun ψ => some (.imp φ ψ)).map
              (fun φ => (syntaxCode φ,syntaxCode (algorithm φ))) := by
        rw [ih,ih]
        cases hp : readFuel (o:=o) fuel n a <;> cases hq : readFuel (o:=o) fuel n b <;> rfl
      have finish_all (a : ℕ) :
          ((Prog.runFuel o fuel (n+1) a).elim none fun a =>
            some (Prog.node 7 [a.1],Prog.neg (Prog.oneExistential o n (Prog.neg a.2)))) =
          ((readFuel (o:=o) fuel (n+1) a).map BoundedFormula.all).map
              (fun φ => (syntaxCode φ,syntaxCode (algorithm φ))) := by
        rw [ih]
        cases hp : readFuel (o:=o) fuel (n+1) a with
        | none => rfl
        | some φ =>
          simp only [Option.map_some,Option.elim_some]
          congr 1
          apply Prod.ext
          · rfl
          · change Prog.neg (Prog.oneExistential o n (localCode ((eliminate (Shared.fromShared φ)).neg))) =
                Prog.neg (localCode (oneExistential ((eliminate (Shared.fromShared φ)).neg)))
            exact congrArg Prog.neg (raw_oneExistential _ (.imp (eliminate_isQF _) .bot))
      have finish_eq (a b : ℕ) :
          ((Prog.readIndex n a).elim none fun i => (Prog.readIndex n b).elim none fun j =>
            some (Prog.atomCode (false,i,j),Prog.atomCode (false,i,j))) =
          ((readTerm (o:=o) n a).bind fun t => (readTerm n b).bind fun u => some (.equal t u)).map
              (fun φ => (syntaxCode φ,syntaxCode (algorithm φ))) := by
        rw [raw_readIndex (o:=o),raw_readIndex (o:=o)]
        cases hp : readTerm (o:=o) n a <;> cases hq : readTerm (o:=o) n b <;> rfl
      have finish_rel (a b : ℕ) :
          ((Prog.readIndex n a).elim none fun i => (Prog.readIndex n b).elim none fun j =>
            some (Prog.atomCode (true,i,j),Prog.atomCode (true,i,j))) =
          ((readTerm (o:=true) n a).bind fun t => (readTerm n b).bind fun u =>
            some ((.rel BinaryRelationSymbol.rel ![t,u]) : (Shared.Lang true).BoundedFormula Empty n)).map
              (fun φ => (syntaxCode φ,syntaxCode (algorithm φ))) := by
        rw [raw_readIndex (o:=true),raw_readIndex (o:=true)]
        cases hp : readTerm (o:=true) n a <;> cases hq : readTerm (o:=true) n b <;> rfl
      by_cases ht7 : t ≤ 7
      · interval_cases t <;>
          rcases aa with _ | ⟨a,_ | ⟨b,_ | ⟨d,_ | ⟨e,aa⟩⟩⟩⟩ <;>
          simp only [List.length_cons,List.length_nil,List.isEmpty_cons,List.isEmpty_nil,
            List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,List.getElem?_nil,
            Nat.reduceAdd,Nat.reduceEqDiff,↓reduceIte,Bool.false_eq_true,
            false_and,true_and,and_false,and_true] <;> try rfl
        all_goals first
          | exact finish_eq _ _
          | exact finish_imp _ _
          | exact finish_all _
          | (cases o <;> simp_all only [Bool.false_eq_true,false_and,true_and,
                ↓reduceIte]; try rfl)
        all_goals cases a <;> simp_all only [Nat.reduceEqDiff,↓reduceIte] <;>
          rfl
      · have h3 : t ≠ 3 := by omega
        have h4 : t ≠ 4 := by omega
        have h5 : t ≠ 5 := by omega
        have h6 : t ≠ 6 := by omega
        have h7 : t ≠ 7 := by omega
        simp only [h3,h4,h5,h6,h7,false_and,and_false,↓reduceIte]
        split <;> simp_all
private theorem raw_eliminate (o : Bool) (n c : ℕ) :
    Prog.eliminate o n c = codeEliminate o n c := by
  unfold Prog.eliminate codeEliminate readSyntax
  rw [raw_runFuel]
  cases h : readFuel (o:=o) c n c with
  | none => rfl
  | some φ =>
    simp only [Option.map_some,Option.elim_some]
    by_cases hc : syntaxCode φ = c <;> simp [Option.filter,hc]

private theorem raw_evalFuel {o} (φ : RelFormula o 0) (hφ : φ.IsQF)
    (fuel : ℕ) (hf : localCode φ ≤ fuel) : Prog.evalFuel fuel (localCode φ) = evaluateClosed φ := by
  induction hφ generalizing fuel with
  | bot => cases fuel <;> simp [Prog.evalFuel,localCode,Shared.toShared,syntaxCode,evaluateClosed]
  | atom a =>
    cases a with
    | inl p => exact p.1.elim0
    | inr p => exact p.2.1.elim0
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases fuel with
    | zero => exact False.elim (Nat.not_le_of_gt (syntaxCode_pos _) hf)
    | succ fuel =>
      have hp := nodeCode_child (t:=6) (show localCode φ ∈ [localCode φ,localCode ψ] by simp)
      have hq := nodeCode_child (t:=6) (show localCode ψ ∈ [localCode φ,localCode ψ] by simp)
      rw [local_imp] at hf
      change nodeCode 6 [localCode φ,localCode ψ] ≤ fuel+1 at hf
      have fp : localCode φ ≤ fuel := by omega
      have fq : localCode ψ ≤ fuel := by omega
      simp only [local_imp,Prog.evalFuel,prog_tag,prog_arg,↓reduceIte,
        List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,evaluateClosed]
      rw [ihφ _ fp,ihψ _ fq]

private theorem raw_decideCode (o : Bool) (c : ℕ) : Prog.decideCode o c = codeDecide o c := by
  unfold Prog.decideCode
  rw [raw_eliminate]
  cases h : readSyntax (o:=o) 0 c with
  | none => simp only [codeEliminate,codeDecide,h,Prog.evalFuel]
  | some φ =>
    simp only [codeEliminate,codeDecide,h]
    exact raw_evalFuel (eliminate (Shared.fromShared φ)) (eliminate_isQF _) _ le_rfl

theorem codeEliminate_primitive (o : Bool) : Primrec₂ (codeEliminate o) :=
  (Prog.eliminate_primitive o).of_eq (raw_eliminate o)

theorem codeEliminate_spec {o n} (φ : (Shared.Lang o).BoundedFormula Empty n) :
    codeEliminate o n (syntaxCode φ) = syntaxCode (algorithm φ) := by
  simp only [codeEliminate, readSyntax_code]


theorem codeDecide_primitive (o : Bool) : Primrec (codeDecide o) :=
  (Prog.decideCode_primitive o).of_eq (raw_decideCode o)

theorem codeDecide_invalid (o : Bool) (c : ℕ) (h : readSyntax (o := o) 0 c = none) :
    codeDecide o c = false := by
  simp only [codeDecide, h]


theorem equality_code_decision (φ : Language.empty.Sentence) :
    codeDecide false (syntaxCode (o := false) φ) = true ↔ Language.empty.infiniteTheory ⊨ᵇ φ := by
  simpa only [codeDecide, readSyntax_code] using equality_sentence_decision φ


theorem order_code_decision (φ : binaryRelLanguage.Sentence) :
    codeDecide true (syntaxCode (o := true) φ) = true ↔ Shared.strictDloTheory ⊨ᵇ φ := by
  simpa only [codeDecide, readSyntax_code] using order_sentence_decision φ


end Lemmatheca.MathematicalLogic.EffectiveQuantifierElimination
