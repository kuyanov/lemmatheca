import Lemmatheca.HerbrandModels.HerbrandModels
import Mathlib.ModelTheory.Quotients

/-! Equality elimination in the actual shared syntax, with a fixed fresh binary
relation, congruence quotient, and actual signed-clause representation. -/
namespace Lemmatheca.MathematicalLogic.EqualityAxioms

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.Propositional
open HerbrandModels

universe u v w z
variable {L : Language.{u, v}} {α : Type w}

/-- One new relation, at arity two only. -/
inductive EqualitySymbol : ℕ → Type
  | equality : EqualitySymbol 2

/-- Old functions and disjoint old/new relation symbols. Chosen from L alone. -/
def Extended (L : Language.{u, v}) : Language.{u, v} where
  Functions := L.Functions
  Relations n := L.Relations n ⊕ EqualitySymbol n

def inclusion (L : Language.{u, v}) : L →ᴸ Extended L where
  onFunction := fun _ f => f
  onRelation := fun _ R => Sum.inl R

abbrev termTranslate (t : L.Term α) : (Extended L).Term α := (inclusion L).onTerm t

/-- A restriction on the actual scoped formula type, allowing quantifiers. -/
def EqualityFree : {n : ℕ} → (Extended L).BoundedFormula α n → Prop
  | _, .falsum => True
  | _, .equal _ _ => False
  | _, .rel _ _ => True
  | _, .imp A B => EqualityFree A ∧ EqualityFree B
  | _, .all A => EqualityFree A

/-- Replace logical equality, preserving the actual free names and bound slots. -/
def translate : {n : ℕ} → L.BoundedFormula α n → (Extended L).BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal s t => .rel (.inr .equality) ![termTranslate s, termTranslate t]
  | _, .rel R ts => .rel (.inl R) (fun i => termTranslate (ts i))
  | _, .imp A B => .imp (translate A) (translate B)
  | _, .all A => .all (translate A)

theorem translate_equalityFree {n : ℕ} (A : L.BoundedFormula α n) :
    EqualityFree (translate A) := by
  induction A with
  | falsum => trivial
  | equal => trivial
  | rel => trivial
  | imp A B ihA ihB => exact ⟨ihA, ihB⟩
  | all A ih => exact ih

/-- Interpretation of the fresh relation on an expanded carrier. -/
def E {N : Type z} [(Extended L).Structure N] (a b : N) : Prop :=
  Structure.RelMap (L := Extended L) (.inr .equality) ![a, b]

/-- The five semantic schemes; old-relation invariance includes both directions,
which are equivalent to the one-way clause scheme in the presence of symmetry. -/
structure Axioms (L : Language.{u, v}) (N : Type z) [(Extended L).Structure N] : Prop where
  reflexive : ∀ a : N, E (L := L) a a
  symmetric : ∀ {a b : N}, E (L := L) a b → E (L := L) b a
  transitive : ∀ {a b c : N}, E (L := L) a b → E (L := L) b c → E (L := L) a c
  functions : ∀ {n} (f : L.Functions n) (a b : Fin n → N),
    (∀ i, E (L := L) (a i) (b i)) → E (L := L) (Structure.funMap (L := Extended L) f a)
      (Structure.funMap (L := Extended L) f b)
  relations : ∀ {n} (R : L.Relations n) (a b : Fin n → N),
    (∀ i, E (L := L) (a i) (b i)) →
      (Structure.RelMap (L := Extended L) (.inl R) a ↔
        Structure.RelMap (L := Extended L) (.inl R) b)

theorem e_congr {N : Type z} [(Extended L).Structure N] (h : Axioms L N)
    {a a' b b' : N} (ha : E (L := L) a a') (hb : E (L := L) b b') : E (L := L) a b ↔ E (L := L) a' b' := by
  constructor
  · intro hab
    exact h.transitive (h.symmetric ha) (h.transitive hab hb)
  · intro hab
    exact h.transitive ha (h.transitive hab (h.symmetric hb))

/-- Interpret E as identity on the original nonempty carrier. -/
@[instance_reducible] def identityExpansion (M : Type z) [L.Structure M] : (Extended L).Structure M where
  funMap f a := Structure.funMap (L := L) f a
  RelMap R a := match R with
    | .inl R => Structure.RelMap (L := L) R a
    | .inr .equality => a 0 = a 1

theorem identity_axioms (M : Type z) [L.Structure M] :
    letI := identityExpansion (L := L) M
    Axioms L M := by
  let := identityExpansion (L := L) M
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro a b hab
    exact Eq.symm hab
  · intro a b c hab hbc
    exact Eq.trans hab hbc
  · intro n f a b hab
    have hab' : a = b := funext fun i => hab i
    subst b
    rfl
  · intro n R a b hab
    have hab' : a = b := funext fun i => hab i
    subst b
    exact Iff.rfl

theorem identity_term (M : Type z) [L.Structure M] (t : L.Term α) (u : α → M) :
    @Term.realize (Extended L) M (identityExpansion (L := L) M) α u (termTranslate t) =
      t.realize u := by
  induction t with
  | var => rfl
  | func f ts ih =>
      change (Structure.funMap (L := L) f fun i =>
        @Term.realize (Extended L) M (identityExpansion (L := L) M) _ u
          (termTranslate (ts i))) = _
      congr 1
      funext i
      exact ih i

theorem identity_truth (M : Type z) [L.Structure M] {n : ℕ}
    (A : L.BoundedFormula α n) (v : α → M) (w : Fin n → M) :
    @BoundedFormula.Realize (Extended L) M (identityExpansion (L := L) M) α n (translate A) v w ↔
      A.Realize v w := by
  induction A generalizing v with
  | falsum => rfl
  | equal s t =>
      change @Term.realize (Extended L) M (identityExpansion (L := L) M) _ (Sum.elim v w)
          (termTranslate s) =
        @Term.realize (Extended L) M (identityExpansion (L := L) M) _ (Sum.elim v w)
          (termTranslate t) ↔ _
      rw [identity_term, identity_term]
      rfl
  | rel R ts =>
      change (Structure.RelMap (L := L) R fun i =>
        @Term.realize (Extended L) M (identityExpansion (L := L) M) _ (Sum.elim v w)
          (termTranslate (ts i))) ↔ _
      simp only [identity_term]
      rfl
  | imp A B ihA ihB =>
      exact imp_congr (ihA v w) (ihB v w)
  | all A ih =>
      exact forall_congr' fun a => ih v (Fin.snoc w a)

/-- The old-language reduct of an expanded structure. -/
@[instance_reducible] def reduct (N : Type z) [(Extended L).Structure N] : L.Structure N where
  funMap f a := Structure.funMap (L := Extended L) f a
  RelMap R a := Structure.RelMap (L := Extended L) (.inl R) a

/-- The equivalence relation to be collapsed. -/
def equivalence {N : Type z} [(Extended L).Structure N] (h : Axioms L N) : Setoid N where
  r := E (L := L)
  iseqv := ⟨h.reflexive, h.symmetric, h.transitive⟩

/-- Explicit compatibility bridge to the library's quotient representation. -/
@[instance_reducible] def prestructure {N : Type z} [(Extended L).Structure N] (h : Axioms L N) :
    L.Prestructure (equivalence h) where
  toStructure := reduct N
  fun_equiv a b hab := h.functions _ a b hab
  rel_equiv a b hab := propext (h.relations _ a b hab)

abbrev QuotientModel {N : Type z} [(Extended L).Structure N] (h : Axioms L N) :=
  Quotient (equivalence h)

noncomputable instance quotientStructure {N : Type z} [(Extended L).Structure N]
    (h : Axioms L N) : L.Structure (QuotientModel h) :=
  @FirstOrder.Language.quotientStructure L N (equivalence h) (prestructure h)

def projection {N : Type z} [(Extended L).Structure N] (h : Axioms L N) : N → QuotientModel h :=
  Quotient.mk (equivalence h)

theorem quotient_nonempty {N : Type z} [(Extended L).Structure N] [Nonempty N]
    (h : Axioms L N) : Nonempty (QuotientModel h) := by
  exact ⟨projection h (Classical.choice inferInstance)⟩

theorem quotient_function {N : Type z} [(Extended L).Structure N] (h : Axioms L N)
    {n} (f : L.Functions n) (a : Fin n → N) :
    Structure.funMap (L := L) f (projection h ∘ a) =
      projection h (Structure.funMap (L := Extended L) f a) := by
  exact @FirstOrder.Language.funMap_quotient_mk' L N (equivalence h) (prestructure h) _ f a

theorem quotient_relation {N : Type z} [(Extended L).Structure N] (h : Axioms L N)
    {n} (R : L.Relations n) (a : Fin n → N) :
    Structure.RelMap (L := L) R (projection h ∘ a) ↔
      Structure.RelMap (L := Extended L) (.inl R) a := by
  exact @FirstOrder.Language.relMap_quotient_mk' L N (equivalence h) (prestructure h) _ R a

theorem term_projection {N : Type z} [(Extended L).Structure N] (h : Axioms L N)
    (t : L.Term α) (a : α → N) :
    t.realize (projection h ∘ a) = projection h ((termTranslate t).realize a) := by
  induction t with
  | var => rfl
  | func f ts ih =>
      change Structure.funMap (L := L) f (fun i => (ts i).realize (projection h ∘ a)) =
        projection h (Structure.funMap (L := Extended L) f
          (fun i => (termTranslate (ts i)).realize a))
      simp_rw [ih]
      exact quotient_function h f (fun i => (termTranslate (ts i)).realize a)

private theorem realize_pair {N : Type z} [(Extended L).Structure N]
    (s t : (Extended L).Term α) (v : α → N) :
    (fun i : Fin 2 => (![s, t] i).realize v) = ![s.realize v, t.realize v] := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) i <;> rfl

/-- Full scoped truth, including quantifiers and arbitrary protected slots. -/
theorem quotient_truth {N : Type z} [(Extended L).Structure N] (h : Axioms L N)
    {n : ℕ} (A : L.BoundedFormula α n) (v : α → N) (w : Fin n → N) :
    A.Realize (projection h ∘ v) (projection h ∘ w) ↔ (translate A).Realize v w := by
  induction A generalizing v with
  | falsum => rfl
  | equal s t =>
      simp only [translate, BoundedFormula.Realize, realize_pair]
      have hv : Sum.elim (projection h ∘ v) (projection h ∘ w) =
          projection h ∘ Sum.elim v w := by
        funext x
        cases x <;> rfl
      rw [hv, term_projection, term_projection]
      exact Quotient.eq
  | rel R ts =>
      simp only [translate, BoundedFormula.Realize]
      have hv : Sum.elim (projection h ∘ v) (projection h ∘ w) =
          projection h ∘ Sum.elim v w := by
        funext x
        cases x <;> rfl
      simp only [hv, term_projection]
      exact quotient_relation h R (fun i => (termTranslate (ts i)).realize (Sum.elim v w))
  | imp A B ihA ihB =>
      exact imp_congr (ihA v w) (ihB v w)
  | all A ih =>
      change (∀ b, A.Realize (projection h ∘ v) (Fin.snoc (projection h ∘ w) b)) ↔
        ∀ a, (translate A).Realize v (Fin.snoc w a)
      constructor
      · intro hall a
        apply (ih v (Fin.snoc w a)).mp
        simpa only [Fin.comp_snoc] using hall (projection h a)
      · intro hall b
        obtain ⟨a, rfl⟩ := (Quotient.mk_surjective (s := equivalence h)) b
        have hb := (ih v (Fin.snoc w a)).mpr (hall a)
        simpa only [Fin.comp_snoc, projection] using hb

/-! Concrete equality axiom clauses use the already shared signed representation. -/
noncomputable section

local instance {δ : Type*} : DecidableEq δ := Classical.decEq _

def eqAtom (s t : (Extended L).Term α) : Atom (Extended L) α :=
  ⟨2, .inr .equality, ![s, t]⟩

def oldAtom {n} (R : L.Relations n) (ts : Fin n → (Extended L).Term α) :
    Atom (Extended L) α := ⟨n, .inl R, ts⟩

def positive (a : Atom (Extended L) α) : FOLiteral (Extended L) α := ⟨a, true⟩
def negative (a : Atom (Extended L) α) : FOLiteral (Extended L) α := ⟨a, false⟩

def reflClause (L : Language.{u, v}) : FOClause (Extended L) ℕ :=
  {positive (eqAtom (.var 0) (.var 0))}

def symmClause (L : Language.{u, v}) : FOClause (Extended L) ℕ :=
  {negative (eqAtom (.var 0) (.var 1)), positive (eqAtom (.var 1) (.var 0))}

def transClause (L : Language.{u, v}) : FOClause (Extended L) ℕ :=
  {negative (eqAtom (.var 0) (.var 1)), negative (eqAtom (.var 1) (.var 2)),
    positive (eqAtom (.var 0) (.var 2))}

def leftVariables {n : ℕ} : Fin n → (Extended L).Term ℕ := fun i => .var (2 * i.val)
def rightVariables {n : ℕ} : Fin n → (Extended L).Term ℕ := fun i => .var (2 * i.val + 1)

def negativePairs (L : Language.{u, v}) (n : ℕ) : FOClause (Extended L) ℕ :=
  Finset.univ.image (fun i : Fin n => negative (eqAtom (leftVariables i) (rightVariables i)))

def functionClause {n} (f : L.Functions n) : FOClause (Extended L) ℕ :=
  negativePairs L n ∪ {positive (eqAtom (.func f leftVariables) (.func f rightVariables))}

def relationClause {n} (R : L.Relations n) : FOClause (Extended L) ℕ :=
  negativePairs L n ∪ {negative (oldAtom R leftVariables), positive (oldAtom R rightVariables)}

/-- Exactly the five listed clause families, including every arity. -/
inductive AxiomClause (L : Language.{u, v}) : FOClause (Extended L) ℕ → Prop
  | refl : AxiomClause L (reflClause L)
  | symm : AxiomClause L (symmClause L)
  | trans : AxiomClause L (transClause L)
  | function {n} (f : L.Functions n) : AxiomClause L (functionClause f)
  | relation {n} (R : L.Relations n) : AxiomClause L (relationClause R)

def axiomClauses (L : Language.{u, v}) : Set (FOClause (Extended L) ℕ) := AxiomClause L

private theorem equalityFree_relabel {β : Type*} {m n : ℕ}
    (A : (Extended L).BoundedFormula α n) (g : α → β ⊕ Fin m) (h : EqualityFree A) :
    EqualityFree (A.relabel g) := by
  induction A with
  | falsum => trivial
  | equal => exact h.elim
  | rel => trivial
  | imp A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | all A ih => simpa only [BoundedFormula.relabel_all, EqualityFree] using ih h

private theorem equalityFree_restrict {β : Type*} [DecidableEq α] {n : ℕ}
    (A : (Extended L).BoundedFormula α n) (h : EqualityFree A)
    (f : A.freeVarFinset → β) : EqualityFree (A.restrictFreeVar f) := by
  induction A with
  | falsum => trivial
  | equal => exact h.elim
  | rel => trivial
  | imp A B ihA ihB => exact ⟨ihA h.1 _, ihB h.2 _⟩
  | all A ih => exact ih h f

private theorem equalityFree_exs {n : ℕ} (A : (Extended L).BoundedFormula α n)
    (h : EqualityFree A) : EqualityFree A.exs := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih A.ex ⟨⟨h, trivial⟩, trivial⟩

private theorem equalityFree_iExs {β : Type*} [Finite β]
    (A : (Extended L).Formula (α ⊕ β)) (h : EqualityFree A) :
    EqualityFree (A.iExs β) := by
  unfold Formula.iExs
  exact equalityFree_exs _ (equalityFree_relabel A _ h)

theorem clauses_equalityFree (C : FOClause (Extended L) α) :
    EqualityFree (clauseToFormula C) := by
  have hl (l : FOLiteral (Extended L) α) : EqualityFree (literalToFormula l) := by
    unfold literalToFormula
    split_ifs <;> simp [Atom.toFormula, Relations.formula, Relations.boundedFormula,
      EqualityFree]
  have hs (ls : List (FOLiteral (Extended L) α)) :
      EqualityFree ((ls.map literalToFormula).foldr (· ⊔ ·) ⊥) := by
    induction ls with
    | nil => trivial
    | cons l ls ih => exact ⟨⟨hl l, trivial⟩, ih⟩
  exact hs C.toList

private theorem eqAtom_realize {N : Type z} [(Extended L).Structure N]
    (s t : (Extended L).Term α) (v : α → N) :
    (eqAtom s t).Realize v ↔ E (L := L) (s.realize v) (t.realize v) := by
  simp only [eqAtom, Atom.Realize, realize_pair, E]

private theorem oldAtom_realize {N : Type z} [(Extended L).Structure N]
    {n} (R : L.Relations n) (ts : Fin n → (Extended L).Term α) (v : α → N) :
    (oldAtom R ts).Realize v ↔
      Structure.RelMap (L := Extended L) (.inl R) (fun i => (ts i).realize v) := Iff.rfl

private theorem refl_clause_truth {N : Type z} [(Extended L).Structure N] (v : ℕ → N) :
    (clauseToFormula (reflClause L)).Realize v ↔ E (L := L) (v 0) (v 0) := by
  rw [clause_formula_realize]
  simp [ClauseRealize, reflClause, positive, eqAtom_realize]

private theorem symm_clause_truth {N : Type z} [(Extended L).Structure N] (v : ℕ → N) :
    (clauseToFormula (symmClause L)).Realize v ↔
      (E (L := L) (v 0) (v 1) → E (L := L) (v 1) (v 0)) := by
  rw [clause_formula_realize]
  simp [ClauseRealize, symmClause, positive, negative, eqAtom_realize, imp_iff_not_or]

private theorem trans_clause_truth {N : Type z} [(Extended L).Structure N] (v : ℕ → N) :
    (clauseToFormula (transClause L)).Realize v ↔
      (E (L := L) (v 0) (v 1) → E (L := L) (v 1) (v 2) → E (L := L) (v 0) (v 2)) := by
  rw [clause_formula_realize]
  simp [ClauseRealize, transClause, positive, negative, eqAtom_realize,
    imp_iff_not_or]

private theorem function_clause_truth {N : Type z} [(Extended L).Structure N]
    {n} (f : L.Functions n) (v : ℕ → N) :
    (clauseToFormula (functionClause f)).Realize v ↔
      ((∀ i : Fin n, E (L := L) (v (2 * i.val)) (v (2 * i.val + 1))) →
        E (L := L) (Structure.funMap (L := Extended L) f (fun i => v (2 * i.val)))
          (Structure.funMap (L := Extended L) f (fun i => v (2 * i.val + 1)))) := by
  rw [clause_formula_realize]
  simp [ClauseRealize, functionClause, negativePairs, positive, negative, eqAtom_realize,
    leftVariables, rightVariables, Term.realize, or_and_right, exists_or, imp_iff_not_or,
    not_forall, or_comm]

private theorem relation_clause_truth {N : Type z} [(Extended L).Structure N]
    {n} (R : L.Relations n) (v : ℕ → N) :
    (clauseToFormula (relationClause R)).Realize v ↔
      ((∀ i : Fin n, E (L := L) (v (2 * i.val)) (v (2 * i.val + 1))) →
        Structure.RelMap (L := Extended L) (.inl R) (fun i => v (2 * i.val)) →
        Structure.RelMap (L := Extended L) (.inl R) (fun i => v (2 * i.val + 1))) := by
  rw [clause_formula_realize]
  simp [ClauseRealize, relationClause, negativePairs, positive, negative, eqAtom_realize,
    oldAtom_realize, leftVariables, rightVariables, or_and_right, exists_or,
    imp_iff_not_or, not_forall, or_comm, or_assoc]

private theorem pair_assignment {N : Type z} [Nonempty N] {n : ℕ} (a b : Fin n → N) :
    ∃ v : ℕ → N, (∀ i, v (2 * i.val) = a i) ∧ (∀ i, v (2 * i.val + 1) = b i) := by
  let e : Fin n ⊕ Fin n → ℕ := Sum.elim (fun i => 2 * i.val) (fun i => 2 * i.val + 1)
  have he : Function.Injective e := by
    intro i j hij
    cases i with
    | inl i =>
        cases j with
        | inl j => congr 1; apply Fin.ext; dsimp [e] at hij; omega
        | inr j => dsimp [e] at hij; omega
    | inr i =>
        cases j with
        | inl j => dsimp [e] at hij; omega
        | inr j => congr 1; apply Fin.ext; dsimp [e] at hij; omega
  refine ⟨Function.extend e (Sum.elim a b) (fun _ => Classical.choice inferInstance), ?_, ?_⟩
  · intro i
    exact he.extend_apply _ _ (Sum.inl i)
  · intro i
    exact he.extend_apply _ _ (Sum.inr i)

theorem axioms_iff_clauses {N : Type z} [(Extended L).Structure N] [Nonempty N] :
    Axioms L N ↔ ∀ C ∈ axiomClauses L, ∀ v : ℕ → N, (clauseToFormula C).Realize v := by
  constructor
  · intro h C hC v
    cases hC with
    | refl => exact (refl_clause_truth v).mpr (h.reflexive _)
    | symm => exact (symm_clause_truth v).mpr h.symmetric
    | trans => exact (trans_clause_truth v).mpr h.transitive
    | function f => exact (function_clause_truth f v).mpr (h.functions f _ _)
    | relation R =>
        exact (relation_clause_truth R v).mpr (fun hab => (h.relations R _ _ hab).mp)
  · intro h
    have hr (a : N) : E (L := L) a a :=
      (refl_clause_truth (fun _ => a)).mp (h _ (.refl) _)
    have hs {a b : N} (hab : E (L := L) a b) : E (L := L) b a := by
      let v : ℕ → N := fun i => if i = 0 then a else b
      have ht := (symm_clause_truth v).mp (h _ (.symm) v)
      exact ht hab
    have ht {a b c : N} (hab : E (L := L) a b) (hbc : E (L := L) b c) :
        E (L := L) a c := by
      let v : ℕ → N := fun i => if i = 0 then a else if i = 1 then b else c
      have hc := (trans_clause_truth v).mp (h _ (.trans) v)
      exact hc hab hbc
    have hf {n} (f : L.Functions n) (a b : Fin n → N)
        (hab : ∀ i, E (L := L) (a i) (b i)) :
        E (L := L) (Structure.funMap (L := Extended L) f a)
          (Structure.funMap (L := Extended L) f b) := by
      obtain ⟨v, ha, hb⟩ := pair_assignment a b
      have hc := (function_clause_truth f v).mp (h _ (.function f) v)
      simpa only [ha, hb] using hc (by simpa only [ha, hb] using hab)
    have hR {n} (R : L.Relations n) (a b : Fin n → N)
        (hab : ∀ i, E (L := L) (a i) (b i)) :
        Structure.RelMap (L := Extended L) (.inl R) a →
          Structure.RelMap (L := Extended L) (.inl R) b := by
      obtain ⟨v, ha, hb⟩ := pair_assignment a b
      have hc := (relation_clause_truth R v).mp (h _ (.relation R) v)
      simpa only [ha, hb] using hc (by simpa only [ha, hb] using hab)
    exact ⟨hr, hs, ht, hf, fun R a b hab => ⟨hR R a b hab, hR R b a (fun i => hs (hab i))⟩⟩

/-- Universal closure of precisely the finite free support, in native syntax. -/
def universalClosure (A : (Extended L).Formula ℕ) : (Extended L).Sentence :=
  A.not.exClosure.not

theorem universalClosure_truth {N : Type z} [(Extended L).Structure N] [Nonempty N]
    (A : (Extended L).Formula ℕ) :
    (universalClosure A).Realize N ↔ ∀ v : ℕ → N, A.Realize v := by
  have hex (B : (Extended L).Formula ℕ) :
      B.exClosure.Realize N ↔ ∃ v : ℕ → N, B.Realize v := by
    rw [Formula.realize_exClosure]
    constructor
    · rintro ⟨v, hv⟩
      let v' : ℕ → N := fun n => if hn : n ∈ B.freeVarFinset
        then v ⟨n, hn⟩ else Classical.choice inferInstance
      refine ⟨v', ?_⟩
      exact (BoundedFormula.realize_restrictFreeVar (φ := B) (f := id) (v := v)
        v' (fun a => by simp [v'])).mp hv
    · rintro ⟨v, hv⟩
      refine ⟨fun a => v a, ?_⟩
      exact (BoundedFormula.realize_restrictFreeVar (φ := B) (f := id)
        (v := fun a => v a) v (fun _ => rfl)).mpr hv
  simp only [universalClosure, Sentence.realize_not, hex, Formula.realize_not,
    not_exists, not_not]

theorem universalClosure_equalityFree (A : (Extended L).Formula ℕ) (h : EqualityFree A) :
    EqualityFree (universalClosure A) := by
  have hr : EqualityFree (A.not.restrictFreeVar id) :=
    equalityFree_restrict A.not ⟨h, trivial⟩ id
  have hf : EqualityFree (Formula.relabel (Sum.inr : A.not.freeVarFinset →
      Empty ⊕ A.not.freeVarFinset) (A.not.restrictFreeVar id)) :=
    equalityFree_relabel _ _ hr
  exact ⟨equalityFree_iExs _ hf, trivial⟩

/-- Actual equality-free native axiom sentences, not a semantic placeholder. -/
def axiomTheory (L : Language.{u, v}) : (Extended L).Theory :=
  {A | ∃ C ∈ axiomClauses L, universalClosure (clauseToFormula C) = A}

theorem axiomTheory_models_iff {N : Type z} [(Extended L).Structure N] [Nonempty N] :
    N ⊨ axiomTheory L ↔ Axioms L N := by
  rw [Theory.model_iff, axioms_iff_clauses]
  constructor
  · intro h C hC v
    exact (universalClosure_truth _).mp (h _ ⟨C, hC, rfl⟩) v
  · intro h A hA
    obtain ⟨C, hC, rfl⟩ := hA
    exact (universalClosure_truth _).mpr (h C hC)

def translatedTheory (T : L.Theory) : (Extended L).Theory := translate '' T

def encodedTheory (T : L.Theory) : (Extended L).Theory := translatedTheory T ∪ axiomTheory L

theorem encodedTheory_models_iff {N : Type z} [(Extended L).Structure N] [Nonempty N]
    (T : L.Theory) :
    N ⊨ encodedTheory T ↔ Axioms L N ∧ ∀ A ∈ T, Sentence.Realize N (translate A) := by
  rw [Theory.model_iff]
  constructor
  · intro h
    have hA : N ⊨ axiomTheory L := ⟨fun A hA => h A (Or.inr hA)⟩
    exact ⟨axiomTheory_models_iff.mp hA, fun A hA => h _ (Or.inl ⟨A, hA, rfl⟩)⟩
  · rintro ⟨hA, hT⟩ A (hAT | hAT)
    · obtain ⟨B, hB, rfl⟩ := hAT
      exact hT B hB
    · exact (axiomTheory_models_iff.mpr hA).realize_of_mem A hAT

/-- The language, formula translation and axiom theory have no theory parameter. -/
theorem theory_equisatisfiable (T : L.Theory) :
    T.IsSatisfiable ↔ (encodedTheory T).IsSatisfiable := by
  constructor
  · rintro ⟨M⟩
    let _ : (Extended L).Structure M := identityExpansion (L := L) M
    have hT : ∀ A ∈ T, Sentence.Realize M (translate A) := by
      intro A hA
      exact (identity_truth M A default default).mpr
        (show BoundedFormula.Realize A (default : Empty → M) (default : Fin 0 → M)
          from Theory.realize_sentence_of_mem T hA)
    let _ : M ⊨ encodedTheory T :=
      (encodedTheory_models_iff T).mpr ⟨identity_axioms M, hT⟩
    exact ⟨Theory.ModelType.of (encodedTheory T) M⟩
  · rintro ⟨N⟩
    obtain ⟨hA, hT⟩ := (encodedTheory_models_iff T).mp (inferInstance : N ⊨ encodedTheory T)
    let _ : Nonempty (QuotientModel hA) := quotient_nonempty hA
    have hQ : QuotientModel hA ⊨ T := by
      constructor
      intro A hAT
      have hp := (quotient_truth hA A default default).mpr (hT A hAT)
      have hv : projection hA ∘ (default : Empty → N) =
          (default : Empty → QuotientModel hA) := Subsingleton.elim _ _
      have hw : projection hA ∘ (default : Fin 0 → N) =
          (default : Fin 0 → QuotientModel hA) := Subsingleton.elim _ _
      change BoundedFormula.Realize A (default : Empty → QuotientModel hA)
        (default : Fin 0 → QuotientModel hA)
      simpa only [hv, hw] using hp
    let _ := hQ
    exact ⟨Theory.ModelType.of T (QuotientModel hA)⟩

/-! Original clauses retain actual logical equality atoms and native formulas. -/
abbrev OriginalAtom (L : Language.{u, v}) (α : Type w) :=
  (L.Term α × L.Term α) ⊕ Atom L α

abbrev OriginalLiteral (L : Language.{u, v}) (α : Type w) := PropLiteral (OriginalAtom L α)
abbrev OriginalClause (L : Language.{u, v}) (α : Type w) :=
  Lemmatheca.ProofTheory.Resolution.Clause (OriginalAtom L α)

def originalAtomFormula : OriginalAtom L α → L.Formula α
  | .inl (s, t) => s.equal t
  | .inr a => a.toFormula

def originalLiteralFormula (l : OriginalLiteral L α) : L.Formula α :=
  if l.positive then originalAtomFormula l.atom else (originalAtomFormula l.atom).not

def originalClauseFormula (C : OriginalClause L α) : L.Formula α :=
  (C.toList.map originalLiteralFormula).foldr (· ⊔ ·) ⊥

def translateAtom : OriginalAtom L α → Atom (Extended L) α
  | .inl (s, t) => eqAtom (termTranslate s) (termTranslate t)
  | .inr a => oldAtom a.relation (fun i => termTranslate (a.terms i))

def translateLiteral (l : OriginalLiteral L α) : FOLiteral (Extended L) α :=
  ⟨translateAtom l.atom, l.positive⟩

def translateClause (C : OriginalClause L α) : FOClause (Extended L) α := C.image translateLiteral

def translatedClauses (Δ : Set (OriginalClause L ℕ)) : Set (FOClause (Extended L) ℕ) :=
  translateClause '' Δ

/-- Nonempty actual native clause models, using all assignments per clause. -/
def OriginalClauseSatisfiable (Δ : Set (OriginalClause L ℕ)) : Prop :=
  ∃ M : Theory.ModelType.{u, v, max u v} (∅ : L.Theory),
    ∀ C ∈ Δ, ∀ v : ℕ → M, (originalClauseFormula C).Realize v

private theorem originalAtom_translate_truth {N : Type z} [(Extended L).Structure N]
    (a : OriginalAtom L α) (v : α → N) :
    Formula.Realize (translate (originalAtomFormula a)) v ↔ (translateAtom a).Realize v := by
  cases a with
  | inl st =>
      rcases st with ⟨s, t⟩
      simp [originalAtomFormula, translateAtom, Term.equal, Term.bdEqual, translate,
        Formula.Realize, BoundedFormula.Realize, realize_pair, eqAtom_realize, E,
        termTranslate, ChangingLanguages.map_term_relabel, Term.realize_relabel, Function.comp_def]
  | inr a =>
      simp [originalAtomFormula, translateAtom, Atom.toFormula, Relations.formula,
        Relations.boundedFormula, translate, Formula.Realize, BoundedFormula.Realize,
        oldAtom_realize, termTranslate, ChangingLanguages.map_term_relabel,
        Term.realize_relabel, Function.comp_def]

private theorem translate_sup {n : ℕ} (A B : L.BoundedFormula α n) :
    translate (A ⊔ B) = translate A ⊔ translate B := rfl

private theorem translate_not {n : ℕ} (A : L.BoundedFormula α n) :
    translate A.not = (translate A).not := rfl

private theorem translate_fold_sup (As : List (L.Formula α)) :
    translate (As.foldr (· ⊔ ·) ⊥) = (As.map translate).foldr (· ⊔ ·) ⊥ := by
  induction As with
  | nil => rfl
  | cons A As ih => simp only [List.foldr_cons, List.map_cons, translate_sup, ih]

theorem originalClause_translate_truth {N : Type z} [(Extended L).Structure N]
    (C : OriginalClause L α) (v : α → N) :
    Formula.Realize (translate (originalClauseFormula C)) v ↔
      (clauseToFormula (translateClause C)).Realize v := by
  have hl (l : OriginalLiteral L α) :
      Formula.Realize (translate (originalLiteralFormula l)) v ↔
        if l.positive then (translateAtom l.atom).Realize v else ¬ (translateAtom l.atom).Realize v := by
    cases hp : l.positive <;>
      simp [originalLiteralFormula, hp, translate_not, originalAtom_translate_truth]
  rw [originalClauseFormula, translate_fold_sup]
  change BoundedFormula.Realize _ v default ↔ _
  rw [BoundedFormula.realize_foldr_sup, clause_formula_realize]
  simp only [List.mem_map, exists_exists_and_eq_and, Finset.mem_toList]
  change (∃ l ∈ C, Formula.Realize (translate (originalLiteralFormula l)) v) ↔ _
  simp only [hl, ClauseRealize, translateClause, Finset.mem_image,
    exists_exists_and_eq_and, translateLiteral]

theorem originalClause_quotient_truth {N : Type z} [(Extended L).Structure N]
    (h : Axioms L N) (C : OriginalClause L α) (v : α → N) :
    (originalClauseFormula C).Realize (projection h ∘ v) ↔
      (clauseToFormula (translateClause C)).Realize v := by
  have hw : projection h ∘ (default : Fin 0 → N) =
      (default : Fin 0 → QuotientModel h) := Subsingleton.elim _ _
  have ht := quotient_truth h (originalClauseFormula C) v default
  rw [hw] at ht
  exact ht.trans (originalClause_translate_truth C v)

/-- Concrete input for equality-free first-order resolution. -/
theorem originalClauses_equisatisfiable (Δ : Set (OriginalClause L ℕ)) :
    OriginalClauseSatisfiable Δ ↔
      ClauseSatisfiable (translatedClauses Δ ∪ axiomClauses L) := by
  constructor
  · rintro ⟨M, hM⟩
    let _ : (Extended L).Structure M := identityExpansion (L := L) M
    let N : Theory.ModelType.{u, v, max u v} (∅ : (Extended L).Theory) :=
      Theory.ModelType.of _ M
    refine ⟨N, ?_⟩
    intro C hC v
    rcases hC with hC | hC
    · obtain ⟨D, hD, rfl⟩ := hC
      exact (originalClause_translate_truth D v).mp
        ((identity_truth M (originalClauseFormula D) v default).mpr (hM D hD v))
    · exact axioms_iff_clauses.mp (identity_axioms M) C hC v
  · rintro ⟨N, hN⟩
    have hA : Axioms L N := axioms_iff_clauses.mpr (fun C hC v => hN C (Or.inr hC) v)
    let _ : Nonempty (QuotientModel hA) := quotient_nonempty hA
    let M : Theory.ModelType.{u, v, max u v} (∅ : L.Theory) :=
      Theory.ModelType.of _ (QuotientModel hA)
    refine ⟨M, ?_⟩
    intro C hC v
    let S := (originalClauseFormula C).freeVarFinset
    let u : ℕ → N := fun n => if hn : n ∈ S
      then Classical.choose ((Quotient.mk_surjective (s := equivalence hA)) (v n))
      else Classical.choice inferInstance
    have hu : ∀ n ∈ S, projection hA (u n) = v n := by
      intro n hn
      dsimp only [u]
      rw [dite_eq_left hn]
      exact Classical.choose_spec ((Quotient.mk_surjective (s := equivalence hA)) (v n))
    have hc := hN (translateClause C) (Or.inl ⟨C, hC, rfl⟩) u
    have hq := (originalClause_quotient_truth hA C u).mpr hc
    exact (FirstOrderSemantics.formula_realize_agree (originalClauseFormula C)
      (projection hA ∘ u) v default hu).mp hq

/-- Generic same-expanded-model representation interface, in the minimal model universe. -/
theorem represented_theory_clause_reduction (T : L.Theory) (Γ : Set (FOClause (Extended L) ℕ))
    (hΓ : ∀ N : Theory.ModelType.{u, v, max u v} (∅ : (Extended L).Theory),
      (∀ C ∈ Γ, ∀ v : ℕ → N, (clauseToFormula C).Realize v) ↔
        ∀ A ∈ T, Sentence.Realize N (translate A)) :
    T.IsSatisfiable ↔ ClauseSatisfiable (Γ ∪ axiomClauses L) := by
  rw [theory_equisatisfiable]
  constructor
  · rintro ⟨N⟩
    obtain ⟨hA, hT⟩ := (encodedTheory_models_iff T).mp (inferInstance : N ⊨ encodedTheory T)
    let M : Theory.ModelType.{u, v, max u v} (∅ : (Extended L).Theory) :=
      Theory.ModelType.of _ N
    refine ⟨M, ?_⟩
    intro C hC v
    rcases hC with hC | hC
    · exact (hΓ M).mpr hT C hC v
    · exact axioms_iff_clauses.mp hA C hC v
  · rintro ⟨N, hN⟩
    have hA : Axioms L N := axioms_iff_clauses.mpr (fun C hC v => hN C (Or.inr hC) v)
    have hT := (hΓ N).mp (fun C hC v => hN C (Or.inl hC) v)
    let _ : N ⊨ encodedTheory T := (encodedTheory_models_iff T).mpr ⟨hA, hT⟩
    exact ⟨Theory.ModelType.of (encodedTheory T) N⟩

/-- Exact zero-arity instances of the concrete family. -/
theorem zero_arity_clauses (c : L.Functions 0) (R : L.Relations 0) :
    functionClause c = {positive (eqAtom (.func c Fin.elim0) (.func c Fin.elim0))} ∧
    relationClause R = {negative (oldAtom R Fin.elim0), positive (oldAtom R Fin.elim0)} := by
  have hl : (leftVariables (L := L) : Fin 0 → (Extended L).Term ℕ) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  have hr : (rightVariables (L := L) : Fin 0 → (Extended L).Term ℕ) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  simp [functionClause, relationClause, negativePairs, hl, hr]

end
end Lemmatheca.MathematicalLogic.EqualityAxioms
