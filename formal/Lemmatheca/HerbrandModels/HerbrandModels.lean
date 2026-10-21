import Lemmatheca.ChangingLanguages.ChangingLanguages
import Lemmatheca.Skolemization.Skolemization
import Lemmatheca.PropositionalCompactness.PropositionalCompactness
import Lemmatheca.Resolution.Resolution

/-! Ground-instance semantics on actual shared first-order terms and formulas.
Only relation atoms, falsum and implication are admitted in a relational matrix;
the restriction excludes built-in equality and quantifiers, not function symbols.
-/

namespace Lemmatheca.MathematicalLogic.HerbrandModels

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.Propositional


universe u v w w' z u' v'
variable {L : Language.{u, v}} {K : Language.{u', v'}}
variable {α : Type w} {β : Type w'}

/-- The Herbrand universe consists of actual closed terms. -/
abbrev GroundTerm (L : Language.{u, v}) := L.Term Empty

/-- Relation atoms retain their arity and actual term arguments. -/
structure Atom (L : Language.{u, v}) (α : Type w) where
  arity : ℕ
  relation : L.Relations arity
  terms : Fin arity → L.Term α

abbrev GroundAtom (L : Language.{u, v}) := Atom L Empty

noncomputable instance atomDecidableEq : DecidableEq (Atom L α) := Classical.decEq _

namespace Atom

/-- Simultaneous substitution in every actual argument term. -/
def subst (σ : α → L.Term β) (a : Atom L α) : Atom L β :=
  ⟨a.arity, a.relation, fun i => (a.terms i).subst σ⟩

/-- The actual shared first-order formula represented by an atom. -/
def toFormula (a : Atom L α) : L.Formula α := a.relation.formula a.terms

/-- Truth of an atom under an assignment in an actual first-order structure. -/
def Realize {M : Type z} [L.Structure M] (a : Atom L α) (v : α → M) : Prop :=
  Structure.RelMap a.relation (fun i => (a.terms i).realize v)

theorem realize_toFormula {M : Type z} [L.Structure M] (a : Atom L α) (v : α → M) :
    a.toFormula.Realize v ↔ a.Realize v := by
  simp [toFormula, Realize, Relations.formula, Formula.Realize,
    Term.realize_relabel, Function.comp_def]

theorem subst_realize {M : Type z} [L.Structure M] (a : Atom L α)
    (σ : α → L.Term β) (v : β → M) :
    (a.subst σ).Realize v ↔ a.Realize (fun x => (σ x).realize v) := by
  simp [subst, Realize, Term.realize_subst]

theorem subst_subst {γ : Type*} (a : Atom L α) (σ : α → L.Term β)
    (τ : β → L.Term γ) :
    (a.subst σ).subst τ = a.subst (fun x => (σ x).subst τ) := by
  cases a
  simp [subst, FirstOrderProofs.term_subst_subst]

theorem subst_var (a : Atom L α) : a.subst Term.var = a := by
  cases a
  simp [subst, FirstOrderProofs.term_subst_var]

end Atom

/-- A restriction on actual shared syntax: relations and Boolean operations only. -/
def RelationalQF : {n : ℕ} → L.BoundedFormula α n → Prop
  | _, .falsum => True
  | _, .equal _ _ => False
  | _, .rel _ _ => True
  | _, .imp φ ψ => RelationalQF φ ∧ RelationalQF ψ
  | _, .all _ => False

theorem relationalQF_isQF {n : ℕ} {φ : L.BoundedFormula α n}
    (h : RelationalQF φ) : φ.IsQF := by
  induction φ with
  | falsum => exact .falsum
  | equal => exact h.elim
  | rel r ts => exact .of_isAtomic (.rel r ts)
  | imp φ ψ ihφ ihψ => exact (ihφ h.1).imp (ihψ h.2)
  | all => exact h.elim

/-- Propositional reading of actual syntax. Values on the excluded constructors
are irrelevant; all truth theorems explicitly require `RelationalQF`. -/
def propositionalize : {n : ℕ} → L.BoundedFormula α n →
    PropFormula (Atom L (α ⊕ Fin n))
  | _, .falsum => .falsum
  | _, .equal _ _ => .falsum
  | _, .rel r ts => .atom ⟨_, r, ts⟩
  | _, .imp φ ψ => .impl (propositionalize φ) (propositionalize ψ)
  | _, .all _ => .falsum

/-- Substitute terms in atoms while preserving the shared propositional syntax. -/
def substituteAtoms (σ : α → L.Term β) (P : PropFormula (Atom L α)) :
    PropFormula (Atom L β) :=
  Propositional.subst (fun a => .atom (a.subst σ)) P

/-- A relational matrix in its actual scoped syntax, with its finite arity. -/
structure Matrix (L : Language.{u, v}) where
  arity : ℕ
  body : L.BoundedFormula Empty arity
  relational : RelationalQF body

/-- Fill every scoped slot by the supplied closed term, then read propositionally. -/
def groundReading {n : ℕ} (φ : L.BoundedFormula Empty n)
    (ts : Fin n → GroundTerm L) : PropFormula (GroundAtom L) :=
  substituteAtoms (Sum.elim Empty.elim ts) (propositionalize φ)

/-- Universal closures are actual shared first-order sentences. -/
def universalTheory (Γ : Set (Matrix L)) : L.Theory :=
  {σ | ∃ A ∈ Γ, A.body.alls = σ}

/-- All ground readings, over one shared atom set. -/
def groundTheory (Γ : Set (Matrix L)) : PropositionalCompactness.Theory (GroundAtom L) :=
  {P | ∃ A ∈ Γ, ∃ ts : Fin A.arity → GroundTerm L, groundReading A.body ts = P}

theorem groundReading_instantiate {n : ℕ} (φ : L.BoundedFormula Empty n)
    (h : RelationalQF φ) (ts : Fin n → GroundTerm L) :
    groundReading (FirstOrderProofs.instantiateSlots φ ts) Fin.elim0 = groundReading φ ts := by
  induction φ with
  | falsum => rfl
  | equal => exact h.elim
  | rel r args =>
    simp [groundReading, FirstOrderProofs.instantiateSlots, BoundedFormula.toFormula,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Relations.formula,
      Relations.boundedFormula,
      propositionalize, substituteAtoms, Propositional.subst, Atom.subst,
      FirstOrderProofs.term_subst_subst, FirstOrderProofs.term_subst_relabel,
      Function.comp_def]
    funext i
    congr 1
    funext x
    cases x with
    | inl x => exact x.elim
    | inr k =>
      change (ts k).subst Empty.elim = ts k
      have he : (Empty.elim : Empty → GroundTerm L) = Term.var := Subsingleton.elim _ _
      rw [he, FirstOrderProofs.term_subst_var]
  | imp φ ψ ihφ ihψ =>
    change PropFormula.impl
      (groundReading (FirstOrderProofs.instantiateSlots φ ts) Fin.elim0)
      (groundReading (FirstOrderProofs.instantiateSlots ψ ts) Fin.elim0) =
      PropFormula.impl (groundReading φ ts) (groundReading ψ ts)
    rw [ihφ h.1 ts, ihψ h.2 ts]
  | all => exact h.elim

noncomputable section

/-- The Boolean valuation induced by the truth of actual ground relation atoms. -/
def modelValuation (M : Type z) [L.Structure M] : Valuation (GroundAtom L) :=
  by
  classical
  exact fun a => decide (a.Realize (M := M) Empty.elim)

theorem groundReading_realize {M : Type z} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula Empty n) (h : RelationalQF φ)
    (ts : Fin n → GroundTerm L) :
    eval (modelValuation M) (groundReading φ ts) = true ↔
      φ.Realize (M := M) Empty.elim (fun i => (ts i).realize Empty.elim) := by
  classical
  induction φ with
  | falsum => simp [groundReading, propositionalize, substituteAtoms, Propositional.subst,
      eval, BoundedFormula.Realize]
  | equal => exact h.elim
  | rel r args =>
    simp only [groundReading, propositionalize, substituteAtoms, Propositional.subst,
      eval, modelValuation, Atom.Realize, Atom.subst, Term.realize_subst,
      BoundedFormula.Realize, decide_eq_true_eq]
    have he : (fun a => (Sum.elim Empty.elim ts a).realize (Empty.elim : Empty → M)) =
        Sum.elim Empty.elim (fun i => (ts i).realize (Empty.elim : Empty → M)) := by
      funext x
      cases x with
      | inl x => exact x.elim
      | inr i => rfl
    rw [he]
  | imp φ ψ ihφ ihψ =>
    have hc := ihφ h.1 ts
    have hd := ihψ h.2 ts
    change ((!eval (modelValuation M) (groundReading φ ts)) ||
      eval (modelValuation M) (groundReading ψ ts)) = true ↔ (_ → _)
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
    tauto
  | all => exact h.elim

theorem actual_instance_truth {M : Type z} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula Empty n) (h : RelationalQF φ)
    (ts : Fin n → GroundTerm L) :
    eval (modelValuation M) (groundReading φ ts) = true ↔
      M ⊨ FirstOrderProofs.instantiateSlots φ ts := by
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simpa only [Sentence.Realize, he] using
    (groundReading_realize φ h ts).trans
      (FirstOrderProofs.instantiateSlots_realize φ ts Empty.elim).symm

/-- Function symbols build terms, and the supplied valuation interprets relations. -/
@[instance_reducible]
def termStructure (b : Valuation (GroundAtom L)) : L.Structure (GroundTerm L) where
  funMap f ts := Term.func f ts
  RelMap r ts := b ⟨_, r, ts⟩ = true

theorem term_realize_substitution (b : Valuation (GroundAtom L))
    (t : L.Term α) (σ : α → GroundTerm L) :
    @Term.realize L (GroundTerm L) (termStructure b) α σ t = t.subst σ := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    change Term.func f (fun i => @Term.realize L (GroundTerm L) (termStructure b) α σ (ts i)) =
      Term.func f (fun i => (ts i).subst σ)
    congr 1
    funext i
    exact ih i

theorem ground_term_self (b : Valuation (GroundAtom L)) (t : GroundTerm L) :
    @Term.realize L (GroundTerm L) (termStructure b) Empty Empty.elim t = t := by
  rw [term_realize_substitution]
  have e : (Empty.elim : Empty → GroundTerm L) = Term.var := by
    funext x
    exact x.elim
  rw [e, FirstOrderProofs.term_subst_var]

theorem termStructure_valuation (b : Valuation (GroundAtom L)) :
    @modelValuation L (GroundTerm L) (termStructure b) = b := by
  classical
  funext a
  apply Bool.eq_iff_iff.mpr
  rw [modelValuation, decide_eq_true_iff]
  change b ⟨a.arity, a.relation,
    fun i => @Term.realize L (GroundTerm L) (termStructure b) Empty Empty.elim (a.terms i)⟩ = true ↔ b a = true
  simp only [ground_term_self]

theorem term_model_truth (b : Valuation (GroundAtom L)) {n : ℕ}
    (φ : L.BoundedFormula Empty n) (h : RelationalQF φ)
    (ts : Fin n → GroundTerm L) :
    @BoundedFormula.Realize L (GroundTerm L) (termStructure b) Empty n φ Empty.elim ts ↔
      eval b (groundReading φ ts) = true := by
  let _ := termStructure b
  have h := groundReading_realize φ h ts (M := GroundTerm L)
  simpa only [termStructure_valuation, ground_term_self] using h.symm

theorem term_model_models [Nonempty (GroundTerm L)]
    (Γ : Set (Matrix L)) (b : Valuation (GroundAtom L))
    (hb : PropositionalCompactness.ModelsTheory b (groundTheory Γ)) :
    @Theory.Model L (GroundTerm L) (termStructure b) (universalTheory Γ) := by
  let _ := termStructure b
  refine ⟨?_⟩
  intro φ hφ
  obtain ⟨A, hA, rfl⟩ := hφ
  rw [Sentence.Realize, BoundedFormula.realize_alls]
  intro ts
  have he : (default : Empty → GroundTerm L) = Empty.elim := Subsingleton.elim _ _
  simpa only [he] using (term_model_truth b A.body A.relational ts).mpr
    (hb _ ⟨A, hA, ts, rfl⟩)

theorem model_gives_ground_valuation {M : Type z} [L.Structure M]
    (Γ : Set (Matrix L)) (hM : M ⊨ universalTheory Γ) :
    PropositionalCompactness.ModelsTheory (modelValuation M) (groundTheory Γ) := by
  intro P hP
  obtain ⟨A, hA, ts, rfl⟩ := hP
  apply (groundReading_realize A.body A.relational ts).mpr
  have ha := hM.realize_of_mem A.body.alls ⟨A, hA, rfl⟩
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simpa only [he] using (BoundedFormula.realize_alls.mp ha)
    (fun i => (ts i).realize (Empty.elim : Empty → M))

theorem herbrand_iff [Nonempty (GroundTerm L)] (Γ : Set (Matrix L)) :
    (universalTheory Γ).IsSatisfiable ↔ PropositionalCompactness.TheorySatisfiable (groundTheory Γ) := by
  constructor
  · rintro ⟨M⟩
    exact ⟨modelValuation M, model_gives_ground_valuation Γ inferInstance⟩
  · rintro ⟨b, hb⟩
    let _ := termStructure b
    let _ := term_model_models Γ b hb
    exact ⟨(Theory.ModelType.of (universalTheory Γ) (GroundTerm L)).ulift.{u, v, u, v}⟩

theorem finite_ground_obstruction [Nonempty (GroundTerm L)] (Γ : Set (Matrix L)) :
    ¬ (universalTheory Γ).IsSatisfiable ↔
      ∃ Δ : Finset (PropFormula (GroundAtom L)),
        (↑Δ : PropositionalCompactness.Theory (GroundAtom L)) ⊆ groundTheory Γ ∧ ¬ Satisfiable Δ := by
  classical
  rw [herbrand_iff]
  exact PropositionalCompactness.finite_unsatisfiable_obstruction (groundTheory Γ)

/-! Clauses use the existing signed propositional atoms and finite-set calculus. -/

abbrev FOLiteral (L : Language.{u, v}) (α : Type w) := PropLiteral (Atom L α)
abbrev FOClause (L : Language.{u, v}) (α : Type w) := Lemmatheca.ProofTheory.Resolution.Clause (Atom L α)
abbrev GroundClause (L : Language.{u, v}) := FOClause L Empty

def literalSubst (σ : α → L.Term β) (l : FOLiteral L α) : FOLiteral L β :=
  ⟨l.atom.subst σ, l.positive⟩

def clauseSubst (σ : α → L.Term β) (C : FOClause L α) : FOClause L β := by
  classical
  exact C.image (literalSubst σ)

def literalToFormula (l : FOLiteral L α) : L.Formula α :=
  if l.positive then l.atom.toFormula else l.atom.toFormula.not

def clauseToFormula (C : FOClause L α) : L.Formula α :=
  (C.toList.map literalToFormula).foldr (· ⊔ ·) ⊥

def ClauseRealize {M : Type z} [L.Structure M]
    (C : FOClause L α) (v : α → M) : Prop :=
  ∃ l ∈ C, if l.positive then l.atom.Realize v else ¬ l.atom.Realize v

def GroundClauses (Γ : Set (FOClause L α)) : Set (GroundClause L) :=
  {D | ∃ C ∈ Γ, ∃ σ : α → GroundTerm L, clauseSubst σ C = D}

/-- Nonempty models of the universally asserted actual clause formulas. -/
def ClauseSatisfiable (Γ : Set (FOClause L α)) : Prop :=
  ∃ M : Theory.ModelType.{u, v, max u v} (∅ : L.Theory), ∀ C ∈ Γ, ∀ v : α → M, (clauseToFormula C).Realize v

def groundClauseFormula (C : GroundClause L) : PropFormula (GroundAtom L) :=
  Propositional.clauseFormula C.toList

def groundClauseTheory (Γ : Set (FOClause L α)) : PropositionalCompactness.Theory (GroundAtom L) :=
  groundClauseFormula '' GroundClauses Γ

theorem clause_formula_realize {M : Type z} [L.Structure M]
    (C : FOClause L α) (v : α → M) :
    (clauseToFormula C).Realize v ↔ ClauseRealize C v := by
  have hl (l : FOLiteral L α) :
      (literalToFormula l).Realize v ↔
        if l.positive then l.atom.Realize v else ¬ l.atom.Realize v := by
    cases h : l.positive <;> simp [literalToFormula, h, Atom.realize_toFormula]
  change BoundedFormula.Realize
    ((C.toList.map literalToFormula).foldr (· ⊔ ·) ⊥) v default ↔ _
  rw [BoundedFormula.realize_foldr_sup]
  simp only [List.mem_map, exists_exists_and_eq_and, Finset.mem_toList]
  change (∃ l ∈ C, (literalToFormula l).Realize v) ↔ ClauseRealize C v
  simp only [hl, ClauseRealize]

theorem ground_clause_formula (C : GroundClause L) (b : Valuation (GroundAtom L)) :
    eval b (groundClauseFormula C) = true ↔ Lemmatheca.ProofTheory.Resolution.ClauseSat b C := by
  simpa [groundClauseFormula] using
    (Lemmatheca.ProofTheory.Resolution.list_clause b C.toList)

theorem grounded_clause_truth {M : Type z} [L.Structure M]
    (C : FOClause L α) (σ : α → GroundTerm L) :
    (clauseToFormula C).Realize (M := M) (fun x => (σ x).realize Empty.elim) ↔
      Lemmatheca.ProofTheory.Resolution.ClauseSat (modelValuation M) (clauseSubst σ C) := by
  classical
  rw [clause_formula_realize]
  have hl (l : FOLiteral L α) :
      (if l.positive then l.atom.Realize (fun x => (σ x).realize (Empty.elim : Empty → M))
        else ¬ l.atom.Realize (fun x => (σ x).realize (Empty.elim : Empty → M))) ↔
        Lemmatheca.ProofTheory.Resolution.LiteralSat (modelValuation M) (literalSubst σ l) := by
    have ht := Atom.subst_realize l.atom σ (Empty.elim : Empty → M)
    cases hs : l.positive <;>
      simp [literalSubst, Lemmatheca.ProofTheory.Resolution.LiteralSat,
        modelValuation, hs, ht]
  simp only [ClauseRealize, Lemmatheca.ProofTheory.Resolution.ClauseSat, clauseSubst,
    Finset.mem_image, exists_exists_and_eq_and, hl]

theorem ground_clause_term_truth (b : Valuation (GroundAtom L))
    (C : FOClause L α) (σ : α → GroundTerm L) :
    @Formula.Realize L (GroundTerm L) (termStructure b) α (clauseToFormula C) σ ↔
      Lemmatheca.ProofTheory.Resolution.ClauseSat b (clauseSubst σ C) := by
  let _ := termStructure b
  simpa only [ground_term_self, termStructure_valuation] using
    (grounded_clause_truth (M := GroundTerm L) C σ)

theorem clause_herbrand_iff [Nonempty (GroundTerm L)] (Γ : Set (FOClause L α)) :
    ClauseSatisfiable Γ ↔ ∃ b : Valuation (GroundAtom L),
      ∀ D ∈ GroundClauses Γ, Lemmatheca.ProofTheory.Resolution.ClauseSat b D := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨modelValuation M, ?_⟩
    rintro D ⟨C, hC, σ, rfl⟩
    exact (grounded_clause_truth C σ).mp (hM C hC _)
  · rintro ⟨b, hb⟩
    let _ := termStructure b
    let e : GroundTerm L ≃ ULift.{v} (GroundTerm L) := Equiv.ulift.symm
    let _ : L.Structure (ULift.{v} (GroundTerm L)) := e.inducedStructure
    let M : Theory.ModelType.{u, v, max u v} (∅ : L.Theory) :=
      Theory.ModelType.of _ (ULift.{v} (GroundTerm L))
    refine ⟨M, ?_⟩
    intro C hC vs
    have hc : @Formula.Realize L (GroundTerm L) (termStructure b) α
        (clauseToFormula C) (e.symm ∘ vs) :=
      (ground_clause_term_truth b C _).mpr (hb _ ⟨C, hC, e.symm ∘ vs, rfl⟩)
    change @Formula.Realize L (ULift.{v} (GroundTerm L)) e.inducedStructure α
      (clauseToFormula C) vs
    have ht := (StrongHomClass.realize_formula e.inducedStructureEquiv
      (clauseToFormula C)).mpr hc
    change @Formula.Realize L (ULift.{v} (GroundTerm L)) e.inducedStructure α
      (clauseToFormula C) (e ∘ (e.symm ∘ vs)) at ht
    have he : e ∘ (e.symm ∘ vs) = vs := by
      funext x
      exact e.apply_symm_apply (vs x)
    rw [he] at ht
    exact ht

theorem clause_ground_theory_iff (Γ : Set (FOClause L α)) :
    PropositionalCompactness.TheorySatisfiable (groundClauseTheory Γ) ↔
      ∃ b : Valuation (GroundAtom L), ∀ D ∈ GroundClauses Γ, Lemmatheca.ProofTheory.Resolution.ClauseSat b D := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, fun D hD => (ground_clause_formula D b).mp (hb _ ⟨D, hD, rfl⟩)⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro P ⟨D, hD, rfl⟩
    exact (ground_clause_formula D b).mpr (hb D hD)

theorem finite_clause_obstruction [Nonempty (GroundTerm L)] (Γ : Set (FOClause L α)) :
    ¬ ClauseSatisfiable Γ ↔ ∃ Δ : Lemmatheca.ProofTheory.Resolution.ClauseSet (GroundAtom L),
      (↑Δ : Set (GroundClause L)) ⊆ GroundClauses Γ ∧ ¬ Lemmatheca.ProofTheory.Resolution.Sat Δ := by
  classical
  constructor
  · intro hn
    have ht : ¬ PropositionalCompactness.TheorySatisfiable (groundClauseTheory Γ) := by
      rw [clause_ground_theory_iff]
      exact fun h => hn ((clause_herbrand_iff Γ).mpr h)
    obtain ⟨Θ, hΘ, hunsat⟩ :=
      (PropositionalCompactness.finite_unsatisfiable_obstruction _).mp ht
    have hx (P : Θ) : ∃ D ∈ GroundClauses Γ, groundClauseFormula D = P.val := hΘ P.property
    let chooseClause (P : Θ) : GroundClause L := Classical.choose (hx P)
    have chosen (P : Θ) : chooseClause P ∈ GroundClauses Γ ∧
        groundClauseFormula (chooseClause P) = P.val := Classical.choose_spec (hx P)
    let Δ : Lemmatheca.ProofTheory.Resolution.ClauseSet (GroundAtom L) :=
      Θ.attach.image chooseClause
    refine ⟨Δ, ?_, ?_⟩
    · intro D hD
      obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hD
      exact (chosen P).1
    · rintro ⟨b, hb⟩
      apply hunsat
      refine ⟨b, ?_⟩
      intro P hP
      let x : Θ := ⟨P, hP⟩
      have hd : chooseClause x ∈ Δ := Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩
      have hh := (ground_clause_formula (chooseClause x) b).mpr (hb _ hd)
      simpa only [(chosen x).2, x, Satisfies] using hh
  · rintro ⟨Δ, hΔ, hunsat⟩ hsat
    obtain ⟨b, hb⟩ := (clause_herbrand_iff Γ).mp hsat
    exact hunsat ⟨b, fun D hD => hb D (hΔ hD)⟩

theorem finite_ground_refutation [Nonempty (GroundTerm L)] (Γ : Set (FOClause L α)) :
    ¬ ClauseSatisfiable Γ ↔ ∃ Δ : Lemmatheca.ProofTheory.Resolution.ClauseSet (GroundAtom L),
      (↑Δ : Set (GroundClause L)) ⊆ GroundClauses Γ ∧ Lemmatheca.ProofTheory.Resolution.Derives Δ ∅ := by
  classical
  rw [finite_clause_obstruction]
  constructor
  · rintro ⟨Δ, hΔ, h⟩
    exact ⟨Δ, hΔ, Lemmatheca.ProofTheory.Resolution.finite_complete h⟩
  · rintro ⟨Δ, hΔ, h⟩
    exact ⟨Δ, hΔ, Lemmatheca.ProofTheory.Resolution.refutation_unsat h⟩

/-! The constant and translation are chosen from the language, before the theory. -/

abbrev freshLanguage (L : Language.{u, v}) : Language := L[[Unit]]

def freshInclusion (L : Language.{u, v}) : L →ᴸ freshLanguage L := LHom.sumInl

def freshTerm (L : Language.{u, v}) : GroundTerm (freshLanguage L) :=
  Term.func (Sum.inr () : (freshLanguage L).Functions 0) Fin.elim0

theorem relationalQF_map (j : L →ᴸ K) {n : ℕ} {φ : L.BoundedFormula Empty n}
    (h : RelationalQF φ) : RelationalQF (j.onBoundedFormula φ) := by
  induction φ with
  | falsum => trivial
  | equal => exact h.elim
  | rel => trivial
  | imp φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | all => exact h.elim

def mapMatrix (j : L →ᴸ K) (A : Matrix L) : Matrix K :=
  ⟨A.arity, j.onBoundedFormula A.body, relationalQF_map j A.relational⟩

theorem universalTheory_map (j : L →ᴸ K) (Γ : Set (Matrix L)) :
    universalTheory (mapMatrix j '' Γ) = j.onTheory (universalTheory Γ) := by
  have hmap : ∀ {n : ℕ} (φ : L.BoundedFormula Empty n),
      j.onSentence φ.alls = (j.onBoundedFormula φ).alls := by
    intro n
    induction n with
    | zero => intro φ; rfl
    | succ n ih => intro φ; exact ih φ.all
  ext θ
  constructor
  · rintro ⟨B, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.body.alls, ⟨A, hA, rfl⟩, hmap A.body⟩
  · rintro ⟨σ, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨mapMatrix j A, ⟨A, hA, rfl⟩, (hmap A.body).symm⟩

theorem fresh_constant_satisfiable (Γ : Set (Matrix L)) :
    (universalTheory Γ).IsSatisfiable ↔
      (universalTheory (mapMatrix (freshInclusion L) '' Γ)).IsSatisfiable := by
  rw [universalTheory_map]
  exact (Theory.isSatisfiable_onTheory_iff (φ := freshInclusion L)
    LHom.sumInl_injective).symm

theorem fresh_constant_herbrand (Γ : Set (Matrix L)) :
    (universalTheory Γ).IsSatisfiable ↔
      PropositionalCompactness.TheorySatisfiable (groundTheory (mapMatrix (freshInclusion L) '' Γ)) := by
  let _ : Nonempty (GroundTerm (freshLanguage L)) := ⟨freshTerm L⟩
  exact (fresh_constant_satisfiable Γ).trans (herbrand_iff _)

theorem fresh_constant_finite_obstruction (Γ : Set (Matrix L)) :
    ¬ (universalTheory Γ).IsSatisfiable ↔
      ∃ Δ : Finset (PropFormula (GroundAtom (freshLanguage L))),
        (↑Δ : PropositionalCompactness.Theory (GroundAtom (freshLanguage L))) ⊆
          groundTheory (mapMatrix (freshInclusion L) '' Γ) ∧ ¬ Satisfiable Δ := by
  classical
  let _ : Nonempty (GroundTerm (freshLanguage L)) := ⟨freshTerm L⟩
  rw [fresh_constant_satisfiable]
  exact finite_ground_obstruction _

end
end Lemmatheca.MathematicalLogic.HerbrandModels
