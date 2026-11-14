import Lemmatheca.EqualityFreeIntuitionisticFirstOrderCutElimination.Properties

/-! Native full scoped occurrences and actual instances, with the falsum required
by primitive negation. Every displayed formula retains its actual parameter type. -/
namespace Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}

/-- Selecting native children retains every available slot encountered under binders. -/
inductive ScopedSubformula : {n m : ℕ} → BoundedFormula L α n → BoundedFormula L α m → Prop
  | refl {n} (A : BoundedFormula L α n) : ScopedSubformula A A
  | negChild {n m} {C : BoundedFormula L α n} {A : BoundedFormula L α m} :
      ScopedSubformula C A → ScopedSubformula C (.neg A)
  | conjLeft {n m} {C : BoundedFormula L α n} {A B : BoundedFormula L α m} :
      ScopedSubformula C A → ScopedSubformula C (.conj A B)
  | conjRight {n m} {C : BoundedFormula L α n} {A B : BoundedFormula L α m} :
      ScopedSubformula C B → ScopedSubformula C (.conj A B)
  | disjLeft {n m} {C : BoundedFormula L α n} {A B : BoundedFormula L α m} :
      ScopedSubformula C A → ScopedSubformula C (.disj A B)
  | disjRight {n m} {C : BoundedFormula L α n} {A B : BoundedFormula L α m} :
      ScopedSubformula C B → ScopedSubformula C (.disj A B)
  | implLeft {n m} {C : BoundedFormula L α n} {A B : BoundedFormula L α m} :
      ScopedSubformula C A → ScopedSubformula C (.impl A B)
  | implRight {n m} {C : BoundedFormula L α n} {A B : BoundedFormula L α m} :
      ScopedSubformula C B → ScopedSubformula C (.impl A B)
  | allBody {n m} {C : BoundedFormula L α n} {A : BoundedFormula L α (m+1)} :
      ScopedSubformula C A → ScopedSubformula C (.all A)
  | exBody {n m} {C : BoundedFormula L α n} {A : BoundedFormula L α (m+1)} :
      ScopedSubformula C A → ScopedSubformula C (.ex A)
end Lemmatheca.ProofTheory.FirstOrder.BoundedFormula

namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder (ScopeSubst)
universe u v w w'
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifocutSubformulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

/-- A literal scoped occurrence and scope substitution from a root end formula. -/
def InstantiatedSubformula (Γ : Context L α) (C : Formula L α)
    (β : Type w') (D : Formula L β) : Prop :=
  ∃ A ∈ insert C Γ, ∃ n, ∃ B : BF L α n,
    B.ScopedSubformula A ∧ ∃ σ : ScopeSubst L α β n 0, B.map σ = D

/-- Falsum is allowed separately because native negation is a primitive constructor. -/
def AnalyticInstance (Γ : Context L α) (C : Formula L α)
    (β : Type w') (D : Formula L β) : Prop :=
  D = .falsum ∨ InstantiatedSubformula Γ C β D

/-- Every context member and conclusion at every node, including protected branches. -/
def CoreProof.Every (P : (δ : Type w) → Formula L δ → Prop) :
    {δ : Type w} → {Γ : Context L δ} → {C : Formula L δ} → CoreProof L Γ C → Prop
  | δ, Γ, C, p => (∀ A ∈ Γ, P δ A) ∧ P δ C ∧ match p with
    | .relation _ _ _ | .falsumLeft _ => True
    | .conjRight p q | .disjLeft _ p q | .implLeft _ p q => p.Every P ∧ q.Every P
    | .conjLeft _ p | .disjRightLeft p | .disjRightRight p | .implRight p
      | .negLeft _ p | .negRight p | .allLeft _ _ p | .allRight p
      | .exLeft _ p | .exRight _ p => p.Every P


private theorem scopedTrans {n m k} {D : BF L α n} {B : BF L α m}
    {A : BF L α k} (hDB : D.ScopedSubformula B) (hBA : B.ScopedSubformula A) :
    D.ScopedSubformula A := by
  induction hBA with
  | refl => exact hDB
  | negChild h ih => exact .negChild (ih hDB)
  | conjLeft h ih => exact .conjLeft (ih hDB)
  | conjRight h ih => exact .conjRight (ih hDB)
  | disjLeft h ih => exact .disjLeft (ih hDB)
  | disjRight h ih => exact .disjRight (ih hDB)
  | implLeft h ih => exact .implLeft (ih hDB)
  | implRight h ih => exact .implRight (ih hDB)
  | allBody h ih => exact .allBody (ih hDB)
  | exBody h ih => exact .exBody (ih hDB)

private theorem instantiated_map {δ : Type w'} {ε : Type*}
    {Γ : Context L α} {C : Formula L α} {A : Formula L δ}
    (h : InstantiatedSubformula Γ C δ A) (τ : ScopeSubst L δ ε 0 0) :
    InstantiatedSubformula Γ C ε (A.map τ) := by
  rcases h with ⟨F, hF, n, B, hB, σ, rfl⟩
  exact ⟨F, hF, n, B, hB, (fun x => (σ x).subst τ), (B.map_comp σ τ).symm⟩

private theorem analytic_rename {δ : Type w'} {ε : Type*}
    {Γ : Context L α} {C : Formula L α} {A : Formula L δ}
    (h : AnalyticInstance Γ C δ A) (f : δ → ε) :
    AnalyticInstance Γ C ε (A.rename f) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (instantiated_map h _)

private theorem analytic_instantiated {δ : Type w'}
    {Γ : Context L α} {C : Formula L α} {A : Formula L δ}
    (h : AnalyticInstance Γ C δ A) (hne : A ≠ .falsum) :
    InstantiatedSubformula Γ C δ A := h.resolve_left hne

private theorem analytic_neg {δ : Type w'} {Γ : Context L α}
    {C : Formula L α} {A : Formula L δ}
    (h : AnalyticInstance Γ C δ (.neg A)) :
    AnalyticInstance Γ C δ A := by
  obtain ⟨F, hF, n, D, hD, σ, heq⟩ := analytic_instantiated h (by intro h; cases h)
  cases D with
  | falsum =>
      cases heq
  | equal s t =>
      cases heq
  | rel R ts =>
      cases heq
  | neg X =>
      cases heq
      exact Or.inr ⟨F, hF, _, X, scopedTrans (.negChild (.refl X)) hD, σ, rfl⟩
  | conj X Y =>
      cases heq
  | disj X Y =>
      cases heq
  | impl X Y =>
      cases heq
  | all X =>
      cases heq
  | ex X =>
      cases heq

private theorem analytic_conj {δ : Type w'} {Γ : Context L α}
    {C : Formula L α} {A B : Formula L δ}
    (h : AnalyticInstance Γ C δ (.conj A B)) :
    AnalyticInstance Γ C δ A ∧ AnalyticInstance Γ C δ B := by
  obtain ⟨F, hF, n, D, hD, σ, heq⟩ := analytic_instantiated h (by intro h; cases h)
  cases D with
  | falsum =>
      cases heq
  | equal s t =>
      cases heq
  | rel R ts =>
      cases heq
  | neg X =>
      cases heq
  | conj X Y =>
      cases heq
      exact ⟨Or.inr ⟨F, hF, _, X, scopedTrans (.conjLeft (.refl X)) hD, σ, rfl⟩,
        Or.inr ⟨F, hF, _, Y, scopedTrans (.conjRight (.refl Y)) hD, σ, rfl⟩⟩
  | disj X Y =>
      cases heq
  | impl X Y =>
      cases heq
  | all X =>
      cases heq
  | ex X =>
      cases heq

private theorem analytic_disj {δ : Type w'} {Γ : Context L α}
    {C : Formula L α} {A B : Formula L δ}
    (h : AnalyticInstance Γ C δ (.disj A B)) :
    AnalyticInstance Γ C δ A ∧ AnalyticInstance Γ C δ B := by
  obtain ⟨F, hF, n, D, hD, σ, heq⟩ := analytic_instantiated h (by intro h; cases h)
  cases D with
  | falsum =>
      cases heq
  | equal s t =>
      cases heq
  | rel R ts =>
      cases heq
  | neg X =>
      cases heq
  | conj X Y =>
      cases heq
  | disj X Y =>
      cases heq
      exact ⟨Or.inr ⟨F, hF, _, X, scopedTrans (.disjLeft (.refl X)) hD, σ, rfl⟩,
        Or.inr ⟨F, hF, _, Y, scopedTrans (.disjRight (.refl Y)) hD, σ, rfl⟩⟩
  | impl X Y =>
      cases heq
  | all X =>
      cases heq
  | ex X =>
      cases heq

private theorem analytic_impl {δ : Type w'} {Γ : Context L α}
    {C : Formula L α} {A B : Formula L δ}
    (h : AnalyticInstance Γ C δ (.impl A B)) :
    AnalyticInstance Γ C δ A ∧ AnalyticInstance Γ C δ B := by
  obtain ⟨F, hF, n, D, hD, σ, heq⟩ := analytic_instantiated h (by intro h; cases h)
  cases D with
  | falsum =>
      cases heq
  | equal s t =>
      cases heq
  | rel R ts =>
      cases heq
  | neg X =>
      cases heq
  | conj X Y =>
      cases heq
  | disj X Y =>
      cases heq
  | impl X Y =>
      cases heq
      exact ⟨Or.inr ⟨F, hF, _, X, scopedTrans (.implLeft (.refl X)) hD, σ, rfl⟩,
        Or.inr ⟨F, hF, _, Y, scopedTrans (.implRight (.refl Y)) hD, σ, rfl⟩⟩
  | all X =>
      cases heq
  | ex X =>
      cases heq

private theorem analytic_all_open {δ : Type w'} {Γ : Context L α}
    {C : Formula L α} {B : BF L δ 1}
    (h : AnalyticInstance Γ C δ (.all B)) :
    AnalyticInstance Γ C (δ ⊕ Fin 1) B.toFormula := by
  obtain ⟨F, hF, n, D, hD, σ, heq⟩ := analytic_instantiated h (by intro h; cases h)
  cases D with
  | falsum =>
      cases heq
  | equal s t =>
      cases heq
  | rel R ts =>
      cases heq
  | neg X =>
      cases heq
  | conj X Y =>
      cases heq
  | disj X Y =>
      cases heq
  | impl X Y =>
      cases heq
  | all X =>
      cases heq
      refine Or.inr ⟨F, hF, _, X, scopedTrans (.allBody (.refl X)) hD,
        (fun x => ((Lemmatheca.ProofTheory.FirstOrder.liftScope σ) x).subst
          (fun v => .var (.inl v))), ?_⟩
      exact (X.map_comp _ _).symm
  | ex X =>
      cases heq

private theorem analytic_all_instance {δ : Type w'} {Γ : Context L α}
    {C : Formula L α} {B : BF L δ 1}
    (h : AnalyticInstance Γ C δ (.all B)) (t : L.Term δ) :
    AnalyticInstance Γ C (δ) (B.instantiate t) := by
  obtain ⟨F, hF, n, D, hD, σ, heq⟩ := analytic_instantiated h (by intro h; cases h)
  cases D with
  | falsum =>
      cases heq
  | equal s t =>
      cases heq
  | rel R ts =>
      cases heq
  | neg X =>
      cases heq
  | conj X Y =>
      cases heq
  | disj X Y =>
      cases heq
  | impl X Y =>
      cases heq
  | all X =>
      cases heq
      refine Or.inr ⟨F, hF, _, X, scopedTrans (.allBody (.refl X)) hD,
        (fun x => ((Lemmatheca.ProofTheory.FirstOrder.liftScope σ) x).subst
          (Sum.elim (fun v => .var (.inl v)) (fun _ => t.relabel Sum.inl))), ?_⟩
      exact (X.map_comp _ _).symm
  | ex X =>
      cases heq

private theorem analytic_ex_open {δ : Type w'} {Γ : Context L α}
    {C : Formula L α} {B : BF L δ 1}
    (h : AnalyticInstance Γ C δ (.ex B)) :
    AnalyticInstance Γ C (δ ⊕ Fin 1) B.toFormula := by
  obtain ⟨F, hF, n, D, hD, σ, heq⟩ := analytic_instantiated h (by intro h; cases h)
  cases D with
  | falsum =>
      cases heq
  | equal s t =>
      cases heq
  | rel R ts =>
      cases heq
  | neg X =>
      cases heq
  | conj X Y =>
      cases heq
  | disj X Y =>
      cases heq
  | impl X Y =>
      cases heq
  | all X =>
      cases heq
  | ex X =>
      cases heq
      refine Or.inr ⟨F, hF, _, X, scopedTrans (.exBody (.refl X)) hD,
        (fun x => ((Lemmatheca.ProofTheory.FirstOrder.liftScope σ) x).subst
          (fun v => .var (.inl v))), ?_⟩
      exact (X.map_comp _ _).symm

private theorem analytic_ex_instance {δ : Type w'} {Γ : Context L α}
    {C : Formula L α} {B : BF L δ 1}
    (h : AnalyticInstance Γ C δ (.ex B)) (t : L.Term δ) :
    AnalyticInstance Γ C (δ) (B.instantiate t) := by
  obtain ⟨F, hF, n, D, hD, σ, heq⟩ := analytic_instantiated h (by intro h; cases h)
  cases D with
  | falsum =>
      cases heq
  | equal s t =>
      cases heq
  | rel R ts =>
      cases heq
  | neg X =>
      cases heq
  | conj X Y =>
      cases heq
  | disj X Y =>
      cases heq
  | impl X Y =>
      cases heq
  | all X =>
      cases heq
  | ex X =>
      cases heq
      refine Or.inr ⟨F, hF, _, X, scopedTrans (.exBody (.refl X)) hD,
        (fun x => ((Lemmatheca.ProofTheory.FirstOrder.liftScope σ) x).subst
          (Sum.elim (fun v => .var (.inl v)) (fun _ => t.relabel Sum.inl))), ?_⟩
      exact (X.map_comp _ _).symm

private theorem analytic_member {Γ : Context L α} {C A : Formula L α}
    (hA : A ∈ insert C Γ) : AnalyticInstance Γ C α A :=
  Or.inr ⟨A, hA, 0, A, .refl A, Term.var, A.map_id⟩

private theorem insert_analytic {δ : Type w'} {Γ : Context L α} {C : Formula L α}
    {Ξ : Context L δ} {A : Formula L δ}
    (hΞ : ∀ D ∈ Ξ, AnalyticInstance Γ C δ D) (hA : AnalyticInstance Γ C δ A) :
    ∀ D ∈ insert A Ξ, AnalyticInstance Γ C δ D := by
  intro D hD
  rcases Finset.mem_insert.mp hD with rfl | hD
  · exact hA
  · exact hΞ D hD

private theorem lift_analytic {δ : Type w'} {Γ : Context L α} {C : Formula L α}
    {Ξ : Context L δ} (hΞ : ∀ D ∈ Ξ, AnalyticInstance Γ C δ D) :
    ∀ D ∈ liftContext Ξ, AnalyticInstance Γ C (δ ⊕ Fin 1) D := by
  intro D hD
  rcases Finset.mem_image.mp hD with ⟨A, hA, rfl⟩
  exact analytic_rename (hΞ A hA) Sum.inl

private theorem analytic_from {Γ : Context L α} {C : Formula L α}
    {δ : Type w} {Ξ : Context L δ} {D : Formula L δ} (p : CoreProof L Ξ D)
    (hΞ : ∀ A ∈ Ξ, AnalyticInstance Γ C δ A) (hD : AnalyticInstance Γ C δ D) :
    p.Every (fun ε A => AnalyticInstance Γ C ε A) := by
  revert hΞ hD
  induction p with
  | relation R ts hm => intro hΞ hD; exact ⟨hΞ, hD, True.intro⟩
  | falsumLeft hm => intro hΞ hD; exact ⟨hΞ, hD, True.intro⟩
  | conjLeft hm p ih =>
      intro hΞ hD
      have hp := analytic_conj (hΞ _ hm)
      exact ⟨hΞ, hD, ih (insert_analytic (insert_analytic hΞ hp.2) hp.1) hD⟩
  | conjRight p q ihP ihQ =>
      intro hΞ hD
      have hp := analytic_conj hD
      exact ⟨hΞ, hD, ihP hΞ hp.1, ihQ hΞ hp.2⟩
  | disjLeft hm p q ihP ihQ =>
      intro hΞ hD
      have hp := analytic_disj (hΞ _ hm)
      exact ⟨hΞ, hD, ihP (insert_analytic hΞ hp.1) hD,
        ihQ (insert_analytic hΞ hp.2) hD⟩
  | disjRightLeft p ih =>
      intro hΞ hD
      exact ⟨hΞ, hD, ih hΞ (analytic_disj hD).1⟩
  | disjRightRight p ih =>
      intro hΞ hD
      exact ⟨hΞ, hD, ih hΞ (analytic_disj hD).2⟩
  | implLeft hm p q ihP ihQ =>
      intro hΞ hD
      have hp := analytic_impl (hΞ _ hm)
      exact ⟨hΞ, hD, ihP hΞ hp.1, ihQ (insert_analytic hΞ hp.2) hD⟩
  | implRight p ih =>
      intro hΞ hD
      have hp := analytic_impl hD
      exact ⟨hΞ, hD, ih (insert_analytic hΞ hp.1) hp.2⟩
  | negLeft hm p ih =>
      intro hΞ hD
      exact ⟨hΞ, hD, ih hΞ (analytic_neg (hΞ _ hm))⟩
  | negRight p ih =>
      intro hΞ hD
      exact ⟨hΞ, hD, ih (insert_analytic hΞ (analytic_neg hD)) (Or.inl rfl)⟩
  | allLeft t hm p ih =>
      intro hΞ hD
      exact ⟨hΞ, hD, ih (insert_analytic hΞ (analytic_all_instance (hΞ _ hm) t)) hD⟩
  | allRight p ih =>
      intro hΞ hD
      exact ⟨hΞ, hD, ih (lift_analytic hΞ) (analytic_all_open hD)⟩
  | exLeft hm p ih =>
      intro hΞ hD
      exact ⟨hΞ, hD, ih (insert_analytic (lift_analytic hΞ)
        (analytic_ex_open (hΞ _ hm))) (analytic_rename hD Sum.inl)⟩
  | exRight t p ih =>
      intro hΞ hD
      exact ⟨hΞ, hD, ih hΞ (analytic_ex_instance hD t)⟩

theorem CoreProof.analytic {Γ : Context L α} {C : Formula L α} (p : CoreProof L Γ C) :
    p.Every (fun δ A => AnalyticInstance Γ C δ A) := by
  exact analytic_from p (fun A hA => analytic_member (Finset.mem_insert_of_mem hA))
    (analytic_member (Finset.mem_insert_self _ _))

theorem RawCutProof.eliminate_analytic {Γ : Context L α} {C : Formula L α}
    (p : RawCutProof L Γ C) :
    p.eliminate.tree.Every (fun δ A => AnalyticInstance Γ C δ A) := by
  exact p.eliminate.tree.analytic

/-- The original displayed formulas remain the source even under the public reserve. -/
theorem proof_analytic {Γ : Context L α} {C : Formula L α} (p : Proof L Γ C) :
    p.tree.Every (fun δ A => AnalyticInstance Γ C δ A) := by
  apply analytic_from p.tree
  · intro A hA
    rcases Finset.mem_image.mp hA with ⟨B, hB, rfl⟩
    exact analytic_rename (analytic_member (Finset.mem_insert_of_mem hB)) Sum.inl
  · exact analytic_rename (analytic_member (Finset.mem_insert_self C Γ)) Sum.inl

theorem cutCertificate_eliminate_analytic {Γ : Context L α} {C : Formula L α}
    (p : CutCertificate L Γ C) :
    p.eliminate.tree.Every (fun δ A => AnalyticInstance Γ C δ A) := by
  exact proof_analytic p.eliminate

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder
