import Lemmatheca.EqualityFreeFirstOrderSequents.Syntax

/-! Scope and interpretation bridges for the signed view. These are syntax
operations; transformations of sequent certificates are owned separately. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder (ScopeSubst liftScope)
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w w' w'' z
variable {L : Language.{u,v}} {α : Type w} {β : Type w'} {γ : Type w''}

namespace Nnf
@[simp] theorem dual_dual {n} (A : Nnf L α n) : A.dual.dual = A := by
  induction A <;> simp_all [dual]
@[simp] theorem rank_dual {n} (A : Nnf L α n) : A.dual.rank = A.rank := by
  induction A <;> simp_all [dual, rank]

theorem read_equalityFree {n} (A : Nnf L α n) : A.read.EqualityFree := by
  induction A <;> simp_all [read, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree]

@[simp] theorem read_map {n m} (A : Nnf L α n) (σ : ScopeSubst L α β n m) :
    (A.map σ).read = A.read.map σ := by
  induction A generalizing m <;> simp_all [map, read, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map]
@[simp] theorem map_dual {n m} (A : Nnf L α n) (σ : ScopeSubst L α β n m) :
    (A.map σ).dual = A.dual.map σ := by
  induction A generalizing m <;> simp_all [map, dual]
@[simp] theorem rank_map {n m} (A : Nnf L α n) (σ : ScopeSubst L α β n m) :
    (A.map σ).rank = A.rank := by
  induction A generalizing m <;> simp_all [map, rank]
@[simp] theorem quantifierFree_map {n m} (A : Nnf L α n) (σ : ScopeSubst L α β n m) :
    (A.map σ).QuantifierFree ↔ A.QuantifierFree := by
  simp only [QuantifierFree, read_map, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.quantifierFree_map]
@[simp] theorem map_id {n} (A : Nnf L α n) : A.map Term.var = A := by
  induction A <;> simp_all [map, Lemmatheca.ProofTheory.FirstOrder.liftScope_id, term_subst_var]

theorem map_comp {n m k} (A : Nnf L α n)
    (σ : ScopeSubst L α β n m) (τ : ScopeSubst L β γ m k) :
    (A.map σ).map τ = A.map (fun x => (σ x).subst τ) := by
  induction A generalizing m k <;>
    simp_all [map, term_subst_subst, ← Lemmatheca.ProofTheory.FirstOrder.liftScope_comp]

@[simp] theorem read_subst {n} (A : Nnf L α n) (σ : α → L.Term β) :
    (A.subst σ).read = A.read.subst σ := by
  simp only [subst, read_map, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst]
@[simp] theorem read_rename {n} (A : Nnf L α n) (f : α → β) :
    (A.rename f).read = A.read.rename f := by
  simp only [rename, read_subst, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename]
@[simp] theorem read_toFormula {n} (A : Nnf L α n) :
    A.toFormula.read = A.read.toFormula := by
  simp only [toFormula, read_map, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula]
@[simp] theorem read_instantiate (A : Nnf L α 1) (t : L.Term α) :
    (A.instantiate t).read = A.read.instantiate t := by
  simp only [instantiate, instantiateSlots, read_map, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots]
@[simp] theorem dual_subst {n} (A : Nnf L α n) (σ : α → L.Term β) :
    (A.subst σ).dual = A.dual.subst σ := by
  exact map_dual A _
@[simp] theorem dual_rename {n} (A : Nnf L α n) (f : α → β) :
    (A.rename f).dual = A.dual.rename f := by
  exact dual_subst A _
@[simp] theorem dual_toFormula {n} (A : Nnf L α n) :
    A.toFormula.dual = A.dual.toFormula := by
  exact map_dual A _
@[simp] theorem rank_toFormula {n} (A : Nnf L α n) :
    A.toFormula.rank = A.rank := by
  exact rank_map A _

/-- Instantiating the lifted body at the new parameter is exactly opening it. -/
theorem instantiate_rename_fresh (A : Nnf L α 1) :
    (A.rename (Sum.inl : α → α ⊕ Fin 1)).instantiate (.var (.inr 0)) = A.toFormula := by
  unfold rename subst instantiate instantiateSlots toFormula
  rw [map_comp]
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

@[simp] theorem normalize_dual {n} (A : Full L α n) (h : A.EqualityFree) :
    normalize A h false = (normalize A h true).dual := by
  induction A with
  | falsum => rfl
  | equal s t => exact False.elim h
  | rel R ts => rfl
  | neg A ih => simpa only [normalize, Bool.not_true, Bool.not_false] using
      ((congrArg dual (ih h)).trans (dual_dual _)).symm
  | conj A B ihA ihB => simp only [normalize, dual, ihA, ihB]
  | disj A B ihA ihB => simp only [normalize, dual, ihA, ihB]
  | impl A B ihA ihB => simp only [normalize, dual, ihA, ihB, dual_dual]
  | all A ih => exact congrArg ex (ih h)
  | ex A ih => exact congrArg all (ih h)

@[simp] theorem normalize_read {n} (A : Nnf L α n) :
    normalize A.read A.read_equalityFree true = A := by
  induction A <;> simp_all [read, normalize]

theorem normalize_freeVarFinset [DecidableEq α] {n} (A : Full L α n)
    (h : A.EqualityFree) (b : Bool) :
    (normalize A h b).freeVarFinset = A.freeVarFinset := by
  induction A generalizing b with
  | falsum => cases b <;> rfl
  | equal s t => exact False.elim h
  | rel R ts => cases b <;> rfl
  | neg A ih => cases b <;> exact ih h _
  | conj A B ihA ihB =>
      cases b <;> exact congrArg₂ (fun s t : Finset α => s ∪ t) (ihA h.1 _) (ihB h.2 _)
  | disj A B ihA ihB =>
      cases b <;> exact congrArg₂ (fun s t : Finset α => s ∪ t) (ihA h.1 _) (ihB h.2 _)
  | impl A B ihA ihB =>
      cases b <;> exact congrArg₂ (fun s t : Finset α => s ∪ t) (ihA h.1 _) (ihB h.2 _)
  | all A ih => cases b <;> exact ih h _
  | ex A ih => cases b <;> exact ih h _

theorem normalize_quantifierFree {n} (A : Full L α n) (h : A.EqualityFree) (b : Bool) :
    (normalize A h b).QuantifierFree ↔ A.QuantifierFree := by
  induction A generalizing b with
  | falsum => cases b <;> rfl
  | equal s t => exact False.elim h
  | rel R ts => cases b <;> rfl
  | neg A ih => cases b <;> exact ih h _
  | conj A B ihA ihB => cases b <;> exact and_congr (ihA h.1 _) (ihB h.2 _)
  | disj A B ihA ihB => cases b <;> exact and_congr (ihA h.1 _) (ihB h.2 _)
  | impl A B ihA ihB => cases b <;> exact and_congr (ihA h.1 _) (ihB h.2 _)
  | all A ih => cases b <;> rfl
  | ex A ih => cases b <;> rfl

theorem normalize_map {n m} (A : Full L α n) (h : A.EqualityFree)
    (σ : ScopeSubst L α β n m) (b : Bool) :
    normalize (A.map σ) ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map A σ).2 h) b =
      (normalize A h b).map σ := by
  induction A generalizing m b with
  | falsum => cases b <;> rfl
  | equal s t => exact False.elim h
  | rel R ts => cases b <;> rfl
  | neg A ih => cases b <;> exact ih h σ _
  | conj A B ihA ihB => cases b <;> exact congrArg₂ _ (ihA h.1 σ _) (ihB h.2 σ _)
  | disj A B ihA ihB => cases b <;> exact congrArg₂ _ (ihA h.1 σ _) (ihB h.2 σ _)
  | impl A B ihA ihB => cases b <;> exact congrArg₂ _ (ihA h.1 σ _) (ihB h.2 σ _)
  | all A ih => cases b <;> exact congrArg _ (ih h _ _)
  | ex A ih => cases b <;> exact congrArg _ (ih h _ _)

@[simp] theorem subst_id {n} (A : Nnf L α n) : A.subst Term.var = A := by
  have hv : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope
      (Term.var : α → L.Term α) n = Term.var := by
    funext x
    cases x <;> rfl
  simpa only [subst, hv] using A.map_id

theorem subst_comp {n} (A : Nnf L α n) (σ : α → L.Term β) (τ : β → L.Term γ) :
    (A.subst σ).subst τ = A.subst (fun x => (σ x).subst τ) := by
  unfold subst
  rw [map_comp]
  congr 1
  funext x
  cases x with
  | inl a =>
    simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
      Sum.elim_inl, term_subst_relabel, term_relabel_subst]
  | inr i => rfl

@[simp] theorem rename_id {n} (A : Nnf L α n) : A.rename id = A := by
  exact A.subst_id

theorem rename_comp {n} (A : Nnf L α n) (f : α → β) (g : β → γ) :
    (A.rename f).rename g = A.rename (g ∘ f) := by
  simp only [rename, subst_comp, Term.subst, Function.comp_def]

@[simp] theorem subst_all {n} (A : Nnf L α (n+1)) (σ : α → L.Term β) :
    A.all.subst σ = (A.subst σ).all := by
  simp [subst, map]
@[simp] theorem subst_ex {n} (A : Nnf L α (n+1)) (σ : α → L.Term β) :
    A.ex.subst σ = (A.subst σ).ex := by
  simp [subst, map]

theorem toFormula_subst {n} (A : Nnf L α n) (σ : α → L.Term β) :
    (A.subst σ).toFormula =
      A.toFormula.subst (Lemmatheca.MathematicalLogic.FirstOrderProofs.liftSubst σ n) := by
  unfold toFormula subst
  rw [map_comp, map_comp]
  congr 1
  funext x
  cases x <;> simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
    liftSubst, term_subst_vars, Term.subst, Term.relabel_relabel]

theorem instantiate_subst (A : Nnf L α 1) (t : L.Term α) (σ : α → L.Term β) :
    (A.instantiate t).subst σ = (A.subst σ).instantiate (t.subst σ) := by
  unfold instantiate instantiateSlots subst
  rw [map_comp, map_comp]
  congr 1
  funext x
  cases x <;> simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
    term_subst_relabel, term_relabel_subst, term_subst_vars, Term.subst]

variable {M : Type z} [L.Structure M]

theorem realize_dual {n} (A : Nnf L α n) (a : α ⊕ Fin n → M) :
    A.dual.realize a ↔ ¬ A.realize a := by
  classical
  induction A <;> simp_all [dual, realize, read,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize]; tauto

theorem realize_map {n m} (A : Nnf L α n) (σ : ScopeSubst L α β n m)
    (a : β ⊕ Fin m → M) :
    (A.map σ).realize a ↔ A.realize (fun x => (σ x).realize a) := by
  unfold realize
  rw [read_map]
  exact A.read.realize_map σ a

theorem realize_rename (A : Nnf L α 0) (f : α → β) (a : β → M) :
    (A.rename f).Realize a ↔ A.Realize (a ∘ f) := by
  unfold Realize rename subst
  rw [realize_map]
  have h : (fun x : α ⊕ Fin 0 => (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope
      (fun x => (Term.var (f x) : L.Term β)) 0 x).realize (Sum.elim a Fin.elim0)) =
      Sum.elim (a ∘ f) Fin.elim0 := by
    funext x
    cases x with
    | inl x => rfl
    | inr x => exact Fin.elim0 x
  rw [h]

theorem realize_toFormula {n} (A : Nnf L α n) (a : α ⊕ Fin n → M) :
    A.toFormula.Realize a ↔ A.realize a := by
  unfold Realize toFormula
  rw [realize_map]
  rfl

theorem realize_instantiate (A : Nnf L α 1) (t : L.Term α) (a : α → M) :
    (A.instantiate t).Realize a ↔ A.realize (Sum.elim a (fun _ => t.realize a)) := by
  unfold Realize instantiate instantiateSlots
  rw [realize_map]
  have h : (fun x : α ⊕ Fin 1 => (Sum.elim (fun x => (Term.var (Sum.inl x) : L.Term (α ⊕ Fin 0)))
      (fun _ => t.relabel Sum.inl) x).realize (Sum.elim a Fin.elim0)) =
      Sum.elim a (fun _ => t.realize a) := by
    funext x
    cases x <;> simp [Term.realize_relabel, Function.comp_def]
  rw [h]

theorem normalize_realize {n} (A : Full L α n) (h : A.EqualityFree) (b : Bool)
    (a : α ⊕ Fin n → M) :
    (normalize A h b).realize a ↔ if b then A.realize a else ¬ A.realize a := by
  classical
  unfold realize
  induction A generalizing b with
  | falsum => cases b <;> simp [normalize, read, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize]
  | equal s t => exact False.elim h
  | rel R ts => cases b <;> rfl
  | neg A ih =>
      cases b
      · exact (ih h true a).trans not_not.symm
      · exact ih h false a
  | conj A B ihA ihB =>
      cases b <;> simp only [normalize, read,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize]
      · rw [ihA h.1 false a, ihB h.2 false a]; simp only [Bool.false_eq_true, ↓reduceIte]; tauto
      · rw [ihA h.1 true a, ihB h.2 true a]; rfl
  | disj A B ihA ihB =>
      cases b <;> simp only [normalize, read,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize]
      · rw [ihA h.1 false a, ihB h.2 false a]; simp
      · rw [ihA h.1 true a, ihB h.2 true a]; rfl
  | impl A B ihA ihB =>
      cases b <;> simp only [normalize, read,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize]
      · rw [ihA h.1 true a, ihB h.2 false a]; simp
      · rw [ihA h.1 false a, ihB h.2 true a]; simp only [Bool.false_eq_true, ↓reduceIte]; tauto
  | all A ih =>
      cases b <;> simp only [normalize, read,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize]
      · simp only [ih h false, Bool.false_eq_true, ↓reduceIte, not_forall]
      · simp only [ih h true, ↓reduceIte]
  | ex A ih =>
      cases b <;> simp only [normalize, read,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize]
      · simp only [ih h false, Bool.false_eq_true, ↓reduceIte, not_exists]
      · simp only [ih h true, ↓reduceIte]

end Nnf

theorem encode_truth {M : Type z} [L.Structure M]
    (Λ Δ : Finset (EqualityFreeFormula L α)) (a : α → M) :
    SatisfiesSequent (encode Λ Δ) a ↔
      ((∀ F ∈ Λ, F.val.Realize a Fin.elim0) → ∃ F ∈ Δ, F.val.Realize a Fin.elim0) := by
  classical
  constructor
  · rintro ⟨A, hA, h⟩ hΛ
    rcases Finset.mem_union.mp hA with hA | hA
    · rcases Finset.mem_image.mp hA with ⟨F, hF, rfl⟩
      have hn := (Nnf.normalize_realize F.val F.property false (Sum.elim a Fin.elim0)).mp h
      exact False.elim (hn (hΛ F hF))
    · rcases Finset.mem_image.mp hA with ⟨F, hF, rfl⟩
      exact ⟨F, hF, (Nnf.normalize_realize F.val F.property true _).mp h⟩
  · intro h
    by_cases hΛ : ∀ F ∈ Λ, F.val.Realize a Fin.elim0
    · rcases h hΛ with ⟨F,hF,hv⟩
      refine ⟨Nnf.normalize F.val F.property true, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨F,hF,rfl⟩), ?_⟩
      exact (Nnf.normalize_realize F.val F.property true _).mpr hv
    · push Not at hΛ
      rcases hΛ with ⟨F,hF,hv⟩
      refine ⟨Nnf.normalize F.val F.property false, Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨F,hF,rfl⟩), ?_⟩
      exact (Nnf.normalize_realize F.val F.property false _).mpr hv

end Lemmatheca.ProofTheory.ClassicalFirstOrder
