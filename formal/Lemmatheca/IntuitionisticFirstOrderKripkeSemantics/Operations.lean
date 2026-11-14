import Lemmatheca.IntuitionisticFirstOrderKripkeSemantics.Models

namespace Lemmatheca.ProofTheory.FirstOrder.Kripke
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w d a b
variable {L : Language.{u,v}} {W : Type w} [Preorder W]
variable (K : Model.{u,v,w,d} L W) {α : Type a} {β : Type b}

theorem transport_refl (w : W) (s : α → K.Domain w) : K.transport (le_refl w) s = s := by
  funext x
  exact K.map_refl w (s x)

theorem transport_trans {w z t : W} (hwz : w ≤ z) (hzt : z ≤ t) (s : α → K.Domain w) :
    K.transport hzt (K.transport hwz s) = K.transport (le_trans hwz hzt) s := by
  funext x
  exact K.map_trans hwz hzt (s x)

theorem transport_extend {w z : W} (h : w ≤ z) {n}
    (s : α ⊕ Fin n → K.Domain w) (x : K.Domain w) :
    K.transport h (extendAssignment s x) = extendAssignment (K.transport h s) (K.map h x) := by
  funext y
  cases y with
  | inl y => rfl
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Model.transport, extendAssignment]

theorem termValue_transport {w z : W} (h : w ≤ z) (s : α → K.Domain w) (t : L.Term α) :
    K.map h (K.termValue w s t) = K.termValue z (K.transport h s) t := by
  let instw : L.Structure (K.Domain w) := K.structureAt w
  let instz : L.Structure (K.Domain z) := K.structureAt z
  exact (HomClass.realize_term (K.map h)).symm

theorem termValue_subst (w : W) (σ : α → L.Term β) (s : β → K.Domain w) (t : L.Term α) :
    K.termValue w s (t.subst σ) = K.termValue w (fun x => K.termValue w s (σ x)) t := by
  let instw : L.Structure (K.Domain w) := K.structureAt w
  exact Term.realize_subst

theorem termValue_relabel (w : W) (f : α → β) (s : β → K.Domain w) (t : L.Term α) :
    K.termValue w s (t.relabel f) = K.termValue w (s ∘ f) t := by
  let instw : L.Structure (K.Domain w) := K.structureAt w
  exact Term.realize_relabel

theorem forces_mono {n} (A : BoundedFormula L α n) {w z : W} (h : w ≤ z)
    (s : α ⊕ Fin n → K.Domain w) (hA : Forces K A w s) : Forces K A z (K.transport h s) := by
  induction A generalizing w z with
  | falsum => exact hA.elim
  | equal t₁ t₂ =>
      change K.termValue z (K.transport h s) t₁ = K.termValue z (K.transport h s) t₂
      rw [← termValue_transport, ← termValue_transport]
      exact congrArg (K.map h) hA
  | rel R ts =>
      let instw : L.Structure (K.Domain w) := K.structureAt w
      let instz : L.Structure (K.Domain z) := K.structureAt z
      change @Structure.RelMap L (K.Domain z) (K.structureAt z) _ R
        (fun i => K.termValue z (K.transport h s) (ts i))
      have ht : (fun i => K.termValue z (K.transport h s) (ts i)) =
          (fun i => K.map h (K.termValue w s (ts i))) := by
        funext i
        exact (termValue_transport K h s (ts i)).symm
      rw [ht]
      exact (K.map h).map_rel' R (fun i => K.termValue w s (ts i)) hA
  | neg A _ =>
      intro t hzt
      rw [transport_trans]
      exact hA t (le_trans h hzt)
  | conj A B ihA ihB => exact ⟨ihA h s hA.1, ihB h s hA.2⟩
  | disj A B ihA ihB => exact hA.imp (ihA h s) (ihB h s)
  | impl A B _ _ =>
      intro t hzt ht
      rw [transport_trans] at ht ⊢
      exact hA t (le_trans h hzt) ht
  | all A _ =>
      intro t hzt x
      rw [transport_trans]
      exact hA t (le_trans h hzt) x
  | ex A ih =>
      rcases hA with ⟨x,hx⟩
      refine ⟨K.map h x, ?_⟩
      simpa only [transport_extend] using ih h (extendAssignment s x) hx

private theorem transport_zero {w z : W} (h : w ≤ z) (s : α → K.Domain w) :
    K.transport h (Sum.elim s Fin.elim0) = Sum.elim (K.transport h s) Fin.elim0 := by
  funext x
  cases x with
  | inl x => rfl
  | inr i => exact Fin.elim0 i

theorem holds_mono (A : Formula L α) {w z : W} (h : w ≤ z)
    (s : α → K.Domain w) (hA : Holds K w A s) : Holds K z A (K.transport h s) := by
  unfold Holds
  have hp := forces_mono K A h (Sum.elim s Fin.elim0) hA
  simpa only [transport_zero] using hp

/-- Evaluation of the protected lifted scope map keeps its newest slot fixed. -/
theorem termValues_liftScope {n m} (σ : ScopeSubst L α β n m) (w : W)
    (s : β ⊕ Fin m → K.Domain w) (x : K.Domain w) :
    (fun y => K.termValue w (extendAssignment s x) (liftScope σ y)) =
      extendAssignment (fun y => K.termValue w s (σ y)) x := by
  have hi : extendAssignment s x ∘ scopeInclusion m = s := by
    funext y
    cases y with
    | inl y => rfl
    | inr i => simp [extendAssignment, scopeInclusion]
  funext y
  cases y with
  | inl y =>
      change K.termValue w (extendAssignment s x) ((σ (.inl y)).relabel (scopeInclusion m)) = _
      rw [termValue_relabel, hi]
      rfl
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [liftScope, Model.termValue, extendAssignment]
      · simp only [liftScope, Sum.elim_inr, Fin.lastCases_castSucc]
        rw [termValue_relabel, hi]
        simp only [extendAssignment, Sum.elim_inr, Fin.lastCases_castSucc]

private theorem termValues_transport {w z : W} (h : w ≤ z) {n m}
    (σ : ScopeSubst L α β n m) (s : β ⊕ Fin m → K.Domain w) :
    (fun x => K.termValue z (K.transport h s) (σ x)) =
      K.transport h (fun x => K.termValue w s (σ x)) := by
  funext x
  exact (termValue_transport K h s (σ x)).symm

theorem forces_map {n m} (A : BoundedFormula L α n) (σ : ScopeSubst L α β n m)
    (w : W) (s : β ⊕ Fin m → K.Domain w) :
    Forces K (A.map σ) w s ↔ Forces K A w (fun x => K.termValue w s (σ x)) := by
  induction A generalizing m w with
  | falsum => rfl
  | equal t₁ t₂ => simp only [BoundedFormula.map, Forces, termValue_subst]
  | rel R ts => simp only [BoundedFormula.map, Forces, termValue_subst]
  | neg A ih => simp only [BoundedFormula.map, Forces, ih, termValues_transport]
  | conj A B ihA ihB => exact and_congr (ihA σ w s) (ihB σ w s)
  | disj A B ihA ihB => exact or_congr (ihA σ w s) (ihB σ w s)
  | impl A B ihA ihB =>
      simp only [BoundedFormula.map, Forces, ihA, ihB, termValues_transport]
  | all A ih =>
      simp only [BoundedFormula.map, Forces, ih, termValues_liftScope, termValues_transport]
  | ex A ih => simp only [BoundedFormula.map, Forces, ih, termValues_liftScope]

theorem holds_subst (A : Formula L α) (σ : α → L.Term β) (w : W) (s : β → K.Domain w) :
    Holds K w (A.subst σ) s ↔ Holds K w A (fun x => K.termValue w s (σ x)) := by
  unfold Holds BoundedFormula.subst
  rw [forces_map]
  have hv : (fun x : α ⊕ Fin 0 =>
      K.termValue w (Sum.elim s Fin.elim0) (BoundedFormula.freeScope σ 0 x)) =
      Sum.elim (fun x => K.termValue w s (σ x)) Fin.elim0 := by
    funext x
    cases x with
    | inl x =>
        simp only [BoundedFormula.freeScope, Sum.elim_inl, termValue_relabel]
        rfl
    | inr i => exact Fin.elim0 i
  rw [hv]

theorem holds_rename (A : Formula L α) (f : α → β) (w : W) (s : β → K.Domain w) :
    Holds K w (A.rename f) s ↔ Holds K w A (s ∘ f) := by
  simpa only [BoundedFormula.rename, Model.termValue, Term.realize_var,
    Function.comp_def] using holds_subst K A (fun x => .var (f x)) w s

theorem holds_open (B : BoundedFormula L α 1) (w : W) (s : α → K.Domain w) (x : K.Domain w) :
    Holds K w B.toFormula (Sum.elim s (fun _ => x)) ↔ Forces K B w (Sum.elim s (fun _ => x)) := by
  unfold Holds BoundedFormula.toFormula
  rw [forces_map]
  rfl

theorem holds_instantiate (B : BoundedFormula L α 1) (t : L.Term α) (w : W) (s : α → K.Domain w) :
    Holds K w (B.instantiate t) s ↔ Forces K B w (Sum.elim s (fun _ => K.termValue w s t)) := by
  unfold Holds BoundedFormula.instantiate BoundedFormula.instantiateSlots
  rw [forces_map]
  have hv : (fun x : α ⊕ Fin 1 => K.termValue w (Sum.elim s Fin.elim0)
      (Sum.elim (fun x => (Term.var (Sum.inl x) : L.Term (α ⊕ Fin 0)))
        (fun _ => t.relabel Sum.inl) x)) =
      Sum.elim s (fun _ => K.termValue w s t) := by
    funext x
    cases x <;> simp only [Sum.elim_inl, Sum.elim_inr, termValue_relabel] <;> rfl
  rw [hv]

private theorem extend_zero {M : Type*} (s : α → M) (x : M) :
    extendAssignment (Sum.elim s Fin.elim0) x = Sum.elim s (fun _ : Fin 1 => x) := by
  funext y
  cases y with
  | inl y => rfl
  | inr i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl

theorem holds_all (B : BoundedFormula L α 1) (w : W) (s : α → K.Domain w) :
    Holds K w (.all B) s ↔ ∀ z (h : w ≤ z) (x : K.Domain z),
      Forces K B z (Sum.elim (K.transport h s) (fun _ => x)) := by
  unfold Holds
  simp only [Forces, transport_zero, extend_zero]

theorem holds_ex (B : BoundedFormula L α 1) (w : W) (s : α → K.Domain w) :
    Holds K w (.ex B) s ↔ ∃ x : K.Domain w, Forces K B w (Sum.elim s (fun _ => x)) := by
  unfold Holds
  simp only [Forces, extend_zero]

theorem holds_termEqual (s t : L.Term α) (w : W) (a : α → K.Domain w) :
    Holds K w (NaturalDeduction.termEqual s t) a ↔ K.termValue w a s = K.termValue w a t := by
  unfold Holds NaturalDeduction.termEqual
  simp only [Forces, termValue_relabel]
  rfl

end Lemmatheca.ProofTheory.FirstOrder.Kripke
