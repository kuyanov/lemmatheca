import Lemmatheca.EqualityFreeIntuitionisticFirstOrderKripkeCompleteness.Canonical

namespace Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v a
noncomputable section
variable {L : Language.{u,v}} {α : Type a}

/-- Open all currently available slots, then substitute the erased assigned term trees. -/
def groundInstance {n : ℕ} (A : BoundedFormula L α n) (w : World L)
    (s : α ⊕ Fin n → Domain w) : PrimeHenkin.Fml L :=
  A.toFormula.subst (erase ∘ s)

/-- Ground old free names and old slots while keeping the newest bound slot protected. -/
def groundBody {n : ℕ} (B : BoundedFormula L α (n+1)) (w : World L)
    (s : α ⊕ Fin n → Domain w) : PrimeHenkin.Body L :=
  B.map (Sum.elim (fun x => (erase (s (.inl x))).relabel Sum.inl)
    (Fin.lastCases (.var (.inr 0)) (fun i => (erase (s (.inr i))).relabel Sum.inl)))

private theorem ground_map {n : ℕ} (A : BoundedFormula L α n) (w : World L)
    (s : α ⊕ Fin n → Domain w) :
    groundInstance A w s = A.map (fun x => (erase (s x)).relabel Sum.inl) := by
  unfold groundInstance BoundedFormula.toFormula BoundedFormula.subst
  rw [BoundedFormula.map_comp]
  rfl

private theorem ground_lift {n : ℕ} (w : World L) (s : α ⊕ Fin n → Domain w) :
    liftScope (fun x => (erase (s x)).relabel Sum.inl : ScopeSubst L α ℕ n 0) =
      Sum.elim (fun x => (erase (s (.inl x))).relabel Sum.inl)
        (Fin.lastCases (.var (.inr 0)) (fun i => (erase (s (.inr i))).relabel Sum.inl)) := by
  funext x
  cases x with
  | inl x => simp only [liftScope,Sum.elim_inl,Term.relabel_relabel]; rfl
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [liftScope_last,Sum.elim_inr,Fin.lastCases_last]
        rfl
      · simp only [Sum.elim_inr,Fin.lastCases_castSucc]
        rw [show liftScope (fun x => (erase (s x)).relabel Sum.inl : ScopeSubst L α ℕ n 0) (.inr j.castSucc) =
          ((erase (s (.inr j))).relabel Sum.inl).relabel (scopeInclusion 0) from
          liftScope_inclusion _ (.inr j)]
        simp only [Term.relabel_relabel]
        rfl

theorem ground_equalityFree {n : ℕ} (A : BoundedFormula L α n) (w : World L)
    (s : α ⊕ Fin n → Domain w) : (groundInstance A w s).EqualityFree ↔ A.EqualityFree := by
  simp only [ground_map,BoundedFormula.equalityFree_map]

theorem ground_supported {n : ℕ} (A : BoundedFormula L α n) (w : World L)
    (s : α ⊕ Fin n → Domain w) :
    PrimeHenkin.Supported w.parameters.carrier (groundInstance A w s) := by
  classical
  intro c hc
  unfold groundInstance at hc
  rw [BoundedFormula.freeVarFinset_subst] at hc
  obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hc
  exact erase_supported (s x) c hx

theorem body_equalityFree {n : ℕ} (B : BoundedFormula L α (n+1)) (w : World L)
    (s : α ⊕ Fin n → Domain w) : (groundBody B w s).EqualityFree ↔ B.EqualityFree := by
  exact B.equalityFree_map _

theorem ground_falsum {n : ℕ} (w : World L) (s : α ⊕ Fin n → Domain w) :
    groundInstance (.falsum : BoundedFormula L α n) w s = .falsum := by
  rfl

theorem ground_relation {n k : ℕ} (R : L.Relations k)
    (ts : Fin k → L.Term (α ⊕ Fin n)) (w : World L) (s : α ⊕ Fin n → Domain w) :
    groundInstance (.rel R ts) w s =
      .rel R (fun i => ((ts i).subst (erase ∘ s)).relabel Sum.inl) := by
  rw [ground_map]
  change BoundedFormula.rel R (fun i => (ts i).subst (fun x => (erase (s x)).relabel Sum.inl)) = _
  congr 1
  funext i
  exact (term_relabel_subst (ts i) (erase ∘ s) Sum.inl).symm

theorem ground_neg {n : ℕ} (A : BoundedFormula L α n) (w : World L)
    (s : α ⊕ Fin n → Domain w) :
    groundInstance (.neg A) w s = .neg (groundInstance A w s) := by
  rfl

theorem ground_conj {n : ℕ} (A B : BoundedFormula L α n) (w : World L)
    (s : α ⊕ Fin n → Domain w) :
    groundInstance (.conj A B) w s = .conj (groundInstance A w s) (groundInstance B w s) := by
  rfl

theorem ground_disj {n : ℕ} (A B : BoundedFormula L α n) (w : World L)
    (s : α ⊕ Fin n → Domain w) :
    groundInstance (.disj A B) w s = .disj (groundInstance A w s) (groundInstance B w s) := by
  rfl

theorem ground_impl {n : ℕ} (A B : BoundedFormula L α n) (w : World L)
    (s : α ⊕ Fin n → Domain w) :
    groundInstance (.impl A B) w s = .impl (groundInstance A w s) (groundInstance B w s) := by
  rfl

theorem ground_all {n : ℕ} (B : BoundedFormula L α (n+1)) (w : World L)
    (s : α ⊕ Fin n → Domain w) :
    groundInstance (.all B) w s = .all (groundBody B w s) := by
  rw [ground_map]
  simp only [BoundedFormula.map,ground_lift,groundBody]

theorem ground_ex {n : ℕ} (B : BoundedFormula L α (n+1)) (w : World L)
    (s : α ⊕ Fin n → Domain w) :
    groundInstance (.ex B) w s = .ex (groundBody B w s) := by
  rw [ground_map]
  simp only [BoundedFormula.map,ground_lift,groundBody]

theorem body_supported {n : ℕ} (B : BoundedFormula L α (n+1)) (w : World L)
    (s : α ⊕ Fin n → Domain w) :
    PrimeHenkin.Supported w.parameters.carrier (groundBody B w s) := by
  have h := ground_supported (.ex B) w s
  rw [ground_ex] at h
  exact h

theorem ground_extend {n : ℕ} (B : BoundedFormula L α (n+1)) (w : World L)
    (s : α ⊕ Fin n → Domain w) (t : Domain w) :
    groundInstance B w (extendAssignment s t) = (groundBody B w s).instantiate (erase t) := by
  rw [ground_map]
  unfold groundBody BoundedFormula.instantiate BoundedFormula.instantiateSlots
  rw [BoundedFormula.map_comp]
  congr 1
  funext x
  cases x with
  | inl x =>
      simp only [Sum.elim_inl,term_subst_relabel,extendAssignment]
      rw [term_subst_vars]
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Sum.elim_inr,Fin.lastCases_last,Term.subst,extendAssignment]
      · simp only [Sum.elim_inr,Fin.lastCases_castSucc,term_subst_relabel,extendAssignment,Sum.elim_inl]
        rw [term_subst_vars]

theorem ground_transition {n : ℕ} (A : BoundedFormula L α n) {w z : World L}
    (h : w ≤ z) (s : α ⊕ Fin n → Domain w) :
    groundInstance A z (transition h ∘ s) = groundInstance A w s := by
  unfold groundInstance
  congr 1
  funext x
  exact erase_transition h (s x)

theorem body_transition {n : ℕ} (B : BoundedFormula L α (n+1)) {w z : World L}
    (h : w ≤ z) (s : α ⊕ Fin n → Domain w) :
    groundBody B z (transition h ∘ s) = groundBody B w s := by
  unfold groundBody
  congr 1
  funext x
  cases x with
  | inl x => simp only [Sum.elim_inl,Function.comp_apply,erase_transition]
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i <;>
        simp only [Sum.elim_inr,Fin.lastCases_last,Fin.lastCases_castSucc,Function.comp_apply,erase_transition]

variable [Countable L.Symbols]

theorem term_value (w : World L) (s : α → Domain w) (t : L.Term α) :
    Kripke.Model.termValue canonicalModel w s t = t.subst s := by
  induction t with
  | var x => rfl
  | func f ts ih =>
      change Term.func f (fun i => Kripke.Model.termValue canonicalModel w s (ts i)) = Term.func f (fun i => (ts i).subst s)
      congr 1
      funext i
      exact ih i

theorem erase_term_value (w : World L) (s : α → Domain w) (t : L.Term α) :
    erase (Kripke.Model.termValue canonicalModel w s t) = t.subst (erase ∘ s) := by
  rw [term_value]
  exact term_relabel_subst t s Subtype.val

end
end Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
