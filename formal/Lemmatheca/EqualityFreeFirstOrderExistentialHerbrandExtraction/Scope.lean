import Lemmatheca.EqualityFreeFirstOrderExistentialHerbrandExtraction.Syntax

/-! Exact scope and tuple identities for the weak fragment. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder.ExistentialHerbrand
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder (ScopeSubst)
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w w'
variable {L : Language.{u,v}} {α : Type w} {β : Type w'}
noncomputable section

private theorem weak_cast {n m} (e : n = m) (A : Nnf L α n) :
    Weak (e ▸ A) ↔ Weak A := by subst m; rfl

private theorem proper_cast {n m} (e : n = m) (A : Nnf L α n) :
    ProperWeak (e ▸ A) ↔ ProperWeak A := by subst m; rfl

private theorem subst_cast {n m} (e : n = m) (A : Nnf L α n) (σ : α → L.Term β) :
    (e ▸ A).subst σ = e ▸ (A.subst σ) := by subst m; rfl

private def castF {n m} (e : n = m) (A : Nnf L α n) : Nnf L α m := e ▸ A

private theorem castF_ex {n m} (e : n = m) (A : Nnf L α (n+1)) :
    castF e (.ex A) = .ex (castF (congrArg (· + 1) e) A) := by subst m; rfl

private theorem bindExists_front (k m) (A : Nnf L α (m+(k+1))) :
    bindExists (k+1) A = .ex (bindExists k (castF (by omega) A)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change bindExists (k+1) (.ex A) = .ex (bindExists k (.ex (castF _ A)))
    rw [ih]
    rw [castF_ex]

/-- Lift a scope action through a specified finite final block. -/
def liftMany : (k : ℕ) → {n m : ℕ} → ScopeSubst L α β n m → ScopeSubst L α β (n+k) (m+k)
  | 0, _, _, σ => σ
  | k+1, _, _, σ => Lemmatheca.ProofTheory.FirstOrder.liftScope (liftMany k σ)

private theorem liftMany_free (k) {n m} (σ : ScopeSubst L α β n m) (a : α) :
    liftMany k σ (.inl a) = (σ (.inl a)).relabel (Sum.map id (Fin.castAdd k)) := by
  induction k with
  | zero => simpa only [liftMany, Fin.castAdd_zero, Fin.cast_refl, Sum.map_id_id, id_eq] using (Term.relabel_id (σ (.inl a))).symm
  | succ k ih =>
    simp only [liftMany, Lemmatheca.ProofTheory.FirstOrder.liftScope, Sum.elim_inl, ih,
      Term.relabel_relabel]
    congr 1
    funext x
    cases x <;> rfl

private theorem liftMany_old (k) {n m} (σ : ScopeSubst L α β n m) (i : Fin n) :
    liftMany k σ (.inr (Fin.castAdd k i)) =
      (σ (.inr i)).relabel (Sum.map id (Fin.castAdd k)) := by
  induction k with
  | zero => simpa only [liftMany, Fin.castAdd_zero, Fin.cast_refl, Sum.map_id_id, id_eq] using (Term.relabel_id (σ (.inr i))).symm
  | succ k ih =>
    rw [← Fin.castSucc_castAdd]
    simp only [liftMany, Lemmatheca.ProofTheory.FirstOrder.liftScope, Sum.elim_inr,
      Fin.lastCases_castSucc, ih, Term.relabel_relabel]
    congr 1
    funext x
    cases x <;> rfl

private theorem liftMany_new (k) {n m} (σ : ScopeSubst L α β n m) (i : Fin k) :
    liftMany k σ (.inr (Fin.natAdd n i)) = .var (.inr (Fin.natAdd m i)) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change Lemmatheca.ProofTheory.FirstOrder.liftScope (liftMany k σ) (.inr (Fin.last (n+k))) = _
      simp only [Lemmatheca.ProofTheory.FirstOrder.liftScope, Sum.elim_inr, Fin.lastCases_last]
      rfl
    · change Lemmatheca.ProofTheory.FirstOrder.liftScope (liftMany k σ) (.inr (Fin.natAdd n j).castSucc) = _
      simp only [Lemmatheca.ProofTheory.FirstOrder.liftScope, Sum.elim_inr, Fin.lastCases_castSucc, ih]
      rfl

/-- Exact action through the stored existential prefix. -/
theorem bindExists_map (k) {n m} (A : Nnf L α (n+k)) (σ : ScopeSubst L α β n m) :
    (bindExists k A).map σ = bindExists k (A.map (liftMany k σ)) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (.ex A)

theorem bindForall_map (k) {n m} (A : Nnf L α (n+k)) (σ : ScopeSubst L α β n m) :
    (bindForall k A).map σ = bindForall k (A.map (liftMany k σ)) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (.all A)

/-- The outermost universal is the earliest available slot. -/
theorem bindForall_front (k m) (A : Nnf L α (m+(k+1))) :
    bindForall (k+1) A = .all (bindForall k ((by omega : m+(k+1) = (m+1)+k) ▸ A)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change bindForall (k+1) (.all A) = .all (bindForall k (.all ((by omega : m+(k+1+1) = (m+1)+(k+1)) ▸ A)))
    rw [ih]
    have hc : ∀ {a b} (e : a = b) (B : Nnf L α (a+1)),
        e ▸ Nnf.all B = Nnf.all ((congrArg (· + 1) e) ▸ B) := by
      intro a b e B; subst b; rfl
    rw [hc]

theorem weak_of_quantifierFree {n} (A : Nnf L α n) (h : A.QuantifierFree) :
    Weak A := by
  induction A with
  | pos => trivial
  | neg => trivial
  | bot => trivial
  | top => trivial
  | and A B ihA ihB => exact h
  | or A B ihA ihB => exact h
  | all A ih => exact False.elim h
  | ex A ih => exact False.elim h

theorem weak_map {n m} (A : Nnf L α n) (σ : ScopeSubst L α β n m) :
    Weak (A.map σ) ↔ Weak A := by
  induction A generalizing m β with
  | pos => exact Iff.rfl
  | neg => exact Iff.rfl
  | bot => exact Iff.rfl
  | top => exact Iff.rfl
  | and A B ihA ihB =>
    exact and_congr (Nnf.quantifierFree_map A σ) (Nnf.quantifierFree_map B σ)
  | or A B ihA ihB =>
    exact and_congr (Nnf.quantifierFree_map A σ) (Nnf.quantifierFree_map B σ)
  | all A ih => exact Iff.rfl
  | ex A ih => exact ih (Lemmatheca.ProofTheory.FirstOrder.liftScope σ)

theorem properWeak_map {n m} (A : Nnf L α n) (σ : ScopeSubst L α β n m) :
    ProperWeak (A.map σ) ↔ ProperWeak A := by
  cases A <;> try exact Iff.rfl
  exact weak_map _ _

theorem existsBlock_weak {n} (A : Nnf L α n) (h : A.QuantifierFree) :
    Weak (existsBlock A) := by
  have aux : ∀ k {m} (B : Nnf L α (m+k)), Weak B → Weak (bindExists k B) := by
    intro k
    induction k with
    | zero => intro m B hB; exact hB
    | succ k ih => intro m B hB; exact ih (.ex B) hB
  exact aux n _ ((weak_cast _ A).mpr (weak_of_quantifierFree A h))

theorem existsBlock_proper {n} (A : Nnf L α n) (h : A.QuantifierFree) (hn : 0 < n) :
    ProperWeak (existsBlock A) := by
  have aux : ∀ k {m} (B : Nnf L α (m+k)), ProperWeak B → ProperWeak (bindExists k B) := by
    intro k
    induction k with
    | zero => intro m B hB; exact hB
    | succ k ih =>
      intro m B hB
      have hW : Weak B := by cases B <;> simp_all [ProperWeak, Weak]
      exact ih (.ex B) hW
  cases n with
  | zero => omega
  | succ n => exact aux n _ ((weak_cast _ A).mpr (weak_of_quantifierFree A h))

theorem existsBlock_subst {n} (A : Nnf L α n) (σ : α → L.Term β) :
    (existsBlock A).subst σ = existsBlock (A.subst σ) := by
  have aux : ∀ k {m} (B : Nnf L α (m+k)),
      (bindExists k B).subst σ = bindExists k (B.subst σ) := by
    intro k
    induction k with
    | zero => intro m B; rfl
    | succ k ih => intro m B; simpa only [bindExists, Nnf.subst_ex] using ih (.ex B)
  simpa only [existsBlock, subst_cast] using aux n (m := 0) ((Nat.zero_add n).symm ▸ A)

theorem forallBlock_subst {n} (A : Nnf L α n) (σ : α → L.Term β) :
    (forallBlock A).subst σ = forallBlock (A.subst σ) := by
  have aux : ∀ k {m} (B : Nnf L α (m+k)),
      (bindForall k B).subst σ = bindForall k (B.subst σ) := by
    intro k
    induction k with
    | zero => intro m B; rfl
    | succ k ih => intro m B; simpa only [bindForall, Nnf.subst_all] using ih (.all B)
  simpa only [forallBlock, subst_cast] using aux n (m := 0) ((Nat.zero_add n).symm ▸ A)

theorem Witness.value_quantifierFree {F : Nnf L α 0} (w : Witness F) :
    w.value.QuantifierFree := by
  induction w with
  | terminal A h => exact h
  | step B t w ih => exact ih

private theorem castF_comp {a b c} (e : a = b) (e' : b = c) (A : Nnf L α a) :
    castF e' (castF e A) = castF (e.trans e') A := by subst b; subst c; rfl

private theorem castF_qf {a b} (e : a = b) (A : Nnf L α a) :
    (castF e A).QuantifierFree ↔ A.QuantifierFree := by subst b; rfl

private def frontBody {n} (A : Nnf L α (n+1)) : Nnf L α 1 :=
  bindExists n (castF (by omega : n+1 = 1+n) A)

private theorem existsBlock_front {n} (A : Nnf L α (n+1)) :
    existsBlock A = .ex (frontBody A) := by
  change bindExists (n+1) (castF _ A) = _
  rw [bindExists_front]
  simp only [frontBody, castF_comp]

private def firstSubst (t : L.Term α) : ScopeSubst L α α 1 0 :=
  Sum.elim (fun a => .var (.inl a)) (fun _ => t.relabel Sum.inl)

private def dropFirst {n} (A : Nnf L α (n+1)) (t : L.Term α) : Nnf L α n :=
  castF (Nat.zero_add n) ((castF (by omega : n+1 = 1+n) A).map (liftMany n (firstSubst t)))

private theorem front_instance {n} (A : Nnf L α (n+1)) (t : L.Term α) :
    (frontBody A).instantiate t = existsBlock (dropFirst A t) := by
  change (bindExists n _).map (firstSubst t) = _
  rw [bindExists_map]
  change bindExists n _ = bindExists n (castF _ (castF _ _))
  rw [castF_comp]
  rfl

private theorem dropFirst_qf {n} (A : Nnf L α (n+1)) (h : A.QuantifierFree) (t : L.Term α) :
    (dropFirst A t).QuantifierFree := by
  exact (castF_qf _ _).mpr ((Nnf.quantifierFree_map _ _).mpr ((castF_qf _ _).mpr h))

private theorem castF_source {a b d} (e : a = b) (A : Nnf L α a)
    (σ : ScopeSubst L α β b d) :
    (castF e A).map σ = A.map (fun x => σ (Sum.map id (Fin.cast e) x)) := by
  subst b
  apply congrArg (fun τ : ScopeSubst L α β a d => A.map τ)
  funext x
  cases x <;> rfl

private theorem dropFirst_slots {n} (A : Nnf L α (n+1)) (t : L.Term α)
    (ts : Fin n → L.Term α) :
    (dropFirst A t).instantiateSlots ts = A.instantiateSlots (Fin.cons t ts) := by
  unfold dropFirst Nnf.instantiateSlots
  rw [castF_source, Nnf.map_comp, castF_source]
  congr 1
  funext x
  cases x with
  | inl a =>
    simp only [Sum.map_inl, id_eq, liftMany_free, firstSubst, Sum.elim_inl,
      Term.relabel, Term.subst]
  | inr i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · have hi : Fin.cast (by omega : n+1 = 1+n) (0 : Fin (n+1)) = Fin.castAdd n (0 : Fin 1) := by
        apply Fin.ext; rfl
      simp only [Sum.map_inr, hi, liftMany_old, firstSubst, Sum.elim_inr, Fin.cons_zero,
        Term.relabel_relabel]
      simp only [term_subst_relabel, Function.comp_apply, Sum.map_inl, id_eq,
        Sum.elim_inl, term_subst_vars]
    · have hi : Fin.cast (by omega : n+1 = 1+n) j.succ = Fin.natAdd 1 j := by
        apply Fin.ext; simp; omega
      simp only [Sum.map_inr, hi, liftMany_new, Term.subst, Sum.elim_inr, Fin.cons_succ]
      congr 1
      have hj : Fin.cast (Nat.zero_add n) (Fin.natAdd 0 j) = j := by apply Fin.ext; simp
      exact congrArg ts hj

private theorem terms_cast {F G : Nnf L α 0} (e : F = G) (w : Witness F) :
    (e ▸ w).terms = w.terms := by subst G; rfl

private theorem value_cast {F G : Nnf L α 0} (e : F = G) (w : Witness F) :
    (e ▸ w).value = w.value := by subst G; rfl

private theorem slots_zero (A : Nnf L α 0) : A.instantiateSlots Fin.elim0 = A := by
  unfold Nnf.instantiateSlots
  have he : (Sum.elim (fun x => Term.var (Sum.inl x))
      (fun i : Fin 0 => (Fin.elim0 i : L.Term α).relabel Sum.inl)) = Term.var := by
    funext x
    cases x with
    | inl a => rfl
    | inr i => exact Fin.elim0 i
  rw [he, Nnf.map_id]

private def decodeTuple : ∀ {n} (A : Nnf L α n) (_h : A.QuantifierFree)
    (w : Witness (existsBlock A)),
    {ts : Fin n → L.Term α // List.ofFn ts = w.terms ∧ w.value = A.instantiateSlots ts} := by
  intro n
  induction n with
  | zero =>
    intro A h w
    change Witness A at w
    cases w with
    | terminal A hA => exact ⟨Fin.elim0, rfl, (slots_zero A).symm⟩
    | step B t w => exact False.elim h
  | succ n ih =>
    intro A h w
    let w' : Witness (.ex (frontBody A)) := (existsBlock_front A) ▸ w
    have ht : w'.terms = w.terms := terms_cast _ w
    have hv : w'.value = w.value := value_cast _ w
    suffices r : {ts : Fin (n+1) → L.Term α //
        List.ofFn ts = w'.terms ∧ w'.value = A.instantiateSlots ts} from
      ⟨r.val, r.property.1.trans ht, hv.symm.trans r.property.2⟩
    cases w' with
    | terminal F hF => exact False.elim hF
    | step B t ww =>
      let wNext : Witness (existsBlock (dropFirst A t)) := (front_instance A t) ▸ ww
      obtain ⟨ts, hts, hval⟩ := ih (dropFirst A t) (dropFirst_qf A h t) wNext
      refine ⟨Fin.cons t ts, ?_, ?_⟩
      · rw [List.ofFn_cons, hts]
        exact congrArg (List.cons t) (terms_cast _ ww)
      · change ww.value = _
        rw [← value_cast (front_instance A t) ww, hval, dropFirst_slots]

private def encodeTuple : ∀ {n} (A : Nnf L α n) (_h : A.QuantifierFree)
    (ts : Fin n → L.Term α),
    {w : Witness (existsBlock A) // w.terms = List.ofFn ts} := by
  intro n
  induction n with
  | zero =>
    intro A h ts
    exact ⟨.terminal A h, by simp [Witness.terms]⟩
  | succ n ih =>
    intro A h ts
    let t := ts 0
    let tail := fun i : Fin n => ts i.succ
    obtain ⟨ww, hww⟩ := ih (dropFirst A t) (dropFirst_qf A h t) tail
    let inner : Witness ((frontBody A).instantiate t) := (front_instance A t).symm ▸ ww
    let outer : Witness (.ex (frontBody A)) := .step (frontBody A) t inner
    refine ⟨(existsBlock_front A).symm ▸ outer, ?_⟩
    rw [terms_cast]
    change t :: inner.terms = List.ofFn ts
    rw [terms_cast, hww, List.ofFn_succ]

/-- Read exactly the successive stored terms, beginning at outermost slot zero. -/
def Witness.tuple {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (w : Witness (existsBlock A)) : Fin n → L.Term α := by
  exact (decodeTuple A h w).val

theorem Witness.tuple_terms {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (w : Witness (existsBlock A)) :
    List.ofFn (w.tuple A h) = w.terms := by
  exact (decodeTuple A h w).property.1

theorem Witness.value_tuple {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (w : Witness (existsBlock A)) :
    w.value = A.instantiateSlots (w.tuple A h) := by
  exact (decodeTuple A h w).property.2

/-- The record constructed with precisely this supplied ordered tuple. -/
def Witness.ofTuple {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (ts : Fin n → L.Term α) : Witness (existsBlock A) := by
  exact (encodeTuple A h ts).val

theorem Witness.tuple_ofTuple {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (ts : Fin n → L.Term α) :
    (Witness.ofTuple A h ts).tuple A h = ts := by
  apply List.ofFn_injective
  rw [Witness.tuple_terms]
  exact (encodeTuple A h ts).property

theorem embed_propositionalize (A : Nnf L α 0) (h : A.QuantifierFree) :
    embed (propositionalize A) = A := by
  have aux : ∀ {n} (B : Nnf L α n) (e : n = 0), B.QuantifierFree →
      embed (propositionalize (e ▸ B)) = e ▸ B := by
    intro n B
    induction B with
    | @pos n k R ts =>
      intro e hB; subst n
      simp only [propositionalize, embed, Term.relabel_relabel]
      congr 1
      funext i
      have hf : (Sum.inl ∘ Sum.elim id (Fin.elim0 : Fin 0 → α)) = id := by
        funext x; cases x with
        | inl a => rfl
        | inr j => exact Fin.elim0 j
      rw [hf, Term.relabel_id]
    | @neg n k R ts =>
      intro e hB; subst n
      simp only [propositionalize, embed, Term.relabel_relabel]
      congr 1
      funext i
      have hf : (Sum.inl ∘ Sum.elim id (Fin.elim0 : Fin 0 → α)) = id := by
        funext x; cases x with
        | inl a => rfl
        | inr j => exact Fin.elim0 j
      rw [hf, Term.relabel_id]
    | @bot n => intro e hB; subst n; simp only [embed, propositionalize]
    | @top n => intro e hB; subst n; simp only [embed, propositionalize]
    | @and n A B ihA ihB =>
      intro e hB; subst n
      simpa only [propositionalize, embed] using congrArg₂ Nnf.and (ihA rfl hB.1) (ihB rfl hB.2)
    | @or n A B ihA ihB =>
      intro e hB; subst n
      simpa only [propositionalize, embed] using congrArg₂ Nnf.or (ihA rfl hB.1) (ihB rfl hB.2)
    | all A ih => intro e hB; exact False.elim hB
    | ex A ih => intro e hB; exact False.elim hB
  exact aux A rfl h

theorem propositionalize_embed (A : PropNnf (Atom L α)) :
    propositionalize (embed A) = A := by
  induction A with
  | pos a =>
    cases a
    simp [embed, propositionalize, Term.relabel_relabel, Function.comp_def]
    funext i
    exact Term.relabel_id _
  | neg a =>
    cases a
    simp [embed, propositionalize, Term.relabel_relabel, Function.comp_def]
    funext i
    exact Term.relabel_id _
  | bot => simp only [embed, propositionalize]
  | top => simp only [embed, propositionalize]
  | and A B ihA ihB => simpa only [embed, propositionalize] using congrArg₂ ClassicalPropositional.Nnf.and ihA ihB
  | or A B ihA ihB => simpa only [embed, propositionalize] using congrArg₂ ClassicalPropositional.Nnf.or ihA ihB

theorem embed_quantifierFree (A : PropNnf (Atom L α)) :
    (embed A).QuantifierFree := by
  induction A with
  | pos => trivial
  | neg => trivial
  | bot => trivial
  | top => trivial
  | and A B ihA ihB => exact ⟨ihA, ihB⟩
  | or A B ihA ihB => exact ⟨ihA, ihB⟩

/-- Open just the universal prefix, leaving the following existential slots available. -/
def openUniversalMatrix {k n} (A : Nnf L α (k+n)) : Nnf L (α ⊕ Fin k) n :=
  A.map (Sum.elim (fun a => .var (.inl (.inl a)))
    (Fin.addCases (fun i => .var (.inl (.inr i))) (fun i => .var (.inr i))))

private theorem castF_map {a b d} (e : a = b) (A : Nnf L α d)
    {γ : Type*} (σ : ScopeSubst L α γ d a) :
    castF e (A.map σ) =
      A.map (fun x => (σ x).relabel (Sum.map id (Fin.cast e))) := by
  subst b
  apply congrArg (fun τ : ScopeSubst L α γ d a => A.map τ)
  funext x
  have he : Sum.map id (Fin.cast (rfl : a = a)) = (id : γ ⊕ Fin a → γ ⊕ Fin a) := by
    funext y; cases y <;> rfl
  rw [he, Term.relabel_id]

/-- Open the earlier slots through the full remaining existential prefix. -/
theorem opened_block {k n} (A : Nnf L α (k+n)) :
    (bindExists n A).toFormula = existsBlock (openUniversalMatrix A) := by
  unfold Nnf.toFormula
  rw [bindExists_map]
  change bindExists n _ = bindExists n (castF _ (A.map _))
  rw [castF_map]
  congr 1
  congr 1
  funext x
  cases x with
  | inl a =>
    rw [liftMany_free]
    rfl
  | inr i =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [liftMany_old]
      simp only [Term.relabel, Sum.map_inl, Fin.addCases_left, Sum.elim_inr]
    · rw [liftMany_new]
      simp only [Fin.addCases_right, Sum.elim_inr]
      congr 2
      apply Fin.ext
      simp

/-- Universal prefix followed by existential prefix, on the actual ordered slots. -/
def universalExistential {k n} (A : Nnf L α (k+n)) : Nnf L α 0 :=
  forallBlock (bindExists n A)

/-- Fix displayed names and replace all reserved variables by the supplied term. -/
def reserveReplacement (r : L.Term α) : α ⊕ ℕ → L.Term α :=
  Sum.elim Term.var (fun _ => r)

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder.ExistentialHerbrand
