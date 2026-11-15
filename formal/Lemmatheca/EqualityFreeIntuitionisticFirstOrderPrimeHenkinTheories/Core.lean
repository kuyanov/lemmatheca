import Lemmatheca.IntuitionisticFirstOrderDeduction.Soundness
import Lemmatheca.IntuitionisticFirstOrderDeduction.EqualityErasure
import Mathlib.ModelTheory.Encoding
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Countable

namespace Lemmatheca.ProofTheory.FirstOrder.PrimeHenkin
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
universe u v w
noncomputable section
local instance primeHenkinFormulaDecidableEq {L : Language.{u,v}} :
    DecidableEq (Formula L ℕ) := Classical.decEq _
local instance primeHenkinPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable

variable {L : Language.{u,v}}
abbrev Fml (L : Language.{u,v}) := Lemmatheca.ProofTheory.FirstOrder.Formula L ℕ
abbrev Body (L : Language.{u,v}) := Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ 1
abbrev Provable (T : Set (Fml L)) (A : Fml L) := TheoryDerives false false L T A

/-- Actual parameter sets leave an infinite complement in the fixed numerical supply. -/
structure Universe where
  carrier : Set ℕ
  nonempty : carrier.Nonempty
  infinite_compl : carrierᶜ.Infinite

/-- Free support only: currently available quantified placeholders are not parameter names. -/
def Supported (U : Set ℕ) {n : ℕ}
    (A : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n) : Prop :=
  ∀ c ∈ A.freeVarFinset, c ∈ U

def TermSupported (U : Set ℕ) (t : L.Term ℕ) : Prop :=
  ∀ c ∈ t.varFinset, c ∈ U

def eligible (U : Set ℕ) : Set (Fml L) :=
  {A | A.EqualityFree ∧ Supported U A}

def Closed (U : Set ℕ) (T : Set (Fml L)) : Prop :=
  ∀ A ∈ eligible (L := L) U, Provable T A → A ∈ T

/-- Native equality-free theories, with actual parameter-instance witnesses. -/
structure Theory (U : Universe) (T : Set (Fml L)) : Prop where
  supported : T ⊆ eligible U.carrier
  proper : (.falsum : Fml L) ∉ T
  closed : Closed U.carrier T
  prime : ∀ {A B : Fml L}, (.disj A B) ∈ T → A ∈ T ∨ B ∈ T
  witness : ∀ {D : Body L}, (.ex D) ∈ T →
    ∃ c ∈ U.carrier, D.instantiate (.var c) ∈ T

/-- Enlargement of both the available parameters and the set of accepted formulas. -/
def Extends (U : Universe) (T : Set (Fml L)) (V : Universe) (S : Set (Fml L)) : Prop :=
  U.carrier ⊆ V.carrier ∧ T ⊆ S

def Avoids (T : Set (Fml L)) (B : Fml L) : Prop := ¬ Provable T B

theorem supported_mono {U V : Set ℕ} {n : ℕ}
    {A : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n}
    (hUV : U ⊆ V) (hA : Supported U A) : Supported V A := by
  intro c hc
  exact hUV (hA c hc)


private theorem term_relabel_keep_support {n m : ℕ} (t : L.Term (ℕ ⊕ Fin n))
    (f : Fin n → Fin m) :
    (t.relabel (Sum.map id f)).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var x => cases x <;> rfl
  | func f ts ih => simp only [Term.relabel, Term.varFinsetLeft, ih]

private theorem term_relabel_left_support {n : ℕ} (t : L.Term ℕ) :
    (t.relabel (Sum.inl : ℕ → ℕ ⊕ Fin n)).varFinsetLeft = t.varFinset := by
  induction t with
  | var x => rfl
  | func f ts ih => simp only [Term.relabel, Term.varFinsetLeft, Term.varFinset, ih]

private theorem term_map_supported {n m : ℕ} (t : L.Term (ℕ ⊕ Fin n))
    (σ : ScopeSubst L ℕ ℕ n m) (U : Set ℕ)
    (hfree : ∀ x ∈ t.varFinsetLeft, ∀ c ∈ (σ (.inl x)).varFinsetLeft, c ∈ U)
    (hbound : ∀ i, ∀ c ∈ (σ (.inr i)).varFinsetLeft, c ∈ U) :
    ∀ c ∈ (t.subst σ).varFinsetLeft, c ∈ U := by
  induction t with
  | var x =>
    cases x with
    | inl x => exact hfree x (Finset.mem_singleton_self _)
    | inr i => exact hbound i
  | @func n f ts ih =>
    intro c hc
    obtain ⟨i,_,hci⟩ := Finset.mem_biUnion.mp hc
    exact ih i (fun x hx => hfree x (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩)) c hci

private theorem map_supported {n m : ℕ}
    (A : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n)
    (σ : ScopeSubst L ℕ ℕ n m) (U : Set ℕ)
    (hfree : ∀ x ∈ A.freeVarFinset, ∀ c ∈ (σ (.inl x)).varFinsetLeft, c ∈ U)
    (hbound : ∀ i, ∀ c ∈ (σ (.inr i)).varFinsetLeft, c ∈ U) : Supported U (A.map σ) := by
  induction A generalizing m with
  | falsum => simp [Supported, BoundedFormula.map, BoundedFormula.freeVarFinset]
  | equal s t =>
    intro c hc
    rcases Finset.mem_union.mp hc with hs | ht
    · exact term_map_supported s σ U
        (fun x hx => hfree x (Finset.mem_union_left _ hx)) hbound c hs
    · exact term_map_supported t σ U
        (fun x hx => hfree x (Finset.mem_union_right _ hx)) hbound c ht
  | rel R ts =>
    intro c hc
    obtain ⟨i,_,hci⟩ := Finset.mem_biUnion.mp hc
    exact term_map_supported (ts i) σ U
      (fun x hx => hfree x (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩)) hbound c hci
  | neg A ih => exact ih σ hfree hbound
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    intro c hc
    rcases Finset.mem_union.mp hc with ha | hb
    · exact ihA σ (fun x hx => hfree x (Finset.mem_union_left _ hx)) hbound c ha
    · exact ihB σ (fun x hx => hfree x (Finset.mem_union_right _ hx)) hbound c hb
  | @all n A ih | @ex n A ih =>
    apply ih (liftScope σ)
    · intro x hx c hc
      have he : (liftScope σ (.inl x)).varFinsetLeft = (σ (.inl x)).varFinsetLeft :=
        term_relabel_keep_support _ _
      exact hfree x hx c (he ▸ hc)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [liftScope, Term.varFinsetLeft]
      · intro c hc
        have he : (liftScope σ (.inr j.castSucc)).varFinsetLeft =
            (σ (.inr j)).varFinsetLeft := by
          rw [show liftScope σ (.inr j.castSucc) = (σ (.inr j)).relabel (scopeInclusion m)
            from liftScope_inclusion σ (.inr j)]
          exact term_relabel_keep_support _ _
        exact hbound j c (he ▸ hc)

theorem instantiate_supported {U : Set ℕ} (D : Body L) (t : L.Term ℕ)
    (hD : Supported U D) (ht : TermSupported U t) : Supported U (D.instantiate t) := by
  unfold BoundedFormula.instantiate BoundedFormula.instantiateSlots
  apply map_supported D _ U
  · intro x hx c hc
    have he : c = x := Finset.mem_singleton.mp hc
    exact he ▸ hD x hx
  · intro i c hc
    rw [Sum.elim_inr,term_relabel_left_support] at hc
    exact ht c hc


theorem instantiate_equalityFree (D : Body L) (t : L.Term ℕ) :
    (D.instantiate t).EqualityFree ↔ D.EqualityFree := by
  exact D.equalityFree_map _


theorem provable_mono {T S : Set (Fml L)} {A : Fml L}
    (hTS : T ⊆ S) (h : Provable T A) : Provable S A := by
  rcases h with ⟨p⟩
  exact ⟨⟨p.assumptions, fun C hC => hTS (p.allowed C hC), p.derivation⟩⟩



private theorem from_assumption {T : Set (Fml L)} {A : Fml L} (hA : A ∈ T) : Provable T A := by
  exact ⟨⟨{A}, by intro C hC; have he := Finset.mem_singleton.mp hC; exact he ▸ hA,
    Proof.assumption (Finset.mem_singleton_self _)⟩⟩

theorem provable_deduction (T : Set (Fml L)) (A B : Fml L) :
    Provable (insert A T) B ↔ Provable T (.impl A B) := by
  constructor
  · rintro ⟨p⟩
    let Δ := p.assumptions.erase A
    have hΔ : ∀ C ∈ Δ, C ∈ T := by
      intro C hC
      have hm := Finset.mem_erase.mp hC
      exact (Set.mem_insert_iff.mp (p.allowed C hm.2)).resolve_left hm.1
    have hp : Proof false false L (insert A Δ) B := p.derivation.weaken (by
      intro C hC
      by_cases he : C = A
      · exact he ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hC⟩))
    exact ⟨⟨Δ,hΔ,Proof.impIntro hp⟩⟩
  · rintro ⟨p⟩
    refine ⟨⟨insert A p.assumptions, ?_, ?_⟩⟩
    · intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (p.allowed C hC)
    · exact Proof.impElim (p.derivation.weaken (Finset.subset_insert _ _))
        (Proof.assumption (Finset.mem_insert_self _ _))


theorem provable_cut {T : Set (Fml L)} {A B : Fml L}
    (hA : Provable T A) (hB : Provable (insert A T) B) : Provable T B := by
  rcases hB with ⟨p⟩
  refine ⟨p.replace (fun C hC => Classical.choice (?_ : Provable T C))⟩
  rcases Set.mem_insert_iff.mp hC with rfl | hC
  · exact hA
  · exact from_assumption hC


theorem provable_increasing_union (T : ℕ → Set (Fml L)) (hT : Monotone T) (A : Fml L) :
    Provable (⋃ n, T n) A ↔ ∃ n, Provable (T n) A := by
  constructor
  · rintro ⟨p⟩
    have finite_bound : ∀ Δ : Finset (Fml L), (∀ C ∈ Δ, C ∈ ⋃ n, T n) →
        ∃ n, ∀ C ∈ Δ, C ∈ T n := by
      intro Δ
      induction Δ using Finset.induction_on with
      | empty => exact fun _ => ⟨0, by simp⟩
      | @insert C Δ hnot ih =>
        intro hall
        obtain ⟨n,hn⟩ := ih (by intro A hA; exact hall A (Finset.mem_insert_of_mem hA))
        obtain ⟨m,hm⟩ := Set.mem_iUnion.mp (hall C (Finset.mem_insert_self _ _))
        refine ⟨max n m, ?_⟩
        intro A hA
        rcases Finset.mem_insert.mp hA with rfl | hA
        · exact hT (le_max_right _ _) hm
        · exact hT (le_max_left _ _) (hn A hA)
    have hbounded := finite_bound p.assumptions p.allowed
    obtain ⟨n,hn⟩ := hbounded
    exact ⟨n,⟨⟨p.assumptions,hn,p.derivation⟩⟩⟩
  · rintro ⟨n,hn⟩
    exact provable_mono (Set.subset_iUnion T n) hn


/-- The literal public-name renaming used before applying a protected eigenparameter rule. -/
def freshRename (c : ℕ) (x : ℕ) : ℕ ⊕ Fin 1 :=
  if x = c then .inr 0 else .inl x

private theorem term_subst_congr_support {α : Type} {β : Type w} [DecidableEq α]
    (t : L.Term α) (σ τ : α → L.Term β)
    (h : ∀ x ∈ t.varFinset, σ x = τ x) : t.subst σ = t.subst τ := by
  induction t with
  | var x => exact h x (Finset.mem_singleton_self _)
  | @func n f ts ih =>
    simp only [Term.subst]
    congr 1
    funext i
    exact ih i (fun x hx => h x (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩))

private theorem mem_varFinset_left {α β : Type w} [DecidableEq α] [DecidableEq β]
    (t : L.Term (α ⊕ β)) (a : α) : Sum.inl a ∈ t.varFinset ↔ a ∈ t.varFinsetLeft := by
  induction t with
  | var x => cases x <;> simp [Term.varFinset,Term.varFinsetLeft]
  | func f ts ih => simp only [Term.varFinset,Term.varFinsetLeft,Finset.mem_biUnion,ih]

private theorem term_scope_congr {β : Type w} {n m : ℕ}
    (t : L.Term (ℕ ⊕ Fin n)) (σ τ : ScopeSubst L ℕ β n m)
    (hfree : ∀ x ∈ t.varFinsetLeft, σ (.inl x) = τ (.inl x))
    (hbound : ∀ i, σ (.inr i) = τ (.inr i)) : t.subst σ = t.subst τ := by
  apply term_subst_congr_support
  intro x hx
  cases x with
  | inl x => exact hfree x ((mem_varFinset_left t x).mp hx)
  | inr i => exact hbound i

private theorem map_congr_support {β : Type w} {n m : ℕ}
    (A : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n)
    (σ τ : ScopeSubst L ℕ β n m)
    (hfree : ∀ x ∈ A.freeVarFinset, σ (.inl x) = τ (.inl x))
    (hbound : ∀ i, σ (.inr i) = τ (.inr i)) : A.map σ = A.map τ := by
  induction A generalizing m with
  | falsum => rfl
  | equal s t =>
    simp only [BoundedFormula.map]
    congr 1
    · exact term_scope_congr s σ τ (fun x hx => hfree x (Finset.mem_union_left _ hx)) hbound
    · exact term_scope_congr t σ τ (fun x hx => hfree x (Finset.mem_union_right _ hx)) hbound
  | rel R ts =>
    simp only [BoundedFormula.map]
    congr 1
    funext i
    exact term_scope_congr (ts i) σ τ
      (fun x hx => hfree x (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩)) hbound
  | neg A ih =>
    simp only [BoundedFormula.map]
    exact congrArg BoundedFormula.neg (ih σ τ hfree hbound)
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    simp only [BoundedFormula.map]
    congr 1
    · exact ihA σ τ (fun x hx => hfree x (Finset.mem_union_left _ hx)) hbound
    · exact ihB σ τ (fun x hx => hfree x (Finset.mem_union_right _ hx)) hbound
  | @all n A ih | @ex n A ih =>
    simp only [BoundedFormula.map]
    congr 1
    apply ih (liftScope σ) (liftScope τ)
    · intro x hx
      change (σ (.inl x)).relabel _ = (τ (.inl x)).relabel _
      rw [hfree x hx]
    · intro i
      refine Fin.lastCases (by simp only [liftScope_last]) (fun j => ?_) i
      change liftScope σ (scopeInclusion n (.inr j)) = liftScope τ (scopeInclusion n (.inr j))
      rw [liftScope_inclusion σ (.inr j),liftScope_inclusion τ (.inr j),hbound j]

theorem rename_of_agree {β : Type w} {n : ℕ}
    (A : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n) (f g : ℕ → β)
    (h : ∀ c ∈ A.freeVarFinset, f c = g c) : A.rename f = A.rename g := by
  apply map_congr_support A
  · intro x hx
    change Term.var (Sum.inl (f x)) = Term.var (Sum.inl (g x))
    rw [h x hx]
  · intro i; rfl


theorem fresh_rename_eq {n : ℕ}
    (A : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n) (c : ℕ)
    (hc : c ∉ A.freeVarFinset) : A.rename (freshRename c) = A.rename Sum.inl := by
  apply rename_of_agree A
  intro x hx
  have hxc : x ≠ c := fun h => hc (h ▸ hx)
  simp [freshRename,hxc]


theorem fresh_instance_open (D : Body L) (c : ℕ) (hc : c ∉ D.freeVarFinset) :
    (D.instantiate (.var c)).rename (freshRename c) = D.toFormula := by
  unfold BoundedFormula.instantiate BoundedFormula.instantiateSlots
    BoundedFormula.rename BoundedFormula.subst BoundedFormula.toFormula
  rw [BoundedFormula.map_comp]
  apply map_congr_support D
  · intro x hx
    have hxc : x ≠ c := fun h => hc (h ▸ hx)
    simp [BoundedFormula.freeScope,Term.subst,Term.relabel,freshRename,hxc]
  · intro i
    simp [BoundedFormula.freeScope,Term.subst,Term.relabel,freshRename]
    exact Subsingleton.elim (0 : Fin 1) i


private theorem fresh_context (Γ : Context L ℕ) (c : ℕ)
    (h : ∀ A ∈ Γ, c ∉ A.freeVarFinset) :
    Γ.image (fun A => A.rename (freshRename c)) = liftContext Γ := by
  unfold liftContext
  apply Finset.image_congr
  intro A hA
  exact fresh_rename_eq A c (h A hA)

theorem fresh_all_intro {T : Set (Fml L)} (D : Body L) (c : ℕ)
    (hT : ∀ A ∈ T, c ∉ A.freeVarFinset) (hD : c ∉ D.freeVarFinset)
    (h : Provable T (D.instantiate (.var c))) : Provable T (.all D) := by
  rcases h with ⟨p⟩
  have hp := p.derivation.rename (freshRename c)
  have hctx := fresh_context p.assumptions c (fun A hA => hT A (p.allowed A hA))
  have hbranch : Proof false false L (liftContext p.assumptions) D.toFormula := by
    simpa only [hctx,fresh_instance_open D c hD] using hp
  exact ⟨⟨p.assumptions,p.allowed,Proof.allIntro hbranch⟩⟩


theorem fresh_ex_elim {T : Set (Fml L)} (D : Body L) (B : Fml L) (c : ℕ)
    (hT : ∀ A ∈ T, c ∉ A.freeVarFinset) (hD : c ∉ D.freeVarFinset)
    (hB : c ∉ B.freeVarFinset) (hex : Provable T (.ex D))
    (h : Provable (insert (D.instantiate (.var c)) T) B) : Provable T B := by
  rcases hex with ⟨pe⟩
  rcases h with ⟨pb⟩
  let I := D.instantiate (.var c)
  let Γ := pe.assumptions ∪ pb.assumptions.erase I
  have hΓ : ∀ A ∈ Γ, A ∈ T := by
    intro A hA
    rcases Finset.mem_union.mp hA with he | hb
    · exact pe.allowed A he
    · have hm := Finset.mem_erase.mp hb
      exact (Set.mem_insert_iff.mp (pb.allowed A hm.2)).resolve_left hm.1
  have hpe : Proof false false L Γ (.ex D) :=
    pe.derivation.weaken Finset.subset_union_left
  have hpb : Proof false false L (insert I Γ) B := pb.derivation.weaken (by
    intro A hA
    by_cases he : A = I
    · exact he ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨he,hA⟩)))
  have hp := hpb.rename (freshRename c)
  have hctx := fresh_context Γ c (fun A hA => hT A (hΓ A hA))
  have hbranch : Proof false false L (insert D.toFormula (liftContext Γ)) (B.rename Sum.inl) := by
    simpa only [Finset.image_insert,I,fresh_instance_open D c hD,hctx,fresh_rename_eq B c hB] using hp
  exact ⟨⟨Γ,hΓ,Proof.exElim hpe hbranch⟩⟩


theorem safe_witness {T : Set (Fml L)} (D : Body L) (B : Fml L) (c : ℕ)
    (hT : ∀ A ∈ T, c ∉ A.freeVarFinset) (hD : c ∉ D.freeVarFinset)
    (hB : c ∉ B.freeVarFinset) (h : Avoids (insert (.ex D) T) B) :
    Avoids (insert (D.instantiate (.var c)) (insert (.ex D) T)) B := by
  intro hbad
  apply h
  apply fresh_ex_elim D B c (hD := hD) (hB := hB)
  · intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact hD
    · exact hT A hA
  · exact from_assumption (Set.mem_insert _ _)
  · exact hbad


theorem theory_consistent {U : Universe} {T : Set (Fml L)} (hT : Theory U T) :
    ¬Provable T .falsum := by
  intro h
  exact hT.proper (hT.closed .falsum ⟨trivial, by simp [Supported, BoundedFormula.freeVarFinset]⟩ h)


end
end Lemmatheca.ProofTheory.FirstOrder.PrimeHenkin
