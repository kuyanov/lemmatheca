import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.SplitIfs

/-! Finite congruence closure on the actual shared first-order ground terms. -/

namespace Lemmatheca.MathematicalLogic.GroundEquality

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}}

abbrev GroundTerm (L : Language.{u, v}) := L.Term Empty
abbrev TermPair (L : Language.{u, v}) := GroundTerm L × GroundTerm L

/-- Equations and disequations are finite sets of pairs of actual ground terms. -/
structure Problem (L : Language.{u, v}) where
  equations : Finset (TermPair L)
  disequations : Finset (TermPair L)

/-- The displayed equality constraints use ordinary first-order term evaluation. -/
def Satisfies (P : Problem L) (M : Type w) [L.Structure M] : Prop :=
  (∀ p ∈ P.equations, p.1.realize Empty.elim = p.2.realize (Empty.elim : Empty → M)) ∧
  (∀ p ∈ P.disequations, p.1.realize Empty.elim ≠ p.2.realize (Empty.elim : Empty → M))

/-- A solution has a nonempty carrier; the finite model below lives in this universe. -/
def HasModel (P : Problem L) : Prop :=
  ∃ (M : Type u) (inst : L.Structure M), Nonempty M ∧ @Satisfies _ P M inst

variable [∀ n, DecidableEq (L.Functions n)]

/-- All subterms, including the term itself. -/
def subterms : GroundTerm L → Finset (GroundTerm L)
  | .var e => nomatch e
  | .func f ts => {.func f ts} ∪ Finset.univ.biUnion (fun i => subterms (ts i))

/-- A finite term set contains the immediate arguments of every retained application. -/
def SubtermClosed (S : Finset (GroundTerm L)) : Prop :=
  ∀ {n} (f : L.Functions n) (ts : Fin n → GroundTerm L),
    Term.func f ts ∈ S → ∀ i, ts i ∈ S

/-- The canonical finite subterm set of an input. -/
def support (P : Problem L) : Finset (GroundTerm L) :=
  (P.equations ∪ P.disequations).biUnion (fun p => subterms p.1 ∪ subterms p.2)

theorem mem_subterms (t : GroundTerm L) : t ∈ subterms t := by
  cases t with
  | var e => exact e.elim
  | func f ts => simp [subterms]

private theorem subterms_subset_of_mem {t s : GroundTerm L} (h : s ∈ subterms t) :
    subterms s ⊆ subterms t := by
  induction t generalizing s with
  | var e => exact e.elim
  | func f ts ih =>
    simp only [subterms, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_univ, true_and] at h
    rcases h with rfl | ⟨i, hi⟩
    · exact Finset.Subset.refl _
    · intro z hz
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ih i hi hz⟩))

theorem subterms_closed (t : GroundTerm L) : SubtermClosed (subterms t) := by
  intro n f ts h i
  apply subterms_subset_of_mem h
  exact Finset.mem_union.mpr (Or.inr
    (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, mem_subterms (ts i)⟩))

theorem support_closed (P : Problem L) : SubtermClosed (support P) := by
  intro n f ts h i
  obtain ⟨p, hp, hterm⟩ := Finset.mem_biUnion.mp h
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hp, ?_⟩
  rcases Finset.mem_union.mp hterm with hleft | hright
  · exact Finset.mem_union.mpr (Or.inl (subterms_closed p.1 f ts hleft i))
  · exact Finset.mem_union.mpr (Or.inr (subterms_closed p.2 f ts hright i))

theorem equations_supported (P : Problem L) :
    P.equations ⊆ (support P).product (support P) := by
  intro p hp
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_union_left _ hp,
      Finset.mem_union_left _ (mem_subterms p.1)⟩
  · exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_union_left _ hp,
      Finset.mem_union_right _ (mem_subterms p.2)⟩

theorem disequations_supported (P : Problem L) :
    P.disequations ⊆ (support P).product (support P) := by
  intro p hp
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_union_right _ hp,
      Finset.mem_union_left _ (mem_subterms p.1)⟩
  · exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_union_right _ hp,
      Finset.mem_union_right _ (mem_subterms p.2)⟩

/-- Root symbols and arities agree, and corresponding arguments are related. -/
def RootCongruent (r : GroundTerm L → GroundTerm L → Prop) :
    GroundTerm L → GroundTerm L → Prop
  | .var e, _ => nomatch e
  | _, .var e => nomatch e
  | @Term.func _ _ n f ts, @Term.func _ _ m g us =>
      if h : n = m then f = h.symm ▸ g ∧ ∀ i, r (ts i) (us (Fin.cast h i)) else False

instance rootCongruentDecidable (r : GroundTerm L → GroundTerm L → Prop)
    [DecidableRel r] (t s : GroundTerm L) : Decidable (RootCongruent r t s) := by
  cases t with
  | var e => exact e.elim
  | @func n f ts =>
    cases s with
    | var e => exact e.elim
    | @func m g us =>
      unfold RootCongruent
      infer_instance

/-- One synchronous step, expressed by finite scans of retained term pairs. -/
def step (S : Finset (GroundTerm L)) (R : Finset (TermPair L)) : Finset (TermPair L) :=
  R ∪ (S.product S).filter (fun p =>
    p.1 = p.2 ∨ (p.2, p.1) ∈ R ∨
    (∃ t ∈ S, (p.1, t) ∈ R ∧ (t, p.2) ∈ R) ∨
    RootCongruent (fun t s => (t, s) ∈ R) p.1 p.2)

/-- Stage zero consists of the equations; later stages apply the same step. -/
def stage (S : Finset (GroundTerm L)) (E : Finset (TermPair L)) : ℕ → Finset (TermPair L)
  | 0 => E
  | k + 1 => step S (stage S E k)

/-- The fixed, explicitly bounded stage used by the decision procedure. -/
def closure (S : Finset (GroundTerm L)) (E : Finset (TermPair L)) : Finset (TermPair L) :=
  stage S E (S.card ^ 2)

/-- Equivalence and function congruence, restricted to applications retained in S. -/
structure IsCongruence (S : Finset (GroundTerm L))
    (r : GroundTerm L → GroundTerm L → Prop) : Prop where
  refl : ∀ t ∈ S, r t t
  symm : ∀ t ∈ S, ∀ s ∈ S, r t s → r s t
  trans : ∀ t ∈ S, ∀ s ∈ S, ∀ z ∈ S, r t s → r s z → r t z
  func : ∀ {n} (f : L.Functions n) (ts us : Fin n → GroundTerm L),
    Term.func f ts ∈ S → Term.func f us ∈ S →
    (∀ i, r (ts i) (us i)) → r (.func f ts) (.func f us)

theorem stage_increasing (S : Finset (GroundTerm L)) (E : Finset (TermPair L)) (k : ℕ) :
    stage S E k ⊆ stage S E (k + 1) := by
  exact Finset.subset_union_left

theorem stage_supported (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (k : ℕ) : stage S E k ⊆ S.product S := by
  induction k with
  | zero => exact hE
  | succ k ih =>
    intro p hp
    rcases Finset.mem_union.mp hp with hold | hnew
    · exact ih hold
    · exact (Finset.mem_filter.mp hnew).1

private theorem stage_fixed_after (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    {j : ℕ} (hj : step S (stage S E j) = stage S E j) (k : ℕ) :
    stage S E (j + k) = stage S E j := by
  induction k with
  | zero => simp
  | succ k ih =>
    change step S (stage S E (j + k)) = stage S E j
    rw [ih, hj]

theorem closure_fixed (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) : step S (closure S E) = closure S E := by
  let N := S.card ^ 2
  have exists_fixed : ∃ j ≤ N, step S (stage S E j) = stage S E j := by
    by_contra h
    have strict (k : ℕ) (hk : k ≤ N) :
        (stage S E k).card < (stage S E (k + 1)).card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨stage_increasing S E k, ?_⟩
      intro heq
      exact h ⟨k, hk, heq.symm⟩
    have grow : ∀ k ≤ N + 1, k ≤ (stage S E k).card := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have hprev := ih (by omega : k ≤ N + 1)
        have hstrict := strict k (by omega)
        omega
    have hlarge := grow (N + 1) (le_refl _)
    have hsmall : (stage S E (N + 1)).card ≤ N := by
      simpa [N, pow_two] using Finset.card_le_card (stage_supported S E hE (N + 1))
    omega
  obtain ⟨j, hj, hfixed⟩ := exists_fixed
  have hstage : stage S E N = stage S E j := by
    simpa [Nat.add_sub_of_le hj] using stage_fixed_after S E hfixed (N - j)
  change step S (stage S E N) = stage S E N
  rw [hstage]
  exact hfixed

theorem stage_after_bound (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (k : ℕ) (hk : S.card ^ 2 ≤ k) :
    stage S E k = closure S E := by
  have hfixed : step S (stage S E (S.card ^ 2)) = stage S E (S.card ^ 2) :=
    closure_fixed S E hE
  have h := stage_fixed_after S E hfixed (k - S.card ^ 2)
  rw [Nat.add_sub_of_le hk] at h
  exact h

theorem equations_subset_closure (S : Finset (GroundTerm L)) (E : Finset (TermPair L)) :
    E ⊆ closure S E := by
  have h : ∀ k, E ⊆ stage S E k := by
    intro k
    induction k with
    | zero => exact Finset.Subset.refl _
    | succ k ih => exact ih.trans (stage_increasing S E k)
  exact h _

theorem closure_congruence (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) :
    IsCongruence S (fun t s => (t, s) ∈ closure S E) := by
  have closed := closure_fixed S E hE
  have add {p : TermPair L}
      (hp : p ∈ S.product S)
      (h : p.1 = p.2 ∨ (p.2, p.1) ∈ closure S E ∨
        (∃ t ∈ S, (p.1, t) ∈ closure S E ∧ (t, p.2) ∈ closure S E) ∨
        RootCongruent (fun t s => (t, s) ∈ closure S E) p.1 p.2) :
      p ∈ closure S E := by
    rw [← closed]
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp, h⟩))
  constructor
  · intro t ht
    exact add (Finset.mem_product.mpr ⟨ht, ht⟩) (Or.inl rfl)
  · intro t ht z hz htz
    exact add (Finset.mem_product.mpr ⟨hz, ht⟩) (Or.inr (Or.inl htz))
  · intro t ht z hz q hq htz hzq
    exact add (Finset.mem_product.mpr ⟨ht, hq⟩)
      (Or.inr (Or.inr (Or.inl ⟨z, hz, htz, hzq⟩)))
  · intro n f ts us ht hu hargs
    apply add (Finset.mem_product.mpr ⟨ht, hu⟩)
    exact Or.inr (Or.inr (Or.inr (by simpa [RootCongruent] using hargs)))

theorem closure_least (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (_hE : E ⊆ S.product S) (r : GroundTerm L → GroundTerm L → Prop)
    (hr : IsCongruence S r) (hEr : ∀ p ∈ E, r p.1 p.2) :
    ∀ p ∈ closure S E, r p.1 p.2 := by
  have stages : ∀ k, ∀ p ∈ stage S E k, r p.1 p.2 := by
    intro k
    induction k with
    | zero => exact hEr
    | succ k ih =>
      intro p hp
      rcases Finset.mem_union.mp hp with hold | hnew
      · exact ih p hold
      · obtain ⟨hpS, hadd⟩ := Finset.mem_filter.mp hnew
        obtain ⟨hleft, hright⟩ := Finset.mem_product.mp hpS
        rcases hadd with heq | hrev | ⟨t, ht, hlt, htr⟩ | hfunc
        · simpa [heq] using hr.refl p.2 hright
        · exact hr.symm p.2 hright p.1 hleft (ih _ hrev)
        · exact hr.trans p.1 hleft t ht p.2 hright (ih _ hlt) (ih _ htr)
        · rcases p with ⟨t, z⟩
          cases t with
          | var e => exact e.elim
          | @func n f ts =>
            cases z with
            | var e => exact e.elim
            | @func m g us =>
              dsimp [RootCongruent] at hfunc
              split_ifs at hfunc with hnm
              · subst m
                obtain ⟨hfg, hargs⟩ := hfunc
                have hfg' : f = g := by simpa using hfg
                have hargs' : ∀ i, (ts i, us i) ∈ stage S E k := by simpa using hargs
                subst g
                exact hr.func f ts us hleft hright (fun i => ih _ (hargs' i))
  exact stages _

theorem closure_sound (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (M : Type w) [L.Structure M]
    (hM : ∀ p ∈ E, p.1.realize Empty.elim = p.2.realize (Empty.elim : Empty → M)) :
    ∀ p ∈ closure S E,
      p.1.realize Empty.elim = p.2.realize (Empty.elim : Empty → M) := by
  apply closure_least S E hE (fun t s =>
    t.realize Empty.elim = s.realize (Empty.elim : Empty → M))
  · constructor
    · intro t _
      rfl
    · intro t _ s _ h
      exact h.symm
    · intro t _ s _ z _ h₁ h₂
      exact h₁.trans h₂
    · intro n f ts us _ _ hargs
      simp only [Term.realize_func]
      exact congrArg (Structure.funMap f) (funext hargs)
  · exact hM

/-- The quotient relation is the actual bounded-stage output, not an existential closure. -/
def termSetoid (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) : Setoid S where
  r t s := (t.val, s.val) ∈ closure S E
  iseqv :=
    ⟨fun t => (closure_congruence S E hE).refl t t.property,
      fun {t s} => (closure_congruence S E hE).symm t t.property s s.property,
      fun {t s z} => (closure_congruence S E hE).trans t t.property s s.property z z.property⟩

/-- Classes plus a separate point, so empty input still gives a nonempty carrier. -/
abbrev Carrier (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) := Option (Quotient (termSetoid S E hE))

/-- A retained term is sent to its class, never to the default point. -/
def classOf (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (t : GroundTerm L) (ht : t ∈ S) : Carrier S E hE :=
  some (Quotient.mk (termSetoid S E hE) ⟨t, ht⟩)

theorem classOf_eq_iff (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (t s : GroundTerm L) (ht : t ∈ S) (hs : s ∈ S) :
    classOf S E hE t ht = classOf S E hE s hs ↔ (t, s) ∈ closure S E := by
  simp only [classOf, Option.some.injEq, Quotient.eq]
  rfl

theorem finite_carrier (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) : Finite (Carrier S E hE) := by
  infer_instance

theorem carrier_card_bound (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) :
    Nat.card (Carrier S E hE) ≤ S.card + 1 := by
  classical
  let : Fintype (Quotient (termSetoid S E hE)) := Fintype.ofFinite _
  have hq : Fintype.card (Quotient (termSetoid S E hE)) ≤ S.card := by
    simpa using Fintype.card_le_of_surjective
      (Quotient.mk (termSetoid S E hE)) Quotient.mk_surjective
  simpa [Nat.card_eq_fintype_card, Carrier] using Nat.add_le_add_right hq 1

end Lemmatheca.MathematicalLogic.GroundEquality
