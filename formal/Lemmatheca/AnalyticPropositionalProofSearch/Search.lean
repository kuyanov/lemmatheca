import Lemmatheca.AnalyticPropositionalProofSearch.States
import Lemmatheca.PropositionalCutElimination.Structures

/-! Actual deterministic decomposition and its exact correctness targets. -/

namespace Lemmatheca.ProofTheory.ClassicalPropositional.AnalyticSearch

def weight : Input → ℕ
  | [] => 0
  | A :: R => A.formulaSize + weight R

/-- The possible remaining-list changes of a recursive call. -/
inductive Decomposes : Input → Input → Prop
  | positive (i R) : Decomposes (.pos i :: R) R
  | negative (i R) : Decomposes (.neg i :: R) R
  | bottom (R) : Decomposes (.bot :: R) R
  | disjunction (A B R) : Decomposes (.or A B :: R) (A :: B :: R)
  | conjunctionLeft (A B R) : Decomposes (.and A B :: R) (A :: R)
  | conjunctionRight (A B R) : Decomposes (.and A B :: R) (B :: R)

theorem weight_decreases {L M : Input} (h : Decomposes L M) : weight M < weight L := by
  cases h <;> simp only [weight, Nnf.formulaSize] <;> omega

private theorem context_cons (S : Sequent ℕ) (A : Nnf ℕ) (R : Input) :
    context S (A :: R) = insert A (context S R) := by
  simp [context]

private theorem context_move (S : Sequent ℕ) (A : Nnf ℕ) (R : Input) :
    context (insert A S) R = context S (A :: R) := by
  simp [context]

private def bottomResult (S : Sequent ℕ) (R : Input) :
    Result (context S R) → Result (context S (.bot :: R))
  | .proved p => .proved ((context_cons S .bot R).symm ▸ Proof.botIntro p)
  | .counter v => .counter v

private def orResult (S : Sequent ℕ) (A B : Nnf ℕ) (R : Input) :
    Result (context S (A :: B :: R)) → Result (context S (.or A B :: R))
  | .proved p => .proved ((context_cons S (.or A B) R).symm ▸
      Proof.orIntro ((by rw [context_cons, context_cons] at p; exact p)))
  | .counter v => .counter v

private def andResult (S : Sequent ℕ) (A B : Nnf ℕ) (R : Input)
    (p : Proof (context S (A :: R))) :
    Result (context S (B :: R)) → Result (context S (.and A B :: R))
  | .proved q => .proved ((context_cons S (.and A B) R).symm ▸
      Proof.andIntro ((context_cons S A R) ▸ p) ((context_cons S B R) ▸ q))
  | .counter v => .counter v

/-- Ordered first-child-first analytic search, returning primitive certificates. -/
def search (S : Sequent ℕ) (L : Input) : Result (context S L) :=
  match L with
  | [] => (terminal S).transport (by simp [context])
  | .pos i :: R => (search (insert (.pos i) S) R).transport (context_move S (.pos i) R)
  | .neg i :: R => (search (insert (.neg i) S) R).transport (context_move S (.neg i) R)
  | .top :: R => .proved (.truth (by simp [context]))
  | .bot :: R => bottomResult S R (search S R)
  | .or A B :: R => orResult S A B R (search S (A :: B :: R))
  | .and A B :: R =>
      match search S (A :: R) with
      | .counter v => .counter v
      | .proved p => andResult S A B R p (search S (B :: R))
termination_by weight L
decreasing_by
  · exact weight_decreases (.positive _ _)
  · exact weight_decreases (.negative _ _)
  · exact weight_decreases (.bottom _)
  · exact weight_decreases (.disjunction _ _ _)
  · exact weight_decreases (.conjunctionLeft _ _ _)
  · exact weight_decreases (.conjunctionRight _ _ _)

private theorem transport_correct {Γ Δ : Sequent ℕ} (h : Γ = Δ)
    (r : Result Γ) (hr : r.Correct) : (r.transport h).Correct := by
  cases h
  cases r <;> exact hr

private theorem literal_insert (S : Sequent ℕ) (A : Nnf ℕ)
    (hS : LiteralContext S) (hA : Literal A) : LiteralContext (insert A S) := by
  intro F hF
  rcases Finset.mem_insert.mp hF with rfl | hF
  · exact hA
  · exact hS F hF

private theorem bottom_correct (S : Sequent ℕ) (R : Input)
    (r : Result (context S R)) (hr : r.Correct) : (bottomResult S R r).Correct := by
  cases r with
  | proved p => trivial
  | counter v =>
    intro F hF
    rw [context_cons] at hF
    rcases Finset.mem_insert.mp hF with rfl | hF
    · rfl
    · exact hr F hF

private theorem or_correct (S : Sequent ℕ) (A B : Nnf ℕ) (R : Input)
    (r : Result (context S (A :: B :: R))) (hr : r.Correct) :
    (orResult S A B R r).Correct := by
  cases r with
  | proved p => trivial
  | counter v =>
    intro F hF
    rw [context_cons] at hF
    rcases Finset.mem_insert.mp hF with rfl | hF
    · have ha := hr A (by rw [context_cons]; simp)
      have hb := hr B (by rw [context_cons, context_cons]; simp)
      simp [Nnf.eval, ha, hb]
    · exact hr F (by rw [context_cons, context_cons]; simp [hF])

private theorem and_counter_left (S : Sequent ℕ) (A B : Nnf ℕ) (R : Input)
    (v : ℕ → Bool) (hr : (Result.counter v : Result (context S (A :: R))).Correct) :
    (Result.counter v : Result (context S (.and A B :: R))).Correct := by
  intro F hF
  rw [context_cons] at hF
  rcases Finset.mem_insert.mp hF with rfl | hF
  · have ha := hr A (by rw [context_cons]; simp)
    simp [Nnf.eval, ha]
  · exact hr F (by rw [context_cons]; simp [hF])

private theorem and_correct (S : Sequent ℕ) (A B : Nnf ℕ) (R : Input)
    (p : Proof (context S (A :: R)))
    (r : Result (context S (B :: R))) (hr : r.Correct) :
    (andResult S A B R p r).Correct := by
  cases r with
  | proved q => trivial
  | counter v =>
    intro F hF
    rw [context_cons] at hF
    rcases Finset.mem_insert.mp hF with rfl | hF
    · have hb := hr B (by rw [context_cons]; simp)
      simp [Nnf.eval, hb]
    · exact hr F (by rw [context_cons]; simp [hF])

theorem search_correct (S : Sequent ℕ) (L : Input) (hS : LiteralContext S) :
    (search S L).Correct := by
  have main : ∀ L : Input, ∀ S, LiteralContext S → (search S L).Correct := by
    intro L
    induction L using (measure weight).wf.induction with
    | h L ih =>
      intro S hS
      cases L with
      | nil =>
        rw [search]
        exact transport_correct _ _ (terminal_correct S hS)
      | cons F R =>
        cases F with
        | pos i =>
          rw [search]
          exact transport_correct _ _
            (ih R (weight_decreases (.positive i R)) _
              (literal_insert S (.pos i) hS trivial))
        | neg i =>
          rw [search]
          exact transport_correct _ _
            (ih R (weight_decreases (.negative i R)) _
              (literal_insert S (.neg i) hS trivial))
        | top => rw [search]; trivial
        | bot =>
          rw [search]
          exact bottom_correct S R _ (ih R (weight_decreases (.bottom R)) S hS)
        | or A B =>
          rw [search]
          exact or_correct S A B R _
            (ih (A :: B :: R) (weight_decreases (.disjunction A B R)) S hS)
        | and A B =>
          rw [search]
          have hl := ih (A :: R) (weight_decreases (.conjunctionLeft A B R)) S hS
          cases he : search S (A :: R) with
          | counter v =>
            rw [he] at hl
            exact and_counter_left S A B R v hl
          | proved p =>
            exact and_correct S A B R p _
              (ih (B :: R) (weight_decreases (.conjunctionRight A B R)) S hS)
  exact main L S hS

theorem search_succeeds_iff_valid (L : Input) :
    (search ∅ L).succeeds = true ↔ Valid L.toFinset := by
  have hc := search_correct ∅ L (by simp [LiteralContext])
  cases he : search ∅ L with
  | proved p =>
    constructor
    · intro _
      simpa [context] using p.sound
    · intro _
      rfl
  | counter v =>
    rw [he] at hc
    constructor
    · intro h
      cases h
    · intro hv
      obtain ⟨A, hA, ht⟩ := hv v
      have hf := hc A (by simpa [context] using hA)
      simp_all

theorem search_succeeds_iff_derives (L : Input) :
    (search ∅ L).succeeds = true ↔ Derives L.toFinset := by
  constructor
  · intro h
    cases he : search ∅ L with
    | proved p => exact ⟨by simpa [context] using p⟩
    | counter v => simp [he, Result.succeeds] at h
  · rintro ⟨p⟩
    exact (search_succeeds_iff_valid L).mpr p.sound

/-- Abstract finite-set completeness; it does not define a canonical input order. -/
theorem derives_iff_valid (Γ : Sequent ℕ) : Derives Γ ↔ Valid Γ := by
  classical
  simpa using (search_succeeds_iff_derives Γ.toList).symm.trans
    (search_succeeds_iff_valid Γ.toList)

theorem presentation_independent (L M : Input) (h : L.toFinset = M.toFinset) :
    (search ∅ L).succeeds = (search ∅ M).succeeds := by
  have hl := search_succeeds_iff_valid L
  have hm := search_succeeds_iff_valid M
  rw [h] at hl
  cases heL : (search ∅ L).succeeds <;> cases heM : (search ∅ M).succeeds <;> simp_all

/-- A supplied list is the computational input of this decision procedure. -/
def decideValid (L : Input) : Decidable (Valid L.toFinset) :=
  if h : (search ∅ L).succeeds = true then
    isTrue ((search_succeeds_iff_valid L).mp h)
  else isFalse (fun hv => h ((search_succeeds_iff_valid L).mpr hv))

def decideDerives (L : Input) : Decidable (Derives L.toFinset) :=
  if h : (search ∅ L).succeeds = true then
    isTrue ((search_succeeds_iff_derives L).mp h)
  else isFalse (fun hd => h ((search_succeeds_iff_derives L).mpr hd))

end Lemmatheca.ProofTheory.ClassicalPropositional.AnalyticSearch
