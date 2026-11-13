import Lemmatheca.ClassicalPropositionalSequents.Properties
import Mathlib.Data.Finset.Max

/-! Ordered input presentations, literal states and computable terminal witnesses. -/

namespace Lemmatheca.ProofTheory.ClassicalPropositional.AnalyticSearch

abbrev Input := List (Nnf ℕ)

/-- The exact finite set represented by the processed and remaining formulas. -/
def context (S : Sequent ℕ) (L : Input) : Sequent ℕ := S ∪ L.toFinset

/-- Constants and compound formulas are not literals. -/
def Literal : Nnf ℕ → Prop
  | .pos _ | .neg _ => True
  | _ => False

def LiteralContext (S : Sequent ℕ) : Prop := ∀ A ∈ S, Literal A

/-- Finite scans, without selecting an ordering of the abstract finite set. -/
def positiveIndices (S : Sequent ℕ) : Finset ℕ :=
  S.biUnion fun A => match A with | .pos i => {i} | _ => ∅

def negativeIndices (S : Sequent ℕ) : Finset ℕ :=
  S.biUnion fun A => match A with | .neg i => {i} | _ => ∅

def clashIndices (S : Sequent ℕ) : Finset ℕ := positiveIndices S ∩ negativeIndices S

def terminalValuation (S : Sequent ℕ) (i : ℕ) : Bool := decide (i ∈ negativeIndices S)

/-- The returned index, when present, is the least actual clash. -/
def leastClash (S : Sequent ℕ) : Option {i // i ∈ clashIndices S} :=
  if h : (clashIndices S).Nonempty then
    some ⟨(clashIndices S).min' h, Finset.min'_mem _ h⟩
  else none

/-- A successful result contains the primitive finite tree itself. -/
inductive Result (Γ : Sequent ℕ) : Type
  | proved : Proof Γ → Result Γ
  | counter : (ℕ → Bool) → Result Γ

namespace Result

def Correct {Γ : Sequent ℕ} : Result Γ → Prop
  | .proved _ => True
  | .counter v => ∀ A ∈ Γ, Nnf.eval v A = false

def succeeds {Γ : Sequent ℕ} : Result Γ → Bool
  | .proved _ => true
  | .counter _ => false

/-- Only certificate data is cast; the tag and returned valuation still compute. -/
def transport {Γ Δ : Sequent ℕ} (h : Γ = Δ) : Result Γ → Result Δ
  | .proved p => .proved (h ▸ p)
  | .counter v => .counter v

end Result

theorem mem_positiveIndices (S : Sequent ℕ) (i : ℕ) :
    i ∈ positiveIndices S ↔ Nnf.pos i ∈ S := by
  simp only [positiveIndices, Finset.mem_biUnion]
  constructor
  · rintro ⟨A, hA, hi⟩
    cases A <;> simp_all
  · intro h
    exact ⟨.pos i, h, by simp⟩

theorem mem_negativeIndices (S : Sequent ℕ) (i : ℕ) :
    i ∈ negativeIndices S ↔ Nnf.neg i ∈ S := by
  simp only [negativeIndices, Finset.mem_biUnion]
  constructor
  · rintro ⟨A, hA, hi⟩
    cases A <;> simp_all
  · intro h
    exact ⟨.neg i, h, by simp⟩

theorem leastClash_le {S : Sequent ℕ} {i : {i // i ∈ clashIndices S}}
    (h : leastClash S = some i) : ∀ j ∈ clashIndices S, i.val ≤ j := by
  unfold leastClash at h
  split at h
  next hn =>
    cases Option.some.inj h
    exact fun j hj => Finset.min'_le _ j hj
  next hn => cases h

/-- Atomic identity or the prescribed negative-index valuation, with no choice. -/
def terminal (S : Sequent ℕ) : Result S :=
  match leastClash S with
  | some i => .proved (.identity i.val
      ((mem_positiveIndices S i.val).mp (Finset.mem_inter.mp i.property).1)
      ((mem_negativeIndices S i.val).mp (Finset.mem_inter.mp i.property).2))
  | none => .counter (terminalValuation S)

theorem terminal_correct (S : Sequent ℕ) (hS : LiteralContext S) :
    (terminal S).Correct := by
  cases hc : leastClash S with
  | some i => simp [terminal, hc, Result.Correct]
  | none =>
      have hn : ¬ (clashIndices S).Nonempty := by
        intro hh
        simp [leastClash, hh] at hc
      simp only [terminal, hc, Result.Correct]
      intro A hA
      have hLit := hS A hA
      cases A with
      | pos i =>
          have hi : i ∉ negativeIndices S := by
            intro hi
            exact hn ⟨i, Finset.mem_inter.mpr ⟨(mem_positiveIndices S i).mpr hA, hi⟩⟩
          simp [Nnf.eval, terminalValuation, hi]
      | neg i => simp [Nnf.eval, terminalValuation, (mem_negativeIndices S i).mpr hA]
      | bot => exact hLit.elim
      | top => exact hLit.elim
      | and A B => exact hLit.elim
      | or A B => exact hLit.elim

theorem valid_or_iff (Γ : Sequent ℕ) (A B : Nnf ℕ) :
    Valid (insert (.or A B) Γ) ↔ Valid (insert A (insert B Γ)) := by
  simp [Valid, SatisfiesSequent, Nnf.eval, or_assoc]

theorem valid_bot_iff (Γ : Sequent ℕ) : Valid (insert .bot Γ) ↔ Valid Γ := by
  simp [Valid, SatisfiesSequent, Nnf.eval]

theorem valid_and_iff (Γ : Sequent ℕ) (A B : Nnf ℕ) :
    Valid (insert (.and A B) Γ) ↔ Valid (insert A Γ) ∧ Valid (insert B Γ) := by
  simp only [Valid, SatisfiesSequent, Finset.exists_mem_insert, Nnf.eval, Bool.and_eq_true]
  constructor
  · intro h
    constructor
    · intro v
      rcases h v with h | h
      · exact Or.inl h.1
      · exact Or.inr h
    · intro v
      rcases h v with h | h
      · exact Or.inl h.2
      · exact Or.inr h
  · rintro ⟨hA, hB⟩ v
    rcases hA v with ha | hg
    · rcases hB v with hb | hg
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr hg
    · exact Or.inr hg

end Lemmatheca.ProofTheory.ClassicalPropositional.AnalyticSearch
