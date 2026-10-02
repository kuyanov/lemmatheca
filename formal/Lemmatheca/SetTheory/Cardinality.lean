import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Fintype.Powerset
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# Cardinality: displayed witnesses beyond the library existence theorems

Types represent arbitrary sets, and subtypes represent specified subsets. Binary
digits use `Bool` (`false` = 0, `true` = 1). Decimal digits use `Fin 10`.
New theorem bodies are deliberately left unfinished for the proving stage.
-/

namespace Lemmatheca.SetTheory

universe u v
variable {α : Type u} {β : Type v}

/-- The successive regions in the displayed Bernstein construction. -/
def bernsteinStage (f : α → β) (g : β → α) : ℕ → Set α
  | 0 => (Set.range g)ᶜ
  | n + 1 => g '' (f '' bernsteinStage f g n)

def bernsteinRegion (f : α → β) (g : β → α) : Set α :=
  ⋃ n, bernsteinStage f g n

/-- The last branch only totalizes the definition; the specification rules it out. -/
noncomputable def bernsteinMap (f : α → β) (g : β → α)
    (hg : Function.Injective g) (a : α) : β := by
  classical
  exact if a ∈ bernsteinRegion f g then f a
    else if ha : a ∈ Set.range g then (Equiv.ofInjective g hg).symm ⟨a, ha⟩ else f a

theorem bernstein_map_spec (f : α → β) (g : β → α) (hg : Function.Injective g) :
    (∀ a ∈ bernsteinRegion f g, bernsteinMap f g hg a = f a) ∧
    (∀ a ∉ bernsteinRegion f g, a ∈ Set.range g ∧ g (bernsteinMap f g hg a) = a) := by
  sorry

theorem bernstein_map_bijective (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Bijective (bernsteinMap f g hg) := by
  sorry

def diagonalSubset (F : α → Set α) : Set α := {a | a ∉ F a}

theorem diagonalSubset_omitted (F : α → Set α) :
    ∀ a, diagonalSubset F ≠ F a := by
  sorry

noncomputable def characteristicSequence (s : Set α) (a : α) : Bool := by
  classical
  exact decide (a ∈ s)

def sequenceSubset (s : α → Bool) : Set α := {a | s a = true}

theorem characteristic_inverse_laws :
    Function.LeftInverse (sequenceSubset (α := α)) characteristicSequence ∧
    Function.RightInverse (sequenceSubset (α := α)) characteristicSequence := by
  sorry

def binaryDiagonal (s : ℕ → ℕ → Bool) (n : ℕ) : Bool := !(s n n)

theorem binaryDiagonal_omitted (s : ℕ → ℕ → Bool) :
    ∀ n, binaryDiagonal s ≠ s n := by
  sorry

/-- The first word digit is the least significant binary digit. -/
def binaryWordCode (w : List Bool) : ℕ :=
  2 ^ w.length + w.foldr (fun b acc => b.toNat + 2 * acc) 0

theorem binaryWordCode_spec :
    Function.Injective binaryWordCode ∧ binaryWordCode [] = 1 ∧
    ∀ w, 2 ^ w.length ≤ binaryWordCode w ∧ binaryWordCode w < 2 ^ (w.length + 1) := by
  sorry

def FiniteSupportBinary := {s : ℕ → Bool // {j | s j = true}.Finite}

noncomputable def finiteSupportCode (s : FiniteSupportBinary) : ℕ :=
  ∑ j ∈ s.property.toFinset, 2 ^ j

theorem finiteSupportCode_spec : Function.Injective finiteSupportCode ∧
    ∀ s : FiniteSupportBinary, s.val = (fun _ => false) → finiteSupportCode s = 0 := by
  sorry

def DecimalDigits := ℕ → Fin 10

/-- The n-th digit has place value 10^(-(n+1)). -/
noncomputable def decimalValue (d : DecimalDigits) : ℝ :=
  ∑' n : ℕ, (d n).val / (10 : ℝ) ^ (n + 1)

def CanonicalDecimal (d : DecimalDigits) : Prop :=
  ¬ ∃ N : ℕ, ∀ n ≥ N, d n = 9

theorem canonical_decimal_expansion {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    ∃! d : DecimalDigits, CanonicalDecimal d ∧ decimalValue d = x := by
  sorry

def decimalDiagonal (d : ℕ → DecimalDigits) (n : ℕ) : Fin 10 :=
  if d n n = 1 then 2 else 1

theorem decimalDiagonal_spec (x : ℕ → ℝ) (d : ℕ → DecimalDigits)
    (hx : ∀ n, x n ∈ Set.Ioo 0 1)
    (hd : ∀ n, CanonicalDecimal (d n) ∧ decimalValue (d n) = x n) :
    decimalValue (decimalDiagonal d) ∈ Set.Ioo 0 1 ∧
    (1 / 9 : ℝ) ≤ decimalValue (decimalDiagonal d) ∧
    decimalValue (decimalDiagonal d) ≤ (2 / 9 : ℝ) ∧
    CanonicalDecimal (decimalDiagonal d) ∧
    ∀ n, decimalValue (decimalDiagonal d) ≠ x n := by
  sorry

theorem irrational_uncountable : ¬ Countable {x : ℝ // Irrational x} := by
  sorry

noncomputable def lineToSymmetricInterval (x : ℝ) : ℝ := x / (1 + |x|)

noncomputable def symmetricIntervalToLine (t : ℝ) : ℝ := t / (1 - |t|)

theorem line_interval_inverse_laws :
    Set.MapsTo lineToSymmetricInterval Set.univ (Set.Ioo (-1) 1) ∧
    (∀ x, symmetricIntervalToLine (lineToSymmetricInterval x) = x) ∧
    (∀ t ∈ Set.Ioo (-1) 1, lineToSymmetricInterval (symmetricIntervalToLine t) = t) := by
  sorry

theorem affine_interval_inverse_laws (a b : ℝ) (hab : a < b) :
    Set.BijOn (fun t : ℝ => a + (b - a) * t) (Set.Ioo 0 1) (Set.Ioo a b) ∧
    (∀ t ∈ Set.Ioo 0 1, (a + (b - a) * t - a) / (b - a) = t) ∧
    (∀ x ∈ Set.Ioo a b, (x - a) / (b - a) ∈ Set.Ioo 0 1 ∧
      a + (b - a) * ((x - a) / (b - a)) = x) := by
  sorry

end Lemmatheca.SetTheory
