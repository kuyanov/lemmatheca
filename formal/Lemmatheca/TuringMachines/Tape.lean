import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum

/-! Fixed-coordinate, finitely supported tapes for the introductory machine model. -/
namespace Lemmatheca.ComputabilityTheory.TuringMachines

structure Alphabet (Γ : Type*) where
  blank : Γ
  mark : Γ
  mark_ne_blank : mark ≠ blank

inductive Move
  | left | stay | right
  deriving DecidableEq

instance moveFintype : Fintype Move :=
  ⟨{.left, .stay, .right}, by intro m; cases m <;> simp⟩

def Move.displacement : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure Tape (Γ : Type*) (blank : Γ) where
  cells : ℤ → Γ
  finite_support : {z | cells z ≠ blank}.Finite

namespace Tape
variable {Γ : Type*} {blank : Γ}

instance : CoeFun (Tape Γ blank) (fun _ => ℤ → Γ) := ⟨Tape.cells⟩

def support (t : Tape Γ blank) : Set ℤ := {z | t z ≠ blank}

noncomputable def write (t : Tape Γ blank) (h : ℤ) (b : Γ) : Tape Γ blank := by
  classical
  refine ⟨Function.update t.cells h b, ?_⟩
  apply (t.finite_support.union (Set.finite_singleton h)).subset
  intro z hz
  by_cases he : z = h
  · exact Or.inr he
  · exact Or.inl (by simpa [Function.update_of_ne he] using hz)

theorem support_write (t : Tape Γ blank) (h : ℤ) (b : Γ) :
    (t.write h b).support ⊆ t.support ∪ {h} := by
  classical
  intro z hz
  by_cases he : z = h
  · exact Or.inr he
  · exact Or.inl (by simpa [support, write, Function.update_of_ne he] using hz)

theorem write_same (t : Tape Γ blank) (h : ℤ) : t.write h (t h) = t := by
  classical
  cases t
  simp [write]

theorem support_bounded (t : Tape Γ blank) :
    ∃ B : ℕ, ∀ z ∈ t.support, -(B : ℤ) ≤ z ∧ z ≤ B := by
  classical
  refine ⟨t.finite_support.toFinset.sup Int.natAbs, ?_⟩
  intro z hz
  have hmem : z ∈ t.finite_support.toFinset := by simpa [support] using hz
  have hbound := Finset.le_sup (f := Int.natAbs) hmem
  have hcast : (z.natAbs : ℤ) ≤ (t.finite_support.toFinset.sup Int.natAbs : ℕ) :=
    Int.ofNat_le.mpr hbound
  have hpos := Int.le_natAbs (a := z)
  have hneg := Int.le_natAbs (a := -z)
  simp only [Int.natAbs_neg] at hneg
  omega

end Tape

structure Config {Γ : Type*} (A : Alphabet Γ) (Q : Type*) where
  state : Q
  head : ℤ
  tape : Tape Γ A.blank

end Lemmatheca.ComputabilityTheory.TuringMachines
