import Lemmatheca.OraclePadding.Basic
import Lemmatheca.TuringJump.Core
import Lemmatheca.PaddingAndInjectiveReductions.Halting

/-! Injective freezing and the two fixed relative halting recodings. -/
namespace Lemmatheca.ComputabilityTheory.OraclePadding

open OracleComputation OracleProgramNumberings TuringJump

set_option backward.isDefEq.respectTransparency false

theorem freeze_injective {e x f y : ℕ} (h : freeze e x = freeze f y) :
    e = f ∧ x = y := by
  have hs := code_bijective.1 h
  change Code.comp (decodeCode e) (constantCode x) =
    Code.comp (decodeCode f) (constantCode y) at hs
  injection hs with he hc
  refine ⟨?_, constantIndex_injective (congrArg encodeCode hc)⟩
  simpa only [encode_decode] using congrArg encodeCode he

theorem relative_oneone_complete (A S : Set ℕ) :
    RelativeCE A S ↔ S ≤₁ jump A := by
  constructor
  · intro hS
    obtain ⟨e, rfl⟩ := (relative_ce_iff_index A S).mp hS
    exact ⟨freeze e, (freeze_primitive.comp (Primrec.const e) Primrec.id).to_comp,
      fun _ _ h => (freeze_injective h).2, freeze_membership A e⟩
  · intro h
    exact (relative_ce_iff_jump A S).mpr h.to_many_one

noncomputable def haltsZero (A : Set ℕ) : Set ℕ := {e | (phi A e 0).Dom}

def diagonalToZero (e : ℕ) : ℕ := freeze e e

def zeroToDiagonal (e : ℕ) : ℕ := freeze e 0

theorem diagonalToZero_primitive : Primrec diagonalToZero := by
  exact freeze_primitive.comp Primrec.id Primrec.id

theorem diagonalToZero_injective : Function.Injective diagonalToZero := by
  intro e f h
  exact (freeze_injective h).1

theorem diagonalToZero_eval (A : Set ℕ) (e x : ℕ) :
    phi A (diagonalToZero e) x = phi A e e := by
  exact freeze_eval A e e x

theorem diagonalToZero_membership (A : Set ℕ) (e : ℕ) :
    e ∈ jump A ↔ diagonalToZero e ∈ haltsZero A := by
  change (phi A e e).Dom ↔ (phi A (diagonalToZero e) 0).Dom
  rw [diagonalToZero_eval]

theorem zeroToDiagonal_primitive : Primrec zeroToDiagonal := by
  exact freeze_primitive.comp Primrec.id (Primrec.const 0)

theorem zeroToDiagonal_injective : Function.Injective zeroToDiagonal := by
  intro e f h
  exact (freeze_injective h).1

theorem zeroToDiagonal_eval (A : Set ℕ) (e x : ℕ) :
    phi A (zeroToDiagonal e) x = phi A e 0 := by
  exact freeze_eval A e 0 x

theorem zeroToDiagonal_membership (A : Set ℕ) (e : ℕ) :
    e ∈ haltsZero A ↔ zeroToDiagonal e ∈ jump A := by
  change (phi A e 0).Dom ↔ (phi A (zeroToDiagonal e) (zeroToDiagonal e)).Dom
  rw [zeroToDiagonal_eval]

theorem halting_oneone_equiv (A : Set ℕ) : OneOneEquiv (jump A) (haltsZero A) := by
  exact ⟨⟨diagonalToZero, diagonalToZero_primitive.to_comp, diagonalToZero_injective,
    diagonalToZero_membership A⟩,
    ⟨zeroToDiagonal, zeroToDiagonal_primitive.to_comp, zeroToDiagonal_injective,
      zeroToDiagonal_membership A⟩⟩

end Lemmatheca.ComputabilityTheory.OraclePadding
