import Lemmatheca.SetTheory.Ordinals
import Lemmatheca.Entry.WellOrderedSets

/-! Explicit order-preserving maps used in the arithmetic examples.
`Prod.Lex` puts the block index first, unlike coordinatewise product order. -/
namespace Lemmatheca.Entry.OrdinalArithmetic
open Ordinal Order
open scoped Ordinal

/-- The extra first point goes to zero; the following naturals shift by one. -/
def firstPointEnumeration : Unit ⊕ ℕ → ℕ
  | Sum.inl _ => 0
  | Sum.inr n => n + 1

theorem firstPointEnumeration_order_iso :
    Function.Bijective firstPointEnumeration ∧
    ∀ x y, Sum.Lex (@emptyRelation Unit) ((· < ·) : ℕ → ℕ → Prop) x y ↔
      firstPointEnumeration x < firstPointEnumeration y := by
  constructor
  · constructor
    · intro x y h
      cases x <;> cases y <;> simp_all [firstPointEnumeration]
    · intro n
      cases n with
      | zero => exact ⟨Sum.inl (), rfl⟩
      | succ n => exact ⟨Sum.inr n, rfl⟩
  · intro x y
    cases x <;> cases y <;> simp [firstPointEnumeration, emptyRelation]

def twoPointBlocks (p : ℕ × Fin 2) : ℕ := 2 * p.1 + p.2.val

theorem twoPointBlocks_order_iso :
    Function.Bijective twoPointBlocks ∧
    ∀ x y, Prod.Lex ((· < ·) : ℕ → ℕ → Prop) ((· < ·) : Fin 2 → Fin 2 → Prop) x y ↔
      twoPointBlocks x < twoPointBlocks y := by
  constructor
  · constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ h
      have ha := a.isLt
      have hb := b.isLt
      simp only [twoPointBlocks] at h
      have hij : i = j := by omega
      have hab : a = b := Fin.ext (by omega)
      simp [hij, hab]
    · intro n
      refine ⟨(n / 2, ⟨n % 2, Nat.mod_lt n (by decide)⟩), ?_⟩
      simp only [twoPointBlocks]
      omega
  · rintro ⟨i, a⟩ ⟨j, b⟩
    have ha := a.isLt
    have hb := b.isLt
    simp only [Prod.lex_iff, twoPointBlocks, Fin.lt_def]
    omega

/-- Recursion determines addition, including every nonzero limit stage. -/
theorem addition_recursion_unique (f : Ordinal → Ordinal → Ordinal)
    (hz : ∀ a, f a 0 = a)
    (hs : ∀ a b, f a (b + 1) = f a b + 1)
    (hl : ∀ a l, IsSuccLimit l → f a l = ⨆ b : Set.Iio l, f a b.val) :
    f = (· + ·) := by
  funext a b
  induction b using Ordinal.limitRecOn with
  | zero => simpa using hz a
  | add_one b ih => simpa [hs, ih, add_assoc]
  | limit l hl' ih =>
    rw [hl a l hl']
    have : Nonempty (Set.Iio l) := ⟨⟨0, hl'.bot_lt⟩⟩
    calc
      (⨆ b : Set.Iio l, f a b.val) = ⨆ b : Set.Iio l, a + b.val :=
        congrArg _ (funext fun b => ih b.val b.property)
      _ = a + l := by rw [← Ordinal.add_iSup, hl'.iSup_Iio]

theorem multiplication_recursion_unique (f : Ordinal → Ordinal → Ordinal)
    (hz : ∀ a, f a 0 = 0)
    (hs : ∀ a b, f a (b + 1) = f a b + a)
    (hl : ∀ a l, IsSuccLimit l → f a l = ⨆ b : Set.Iio l, f a b.val) :
    f = (· * ·) := by
  funext a b
  induction b using Ordinal.limitRecOn with
  | zero => simpa using hz a
  | add_one b ih => simpa [hs, ih, mul_add_one]
  | limit l hl' ih =>
    rw [hl a l hl']
    calc
      (⨆ b : Set.Iio l, f a b.val) = ⨆ b : Set.Iio l, a * b.val :=
        congrArg _ (funext fun b => ih b.val b.property)
      _ = a * l := by rw [← Ordinal.mul_iSup, hl'.iSup_Iio]

end Lemmatheca.Entry.OrdinalArithmetic
