import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Order.Hom.Lex
import Mathlib.Tactic

/-! Reusable OrdinalArithmetic definitions and results. -/

/-! Recursion characterizes ordinal addition and multiplication. An initial
segment followed by its inherited-order remainder has the original order type. -/
namespace Lemmatheca.SetTheory.OrdinalArithmetic
open Ordinal Order
open scoped Ordinal

/-- Recursion determines addition, including every nonzero limit stage. -/
theorem addition_recursion_unique (f : Ordinal → Ordinal → Ordinal)
    (hz : ∀ a, f a 0 = a)
    (hs : ∀ a b, f a (b + 1) = f a b + 1)
    (hl : ∀ a l, IsSuccLimit l → f a l = ⨆ b : Set.Iio l, f a b.val) :
    f = (· + ·) := by
  funext a b
  induction b using Ordinal.limitRecOn with
  | zero => simpa using hz a
  | add_one b ih => simp [hs, ih, add_assoc]
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
  | add_one b ih => simp [hs, ih, mul_add_one]
  | limit l hl' ih =>
    rw [hl a l hl']
    calc
      (⨆ b : Set.Iio l, f a b.val) = ⨆ b : Set.Iio l, a * b.val :=
        congrArg _ (funext fun b => ih b.val b.property)
      _ = a * l := by rw [← Ordinal.mul_iSup, hl'.iSup_Iio]

/-- The points of a representative of b whose ordinal positions are at least a. -/
abbrev remainderTail (a b : Ordinal) :=
  {x : b.ToType // a ≤ Ordinal.typein (α := b.ToType) (· < ·) x}

/-- The initial a-segment followed by its inherited-order tail has type b. -/
theorem remainderTail_type (a b : Ordinal) (h : a ≤ b) :
    a + typeLT (remainderTail a b) = b := by
  classical
  obtain hab | rfl := lt_or_eq_of_le h
  · obtain ⟨x, hx⟩ := typein_surj (α := b.ToType) (· < ·)
      (show a < typeLT b.ToType by simpa using hab)
    have hp : ({y : b.ToType | a ≤ typein (α := b.ToType) (· < ·) y} : Set b.ToType) =
        Set.Ici x := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_Ici]
      rw [← hx, typein_le_typein' b]
    have htail : typeLT (remainderTail a b) = typeLT (Set.Ici x) :=
      (Set.orderIsoOfEq _ _ hp).toRelIsoLT.ordinalType_congr
    rw [htail]
    let e := OrderIso.sumLexIioIci x
    let : WellFoundedLT (Set.Iio x ⊕ₗ Set.Ici x) :=
      e.toRelIsoLT.toRelEmbedding.wellFounded wellFounded_lt
    have hsum := e.toRelIsoLT.ordinalType_congr
    change type (Sum.Lex ((· < ·) : Set.Iio x → Set.Iio x → Prop)
      ((· < ·) : Set.Ici x → Set.Ici x → Prop)) = typeLT b.ToType at hsum
    simpa only [type_sum_lex, type_Iio_lt, hx, type_toType] using hsum
  · let : IsEmpty (remainderTail a a) :=
      ⟨fun x => (typein_lt_self x.val).not_ge x.property⟩
    rw [type_eq_zero_of_empty, add_zero]

end Lemmatheca.SetTheory.OrdinalArithmetic
