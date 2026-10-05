import Lemmatheca.SetTheory.Ordinals
import Lemmatheca.Entry.WellOrderedSets
import Mathlib.Order.Hom.Lex

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
      cases x with
      | inl a =>
        cases y with
        | inl b => cases a; cases b; rfl
        | inr b => exact Nat.noConfusion h
      | inr a =>
        cases y with
        | inl b => exact Nat.noConfusion h
        | inr b => exact congrArg Sum.inr (Nat.succ_inj.mp h)
    · intro n
      cases n with
      | zero => exact ⟨Sum.inl (), rfl⟩
      | succ n => exact ⟨Sum.inr n, rfl⟩
  · intro x y
    cases x <;> cases y <;>
      simp only [Sum.lex_inl_inl, Sum.lex_inr_inl, Sum.lex_inr_inr,
        firstPointEnumeration, emptyRelation, Nat.not_lt_zero, Nat.zero_lt_succ,
        Nat.succ_lt_succ_iff]
    exact ⟨fun _ => trivial, fun _ => Sum.Lex.sep _ _⟩

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
    constructor
    · rintro (h | ⟨h, h'⟩) <;> omega
    · intro h
      rcases Nat.lt_trichotomy i j with hij | hij | hij
      · exact Or.inl hij
      · exact Or.inr ⟨hij, by omega⟩
      · omega

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

end Lemmatheca.Entry.OrdinalArithmetic
