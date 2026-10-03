import Lemmatheca.SetTheory.Ordinals
import Mathlib.Order.Extension.Linear
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! Universe-relative formulations of choice and its equivalents.
These are statements within Lean's classical foundation, not an independence development over ZF.
`Option α` supplies an external marker `none` for the bounded listing construction. -/
namespace Lemmatheca.SetTheory
open Set Function
universe u

def ChoicePrinciple : Prop :=
  ∀ (ι α : Type u) (A : ι → Set α),
    (∀ i, (A i).Nonempty) → ∃ c : ι → α, ∀ i, c i ∈ A i

def WellOrderingPrinciple : Prop :=
  ∀ α : Type u, ∃ r : α → α → Prop, IsWellOrder α r

def ZornPrinciple : Prop :=
  ∀ (α : Type u) (p : PartialOrder α),
    Nonempty α → (∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) → ∃ m : α, IsMax m

def SplitSurjections : Prop :=
  ∀ (E I : Type u) (p : E → I), Surjective p → ∃ s : I → E, RightInverse s p

theorem choice_iff_wellOrdering : ChoicePrinciple.{u} ↔ WellOrderingPrinciple.{u} := by sorry

theorem wellOrdering_iff_zorn : WellOrderingPrinciple.{u} ↔ ZornPrinciple.{u} := by sorry

theorem choice_iff_splitSurjections : ChoicePrinciple.{u} ↔ SplitSurjections.{u} := by sorry

/-- The Hartogs bound is the supremum of successors of well-ordered subset types. -/
def hartogsTypes (α : Type u) : Set Ordinal.{u} :=
  {o | ∃ (s : Set α) (r : s → s → Prop) (h : IsWellOrder s r), o = @Ordinal.type s r h}

noncomputable def hartogsBound (α : Type u) : Ordinal.{u} :=
  sSup ((fun o => o + 1) '' hartogsTypes α)

theorem hartogsBound_spec (α : Type u) :
    BddAbove (hartogsTypes α) ∧
    (∀ o ∈ hartogsTypes α, o + 1 ≤ hartogsBound α) ∧
    ¬ Nonempty ((hartogsBound α).ToType ↪ α) := by sorry

/-- The selector receives any nonempty remaining subset, including after an invalid history. -/
noncomputable def choiceListingRule {α : Type u} (h : Ordinal.{u})
    (s : (B : Set α) → B.Nonempty → α) : RecursionRule h.ToType (Option α) := by
  classical
  exact fun _ history =>
    let B : Set α := {a | ∀ b, history b ≠ some a}
    if hn : B.Nonempty then some (s B hn) else none

theorem choiceListing_exhausts {α : Type u} (h : Ordinal.{u})
    (hh : ¬ Nonempty (h.ToType ↪ α))
    (s : (B : Set α) → B.Nonempty → α) (hs : ∀ B hn, s B hn ∈ B) :
    let f := recursiveValue (choiceListingRule h s)
    ∃ l : h.ToType, f l = none ∧ (∀ b, b < l → f b ≠ none) ∧
      Function.Injective (fun b : Set.Iio l => f b.val) ∧
      Set.range (fun b : Set.Iio l => f b.val) = Set.range (some : α → Option α) := by sorry

/-- Add a comparison using the reflexive closure of an explicitly strict relation. -/
def adjoinComparison {α : Type u} (r : α → α → Prop) (a b : α) : α → α → Prop :=
  fun x y => r x y ∨ (x = a ∨ r x a) ∧ (b = y ∨ r b y)

theorem adjoinComparison_spec {α : Type u} (r : α → α → Prop)
    (hirr : Std.Irrefl r) (htrans : IsTrans α r) (a b : α)
    (hne : a ≠ b) (hab : ¬ r a b) (hba : ¬ r b a) :
    Std.Irrefl (adjoinComparison r a b) ∧ IsTrans α (adjoinComparison r a b) ∧
    (∀ x y, r x y → adjoinComparison r a b x y) ∧
    adjoinComparison r a b a b ∧ ¬ r a b := by sorry

end Lemmatheca.SetTheory

namespace Lemmatheca.Entry.AxiomOfChoice
open Set
universe u v

theorem empty_choice_cases {ι : Type u} {α : Type v} (A : ι → Set α) :
    (IsEmpty ι → ∃! c : ι → α, ∀ i, c i ∈ A i) ∧
    ((∃ i, A i = ∅) → ¬ ∃ c : ι → α, ∀ i, c i ∈ A i) := by sorry

/-- Exactly two strict total orders extend the strict empty relation on two points. -/
theorem two_point_extensions :
    {r : Fin 2 → Fin 2 → Prop | Std.Irrefl r ∧ IsTrans (Fin 2) r ∧
      ∀ a b, a ≠ b → r a b ∨ r b a} =
    {((· < ·) : Fin 2 → Fin 2 → Prop), (fun a b : Fin 2 => b < a)} := by sorry

theorem total_extension_unique {α : Type u} (r s : α → α → Prop)
    (hr : IsLinearOrder α r) (hs : IsPartialOrder α s) (he : ∀ a b, r a b → s a b) :
    r = s := by sorry

end Lemmatheca.Entry.AxiomOfChoice
