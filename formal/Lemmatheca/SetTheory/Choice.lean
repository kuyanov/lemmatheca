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

theorem choice_iff_wellOrdering : ChoicePrinciple.{u} ↔ WellOrderingPrinciple.{u} := by
  -- Library reuse in Lean's classical foundation, rather than a ZF independence proof.
  constructor
  · intro _ α
    exact ⟨WellOrderingRel, inferInstance⟩
  · intro h ι α A hA
    classical
    obtain ⟨r, hr⟩ := h α
    exact ⟨fun i => hr.wf.min (A i) (hA i), fun i => hr.wf.min_mem (A i) (hA i)⟩

theorem wellOrdering_iff_zorn : WellOrderingPrinciple.{u} ↔ ZornPrinciple.{u} := by
  constructor
  · intro _ α p _ h
    letI := p
    exact zorn_le h
  · intro _ α
    exact ⟨WellOrderingRel, inferInstance⟩

theorem choice_iff_splitSurjections : ChoicePrinciple.{u} ↔ SplitSurjections.{u} := by
  constructor
  · intro h E I p hp
    obtain ⟨s, hs⟩ := h I E (fun i => {e | p e = i}) hp
    exact ⟨s, hs⟩
  · intro h ι α A hA
    let E := {p : ι × α // p.2 ∈ A p.1}
    let p : E → ι := fun x => x.val.1
    have hp : Surjective p := by
      intro i
      obtain ⟨a, ha⟩ := hA i
      exact ⟨⟨(i, a), ha⟩, rfl⟩
    obtain ⟨s, hs⟩ := h E ι p hp
    refine ⟨fun i => (s i).val.2, fun i => ?_⟩
    have hi := (s i).property
    have he : (s i).val.1 = i := hs i
    simpa only [he] using hi

/-- The Hartogs bound is the supremum of successors of well-ordered subset types. -/
def hartogsTypes (α : Type u) : Set Ordinal.{u} :=
  {o | ∃ (s : Set α) (r : s → s → Prop) (h : IsWellOrder s r), o = @Ordinal.type s r h}

noncomputable def hartogsBound (α : Type u) : Ordinal.{u} :=
  sSup ((fun o => o + 1) '' hartogsTypes α)

theorem hartogsBound_spec (α : Type u) :
    BddAbove (hartogsTypes α) ∧
    (∀ o ∈ hartogsTypes α, o + 1 ≤ hartogsBound α) ∧
    ¬ Nonempty ((hartogsBound α).ToType ↪ α) := by
  classical
  let B : Ordinal.{u} := (Order.succ (Cardinal.mk α)).ord
  have hlt : ∀ o ∈ hartogsTypes α, o < B := by
    rintro o ⟨s, r, h, rfl⟩
    letI := h
    apply Cardinal.card_le_iff.mp
    rw [Ordinal.card_type]
    exact Cardinal.mk_subtype_le _
  have hbd : BddAbove ((fun o => o + 1) '' hartogsTypes α) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨o, ho, rfl⟩
    simpa only [Order.succ_eq_add_one] using Order.succ_le_of_lt (hlt o ho)
  have hsucc : ∀ o ∈ hartogsTypes α, o + 1 ≤ hartogsBound α := by
    intro o ho
    exact le_csSup hbd ⟨o, ho, rfl⟩
  refine ⟨⟨B, fun o ho => (hlt o ho).le⟩, hsucc, ?_⟩
  rintro ⟨e⟩
  let t := hartogsBound α
  let f := (Equiv.ofInjective e e.injective).symm
  let r : Set.range e → Set.range e → Prop := fun x y => f x < f y
  have hr : IsWellOrder (Set.range e) r := (RelIso.preimage f (· < ·)).toRelEmbedding.isWellOrder
  have ht : t ∈ hartogsTypes α := by
    refine ⟨Set.range e, r, hr, ?_⟩
    letI := hr
    calc
      t = Ordinal.type ((· < ·) : t.ToType → t.ToType → Prop) := (Ordinal.type_toType t).symm
      _ = Ordinal.type r := Ordinal.type_eq.mpr ⟨(RelIso.preimage f (· < ·)).symm⟩
  exact (lt_add_one t).not_ge (hsucc t ht)

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
      Set.range (fun b : Set.Iio l => f b.val) = Set.range (some : α → Option α) := by
  classical
  let f := recursiveValue (choiceListingRule h s)
  let B : h.ToType → Set α := fun c => {a | ∀ b : Set.Iio c, f b.val ≠ some a}
  have heq (c : h.ToType) : f c = if hn : (B c).Nonempty then some (s (B c) hn) else none := by
    exact wellFounded_lt.fix_eq _ c
  have hfresh : ∀ c a, f c = some a → ∀ b, b < c → f b ≠ some a := by
    intro c a hca b hbc
    rw [heq] at hca
    split_ifs at hca with hn
    · have ha : s (B c) hn = a := Option.some.inj hca
      simpa only [ha] using hs (B c) hn ⟨b, hbc⟩
  have hinj (D : Set h.ToType) (hD : ∀ b ∈ D, f b ≠ none) :
      Injective (fun b : D => f b.val) := by
    intro b c he
    apply Subtype.ext
    rcases lt_trichotomy b.val c.val with hbc | heq | hcb
    · cases hfc : f c.val with
      | none => exact False.elim (hD c.val c.property hfc)
      | some a => exact False.elim (hfresh c.val a hfc b.val hbc (he.trans hfc))
    · exact heq
    · cases hfb : f b.val with
      | none => exact False.elim (hD b.val b.property hfb)
      | some a => exact False.elim (hfresh b.val a hfb c.val hcb (he.symm.trans hfb))
  have hnone : ∃ c, f c = none := by
    by_contra hn
    have hvalues : ∀ c, ∃ a, f c = some a := by
      intro c
      cases he : f c with
      | none => exact False.elim (hn ⟨c, he⟩)
      | some a => exact ⟨a, rfl⟩
    choose g hg using hvalues
    apply hh
    refine ⟨⟨g, ?_⟩⟩
    intro b c hbc
    have he : f b = f c := by rw [hg b, hg c, hbc]
    have hi := hinj Set.univ (fun b _ hb => hn ⟨b, hb⟩)
    exact congrArg Subtype.val (hi (a₁ := ⟨b, Set.mem_univ _⟩) (a₂ := ⟨c, Set.mem_univ _⟩) he)
  let D : Set h.ToType := {c | f c = none}
  have hD : D.Nonempty := hnone
  let l := wellFounded_lt.min D hD
  have hl : f l = none := wellFounded_lt.min_mem D hD
  have hbefore : ∀ b, b < l → f b ≠ none := by
    intro b hb hf
    exact wellFounded_lt.not_lt_min D hf hb
  refine ⟨l, hl, hbefore, hinj _ (fun b hb => hbefore b hb), ?_⟩
  apply Set.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    cases he : f b.val with
    | none => exact False.elim (hbefore b.val b.property he)
    | some a => exact ⟨a, he.symm⟩
  · rintro ⟨a, rfl⟩
    have hempty : ¬ (B l).Nonempty := by
      intro hn
      rw [heq, dite_eq_left hn] at hl
      contradiction
    have hex : ∃ b : Set.Iio l, f b.val = some a := by
      by_contra hn
      exact hempty ⟨a, fun b hb => hn ⟨b, hb⟩⟩
    exact hex

/-- Add a comparison using the reflexive closure of an explicitly strict relation. -/
def adjoinComparison {α : Type u} (r : α → α → Prop) (a b : α) : α → α → Prop :=
  fun x y => r x y ∨ (x = a ∨ r x a) ∧ (b = y ∨ r b y)

theorem adjoinComparison_spec {α : Type u} (r : α → α → Prop)
    (hirr : Std.Irrefl r) (htrans : IsTrans α r) (a b : α)
    (hne : a ≠ b) (hab : ¬ r a b) (hba : ¬ r b a) :
    Std.Irrefl (adjoinComparison r a b) ∧ IsTrans α (adjoinComparison r a b) ∧
    (∀ x y, r x y → adjoinComparison r a b x y) ∧
    adjoinComparison r a b a b ∧ ¬ r a b := by
  have hi : ∀ x, ¬ r x x := hirr.irrefl
  have ht : ∀ x y z, r x y → r y z → r x z := htrans.trans
  refine ⟨⟨?_⟩, ⟨?_⟩, ?_, ?_, hab⟩
  · intro x
    simp only [adjoinComparison]
    grind
  · intro x y z hxy hyz
    simp only [adjoinComparison] at *
    grind
  · intro x y hxy
    exact Or.inl hxy
  · exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩

end Lemmatheca.SetTheory

namespace Lemmatheca.Entry.AxiomOfChoice
open Set
universe u v

theorem empty_choice_cases {ι : Type u} {α : Type v} (A : ι → Set α) :
    (IsEmpty ι → ∃! c : ι → α, ∀ i, c i ∈ A i) ∧
    ((∃ i, A i = ∅) → ¬ ∃ c : ι → α, ∀ i, c i ∈ A i) := by
  constructor
  · intro h
    letI := h
    refine ⟨isEmptyElim, fun i => isEmptyElim i, ?_⟩
    intro c _
    exact funext fun i => isEmptyElim i
  · rintro ⟨i, hi⟩ ⟨c, hc⟩
    simpa [hi] using hc i

/-- Exactly two strict total orders extend the strict empty relation on two points. -/
theorem two_point_extensions :
    {r : Fin 2 → Fin 2 → Prop | Std.Irrefl r ∧ IsTrans (Fin 2) r ∧
      ∀ a b, a ≠ b → r a b ∨ r b a} =
    {((· < ·) : Fin 2 → Fin 2 → Prop), (fun a b : Fin 2 => b < a)} := by
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hi, ht, htot⟩
    have hir : ∀ a, ¬ r a a := hi.irrefl
    have htr : ∀ a b c, r a b → r b c → r a c := ht.trans
    rcases htot 0 1 (by decide) with h | h
    · left
      funext a b
      fin_cases a <;> fin_cases b <;> apply propext <;> norm_num <;> grind
    · right
      funext a b
      fin_cases a <;> fin_cases b <;> apply propext <;> norm_num <;> grind
  · rintro (rfl | rfl)
    · exact ⟨inferInstance, inferInstance, fun a b h => lt_or_gt_of_ne h⟩
    · refine ⟨⟨fun a => lt_irrefl a⟩, ⟨fun a b c hab hbc => hbc.trans hab⟩, ?_⟩
      intro a b h
      exact (lt_or_gt_of_ne h).symm

theorem total_extension_unique {α : Type u} (r s : α → α → Prop)
    (hr : IsLinearOrder α r) (hs : IsPartialOrder α s) (he : ∀ a b, r a b → s a b) :
    r = s := by
  letI := hr
  letI := hs
  funext a b
  apply propext
  refine ⟨he a b, fun hab => ?_⟩
  rcases total_of r a b with h | h
  · exact h
  · have hab' := antisymm_of s hab (he b a h)
    subst b
    exact refl_of r a

end Lemmatheca.Entry.AxiomOfChoice
