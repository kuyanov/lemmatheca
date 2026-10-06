import Lemmatheca.SetTheory.WellFoundedRecursion

/-! Reusable MostowskiCollapse definitions and results. -/

/-! Universe-relative set-valued recursion; this does not encode first-order ZF. -/
set_option autoImplicit false
universe u v
namespace Lemmatheca.SetTheory.MostowskiCollapse
open Lemmatheca.SetTheory.WellFoundedRecursion
open scoped ZFSet Ordinal

/-- Distinct points have distinct predecessor sets. -/
def Extensional {α : Type v} (R : α → α → Prop) : Prop :=
  ∀ a b, (∀ c, R c a ↔ R c b) → a = b

/-- Membership on a transitive set satisfies both collapse hypotheses. -/
theorem transitive_membership_hypotheses (T : ZFSet.{u}) (hT : T.IsTransitive) :
    WellFounded (fun a b : T => a.val ∈ b.val) ∧
    Extensional (fun a b : T => a.val ∈ b.val) := by
  refine ⟨InvImage.wf Subtype.val ZFSet.mem_wf, ?_⟩
  intro a b hab
  apply Subtype.ext
  apply ZFSet.ext
  intro c
  constructor
  · intro hc
    exact (hab ⟨c, hT.mem_trans hc a.property⟩).mp hc
  · intro hc
    exact (hab ⟨c, hT.mem_trans hc b.property⟩).mpr hc

/-- The empty carrier is well-founded and extensional. -/
theorem empty_hypotheses : WellFounded (fun _ _ : Empty => False) ∧
    Extensional (fun _ _ : Empty => False) := by
  refine ⟨⟨fun a => nomatch a⟩, ?_⟩
  intro a
  exact a.elim

/-- A point collapses to the set of collapsed predecessors. -/
noncomputable def collapse {α : Type v} [Small.{u} α] {R : α → α → Prop}
    (h : WellFounded R) : α → ZFSet.{u} :=
  recursiveValue h (fun _ values => ZFSet.range values)

/-- The collapse equation. -/
theorem collapse_equation {α : Type v} [Small.{u} α] {R : α → α → Prop}
    (h : WellFounded R) (a : α) :
    collapse.{u} h a = ZFSet.range (fun b : {b // R b a} => collapse.{u} h b.val) := by
  exact h.fix_eq _ a

/-- The collapse has transitive image and preserves relation edges. -/
theorem collapse_image {α : Type v} [Small.{u} α] {R : α → α → Prop}
    (h : WellFounded R) : (ZFSet.range (collapse.{u} h)).IsTransitive ∧
    (∀ a b, R a b → collapse.{u} h a ∈ collapse.{u} h b) := by
  have edge : ∀ a b, R a b → collapse.{u} h a ∈ collapse.{u} h b := by
    intro a b hab
    rw [collapse_equation]
    exact ZFSet.mem_range.mpr ⟨⟨a, hab⟩, rfl⟩
  refine ⟨?_, edge⟩
  intro x hx y hy
  obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hx
  rw [collapse_equation] at hy
  obtain ⟨b, rfl⟩ := ZFSet.mem_range.mp hy
  exact ZFSet.mem_range_self b.val

/-- An extensional collapse is injective and reflects membership. -/
theorem collapse_injective {α : Type v} [Small.{u} α] {R : α → α → Prop}
    (h : WellFounded R) (he : Extensional R) :
    Function.Injective (collapse.{u} h) ∧ ∀ a b, R a b ↔ collapse.{u} h a ∈ collapse.{u} h b := by
  have hinj : Function.Injective (collapse.{u} h) := by
    intro a
    induction a using h.induction with
    | h a ih =>
      intro b hab
      apply he a b
      intro c
      constructor
      · intro hca
        have hc := (collapse_image h).2 c a hca
        rw [hab, collapse_equation] at hc
        obtain ⟨d, hd⟩ := ZFSet.mem_range.mp hc
        have hcd := ih c hca hd.symm
        exact hcd ▸ d.property
      · intro hcb
        have hc := (collapse_image h).2 c b hcb
        rw [← hab, collapse_equation] at hc
        obtain ⟨d, hd⟩ := ZFSet.mem_range.mp hc
        have hdc := ih d.val d.property hd
        exact hdc ▸ d.property
  refine ⟨hinj, ?_⟩
  intro a b
  refine ⟨(collapse_image h).2 a b, ?_⟩
  intro hab
  rw [collapse_equation] at hab
  obtain ⟨c, hc⟩ := ZFSet.mem_range.mp hab
  exact hinj hc ▸ c.property

/-- A well-founded extensional relation has a unique transitive membership representation. -/
theorem mostowski {α : Type v} [Small.{u} α] {R : α → α → Prop}
    (h : WellFounded R) (he : Extensional R) :
    ∃! p : ZFSet.{u} × (α → ZFSet.{u}),
      p.1.IsTransitive ∧ ZFSet.range p.2 = p.1 ∧ Function.Injective p.2 ∧
      ∀ a b, R a b ↔ p.2 a ∈ p.2 b := by
  refine ⟨⟨ZFSet.range (collapse.{u} h), collapse.{u} h⟩,
    ⟨(collapse_image h).1, rfl, (collapse_injective h he).1,
      (collapse_injective h he).2⟩, ?_⟩
  intro p hp
  have heq : ∀ a, p.2 a = ZFSet.range (fun b : {b // R b a} => p.2 b.val) := by
    intro a
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      have hxM := hp.1.mem_trans hx (hp.2.1 ▸ ZFSet.mem_range_self a)
      rw [← hp.2.1] at hxM
      obtain ⟨b, rfl⟩ := ZFSet.mem_range.mp hxM
      exact ZFSet.mem_range.mpr ⟨⟨b, (hp.2.2.2 b a).mpr hx⟩, rfl⟩
    · intro hx
      obtain ⟨b, rfl⟩ := ZFSet.mem_range.mp hx
      exact (hp.2.2.2 b.val a).mp b.property
  have hf : p.2 = collapse.{u} h :=
    (recursion_exists_unique h (fun _ values => ZFSet.range values)).unique heq
      (collapse_equation h)
  apply Prod.ext
  · exact hp.2.1.symm.trans (congrArg ZFSet.range hf)
  · exact hf

/-- The empty carrier collapses to the empty image. -/
theorem empty_collapse (h : WellFounded (fun _ _ : Empty => False)) :
    ZFSet.range (collapse.{u} h) = ∅ := by
  ext x
  simp only [ZFSet.mem_range, ZFSet.notMem_empty, iff_false]
  rintro ⟨a, _⟩
  exact a.elim

/-- No predecessors give the empty set; a unique predecessor gives a singleton. -/
theorem collapse_small_predecessors {α : Type v} [Small.{u} α]
    {R : α → α → Prop} (h : WellFounded R) (a : α) :
    ((∀ b, ¬ R b a) → collapse.{u} h a = ∅) ∧
    (∀ b, (∀ c, R c a ↔ c = b) → collapse.{u} h a = {collapse.{u} h b}) := by
  constructor
  · intro ha
    rw [collapse_equation]
    ext x
    simp only [ZFSet.mem_range, ZFSet.notMem_empty, iff_false]
    rintro ⟨b, _⟩
    exact ha b.val b.property
  · intro b hb
    rw [collapse_equation]
    ext x
    simp only [ZFSet.mem_range, ZFSet.mem_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact congrArg (collapse h) ((hb c.val).mp c.property)
    · intro hx
      exact ⟨⟨b, (hb b).mpr rfl⟩, hx.symm⟩

/-- Membership on a transitive set collapses to itself. -/
theorem transitive_fixed (T : ZFSet.{u}) (hT : T.IsTransitive)
    (h : WellFounded (fun a b : T => a.val ∈ b.val)) :
    (∀ a : T, collapse.{u} h a = a.val) ∧ ZFSet.range (collapse.{u} h) = T := by
  have heq : ∀ a : T, a.val = ZFSet.range (fun b : {b : T // b.val ∈ a.val} => b.val.val) := by
    intro a
    ext x
    simp only [ZFSet.mem_range]
    constructor
    · intro hx
      exact ⟨⟨⟨x, hT.mem_trans hx a.property⟩, hx⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact b.property
  have hf : Subtype.val = collapse.{u} h :=
    (recursion_exists_unique h (fun _ values => ZFSet.range values)).unique heq
      (collapse_equation h)
  refine ⟨fun a => congrFun hf.symm a, ?_⟩
  rw [← hf]
  ext x
  simp

/-- A membership isomorphism between transitive sets fixes every element. -/
theorem transitive_iso_identity (T U : ZFSet.{u}) (hT : T.IsTransitive) (hU : U.IsTransitive)
    (e : T ≃ U) (he : ∀ a b : T, a.val ∈ b.val ↔ (e a).val ∈ (e b).val) :
    T = U ∧ ∀ a : T, (e a).val = a.val := by
  have h := (transitive_membership_hypotheses T hT).1
  have hrep : ZFSet.range (fun a : T => (e a).val) = U := by
    ext x
    simp only [ZFSet.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
  have hp : U.IsTransitive ∧ ZFSet.range (fun a : T => (e a).val) = U ∧
      Function.Injective (fun a : T => (e a).val) ∧
      ∀ a b : T, a.val ∈ b.val ↔ (e a).val ∈ (e b).val :=
    ⟨hU, hrep, Subtype.val_injective.comp e.injective, he⟩
  have hu : (U, fun a : T => (e a).val) =
      (ZFSet.range (collapse.{u} h), collapse.{u} h) :=
    (mostowski h (transitive_membership_hypotheses T hT).2).unique hp
      ⟨(collapse_image h).1, rfl, (collapse_injective h
        (transitive_membership_hypotheses T hT).2).1,
        (collapse_injective h (transitive_membership_hypotheses T hT).2).2⟩
  have hf : (fun a : T => (e a).val) = collapse.{u} h := congrArg Prod.snd hu
  have hfixed := transitive_fixed T hT h
  refine ⟨?_, fun a => (congrFun hf a).trans (hfixed.1 a)⟩
  calc
    T = ZFSet.range (collapse.{u} h) := hfixed.2.symm
    _ = ZFSet.range (fun a : T => (e a).val) := congrArg ZFSet.range hf.symm
    _ = U := hrep

/-- A set-sized well-order collapses to its ordinal order type. -/
theorem wellOrder_collapse {α : Type u} (R : α → α → Prop) [h : IsWellOrder α R] :
    Extensional R ∧ ∃ hw : WellFounded R,
      ZFSet.range (collapse.{u} hw) = (@Ordinal.type α R h).toZFSet := by
  have he : Extensional R := by
    intro a b hab
    by_contra hn
    rcases trichotomous_of R a b with ha | ha | ha
    · exact irrefl a ((hab a).mpr ha)
    · exact hn ha
    · exact irrefl b ((hab b).mp ha)
  let hw : WellFounded R := IsWellOrder.wf
  have heq : ∀ a, (Ordinal.typein R a).toZFSet =
      ZFSet.range (fun b : {b // R b a} => (Ordinal.typein R b.val).toZFSet) := by
    intro a
    ext x
    rw [Ordinal.mem_toZFSet_iff, ZFSet.mem_range]
    constructor
    · rintro ⟨o, ho, rfl⟩
      obtain ⟨b, rfl⟩ := Ordinal.typein_surj R (ho.trans (Ordinal.typein_lt_type R a))
      exact ⟨⟨b, (Ordinal.typein_lt_typein R).mp ho⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Ordinal.typein R b.val, (Ordinal.typein_lt_typein R).mpr b.property, rfl⟩
  have hf : (fun a => (Ordinal.typein R a).toZFSet) = collapse.{u} hw :=
    (recursion_exists_unique hw (fun _ values => ZFSet.range values)).unique heq
      (collapse_equation hw)
  refine ⟨he, hw, ?_⟩
  rw [← hf]
  ext x
  rw [ZFSet.mem_range, Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Ordinal.typein R a, Ordinal.typein_lt_type R a, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    obtain ⟨a, rfl⟩ := Ordinal.typein_surj R ho
    exact ⟨a, rfl⟩

end Lemmatheca.SetTheory.MostowskiCollapse
