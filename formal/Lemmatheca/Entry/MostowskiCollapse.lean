import Lemmatheca.SetTheory.MostowskiCollapse

/-! Particular examples and counterexamples for the human entry. -/

set_option autoImplicit false
universe u v
namespace Lemmatheca.Entry.MostowskiCollapse
open Lemmatheca.SetTheory.MostowskiCollapse Lemmatheca.SetTheory.WellFoundedRecursion
open scoped ZFSet Ordinal

/-- The relation with just the edges zero to one and one to two. -/
def pathRelation (a b : Fin 3) : Prop := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)

/-- The path collapses to a transitive set which is not an ordinal. -/
theorem path_example : ∃ h : WellFounded pathRelation,
    Extensional pathRelation ∧
    collapse.{u} h 0 = ∅ ∧ collapse.{u} h 1 = {∅} ∧ collapse.{u} h 2 = {{∅}} ∧
    ZFSet.range (collapse.{u} h) = {∅, {∅}, {{∅}}} ∧
    ¬ ∃ o : Ordinal.{u}, ZFSet.range (collapse.{u} h) = o.toZFSet := by
  have h : WellFounded pathRelation := (measure Fin.val).wf.mono (by
    intro a b hab
    change a.val < b.val
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
  have he : Extensional pathRelation := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first | rfl | have h0 := hab 0; have h1 := hab 1; simp [pathRelation] at *
  have h0 : collapse.{u} h 0 = ∅ :=
    (collapse_small_predecessors.{u} h 0).1 (by intro b; simp [pathRelation])
  have h1 : collapse.{u} h 1 = {∅} := by
    rw [(collapse_small_predecessors.{u} h 1).2 0 (by intro c; simp [pathRelation]), h0]
  have h2 : collapse.{u} h 2 = {{∅}} := by
    rw [(collapse_small_predecessors.{u} h 2).2 1 (by intro c; simp [pathRelation]), h1]
  have hr : ZFSet.range (collapse.{u} h) = {∅, {∅}, {{∅}}} := by
    ext x
    simp only [ZFSet.mem_range, ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a <;> simp [h0, h1, h2]
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
  refine ⟨h, he, h0, h1, h2, hr, ?_⟩
  rintro ⟨o, ho⟩
  have ht : ({{∅}} : ZFSet.{u}).IsTransitive :=
    ((ZFSet.isOrdinal_toZFSet o).mem (by rw [← ho, hr]; simp)).isTransitive
  have hempty : (∅ : ZFSet.{u}) ∈ {{∅}} :=
    ht.mem_trans (show (∅ : ZFSet.{u}) ∈ {∅} by simp) (show ({∅} : ZFSet.{u}) ∈ {{∅}} by simp)
  have heq : (∅ : ZFSet.{u}) = {∅} := ZFSet.mem_singleton.mp hempty
  have hmem : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := by simp
  rw [← heq] at hmem
  exact ZFSet.notMem_empty _ hmem

/-- Isolated points merge, whereas a self-loop prevents any membership representation. -/
theorem hypotheses_examples :
    (∃ h : WellFounded (fun _ _ : Fin 2 => False),
      ¬ Extensional (fun _ _ : Fin 2 => False) ∧
      ZFSet.range (collapse.{u} h) = {∅} ∧ ¬ Function.Injective (collapse.{u} h)) ∧
    (Extensional (fun _ _ : Unit => True) ∧ ¬ WellFounded (fun _ _ : Unit => True)) ∧
    (¬ ∃ f : Unit → ZFSet.{u}, f () ∈ f ()) ∧
    (¬ ∃ f : Unit → ZFSet.{u}, f () = {f ()}) := by
  have h : WellFounded (fun _ _ : Fin 2 => False) := ⟨fun a => .intro a (by simp)⟩
  have hc : ∀ a : Fin 2, collapse.{u} h a = ∅ :=
    fun a => (collapse_small_predecessors.{u} h a).1 (by simp)
  refine ⟨⟨h, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro he
    have hn : (0 : Fin 2) = 1 := he 0 1 (by simp)
    exact Fin.zero_ne_one hn
  · ext x
    simp only [ZFSet.mem_range, ZFSet.mem_singleton]
    constructor
    · rintro ⟨a, rfl⟩; exact hc a
    · intro hx; exact ⟨0, (hc 0).trans hx.symm⟩
  · intro hi
    exact Fin.zero_ne_one (hi ((hc 0).trans (hc 1).symm))
  · intro a b _; exact Subsingleton.elim a b
  · intro hw; exact hw.irrefl.irrefl () trivial
  · rintro ⟨f, hf⟩; exact ZFSet.mem_irrefl _ hf
  · rintro ⟨f, hf⟩
    apply ZFSet.mem_irrefl (f ())
    have hm : f () ∈ ({f ()} : ZFSet.{u}) := by simp
    rwa [← hf] at hm

/-- Two isolated points cannot have an injective transitive membership representation. -/
theorem isolated_pair_no_representation :
    ¬ ∃ M : ZFSet.{u}, ∃ π : Fin 2 → ZFSet.{u},
      M.IsTransitive ∧ ZFSet.range π = M ∧ Function.Injective π ∧
      ∀ a b, False ↔ π a ∈ π b := by
  rintro ⟨M, π, hM, hr, hi, he⟩
  have hempty : ∀ a, π a = ∅ := by
    intro a
    ext x
    simp only [ZFSet.notMem_empty, iff_false]
    intro hx
    have hxM := hM.mem_trans hx (show π a ∈ M from hr ▸ (ZFSet.mem_range.mpr ⟨a, rfl⟩))
    rw [← hr] at hxM
    obtain ⟨b, rfl⟩ := ZFSet.mem_range.mp hxM
    exact (he b a).mpr hx
  exact Fin.zero_ne_one (hi ((hempty 0).trans (hempty 1).symm))

end Lemmatheca.Entry.MostowskiCollapse
