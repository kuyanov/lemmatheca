import Lemmatheca.SetTheory.Clubs
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Set.Countable

namespace Lemmatheca.SetTheory.PressingDown

open Set Cardinal Order
universe u v

variable {α : Type u} [LinearOrder α]

def RegressiveOn (S : Set α) (f : α → α) : Prop := ∀ a ∈ S, f a < a

theorem regressive_excludes_minimum [OrderBot α] {S : Set α} {f : α → α}
    (hf : RegressiveOn S f) : (⊥ : α) ∉ S := by
  exact fun h => (not_lt_bot) (hf _ h)

theorem constant_minimum_regressive [OrderBot α] :
    RegressiveOn (Ioi (⊥ : α)) (fun _ => ⊥) := by
  exact fun _ h => h

/-- A predecessor is selected only at points which have an immediate predecessor. -/
noncomputable def successorPredecessor (a : α) : α := by
  classical
  exact if h : ∃ b, b ⋖ a then Classical.choose h else a

theorem successor_predecessor_specification :
    RegressiveOn (Clubs.successorPoints α) successorPredecessor ∧
      Set.InjOn successorPredecessor (Clubs.successorPoints α) := by
  classical
  have hpred {a : α} (ha : a ∈ Clubs.successorPoints α) : successorPredecessor a ⋖ a := by
    have ha' : ∃ b, b ⋖ a := ha
    simpa [successorPredecessor, ha'] using Classical.choose_spec ha'
  refine ⟨fun a ha => (hpred ha).lt, ?_⟩
  intro a ha b hb hab
  exact (hab ▸ hpred ha).unique_right (hpred hb)

theorem successor_fibers_nonstationary [WellFoundedLT α] (hα : ℵ₀ < cof α) :
    ∀ b, ¬ IsStationary (Clubs.successorPoints α ∩ successorPredecessor ⁻¹' {b}) := by
  intro b h
  obtain ⟨a, ha⟩ := h.nonempty
  obtain ⟨c, hc, hac⟩ := Clubs.stationary_unbounded hα h a
  have heq := successor_predecessor_specification.2 ha.1 hc.1 (ha.2.trans hc.2.symm)
  exact hac.ne heq

theorem identity_boundary [WellFoundedLT α] (hα : ℵ₀ < cof α) :
    IsStationary (univ : Set α) ∧ ¬ RegressiveOn (univ : Set α) (id : α → α) ∧
      ∀ a : α, ¬ IsStationary ({a} : Set α) := by
  have : Nonempty α := by
    cases isEmpty_or_nonempty α
    · simp at hα
    · assumption
  refine ⟨IsStationary.univ, ?_, ?_⟩
  · intro h
    obtain ⟨a⟩ := ‹Nonempty α›
    exact (lt_irrefl a) (h a (mem_univ a))
  · intro a h
    obtain ⟨b, hb, hab⟩ := Clubs.stationary_unbounded hα h a
    exact hab.ne' hb

theorem stationary_countable_range_fiber [WellFoundedLT α] (hα : ℵ₀ < cof α)
    {S : Set α} (hS : IsStationary S) {β : Type v} (g : S → β)
    (hg : (Set.range g).Countable) :
    ∃ b, IsStationary {a | ∃ ha : a ∈ S, g ⟨a, ha⟩ = b} := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS.nonempty
  let : Countable (Set.range g) := hg.to_subtype
  let f (a : α) : Set.range g :=
    if ha : a ∈ S then ⟨g ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩
    else ⟨g ⟨a₀, ha₀⟩, ⟨⟨a₀, ha₀⟩, rfl⟩⟩
  have hsmall : lift.{u} #(Set.range g) < lift.{v} (cof α) := by
    exact (Cardinal.lift_le.mpr Cardinal.mk_le_aleph0).trans_lt
      (by simpa using Cardinal.lift_lt.{u, v}.mpr hα)
  obtain ⟨b, hb⟩ := Clubs.stationary_small_fiber hα hsmall hS f
  refine ⟨b.1, hb.mono ?_⟩
  intro a ha
  refine ⟨ha.1, ?_⟩
  have heq := congrArg Subtype.val ha.2
  simpa [f, ha.1] using heq

end Lemmatheca.SetTheory.PressingDown
