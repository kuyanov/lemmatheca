import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Category.PartOrd

/-!
# Additional order statements

Standard definitions, bounds, strict orders, and quotient constructions are bound
directly to mathlib. These are the remaining statements for the ordered-sets entry.
-/

namespace Lemmatheca.SetTheory

universe u v
variable {α : Type u} {β : Type v}

theorem equality_partial_order : IsPartialOrder α Eq := by
  exact { refl := Eq.refl, trans := fun _ _ _ => Eq.trans,
          antisymm := fun _ _ h _ => h }

theorem equality_order_total_iff : Std.Total (Eq : α → α → Prop) ↔ Subsingleton α := by
  constructor
  · intro h
    exact ⟨fun a b => (h.total a b).elim id Eq.symm⟩
  · intro h
    exact ⟨fun a b => Or.inl (h.elim a b)⟩

theorem finite_unique_minimal_isLeast [PartialOrder α] {s : Set α} (hs : s.Finite)
    {m : α} (hm : Minimal (· ∈ s) m) (hu : ∀ x, Minimal (· ∈ s) x → x = m) :
    IsLeast s m := by
  refine ⟨hm.1, ?_⟩
  intro a ha
  obtain ⟨b, hba, hb⟩ := hs.exists_le_minimal ha
  simpa [hu b hb] using hba

theorem finite_unique_maximal_isGreatest [PartialOrder α] {s : Set α} (hs : s.Finite)
    {m : α} (hm : Maximal (· ∈ s) m) (hu : ∀ x, Maximal (· ∈ s) x → x = m) :
    IsGreatest s m := by
  exact finite_unique_minimal_isLeast (α := αᵒᵈ) hs hm hu

theorem empty_orders [IsEmpty α] (r : α → α → Prop) :
    IsLinearOrder α r ∧ IsStrictOrder α r := by
  constructor
  · exact { refl := fun a => isEmptyElim a
            trans := fun a => isEmptyElim a
            antisymm := fun a => isEmptyElim a
            total := fun a => isEmptyElim a }
  · exact { irrefl := fun a => isEmptyElim a
            trans := fun a => isEmptyElim a }

theorem empty_poset_extrema_and_bounds [IsEmpty α] [Preorder α] (s : Set α) :
    (¬ ∃ a, IsLeast s a) ∧ (¬ ∃ a, IsGreatest s a) ∧
    (¬ ∃ a, Minimal (· ∈ s) a) ∧ (¬ ∃ a, Maximal (· ∈ s) a) ∧
    ¬ BddAbove s ∧ ¬ BddBelow s ∧ (¬ ∃ a, IsLUB s a) ∧ (¬ ∃ a, IsGLB s a) := by
  simp [BddAbove, BddBelow, Set.Nonempty]

theorem induced_order_antisymmetric_iff [PartialOrder β] (h : α → β) :
    Std.Antisymm (fun a b => h a ≤ h b) ↔ Function.Injective h := by
  constructor
  · intro hanti a b hab
    exact hanti.antisymm a b (le_of_eq hab) (le_of_eq hab.symm)
  · intro hinj
    exact ⟨fun a b hab hba => hinj (le_antisymm hab hba)⟩

theorem partial_order_quotient_iso [PartialOrder α] :
    ∃ e : α ≃o Antisymmetrization α (· ≤ ·),
      ∀ a, e a = toAntisymmetrization (· ≤ ·) a := by
  let e : α ≃o Antisymmetrization α (· ≤ ·) :=
    { toFun := toAntisymmetrization (· ≤ ·)
      invFun := Quotient.lift id (fun _ _ h => le_antisymm h.1 h.2)
      left_inv := fun _ => rfl
      right_inv := fun q => Quotient.inductionOn q (fun _ => rfl)
      map_rel_iff' := Iff.rfl }
  exact ⟨e, fun _ => rfl⟩

end Lemmatheca.SetTheory
