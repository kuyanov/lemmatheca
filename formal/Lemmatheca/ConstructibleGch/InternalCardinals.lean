import Lemmatheca.ConstructibleGch.Counting
import Lemmatheca.ConstructibleInnerModel.Axioms

namespace Lemmatheca.SetTheory.ConstructibleGch
open Lemmatheca.SetTheory.ConstructibleHierarchy
open Lemmatheca.SetTheory.ConstructibleInnerModel
open scoped Cardinal Ordinal ZFSet
universe u
noncomputable section

/-- The actual set of ordered pairs of the supplied bijection. -/
def bijectionGraph (X Y : ZFSet.{u}) (f : X ≃ Y) : ZFSet.{u} :=
  ZFSet.range (fun x : X => ZFSet.pair x.val (f x).val)

theorem bijectionGraph_mem (X Y : ZFSet.{u}) (f : X ≃ Y) (x : X) (y : Y) :
    ZFSet.pair x.val y.val ∈ bijectionGraph X Y f ↔ f x = y := by
  rw [bijectionGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨z,hz⟩
    have hx : z = x := Subtype.ext (ZFSet.pair_inj.mp hz).1
    subst z
    exact Subtype.ext (ZFSet.pair_inj.mp hz).2
  · intro h
    exact ⟨x, by rw [h]⟩

/-- Bijection availability in L refers to the graph, not just an ambient size equality. -/
def ConstructiblyEquinumerous (X Y : ZFSet.{u}) : Prop :=
  ∃ f : X ≃ Y, IsConstructible (bijectionGraph X Y f)

/-- Ordinals are compared using precisely the constructible bijection graphs. -/
def IsLCardinal (k : Ordinal.{u}) : Prop :=
  ∀ a < k, ¬ ConstructiblyEquinumerous k.toZFSet a.toZFSet

/-- The internal successor relation, without replacing it by the ambient successor. -/
def IsLSuccessor (k l : Ordinal.{u}) : Prop :=
  k < l ∧ IsLCardinal l ∧ ∀ a, k < a → a < l → ¬ IsLCardinal a

theorem constructiblyEquinumerous_card {X Y : ZFSet.{u}}
    (h : ConstructiblyEquinumerous X Y) : X.card = Y.card := by
  obtain ⟨f,_⟩ := h
  apply Cardinal.lift_injective.{u+1,u}
  rw [← ZFSet.cardinalMk_coe_sort, ← ZFSet.cardinalMk_coe_sort]
  exact Cardinal.mk_congr f

theorem ambient_cardinal_isLCardinal (k : Cardinal.{u}) : IsLCardinal k.ord := by
  intro a ha h
  have he := constructiblyEquinumerous_card h
  rw [Ordinal.card_toZFSet, Cardinal.card_ord, Ordinal.card_toZFSet] at he
  exact (Cardinal.lt_ord.mp ha).ne he.symm

theorem intervening_ordinal_card (k : Cardinal.{u}) (l : Ordinal.{u})
    (hlower : k.ord < l) (hupper : l < (Order.succ k).ord) : l.card = k := by
  apply le_antisymm
  · exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp hupper)
  · exact Cardinal.ord_le.mp hlower.le

theorem internal_power_card_of_bijection (k : Cardinal.{u}) (l : Ordinal.{u})
    (hlower : k.ord < l) (hupper : l < (Order.succ k).ord)
    (h : ConstructiblyEquinumerous (internalPowerSet k.ord.toZFSet) l.toZFSet) :
    (internalPowerSet k.ord.toZFSet).card = k := by
  have he := constructiblyEquinumerous_card h
  rw [Ordinal.card_toZFSet] at he
  exact he.trans (intervening_ordinal_card k l hlower hupper)

end
end Lemmatheca.SetTheory.ConstructibleGch
