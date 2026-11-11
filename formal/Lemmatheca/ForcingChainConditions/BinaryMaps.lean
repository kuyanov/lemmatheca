import Lemmatheca.ForcingChainConditions.Orders
import Lemmatheca.ForcingAndGenericFilters.Cohen

namespace Lemmatheca.SetTheory.ForcingChainConditions
open Set Order
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.FinitePartialMaps
universe u
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type u}

theorem binary_graph_injective :
    Function.Injective (graph : BinaryMap I → Set (I × Bool)) := by
  classical
  have hl (p : BinaryMap I) (i : I) (b : Bool) :
      (i, b) ∈ graph p ↔ p.lookup i = some b := Finmap.lookup_eq_some_iff.symm
  intro p q h
  apply Finmap.ext_lookup
  intro i
  apply Option.ext
  intro b
  simp only [← hl, h]

@[instance_reducible] def binaryOrder (I : Type u) : PartialOrder (BinaryMap I) :=
  PartialOrder.lift (fun p : BinaryMap I => OrderDual.toDual (graph p)) binary_graph_injective

@[instance_reducible] def binaryOrderTop (I : Type u) : @OrderTop (BinaryMap I) (binaryOrder I).toLE := by
  letI := binaryOrder I
  exact {
    top := ∅
    le_top := by
      intro p
      change graph (∅ : BinaryMap I) ⊆ graph p
      rintro ⟨i, b⟩ hb
      have he : (∅ : BinaryMap I).lookup i = some b := Finmap.lookup_eq_some_iff.mpr hb
      simp at he
  }


theorem binary_order (q p : BinaryMap I) :
    @LE.le _ (binaryOrder I).toLE q p ↔ Extends q p := by
  rfl

theorem binary_compatible (q p : BinaryMap I) :
    @ForcingAndGenericFilters.Compatible _ (binaryOrder I) q p ↔
      FinitePartialMaps.Compatible q p := by
  rfl

theorem binary_ccc : @CCC (BinaryMap I) (binaryOrder I) := by
  intro A hA
  apply FinitePartialMaps.incompatible_family_countable
  intro p hp q hq hpq hcomp
  exact hA hp hq hpq ((binary_compatible p q).mpr hcomp)

theorem binary_countable [Countable I] : Countable (BinaryMap I) := by
  have hi : Function.Injective (fun p : BinaryMap I => p.entries) :=
    fun _ _ h => Finmap.ext h
  exact hi.countable

theorem cohen_ccc : CCC Cohen := by
  exact binary_ccc (I := ℕ)

end
end Lemmatheca.SetTheory.ForcingChainConditions
