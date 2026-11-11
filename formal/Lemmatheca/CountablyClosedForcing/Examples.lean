import Lemmatheca.CountablyClosedForcing.Names

namespace Lemmatheca.SetTheory.CountablyClosedForcing
open Set Order Ordinal Cardinal
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.InfiniteTrees
noncomputable section
attribute [local instance] prefixOrder prefixOrderTop

theorem listed_old_cardinal_bound (G : PFilter Prefix) (S : Set (ℕ → Bool))
    (κ : Cardinal) (e : κ.ord.ToType ≃ S)
    (hc : S ⊆ Set.range (blockReal G)) : κ ≤ ℵ₁ := by
  have he := Cardinal.lift_mk_le_lift_mk_of_injective e.injective
  simpa using he.trans (Cardinal.lift_le.mpr (listing_cardinal_bound G S hc))

def zeroPrefixSequence (θ : Ordinal) (a : ℕ → θ.ToType) :
    ℕ → FunctionNode θ Bool := fun n => ⟨a n,fun _ => false⟩

theorem zero_prefix_sequence_monotone (θ : Ordinal) (a : ℕ → θ.ToType)
    (ha : Monotone a) : Monotone (zeroPrefixSequence θ a) := by
  intro m n hmn
  exact ⟨ha hmn,by funext i; rfl⟩

theorem zero_prefix_no_lower_bound (θ : Ordinal) (a : ℕ → θ.ToType)
    (ha : ∀ i, ∃ n, i < a n) :
    ¬∃ q : FunctionNode θ Bool, ∀ n, Extends (zeroPrefixSequence θ a n) q := by
  rintro ⟨q,hq⟩
  obtain ⟨n,hn⟩ := ha q.1
  exact (not_le_of_gt hn) (hq n).1

end
end Lemmatheca.SetTheory.CountablyClosedForcing
