import Lemmatheca.CardinalSaturationAndHomogeneity.PartialMaps
import Mathlib.Order.Zorn

namespace Lemmatheca.ModelTheory.PartialElementaryMaps
open FirstOrder FirstOrder.Language
universe u v w w'
variable {L : Language.{u,v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]
namespace Map

theorem exists_maximal_extension (p : Map L M N) :
    ∃ q : Map L M N, p ≤ q ∧ ∀ r : Map L M N, q ≤ r → r = q := by
  obtain ⟨q, hpq, hmax⟩ := zorn_le_nonempty_Ici₀ p
    (fun C _ hC c hc => ⟨chainUnion C hC ⟨c, hc⟩,
      fun r hr => (chain_union_spec C hC ⟨c, hc⟩).2.2 r hr⟩) p le_rfl
  exact ⟨q, hpq, fun r hqr => le_antisymm (hmax hqr) hqr⟩

end Map
end Lemmatheca.ModelTheory.PartialElementaryMaps
