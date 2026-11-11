import Lemmatheca.AntiDiagonalNormalization.Selector

namespace Lemmatheca.ComputabilityTheory.AntiDiagonalNormalization

open UniversalComputation EffectiveEnumerations
noncomputable section

def universalRequest (w : ℕ) : Part ℕ := phi w.unpair.1 w.unpair.2

theorem universal_request_partial : Nat.Partrec universalRequest := by
  exact Partrec₂.unpaired'.mpr phi_recursive

def universalRequestIndex : ℕ := Classical.choose (phi_complete universal_request_partial)

theorem universal_request_eval (e n : ℕ) :
    phi universalRequestIndex (Nat.pair e n) = phi e n := by
  simpa only [universalRequestIndex, universalRequest, Nat.unpair_pair] using
    congrFun (Classical.choose_spec (phi_complete universal_request_partial)) (Nat.pair e n)

def uniformSelector (d e n : ℕ) : ℕ := selector d universalRequestIndex (Nat.pair e n)

theorem uniform_selector_primitive (d : ℕ) : Primrec₂ (uniformSelector d) := by
  exact (selector_primitive d universalRequestIndex).comp Primrec₂.natPair

theorem uniform_adn (d : ℕ) (hd : PartialFPF (phi d)) :
    Primrec₂ (uniformSelector d) ∧
      (∀ e n j, j ∈ phi e n → indexSet (uniformSelector d e n) = indexSet j) ∧
      (∀ e n, ¬ (phi e n).Dom → ¬ (phi d (uniformSelector d e n)).Dom) := by
  refine ⟨uniform_selector_primitive d, ?_, ?_⟩
  · intro e n j hj
    apply selector_domains d universalRequestIndex (Nat.pair e n) j hd
    rwa [universal_request_eval]
  · intro e n hn
    apply selector_avoids d universalRequestIndex (Nat.pair e n) hd
    rwa [universal_request_eval]

theorem uniform_adn_exists {δ : ℕ → Part ℕ} (hδ : Nat.Partrec δ)
    (hd : PartialFPF δ) :
    ∃ H : ℕ → ℕ → ℕ, Primrec₂ H ∧
      (∀ e n j, j ∈ phi e n → indexSet (H e n) = indexSet j) ∧
      (∀ e n, ¬ (phi e n).Dom → ¬ (δ (H e n)).Dom) := by
  obtain ⟨d, hdδ⟩ := phi_complete hδ
  subst δ
  exact ⟨uniformSelector d, uniform_adn d hd⟩

end
end Lemmatheca.ComputabilityTheory.AntiDiagonalNormalization
