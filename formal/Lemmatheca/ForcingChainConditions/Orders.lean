import Lemmatheca.ForcingAndGenericFilters.Orders
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace Lemmatheca.SetTheory.ForcingChainConditions
open Set Order
universe u v
noncomputable section
attribute [local instance] Classical.propDecidable
variable {P : Type u} [PartialOrder P]
open Lemmatheca.SetTheory.ForcingAndGenericFilters

def CCC (P : Type u) [PartialOrder P] : Prop :=
  ∀ A : Set P, Antichain A → A.Countable

def PredenseBelow (A : Set P) (p : P) : Prop :=
  ∀ q, q ≤ p → ∃ a ∈ A, Compatible q a

theorem countable_ccc [Countable P] : CCC P := by
  intro A _
  exact Set.to_countable A

theorem exists_countable_antichain_below (hccc : CCC P) {D : Set P} {p : P}
    (hD : DenseBelow D p) :
    ∃ A : Set P, A ⊆ D ∧ A ⊆ Set.Iic p ∧ Antichain A ∧
      PredenseBelow A p ∧ A.Countable := by
  classical
  have hcone : DenseBelow (D ∩ Set.Iic p) p := by
    intro q hqp
    obtain ⟨r, hr, hrq⟩ := hD q hqp
    exact ⟨r, ⟨hr, hrq.trans hqp⟩, hrq⟩
  obtain ⟨B, hBE, hB⟩ := exists_maximal_antichain_in_dense (dense_below_union hcone)
  let A := B ∩ Set.Iic p
  have hant : Antichain A := fun _ hx _ hy hxy => hB.1 hx.1 hy.1 hxy
  refine ⟨A, ?_, Set.inter_subset_right, hant, ?_, hccc A hant⟩
  · intro a ha
    rcases hBE ha.1 with hgood | hbad
    · exact hgood.1
    · exact False.elim (hbad ⟨a, le_rfl, ha.2⟩)
  · intro q hqp
    obtain ⟨a, ha, hqa⟩ := ((maximal_antichain_iff B).mp hB).2 q
    have hap : a ≤ p := by
      rcases hBE ha with hgood | hbad
      · exact hgood.2
      · obtain ⟨r, hrq, hra⟩ := hqa
        exact False.elim (hbad ⟨r, hra, hrq.trans hqp⟩)
    exact ⟨a, ⟨ha, hap⟩, hqa⟩

theorem predense_downward_dense_below {A : Set P} {p : P}
    (hA : PredenseBelow A p) : DenseBelow (downwardClosure A) p := by
  intro q hqp
  obtain ⟨a, ha, r, hrq, hra⟩ := hA q hqp
  exact ⟨r, ⟨a, ha, hra⟩, hrq⟩

theorem generic_meets_predense (G : PFilter P) (S : Set (Set P))
    (hG : GenericFor G S) {A : Set P} {p : P} (hp : p ∈ G)
    (hA : PredenseBelow A p)
    (hE : downwardClosure A ∪ {q | ¬Compatible q p} ∈ S) :
    Meets G A := by
  obtain ⟨q, hqG, a, haA, hqa⟩ :=
    generic_dense_below G S hG hp (predense_downward_dense_below hA) hE
  exact ⟨a, PFilter.mem_of_le hqa hqG, haA⟩

theorem antichain_filter_subsingleton (G : PFilter P) {A : Set P}
    (hA : Antichain A) : ((G : Set P) ∩ A).Subsingleton := by
  intro p hp q hq
  by_contra hne
  exact hA hp.2 hq.2 hne (filter_compatible G hp.1 hq.1)

end
end Lemmatheca.SetTheory.ForcingChainConditions
