import Lemmatheca.DenseForcingPresentations.Orders

namespace Lemmatheca.SetTheory.DenseForcingPresentations
open Set Order
open Lemmatheca.SetTheory.ForcingAndGenericFilters
noncomputable section
local instance denseCounterPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable

inductive DiscreteTwo | a | b deriving DecidableEq

instance discreteTwoOrder : PartialOrder DiscreteTwo where
  le := Eq
  le_refl := Eq.refl
  le_trans := fun _ _ _ => Eq.trans
  le_antisymm := fun _ _ h _ => h

def discreteToChain : DiscreteTwo → Bool
  | .a => false
  | .b => true

def discreteGeneric : PFilter DiscreteTwo := PFilter.principal .b

def chainGeneric : PFilter Bool := PFilter.principal false

def falseLift : Set Bool := {p | ∃ q ∈ discreteGeneric, discreteToChain q ≤ p}

theorem discrete_dense_iff (A : Set DiscreteTwo) : Dense A ↔ A = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨r,hr,hrq⟩ := h q
    change r = q at hrq
    exact hrq ▸ hr
  · rintro rfl q
    exact ⟨q,Set.mem_univ q,le_rfl⟩

theorem discrete_map_facts : Function.Injective discreteToChain ∧ Monotone discreteToChain ∧
    ForcingAndGenericFilters.Dense (Set.range discreteToChain) ∧
      discreteToChain .a ≤ discreteToChain .b ∧ ¬ DiscreteTwo.a ≤ DiscreteTwo.b := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x y he
    cases x <;> cases y <;> simp_all [discreteToChain]
  · intro x y hxy
    change x = y at hxy
    subst y
    exact le_rfl
  · intro p
    exact ⟨false,⟨.a,rfl⟩,by cases p <;> decide⟩
  · decide
  · change DiscreteTwo.a ≠ DiscreteTwo.b
    exact DiscreteTwo.noConfusion

theorem discrete_singleton_generic : GenericFor discreteGeneric Set.univ := by
  intro A _ hA
  have he := (discrete_dense_iff A).mp hA
  exact ⟨.b,by change DiscreteTwo.b = DiscreteTwo.b; rfl,he.symm ▸ Set.mem_univ _⟩

theorem false_lift_not_generic : falseLift = {true} ∧
    ¬ GenericFor (PFilter.principal true : PFilter Bool) Set.univ := by
  constructor
  · ext p
    constructor
    · rintro ⟨q,hq,hqp⟩
      change DiscreteTwo.b = q at hq
      subst q
      cases p
      · exact False.elim ((by decide : ¬(true ≤ false)) hqp)
      · exact Set.mem_singleton _
    · intro hp
      have he : p = true := Set.mem_singleton_iff.mp hp
      subst p
      exact ⟨.b,by change DiscreteTwo.b = DiscreteTwo.b; rfl,le_rfl⟩
  · intro hg
    have hd : ForcingAndGenericFilters.Dense ({false} : Set Bool) := by
      intro p
      exact ⟨false,Set.mem_singleton _,by cases p <;> decide⟩
    obtain ⟨p,hp,hpf⟩ := hg _ (Set.mem_univ _) hd
    have he : p = false := Set.mem_singleton_iff.mp hpf
    subst p
    exact (by decide : ¬(true ≤ false)) hp

theorem chain_generic_and_bad_trace : GenericFor chainGeneric Set.univ ∧
    ¬ IsPFilter {q : DiscreteTwo | discreteToChain q ∈ chainGeneric} := by
  constructor
  · intro A _ hA
    obtain ⟨p,hp,hpfalse⟩ := hA false
    have he : p = false := by
      cases p
      · rfl
      · exact False.elim ((by decide : ¬(true ≤ false)) hpfalse)
    subst p
    exact ⟨false,by change false ≤ false; exact le_rfl,hp⟩
  · intro hfilter
    have hmem (q : DiscreteTwo) : discreteToChain q ∈ chainGeneric := by
      change false ≤ discreteToChain q
      cases q <;> decide
    let F := hfilter.toPFilter
    obtain ⟨r,_,hra,hrb⟩ := F.directed .a (hmem .a) .b (hmem .b)
    change r = DiscreteTwo.a at hra
    change r = DiscreteTwo.b at hrb
    exact DiscreteTwo.noConfusion (hra.symm.trans hrb)

end
end Lemmatheca.SetTheory.DenseForcingPresentations
