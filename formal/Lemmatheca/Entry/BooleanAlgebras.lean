import Lemmatheca.SetTheory.BooleanAlgebras
import Lemmatheca.SetTheory.FiniteErrors

namespace Lemmatheca.Entry.BooleanAlgebras

open Set Order Lemmatheca.SetTheory.BooleanAlgebras

theorem finiteCofinite_omits_even : {n : ℕ | n % 2 = 0} ∉ finiteCofinite := by
  rintro (h | h)
  · exact Lemmatheca.SetTheory.FiniteErrors.parity_partition.1 h
  · apply Lemmatheca.SetTheory.FiniteErrors.parity_partition.2.1
    apply h.subset
    intro n hn
    simp only [mem_compl_iff, mem_ofPred_eq] at *
    omega

theorem two_element_powerSet : Nonempty (Bool ≃o Set Unit) := by
  classical
  let f : Bool ↪o Set Unit :=
    { toFun := fun b => {x | b = true}
      inj' := by
        intro a b h
        have hm : a = true ↔ b = true := Set.ext_iff.mp h ()
        cases a <;> cases b <;> simp_all
      map_rel_iff' := by
        intro a b
        change (∀ x : Unit, a = true → b = true) ↔ a ≤ b
        cases a <;> cases b <;> simp }
  apply Nonempty.intro
  refine OrderIso.ofSurjective f ?_
  intro S
  refine ⟨decide (() ∈ S), ?_⟩
  ext x
  cases x
  change decide (() ∈ S) = true ↔ () ∈ S
  simp

theorem carrier_complement_not_ideal :
    ¬ Order.IsIdeal ((PFilter.principal (univ : Set Bool) : Set (Set Bool))ᶜ) := by
  intro h
  have hf : ({false} : Set Bool) ∈ ((PFilter.principal (univ : Set Bool) : Set (Set Bool))ᶜ) := by
    simp [PFilter.mem_principal]
  have ht : ({true} : Set Bool) ∈ ((PFilter.principal (univ : Set Bool) : Set (Set Bool))ᶜ) := by
    simp [PFilter.mem_principal]
  obtain ⟨S, hS, hfS, htS⟩ := h.Directed _ hf _ ht
  have he : S = univ := by
    ext b
    cases b
    · simp_all
    · simp_all
  simp [he, PFilter.mem_principal] at hS

end Lemmatheca.Entry.BooleanAlgebras
