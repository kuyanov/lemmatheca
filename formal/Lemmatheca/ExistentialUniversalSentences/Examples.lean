import Lemmatheca.ExistentialUniversalSentences.Decision
import Mathlib.Order.Preorder.Finite

namespace Lemmatheca.Entry.ExistentialUniversalSentences

/-- The witness/constant list can require every one of its entries to be different. -/
theorem distinct_values_bound {M : Type*} [Fintype M] {k : ℕ} (a : Fin k → M)
    (h : Function.Injective a) : k ≤ Fintype.card M := by
  simpa using Fintype.card_le_of_injective a h

theorem distinct_values_exist (k : ℕ) :
    ∃ a : Fin k → Fin k, Function.Injective a := ⟨id, Function.injective_id⟩

theorem existential_restriction_counterexample :
    (∀ x : Bool, ∃ z : Bool, z ≠ x) ∧
      (∀ x z : Unit, ¬ z ≠ x) := by
  constructor
  · intro x
    cases x
    · exact ⟨true, by decide⟩
    · exact ⟨false, by decide⟩
  · intro x z
    simp [Subsingleton.elim z x]

theorem two_point_example :
    ∃ (P : Bool → Prop) (x z : Bool),
      P x ∧ ¬P z ∧ ∀ y : Bool, y = x ∨ y = z := by
  refine ⟨fun b => b = true, true, false, rfl, by decide, ?_⟩
  intro y
  cases y <;> simp

theorem singleton_example_impossible {M : Type*} [Subsingleton M] (P : M → Prop) :
    ¬ ∃ x z, P x ∧ ¬P z := by
  rintro ⟨x,z,hx,hz⟩
  exact hz (Subsingleton.elim x z ▸ hx)

theorem conjunctive_example_impossible {M : Type*} [Nonempty M] (P : M → Prop) :
    ¬ ∃ x z, P x ∧ ¬P z ∧ ∀ y, y = x ∧ y = z := by
  rintro ⟨x,z,hx,hz,hall⟩
  exact hz ((hall x).2 ▸ hx)

theorem successor_model :
    Function.Injective Nat.succ ∧ ∀ n, Nat.succ n ≠ 0 :=
  ⟨Nat.succ_injective, Nat.succ_ne_zero⟩

theorem no_finite_omitting_injection {M : Type*} [Finite M] (a : M) (f : M → M)
    (hi : Function.Injective f) : ¬ ∀ x, f x ≠ a := by
  intro h
  obtain ⟨x,hx⟩ := Finite.surjective_of_injective hi a
  exact h x hx

theorem natural_strict_order_model :
    (∀ x : ℕ, ¬ x < x) ∧
      (∀ {x y z : ℕ}, x < y → y < z → x < z) ∧ ∀ x : ℕ, ∃ y, x < y :=
  ⟨Nat.lt_irrefl, Nat.lt_trans, fun x => ⟨x+1, Nat.lt_succ_self x⟩⟩

theorem no_finite_strict_successors {M : Type*} [Finite M] [Nonempty M]
    (r : M → M → Prop) (hi : ∀ x, ¬ r x x) (ht : ∀ {x y z}, r x y → r y z → r x z) :
    ¬ ∀ x, ∃ y, r x y := by
  classical
  let : Preorder M := {
    le x y := x = y ∨ r x y
    le_refl x := Or.inl rfl
    le_trans x y z hxy hyz := by
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr (ht hxy hyz) }
  intro hs
  obtain ⟨a,ha⟩ := (Set.toFinite (Set.univ : Set M)).exists_maximal (Set.univ_nonempty)
  obtain ⟨b,hab⟩ := hs a
  have hba : b ≤ a := ha.2 (Set.mem_univ b) (Or.inr hab)
  rcases hba with hba | hba
  · subst b
    exact hi a hab
  · exact hi a (ht hab hba)

end Lemmatheca.Entry.ExistentialUniversalSentences
