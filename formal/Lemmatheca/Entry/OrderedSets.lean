import Lemmatheca.SetTheory.OrderedSets
import Lemmatheca.Entry.EquivalenceRelations
import Mathlib.Data.PNat.Prime
import Mathlib.Data.Sum.Order
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Antichain

/-!
# Ordered-sets entry: examples and counterexamples

Distinct type synonyms keep the divisibility order, the four-point order, and the
first-coordinate preorder separate from the usual orders. `FourPoint` uses the
labels a = 0, b = 1, u = 2, v = 3.
`Fin 2` represents {0, 1}, and `ℤ ⊕ Unit` adjoins an isolated star to the integers.
Definition bodies specify the examples; all new theorem proofs remain `sorry`.
-/

namespace Lemmatheca.Entry.OrderedSets

section Divisibility

/-- A copy of the positive integers reserved for the divisibility order. -/
def DvdPNat := ℕ+

instance (n : ℕ) [NeZero n] : OfNat DvdPNat n := inferInstanceAs (OfNat ℕ+ n)
instance : Dvd DvdPNat := inferInstanceAs (Dvd ℕ+)

/-- Positive integers ordered by divisibility, not by their numerical size. -/
instance pnatDivisibility : PartialOrder DvdPNat where
  le := (· ∣ ·)
  lt a b := a ∣ b ∧ ¬ b ∣ a
  le_refl a := @dvd_refl ℕ+ _ a
  le_trans a b c := @dvd_trans ℕ+ _ a b c
  le_antisymm _ _ := PNat.dvd_antisymm


/-- The ambient finite poset in the diagram. -/
abbrev Divisor12 := {n : DvdPNat // n ∣ 12}

/-- Labels used by the figure and the examples. -/
def divisor (n : DvdPNat) (h : n ∣ 12 := by apply PNat.dvd_iff.mpr; decide) :
    Divisor12 := ⟨n, h⟩

theorem divisibility_incomparable : ¬ (2 : DvdPNat) ≤ 3 ∧ ¬ (3 : DvdPNat) ≤ 2 := by
  sorry

theorem divisors_twelve :
    {n : DvdPNat | n ∣ 12} = {1, 2, 3, 4, 6, 12} := by
  sorry

theorem divisor_comparisons :
    divisor 3 ≤ divisor 6 ∧ ¬ divisor 3 ≤ divisor 4 ∧ ¬ divisor 4 ≤ divisor 3 := by
  sorry

theorem divisor_chain_antichain :
    IsChain (· ≤ ·) ({divisor 1, divisor 2, divisor 4, divisor 12} : Set Divisor12) ∧
    IsAntichain (· ≤ ·) ({divisor 4, divisor 6} : Set Divisor12) := by
  sorry

theorem divisor_covers (a b : Divisor12) :
    a ⋖ b ↔ (a, b) ∈ ({(divisor 1, divisor 2), (divisor 1, divisor 3),
      (divisor 2, divisor 4), (divisor 2, divisor 6), (divisor 3, divisor 6),
      (divisor 4, divisor 12), (divisor 6, divisor 12)} : Set (Divisor12 × Divisor12)) := by
  sorry

theorem divisor_pair_extrema :
    (∀ x ∈ ({divisor 4, divisor 6} : Set Divisor12),
      Minimal (· ∈ ({divisor 4, divisor 6} : Set Divisor12)) x ∧
      Maximal (· ∈ ({divisor 4, divisor 6} : Set Divisor12)) x) ∧
    (¬ ∃ x, IsLeast ({divisor 4, divisor 6} : Set Divisor12) x) ∧
    (¬ ∃ x, IsGreatest ({divisor 4, divisor 6} : Set Divisor12) x) := by
  sorry

theorem divisor_bottom_top :
    IsBot (divisor 1) ∧ IsTop (divisor 12) := by
  sorry

theorem divisor_pair_bounds :
    upperBounds ({divisor 4, divisor 6} : Set Divisor12) = {divisor 12} ∧
    lowerBounds ({divisor 4, divisor 6} : Set Divisor12) = {divisor 1, divisor 2} ∧
    Disjoint ({divisor 4, divisor 6} : Set Divisor12)
      {divisor 1, divisor 2, divisor 12} := by
  sorry

theorem divisor_pair_lub_glb :
    IsLUB ({divisor 4, divisor 6} : Set Divisor12) (divisor 12) ∧
    IsGLB ({divisor 4, divisor 6} : Set Divisor12) (divisor 2) := by
  sorry

/-- Remove 12 from the ambient poset, retaining the inherited order. -/
abbrev ProperDivisor12 := {n : Divisor12 // n ≠ divisor 12}

theorem proper_divisors_no_upper_bound :
    ¬ BddAbove {n : ProperDivisor12 | n.val = divisor 4 ∨ n.val = divisor 6} := by
  sorry

end Divisibility

theorem isolated_star_minimal_not_least :
    (∀ x : ℤ ⊕ Unit, Minimal (· ∈ (Set.univ : Set (ℤ ⊕ Unit))) x ↔
      x = Sum.inr ()) ∧
    (∀ n : ℤ, (Sum.inl (n - 1) : ℤ ⊕ Unit) < Sum.inl n) ∧
    ¬ (Sum.inr () : ℤ ⊕ Unit) ≤ Sum.inl 0 ∧
    (¬ ∃ x, IsLeast (Set.univ : Set (ℤ ⊕ Unit)) x) := by
  sorry

theorem open_unit_interval_upper_witness (v : ℝ) (hv : v < 1) :
    (max v 0 + 1) / 2 ∈ Set.Ioo (0 : ℝ) 1 ∧ v < (max v 0 + 1) / 2 := by
  sorry

theorem open_unit_interval_lower_witness (v : ℝ) (hv : 0 < v) :
    min v 1 / 2 ∈ Set.Ioo (0 : ℝ) 1 ∧ min v 1 / 2 < v := by
  sorry

section FourPoints

/-- A copy of four labels with no inherited numerical order. -/
def FourPoint := Fin 4

instance (n : ℕ) : OfNat FourPoint n := inferInstanceAs (OfNat (Fin 4) n)

/-- Labels 0,1 are below both 2,3; there are no other strict comparisons. -/
instance fourPointOrder : PartialOrder (FourPoint) where
  le a b := a = b ∨ a.val < 2 ∧ 2 ≤ b.val
  lt a b := (a = b ∨ a.val < 2 ∧ 2 ≤ b.val) ∧ ¬ (b = a ∨ b.val < 2 ∧ 2 ≤ a.val)
  le_refl := by sorry
  le_trans := by sorry
  le_antisymm := by sorry


theorem four_point_bounds :
    upperBounds ({0, 1} : Set (FourPoint)) = {2, 3} ∧
    lowerBounds ({2, 3} : Set (FourPoint)) = {0, 1} ∧
    IsAntichain (· ≤ ·) ({2, 3} : Set (FourPoint)) ∧
    IsAntichain (· ≤ ·) ({0, 1} : Set (FourPoint)) ∧
    (∀ x ∈ ({2, 3} : Set (FourPoint)), Minimal (· ∈ upperBounds ({0, 1} : Set (FourPoint))) x) ∧
    (¬ ∃ x, IsLUB ({0, 1} : Set (FourPoint)) x) ∧
    (¬ ∃ x, IsGLB ({2, 3} : Set (FourPoint)) x) := by
  sorry

end FourPoints

theorem equality_to_linear_monotone_bijection :
    Function.Bijective (id : Fin 2 → Fin 2) ∧
    (∀ a b : Fin 2, a = b → id a ≤ id b) ∧
    (id (0 : Fin 2) ≤ id 1 ∧ (0 : Fin 2) ≠ 1) ∧
    ¬ (∀ a b : Fin 2, a ≤ b → id a = id b) := by
  sorry

/-- The entry's monotone map which does not preserve a binary supremum. -/
noncomputable def fullSetIndicator (s : Set (Fin 2)) : Fin 2 := by
  classical
  exact if s = Set.univ then 1 else 0

theorem full_set_indicator_monotone : Monotone fullSetIndicator := by
  sorry

theorem full_set_indicator_not_preserve_sup :
    IsLUB ({{0}, {1}} : Set (Set (Fin 2))) Set.univ ∧
    fullSetIndicator Set.univ = 1 ∧
    fullSetIndicator '' ({{0}, {1}} : Set (Set (Fin 2))) = {0} ∧
    IsLUB (fullSetIndicator '' ({{0}, {1}} : Set (Set (Fin 2)))) 0 ∧
    ¬ IsLUB (fullSetIndicator '' ({{0}, {1}} : Set (Set (Fin 2))))
      (fullSetIndicator Set.univ) := by
  sorry

section Plane

/-- A copy of the real plane reserved for the first-coordinate preorder. -/
def PreorderedPlane := ℝ × ℝ

/-- Only the first coordinate is compared. -/
instance planePreorder : Preorder (PreorderedPlane) := Preorder.lift (fun p : PreorderedPlane => (p : ℝ × ℝ).1)


theorem plane_not_antisymmetric :
    ((0, 0) : PreorderedPlane) ≤ (0, 1) ∧ ((0, 1) : PreorderedPlane) ≤ (0, 0) ∧
    ((0, 0) : PreorderedPlane) ≠ (0, 1) := by
  sorry

theorem plane_classes (p : PreorderedPlane) :
    {q | AntisymmRel (· ≤ ·) q p} = Set.prod {p.1} Set.univ := by
  sorry

theorem plane_quotient_order_iso :
    ∃ e : Antisymmetrization PreorderedPlane (· ≤ ·) ≃o ℝ,
      (∀ p : PreorderedPlane, e (toAntisymmetrization (· ≤ ·) p) = p.1) ∧
      (∀ x : ℝ, e.symm x =
        toAntisymmetrization (α := PreorderedPlane) (· ≤ ·) (x, 0)) := by
  sorry

theorem plane_identity_not_factor :
    ¬ ∃ g : Antisymmetrization PreorderedPlane (· ≤ ·) → PreorderedPlane,
      ∀ p, g (toAntisymmetrization (· ≤ ·) p) = p := by
  sorry

end Plane

open Lemmatheca.Entry.EquivalenceRelations in
theorem parity_comparison_not_well_defined :
    paritySetoid 0 2 ∧ (0 : ℤ) ≤ 1 ∧ ¬ (2 : ℤ) ≤ 1 := by
  sorry

/-- Compare parity classes by the existence of comparable representatives. -/
def parityRepresentativeLE (a b : Quotient Lemmatheca.Entry.EquivalenceRelations.paritySetoid) :
    Prop := ∃ x y : ℤ, Quotient.mk _ x = a ∧ Quotient.mk _ y = b ∧ x ≤ y

theorem parity_representative_order_not_antisymmetric :
    let q := Quotient.mk Lemmatheca.Entry.EquivalenceRelations.paritySetoid
    q 0 ≠ q 1 ∧ q 2 = q 0 ∧ (0 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ 2 ∧
      parityRepresentativeLE (q 0) (q 1) ∧
      parityRepresentativeLE (q 1) (q 0) ∧
      ¬ Std.Antisymm parityRepresentativeLE := by
  sorry

end Lemmatheca.Entry.OrderedSets
