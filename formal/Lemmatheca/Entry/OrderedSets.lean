import Lemmatheca.SetTheory.OrderedSets
import Lemmatheca.SetTheory.PositiveDivisibility
import Lemmatheca.Entry.EquivalenceRelations
import Mathlib.Tactic.IntervalCases

/-!
# Ordered-sets entry: examples and counterexamples

Distinct type synonyms keep the divisibility order, the four-point order, and the
first-coordinate preorder separate from the usual orders. `FourPoint` uses the
labels a = 0, b = 1, u = 2, v = 3.
`Fin 2` represents {0, 1}, and `ℤ ⊕ Unit` adjoins an isolated star to the integers.
-/

namespace Lemmatheca.Entry.OrderedSets

open Lemmatheca.SetTheory.PositiveDivisibility

section Divisibility

/-- The ambient finite poset in the diagram. -/
abbrev Divisor12 := {n : DvdPNat // n ∣ 12}

/-- Labels used by the figure and the examples. -/
def divisor (n : DvdPNat) (h : n ∣ 12 := by apply PNat.dvd_iff.mpr; decide) :
    Divisor12 := ⟨n, h⟩

private theorem divisor_le_iff (a b : Divisor12) :
    a ≤ b ↔ (a.val : ℕ+).val ∣ (b.val : ℕ+).val :=
  PNat.dvd_iff

private theorem divisor_eq_iff (a b : Divisor12) :
    a = b ↔ (a.val : ℕ+).val = (b.val : ℕ+).val :=
  (Subtype.val_inj.trans Subtype.val_inj).symm

theorem divisibility_incomparable : ¬ (2 : DvdPNat) ≤ 3 ∧ ¬ (3 : DvdPNat) ≤ 2 := by
  simp only [dvdPNat_le_iff]
  decide

theorem divisors_twelve :
    {n : DvdPNat | n ∣ 12} = {1, 2, 3, 4, 6, 12} := by
  ext n
  change n ∣ 12 ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 12
  simp only [dvdPNat_dvd_iff, dvdPNat_eq_iff]
  rcases n with ⟨n, hn⟩
  change n ∣ 12 ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 12
  constructor
  · intro h
    have hle : n ≤ 12 := Nat.le_of_dvd (by decide) h
    interval_cases n <;> norm_num at *
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

private theorem divisor_cases (n : Divisor12) :
    n = divisor 1 ∨ n = divisor 2 ∨ n = divisor 3 ∨
      n = divisor 4 ∨ n = divisor 6 ∨ n = divisor 12 := by
  have hn : n.val ∈ ({1, 2, 3, 4, 6, 12} : Set DvdPNat) := by
    rw [← divisors_twelve]
    exact n.property
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, divisor, Subtype.ext_iff] using hn

private theorem forall_divisor12 {p : Divisor12 → Prop} :
    (∀ n, p n) ↔ p (divisor 1) ∧ p (divisor 2) ∧ p (divisor 3) ∧
      p (divisor 4) ∧ p (divisor 6) ∧ p (divisor 12) := by
  constructor
  · intro h
    exact ⟨h _, h _, h _, h _, h _, h _⟩
  · rintro ⟨h1, h2, h3, h4, h6, h12⟩ n
    rcases divisor_cases n with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem divisor_comparisons :
    divisor 3 ≤ divisor 6 ∧ ¬ divisor 3 ≤ divisor 4 ∧ ¬ divisor 4 ≤ divisor 3 := by
  simp only [divisor_le_iff]
  decide

theorem divisor_chain_antichain :
    IsChain (· ≤ ·) ({divisor 1, divisor 2, divisor 4, divisor 12} : Set Divisor12) ∧
    IsAntichain (· ≤ ·) ({divisor 4, divisor 6} : Set Divisor12) := by
  simp only [IsChain, IsAntichain, Set.Pairwise, forall_divisor12,
    Set.mem_insert_iff, Set.mem_singleton_iff, divisor_eq_iff, divisor_le_iff]
  set_option backward.isDefEq.respectTransparency false in
    norm_num [divisor, instOfNatDvdPNatOfNeZeroNat, Subtype.ext_iff]

theorem divisor_covers (a b : Divisor12) :
    a ⋖ b ↔ (a, b) ∈ ({(divisor 1, divisor 2), (divisor 1, divisor 3),
      (divisor 2, divisor 4), (divisor 2, divisor 6), (divisor 3, divisor 6),
      (divisor 4, divisor 12), (divisor 6, divisor 12)} : Set (Divisor12 × Divisor12)) := by
  revert a b
  simp only [CovBy, lt_iff_le_not_ge, forall_divisor12,
    Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, divisor_eq_iff, divisor_le_iff]
  set_option backward.isDefEq.respectTransparency false in
    norm_num [divisor, instOfNatDvdPNatOfNeZeroNat, Subtype.ext_iff]

theorem divisor_pair_extrema :
    (∀ x ∈ ({divisor 4, divisor 6} : Set Divisor12),
      Minimal (· ∈ ({divisor 4, divisor 6} : Set Divisor12)) x ∧
      Maximal (· ∈ ({divisor 4, divisor 6} : Set Divisor12)) x) ∧
    (¬ ∃ x, IsLeast ({divisor 4, divisor 6} : Set Divisor12) x) ∧
    (¬ ∃ x, IsGreatest ({divisor 4, divisor 6} : Set Divisor12) x) := by
  simp only [Minimal, Maximal, IsLeast, IsGreatest, lowerBounds, upperBounds,
    Set.mem_ofPred_eq, not_exists, forall_divisor12, Set.mem_insert_iff,
    Set.mem_singleton_iff, divisor_eq_iff, divisor_le_iff]
  set_option backward.isDefEq.respectTransparency false in
    norm_num [divisor, instOfNatDvdPNatOfNeZeroNat, Subtype.ext_iff]

theorem divisor_bottom_top :
    IsBot (divisor 1) ∧ IsTop (divisor 12) := by
  constructor
  · intro n
    exact (dvdPNat_le_iff _ _).mpr (by change 1 ∣ (n.val : ℕ+).val; exact one_dvd _)
  · intro n
    exact n.property

theorem divisor_pair_bounds :
    upperBounds ({divisor 4, divisor 6} : Set Divisor12) = {divisor 12} ∧
    lowerBounds ({divisor 4, divisor 6} : Set Divisor12) = {divisor 1, divisor 2} ∧
    Disjoint ({divisor 4, divisor 6} : Set Divisor12)
      {divisor 1, divisor 2, divisor 12} := by
  simp only [Set.ext_iff, upperBounds, lowerBounds, Set.disjoint_left,
    Set.mem_ofPred_eq, forall_divisor12, Set.mem_insert_iff,
    Set.mem_singleton_iff, divisor_eq_iff, divisor_le_iff]
  set_option backward.isDefEq.respectTransparency false in
    norm_num [divisor, instOfNatDvdPNatOfNeZeroNat, Subtype.ext_iff]

theorem divisor_pair_lub_glb :
    IsLUB ({divisor 4, divisor 6} : Set Divisor12) (divisor 12) ∧
    IsGLB ({divisor 4, divisor 6} : Set Divisor12) (divisor 2) := by
  change IsLeast (upperBounds _) _ ∧ IsGreatest (lowerBounds _) _
  rw [divisor_pair_bounds.1, divisor_pair_bounds.2.1]
  simp only [IsLeast, IsGreatest, upperBounds, lowerBounds,
    Set.mem_ofPred_eq, forall_divisor12, Set.mem_insert_iff,
    Set.mem_singleton_iff, divisor_eq_iff, divisor_le_iff]
  decide

/-- Remove 12 from the ambient poset, retaining the inherited order. -/
abbrev ProperDivisor12 := {n : Divisor12 // n ≠ divisor 12}

theorem proper_divisors_no_upper_bound :
    ¬ BddAbove {n : ProperDivisor12 | n.val = divisor 4 ∨ n.val = divisor 6} := by
  rintro ⟨u, hu⟩
  have h4 : divisor 4 ≠ divisor 12 := by rw [ne_eq, divisor_eq_iff]; decide
  have h6 : divisor 6 ≠ divisor 12 := by rw [ne_eq, divisor_eq_iff]; decide
  have hu4 : divisor 4 ≤ u.val := hu (a := ⟨divisor 4, h4⟩) (Or.inl rfl)
  have hu6 : divisor 6 ≤ u.val := hu (a := ⟨divisor 6, h6⟩) (Or.inr rfl)
  have hbound : u.val ∈ upperBounds ({divisor 4, divisor 6} : Set Divisor12) := by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hu4
    · rw [Set.mem_singleton_iff] at ha
      simpa [ha] using hu6
  rw [divisor_pair_bounds.1, Set.mem_singleton_iff] at hbound
  exact u.property hbound

end Divisibility

theorem isolated_star_minimal_not_least :
    (∀ x : ℤ ⊕ Unit, Minimal (· ∈ (Set.univ : Set (ℤ ⊕ Unit))) x ↔
      x = Sum.inr ()) ∧
    (∀ n : ℤ, (Sum.inl (n - 1) : ℤ ⊕ Unit) < Sum.inl n) ∧
    ¬ (Sum.inr () : ℤ ⊕ Unit) ≤ Sum.inl 0 ∧
    (¬ ∃ x, IsLeast (Set.univ : Set (ℤ ⊕ Unit)) x) := by
  have hminimal (x : ℤ ⊕ Unit) :
      Minimal (· ∈ (Set.univ : Set (ℤ ⊕ Unit))) x ↔ x = Sum.inr () := by
    rcases x with n | u
    · constructor
      · intro h
        have hle := h.2 (y := Sum.inl (n - 1)) (by trivial)
          (by simp)
        have : n ≤ n - 1 := Sum.inl_le_inl_iff.mp hle
        omega
      · intro h
        cases h
    · cases u
      refine ⟨fun _ => rfl, fun _ => ⟨by trivial, ?_⟩⟩
      rintro (n | u) _ h
      · exact (Sum.not_inl_le_inr h).elim
      · cases u
        exact le_rfl
  refine ⟨hminimal, ?_, Sum.not_inr_le_inl, ?_⟩
  · intro n
    simp
  · rintro ⟨x, hx⟩
    have heq := (hminimal x).mp hx.minimal
    subst x
    exact Sum.not_inr_le_inl (hx.2 (Set.mem_univ (Sum.inl 0)))

theorem open_unit_interval_upper_witness (v : ℝ) (hv : v < 1) :
    (max v 0 + 1) / 2 ∈ Set.Ioo (0 : ℝ) 1 ∧ v < (max v 0 + 1) / 2 := by
  have hlt : max v 0 < 1 := max_lt hv (by norm_num)
  have hnonneg : 0 ≤ max v 0 := le_max_right _ _
  have hvmax : v ≤ max v 0 := le_max_left _ _
  constructor
  · constructor <;> linarith
  · linarith

theorem open_unit_interval_lower_witness (v : ℝ) (hv : 0 < v) :
    min v 1 / 2 ∈ Set.Ioo (0 : ℝ) 1 ∧ min v 1 / 2 < v := by
  have hpos : 0 < min v 1 := lt_min hv (by norm_num)
  have hone : min v 1 ≤ 1 := min_le_right _ _
  have hvmin : min v 1 ≤ v := min_le_left _ _
  constructor
  · constructor <;> linarith
  · linarith

section FourPoints

/-- A copy of four labels with no inherited numerical order. -/
def FourPoint := Fin 4

instance (n : ℕ) : OfNat FourPoint n := inferInstanceAs (OfNat (Fin 4) n)

/-- Labels 0,1 are below both 2,3; there are no other strict comparisons. -/
instance fourPointOrder : PartialOrder (FourPoint) where
  le a b := a = b ∨ a.val < 2 ∧ 2 ≤ b.val
  lt a b := (a = b ∨ a.val < 2 ∧ 2 ≤ b.val) ∧ ¬ (b = a ∨ b.val < 2 ∧ 2 ≤ a.val)
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact False.elim (by omega)
  le_antisymm a b hab hba := by
    rcases hab with hab | hab
    · exact hab
    rcases hba with hba | hba
    · exact hba.symm
    · exact False.elim (by omega)


private theorem forall_fourPoint {p : FourPoint → Prop} :
    (∀ x, p x) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 := by
  constructor
  · intro h
    exact ⟨h _, h _, h _, h _⟩
  · rintro ⟨h0, h1, h2, h3⟩ x
    change Fin 4 at x
    fin_cases x <;> assumption

private theorem fourPoint_le_iff (a b : FourPoint) :
    a ≤ b ↔ a = b ∨ a.val < 2 ∧ 2 ≤ b.val := Iff.rfl

private theorem fourPoint_eq_iff (a b : FourPoint) : a = b ↔ a.val = b.val :=
  Fin.ext_iff

theorem four_point_bounds :
    upperBounds ({0, 1} : Set (FourPoint)) = {2, 3} ∧
    lowerBounds ({2, 3} : Set (FourPoint)) = {0, 1} ∧
    IsAntichain (· ≤ ·) ({2, 3} : Set (FourPoint)) ∧
    IsAntichain (· ≤ ·) ({0, 1} : Set (FourPoint)) ∧
    (∀ x ∈ ({2, 3} : Set (FourPoint)), Minimal (· ∈ upperBounds ({0, 1} : Set (FourPoint))) x) ∧
    (¬ ∃ x, IsLUB ({0, 1} : Set (FourPoint)) x) ∧
    (¬ ∃ x, IsGLB ({2, 3} : Set (FourPoint)) x) := by
  set_option backward.isDefEq.respectTransparency false in
    norm_num [Set.ext_iff, upperBounds, lowerBounds, IsAntichain, Set.Pairwise,
      Minimal, IsLUB, IsGLB, IsLeast, IsGreatest, not_exists, forall_fourPoint,
      fourPoint_le_iff, fourPoint_eq_iff, instOfNatFourPoint, FourPoint]

end FourPoints

theorem equality_to_linear_monotone_bijection :
    Function.Bijective (id : Fin 2 → Fin 2) ∧
    (∀ a b : Fin 2, a = b → id a ≤ id b) ∧
    (id (0 : Fin 2) ≤ id 1 ∧ (0 : Fin 2) ≠ 1) ∧
    ¬ (∀ a b : Fin 2, a ≤ b → id a = id b) := by
  refine ⟨Function.bijective_id, ?_, by decide, ?_⟩
  · intro a b hab
    exact le_of_eq hab
  · intro h
    have := h 0 1 (by decide)
    norm_num at this

/-- The entry's monotone map which does not preserve a binary supremum. -/
noncomputable def fullSetIndicator (s : Set (Fin 2)) : Fin 2 := by
  classical
  exact if s = Set.univ then 1 else 0

theorem full_set_indicator_monotone : Monotone fullSetIndicator := by
  classical
  intro s t hst
  by_cases hs : s = Set.univ
  · have ht : t = Set.univ := Set.eq_univ_of_univ_subset (hs ▸ hst)
    simp [fullSetIndicator, hs, ht]
  · simp only [fullSetIndicator, hs, ↓reduceIte]
    split <;> decide

theorem full_set_indicator_not_preserve_sup :
    IsLUB ({{0}, {1}} : Set (Set (Fin 2))) Set.univ ∧
    fullSetIndicator Set.univ = 1 ∧
    fullSetIndicator '' ({{0}, {1}} : Set (Set (Fin 2))) = {0} ∧
    IsLUB (fullSetIndicator '' ({{0}, {1}} : Set (Set (Fin 2)))) 0 ∧
    ¬ IsLUB (fullSetIndicator '' ({{0}, {1}} : Set (Set (Fin 2))))
      (fullSetIndicator Set.univ) := by
  classical
  have h0 : ({0} : Set (Fin 2)) ≠ Set.univ := by
    intro h
    have := Set.eq_univ_iff_forall.mp h 1
    norm_num at this
  have h1 : ({1} : Set (Fin 2)) ≠ Set.univ := by
    intro h
    have := Set.eq_univ_iff_forall.mp h 0
    norm_num at this
  have hunion : ({0} : Set (Fin 2)) ∪ {1} = Set.univ := by
    ext x
    fin_cases x <;> simp
  have hlub : IsLUB ({{0}, {1}} : Set (Set (Fin 2))) Set.univ := by
    simpa only [Set.sup_eq_union, hunion] using
      (isLUB_pair : IsLUB ({{0}, {1}} : Set (Set (Fin 2))) ({0} ⊔ {1}))
  have himage : fullSetIndicator '' ({{0}, {1}} : Set (Set (Fin 2))) = {0} := by
    simp [fullSetIndicator, h0, h1]
  have hzero : IsLUB (fullSetIndicator '' ({{0}, {1}} : Set (Set (Fin 2)))) 0 := by
    rw [himage]
    exact isLUB_singleton
  refine ⟨hlub, by simp [fullSetIndicator], himage, hzero, ?_⟩
  intro h
  have heq := h.unique hzero
  norm_num [fullSetIndicator] at heq

section Plane

/-- A copy of the real plane reserved for the first-coordinate preorder. -/
def PreorderedPlane := ℝ × ℝ

/-- Only the first coordinate is compared. -/
instance planePreorder : Preorder (PreorderedPlane) := Preorder.lift (fun p : PreorderedPlane => (p : ℝ × ℝ).1)


-- Fix the relation's domain before pair literals can infer the usual product order.

theorem plane_not_antisymmetric :
    ((· ≤ ·) : PreorderedPlane → PreorderedPlane → Prop) (0, 0) (0, 1) ∧
    ((· ≤ ·) : PreorderedPlane → PreorderedPlane → Prop) (0, 1) (0, 0) ∧
    ((0, 0) : PreorderedPlane) ≠ (0, 1) := by
  refine ⟨show (0 : ℝ) ≤ 0 from le_rfl, show (0 : ℝ) ≤ 0 from le_rfl, ?_⟩
  intro h
  have := congrArg (fun p : PreorderedPlane => p.2) h
  norm_num at this

theorem plane_classes (p : PreorderedPlane) :
    {q | AntisymmRel (· ≤ ·) q p} = Set.prod {p.1} Set.univ := by
  ext q
  change (q.1 ≤ p.1 ∧ p.1 ≤ q.1) ↔ q.1 = p.1 ∧ True
  constructor
  · intro h
    exact ⟨le_antisymm h.1 h.2, trivial⟩
  · rintro ⟨h, _⟩
    exact ⟨le_of_eq h, le_of_eq h.symm⟩

theorem plane_quotient_order_iso :
    ∃ e : Antisymmetrization PreorderedPlane (· ≤ ·) ≃o ℝ,
      (∀ p : PreorderedPlane, e (toAntisymmetrization (· ≤ ·) p) = p.1) ∧
      (∀ x : ℝ, e.symm x =
        toAntisymmetrization (α := PreorderedPlane) (· ≤ ·) (x, 0)) := by
  let e : Antisymmetrization PreorderedPlane (· ≤ ·) ≃o ℝ :=
    { toFun := Quotient.lift (fun p : PreorderedPlane => p.1)
        (fun _ _ h => le_antisymm h.1 h.2)
      invFun := fun x => toAntisymmetrization (α := PreorderedPlane) (· ≤ ·) (x, 0)
      left_inv := fun q => Quotient.inductionOn q
        (fun p => Quotient.sound ⟨show p.1 ≤ p.1 from le_rfl, show p.1 ≤ p.1 from le_rfl⟩)
      right_inv := fun _ => rfl
      map_rel_iff' := by rintro ⟨p⟩ ⟨q⟩; rfl }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

theorem plane_identity_not_factor :
    ¬ ∃ g : Antisymmetrization PreorderedPlane (· ≤ ·) → PreorderedPlane,
      ∀ p, g (toAntisymmetrization (· ≤ ·) p) = p := by
  rintro ⟨g, hg⟩
  have heq : toAntisymmetrization (α := PreorderedPlane) (· ≤ ·) (0, 0) =
      toAntisymmetrization (α := PreorderedPlane) (· ≤ ·) (0, 1) :=
    Quotient.sound ⟨show (0 : ℝ) ≤ 0 from le_rfl, show (0 : ℝ) ≤ 0 from le_rfl⟩
  have h := congrArg g heq
  exact plane_not_antisymmetric.2.2 ((hg (0, 0)).symm.trans (h.trans (hg (0, 1))))

end Plane

open Lemmatheca.Entry.EquivalenceRelations in

theorem parity_comparison_not_well_defined :
    paritySetoid 0 2 ∧ (0 : ℤ) ≤ 1 ∧ ¬ (2 : ℤ) ≤ 1 := by
  change (0 : ℤ) % 2 = 2 % 2 ∧ (0 : ℤ) ≤ 1 ∧ ¬ (2 : ℤ) ≤ 1
  norm_num

/-- Compare parity classes by the existence of comparable representatives. -/
def parityRepresentativeLE (a b : Quotient Lemmatheca.Entry.EquivalenceRelations.paritySetoid) :
    Prop := ∃ x y : ℤ, Quotient.mk _ x = a ∧ Quotient.mk _ y = b ∧ x ≤ y

theorem parity_representative_order_not_antisymmetric :
    let q := Quotient.mk Lemmatheca.Entry.EquivalenceRelations.paritySetoid
    q 0 ≠ q 1 ∧ q 2 = q 0 ∧ (0 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ 2 ∧
      parityRepresentativeLE (q 0) (q 1) ∧
      parityRepresentativeLE (q 1) (q 0) ∧
      ¬ Std.Antisymm parityRepresentativeLE := by
  dsimp only
  let q := Quotient.mk Lemmatheca.Entry.EquivalenceRelations.paritySetoid
  have hne : q 0 ≠ q 1 := by
    intro h
    have hmod := Quotient.exact h
    change (0 : ℤ) % 2 = 1 % 2 at hmod
    norm_num at hmod
  have heq : q 2 = q 0 := Quotient.sound (by change (2 : ℤ) % 2 = 0 % 2; norm_num)
  have h01 : parityRepresentativeLE (q 0) (q 1) := ⟨0, 1, rfl, rfl, by decide⟩
  have h10 : parityRepresentativeLE (q 1) (q 0) := ⟨1, 2, rfl, heq, by decide⟩
  exact ⟨hne, heq, by decide, by decide, h01, h10,
    fun h => hne (h.antisymm _ _ h01 h10)⟩

end Lemmatheca.Entry.OrderedSets
