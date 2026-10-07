import Lemmatheca.SetTheory.AlmostDisjoint
import Lemmatheca.SetTheory.BooleanAlgebras
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Atoms
import Mathlib.Order.Hom.BoundedLattice

/-! Power sets modulo an ideal of small subsets.

The ambient set is represented by its member type. `Order.Ideal (Set α)`
uses inclusion and therefore expresses precisely empty-set, downward, and
finite-union closure. Native quotient elements are related to the human
equivalence classes by `Setoid.quotientEquivClasses`. All operations below
are explicit lifts of the set operations, and the order is meet absorption.
Classical Lean checks ordinary conclusions, not first-order axiom strength.
-/

namespace Lemmatheca.SetTheory.SubsetsModuloSmallSets

open Set Filter Order
open scoped Classical symmDiff
universe u

variable {α : Type u}

/-- The ideal of all finite subsets of a carrier. -/
def finiteIdeal (α : Type u) : Order.Ideal (Set α) where
  carrier := {A | A.Finite}
  lower' := fun _ _ h hA => hA.subset h
  nonempty' := ⟨∅, Set.finite_empty⟩
  directed' := fun A hA B hB => ⟨A ∪ B, hA.union hB, subset_union_left, subset_union_right⟩

theorem finiteIdeal_proper_iff (α : Type u) :
    (finiteIdeal α).IsProper ↔ (Set.univ : Set α).Infinite := by
  rw [Order.Ideal.isProper_iff_top_notMem]
  rfl

theorem finiteIdeal_not_countably_union_closed :
    (∀ n : ℕ, ({n} : Set ℕ) ∈ finiteIdeal ℕ) ∧
      (⋃ n : ℕ, ({n} : Set ℕ)) ∉ finiteIdeal ℕ := by
  refine ⟨fun n => Set.finite_singleton n, ?_⟩
  change ¬ (⋃ n : ℕ, ({n} : Set ℕ)).Finite
  have hu : (⋃ n : ℕ, ({n} : Set ℕ)) = Set.univ := by ext x; simp
  rw [hu]
  exact Set.infinite_univ

/-- Two subsets agree outside an error belonging to the ideal. -/
def EqMod (I : Order.Ideal (Set α)) (A B : Set α) : Prop := A ∆ B ∈ I

theorem eqMod_equivalence (I : Order.Ideal (Set α)) :
    Equivalence (EqMod I) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A
    change A ∆ A ∈ I
    rw [symmDiff_self]
    exact I.bot_mem
  · intro A B h
    simpa [EqMod, symmDiff_comm] using h
  · intro A B C hAB hBC
    exact I.lower (symmDiff_triangle A B C) (Order.Ideal.sup_mem hAB hBC)

def modSetoid (I : Order.Ideal (Set α)) : Setoid (Set α) where
  r := EqMod I
  iseqv := eqMod_equivalence I

abbrev SmallQuotient (I : Order.Ideal (Set α)) := Quotient (modSetoid I)

def mk (I : Order.Ideal (Set α)) (A : Set α) : SmallQuotient I :=
  Quotient.mk (modSetoid I) A

theorem eqMod_operations_compatible (I : Order.Ideal (Set α))
    (A A' B B' : Set α) (hA : EqMod I A A') (hB : EqMod I B B') :
    EqMod I (A ∩ B) (A' ∩ B') ∧ EqMod I (A ∪ B) (A' ∪ B') ∧
      EqMod I Aᶜ A'ᶜ := by
  have hE : A ∆ A' ∪ B ∆ B' ∈ I := Order.Ideal.sup_mem hA hB
  refine ⟨I.lower ?_ hE, I.lower (Set.union_symmDiff_union_subset) hE, ?_⟩
  · intro x hx
    simp only [mem_symmDiff, mem_inter_iff, mem_union] at hx ⊢
    tauto
  · have he : Aᶜ ∆ A'ᶜ = A ∆ A' := by ext x; simp only [mem_symmDiff, mem_compl_iff]; tauto
    simpa [EqMod, he] using hA

def meet (I : Order.Ideal (Set α)) : SmallQuotient I → SmallQuotient I → SmallQuotient I :=
  Quotient.lift₂ (fun A B => mk I (A ∩ B))
    (fun A B A' B' hA hB => Quotient.sound
      (eqMod_operations_compatible I A A' B B' hA hB).1)

def join (I : Order.Ideal (Set α)) : SmallQuotient I → SmallQuotient I → SmallQuotient I :=
  Quotient.lift₂ (fun A B => mk I (A ∪ B))
    (fun A B A' B' hA hB => Quotient.sound
      (eqMod_operations_compatible I A A' B B' hA hB).2.1)

def complement (I : Order.Ideal (Set α)) : SmallQuotient I → SmallQuotient I :=
  Quotient.lift (fun A => mk I Aᶜ)
    (fun A A' hA => Quotient.sound
      (eqMod_operations_compatible I A A' A A' hA hA).2.2)

private theorem mk_eq_iff (I : Order.Ideal (Set α)) (A B : Set α) :
    mk I A = mk I B ↔ EqMod I A B := Quotient.eq

private theorem meet_eq_left_iff (I : Order.Ideal (Set α)) (A B : Set α) :
    meet I (mk I A) (mk I B) = mk I A ↔ A \ B ∈ I := by
  change mk I (A ∩ B) = mk I A ↔ _
  rw [mk_eq_iff]
  have he : (A ∩ B) ∆ A = A \ B := by
    ext x
    simp only [mem_symmDiff, mem_inter_iff, Set.mem_sdiff]
    tauto
  simp only [EqMod, he]

/-- Its data fields use the lifted set operations and meet-defined order. -/
instance quotientBooleanAlgebra (I : Order.Ideal (Set α)) : BooleanAlgebra (SmallQuotient I) where
  le := fun q r => meet I q r = q
  sup := join I
  inf := meet I
  compl := complement I
  top := mk I Set.univ
  bot := mk I ∅
  le_refl := by
    intro q
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    change mk I (A ∩ A) = mk I A
    simp
  le_trans := by
    intro q r s hqr hrs
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨B, rfl⟩ := Quotient.mk_surjective r
    obtain ⟨C, rfl⟩ := Quotient.mk_surjective s
    apply (meet_eq_left_iff I A C).mpr
    apply I.lower _ (Order.Ideal.sup_mem
      ((meet_eq_left_iff I A B).mp hqr) ((meet_eq_left_iff I B C).mp hrs))
    intro x hx
    change x ∈ (A \ B) ∪ (B \ C)
    simp only [Set.mem_sdiff, mem_union] at hx ⊢
    tauto
  le_antisymm := by
    intro q r hqr hrq
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨B, rfl⟩ := Quotient.mk_surjective r
    apply (mk_eq_iff I A B).mpr
    exact Order.Ideal.sup_mem ((meet_eq_left_iff I A B).mp hqr)
      ((meet_eq_left_iff I B A).mp hrq)
  le_sup_left := by
    intro q r
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨B, rfl⟩ := Quotient.mk_surjective r
    change mk I (A ∩ (A ∪ B)) = mk I A
    congr 1
    ext x
    simp only [mem_inter_iff, mem_union]
    tauto
  le_sup_right := by
    intro q r
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨B, rfl⟩ := Quotient.mk_surjective r
    change mk I (B ∩ (A ∪ B)) = mk I B
    congr 1
    ext x
    simp only [mem_inter_iff, mem_union]
    tauto
  sup_le := by
    intro q r s hq hr
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨B, rfl⟩ := Quotient.mk_surjective r
    obtain ⟨C, rfl⟩ := Quotient.mk_surjective s
    apply (meet_eq_left_iff I (A ∪ B) C).mpr
    rw [Set.union_sdiff_distrib]
    exact Order.Ideal.sup_mem ((meet_eq_left_iff I A C).mp hq)
      ((meet_eq_left_iff I B C).mp hr)
  inf_le_left := by
    intro q r
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨B, rfl⟩ := Quotient.mk_surjective r
    change mk I ((A ∩ B) ∩ A) = mk I (A ∩ B)
    congr 1
    ext x
    simp only [mem_inter_iff]
    tauto
  inf_le_right := by
    intro q r
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨B, rfl⟩ := Quotient.mk_surjective r
    change mk I ((A ∩ B) ∩ B) = mk I (A ∩ B)
    congr 1
    ext x
    simp only [mem_inter_iff]
    tauto
  le_inf := by
    intro q r s hr hs
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨B, rfl⟩ := Quotient.mk_surjective r
    obtain ⟨C, rfl⟩ := Quotient.mk_surjective s
    apply (meet_eq_left_iff I A (B ∩ C)).mpr
    rw [Set.sdiff_inter]
    exact Order.Ideal.sup_mem ((meet_eq_left_iff I A B).mp hr)
      ((meet_eq_left_iff I A C).mp hs)
  le_sup_inf := by
    intro q r s
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨B, rfl⟩ := Quotient.mk_surjective r
    obtain ⟨C, rfl⟩ := Quotient.mk_surjective s
    change mk I (((A ∪ B) ∩ (A ∪ C)) ∩ (A ∪ (B ∩ C))) = mk I ((A ∪ B) ∩ (A ∪ C))
    congr 1
    ext x
    simp only [mem_inter_iff, mem_union]
    tauto
  inf_compl_le_bot := by
    intro q
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    change mk I ((A ∩ Aᶜ) ∩ ∅) = mk I (A ∩ Aᶜ)
    simp
  top_le_sup_compl := by
    intro q
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    change mk I (Set.univ ∩ (A ∪ Aᶜ)) = mk I Set.univ
    simp
  le_top := by
    intro q
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    change mk I (A ∩ Set.univ) = mk I A
    simp
  bot_le := by
    intro q
    obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
    change mk I (∅ ∩ A) = mk I ∅
    simp

theorem quotient_operations (I : Order.Ideal (Set α)) (A B : Set α) :
    mk I A ⊓ mk I B = mk I (A ∩ B) ∧
      mk I A ⊔ mk I B = mk I (A ∪ B) ∧
      (mk I A)ᶜ = mk I Aᶜ ∧
      (⊥ : SmallQuotient I) = mk I ∅ ∧ (⊤ : SmallQuotient I) = mk I Set.univ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem quotient_le_iff (I : Order.Ideal (Set α)) (A B : Set α) :
    mk I A ≤ mk I B ↔ A \ B ∈ I := meet_eq_left_iff I A B

/-- The power-set projection is a bounded lattice homomorphism, hence Boolean. -/
def projection (I : Order.Ideal (Set α)) : BoundedLatticeHom (Set α) (SmallQuotient I) where
  toFun := mk I
  map_sup' := fun _ _ => rfl
  map_inf' := fun _ _ => rfl
  map_top' := rfl
  map_bot' := rfl

theorem quotient_zero_iff (I : Order.Ideal (Set α)) (A : Set α) :
    mk I A = ⊥ ↔ A ∈ I := by
  change mk I A = mk I ∅ ↔ _
  rw [mk_eq_iff]
  simp [EqMod, Set.symmDiff_def]

theorem quotient_one_iff (I : Order.Ideal (Set α)) (A : Set α) :
    mk I A = ⊤ ↔ Aᶜ ∈ I := by
  change mk I A = mk I Set.univ ↔ _
  rw [mk_eq_iff]
  have he : A ∆ Set.univ = Aᶜ := by ext x; simp only [mem_symmDiff, mem_univ, mem_compl_iff]; tauto
  simp only [EqMod, he]

theorem quotient_nontrivial_iff (I : Order.Ideal (Set α)) :
    Nontrivial (SmallQuotient I) ↔ I.IsProper := by
  constructor
  · intro h
    have := h
    apply Order.Ideal.isProper_iff_top_notMem.mpr
    intro hu
    exact bot_ne_top ((quotient_zero_iff I Set.univ).mpr hu).symm
  · intro h
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro he
    exact (Order.Ideal.isProper_iff_top_notMem.mp h)
      ((quotient_zero_iff I Set.univ).mp he.symm)

theorem quotient_subsingleton_iff (I : Order.Ideal (Set α)) :
    Subsingleton (SmallQuotient I) ↔ (Set.univ : Set α) ∈ I := by
  constructor
  · intro h
    have := h
    exact (quotient_zero_iff I Set.univ).mp (Subsingleton.elim _ _)
  · intro hu
    exact subsingleton_of_bot_eq_top ((quotient_zero_iff I Set.univ).mpr hu).symm

/-- An outside subset is represented on the member type of the remaining region. -/
def outside (S A : Set α) : Set {x : α // x ∉ S} := {x | x.val ∈ A}

theorem principal_eqMod_iff (S A B : Set α) :
    EqMod (Order.Ideal.principal S) A B ↔ A \ S = B \ S := by
  simp only [EqMod, Order.Ideal.mem_principal, Set.subset_def, Set.mem_symmDiff,
    Set.ext_iff, Set.mem_sdiff]
  constructor
  · intro h x
    specialize h x
    tauto
  · intro h x
    specialize h x
    tauto

/-- Discarding a fixed region, with the inverse taking the image in the ambient carrier. -/
noncomputable def fixedRegionIso (S : Set α) :
    SmallQuotient (Order.Ideal.principal S) ≃o Set {x : α // x ∉ S} where
  toFun := Quotient.lift (fun A => outside S A) (by
    intro A B h
    ext x
    have hx := Set.ext_iff.mp ((principal_eqMod_iff S A B).mp h) x.val
    simpa [outside, x.property] using hx)
  invFun := fun T => mk (Order.Ideal.principal S) (Subtype.val '' T)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro A
    apply (mk_eq_iff _ _ _).mpr
    rw [principal_eqMod_iff]
    ext x
    simp [outside]
  right_inv := by
    intro T
    ext x
    change x.val ∈ Subtype.val '' T ↔ x ∈ T
    simp [x.property]
  map_rel_iff' := by
    intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro A B
    change outside S A ⊆ outside S B ↔
      mk (Order.Ideal.principal S) A ≤ mk (Order.Ideal.principal S) B
    rw [quotient_le_iff]
    change outside S A ⊆ outside S B ↔ A \ B ∈ Order.Ideal.principal S
    rw [Order.Ideal.mem_principal]
    constructor
    · intro h x hx
      by_contra hs
      exact hx.2 (h (show (⟨x, hs⟩ : {x : α // x ∉ S}) ∈ outside S A from hx.1))
    · intro h x hx
      by_contra hb
      exact x.property (h ⟨hx, hb⟩)

abbrev FiniteQuotient := SmallQuotient (finiteIdeal ℕ)

theorem finite_quotient_eq_iff (A B : Set ℕ) :
    mk (finiteIdeal ℕ) A = mk (finiteIdeal ℕ) B ↔ A =ᶠ[cofinite] B := by
  rw [mk_eq_iff, FiniteErrors.almostEq_iff_finite_symmDiff]
  rfl

theorem finite_quotient_le_iff (A B : Set ℕ) :
    mk (finiteIdeal ℕ) A ≤ mk (finiteIdeal ℕ) B ↔ A ≤ᶠ[cofinite] B := by
  rw [quotient_le_iff, FiniteErrors.almostSubset_iff_finite_sdiff]
  rfl

theorem finite_quotient_nonzero_iff (A : Set ℕ) :
    mk (finiteIdeal ℕ) A ≠ ⊥ ↔ A.Infinite := by
  rw [ne_eq, quotient_zero_iff]
  rfl

instance finiteQuotientNontrivial : Nontrivial FiniteQuotient :=
  (quotient_nontrivial_iff _).mpr ((finiteIdeal_proper_iff ℕ).mpr Set.infinite_univ)

theorem finite_quotient_zero_meet_iff (A B : Set ℕ) :
    mk (finiteIdeal ℕ) A ⊓ mk (finiteIdeal ℕ) B = ⊥ ↔ (A ∩ B).Finite := by
  rw [(quotient_operations _ A B).1, quotient_zero_iff]
  rfl

theorem almostDisjoint_classes (A : Set (Set ℕ)) (hA : AlmostDisjoint.IsAlmostDisjoint A) :
    Set.InjOn (mk (finiteIdeal ℕ)) A ∧
      (∀ q ∈ mk (finiteIdeal ℕ) '' A, q ≠ ⊥) ∧
      (mk (finiteIdeal ℕ) '' A).Pairwise (fun q r => q ⊓ r = ⊥) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S hS T hT he
    by_contra hne
    have hz := (finite_quotient_zero_meet_iff S T).mpr (hA.2 hS hT hne)
    rw [← he, inf_idem] at hz
    exact ((finite_quotient_nonzero_iff S).mpr (hA.1 S hS)) hz
  · rintro q ⟨S, hS, rfl⟩
    exact (finite_quotient_nonzero_iff S).mpr (hA.1 S hS)
  · rintro q ⟨S, hS, rfl⟩ r ⟨T, hT, rfl⟩ hne
    apply (finite_quotient_zero_meet_iff S T).mpr
    exact hA.2 hS hT (fun h => hne (congrArg (mk (finiteIdeal ℕ)) h))

theorem representatives_almostDisjoint (Q : Set FiniteQuotient)
    (hQ : ∀ q ∈ Q, q ≠ ⊥) (hd : Q.Pairwise (fun q r => q ⊓ r = ⊥))
    (r : Q → Set ℕ) (hr : ∀ q : Q, mk (finiteIdeal ℕ) (r q) = q.val) :
    AlmostDisjoint.IsAlmostDisjoint (Set.range r) ∧ Function.Injective r ∧
      mk (finiteIdeal ℕ) '' Set.range r = Q := by
  have hi : Function.Injective r := by
    intro q v he
    apply Subtype.ext
    rw [← hr q, ← hr v, he]
  refine ⟨⟨?_, ?_⟩, hi, ?_⟩
  · rintro S ⟨q, rfl⟩
    exact (finite_quotient_nonzero_iff (r q)).mp (by rw [hr q]; exact hQ q.val q.property)
  · rintro S ⟨q, rfl⟩ T ⟨v, rfl⟩ hne
    apply (finite_quotient_zero_meet_iff _ _).mp
    rw [hr q, hr v]
    exact hd q.property v.property (fun h => hne (congrArg r (Subtype.ext h)))
  · ext q
    constructor
    · rintro ⟨S, ⟨v, rfl⟩, he⟩
      rw [hr v] at he
      exact he ▸ v.property
    · intro hq
      exact ⟨r ⟨q, hq⟩, mem_range_self _, hr _⟩

/-- An ordered Boolean algebra is atomless when none of its elements is an atom. -/
def IsAtomless (B : Type u) [PartialOrder B] [OrderBot B] : Prop := ∀ q : B, ¬ IsAtom q

theorem enumeration_split (A : Set ℕ) (e : ℕ ≃o A) :
    let C := Set.range (fun n => (e (2 * n)).val)
    let D := Set.range (fun n => (e (2 * n + 1)).val)
    C.Infinite ∧ D.Infinite ∧ Disjoint C D ∧ C ∪ D = A ∧
      (⊥ : FiniteQuotient) < mk (finiteIdeal ℕ) C ∧
      mk (finiteIdeal ℕ) C < mk (finiteIdeal ℕ) A := by
  let f : ℕ → ℕ := fun n => (e n).val
  let C := Set.range (fun n => f (2 * n))
  let D := Set.range (fun n => f (2 * n + 1))
  change C.Infinite ∧ D.Infinite ∧ Disjoint C D ∧ C ∪ D = A ∧
    (⊥ : FiniteQuotient) < mk (finiteIdeal ℕ) C ∧ mk (finiteIdeal ℕ) C < mk (finiteIdeal ℕ) A
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hC : C.Infinite := infinite_range_of_injective fun m n h => by
    have := hf h
    omega
  have hD : D.Infinite := infinite_range_of_injective fun m n h => by
    have := hf h
    omega
  have hCA : C ⊆ A := by rintro x ⟨n, rfl⟩; exact (e (2 * n)).property
  have hDA : D ⊆ A := by rintro x ⟨n, rfl⟩; exact (e (2 * n + 1)).property
  have hCD : Disjoint C D := by
    rw [Set.disjoint_left]
    rintro x ⟨n, hn⟩ ⟨m, hm⟩
    have := hf (hn.trans hm.symm)
    omega
  have hU : C ∪ D = A := by
    apply Set.Subset.antisymm (union_subset hCA hDA)
    intro x hx
    obtain ⟨k, hk⟩ := e.surjective ⟨x, hx⟩
    have hfk : f k = x := congrArg Subtype.val hk
    by_cases hpar : k % 2 = 0
    · left
      refine ⟨k / 2, ?_⟩
      have he : 2 * (k / 2) = k := by omega
      simpa [he] using hfk
    · right
      refine ⟨k / 2, ?_⟩
      have he : 2 * (k / 2) + 1 = k := by omega
      simpa [he] using hfk
  refine ⟨hC, hD, hCD, hU, bot_lt_iff_ne_bot.mpr ((finite_quotient_nonzero_iff C).mpr hC), ?_⟩
  apply lt_iff_le_not_ge.mpr
  constructor
  · apply (quotient_le_iff _ C A).mpr
    change (C \ A).Finite
    rw [Set.sdiff_eq_empty.mpr hCA]
    exact Set.finite_empty
  · intro hAC
    have hfin : (A \ C).Finite := (quotient_le_iff _ A C).mp hAC
    exact hD (hfin.subset fun x hx => ⟨hDA hx, fun hc => Set.disjoint_left.mp hCD hc hx⟩)

theorem split_nonzero_class (q : FiniteQuotient) (hq : q ≠ ⊥) :
    ∃ u v : FiniteQuotient, u ≠ ⊥ ∧ v ≠ ⊥ ∧ u ⊓ v = ⊥ ∧ u ⊔ v = q := by
  obtain ⟨A, rfl⟩ := Quotient.mk_surjective q
  have hA : A.Infinite := (finite_quotient_nonzero_iff A).mp hq
  have := hA.to_subtype
  let e := Nat.Subtype.orderIsoOfNat A
  let C := Set.range (fun n => (e (2 * n)).val)
  let D := Set.range (fun n => (e (2 * n + 1)).val)
  obtain ⟨hC, hD, hCD, hU, _, _⟩ := enumeration_split A e
  refine ⟨mk (finiteIdeal ℕ) C, mk (finiteIdeal ℕ) D,
    (finite_quotient_nonzero_iff C).mpr hC, (finite_quotient_nonzero_iff D).mpr hD, ?_, ?_⟩
  · apply (finite_quotient_zero_meet_iff C D).mpr
    rw [Set.disjoint_iff_inter_eq_empty.mp hCD]
    exact Set.finite_empty
  · rw [(quotient_operations _ C D).2.1, hU]
    rfl

theorem finite_quotient_atomless : IsAtomless FiniteQuotient := by
  intro q hAtom
  obtain ⟨u, v, hu, hv, huv, he⟩ := split_nonzero_class q hAtom.ne_bot
  have huq : u ≤ q := he ▸ le_sup_left
  have hvq : v ≤ q := he ▸ le_sup_right
  have hue : u = q := (hAtom.le_iff_eq hu).mp huq
  have hvu : v ≤ u := hue.symm ▸ hvq
  exact hv ((inf_eq_right.mpr hvu).symm.trans huv)

theorem descending_representatives_pseudointersection (A : ℕ → Set ℕ)
    (hinf : ∀ n, (A n).Infinite)
    (hd : ∀ i j, i ≤ j → A j ≤ᶠ[cofinite] A i) :
    ∃ B, FiniteErrors.IsPseudointersection (Set.range A) B := by
  classical
  apply FiniteErrors.countable_pseudointersection (Set.range A) (Set.countable_range A)
  intro E hEA hE
  have := hE.fintype
  let idx : E → ℕ := fun S => Classical.choose (hEA S.property)
  have hi (S : E) : A (idx S) = S.val := Classical.choose_spec (hEA S.property)
  let N := (Finset.univ : Finset E).sup idx
  have hP : FiniteErrors.IsPseudointersection E (A N) := by
    refine ⟨hinf N, ?_⟩
    intro S hS
    let v : E := ⟨S, hS⟩
    change A N ≤ᶠ[cofinite] v.val
    rw [← hi v]
    exact hd (idx v) N (Finset.le_sup (Finset.mem_univ v))
  exact hP.strongFiniteIntersections E Set.Subset.rfl hE

theorem descending_nonzero_lower_bound (q : ℕ → FiniteQuotient)
    (hd : Antitone q) (hn : ∀ n, q n ≠ ⊥) :
    ∃ r : FiniteQuotient, r ≠ ⊥ ∧ ∀ n, r ≤ q n := by
  classical
  choose A hA using fun n => Quotient.mk_surjective (q n)
  change ∀ n, mk (finiteIdeal ℕ) (A n) = q n at hA
  have hInf : ∀ n, (A n).Infinite := fun n => (finite_quotient_nonzero_iff (A n)).mp
    (by rw [hA n]; exact hn n)
  have hDec : ∀ i j, i ≤ j → A j ≤ᶠ[cofinite] A i := by
    intro i j hij
    apply (finite_quotient_le_iff _ _).mp
    rw [hA j, hA i]
    exact hd hij
  obtain ⟨B, hB⟩ := descending_representatives_pseudointersection A hInf hDec
  refine ⟨mk (finiteIdeal ℕ) B, (finite_quotient_nonzero_iff B).mpr hB.1, ?_⟩
  intro n
  rw [← hA n]
  exact (finite_quotient_le_iff B (A n)).mpr (hB.2 (A n) (mem_range_self n))

end Lemmatheca.SetTheory.SubsetsModuloSmallSets
