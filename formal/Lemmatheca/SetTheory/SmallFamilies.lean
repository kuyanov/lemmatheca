import Lemmatheca.SetTheory.AlmostDisjoint
import Lemmatheca.SetTheory.BoundingAndDominating

/-! Elementary minima p, a and u. The almost disjoint family must be infinite,
and the ultrafilter must be nonprincipal. All cardinalities refer to membership
subtypes, and almost containment uses the cofinite filter. -/

namespace Lemmatheca.SetTheory.SmallFamilies

open Set Filter Cardinal
open FiniteErrors

def IsPseudointersectionObstruction (F : Set (Set ℕ)) : Prop :=
  FiniteErrors.HasStrongFiniteIntersectionProperty F ∧
    ¬ ∃ P, FiniteErrors.IsPseudointersection F P

def IsInfiniteMAD (A : Set (Set ℕ)) : Prop :=
  A.Infinite ∧ AlmostDisjoint.IsMaximalAlmostDisjoint A

def IsFreeUltrafilterBase (B : Set (Set ℕ)) : Prop :=
  ∃ U : Ultrafilter ℕ, ¬ FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ) ∧
    (U : Filter ℕ).HasBasis (fun S => S ∈ B) id

noncomputable def pseudointersectionNumber : Cardinal :=
  ⨅ F : {F : Set (Set ℕ) // IsPseudointersectionObstruction F}, Cardinal.mk F.val

noncomputable def almostDisjointnessNumber : Cardinal :=
  ⨅ A : {A : Set (Set ℕ) // IsInfiniteMAD A}, Cardinal.mk A.val

noncomputable def ultrafilterNumber : Cardinal :=
  ⨅ B : {B : Set (Set ℕ) // IsFreeUltrafilterBase B}, Cardinal.mk B.val

theorem free_base_obstruction (B : Set (Set ℕ)) (hB : IsFreeUltrafilterBase B) :
    IsPseudointersectionObstruction B := by
  classical
  obtain ⟨U, hU, hb⟩ := hB
  have hmem (S : Set ℕ) (hS : S ∈ (U : Filter ℕ)) : S.Infinite := by
    intro hfin
    obtain ⟨x, _, hx⟩ := U.eq_pure_of_finite_mem hfin hS
    exact hU ((FiltersAndUltrafilters.principal_ultrafilter_iff U).mpr ⟨x, hx⟩)
  have hstrong : HasStrongFiniteIntersectionProperty B := by
    intro E hEB hE
    apply hmem
    apply (Filter.sInter_mem hE).mpr
    intro S hS
    exact hb.mem_iff.mpr ⟨S, hEB hS, Subset.rfl⟩
  refine ⟨hstrong, ?_⟩
  rintro ⟨P, hP⟩
  let e := hP.1.natEmbedding P
  let f : ℕ → ℕ := fun n => (e n).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let C := range (fun n => f (2 * n))
  let D := range (fun n => f (2 * n + 1))
  have hC : C.Infinite := infinite_range_of_injective fun m n h => by
    have := hf h
    omega
  have hD : D.Infinite := infinite_range_of_injective fun m n h => by
    have := hf h
    omega
  have hCP : C ⊆ P := by rintro _ ⟨n, rfl⟩; exact (e (2 * n)).property
  have hDP : D ⊆ P := by rintro _ ⟨n, rfl⟩; exact (e (2 * n + 1)).property
  have hDC : Disjoint D C := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn⟩ ⟨m, hm⟩
    have := hf (hn.trans hm.symm)
    omega
  rcases U.mem_or_compl_mem C with hc | hc
  · obtain ⟨S, hSB, hSC⟩ := hb.mem_iff.mp hc
    have hd := (almostSubset_iff_finite_sdiff P S).mp (hP.2 S hSB)
    exact hD (hd.subset fun x hx => ⟨hDP hx, fun hs => Set.disjoint_left.mp hDC hx (hSC hs)⟩)
  · obtain ⟨S, hSB, hSC⟩ := hb.mem_iff.mp hc
    have hd := (almostSubset_iff_finite_sdiff P S).mp (hP.2 S hSB)
    exact hC (hd.subset fun x hx => ⟨hCP hx, fun hs => hSC hs hx⟩)

theorem witnesses_exist :
    (∃ F, IsPseudointersectionObstruction F) ∧
    (∃ A, IsInfiniteMAD A ∧ Cardinal.mk A = continuum) ∧
    ∃ B, IsFreeUltrafilterBase B := by
  classical
  let U := Filter.hyperfilter ℕ
  have hU : ¬ FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ) :=
    (FiltersAndUltrafilters.nonprincipal_iff_cofinite U).mpr Filter.hyperfilter_le_cofinite
  let B : Set (Set ℕ) := {S | S ∈ (U : Filter ℕ)}
  have hB : IsFreeUltrafilterBase B := by
    refine ⟨U, hU, ⟨?_⟩⟩
    intro S
    exact ⟨fun h => ⟨S, h, Subset.rfl⟩, fun ⟨T, hT, hTS⟩ => mem_of_superset hT hTS⟩
  obtain ⟨A, hA, hcard⟩ := AlmostDisjoint.continuum_maximal_family
  have hi : A.Infinite := by
    rw [← Cardinal.aleph0_le_mk_set]
    rw [hcard]
    exact Cardinal.aleph0_le_continuum
  exact ⟨⟨B, free_base_obstruction B hB⟩, ⟨A, ⟨hi, hA⟩, hcard⟩, B, hB⟩

theorem pseudointersectionNumber_spec :
    (∃ F, IsPseudointersectionObstruction F ∧ Cardinal.mk F = pseudointersectionNumber) ∧
    (∀ F, IsPseudointersectionObstruction F → pseudointersectionNumber ≤ Cardinal.mk F) ∧
    (∀ F : Set (Set ℕ), Cardinal.mk F < pseudointersectionNumber →
      FiniteErrors.HasStrongFiniteIntersectionProperty F →
        ∃ P, FiniteErrors.IsPseudointersection F P)  := by
  classical
  obtain ⟨F, hF⟩ := witnesses_exist.1
  have : Nonempty {F : Set (Set ℕ) // IsPseudointersectionObstruction F} := ⟨⟨F, hF⟩⟩
  obtain ⟨F, hF⟩ := ciInf_mem (fun F : {F : Set (Set ℕ) // IsPseudointersectionObstruction F} => Cardinal.mk F.val)
  have hmin (F : Set (Set ℕ)) (hF : IsPseudointersectionObstruction F) : pseudointersectionNumber ≤ Cardinal.mk F :=
    ciInf_le' (fun F : {F : Set (Set ℕ) // IsPseudointersectionObstruction F} => Cardinal.mk F.val) ⟨F, hF⟩
  refine ⟨⟨F.val, F.property, hF⟩, hmin, ?_⟩
  intro F hcard hstrong
  by_contra h
  exact hcard.not_ge (hmin F ⟨hstrong, h⟩)


theorem almostDisjointnessNumber_spec :
    (∃ A, IsInfiniteMAD A ∧ Cardinal.mk A = almostDisjointnessNumber) ∧
    (∀ A, IsInfiniteMAD A → almostDisjointnessNumber ≤ Cardinal.mk A)  := by
  classical
  obtain ⟨F, hF, _⟩ := witnesses_exist.2.1
  have : Nonempty {F : Set (Set ℕ) // IsInfiniteMAD F} := ⟨⟨F, hF⟩⟩
  obtain ⟨F, hF⟩ := ciInf_mem (fun F : {F : Set (Set ℕ) // IsInfiniteMAD F} => Cardinal.mk F.val)
  have hmin (F : Set (Set ℕ)) (hF : IsInfiniteMAD F) : almostDisjointnessNumber ≤ Cardinal.mk F :=
    ciInf_le' (fun F : {F : Set (Set ℕ) // IsInfiniteMAD F} => Cardinal.mk F.val) ⟨F, hF⟩
  exact ⟨⟨F.val, F.property, hF⟩, hmin⟩


theorem ultrafilterNumber_spec :
    (∃ B, IsFreeUltrafilterBase B ∧ Cardinal.mk B = ultrafilterNumber) ∧
    (∀ B, IsFreeUltrafilterBase B → ultrafilterNumber ≤ Cardinal.mk B)  := by
  classical
  obtain ⟨F, hF⟩ := witnesses_exist.2.2
  have : Nonempty {F : Set (Set ℕ) // IsFreeUltrafilterBase F} := ⟨⟨F, hF⟩⟩
  obtain ⟨F, hF⟩ := ciInf_mem (fun F : {F : Set (Set ℕ) // IsFreeUltrafilterBase F} => Cardinal.mk F.val)
  have hmin (F : Set (Set ℕ)) (hF : IsFreeUltrafilterBase F) : ultrafilterNumber ≤ Cardinal.mk F :=
    ciInf_le' (fun F : {F : Set (Set ℕ) // IsFreeUltrafilterBase F} => Cardinal.mk F.val) ⟨F, hF⟩
  exact ⟨⟨F.val, F.property, hF⟩, hmin⟩


theorem bounds :
    (ℵ₁ ≤ pseudointersectionNumber ∧ pseudointersectionNumber ≤ continuum) ∧
    (ℵ₁ ≤ almostDisjointnessNumber ∧ almostDisjointnessNumber ≤ continuum) ∧
    (ℵ₁ ≤ ultrafilterNumber ∧ ultrafilterNumber ≤ continuum) := by
  have hupper (F : Set (Set ℕ)) : Cardinal.mk F ≤ continuum := by
    calc
      Cardinal.mk F ≤ Cardinal.mk (Set ℕ) := Cardinal.mk_subtype_le _
      _ = continuum := by rw [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0]
  obtain ⟨P, hP, hpc⟩ := pseudointersectionNumber_spec.1
  obtain ⟨A, hA, hac⟩ := almostDisjointnessNumber_spec.1
  obtain ⟨B, hB, hbc⟩ := ultrafilterNumber_spec.1
  have hp : ℵ₁ ≤ Cardinal.mk P := by
    by_contra h
    have hc := Cardinal.le_aleph0_iff_set_countable.mp
      (Cardinal.lt_aleph_one_iff.mp (lt_of_not_ge h))
    exact hP.2 (countable_pseudointersection P hc hP.1)
  have ha : ℵ₁ ≤ Cardinal.mk A := by
    by_contra h
    have hc := Cardinal.le_aleph0_iff_set_countable.mp
      (Cardinal.lt_aleph_one_iff.mp (lt_of_not_ge h))
    obtain ⟨X, _, hn, _, hx⟩ := AlmostDisjoint.countable_infinite_extension A hA.2.1 hc hA.1
    have he := hA.2.2 (insert X A) hx (subset_insert _ _)
    exact hn (he ▸ mem_insert X A)
  have hu : ℵ₁ ≤ Cardinal.mk B := by
    by_contra h
    have hc := Cardinal.le_aleph0_iff_set_countable.mp
      (Cardinal.lt_aleph_one_iff.mp (lt_of_not_ge h))
    obtain ⟨U, hU, hb⟩ := hB
    exact no_countable_ultrafilter_base U hU B hc hb
  exact ⟨⟨hpc ▸ hp, hpc ▸ hupper P⟩, ⟨hac ▸ ha, hac ▸ hupper A⟩,
    hbc ▸ hu, hbc ▸ hupper B⟩

theorem pseudointersectionNumber_le_boundingNumber :
    pseudointersectionNumber ≤ BoundingAndDominating.boundingNumber := by
  classical
  by_contra h
  obtain ⟨B, hB, hcard⟩ := BoundingAndDominating.boundingNumber_spec.1
  have hc : Cardinal.mk B < pseudointersectionNumber := hcard ▸ lt_of_not_ge h
  let I := B ⊕ ℕ
  let W : I → Set ℕ := fun i => match i with
    | Sum.inl f => {x | ∀ j ≤ (Nat.unpair x).1, f.val j ≤ (Nat.unpair x).2}
    | Sum.inr k => {x | k ≤ (Nat.unpair x).1}
  let F : Set (Set ℕ) := range W
  have hF : Cardinal.mk F < pseudointersectionNumber := by
    apply (Cardinal.mk_range_le (f := W)).trans_lt
    rw [Cardinal.mk_sum, Cardinal.mk_nat]
    simp only [Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 1 |>.trans bounds.1.1) hc
      (Cardinal.aleph0_lt_aleph_one.trans_le bounds.1.1)
  have hstrong : HasStrongFiniteIntersectionProperty F := by
    intro E hEF hE
    let : Fintype E := hE.fintype
    have hr (S : E) : ∃ i, W i = S.val := hEF S.property
    choose r hr using hr
    let threshold : I → ℕ := Sum.elim (fun _ => 0) id
    let value : I → ℕ → ℕ := Sum.elim (fun f => f.val) (fun _ _ => 0)
    let N : ℕ := Finset.univ.sup (fun S : E => threshold (r S))
    let m : ℕ → ℕ := fun n => Finset.univ.sup
      (fun S : E => (Finset.range (n + 1)).sup (value (r S)))
    let e : ℕ → ℕ := fun n => Nat.pair (n + N) (m (n + N))
    apply infinite_of_injective_forall_mem (f := e)
    · intro n k he
      have he' := congrArg (fun x => (Nat.unpair x).1) he
      simp only [e, Nat.unpair_pair] at he'
      omega
    · intro n
      rw [mem_sInter]
      intro S hSE
      let s : E := ⟨S, hSE⟩
      change e n ∈ s.val
      rw [← hr s]
      have ht : threshold (r s) ≤ N := Finset.le_sup (s := Finset.univ)
        (f := fun S : E => threshold (r S)) (Finset.mem_univ s)
      have hv (j : ℕ) (hj : j ≤ n + N) : value (r s) j ≤ m (n + N) := by
        exact (Finset.le_sup (s := Finset.range (n + N + 1))
          (f := value (r s)) (by simp; omega)).trans
            (Finset.le_sup (s := Finset.univ) (f := fun S : E =>
              (Finset.range (n + N + 1)).sup (value (r S))) (Finset.mem_univ s))
      cases he : r s with
      | inl f => simpa [W, e, value, he] using hv
      | inr k => simpa [W, e, threshold, he] using ht.trans (Nat.le_add_left N n)
  obtain ⟨P, hP⟩ := pseudointersectionNumber_spec.2.2 F hF hstrong
  have hex (n : ℕ) : ∃ p ∈ P, n ≤ (Nat.unpair p).1 := by
    have hd := (almostSubset_iff_finite_sdiff P (W (Sum.inr n))).mp
      (hP.2 _ (mem_range_self (Sum.inr n)))
    obtain ⟨p, hp, hpn⟩ := (hP.1.sdiff hd).nonempty
    refine ⟨p, hp, ?_⟩
    by_contra hn
    exact hpn ⟨hp, hn⟩
  choose p hp hpn using hex
  refine hB ⟨fun n => (Nat.unpair (p n)).2, ?_⟩
  intro f hf
  let s : B := ⟨f, hf⟩
  have hd := (almostSubset_iff_finite_sdiff P (W (Sum.inl s))).mp
    (hP.2 _ (mem_range_self (Sum.inl s)))
  obtain ⟨N, hN⟩ := (hd.image (fun x => (Nat.unpair x).1)).bddAbove
  apply eventually_atTop.mpr
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hgood : p n ∈ W (Sum.inl s) := by
    by_contra hbad
    have hb := hN (mem_image_of_mem (fun x => (Nat.unpair x).1) ⟨hp n, hbad⟩)
    have hb' := hpn n
    omega
  exact hgood n (hpn n)


theorem small_almost_disjoint_extension (A : Set (Set ℕ))
    (hA : AlmostDisjoint.IsAlmostDisjoint A) (hi : A.Infinite)
    (hc : Cardinal.mk A < BoundingAndDominating.boundingNumber) :
    ∃ X, X.Infinite ∧ X ∉ A ∧ ∀ S ∈ A, (S ∩ X).Finite := by
  classical
  let C : ℕ → Set ℕ := fun n => (hi.natEmbedding A n).val
  have hC (n) : C n ∈ A := (hi.natEmbedding A n).property
  have hCi : Function.Injective C := Subtype.val_injective.comp (hi.natEmbedding A).injective
  let D : ℕ → Set ℕ := fun n => C n \ ⋃ j : Fin n, C j.val
  have hD (n) : (D n).Infinite := by
    have hf : (⋃ j : Fin n, C n ∩ C j.val).Finite :=
      Set.finite_iUnion fun j => hA.2 (hC n) (hC j.val)
        (fun h => (ne_of_gt j.isLt) (hCi h))
    apply ((hA.1 (C n) (hC n)).sdiff hf).mono
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxU
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxU
    exact hx.2 (mem_iUnion.mpr ⟨j, hx.1, hj⟩)
  have hd : Pairwise (fun n m => Disjoint (D n) (D m)) := by
    intro n m hnm
    rw [Set.disjoint_left]
    intro x hxn hxm
    rcases lt_or_gt_of_ne hnm with h | h
    · exact hxm.2 (mem_iUnion.mpr ⟨⟨n, h⟩, hxn.1⟩)
    · exact hxn.2 (mem_iUnion.mpr ⟨⟨m, h⟩, hxm.1⟩)
  let d (n : ℕ) : ℕ ↪ D n := (hD n).natEmbedding (D n)
  let v (n k : ℕ) : ℕ := (d n k).val
  have hv (n) : Function.Injective (v n) := Subtype.val_injective.comp (d n).injective
  have hex (S : A) (n : ℕ) : ∃ m : ℕ, C n ≠ S.val → ∀ k, v n k ∈ S.val → k ≤ m := by
    by_cases he : C n = S.val
    · exact ⟨0, fun h => (h he).elim⟩
    · have hf : (D n ∩ S.val).Finite :=
        (hA.2 (hC n) S.property he).subset (inter_subset_inter_left _ sdiff_subset)
      have hp : ((v n) ⁻¹' S.val).Finite :=
        ((hf.preimage_embedding ⟨v n, hv n⟩).subset
          fun k hk => ⟨(d n k).property, hk⟩)
      obtain ⟨m, hm⟩ := hp.bddAbove
      exact ⟨m, fun _ k hk => hm hk⟩
  choose f hf using hex
  let F : Set (ℕ → ℕ) := range f
  have hF : Cardinal.mk F < BoundingAndDominating.boundingNumber :=
    (Cardinal.mk_range_le (f := f)).trans_lt hc
  obtain ⟨g, hg⟩ := BoundingAndDominating.boundingNumber_spec.2.2 F hF
  let x : ℕ → ℕ := fun n => v n (g n + 1)
  have hxD (n) : x n ∈ D n := (d n (g n + 1)).property
  have hxi : Function.Injective x := by
    intro n m he
    by_contra hnm
    exact Set.disjoint_left.mp (hd hnm) (hxD n) (he ▸ hxD m)
  let X : Set ℕ := range x
  have hX : X.Infinite := infinite_range_of_injective hxi
  have hfin (S : Set ℕ) (hS : S ∈ A) : (S ∩ X).Finite := by
    let s : A := ⟨S, hS⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hg (f s) (mem_range_self s))
    have hefin : {n | C n = S}.Finite :=
      (Set.finite_singleton S).preimage_embedding ⟨C, hCi⟩
    have hbad : {n | x n ∈ S}.Finite := by
      apply ((Set.finite_Iio N).union hefin).subset
      intro n hn
      by_cases hlt : n < N
      · exact Or.inl hlt
      · apply Or.inr
        by_contra he
        have hh := hf s n he (g n + 1) hn
        have hh' := hN n (le_of_not_gt hlt)
        omega
    apply (hbad.image x).subset
    rintro y ⟨hyS, n, rfl⟩
    exact mem_image_of_mem x hyS
  refine ⟨X, hX, ?_, hfin⟩
  intro hXA
  exact hX (by simpa using hfin X hXA)


theorem boundingNumber_le_almostDisjointnessNumber :
    BoundingAndDominating.boundingNumber ≤ almostDisjointnessNumber := by
  obtain ⟨A, hA, hcard⟩ := almostDisjointnessNumber_spec.1
  rw [← hcard]
  by_contra h
  obtain ⟨X, hX, _, hf⟩ := small_almost_disjoint_extension A hA.2.1 hA.1 (lt_of_not_ge h)
  obtain ⟨S, hS, hi⟩ := (AlmostDisjoint.maximal_iff_infinite_intersection A hA.2.1).mp hA.2 X hX
  exact hi (hf S hS)

theorem pseudointersectionNumber_le_ultrafilterNumber :
    pseudointersectionNumber ≤ ultrafilterNumber := by
  obtain ⟨B, hB, hcard⟩ := ultrafilterNumber_spec.1
  rw [← hcard]
  exact pseudointersectionNumber_spec.2.1 B (free_base_obstruction B hB)

theorem numbers_of_ch (h : (continuum : Cardinal.{0}) = ℵ₁) :
    pseudointersectionNumber = ℵ₁ ∧ almostDisjointnessNumber = ℵ₁ ∧
      ultrafilterNumber = ℵ₁ := by
  obtain ⟨hp, ha, hu⟩ := bounds
  rw [h] at hp ha hu
  exact ⟨le_antisymm hp.2 hp.1, le_antisymm ha.2 ha.1, le_antisymm hu.2 hu.1⟩

end Lemmatheca.SetTheory.SmallFamilies
