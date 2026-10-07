import Lemmatheca.SetTheory.FiniteErrors
import Lemmatheca.SetTheory.Cofinality
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Ordinal.FundamentalSequence

/-! Bounding and dominating families for eventual comparison on `ℕ → ℕ`.

All family comparisons below explicitly use `Filter.atTop`. The ordinary order
on functions is pointwise and is not used to define the two cardinal invariants.
The invariants are infima of the cardinalities of witnessing family subtypes;
their specification theorems assert attainment and the intended minimum property.
-/

namespace Lemmatheca.SetTheory.BoundingAndDominating

open Set Filter Cardinal
universe u

def IsBounded (B : Set (ℕ → ℕ)) : Prop :=
  ∃ g : ℕ → ℕ, ∀ f ∈ B, f ≤ᶠ[atTop] g

def IsUnbounded (B : Set (ℕ → ℕ)) : Prop :=
  ¬ IsBounded B

def IsDominating (D : Set (ℕ → ℕ)) : Prop :=
  ∀ f : ℕ → ℕ, ∃ g ∈ D, f ≤ᶠ[atTop] g

noncomputable def boundingNumber : Cardinal :=
  ⨅ B : {B : Set (ℕ → ℕ) // IsUnbounded B}, Cardinal.mk B.val

noncomputable def dominatingNumber : Cardinal :=
  ⨅ D : {D : Set (ℕ → ℕ) // IsDominating D}, Cardinal.mk D.val

theorem isUnbounded_iff (B : Set (ℕ → ℕ)) :
    IsUnbounded B ↔ ∀ g : ℕ → ℕ, ∃ f ∈ B, ¬ f ≤ᶠ[atTop] g := by
  classical
  simp only [IsUnbounded, IsBounded, not_exists, not_forall, exists_prop]

theorem empty_family :
    IsBounded (∅ : Set (ℕ → ℕ)) ∧ ¬ IsDominating (∅ : Set (ℕ → ℕ)) := by
  simp [IsBounded, IsDominating]

theorem dominating_isUnbounded (D : Set (ℕ → ℕ)) (hD : IsDominating D) :
    IsUnbounded D := by
  rintro ⟨g, hg⟩
  obtain ⟨f, hf, hgf⟩ := hD (fun n => g n + 1)
  exact FiniteErrors.successor_not_eventuallyLE g (hgf.trans (hg f hf))

theorem univ_family :
    IsDominating (Set.univ : Set (ℕ → ℕ)) ∧
      IsUnbounded (Set.univ : Set (ℕ → ℕ)) := by
  have hD : IsDominating (Set.univ : Set (ℕ → ℕ)) :=
    fun f => ⟨f, Set.mem_univ _, Filter.Eventually.of_forall fun _ => le_rfl⟩
  exact ⟨hD, dominating_isUnbounded _ hD⟩

theorem strict_comparison_conventions (B : Set (ℕ → ℕ)) :
    (IsBounded B ↔ ∃ g : ℕ → ℕ, ∀ f ∈ B, FiniteErrors.EventuallyLT f g) ∧
    (∀ g : ℕ → ℕ, (∀ f ∈ B, f ≤ᶠ[atTop] g) →
      ∀ f ∈ B, FiniteErrors.EventuallyLT f (fun n => g n + 1)) ∧
    (IsUnbounded B ↔ ∀ g : ℕ → ℕ, ∃ f ∈ B, ¬ FiniteErrors.EventuallyLT f g) ∧
    (IsDominating B ↔ ∀ f : ℕ → ℕ, ∃ g ∈ B, FiniteErrors.EventuallyLT f g) := by
  classical
  have hbound : IsBounded B ↔ ∃ g : ℕ → ℕ, ∀ f ∈ B, FiniteErrors.EventuallyLT f g := by
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨fun n => g n + 1, fun f hf => (hg f hf).mono fun n hn => Nat.lt_succ_of_le hn⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, fun f hf => (hg f hf).mono fun _ hn => hn.le⟩
  refine ⟨hbound, ?_, ?_, ?_⟩
  · exact fun g hg f hf => (hg f hf).mono fun n hn => Nat.lt_succ_of_le hn
  · rw [IsUnbounded, hbound]
    simp only [not_exists, not_forall, exists_prop]
  · constructor
    · intro hD f
      obtain ⟨g, hg, hfg⟩ := hD (fun n => f n + 1)
      exact ⟨g, hg, hfg.mono fun _ hn => Nat.lt_of_succ_le hn⟩
    · intro hD f
      obtain ⟨g, hg, hfg⟩ := hD f
      exact ⟨g, hg, hfg.mono fun _ hn => hn.le⟩

theorem boundingNumber_spec :
    (∃ B : Set (ℕ → ℕ), IsUnbounded B ∧ Cardinal.mk B = boundingNumber) ∧
    (∀ B : Set (ℕ → ℕ), IsUnbounded B → boundingNumber ≤ Cardinal.mk B) ∧
    (∀ B : Set (ℕ → ℕ), Cardinal.mk B < boundingNumber → IsBounded B) := by
  classical
  have : Nonempty {B : Set (ℕ → ℕ) // IsUnbounded B} := ⟨⟨Set.univ, univ_family.2⟩⟩
  obtain ⟨B, hB⟩ := ciInf_mem (fun B : {B : Set (ℕ → ℕ) // IsUnbounded B} => Cardinal.mk B.val)
  have hmin (B : Set (ℕ → ℕ)) (hB : IsUnbounded B) : boundingNumber ≤ Cardinal.mk B :=
    ciInf_le' (fun B : {B : Set (ℕ → ℕ) // IsUnbounded B} => Cardinal.mk B.val) ⟨B, hB⟩
  refine ⟨⟨B.val, B.property, hB⟩, hmin, ?_⟩
  intro B hB
  by_contra h
  exact hB.not_ge (hmin B h)

theorem dominatingNumber_spec :
    (∃ D : Set (ℕ → ℕ), IsDominating D ∧ Cardinal.mk D = dominatingNumber) ∧
    (∀ D : Set (ℕ → ℕ), IsDominating D → dominatingNumber ≤ Cardinal.mk D) ∧
    (∀ D : Set (ℕ → ℕ), Cardinal.mk D < dominatingNumber → ¬ IsDominating D) := by
  classical
  have : Nonempty {D : Set (ℕ → ℕ) // IsDominating D} := ⟨⟨Set.univ, univ_family.1⟩⟩
  obtain ⟨D, hD⟩ := ciInf_mem (fun D : {D : Set (ℕ → ℕ) // IsDominating D} => Cardinal.mk D.val)
  have hmin (D : Set (ℕ → ℕ)) (hD : IsDominating D) : dominatingNumber ≤ Cardinal.mk D :=
    ciInf_le' (fun D : {D : Set (ℕ → ℕ) // IsDominating D} => Cardinal.mk D.val) ⟨D, hD⟩
  refine ⟨⟨D.val, D.property, hD⟩, hmin, ?_⟩
  intro D hD h
  exact hD.not_ge (hmin D h)

theorem aleph_one_le_boundingNumber :
    Cardinal.aleph 1 ≤ boundingNumber := by
  obtain ⟨B, hB, hcard⟩ := boundingNumber_spec.1
  rw [← hcard]
  by_contra h
  have hcount := Cardinal.le_aleph0_iff_set_countable.mp
    (Cardinal.lt_aleph_one_iff.mp (lt_of_not_ge h))
  obtain ⟨g, _, hg⟩ := FiniteErrors.countable_eventual_bound B hcount
  exact hB ⟨g, fun f hf => (hg f hf).mono fun _ hn => hn.le⟩

theorem boundingNumber_le_dominatingNumber :
    boundingNumber ≤ dominatingNumber := by
  obtain ⟨D, hD, hcard⟩ := dominatingNumber_spec.1
  rw [← hcard]
  exact boundingNumber_spec.2.1 D (dominating_isUnbounded D hD)

theorem dominatingNumber_le_continuum :
    dominatingNumber ≤ Cardinal.continuum := by
  have h := dominatingNumber_spec.2.1 Set.univ univ_family.1
  simpa [Cardinal.mk_univ, Cardinal.mk_arrow, Cardinal.mk_nat,
    Cardinal.aleph0_power_aleph0] using h

theorem bounded_iUnion {ι : Type} (B : ι → Set (ℕ → ℕ))
    (hι : Cardinal.mk ι < boundingNumber) (hB : ∀ i, IsBounded (B i)) :
    IsBounded (⋃ i, B i) := by
  classical
  choose g hg using hB
  have hsmall : Cardinal.mk (Set.range g) < boundingNumber :=
    (Cardinal.mk_range_le (f := g)).trans_lt hι
  obtain ⟨h, hh⟩ := boundingNumber_spec.2.2 (Set.range g) hsmall
  refine ⟨h, ?_⟩
  intro f hf
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hf
  exact (hg i f hi).trans (hh (g i) ⟨i, rfl⟩)

theorem cofinal_cover {α : Type u} (X : Set α) (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) (hX : Cardinal.mk X = κ) :
    ∃ pieces : κ.ord.cof.ord.ToType → Set α,
      (∀ i, pieces i ⊆ X ∧ Cardinal.mk (pieces i) < κ) ∧
      (⋃ i, pieces i) = X := by
  classical
  obtain ⟨e⟩ : Nonempty (X ≃ κ.ord.ToType) := Cardinal.eq.mp (by simpa using hX)
  obtain ⟨f, hf⟩ := Ordinal.exists_isFundamentalSeq (o := κ.ord) rfl
  let endpoint (i : κ.ord.cof.ord.ToType) : κ.ord.ToType :=
    Ordinal.ToType.mk (f i.toOrd)
  let pieces (i : κ.ord.cof.ord.ToType) : Set α :=
    (fun j : κ.ord.ToType => (e.symm j).val) '' Set.Iio (endpoint i)
  refine ⟨pieces, ?_, ?_⟩
  · intro i
    refine ⟨?_, (Cardinal.mk_image_le).trans_lt ?_⟩
    · rintro x ⟨j, _, rfl⟩
      exact (e.symm j).property
    · simpa only [Cardinal.mk_toType, Cardinal.card_ord] using
        (Cardinal.mk_Iio_lt (endpoint i) (by simp [Cardinal.mk_toType]))
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, j, hj, rfl⟩ := Set.mem_iUnion.mp hx
      exact (e.symm j).property
    · intro x hx
      let j := e ⟨x, hx⟩
      have hnext : j.toOrd.val + 1 < κ.ord := by
        simpa using (Cardinal.isSuccLimit_ord hκ).succ_lt j.toOrd.property
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hf.isCofinal_range ⟨j.toOrd.val + 1, hnext⟩
      refine Set.mem_iUnion.mpr ⟨Ordinal.ToType.mk i, j, ?_, ?_⟩
      · apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
        change j.toOrd.val < (Ordinal.ToType.mk.symm (endpoint (Ordinal.ToType.mk i))).val
        simpa only [endpoint, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply] using
          (lt_add_one j.toOrd.val).trans_le hi
      · exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)

theorem boundingNumber_isRegular :
    boundingNumber.IsRegular := by
  have hinf : Cardinal.aleph0 ≤ boundingNumber :=
    Cardinal.aleph0_lt_aleph_one.le.trans aleph_one_le_boundingNumber
  refine ⟨hinf, le_of_not_gt ?_⟩
  intro hcof
  obtain ⟨B, hB, hcard⟩ := boundingNumber_spec.1
  obtain ⟨pieces, hp, hcover⟩ := cofinal_cover B boundingNumber hinf hcard
  have hi : Cardinal.mk boundingNumber.ord.cof.ord.ToType < boundingNumber :=
    by simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hcof
  have hbound := bounded_iUnion pieces hi
    (fun i => boundingNumber_spec.2.2 _ (hp i).2)
  exact hB (hcover ▸ hbound)

theorem boundingNumber_le_cofinality_dominatingNumber :
    boundingNumber ≤ dominatingNumber.ord.cof := by
  classical
  by_contra h
  have hcof : dominatingNumber.ord.cof < boundingNumber := lt_of_not_ge h
  have hinf : Cardinal.aleph0 ≤ dominatingNumber :=
    Cardinal.aleph0_lt_aleph_one.le.trans
      (aleph_one_le_boundingNumber.trans boundingNumber_le_dominatingNumber)
  obtain ⟨D, hD, hcard⟩ := dominatingNumber_spec.1
  obtain ⟨pieces, hp, hcover⟩ := cofinal_cover D dominatingNumber hinf hcard
  have hbad : ∀ i, ∃ f : ℕ → ℕ, ∀ g ∈ pieces i, ¬ f ≤ᶠ[atTop] g := by
    intro i
    have hh := dominatingNumber_spec.2.2 _ (hp i).2
    simpa only [IsDominating, not_forall, not_exists, not_and] using hh
  choose f hf using hbad
  have hsmall : Cardinal.mk (Set.range f) < boundingNumber :=
    Cardinal.mk_range_le.trans_lt (by
      simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hcof)
  obtain ⟨g, hg⟩ := boundingNumber_spec.2.2 _ hsmall
  obtain ⟨h, hh, hgh⟩ := hD g
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover.symm ▸ hh)
  exact hf i h hi ((hg (f i) ⟨i, rfl⟩).trans hgh)

theorem numbers_of_continuum_hypothesis
    (hCH : Cardinal.continuum = Cardinal.aleph 1) :
    boundingNumber = Cardinal.aleph 1 ∧ dominatingNumber = Cardinal.aleph 1 := by
  have hd : dominatingNumber ≤ Cardinal.aleph 1 := by
    have hCH0 : Cardinal.continuum.{0} = Cardinal.aleph.{0} 1 := by
      apply Cardinal.lift_inj.mp
      simpa using hCH
    exact dominatingNumber_le_continuum.trans hCH0.le
  have hb : boundingNumber ≤ Cardinal.aleph 1 := boundingNumber_le_dominatingNumber.trans hd
  exact ⟨hb.antisymm aleph_one_le_boundingNumber,
    hd.antisymm (aleph_one_le_boundingNumber.trans boundingNumber_le_dominatingNumber)⟩

end Lemmatheca.SetTheory.BoundingAndDominating
