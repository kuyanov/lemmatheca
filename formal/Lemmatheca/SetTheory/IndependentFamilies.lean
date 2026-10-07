import Lemmatheca.SetTheory.AlmostDisjoint
import Lemmatheca.SetTheory.FiltersAndUltrafilters
import Mathlib.Order.Filter.Ultrafilter.Cardinality
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Preimage

/-! Independent families of subsets, finite-record coding, and free ultrafilters.

Finite subfamilies are represented by finsets; `cell` takes the empty
intersection to be the whole carrier. Independence requires infinite cells.
The nonprincipal-ultrafilter subtype uses the existing filter predicate.
-/

namespace Lemmatheca.SetTheory.IndependentFamilies

open Set Filter Cardinal
open scoped Classical
universe u

def cell {α : Type u} (E H : Finset (Set α)) : Set α :=
  {x | (∀ A ∈ E, x ∈ A) ∧ ∀ B ∈ H, x ∉ B}

def IsIndependent {α : Type u} (A : Set (Set α)) : Prop :=
  ∀ E H : Finset (Set α), (↑E : Set (Set α)) ⊆ A →
    (↑H : Set (Set α)) ⊆ A → Disjoint E H → (cell E H).Infinite

theorem singleton_iff {α : Type u} (A : Set α) :
    IsIndependent {A} ↔ A.Infinite ∧ Aᶜ.Infinite := by
  constructor
  · intro h
    have h₁ := h {A} ∅ (by simp) (by simp) (by simp)
    have h₂ := h ∅ {A} (by simp) (by simp) (by simp)
    simpa [cell, Set.compl_def] using And.intro h₁ h₂
  · rintro ⟨hA, hc⟩ E H hE hH hd
    by_cases hn : A ∈ H
    · apply hc.mono
      intro x hx
      refine ⟨?_, ?_⟩
      · intro B hB
        have heq : B = A := by simpa using hE hB
        subst B
        exact False.elim ((Finset.disjoint_left.mp hd hB) hn)
      · intro B hB
        have heq : B = A := by simpa using hH hB
        simpa [heq] using hx
    · apply hA.mono
      intro x hx
      refine ⟨?_, ?_⟩
      · intro B hB
        have heq : B = A := by simpa using hE hB
        simpa [heq] using hx
      · intro B hB
        have heq : B = A := by simpa using hH hB
        exact False.elim (hn (heq ▸ hB))

theorem pair_iff {α : Type u} (A B : Set α) (hne : A ≠ B) :
    IsIndependent {A, B} ↔
      (A ∩ B).Infinite ∧ (A \ B).Infinite ∧ (B \ A).Infinite ∧ (A ∪ B)ᶜ.Infinite := by
  constructor
  · intro h
    have h₁ := h {A, B} ∅ (by simp) (by simp) (by simp)
    have h₂ := h {A} {B} (by simp) (by simp) (by simp [hne])
    have h₃ := h {B} {A} (by simp) (by simp) (by simp [hne.symm])
    have h₄ := h ∅ {A, B} (by simp) (by simp) (by simp)
    have he₁ : cell ({A, B} : Finset (Set α)) ∅ = A ∩ B := by ext x; simp [cell]
    have he₂ : cell ({A} : Finset (Set α)) {B} = A \ B := by ext x; simp [cell]
    have he₃ : cell ({B} : Finset (Set α)) {A} = B \ A := by ext x; simp [cell]
    have he₄ : cell (∅ : Finset (Set α)) {A, B} = (A ∪ B)ᶜ := by ext x; simp [cell]
    rw [he₁] at h₁; rw [he₂] at h₂; rw [he₃] at h₃; rw [he₄] at h₄
    exact ⟨h₁, h₂, h₃, h₄⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩ E H hE hH hd
    let C := (if A ∈ H then Aᶜ else A) ∩ (if B ∈ H then Bᶜ else B)
    have hC : C.Infinite := by
      by_cases ha : A ∈ H <;> by_cases hb : B ∈ H
      · simpa [C, ha, hb, Set.compl_union] using h₄
      · simpa [C, ha, hb, Set.sdiff_eq, inter_comm] using h₃
      · simpa [C, ha, hb, Set.sdiff_eq] using h₂
      · simpa [C, ha, hb] using h₁
    apply hC.mono
    intro x hx
    change (x ∈ if A ∈ H then Aᶜ else A) ∧ (x ∈ if B ∈ H then Bᶜ else B) at hx
    constructor
    · intro S hS
      have hcases : S = A ∨ S = B := by simpa using hE hS
      rcases hcases with rfl | rfl
      · simpa [Finset.disjoint_left.mp hd hS] using hx.1
      · simpa [Finset.disjoint_left.mp hd hS] using hx.2
    · intro S hS
      have hcases : S = A ∨ S = B := by simpa using hH hS
      rcases hcases with rfl | rfl
      · simpa [hS] using hx.1
      · simpa [hS] using hx.2

theorem complement_pair_not_independent {α : Type u} (A : Set α) :
    ¬ IsIndependent {A, Aᶜ} := by
  intro h
  have hi := h {A, Aᶜ} ∅ (by simp) (by simp) (by simp)
  have he : cell ({A, Aᶜ} : Finset (Set α)) ∅ = ∅ := by
    ext x; simp [cell]
  rw [he] at hi
  exact hi Set.finite_empty

abbrev Records := Finset ℕ × Finset (Finset ℕ)

theorem singleton_records_injective :
    Function.Injective (fun n : ℕ => (({n}, ∅) : Records)) := by
  intro n m h
  simpa using congrArg Prod.fst h

theorem records_countably_infinite : Nonempty (ℕ ≃ Records) := by
  have : Infinite Records := Infinite.of_injective _ singleton_records_injective
  exact nonempty_equiv_of_countable

def traceSet (A : Set ℕ) : Set Records :=
  {p | p.1.filter (· ∈ A) ∈ p.2}

theorem singleton_trace_record (A : Set ℕ) (n : ℕ) :
    (({n}, {{n}}) : Records) ∈ traceSet A ↔ n ∈ A := by
  by_cases hn : n ∈ A <;> simp [traceSet, hn]

theorem traceSet_injective : Function.Injective traceSet := by
  intro A B h
  ext n
  rw [← singleton_trace_record A n, h, singleton_trace_record B n]

theorem finite_trace_separation (E H : Finset (Set ℕ)) (hd : Disjoint E H) :
    ∃ F₀ : Finset ℕ, ∀ F : Finset ℕ, F₀ ⊆ F →
      ∀ A ∈ E, ∀ B ∈ H, F.filter (· ∈ A) ≠ F.filter (· ∈ B) := by
  classical
  let P := {A // A ∈ E} × {B // B ∈ H}
  have hex : ∀ p : P, ∃ n : ℕ,
      (n ∈ p.1.val ∧ n ∉ p.2.val) ∨ (n ∈ p.2.val ∧ n ∉ p.1.val) := by
    intro p
    have hne : p.1.val ≠ p.2.val := by
      intro heq
      exact (Finset.disjoint_left.mp hd p.1.property) (heq ▸ p.2.property)
    exact Set.symmDiff_nonempty.mpr hne
  choose w hw using hex
  refine ⟨Finset.univ.image w, ?_⟩
  intro F hF A hA B hB heq
  let p : P := (⟨A, hA⟩, ⟨B, hB⟩)
  have hnF : w p ∈ F := hF (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
  have he : w p ∈ F.filter (· ∈ A) ↔ w p ∈ F.filter (· ∈ B) := by rw [heq]
  simp only [Finset.mem_filter, hnF, true_and] at he
  have hh := hw p
  change (w p ∈ A ∧ w p ∉ B) ∨ (w p ∈ B ∧ w p ∉ A) at hh
  tauto

theorem trace_family_independent : IsIndependent (range traceSet) := by
  classical
  intro E H hE hH hd
  let E' := E.preimage traceSet traceSet_injective.injOn
  let H' := H.preimage traceSet traceSet_injective.injOn
  have hd' : Disjoint E' H' := Finset.disjoint_preimage hd
  obtain ⟨F₀, hF₀⟩ := finite_trace_separation E' H' hd'
  let M := F₀.sup id + 1
  let F := fun n : ℕ => insert (M + n) F₀
  let recordFn : ℕ → Records := fun n : ℕ => (F n, E'.image (fun A => (F n).filter (· ∈ A)))
  have hnot : ∀ n : ℕ, M + n ∉ F₀ := by
    intro n hn
    have hh := Finset.le_sup (f := id) hn
    dsimp [M] at *
    omega
  have hinj : Function.Injective recordFn := by
    intro n m heq
    have hf : F n = F m := congrArg Prod.fst heq
    have hn : M + n ∈ F m := hf ▸ (Finset.mem_insert_self _ _)
    rcases Finset.mem_insert.mp hn with hn | hn
    · omega
    · exact False.elim (hnot n hn)
  refine Set.infinite_of_injective_forall_mem hinj ?_
  intro n
  constructor
  · intro S hS
    obtain ⟨A, rfl⟩ := hE hS
    change (F n).filter (· ∈ A) ∈ E'.image (fun A => (F n).filter (· ∈ A))
    exact Finset.mem_image_of_mem _ (Finset.mem_preimage.mpr hS)
  · intro S hS
    obtain ⟨B, rfl⟩ := hH hS
    change (F n).filter (· ∈ B) ∉ E'.image (fun A => (F n).filter (· ∈ A))
    intro hb
    obtain ⟨A, hA, hab⟩ := Finset.mem_image.mp hb
    exact hF₀ (F n) (Finset.subset_insert _ _) A hA B
      (Finset.mem_preimage.mpr hS) hab

def pulledTrace (e : ℕ ≃ Records) (A : Set ℕ) : Set ℕ := e ⁻¹' traceSet A

theorem pulledTrace_family (e : ℕ ≃ Records) :
    Function.Injective (pulledTrace e) ∧ IsIndependent (range (pulledTrace e)) ∧
      #(range (pulledTrace e)) = continuum := by
  classical
  have hi : Function.Injective (pulledTrace e) := by
    intro A B h
    apply traceSet_injective
    ext p
    have hh := congrArg (fun S : Set ℕ => e.symm p ∈ S) h
    simpa [pulledTrace] using hh
  refine ⟨hi, ?_, ?_⟩
  · intro E H hE hH hd
    let E' := E.preimage (pulledTrace e) hi.injOn
    let H' := H.preimage (pulledTrace e) hi.injOn
    have hd' : Disjoint E' H' := Finset.disjoint_preimage hd
    have hd'' : Disjoint (E'.image traceSet) (H'.image traceSet) :=
      (Finset.disjoint_image traceSet_injective).mpr hd'
    have he : (↑(E'.image traceSet) : Set (Set Records)) ⊆ range traceSet := by
      intro S hS
      obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hS
      exact mem_range_self A
    have hh : (↑(H'.image traceSet) : Set (Set Records)) ⊆ range traceSet := by
      intro S hS
      obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hS
      exact mem_range_self A
    have hf := trace_family_independent (E'.image traceSet) (H'.image traceSet) he hh hd''
    have hp : (e ⁻¹' cell (E'.image traceSet) (H'.image traceSet)).Infinite :=
      hf.preimage (by intro p _; exact ⟨e.symm p, e.apply_symm_apply p⟩)
    apply hp.mono
    intro n hn
    constructor
    · intro S hS
      obtain ⟨A, rfl⟩ := hE hS
      change e n ∈ traceSet A
      exact hn.1 _ (Finset.mem_image_of_mem traceSet (Finset.mem_preimage.mpr hS))
    · intro S hS
      obtain ⟨A, rfl⟩ := hH hS
      change e n ∉ traceSet A
      exact hn.2 _ (Finset.mem_image_of_mem traceSet (Finset.mem_preimage.mpr hS))
  · rw [Cardinal.mk_range_eq _ hi, Cardinal.mk_set, Cardinal.mk_nat]
    rfl

theorem exists_continuum_independent_family :
    ∃ A : Set (Set ℕ), IsIndependent A ∧ #A = continuum := by
  obtain ⟨e⟩ := records_countably_infinite
  exact ⟨range (pulledTrace e), (pulledTrace_family e).2⟩

def sideChoices {α : Type u} (A : Set (Set α)) (ε : A → Bool) : Set (Set α) :=
  {S | (∃ a : A, (ε a = true ∧ S = a.val) ∨ (ε a = false ∧ S = a.valᶜ)) ∨
    Sᶜ.Finite}

theorem sideChoices_finite_intersections_infinite {α : Type u} (A : Set (Set α))
    (hA : IsIndependent A) (ε : A → Bool) (T : Finset (Set α))
    (hT : (↑T : Set (Set α)) ⊆ sideChoices A ε) :
    (⋂₀ (↑T : Set (Set α))).Infinite := by
  classical
  let E := T.filter (fun S => ∃ a : A, ε a = true ∧ S = a.val)
  let H := (T.image (fun S => Sᶜ)).filter
    (fun S => ∃ a : A, ε a = false ∧ S = a.val)
  let C := T.filter (fun S => Sᶜ.Finite)
  have hEA : (↑E : Set (Set α)) ⊆ A := by
    intro S hS
    obtain ⟨a, _, rfl⟩ := (Finset.mem_filter.mp hS).2
    exact a.property
  have hHA : (↑H : Set (Set α)) ⊆ A := by
    intro S hS
    obtain ⟨a, _, rfl⟩ := (Finset.mem_filter.mp hS).2
    exact a.property
  have hdis : Disjoint E H := by
    apply Finset.disjoint_left.mpr
    intro S hSE hSH
    obtain ⟨a, ha, hSa⟩ := (Finset.mem_filter.mp hSE).2
    obtain ⟨b, hb, hSb⟩ := (Finset.mem_filter.mp hSH).2
    have hab : a = b := Subtype.ext (hSa.symm.trans hSb)
    have : ε a = false := hab ▸ hb
    simp [ha] at this
  let K : Set α := ⋃ S ∈ (↑C : Set (Set α)), Sᶜ
  have hK : K.Finite := C.finite_toSet.biUnion fun S hS => (Finset.mem_filter.mp hS).2
  apply ((hA E H hEA hHA hdis).sdiff hK).mono
  intro x hx
  simp only [Set.mem_sInter]
  intro S hS
  rcases hT hS with ⟨a, hpos | hneg⟩ | hcof
  · obtain ⟨ha, rfl⟩ := hpos
    exact hx.1.1 a.val (Finset.mem_filter.mpr ⟨hS, a, ha, rfl⟩)
  · obtain ⟨ha, rfl⟩ := hneg
    have hmem : a.val ∈ H := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨a.valᶜ, hS, compl_compl _⟩, a, ha, rfl⟩
    have hn := hx.1.2 a.val hmem
    simpa using hn
  · have hn : x ∉ Sᶜ := by
      intro hh
      exact hx.2 (Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hS, hcof⟩, hh⟩⟩)
    simpa using hn


theorem sideChoices_finite_intersections {α : Type u} (A : Set (Set α))
    (hA : IsIndependent A) (ε : A → Bool) :
    FiltersAndUltrafilters.HasFiniteIntersectionProperty (sideChoices A ε) := by
  intro t ht hfin
  have hh := sideChoices_finite_intersections_infinite A hA ε hfin.toFinset
    (by simpa using ht)
  simpa using hh.nonempty


theorem sideChoices_ultrafilter {α : Type u} [Infinite α] (A : Set (Set α))
    (hA : IsIndependent A) (ε : A → Bool) :
    ∃ U : Ultrafilter α, sideChoices A ε ⊆ U.sets ∧
      ¬ FiltersAndUltrafilters.IsPrincipal (U : Filter α) := by
  obtain ⟨U, hU⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty (sideChoices A ε)
    (fun T hT => (sideChoices_finite_intersections_infinite A hA ε T hT).nonempty)
  refine ⟨U, hU, ?_⟩
  apply (Lemmatheca.SetTheory.FiltersAndUltrafilters.nonprincipal_iff_cofinite U).mpr
  intro S hS
  exact hU (Or.inr (Filter.mem_cofinite.mp hS))


theorem distinct_assignments_no_common_extension {α : Type u} (A : Set (Set α))
    (ε δ : A → Bool) (hne : ε ≠ δ) :
    ¬ ∃ U : Ultrafilter α, sideChoices A ε ⊆ U.sets ∧ sideChoices A δ ⊆ U.sets := by
  classical
  rintro ⟨U, hε, hδ⟩
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  cases he : ε a <;> cases hd : δ a
  · exact ha (he.trans hd.symm)
  · have hc : a.valᶜ ∈ U := hε (Or.inl ⟨a, Or.inr ⟨he, rfl⟩⟩)
    have hm : a.val ∈ U := hδ (Or.inl ⟨a, Or.inl ⟨hd, rfl⟩⟩)
    exact (U.compl_mem_iff_notMem.mp hc) hm
  · have hm : a.val ∈ U := hε (Or.inl ⟨a, Or.inl ⟨he, rfl⟩⟩)
    have hc : a.valᶜ ∈ U := hδ (Or.inl ⟨a, Or.inr ⟨hd, rfl⟩⟩)
    exact (U.compl_mem_iff_notMem.mp hc) hm
  · exact ha (he.trans hd.symm)


theorem assignment_ultrafilter_injection {α : Type u} [Infinite α]
    (A : Set (Set α)) (hA : IsIndependent A) :
    ∃ f : (A → Bool) → {U : Ultrafilter α // ¬ FiltersAndUltrafilters.IsPrincipal (U : Filter α)},
      Function.Injective f ∧ ∀ ε, sideChoices A ε ⊆ (f ε).val.sets := by
  classical
  choose U hU hn using fun ε => sideChoices_ultrafilter A hA ε
  let f ε := (⟨U ε, hn ε⟩ : {U : Ultrafilter α //
    ¬ Lemmatheca.SetTheory.FiltersAndUltrafilters.IsPrincipal (U : Filter α)})
  refine ⟨f, ?_, hU⟩
  intro ε δ heq
  by_contra hne
  have hv : U ε = U δ := congrArg Subtype.val heq
  exact distinct_assignments_no_common_extension A ε δ hne
    ⟨U ε, hU ε, hv.symm ▸ hU δ⟩


theorem nonprincipal_ultrafilter_cardinality :
    #{U : Ultrafilter ℕ // ¬ FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ)} =
      2 ^ continuum := by
  classical
  apply le_antisymm
  · have h := Cardinal.mk_subtype_le
      (fun U : Ultrafilter ℕ => ¬ Lemmatheca.SetTheory.FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ))
    simpa using h.trans_eq (Cardinal.mk_ultrafilter_of_infinite (α := ℕ))
  · obtain ⟨A, hA, hcard⟩ := exists_continuum_independent_family
    obtain ⟨f, hf, _⟩ := assignment_ultrafilter_injection A hA
    have hh := Cardinal.mk_le_of_injective hf
    simpa [Cardinal.mk_arrow, Cardinal.mk_bool, hcard] using hh


theorem almost_disjoint_not_independent (A : Set (Set ℕ))
    (hA : AlmostDisjoint.IsAlmostDisjoint A) (hpair : ∃ S ∈ A, ∃ T ∈ A, S ≠ T) :
    ¬ IsIndependent A := by
  obtain ⟨S, hS, T, hT, hne⟩ := hpair
  intro h
  have hi := h {S, T} ∅ (by simp only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff]; exact ⟨hS, hT⟩) (by simp) (by simp)
  have he : cell ({S, T} : Finset (Set ℕ)) ∅ = S ∩ T := by ext x; simp [cell]
  rw [he] at hi
  exact hi (hA.2 hS hT hne)

theorem finite_carrier_not_independent {α : Type u} [Finite α] (A : Set (Set α)) :
    ¬ IsIndependent A := by
  intro h
  have hi := h ∅ ∅ (by simp) (by simp) (by simp)
  have he : cell (∅ : Finset (Set α)) ∅ = Set.univ := by ext x; simp [cell]
  rw [he] at hi
  exact hi Set.finite_univ

end Lemmatheca.SetTheory.IndependentFamilies
