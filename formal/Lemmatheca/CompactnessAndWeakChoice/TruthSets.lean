import Lemmatheca.BooleanAlgebras.BooleanAlgebras
import Lemmatheca.FiltersAndUltrafilters.FiltersAndUltrafilters
import Lemmatheca.PropositionalCompactness.PropositionalCompactness

/-! Witness-level constructions; the claimed ZF derivability/strength is not encoded here. -/
namespace Lemmatheca.SetTheory.CompactnessAndWeakChoice
open Set Filter Order
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.PropositionalCompactness
open Lemmatheca.SetTheory.BooleanAlgebras
universe u v
variable {α : Type u}

def truthSet (A : PropFormula α) : Set (Valuation α) := {v | Satisfies v A}

theorem all_valuations_nonempty : Nonempty (Valuation α) := by
  exact ⟨fun _ => false⟩

theorem truthSet_laws (A B : PropFormula α) :
    truthSet (PropFormula.falsum : PropFormula α) = ∅ ∧
    truthSet (verum : PropFormula α) = Set.univ ∧
    truthSet (.neg A) = (truthSet A)ᶜ ∧
    truthSet (.conj A B) = truthSet A ∩ truthSet B ∧
    truthSet (.disj A B) = truthSet A ∪ truthSet B ∧
    truthSet (.impl A B) = (truthSet A)ᶜ ∪ truthSet B := by
  classical
  repeat' constructor
  all_goals (ext v; simp [truthSet, Satisfies, eval, verum, Bool.not_eq_true])

def truthSetFilter (Γ : Theory α) : Filter (Valuation α) :=
  Filter.generate (truthSet '' Γ)

theorem truthSetFilter_mem [DecidableEq α] (Γ : Theory α) (Y : Set (Valuation α)) :
    Y ∈ truthSetFilter Γ ↔
      ∃ Δ : Finset (PropFormula α), (↑Δ : Theory α) ⊆ Γ ∧
        (⋂ A ∈ Δ, truthSet A) ⊆ Y := by
  classical
  constructor
  · intro h
    change Filter.GenerateSets (truthSet '' Γ) Y at h
    induction h with
    | @basic X hX =>
      obtain ⟨A,hA,rfl⟩ := hX
      refine ⟨{A}, by simpa, ?_⟩
      simp
    | univ => exact ⟨∅, by simp, by simp⟩
    | @superset X Z hXZ hXZsub ih =>
      obtain ⟨Δ,hΔ,hsub⟩ := ih
      exact ⟨Δ,hΔ,hsub.trans hXZsub⟩
    | @inter X Z hX hZ ihX ihZ =>
      obtain ⟨Δ,hΔ,hsubΔ⟩ := ihX
      obtain ⟨E,hE,hsubE⟩ := ihZ
      refine ⟨Δ ∪ E, by simpa using Set.union_subset hΔ hE, ?_⟩
      intro v hv
      have hv' : ∀ A ∈ Δ ∪ E, v ∈ truthSet A := by simpa using hv
      exact ⟨hsubΔ (by simp only [Set.mem_iInter]; exact fun A hA => hv' A (Finset.mem_union_left E hA)),
        hsubE (by simp only [Set.mem_iInter]; exact fun A hA => hv' A (Finset.mem_union_right Δ hA))⟩
  · rintro ⟨Δ,hΔ,hY⟩
    apply Filter.mem_of_superset _ hY
    apply (Filter.biInter_mem Δ.finite_toSet).mpr
    intro A hA
    exact Filter.mem_generate_of_mem ⟨A,hΔ hA,rfl⟩

theorem truthSetFilter_proper [DecidableEq α] (Γ : Theory α) (hΓ : FiniteSatisfiable Γ) :
    NeBot (truthSetFilter Γ) ∧ ∀ A ∈ Γ, truthSet A ∈ truthSetFilter Γ := by
  classical
  refine ⟨Filter.forall_mem_nonempty_iff_neBot.mp ?_, ?_⟩
  · intro Y hY
    obtain ⟨Δ,hΔ,hsub⟩ := (truthSetFilter_mem Γ Y).mp hY
    obtain ⟨v,hv⟩ := hΓ Δ hΔ
    refine ⟨v,hsub ?_⟩
    simp only [Set.mem_iInter]
    exact hv
  · intro A hA
    exact Filter.mem_generate_of_mem ⟨A,hA,rfl⟩

noncomputable def ultrafilterValuation (U : Ultrafilter (Valuation α)) : Valuation α :=
  by classical exact fun p => decide (truthSet (.atom p) ∈ U)

theorem ultrafilterValuation_truth (U : Ultrafilter (Valuation α)) (A : PropFormula α) :
    Satisfies (ultrafilterValuation U) A ↔ truthSet A ∈ U := by
  classical
  induction A with
  | atom p => simp only [ultrafilterValuation, Satisfies, eval, decide_eq_true_eq]
  | falsum => simp [Satisfies, eval, (truthSet_laws (PropFormula.falsum : PropFormula α) .falsum).1]
  | neg A ih =>
    rw [(truthSet_laws A A).2.2.1, Ultrafilter.compl_mem_iff_notMem, ← ih]
    simp [Satisfies, eval, Bool.not_eq_true]
  | conj A B ihA ihB =>
    rw [(truthSet_laws A B).2.2.2.1]
    have hmem : truthSet A ∩ truthSet B ∈ U ↔ truthSet A ∈ U ∧ truthSet B ∈ U := Filter.inter_mem_iff
    rw [hmem, ← ihA, ← ihB]
    simp [Satisfies, eval]
  | disj A B ihA ihB =>
    rw [(truthSet_laws A B).2.2.2.2.1, Ultrafilter.union_mem_iff, ← ihA, ← ihB]
    simp [Satisfies, eval]
  | impl A B ihA ihB =>
    rw [(truthSet_laws A B).2.2.2.2.2, Ultrafilter.union_mem_iff,
      Ultrafilter.compl_mem_iff_notMem, ← ihA, ← ihB]
    simp [Satisfies, eval, Bool.not_eq_true]

theorem ultrafilterValuation_models (Γ : Theory α) (U : Ultrafilter (Valuation α))
    (hU : (U : Filter (Valuation α)) ≤ truthSetFilter Γ) :
    ModelsTheory (ultrafilterValuation U) Γ := by
  intro A hA
  apply (ultrafilterValuation_truth U A).mpr
  exact hU (Filter.mem_generate_of_mem ⟨A,hA,rfl⟩)

theorem point_valuation (w : Valuation α) :
    ultrafilterValuation (pure w) = w := by
  classical
  funext p
  have h := ultrafilterValuation_truth (pure w) (.atom p)
  simp only [Satisfies, eval, truthSet, Set.mem_ofPred_eq, Ultrafilter.mem_pure] at h
  exact Bool.eq_iff_iff.mpr h

def subsetFilter (F : Filter α) : PFilter (Set α) :=
  (Order.IsPFilter.of_def (F := F.sets)
    ⟨Set.univ,Filter.univ_mem⟩
    (fun A hA B hB => ⟨A ∩ B,Filter.inter_mem hA hB,Set.inter_subset_left,Set.inter_subset_right⟩)
    (fun h hA => Filter.mem_of_superset hA h)).toPFilter

def fromSubsetFilter (F : PFilter (Set α)) : Filter α where
  sets := F
  univ_sets := PFilter.top_mem
  sets_of_superset := fun h hAB => PFilter.mem_of_le hAB h
  inter_sets := fun hA hB => PFilter.inf_mem hA hB

theorem subset_filter_bridge (F : Filter α) :
    (∀ A, A ∈ subsetFilter F ↔ A ∈ F) ∧
    (IsProperFilter (subsetFilter F) ↔ NeBot F) ∧
    fromSubsetFilter (subsetFilter F) = F := by
  refine ⟨fun _ => Iff.rfl, ?_, ?_⟩
  · change (∅ ∉ F) ↔ NeBot F
    exact (not_congr Filter.empty_mem_iff_bot).trans Filter.neBot_iff.symm
  · apply Filter.ext
    intro A
    rfl

theorem subset_ultrafilter_bridge (F : PFilter (Set α)) :
    IsUltrafilter F ↔ ∃ U : Ultrafilter α, ∀ A, A ∈ U ↔ A ∈ F := by
  classical
  constructor
  · intro hF
    have hc := (ultrafilter_characterizations F hF.1).1.mp hF
    let U : Ultrafilter α := Ultrafilter.ofComplNotMemIff (fromSubsetFilter F)
      (fun A => (hc A).symm)
    exact ⟨U,fun _ => Iff.rfl⟩
  · rintro ⟨U,hU⟩
    have hp : IsProperFilter F := by
      intro he
      exact U.empty_notMem ((hU ∅).mpr he)
    apply (ultrafilter_characterizations F hp).1.mpr
    intro A
    rw [← hU A, ← hU Aᶜ]
    exact Ultrafilter.compl_notMem_iff.symm

theorem subset_extension_bridge (F : Filter α) (U : PFilter (Set α))
    (hU : IsUltrafilter U) (hFU : subsetFilter F ≤ U) :
    ∃ V : Ultrafilter α, (∀ A, A ∈ V ↔ A ∈ U) ∧ (V : Filter α) ≤ F := by
  obtain ⟨V,hV⟩ := (subset_ultrafilter_bridge U).mp hU
  refine ⟨V,hV,?_⟩
  intro A hA
  exact (hV A).mpr (hFU hA)

theorem prime_dual {B : Type v} [BooleanAlgebra B] (F : PFilter B) (I : Ideal B)
    (hI : (I : Set B) = dualIdeal F) :
    IsUltrafilter F ↔ I.IsPrime := by
  rw [ultrafilter_dual_maximal F I hI]
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    infer_instance

theorem trivial_no_proper {B : Type v} [BooleanAlgebra B] (h : (⊥ : B) = ⊤) :
    (∀ F : PFilter B, ¬IsProperFilter F) ∧ (∀ I : Ideal B, ¬I.IsProper) := by
  constructor
  · intro F hF
    apply hF
    rw [h]
    exact PFilter.top_mem
  · intro I hI
    exact hI.top_notMem (h ▸ (Ideal.bot_mem I))

theorem cofinite_exclusion (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    (∀ A : Set ℕ, A.Finite → A ∉ U) ∧
    ¬Lemmatheca.SetTheory.FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ) := by
  refine ⟨?_, (Lemmatheca.SetTheory.FiltersAndUltrafilters.nonprincipal_iff_cofinite U).mpr hU⟩
  intro A hA hAU
  exact (Ultrafilter.compl_mem_iff_notMem.mp (hU hA.compl_mem_cofinite)) hAU

end Lemmatheca.SetTheory.CompactnessAndWeakChoice
