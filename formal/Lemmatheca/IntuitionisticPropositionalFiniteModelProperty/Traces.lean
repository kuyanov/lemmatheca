import Lemmatheca.IntuitionisticPropositionalFiniteModelProperty.Subformulas

namespace Lemmatheca.ProofTheory.Intuitionistic.FiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Classical

/-- The exact finite intersection of a specified prime theory with Δ. -/
noncomputable def trace (Δ : Finset Formula) (T : Canonical.PrimeWorld) : Finset Formula :=
  Δ.filter (fun A => A ∈ T.val)

/-- Worlds are the realized finite subsets themselves, not chosen representatives. -/
abbrev TraceWorld (Δ : Finset Formula) :=
  {s : Finset Formula // ∃ T : Canonical.PrimeWorld, trace Δ T = s}

noncomputable def traceWorld (Δ : Finset Formula) (T : Canonical.PrimeWorld) : TraceWorld Δ :=
  ⟨trace Δ T, T, rfl⟩

theorem trace_mem (Δ : Finset Formula) (T : Canonical.PrimeWorld) (A : Formula) :
    A ∈ trace Δ T ↔ A ∈ Δ ∧ A ∈ T.val := by
  simp [trace]

theorem trace_subset (Δ : Finset Formula) (T : Canonical.PrimeWorld) :
    trace Δ T ⊆ Δ := by
  exact Finset.filter_subset _ _

private noncomputable def traceInPower (Δ : Finset Formula) (w : TraceWorld Δ) : Δ.powerset :=
  ⟨w.val, by
    obtain ⟨T, hT⟩ := w.property
    rw [← hT]
    exact Finset.mem_powerset.mpr (trace_subset Δ T)⟩

private theorem traceInPower_injective (Δ : Finset Formula) : Function.Injective (traceInPower Δ) := by
  intro s t h
  exact Subtype.ext (congrArg (fun z : Δ.powerset => z.val) h)

instance traceWorldFinite (Δ : Finset Formula) : Finite (TraceWorld Δ) := by
  exact Finite.of_injective (traceInPower Δ) (traceInPower_injective Δ)

noncomputable instance traceWorldFintype (Δ : Finset Formula) : Fintype (TraceWorld Δ) :=
  Fintype.ofFinite _

instance traceWorldNonempty (Δ : Finset Formula) : Nonempty (TraceWorld Δ) := by
  obtain ⟨T⟩ := Canonical.canonicalModel.world_nonempty
  exact ⟨traceWorld Δ T⟩

/-- Inclusion is the inherited partial order; untracked atoms are false. -/
noncomputable def traceModel (Δ : Finset Formula) : Kripke.Model ℕ (TraceWorld Δ) where
  world_nonempty := inferInstance
  valuation s p := atom p ∈ s.val
  persistent h _ hp := h hp

theorem trace_card_bounds (Δ : Finset Formula) :
    1 ≤ Fintype.card (TraceWorld Δ) ∧ Fintype.card (TraceWorld Δ) ≤ 2 ^ Δ.card := by
  constructor
  · exact Nat.succ_le_of_lt Fintype.card_pos
  · simpa using Fintype.card_le_of_injective (traceInPower Δ) (traceInPower_injective Δ)

theorem trace_mono (Δ : Finset Formula) {T U : Canonical.PrimeWorld} (h : T ≤ U) :
    traceWorld Δ T ≤ traceWorld Δ U := by
  intro A hA
  obtain ⟨hΔ, hT⟩ := (trace_mem Δ T A).mp hA
  exact (trace_mem Δ U A).mpr ⟨hΔ, h hT⟩

theorem trace_transfer (Δ : Finset Formula) {T U : Canonical.PrimeWorld}
    (h : traceWorld Δ T ≤ traceWorld Δ U) {A : Formula} (hΔ : A ∈ Δ) (hT : A ∈ T.val) :
    A ∈ U.val := by
  exact ((trace_mem Δ U A).mp (h ((trace_mem Δ T A).mpr ⟨hΔ, hT⟩))).2

theorem trace_forcing (Δ : Finset Formula) (hΔ : SubformulaClosed Δ)
    (A : Formula) (hA : A ∈ Δ) (T : Canonical.PrimeWorld) :
    Kripke.Forces (traceModel Δ) (traceWorld Δ T) A ↔ A ∈ T.val := by
  classical
  induction A generalizing T with
  | atom p =>
      change atom p ∈ trace Δ T ↔ atom p ∈ T.val
      exact (trace_mem Δ T _).trans (and_iff_right hA)
  | falsum =>
      constructor
      · intro h
        exact h.elim
      · intro h
        exact T.property.consistent (.assumption h)
  | neg A ih =>
      have hc : A ∈ Δ := hΔ _ hA (by simp [subformulas, self_mem_subformulas])
      constructor
      · intro h
        by_contra hn
        obtain ⟨hU, hTU, hUA⟩ := Canonical.missing_negation_extension T.property hn
        let U : Canonical.PrimeWorld := ⟨Canonical.extension (insert A T.val) falsum, hU⟩
        exact h (traceWorld Δ U) (trace_mono Δ hTU) ((ih hc U).mpr hUA)
      · intro hN w hw hB
        obtain ⟨U, hU⟩ := w.property
        have heq : traceWorld Δ U = w := Subtype.ext hU
        subst w
        have hNU := trace_transfer Δ hw hA hN
        exact U.property.consistent (.negElim (.assumption ((ih hc U).mp hB))
          (.assumption hNU))
  | conj A B ihA ihB =>
      have hcA : A ∈ Δ := hΔ _ hA (by simp [subformulas, self_mem_subformulas])
      have hcB : B ∈ Δ := hΔ _ hA (by simp [subformulas, self_mem_subformulas])
      exact (and_congr (ihA hcA T) (ihB hcB T)).trans
        (Canonical.prime_conj_iff T.property A B).symm
  | disj A B ihA ihB =>
      have hcA : A ∈ Δ := hΔ _ hA (by simp [subformulas, self_mem_subformulas])
      have hcB : B ∈ Δ := hΔ _ hA (by simp [subformulas, self_mem_subformulas])
      exact (or_congr (ihA hcA T) (ihB hcB T)).trans
        (Canonical.prime_disj_iff T.property A B).symm
  | impl A B ihA ihB =>
      have hcA : A ∈ Δ := hΔ _ hA (by simp [subformulas, self_mem_subformulas])
      have hcB : B ∈ Δ := hΔ _ hA (by simp [subformulas, self_mem_subformulas])
      constructor
      · intro h
        by_contra hn
        obtain ⟨hU, hTU, hUA, hnUB⟩ := Canonical.missing_implication_extension T.property hn
        let U : Canonical.PrimeWorld := ⟨Canonical.extension (insert A T.val) B, hU⟩
        exact hnUB ((ihB hcB U).mp
          (h (traceWorld Δ U) (trace_mono Δ hTU) ((ihA hcA U).mpr hUA)))
      · intro hImp w hw hB
        obtain ⟨U, hU⟩ := w.property
        have heq : traceWorld Δ U = w := Subtype.ext hU
        subst w
        have hIU := trace_transfer Δ hw hA hImp
        have hBU : B ∈ U.val := U.property.closed
          (.implElim (.assumption hIU) (.assumption ((ihA hcA U).mp hB)))
        exact (ihB hcB U).mpr hBU

/-- The actual designated trace of the specified canonical extension is a counterexample. -/
theorem bounded_countermodel (Γ : Finset Formula) (A : Formula)
    (h : ¬ Derives (Γ : Set Formula) A) :
    Kripke.Countermodel (traceModel (problemSubformulas Γ A))
      (traceWorld (problemSubformulas Γ A) (Canonical.extensionWorld (Γ : Set Formula) A h))
      (Γ : Set Formula) A := by
  let Δ := problemSubformulas Γ A
  let T := Canonical.extensionWorld (Γ : Set Formula) A h
  have hc := problem_closed Γ A
  constructor
  · intro B hB
    apply (trace_forcing Δ hc B ((problem_contains Γ A).2 hB) T).mpr
    exact Canonical.extension_contains (Γ : Set Formula) A hB
  · intro hA
    exact Canonical.extension_omits h
      ((trace_forcing Δ hc A (problem_contains Γ A).1 T).mp hA)

/-- Public finite-poset witness for consequences using a finite premise set. -/
theorem finite_poset_countermodel (Γ : Finset Formula) (A : Formula)
    (h : ¬ Derives (Γ : Set Formula) A) :
    ∃ (W : Type) (r : PartialOrder W) (f : Fintype W)
      (M : @Kripke.Model ℕ W r.toPreorder) (w : W),
      @Fintype.card W f ≤ worldBound Γ A ∧
        @Kripke.Countermodel ℕ W r.toPreorder M w (Γ : Set Formula) A := by
  let Δ := problemSubformulas Γ A
  refine ⟨TraceWorld Δ, inferInstance, inferInstance, traceModel Δ,
    traceWorld Δ (Canonical.extensionWorld (Γ : Set Formula) A h), ?_,
    bounded_countermodel Γ A h⟩
  exact (trace_card_bounds Δ).2

theorem finite_poset_valid_iff (A : Formula) :
    (∀ (W : Type) (r : PartialOrder W) (_f : Fintype W)
      (M : @Kripke.Model ℕ W r.toPreorder) (w : W),
      @Kripke.Forces ℕ W r.toPreorder M w A) ↔ Derives ∅ A := by
  constructor
  · intro h
    by_contra hn
    have hn' : ¬ Derives ((∅ : Finset Formula) : Set Formula) A := by simpa using hn
    obtain ⟨W, r, f, M, w, _, hc⟩ := finite_poset_countermodel ∅ A hn'
    exact hc.2 (h W r f M w)
  · intro hd W r f M w
    exact @Kripke.sound ℕ W r.toPreorder ∅ A hd M w (by simp [Kripke.ForcesContext])

end Lemmatheca.ProofTheory.Intuitionistic.FiniteModels
