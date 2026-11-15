import Lemmatheca.IntuitionisticPropositionalFiniteModelProperty.Subformulas
import Lemmatheca.IntuitionisticPropositionalKripkeMorphisms.Morphisms

/-! Realized forcing traces of an arbitrary supplied model. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Filtrations

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Classical

universe v
abbrev Formula := FiniteModels.Formula
variable {W : Type v} [Preorder W]

/-- The exact tracked formulas forced at the supplied original world. -/
noncomputable def trace (M : Kripke.Model ℕ W) (Δ : Finset Formula) (w : W) :
    Finset Formula :=
  Δ.filter (fun A => Kripke.Forces M w A)

/-- Worlds are realized finite subsets, independently of representatives. -/
abbrev TraceWorld (M : Kripke.Model ℕ W) (Δ : Finset Formula) :=
  {s : Finset Formula // ∃ w : W, trace M Δ w = s}

/-- The specified map from an original world to its actual trace. -/
noncomputable def traceWorld (M : Kripke.Model ℕ W) (Δ : Finset Formula)
    (w : W) : TraceWorld M Δ :=
  ⟨trace M Δ w, w, rfl⟩

theorem trace_mem (M : Kripke.Model ℕ W) (Δ : Finset Formula) (w : W)
    (A : Formula) : A ∈ trace M Δ w ↔ A ∈ Δ ∧ Kripke.Forces M w A := by
  simp [trace]

theorem trace_subset (M : Kripke.Model ℕ W) (Δ : Finset Formula) (w : W) :
    trace M Δ w ⊆ Δ := by
  exact Finset.filter_subset _ _

theorem trace_eq_iff (M : Kripke.Model ℕ W) (Δ : Finset Formula) (w z : W) :
    trace M Δ w = trace M Δ z ↔
      ∀ A ∈ Δ, (Kripke.Forces M w A ↔ Kripke.Forces M z A) := by
  constructor
  · intro h A hA
    have hm : (A ∈ trace M Δ w ↔ A ∈ trace M Δ z) := by rw [h]
    simpa only [trace_mem, and_iff_right hA] using hm
  · intro h
    ext A
    by_cases hA : A ∈ Δ
    · simpa only [trace_mem, and_iff_right hA] using h A hA
    · simp [trace_mem, hA]

private noncomputable def traceInPower (M : Kripke.Model ℕ W) (Δ : Finset Formula)
    (s : TraceWorld M Δ) : Δ.powerset :=
  ⟨s.val, by
    obtain ⟨w, hw⟩ := s.property
    rw [← hw]
    exact Finset.mem_powerset.mpr (trace_subset M Δ w)⟩

private theorem traceInPower_injective (M : Kripke.Model ℕ W) (Δ : Finset Formula) :
    Function.Injective (traceInPower M Δ) := by
  intro s t h
  exact Subtype.ext (congrArg (fun x : Δ.powerset => x.val) h)

instance traceWorldFinite (M : Kripke.Model ℕ W) (Δ : Finset Formula) :
    Finite (TraceWorld M Δ) :=
  Finite.of_injective (traceInPower M Δ) (traceInPower_injective M Δ)

noncomputable instance traceWorldFintype (M : Kripke.Model ℕ W) (Δ : Finset Formula) :
    Fintype (TraceWorld M Δ) :=
  Fintype.ofFinite _

instance traceWorldNonempty (M : Kripke.Model ℕ W) (Δ : Finset Formula) :
    Nonempty (TraceWorld M Δ) := by
  obtain ⟨w⟩ := M.world_nonempty
  exact ⟨traceWorld M Δ w⟩

/-- Inclusion is inherited; every atom absent from Δ is false. -/
noncomputable def traceModel (M : Kripke.Model ℕ W) (Δ : Finset Formula) :
    Kripke.Model ℕ (TraceWorld M Δ) where
  world_nonempty := inferInstance
  valuation s p := atom p ∈ s.val
  persistent h _ hp := h hp

theorem trace_card_bounds (M : Kripke.Model ℕ W) (Δ : Finset Formula) :
    1 ≤ Fintype.card (TraceWorld M Δ) ∧
      Fintype.card (TraceWorld M Δ) ≤ 2 ^ Δ.card := by
  constructor
  · exact Nat.succ_le_of_lt Fintype.card_pos
  · simpa using Fintype.card_le_of_injective (traceInPower M Δ)
      (traceInPower_injective M Δ)

theorem untracked_atom_false (M : Kripke.Model ℕ W) (Δ : Finset Formula)
    (p : ℕ) (hp : atom p ∉ Δ) (s : TraceWorld M Δ) :
    ¬ Kripke.Forces (traceModel M Δ) s (atom p) := by
  intro h
  obtain ⟨w, hw⟩ := s.property
  change atom p ∈ s.val at h
  rw [← hw] at h
  exact hp (trace_subset M Δ w h)

theorem trace_surjective (M : Kripke.Model ℕ W) (Δ : Finset Formula) :
    Function.Surjective (traceWorld M Δ) := by
  intro s
  obtain ⟨w, hw⟩ := s.property
  exact ⟨w, Subtype.ext hw⟩

theorem trace_mono (M : Kripke.Model ℕ W) (Δ : Finset Formula) :
    Monotone (traceWorld M Δ) := by
  intro w z hwz A hA
  obtain ⟨hΔ, hw⟩ := (trace_mem M Δ w A).mp hA
  exact (trace_mem M Δ z A).mpr ⟨hΔ, Kripke.forces_mono M A hwz hw⟩

theorem trace_transfer (M : Kripke.Model ℕ W) (Δ : Finset Formula) {w z : W}
    (h : traceWorld M Δ w ≤ traceWorld M Δ z)
    {A : Formula} (hA : A ∈ Δ) (hw : Kripke.Forces M w A) :
    Kripke.Forces M z A := by
  exact ((trace_mem M Δ z A).mp (h ((trace_mem M Δ w A).mpr ⟨hA, hw⟩))).2

theorem trace_forcing (M : Kripke.Model ℕ W) (Δ : Finset Formula)
    (hΔ : FiniteModels.SubformulaClosed Δ) (A : Formula) (hA : A ∈ Δ) (w : W) :
    Kripke.Forces (traceModel M Δ) (traceWorld M Δ w) A ↔
      Kripke.Forces M w A := by
  induction A generalizing w with
  | atom p =>
      change atom p ∈ trace M Δ w ↔ Kripke.Forces M w (atom p)
      exact (trace_mem M Δ w _).trans (and_iff_right hA)
  | falsum => rfl
  | neg A ih =>
      have hc : A ∈ Δ :=
        hΔ _ hA (by simp [FiniteModels.subformulas, FiniteModels.self_mem_subformulas])
      constructor
      · intro h z hwz hz
        exact h (traceWorld M Δ z) (trace_mono M Δ hwz) ((ih hc z).mpr hz)
      · intro hn s hs hB
        obtain ⟨z, hz⟩ := s.property
        have heq : traceWorld M Δ z = s := Subtype.ext hz
        subst s
        have hnz := trace_transfer M Δ hs hA hn
        exact hnz z le_rfl ((ih hc z).mp hB)
  | conj A B ihA ihB =>
      have hcA : A ∈ Δ :=
        hΔ _ hA (by simp [FiniteModels.subformulas, FiniteModels.self_mem_subformulas])
      have hcB : B ∈ Δ :=
        hΔ _ hA (by simp [FiniteModels.subformulas, FiniteModels.self_mem_subformulas])
      exact and_congr (ihA hcA w) (ihB hcB w)
  | disj A B ihA ihB =>
      have hcA : A ∈ Δ :=
        hΔ _ hA (by simp [FiniteModels.subformulas, FiniteModels.self_mem_subformulas])
      have hcB : B ∈ Δ :=
        hΔ _ hA (by simp [FiniteModels.subformulas, FiniteModels.self_mem_subformulas])
      exact or_congr (ihA hcA w) (ihB hcB w)
  | impl A B ihA ihB =>
      have hcA : A ∈ Δ :=
        hΔ _ hA (by simp [FiniteModels.subformulas, FiniteModels.self_mem_subformulas])
      have hcB : B ∈ Δ :=
        hΔ _ hA (by simp [FiniteModels.subformulas, FiniteModels.self_mem_subformulas])
      constructor
      · intro h z hwz hz
        exact (ihB hcB z).mp
          (h (traceWorld M Δ z) (trace_mono M Δ hwz) ((ihA hcA z).mpr hz))
      · intro h s hs hB
        obtain ⟨z, hz⟩ := s.property
        have heq : traceWorld M Δ z = s := Subtype.ext hz
        subst s
        have hiz := trace_transfer M Δ hs hA h
        exact (ihB hcB z).mpr (hiz z le_rfl ((ihA hcA z).mp hB))

theorem trace_context (M : Kripke.Model ℕ W) (Δ : Finset Formula)
    (hΔ : FiniteModels.SubformulaClosed Δ) (Γ : Set Formula)
    (hΓ : Γ ⊆ (Δ : Set Formula)) (w : W) :
    Kripke.ForcesContext (traceModel M Δ) (traceWorld M Δ w) Γ ↔
      Kripke.ForcesContext M w Γ := by
  constructor
  · intro h A hA
    exact (trace_forcing M Δ hΔ A (hΓ hA) w).mp (h A hA)
  · intro h A hA
    exact (trace_forcing M Δ hΔ A (hΓ hA) w).mpr (h A hA)

theorem trace_countermodel (M : Kripke.Model ℕ W) (Δ : Finset Formula)
    (hΔ : FiniteModels.SubformulaClosed Δ) (Γ : Set Formula)
    (hΓ : Γ ⊆ (Δ : Set Formula)) (A : Formula) (hA : A ∈ Δ) (w : W) :
    Kripke.Countermodel (traceModel M Δ) (traceWorld M Δ w) Γ A ↔
      Kripke.Countermodel M w Γ A := by
  exact and_congr (trace_context M Δ hΔ Γ hΓ w)
    (not_congr (trace_forcing M Δ hΔ A hA w))

theorem trace_root (M : Kripke.Model ℕ W) (Δ : Finset Formula)
    (r : W) (hr : ∀ w : W, r ≤ w) :
    ∀ s : TraceWorld M Δ, traceWorld M Δ r ≤ s := by
  intro s
  obtain ⟨w, rfl⟩ := trace_surjective M Δ s
  exact trace_mono M Δ (hr w)

theorem trace_directed (M : Kripke.Model ℕ W) (Δ : Finset Formula)
    (h : ∀ w z : W, ∃ u : W, w ≤ u ∧ z ≤ u) :
    ∀ s t : TraceWorld M Δ, ∃ u : TraceWorld M Δ, s ≤ u ∧ t ≤ u := by
  intro s t
  obtain ⟨w, rfl⟩ := trace_surjective M Δ s
  obtain ⟨z, rfl⟩ := trace_surjective M Δ t
  obtain ⟨u, hwu, hzu⟩ := h w z
  exact ⟨traceWorld M Δ u, trace_mono M Δ hwu, trace_mono M Δ hzu⟩

theorem trace_greatest (M : Kripke.Model ℕ W) (Δ : Finset Formula)
    (h : ∀ w z : W, ∃ u : W, w ≤ u ∧ z ≤ u) :
    ∃ g : TraceWorld M Δ, ∀ s : TraceWorld M Δ, s ≤ g := by
  obtain ⟨r⟩ := M.world_nonempty
  have hb (S : Finset (TraceWorld M Δ)) :
      ∃ u : TraceWorld M Δ, ∀ s ∈ S, s ≤ u := by
    induction S using Finset.induction_on with
    | empty => exact ⟨traceWorld M Δ r, by simp⟩
    | @insert a S _ ih =>
        obtain ⟨u, hu⟩ := ih
        obtain ⟨z, huz, haz⟩ := trace_directed M Δ h u a
        refine ⟨z, ?_⟩
        intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact haz
        · exact le_trans (hu s hs) huz
  obtain ⟨g, hg⟩ := hb Finset.univ
  exact ⟨g, fun s => hg s (Finset.mem_univ s)⟩

theorem trace_comparable (M : Kripke.Model ℕ W) (Δ : Finset Formula)
    (h : ∀ w z : W, w ≤ z ∨ z ≤ w) :
    ∀ s t : TraceWorld M Δ, s ≤ t ∨ t ≤ s := by
  intro s t
  obtain ⟨w, rfl⟩ := trace_surjective M Δ s
  obtain ⟨z, rfl⟩ := trace_surjective M Δ t
  exact (h w z).imp (fun hwz => trace_mono M Δ hwz)
    (fun hzw => trace_mono M Δ hzw)

theorem empty_traces (M : Kripke.Model ℕ W) :
    Fintype.card (TraceWorld M ∅) = 1 ∧
      ∀ (s : TraceWorld M ∅) (p : ℕ),
        ¬ Kripke.Forces (traceModel M ∅) s (atom p) := by
  have hv (s : TraceWorld M ∅) : s.val = ∅ := by
    obtain ⟨w, hw⟩ := s.property
    rw [← hw]
    simp [trace]
  have hsub : Subsingleton (TraceWorld M ∅) := ⟨fun s t =>
    Subtype.ext ((hv s).trans (hv t).symm)⟩
  have hle : Fintype.card (TraceWorld M ∅) ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr hsub
  refine ⟨Nat.le_antisymm hle (Nat.succ_le_of_lt Fintype.card_pos), ?_⟩
  intro s p
  exact untracked_atom_false M ∅ p (by simp) s

end Lemmatheca.ProofTheory.Intuitionistic.Filtrations
