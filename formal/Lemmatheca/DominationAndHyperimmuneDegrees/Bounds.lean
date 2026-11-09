import Lemmatheca.BusyBeaverFunctions.FunctionOracles
import Mathlib.Order.Filter.AtTopBot.Basic

/-! Computable bounds and oracle-invariant hyperimmunity properties. -/
namespace Lemmatheca.ComputabilityTheory.HyperimmuneDegrees

open OracleComputation TuringDegrees UniversalComputation
open BusyBeaverFunctions

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The first argument is the bound. -/
def Majorizes (g f : ℕ → ℕ) : Prop := ∀ n, f n ≤ g n

def ComputablyDominated (f : ℕ → ℕ) : Prop :=
  ∃ g : ℕ → ℕ, Computable g ∧ Filter.EventuallyLE Filter.atTop f g

def initialMaximum (f : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((List.range N).map f).foldl max 0

def patchedBound (f g : ℕ → ℕ) (N n : ℕ) : ℕ := max (initialMaximum f N) (g n)

theorem finite_exception_patch (f g : ℕ → ℕ) (N : ℕ) (hg : Computable g)
    (hb : ∀ n, N ≤ n → f n ≤ g n) :
    Computable (patchedBound f g N) ∧ Majorizes (patchedBound f g N) f := by
  have hm : ∀ M n, n < M → f n ≤ initialMaximum f M := by
    intro M
    induction M with
    | zero => intro n hn; omega
    | succ M ih =>
      intro n hn
      have he : initialMaximum f (M + 1) = max (initialMaximum f M) (f M) := by
        simp [initialMaximum, List.range_succ, List.foldl_append]
      rw [he]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn) with h | rfl
      · exact (ih n h).trans (le_max_left _ _)
      · exact le_max_right _ _
  refine ⟨Primrec.nat_max.to_comp.comp (Computable.const _) hg, ?_⟩
  intro n
  by_cases hn : n < N
  · exact (hm N n hn).trans (le_max_left _ _)
  · exact (hb n (by omega)).trans (le_max_right _ _)

theorem computable_bounds_equivalent (f : ℕ → ℕ) :
    ComputablyDominated f ↔ ∃ g : ℕ → ℕ, Computable g ∧ Majorizes g f := by
  constructor
  · rintro ⟨g, hg, hb⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
    exact ⟨patchedBound f g N, finite_exception_patch f g N hg hN⟩
  · rintro ⟨g, hg, hb⟩
    exact ⟨g, hg, Filter.Eventually.of_forall hb⟩

def HyperimmuneFunction (f : ℕ → ℕ) : Prop := ¬ ComputablyDominated f

def HasHyperimmuneDegree (A : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ, PartialComputable A (fun n => Part.some (f n)) ∧ HyperimmuneFunction f

def HyperimmuneFree (A : Set ℕ) : Prop :=
  ∀ f : ℕ → ℕ, PartialComputable A (fun n => Part.some (f n)) → ComputablyDominated f

theorem hyperimmune_iff_escape (f : ℕ → ℕ) :
    HyperimmuneFunction f ↔
      ∀ g : ℕ → ℕ, Computable g → ∀ N, ∃ n, N ≤ n ∧ g n < f n := by
  classical
  constructor
  · intro hh g hg N
    by_contra he
    apply hh
    refine ⟨g, hg, Filter.eventually_atTop.mpr ⟨N, ?_⟩⟩
    intro n hn
    have h : ¬ g n < f n := fun hlt => he ⟨n, hn, hlt⟩
    omega
  · intro he hd
    obtain ⟨g, hg, hb⟩ := hd
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
    obtain ⟨n, hn, hlt⟩ := he g hg N
    exact (Nat.not_lt_of_ge (hN n hn)) hlt

theorem hyperimmune_iff_no_majorant (f : ℕ → ℕ) :
    HyperimmuneFunction f ↔ ¬ ∃ g : ℕ → ℕ, Computable g ∧ Majorizes g f := by
  rw [HyperimmuneFunction, computable_bounds_equivalent]

theorem hyperimmune_or_free (A : Set ℕ) :
    HasHyperimmuneDegree A ↔ ¬ HyperimmuneFree A := by
  classical
  constructor
  · rintro ⟨f, hf, hh⟩ hA
    exact hh (hA f hf)
  · intro hA
    change ¬ ∀ f : ℕ → ℕ, PartialComputable A (fun n => Part.some (f n)) →
      ComputablyDominated f at hA
    push Not at hA
    exact hA

theorem hyperimmune_upward {A B : Set ℕ} (hAB : Reducible A B)
    (hA : HasHyperimmuneDegree A) : HasHyperimmuneDegree B := by
  obtain ⟨f, hf, hh⟩ := hA
  exact ⟨f, (function_computable_iff_graph_reducible B f).mpr
    (reducible_trans ((function_computable_iff_graph_reducible A f).mp hf) hAB), hh⟩

theorem hyperimmune_free_downward {A B : Set ℕ} (hAB : Reducible A B)
    (hB : HyperimmuneFree B) : HyperimmuneFree A := by
  intro f hf
  exact hB f ((function_computable_iff_graph_reducible B f).mpr
    (reducible_trans ((function_computable_iff_graph_reducible A f).mp hf) hAB))

theorem degree_invariance {A B : Set ℕ} (hAB : Equivalent A B) :
    (HasHyperimmuneDegree A ↔ HasHyperimmuneDegree B) ∧
      (HyperimmuneFree A ↔ HyperimmuneFree B) := by
  exact ⟨⟨hyperimmune_upward hAB.1, hyperimmune_upward hAB.2⟩,
    ⟨hyperimmune_free_downward hAB.2, hyperimmune_free_downward hAB.1⟩⟩

theorem computable_hyperimmune_free (A : Set ℕ) (hA : ComputablePred (fun n => n ∈ A)) :
    HyperimmuneFree A := by
  intro f hf
  have hp := (computable_oracle_iff A hA (fun n => Part.some (f n))).mp hf
  have hc : Computable f := Partrec.nat_iff.mpr hp
  exact ⟨f, hc, Filter.Eventually.of_forall (fun _ => le_rfl)⟩

end
end Lemmatheca.ComputabilityTheory.HyperimmuneDegrees
