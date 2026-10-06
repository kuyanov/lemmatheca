import Lemmatheca.SetTheory.WellOrders
import Mathlib.SetTheory.ZFC.Ordinal

/-!
# Transfinite recursion on set-function graphs

Functions and their histories are actual `ZFSet` graphs of Kuratowski pairs.
Ordinals are represented as von Neumann sets using `Ordinal.toZFSet`.
No containing value set is supplied to the recursion rule; each resulting graph
has some set of values. A rule is a relation, required to have a unique output
on every valid history, with no requirement on invalid histories.

Rules and ordinal class functions are universe-relative Lean relations and
functions. This is a semantic representation, not an encoding of first-order
formula syntax or a certification of derivability over ZF without Choice.
-/

set_option autoImplicit false

namespace Lemmatheca.SetTheory.TransfiniteRecursion

universe u

/-- Restrict a set graph to pairs whose first coordinate belongs to `A`. -/
def restrict (G A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y, z = ZFSet.pair x y) G

/-- A relational rule for the next value from an ordinal and a set-function history. -/
abbrev Rule := Ordinal.{u} → ZFSet.{u} → ZFSet.{u} → Prop

/-- The rule supplies exactly one output for every history with the required domain. -/
def IsTotalRule (Φ : Rule.{u}) : Prop :=
  ∀ (α : Ordinal.{u}) (h : ZFSet.{u}),
    (∃ S : ZFSet.{u}, ZFSet.IsFunc α.toZFSet S h) → ∃! y, Φ α h y

/-- A set-function on `θ` satisfying the rule using its restricted set graphs. -/
def IsRecursiveSolution (Φ : Rule.{u}) (θ : Ordinal.{u}) (F : ZFSet.{u}) : Prop :=
  (∃ S : ZFSet.{u}, ZFSet.IsFunc θ.toZFSet S F) ∧
    ∀ α < θ, ∀ y : ZFSet.{u},
      ZFSet.pair α.toZFSet y ∈ F ↔ Φ α (restrict F α.toZFSet) y

/-- The graph of an ordinal class function on a set-sized initial segment. -/
noncomputable def graph (f : Ordinal.{u} → ZFSet.{u}) (θ : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.range (fun α : Set.Iio θ => ZFSet.pair α.val.toZFSet (f α.val))

private theorem pair_mem_restrict (G A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ restrict G A ↔ ZFSet.pair x y ∈ G ∧ x ∈ A := by
  rw [restrict, ZFSet.mem_sep]
  constructor
  · rintro ⟨hG, a, ha, b, hab⟩
    exact ⟨hG, (ZFSet.pair_inj.mp hab).1.symm ▸ ha⟩
  · rintro ⟨hG, hx⟩
    exact ⟨hG, x, hx, y, rfl⟩

private theorem restrict_isFunc {A B S F : ZFSet.{u}}
    (hF : ZFSet.IsFunc A S F) (hBA : B ⊆ A) : ZFSet.IsFunc B S (restrict F B) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, _, y, hy, rfl⟩ := ZFSet.mem_prod.mp (hF.1 (ZFSet.mem_sep.mp hz).1)
    exact ZFSet.pair_mem_prod.mpr ⟨(pair_mem_restrict F B x y).mp hz |>.2, hy⟩
  · intro x hx
    obtain ⟨y, hy, huniq⟩ := hF.2 x (hBA hx)
    refine ⟨y, (pair_mem_restrict F B x y).mpr ⟨hy, hx⟩, ?_⟩
    intro z hz
    exact huniq z ((pair_mem_restrict F B x z).mp hz).1

private theorem restrict_restrict (F : ZFSet.{u}) {A B : ZFSet.{u}} (hAB : A ⊆ B) :
    restrict (restrict F B) A = restrict F A := by
  apply ZFSet.ext
  intro z
  simp only [restrict, ZFSet.mem_sep]
  constructor
  · exact fun hz => ⟨hz.1.1, hz.2⟩
  · rintro ⟨hz, hA⟩
    refine ⟨⟨hz, ?_⟩, hA⟩
    obtain ⟨x, hx, y, hxy⟩ := hA
    exact ⟨x, hAB hx, y, hxy⟩

private theorem function_ext {A S T F G : ZFSet.{u}}
    (hF : ZFSet.IsFunc A S F) (hG : ZFSet.IsFunc A T G)
    (h : ∀ x ∈ A, ∀ y, ZFSet.pair x y ∈ F ↔ ZFSet.pair x y ∈ G) : F = G := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hF.1 hz)
    exact (h x hx y).mp hz
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hG.1 hz)
    exact (h x hx y).mpr hz

/-- Restricting a recursive set-function to an earlier ordinal preserves its equations. -/
theorem solution_restrict (Φ : Rule.{u}) {η θ : Ordinal.{u}} {F : ZFSet.{u}}
    (hF : IsRecursiveSolution Φ θ F) (hη : η ≤ θ) :
    IsRecursiveSolution Φ η (restrict F η.toZFSet) := by
  obtain ⟨S, hS⟩ := hF.1
  refine ⟨⟨S, restrict_isFunc hS (Ordinal.toZFSet_monotone hη)⟩, ?_⟩
  intro α hα y
  rw [pair_mem_restrict]
  have hmem : α.toZFSet ∈ η.toZFSet := Ordinal.toZFSet_mem_toZFSet_iff.mpr hα
  simp only [hmem, and_true]
  rw [restrict_restrict F (Ordinal.toZFSet_monotone hα.le)]
  exact hF.2 α (lt_of_lt_of_le hα hη) y

private theorem solutions_eq (Φ : Rule.{u}) {θ : Ordinal.{u}} {F G : ZFSet.{u}}
    (hF : IsRecursiveSolution Φ θ F) (hG : IsRecursiveSolution Φ θ G) : F = G := by
  obtain ⟨S, hS⟩ := hF.1
  obtain ⟨T, hT⟩ := hG.1
  have agree : ∀ α < θ, ∀ y : ZFSet.{u},
      ZFSet.pair α.toZFSet y ∈ F ↔ ZFSet.pair α.toZFSet y ∈ G := by
    intro α
    induction α using (wellFounded_lt (α := Ordinal.{u})).induction with
    | h α ih =>
      intro hα y
      have histories : restrict F α.toZFSet = restrict G α.toZFSet := by
        apply function_ext
          (restrict_isFunc hS (Ordinal.toZFSet_monotone hα.le))
          (restrict_isFunc hT (Ordinal.toZFSet_monotone hα.le))
        intro x hx z
        obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
        simp only [pair_mem_restrict, Ordinal.toZFSet_mem_toZFSet_iff, hβ, and_true]
        exact ih β hβ (hβ.trans hα) z
      rw [hF.2 α hα y, hG.2 α hα y, histories]
  apply function_ext hS hT
  intro x hx y
  obtain ⟨α, hα, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
  exact agree α hα y

/-- Partial recursive set-functions agree on the intersection of their ordinal domains. -/
theorem partial_solutions_agree (Φ : Rule.{u}) {η θ : Ordinal.{u}} {F G : ZFSet.{u}}
    (hF : IsRecursiveSolution Φ η F) (hG : IsRecursiveSolution Φ θ G) :
    restrict F (min η θ).toZFSet = restrict G (min η θ).toZFSet := by
  exact solutions_eq Φ (solution_restrict Φ hF (min_le_left η θ))
    (solution_restrict Φ hG (min_le_right η θ))

private noncomputable def historyGraph (α : Ordinal.{u})
    (h : Set.Iio α → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun β : Set.Iio α => ZFSet.pair β.val.toZFSet (h β))

private theorem pair_mem_historyGraph (α β : Ordinal.{u})
    (h : Set.Iio α → ZFSet.{u}) (y : ZFSet.{u}) :
    ZFSet.pair β.toZFSet y ∈ historyGraph α h ↔ ∃ hb : β < α, h ⟨β, hb⟩ = y := by
  constructor
  · intro hy
    obtain ⟨⟨b, hb⟩, he⟩ := ZFSet.mem_range.mp hy
    obtain ⟨he, hv⟩ := ZFSet.pair_inj.mp he
    have he' := Ordinal.toZFSet_injective he
    change b = β at he'
    subst b
    exact ⟨hb, hv⟩
  · rintro ⟨hb, rfl⟩
    exact ZFSet.mem_range_self (f := fun b : Set.Iio α =>
      ZFSet.pair b.val.toZFSet (h b)) ⟨β, hb⟩

private theorem historyGraph_isFunc (α : Ordinal.{u}) (h : Set.Iio α → ZFSet.{u}) :
    ZFSet.IsFunc α.toZFSet (ZFSet.range h) (historyGraph α h) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨β, rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.pair_mem_prod.mpr
      ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr β.property, ZFSet.mem_range_self β⟩
  · intro x hx
    obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    refine ⟨h ⟨β, hβ⟩, (pair_mem_historyGraph α β h _).mpr ⟨hβ, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨hb, he⟩ := (pair_mem_historyGraph α β h y).mp hy
    exact he.symm

private theorem pair_mem_graph (f : Ordinal.{u} → ZFSet.{u}) (θ α : Ordinal.{u})
    (y : ZFSet.{u}) : ZFSet.pair α.toZFSet y ∈ graph f θ ↔ α < θ ∧ f α = y := by
  change ZFSet.pair α.toZFSet y ∈ historyGraph θ (fun β => f β.val) ↔ _
  rw [pair_mem_historyGraph]
  simp only [exists_prop]

private theorem graph_restrict (f : Ordinal.{u} → ZFSet.{u}) {η θ : Ordinal.{u}}
    (hη : η ≤ θ) : restrict (graph f θ) η.toZFSet = graph f η := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨β, rfl⟩ := ZFSet.mem_range.mp (ZFSet.mem_sep.mp hz).1
    have hb := (pair_mem_restrict (graph f θ) η.toZFSet _ _).mp hz |>.2
    exact (pair_mem_graph f η β.val _).mpr
      ⟨Ordinal.toZFSet_mem_toZFSet_iff.mp hb, rfl⟩
  · intro hz
    obtain ⟨β, rfl⟩ := ZFSet.mem_range.mp hz
    exact (pair_mem_restrict (graph f θ) η.toZFSet _ _).mpr
      ⟨(pair_mem_graph f θ β.val _).mpr ⟨lt_of_lt_of_le β.property hη, rfl⟩,
        Ordinal.toZFSet_mem_toZFSet_iff.mpr β.property⟩

private theorem graph_solution (Φ : Rule.{u}) (hΦ : IsTotalRule Φ)
    (f : Ordinal.{u} → ZFSet.{u}) (hf : ∀ α, Φ α (graph f α) (f α))
    (θ : Ordinal.{u}) : IsRecursiveSolution Φ θ (graph f θ) := by
  refine ⟨⟨ZFSet.range (fun β : Set.Iio θ => f β.val),
    historyGraph_isFunc θ (fun β => f β.val)⟩, ?_⟩
  intro α hα y
  rw [graph_restrict f hα.le, pair_mem_graph]
  simp only [hα, true_and]
  constructor
  · rintro rfl
    exact hf α
  · intro hy
    exact ((hΦ α (graph f α)
      ⟨_, historyGraph_isFunc α (fun β => f β.val)⟩).unique hy (hf α)).symm

/-- The compatible set solutions determine one ordinal class function with set graphs
and a set of values on every ordinal domain. -/
theorem class_function_exists_unique (Φ : Rule.{u}) (hΦ : IsTotalRule Φ) :
    ∃! f : Ordinal.{u} → ZFSet.{u},
      (∀ α, Φ α (graph f α) (f α)) ∧
      (∀ θ, IsRecursiveSolution Φ θ (graph f θ)) ∧
      (∀ η θ, η ≤ θ → restrict (graph f θ) η.toZFSet = graph f η) ∧
      (∀ θ, ∃ B : ZFSet.{u}, ∀ y : ZFSet.{u},
        y ∈ B ↔ ∃ α < θ, f α = y) := by
  classical
  let rule : Lemmatheca.SetTheory.RecursionRule Ordinal.{u} ZFSet.{u} := fun α h =>
    (hΦ α (historyGraph α h) ⟨ZFSet.range h, historyGraph_isFunc α h⟩).choose
  obtain ⟨f, hf, _⟩ := Lemmatheca.SetTheory.recursion_exists_unique rule
  have hrel : ∀ α, Φ α (graph f α) (f α) := by
    intro α
    rw [hf α]
    exact (hΦ α (historyGraph α (fun β => f β.val))
      ⟨_, historyGraph_isFunc α (fun β => f β.val)⟩).choose_spec.1
  refine ⟨f, ⟨hrel, graph_solution Φ hΦ f hrel, ?_, ?_⟩, ?_⟩
  · intro η θ hη
    exact graph_restrict f hη
  · intro θ
    refine ⟨ZFSet.range (fun α : Set.Iio θ => f α.val), fun y => ?_⟩
    simp only [ZFSet.mem_range]
    constructor
    · rintro ⟨α, hα⟩
      exact ⟨α.val, α.property, hα⟩
    · rintro ⟨α, hα, he⟩
      exact ⟨⟨α, hα⟩, he⟩
  · intro g hg
    funext α
    induction α using (wellFounded_lt (α := Ordinal.{u})).induction with
    | h α ih =>
      have histories : graph g α = graph f α := by
        unfold graph
        congr 1
        funext β
        rw [ih β.val β.property]
      have hgr := hg.1 α
      rw [histories] at hgr
      exact (hΦ α (graph f α)
        ⟨_, historyGraph_isFunc α (fun β => f β.val)⟩).unique hgr (hrel α)

/-- Every total rule has exactly one recursive set-function graph on each ordinal. -/
theorem recursion_exists_unique (Φ : Rule.{u}) (hΦ : IsTotalRule Φ) (θ : Ordinal.{u}) :
    ∃! F : ZFSet.{u}, IsRecursiveSolution Φ θ F := by
  obtain ⟨f, hf, _⟩ := class_function_exists_unique Φ hΦ
  exact ⟨graph f θ, hf.2.1 θ, fun F hF => solutions_eq Φ hF (hf.2.1 θ)⟩

end Lemmatheca.SetTheory.TransfiniteRecursion
