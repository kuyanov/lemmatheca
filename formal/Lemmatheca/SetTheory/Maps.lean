import Lemmatheca.SetTheory.SetOperations
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Maps, images, and inverses

Reviewed declarations and proofs for the sets-and-maps entry, including its
examples and question answers. Proofs preserve the approved targets.

Types represent map domains and codomains; subsets are represented by `Set` and
can be used as domain or codomain types through their subtypes. The diagram uses
`Fin 3` for {0, 1, 2} and `MapLabel` for {p, q, r}.

Lean's real division is total, with 1 / 0 = 0. To express the human question
about an undefined reciprocal, use the relation x * y = 1, not the false claim
that Lean's term 1 / 0 has no value. Likewise, square roots are specified by
their relation and the required nonnegative domain and codomain.
-/

namespace Lemmatheca.SetsAndMaps

universe u v w z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}

/-- Domain and codomain are both part of a map's type. -/
abbrev Map (A : Type u) (B : Type v) := A → B

/-- The totality and uniqueness condition on a relation between two types. -/
def isFunctionGraph (R : Set (α × β)) : Prop := ∀ x, ∃! y, (x, y) ∈ R

theorem graph_has_unique_outputs (f : α → β) :
    isFunctionGraph (Set.graphOn f Set.univ) := by
  intro x
  refine ⟨f x, by simp, ?_⟩
  intro y hy
  exact (Set.mem_graphOn.mp hy).2.symm

theorem function_graph_characterization (R : Set (α × β)) :
    isFunctionGraph R ↔ ∃ f : α → β, R = Set.graphOn f Set.univ := by
  classical
  constructor
  · intro h
    unfold isFunctionGraph at h
    choose f hf hunique using h
    refine ⟨f, ?_⟩
    ext ⟨x, y⟩
    simp only [Set.mem_graphOn, Set.mem_univ, true_and]
    exact ⟨fun hxy => (hunique x y hxy).symm, fun hxy => hxy ▸ hf x⟩
  · rintro ⟨f, rfl⟩
    exact graph_has_unique_outputs f

theorem map_equality (f g : α → β) : f = g ↔ ∀ x, f x = g x := by
  exact ⟨fun h x => congrFun h x, funext⟩

theorem equal_real_formulas :
    (fun x : ℝ => 2 * (x + 1)) = (fun x : ℝ => 2 * x + 2) := by
  apply (map_equality _ _).mpr
  intro x
  ring

/-- The three distinct labels in the diagram's codomain. -/
inductive MapLabel where
  | p | q | r
  deriving DecidableEq

/-- The displayed map: 0 goes to p, and 1 and 2 go to q. -/
def diagramMap (x : Fin 3) : MapLabel := if x = 0 then .p else .q

theorem diagram_map_values :
    diagramMap 0 = .p ∧ diagramMap 1 = .q ∧ diagramMap 2 = .q := by
  simp [diagramMap]

theorem diagram_map_graph :
    Set.graphOn diagramMap Set.univ = {(0, .p), (1, .q), (2, .q)} := by
  ext ⟨x, y⟩
  fin_cases x <;> cases y <;> simp [diagramMap]

theorem reciprocal_at_zero_impossible : ¬ ∃ y : ℝ, (0 : ℝ) * y = 1 := by
  simp

/-- The reciprocal with the nonzero domain required in the answer. -/
noncomputable def reciprocalNonzero (x : {x : ℝ // x ≠ 0}) : ℝ := 1 / x.val

theorem reciprocal_nonzero_unique (x : {x : ℝ // x ≠ 0}) :
    x.val * reciprocalNonzero x = 1 ∧ ∃! y : ℝ, x.val * y = 1 := by
  have hmul : x.val * reciprocalNonzero x = 1 := by
    simpa [reciprocalNonzero, one_div] using mul_inv_cancel₀ x.property
  refine ⟨hmul, reciprocalNonzero x, hmul, ?_⟩
  intro y hy
  apply mul_left_cancel₀ x.property
  exact hy.trans hmul.symm

theorem negative_has_no_square_root (x : ℝ) (hx : x < 0) :
    ¬ ∃ y : ℝ, y ^ 2 = x := by
  rintro ⟨y, hy⟩
  nlinarith [sq_nonneg y]

theorem positive_has_two_square_roots (x : ℝ) (hx : 0 < x) :
    ∃ y z : ℝ, y ≠ z ∧ ∀ t : ℝ, t ^ 2 = x ↔ t = y ∨ t = z := by
  have hs := Real.sq_sqrt hx.le
  refine ⟨Real.sqrt x, -Real.sqrt x, ?_, ?_⟩
  · have hpos := Real.sqrt_pos.mpr hx
    linarith
  · intro t
    constructor
    · intro ht
      have hprod : (t - Real.sqrt x) * (t + Real.sqrt x) = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with h | h
      · left
        linarith
      · right
        linarith
    · rintro (rfl | rfl) <;> nlinarith

theorem four_has_two_square_roots :
    (2 : ℝ) ^ 2 = 4 ∧ (-2 : ℝ) ^ 2 = 4 ∧ (2 : ℝ) ≠ -2 := by
  norm_num

theorem nonnegative_square_root_unique (x : {x : ℝ // 0 ≤ x}) :
    ∃! y : {y : ℝ // 0 ≤ y}, y.val ^ 2 = x.val := by
  refine ⟨⟨Real.sqrt x.val, Real.sqrt_nonneg _⟩, Real.sq_sqrt x.property, ?_⟩
  intro y hy
  apply Subtype.ext
  have hy0 := y.property
  have hs0 := Real.sqrt_nonneg x.val
  have hs := Real.sq_sqrt x.property
  dsimp at *
  nlinarith

theorem nonnegative_square_root_map_exists :
    ∃ g : {x : ℝ // 0 ≤ x} → {y : ℝ // 0 ≤ y}, ∀ x, (g x).val ^ 2 = x.val := by
  classical
  choose g hg using fun x => (nonnegative_square_root_unique x).exists
  exact ⟨g, hg⟩

/-- Composition applies the right-hand map first. -/
def compose (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)

/-- The identity leaves every input fixed. -/
def identityMap (A : Type u) : A → A := fun x => x

/-- Restriction changes the domain to a subset and retains the same values. -/
def restrictMap (f : α → β) (S : Set α) : S → β := fun x => f x.val

theorem composition_order_example :
    (∀ x : ℝ, ((fun y => 2 * y) ∘ (fun y => y + 1)) x = 2 * x + 2) ∧
      (∀ x : ℝ, ((fun y => y + 1) ∘ (fun y => 2 * y)) x = 2 * x + 1) ∧
      ((fun y : ℝ => 2 * y) ∘ (fun y => y + 1)) ≠
        ((fun y : ℝ => y + 1) ∘ (fun y => 2 * y)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    dsimp
    ring
  · intro x
    rfl
  · intro h
    have hzero := congrFun h 0
    norm_num at hzero

theorem composition_associative (f : α → β) (g : β → γ) (h : γ → δ) :
    (h ∘ g) ∘ f = h ∘ (g ∘ f) := by
  rfl

theorem composition_identity (f : α → β) : id ∘ f = f ∧ f ∘ id = f := by
  exact ⟨rfl, rfl⟩

/-- The fiber over y is the preimage of its singleton. -/
def fiber (f : α → β) (y : β) : Set α := f ⁻¹' {y}

theorem range_is_image_univ (f : α → β) : Set.range f = f '' Set.univ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩
  · rintro ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩

theorem diagram_images_and_preimages :
    diagramMap '' {1, 2} = {.q} ∧
      diagramMap ⁻¹' {.q} = {1, 2} ∧ diagramMap ⁻¹' {.r} = ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · simp [diagramMap]
  · ext x
    fin_cases x <;> simp [diagramMap]
  · ext x
    fin_cases x <;> simp [diagramMap]

theorem preimage_union (f : α → β) (T V : Set β) :
    f ⁻¹' (T ∪ V) = (f ⁻¹' T) ∪ (f ⁻¹' V) := by
  rfl

theorem preimage_intersection (f : α → β) (T V : Set β) :
    f ⁻¹' (T ∩ V) = (f ⁻¹' T) ∩ (f ⁻¹' V) := by
  rfl

theorem preimage_complement (f : α → β) (T : Set β) :
    f ⁻¹' Tᶜ = (f ⁻¹' T)ᶜ := by
  rfl

theorem preimage_empty (f : α → β) : f ⁻¹' ∅ = ∅ := by
  rfl

theorem preimage_univ (f : α → β) : f ⁻¹' Set.univ = Set.univ := by
  rfl

theorem image_union (f : α → β) (S T : Set α) :
    f '' (S ∪ T) = (f '' S) ∪ (f '' T) := by
  ext y
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩

theorem image_intersection_subset (f : α → β) (S T : Set α) :
    f '' (S ∩ T) ⊆ (f '' S) ∩ (f '' T) := by
  rintro y ⟨x, ⟨hS, hT⟩, rfl⟩
  exact ⟨⟨x, hS, rfl⟩, ⟨x, hT, rfl⟩⟩

theorem image_intersection_counterexample :
    ({1} : Set (Fin 3)) ∩ {2} = ∅ ∧
      diagramMap '' (({1} : Set (Fin 3)) ∩ {2}) = ∅ ∧
      diagramMap '' {1} = {.q} ∧ diagramMap '' {2} = {.q} ∧
      (diagramMap '' {1}) ∩ (diagramMap '' {2}) = {.q} ∧
      diagramMap '' (({1} : Set (Fin 3)) ∩ {2}) ≠
        (diagramMap '' {1}) ∩ (diagramMap '' {2}) := by
  have hdisjoint : ({1} : Set (Fin 3)) ∩ {2} = ∅ := by
    ext x
    fin_cases x <;> simp
  simp [hdisjoint, diagramMap]

theorem injective_iff_fibers_subsingleton (f : α → β) :
    Function.Injective f ↔ ∀ y, (fiber f y).Subsingleton := by
  constructor
  · intro hf y a ha b hb
    change f a = y at ha
    change f b = y at hb
    exact hf (ha.trans hb.symm)
  · intro h a b hab
    exact h (f a) rfl hab.symm

theorem surjective_iff_range_univ (f : α → β) :
    Function.Surjective f ↔ Set.range f = Set.univ := by
  constructor
  · intro hf
    ext y
    exact ⟨fun _ => trivial, fun _ => hf y⟩
  · intro h y
    have hy : y ∈ Set.range f := by rw [h]; trivial
    exact hy

theorem surjective_iff_fibers_nonempty (f : α → β) :
    Function.Surjective f ↔ ∀ y, (fiber f y).Nonempty := by
  rfl

theorem bijective_iff_unique_preimages (f : α → β) :
    Function.Bijective f ↔ ∀ y, ∃! x, f x = y := by
  constructor
  · rintro ⟨hinj, hsurj⟩ y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, hx, fun z hz => hinj (hz.trans hx.symm)⟩
  · intro h
    constructor
    · intro a b hab
      obtain ⟨x, _, hunique⟩ := h (f a)
      exact (hunique a rfl).trans (hunique b hab.symm).symm
    · intro y
      exact (h y).exists

theorem diagram_map_neither_injective_nor_surjective :
    ¬ Function.Injective diagramMap ∧ ¬ Function.Surjective diagramMap := by
  constructor
  · intro h
    have hinputs := h (show diagramMap 1 = diagramMap 2 by decide)
    norm_num at hinputs
  · intro h
    obtain ⟨x, hx⟩ := h .r
    fin_cases x <;> simp [diagramMap] at hx

theorem successor_injective_not_surjective :
    Function.Injective Nat.succ ∧ ¬ Function.Surjective Nat.succ ∧
      0 ∉ Set.range Nat.succ := by
  refine ⟨Nat.succ_injective, ?_, ?_⟩
  · intro h
    obtain ⟨n, hn⟩ := h 0
    exact Nat.succ_ne_zero n hn
  · rintro ⟨n, hn⟩
    exact Nat.succ_ne_zero n hn

theorem real_translation_bijective :
    Function.Bijective (fun x : ℝ => x + 1) ∧
      ∀ y : ℝ, (y - 1) + 1 = y ∧ ∀ x : ℝ, x + 1 = y → x = y - 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b h
    linarith
  · intro y
    refine ⟨y - 1, ?_⟩
    ring
  · intro y
    constructor
    · ring
    · intro x h
      linarith

/-- Range equality expresses surjectivity onto the nonnegative reals. -/
theorem square_map_codomain_example :
    ¬ Function.Surjective (fun x : ℝ => x ^ 2) ∧
      Set.range (fun x : ℝ => x ^ 2) = {y : ℝ | 0 ≤ y} ∧
      ¬ Function.Injective (fun x : ℝ => x ^ 2) ∧
      (1 : ℝ) ^ 2 = (-1 : ℝ) ^ 2 ∧ (1 : ℝ) ≠ -1 := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩
  · intro h
    exact (negative_has_no_square_root (-1) (by norm_num)) (h (-1))
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact sq_nonneg x
    · intro hy
      obtain ⟨x, hx, _⟩ := nonnegative_square_root_unique ⟨y, hy⟩
      exact ⟨x.val, hx⟩
  · intro h
    have hinputs := h (show (1 : ℝ) ^ 2 = (-1 : ℝ) ^ 2 by norm_num)
    norm_num at hinputs

theorem subset_preimage_image (f : α → β) (S : Set α) : S ⊆ f ⁻¹' (f '' S) := by
  intro x hx
  exact ⟨x, hx, rfl⟩

theorem preimage_image_strict_example :
    properSubset ({1} : Set (Fin 3)) (diagramMap ⁻¹' (diagramMap '' {1})) := by
  unfold properSubset
  rw [Set.image_singleton, diagram_map_values.2.1, diagram_images_and_preimages.2.1]
  constructor
  · intro x hx
    exact Or.inl hx
  · intro h
    have htwo : (2 : Fin 3) ∈ ({1} : Set (Fin 3)) := by rw [h]; simp
    norm_num at htwo

theorem image_preimage (f : α → β) (T : Set β) :
    f '' (f ⁻¹' T) = T ∩ Set.range f := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, ⟨x, rfl⟩⟩
  · rintro ⟨hy, ⟨x, rfl⟩⟩
    exact ⟨x, hy, rfl⟩

theorem preimage_image_of_injective (f : α → β) (hf : Function.Injective f) (S : Set α) :
    f ⁻¹' (f '' S) = S := by
  ext x
  constructor
  · rintro ⟨s, hs, heq⟩
    exact hf heq ▸ hs
  · intro hx
    exact subset_preimage_image f S hx

theorem image_preimage_of_surjective (f : α → β) (hf : Function.Surjective f) (T : Set β) :
    f '' (f ⁻¹' T) = T := by
  rw [image_preimage, (surjective_iff_range_univ f).mp hf, Set.inter_univ]

/-- Both composition identities are required for an inverse. -/
def isInverse (f : α → β) (g : β → α) : Prop := g ∘ f = id ∧ f ∘ g = id

theorem inverse_exists_iff_bijective (f : α → β) :
    (∃ g : β → α, isInverse f g) ↔ Function.Bijective f := by
  classical
  constructor
  · rintro ⟨g, hleft, hright⟩
    constructor
    · intro a b hab
      calc
        a = g (f a) := (congrFun hleft a).symm
        _ = g (f b) := congrArg g hab
        _ = b := congrFun hleft b
    · intro y
      exact ⟨g y, congrFun hright y⟩
  · intro hf
    have hpreimages := (bijective_iff_unique_preimages f).mp hf
    choose g hfg hunique using hpreimages
    refine ⟨g, ?_, ?_⟩
    · funext x
      exact (hunique (f x) x rfl).symm
    · funext y
      exact hfg y

theorem inverse_unique (f : α → β) (g h : β → α)
    (hg : isInverse f g) (hh : isInverse f h) : g = h := by
  funext y
  calc
    g y = g (f (h y)) := congrArg g (congrFun hh.2 y).symm
    _ = h y := congrFun hg.1 (h y)

theorem preimage_is_inverse_image (f : α → β) (g : β → α)
    (hg : isInverse f g) (T : Set β) : f ⁻¹' T = g '' T := by
  ext x
  constructor
  · intro hx
    exact ⟨f x, hx, congrFun hg.1 x⟩
  · rintro ⟨y, hy, rfl⟩
    change f (g y) ∈ T
    rw [show f (g y) = y from congrFun hg.2 y]
    exact hy

theorem one_sided_inverse_counterexample :
    Nat.pred ∘ Nat.succ = id ∧ Nat.succ (Nat.pred 0) = 1 ∧
      Nat.succ (Nat.pred 0) ≠ 0 ∧ Nat.succ ∘ Nat.pred ≠ id ∧
      ¬ ∃ g : ℕ → ℕ, isInverse Nat.succ g := by
  refine ⟨?_, rfl, by decide, ?_, ?_⟩
  · funext n
    exact Nat.pred_succ n
  · intro h
    have hzero := congrFun h 0
    norm_num at hzero
  · intro h
    exact successor_injective_not_surjective.2.1
      ((inverse_exists_iff_bijective Nat.succ).mp h).2

theorem empty_domain_unique_map [IsEmpty α] : ∃! _f : α → β, True := by
  refine ⟨fun x => isEmptyElim x, trivial, ?_⟩
  intro g _
  funext x
  exact isEmptyElim x

theorem empty_domain_graph [IsEmpty α] (f : α → β) :
    Set.graphOn f Set.univ = ∅ := by
  ext ⟨x, y⟩
  exact isEmptyElim x

theorem no_map_to_empty [Nonempty α] [IsEmpty β] : ¬ Nonempty (α → β) := by
  rintro ⟨f⟩
  obtain ⟨x⟩ := ‹Nonempty α›
  exact isEmptyElim (f x)

theorem empty_domain_injective [IsEmpty α] (f : α → β) : Function.Injective f := by
  intro x
  exact isEmptyElim x

theorem empty_domain_surjective_iff [IsEmpty α] (f : α → β) :
    Function.Surjective f ↔ IsEmpty β := by
  constructor
  · intro h
    refine ⟨?_⟩
    intro y
    obtain ⟨x, _⟩ := h y
    exact isEmptyElim x
  · intro h y
    exact (h.false y).elim

theorem empty_self_map_bijective_and_inverse [IsEmpty α] (f : α → α) :
    Function.Bijective f ∧ isInverse f f := by
  refine ⟨⟨empty_domain_injective f, (empty_domain_surjective_iff f).mpr inferInstance⟩, ?_, ?_⟩
  · funext x
    exact isEmptyElim x
  · funext x
    exact isEmptyElim x

end Lemmatheca.SetsAndMaps
