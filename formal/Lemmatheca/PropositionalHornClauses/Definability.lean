import Lemmatheca.PropositionalHornClauses.PropositionalHornClauses
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Powerset

namespace Lemmatheca.MathematicalLogic.HornClauses

universe u
noncomputable section
variable {α : Type u} [DecidableEq α] [Fintype α]
attribute [local instance] Classical.propDecidable

def IntersectionClosed (𝓜 : Set (Set α)) : Prop :=
  ∀ X ∈ 𝓜, ∀ Y ∈ 𝓜, X ∩ Y ∈ 𝓜

private def allRules : Finset (Rule α) :=
  Finset.univ.biUnion fun B : Finset α =>
    (Finset.univ : Finset (Option α)).image fun h => ⟨B, h⟩

def commonTheory (𝓜 : Set (Set α)) : Finset (Rule α) :=
  allRules.filter fun r => ∀ X ∈ 𝓜, Holds r X

def definiteCommonTheory (𝓜 : Set (Set α)) : Finset (Rule α) :=
  (commonTheory 𝓜).filter fun r => r.head.isSome

theorem mem_commonTheory (𝓜 : Set (Set α)) (r : Rule α) :
    r ∈ commonTheory 𝓜 ↔ ∀ X ∈ 𝓜, Holds r X := by
  rcases r with ⟨B, h⟩
  simp [commonTheory, allRules]

theorem allowed_model_commonTheory (𝓜 : Set (Set α)) {X : Set α} (hX : X ∈ 𝓜) :
    models (commonTheory 𝓜) X := by
  intro r hr
  exact (mem_commonTheory 𝓜 r).mp hr X hX

omit [DecidableEq α] [Fintype α] in
theorem finite_nonempty_intersection (𝓜 : Set (Set α)) (h𝓜 : IntersectionClosed 𝓜)
    (A : Set (Set α)) (hfin : A.Finite) (hne : A.Nonempty) (hA : A ⊆ 𝓜) :
    ⋂₀ A ∈ 𝓜 := by
  induction A, hfin using Set.Finite.induction_on with
  | empty => simp at hne
  | @insert Y A hYA hfin ih =>
    have hY : Y ∈ 𝓜 := hA (Set.mem_insert Y A)
    by_cases hneA : A.Nonempty
    · rw [Set.sInter_insert]
      exact h𝓜 Y hY _ (ih hneA (fun Z hZ => hA (Set.mem_insert_of_mem Y hZ)))
    · have hzero : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hneA
      simpa [hzero] using hY

theorem separating_rule (𝓜 : Set (Set α)) (h𝓜 : IntersectionClosed 𝓜)
    (X : Set α) (hX : X ∉ 𝓜) :
    ∃ r : Rule α, (↑r.body : Set α) = X ∧
      r ∈ commonTheory 𝓜 ∧ ¬ Holds r X := by
  let A : Set (Set α) := {Y | Y ∈ 𝓜 ∧ X ⊆ Y}
  have hbody : (↑X.toFinset : Set α) = X := Set.coe_toFinset X
  by_cases hne : A.Nonempty
  · let C := ⋂₀ A
    have hC : C ∈ 𝓜 := finite_nonempty_intersection 𝓜 h𝓜 A
      (Set.toFinite A) hne (fun Y hY => hY.1)
    have hXC : X ⊆ C := fun p hp => Set.mem_sInter.mpr (fun Y hY => hY.2 hp)
    have hnCX : ¬C ⊆ X := by
      intro hCX
      exact hX (Set.Subset.antisymm hCX hXC ▸ hC)
    obtain ⟨p, hpC, hpX⟩ := Set.not_subset.mp hnCX
    refine ⟨⟨X.toFinset, some p⟩, hbody, ?_, ?_⟩
    · apply (mem_commonTheory 𝓜 _).mpr
      intro Y hY hb
      apply Set.mem_sInter.mp hpC Y
      exact ⟨hY, fun a ha => hb a (Set.mem_toFinset.mpr ha)⟩
    · intro h
      exact hpX (h (fun a ha => Set.mem_toFinset.mp ha))
  · refine ⟨⟨X.toFinset, none⟩, hbody, ?_, ?_⟩
    · apply (mem_commonTheory 𝓜 _).mpr
      intro Y hY hb
      exact hne ⟨Y, hY, fun a ha => hb a (Set.mem_toFinset.mpr ha)⟩
    · intro h
      exact h (fun a ha => Set.mem_toFinset.mp ha)

theorem commonTheory_models_iff (𝓜 : Set (Set α)) (h𝓜 : IntersectionClosed 𝓜)
    (X : Set α) : models (commonTheory 𝓜) X ↔ X ∈ 𝓜 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨r, _, hr, hbad⟩ := separating_rule 𝓜 h𝓜 X hn
    exact hbad (h r hr)
  · exact allowed_model_commonTheory 𝓜

theorem horn_definability (𝓜 : Set (Set α)) :
    (∃ Γ : Finset (Rule α), ∀ X : Set α, models Γ X ↔ X ∈ 𝓜) ↔
      IntersectionClosed 𝓜 := by
  constructor
  · rintro ⟨Γ, hΓ⟩ X hX Y hY
    apply (hΓ (X ∩ Y)).mp
    have h := model_intersection (↑Γ) (𝓜 := {X, Y})
      ⟨X, by simp⟩ (by
        intro Z hZ
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
        rcases hZ with hZ | hZ
        · subst Z; exact (hΓ _).mpr hX
        · subst Z; exact (hΓ _).mpr hY)
    simpa only [Set.sInter_pair, models] using h
  · intro h𝓜
    exact ⟨commonTheory 𝓜, commonTheory_models_iff 𝓜 h𝓜⟩

omit [DecidableEq α] [Fintype α] in
theorem definite_all_true [_inst : DecidableEq α] (Γ : Finset (Rule α))
    (hΓ : ∀ r ∈ Γ, r.head.isSome) : models Γ Set.univ := by
  intro r hr _
  have hh := hΓ r hr
  cases he : r.head with
  | none => simp [he] at hh
  | some p => trivial

theorem definiteCommonTheory_models_iff (𝓜 : Set (Set α))
    (h𝓜 : IntersectionClosed 𝓜) (htop : Set.univ ∈ 𝓜) (X : Set α) :
    models (definiteCommonTheory 𝓜) X ↔ X ∈ 𝓜 := by
  have he : definiteCommonTheory 𝓜 = commonTheory 𝓜 := by
    apply Finset.filter_eq_self.mpr
    intro r hr
    have h := (mem_commonTheory 𝓜 r).mp hr Set.univ htop
    cases hh : r.head with
    | none =>
      have hn := h (fun _ _ => Set.mem_univ _)
      simp [hh] at hn
    | some p => simp
  rw [he]
  exact commonTheory_models_iff 𝓜 h𝓜 X

theorem definite_common_heads (𝓜 : Set (Set α)) :
    ∀ r ∈ definiteCommonTheory 𝓜, r.head.isSome := by
  intro r hr
  exact (Finset.mem_filter.mp hr).2

theorem definite_horn_definability (𝓜 : Set (Set α)) :
    (∃ Γ : Finset (Rule α), (∀ r ∈ Γ, r.head.isSome) ∧
      ∀ X : Set α, models Γ X ↔ X ∈ 𝓜) ↔
      IntersectionClosed 𝓜 ∧ Set.univ ∈ 𝓜 := by
  constructor
  · rintro ⟨Γ, hheads, hΓ⟩
    exact ⟨horn_definability 𝓜 |>.mp ⟨Γ, hΓ⟩,
      (hΓ Set.univ).mp (definite_all_true Γ hheads)⟩
  · rintro ⟨h𝓜, htop⟩
    exact ⟨definiteCommonTheory 𝓜, definite_common_heads 𝓜,
      definiteCommonTheory_models_iff 𝓜 h𝓜 htop⟩

end
end Lemmatheca.MathematicalLogic.HornClauses
