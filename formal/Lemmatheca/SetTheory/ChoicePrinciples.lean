import Lemmatheca.SetTheory.Choice
import Mathlib.Tactic

/-! Reusable ChoicePrinciples definitions and results. -/

/-! The principle definitions are faithful universe-relative formulations.
Their equivalences over ZF are unbound corpus claims: classical Lean proves
the principles outright. The lemmas here describe constructions from supplied
data and do not certify restricted axiom strength. -/
set_option autoImplicit false
universe u
namespace Lemmatheca.SetTheory.ChoicePrinciples
open Order
open scoped Ordinal Cardinal

/-- Every pair of carriers is comparable by an injection. -/
def CardinalComparability : Prop := ∀ α β : Type u,
  Nonempty (α ↪ β) ∨ Nonempty (β ↪ α)

/-- Every chain extends to an inclusion-maximal chain. -/
def HausdorffPrinciple : Prop := ∀ (α : Type u) (p : PartialOrder α) (C : Set α),
  @IsChain α p.le C → ∃ M, C ⊆ M ∧ @IsChain α p.le M ∧
    ∀ N, @IsChain α p.le N → M ⊆ N → N = M

/-- Membership in a family is determined by its finite subsets. -/
def FiniteCharacter {α : Type u} (F : Set (Set α)) : Prop :=
  ∀ A, A ∈ F ↔ ∀ B, B.Finite → B ⊆ A → B ∈ F

/-- Every member of a nonempty finite-character family extends to a maximal member. -/
def TukeyPrinciple : Prop := ∀ (α : Type u) (F : Set (Set α)),
  F.Nonempty → FiniteCharacter F → ∀ A ∈ F, ∃ M ∈ F,
    A ⊆ M ∧ ∀ N ∈ F, M ⊆ N → N = M

/-- Chains have finite character. -/
theorem chains_finite_character (α : Type u) [PartialOrder α] :
    FiniteCharacter {C : Set α | IsChain (· ≤ ·) C} := by
  intro C
  constructor
  · intro h B _ hB
    exact h.mono hB
  · intro h a ha b hb hab
    exact h {a,b} (Set.toFinite {a,b}) (by
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact ha
        · exact Set.mem_singleton_iff.mp hz ▸ hb)
      (by simp) (by simp) hab

/-- A nonempty finite-character family contains the empty subset. -/
theorem finite_character_empty {α : Type u} (F : Set (Set α))
    (hF : F.Nonempty) (h : FiniteCharacter F) : ∅ ∈ F := by
  obtain ⟨A, hA⟩ := hF
  exact (h A).mp hA ∅ Set.finite_empty (Set.empty_subset A)

/-- In the classical carrier model, the Hartogs bound is the successor cardinal's ordinal. -/
private theorem hartogsBound_eq (α : Type u) :
    Lemmatheca.SetTheory.hartogsBound α = (Order.succ (Cardinal.mk α)).ord := by
  open Lemmatheca.SetTheory in
    apply le_antisymm
    · unfold hartogsBound
      apply csSup_le
      · exact ⟨Ordinal.type (fun _ _ : (∅ : Set α) => False) + 1,
          Ordinal.type (fun _ _ : (∅ : Set α) => False),
          ⟨∅, (fun _ _ => False), inferInstance, rfl⟩, rfl⟩
      · rintro _ ⟨o, ⟨s, r, h, rfl⟩, rfl⟩
        let := h
        change Ordinal.type r + 1 ≤ _
        apply (show Ordinal.type r < _ → Ordinal.type r + 1 ≤ _ from
          fun hlt => by simpa only [Order.succ_eq_add_one] using Order.succ_le_of_lt hlt)
        apply Cardinal.card_le_iff.mp
        rw [Ordinal.card_type]
        exact Cardinal.mk_subtype_le _
    · apply Cardinal.ord_le.mpr
      apply Order.succ_le_of_lt
      apply lt_of_not_ge
      intro hle
      have he : Nonempty ((hartogsBound α).ToType ↪ α) := by
        apply (Cardinal.le_def _ _).mp
        simpa only [Cardinal.mk_toType] using hle
      exact (hartogsBound_spec α).2.2 he

/-- Hartogs's bound is the least ordinal whose carrier does not inject into the set. -/
theorem hartogs_least (α : Type u) :
    IsLeast {a : Ordinal.{u} | ¬ Nonempty (a.ToType ↪ α)}
      (Lemmatheca.SetTheory.hartogsBound α) := by
  refine ⟨(Lemmatheca.SetTheory.hartogsBound_spec α).2.2, ?_⟩
  intro a ha
  rw [hartogsBound_eq]
  apply le_of_not_gt
  intro hlt
  have hcard := Cardinal.card_le_iff.mpr hlt
  apply ha
  apply (Cardinal.le_def _ _).mp
  simpa only [Cardinal.mk_toType] using hcard

/-- Hartogs's number of the naturals is omega one. -/
theorem hartogs_naturals :
    Lemmatheca.SetTheory.hartogsBound (ULift.{u} ℕ) = (Ordinal.omega 1 : Ordinal.{u}) := by
  rw [hartogsBound_eq]
  simp [Cardinal.succ_aleph0, Cardinal.ord_aleph]

/-- Omega one consists of the countable ordinals and is a limit beyond omega plus one. -/
theorem first_uncountable_spec :
    (∀ a : Ordinal.{u}, a < Ordinal.omega 1 ↔ Countable a.ToType) ∧
    IsSuccLimit (Ordinal.omega 1 : Ordinal.{u}) ∧
    (ω + 1 : Ordinal.{u}) < Ordinal.omega 1 := by
  refine ⟨?_, Cardinal.isSuccLimit_omega 1, ?_⟩
  · intro a
    rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType, Cardinal.card_le_iff,
      Cardinal.succ_aleph0, Cardinal.ord_aleph]
  · exact (Cardinal.isSuccLimit_omega 1).succ_lt (Ordinal.omega0_lt_omega_one)

/-- An upper bound of a maximal chain lies in the chain and is maximal in the poset. -/
theorem maximal_chain_upper_bound {α : Type u} [PartialOrder α] (C : Set α)
    (hC : IsMaxChain (· ≤ ·) C) (x : α) (hx : x ∈ upperBounds C) :
    x ∈ C ∧ IsMax x := by
  have hxC : x ∈ C := by
    have hi : insert x C = C := (hC.2
      (hC.1.insert (fun b hb _ => Or.inr (hx hb))) (Set.subset_insert _ _)).symm
    exact hi ▸ Set.mem_insert x C
  refine ⟨hxC, ?_⟩
  intro y hxy
  have hyC : y ∈ C := by
    have hi : insert y C = C := (hC.2
      (hC.1.insert (fun b hb _ => Or.inr ((hx hb).trans hxy))) (Set.subset_insert _ _)).symm
    exact hi ▸ Set.mem_insert y C
  exact hx hyC

/-- A nonempty inclusion-chain in a finite-character family has its union in the family. -/
theorem finite_character_chain_union {α : Type u} (F : Set (Set α))
    (hF : FiniteCharacter F) (C : Set (Set α)) (hne : C.Nonempty)
    (hC : C ⊆ F) (hchain : IsChain (· ⊆ ·) C) : ⋃₀ C ∈ F := by
  apply (hF _).mpr
  intro B hB hsub
  have hcontain : ∃ D ∈ C, B ⊆ D := by
    induction B, hB using Set.Finite.induction_on with
    | empty =>
      obtain ⟨D, hD⟩ := hne
      exact ⟨D, hD, Set.empty_subset _⟩
    | @insert b B hb hB ih =>
      obtain ⟨D, hD, hBD⟩ := ih (fun x hx => hsub (Set.mem_insert_of_mem _ hx))
      obtain ⟨E, hE, hbE⟩ := Set.mem_sUnion.mp (hsub (Set.mem_insert b B))
      rcases eq_or_ne D E with rfl | hDE
      · exact ⟨D, hD, Set.insert_subset hbE hBD⟩
      · rcases hchain hD hE hDE with hd | he
        · exact ⟨E, hE, Set.insert_subset hbE (hBD.trans hd)⟩
        · exact ⟨D, hD, Set.insert_subset (he hbE) hBD⟩
  obtain ⟨D, hD, hBD⟩ := hcontain
  exact (hF D).mp (hC hD) B hB hBD

/-- A graph is a partial selection if its pairs are valid and each index has at most one value. -/
def PartialSelection {ι α : Type u} (A : ι → Set α) (G : Set (ι × α)) : Prop :=
  (∀ i a, (i,a) ∈ G → a ∈ A i) ∧
  ∀ i a b, (i,a) ∈ G → (i,b) ∈ G → a = b

/-- The union of an inclusion-chain of partial selections is a partial selection, also for an empty chain. -/
theorem partial_selections_chain_union {ι α : Type u} (A : ι → Set α)
    (C : Set (Set (ι × α))) (hC : ∀ G ∈ C, PartialSelection A G)
    (hchain : IsChain (· ⊆ ·) C) : PartialSelection A (⋃₀ C) := by
  constructor
  · intro i a ha
    obtain ⟨G, hG, haG⟩ := Set.mem_sUnion.mp ha
    exact (hC G hG).1 i a haG
  · intro i a b ha hb
    obtain ⟨G, hG, haG⟩ := Set.mem_sUnion.mp ha
    obtain ⟨H, hH, hbH⟩ := Set.mem_sUnion.mp hb
    rcases eq_or_ne G H with rfl | hGH
    · exact (hC G hG).2 i a b haG hbH
    · rcases hchain hG hH hGH with hsub | hsub
      · exact (hC H hH).2 i a b (hsub haG) hbH
      · exact (hC G hG).2 i a b haG (hsub hbH)

/-- A maximal partial selection for a nonempty family is total and determines a choice function. -/
theorem maximal_partial_selection_total {ι α : Type u} (A : ι → Set α)
    (hne : ∀ i, (A i).Nonempty) (G : Set (ι × α))
    (hG : Maximal (PartialSelection A) G) :
    (∀ i, ∃ a, (i,a) ∈ G) ∧
    ∃ c : ι → α, (∀ i, c i ∈ A i) ∧ G = {p | p.2 = c p.1} := by
  classical
  have htotal : ∀ i, ∃ a, (i,a) ∈ G := by
    intro i
    by_contra hn
    obtain ⟨a, ha⟩ := hne i
    have hnew : PartialSelection A (insert (i,a) G) := by
      constructor
      · intro j b hb
        rcases hb with h | hb
        · cases h; exact ha
        · exact hG.prop.1 j b hb
      · intro j b c hb hc
        rcases hb with h | hb <;> rcases hc with h' | hc
        · exact (Prod.mk.inj h).2.trans (Prod.mk.inj h').2.symm
        · cases h
          exact False.elim (hn ⟨c, hc⟩)
        · cases h'
          exact False.elim (hn ⟨b, hb⟩)
        · exact hG.prop.2 j b c hb hc
    have hi := hG.le_of_ge hnew (Set.subset_insert _ _)
    exact hn ⟨a, hi (Set.mem_insert _ _)⟩
  have total := htotal
  choose c hc using total
  refine ⟨htotal, c, fun i => hG.prop.1 i (c i) (hc i), ?_⟩
  ext p
  constructor
  · intro hp
    exact hG.prop.2 p.1 p.2 (c p.1) hp (hc p.1)
  · intro hp
    change p.2 = c p.1 at hp
    simpa only [← hp, Prod.eta] using hc p.1

end Lemmatheca.SetTheory.ChoicePrinciples
