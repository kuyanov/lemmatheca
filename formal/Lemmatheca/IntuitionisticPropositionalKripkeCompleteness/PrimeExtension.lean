import Lemmatheca.IntuitionisticPropositionalDeduction.Deduction
import Mathlib.Tactic.DeriveEncodable
import Mathlib.Data.Set.Finite.Lattice

/-! Enumerative prime extensions in the actual numbered-atom propositional language. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Canonical

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Classical

abbrev Formula := PropFormula ℕ

deriving instance Encodable for PropFormula

/-- A fixed surjective list; failed numerical decodings are replaced by falsum. -/
def formulaEnumeration (n : ℕ) : Formula :=
  (Encodable.decode (α := Formula) n).getD falsum

theorem formulaEnumeration_surjective : Function.Surjective formulaEnumeration := by
  intro A
  exact ⟨Encodable.encode A, by simp [formulaEnumeration]⟩

def DeductivelyClosed (T : Set Formula) : Prop :=
  ∀ ⦃A⦄, Derives T A → A ∈ T

def Consistent (T : Set Formula) : Prop := ¬ Derives T falsum

structure IsPrime (T : Set Formula) : Prop where
  closed : DeductivelyClosed T
  consistent : Consistent T
  disjunction : ∀ ⦃A B⦄, disj A B ∈ T → A ∈ T ∨ B ∈ T

theorem closed_mem_iff {T : Set Formula} (hT : DeductivelyClosed T) (A : Formula) :
    A ∈ T ↔ Derives T A := by
  exact ⟨Derives.assumption, fun h => hT h⟩

theorem consistent_iff_not_mem {T : Set Formula} (hT : DeductivelyClosed T) :
    Consistent T ↔ falsum ∉ T := by
  exact ⟨fun h hmem => h (.assumption hmem), fun h hd => h (hT hd)⟩

private theorem finite_subset_stage (S : ℕ → Set Formula) (hS : Monotone S)
    (D : Set Formula) (hD : D.Finite) (hsub : D ⊆ ⋃ n, S n) :
    ∃ n, D ⊆ S n := by
  induction D, hD using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert A D _ _ ih =>
      obtain ⟨n, hn⟩ := ih (fun C hC => hsub (Set.mem_insert_of_mem _ hC))
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (hsub (Set.mem_insert A D))
      refine ⟨max n m, ?_⟩
      intro C hC
      rcases hC with rfl | hC
      · exact hS (le_max_right _ _) hm
      · exact hS (le_max_left _ _) (hn hC)

theorem increasing_union_derives (S : ℕ → Set Formula) (hS : Monotone S) (A : Formula) :
    Derives (⋃ n, S n) A ↔ ∃ n, Derives (S n) A := by
  constructor
  · intro h
    obtain ⟨D, hD, hsub, hd⟩ := finite_support.mp h
    obtain ⟨n, hn⟩ := finite_subset_stage S hS D hD hsub
    exact ⟨n, hd.weaken hn⟩
  · rintro ⟨n, h⟩
    exact h.weaken (Set.subset_iUnion S n)

/-- The exact stage recurrence which inserts the next listed formula only if B stays underivable. -/
noncomputable def extensionStage (Γ : Set Formula) (B : Formula) : ℕ → Set Formula
  | 0 => Γ
  | n + 1 => if ¬ Derives (insert (formulaEnumeration n) (extensionStage Γ B n)) B
      then insert (formulaEnumeration n) (extensionStage Γ B n)
      else extensionStage Γ B n

noncomputable def extension (Γ : Set Formula) (B : Formula) : Set Formula :=
  ⋃ n, extensionStage Γ B n

theorem extensionStage_monotone (Γ : Set Formula) (B : Formula) :
    Monotone (extensionStage Γ B) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [extensionStage]
  split
  · exact Set.subset_insert _ _
  · exact Set.Subset.rfl

theorem extension_contains (Γ : Set Formula) (B : Formula) : Γ ⊆ extension Γ B := by
  exact Set.subset_iUnion (extensionStage Γ B) 0

theorem extension_not_derives {Γ : Set Formula} {B : Formula} (h : ¬ Derives Γ B) :
    ¬ Derives (extension Γ B) B := by
  have stages : ∀ n, ¬ Derives (extensionStage Γ B n) B := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
        simp only [extensionStage]
        split
        · assumption
        · exact ih
  intro hd
  obtain ⟨n, hn⟩ :=
    (increasing_union_derives _ (extensionStage_monotone Γ B) B).mp hd
  exact stages n hn

theorem extension_maximal {Γ : Set Formula} {B C : Formula}
    (hC : C ∉ extension Γ B) : Derives (insert C (extension Γ B)) B := by
  obtain ⟨n, rfl⟩ := formulaEnumeration_surjective C
  by_cases hskip : ¬ Derives (insert (formulaEnumeration n) (extensionStage Γ B n)) B
  · exfalso
    apply hC
    apply Set.mem_iUnion.mpr
    refine ⟨n + 1, ?_⟩
    simp [extensionStage, hskip]
  · have hd : Derives (insert (formulaEnumeration n) (extensionStage Γ B n)) B :=
      Classical.byContradiction hskip
    exact hd.weaken (Set.insert_subset_insert (Set.subset_iUnion (extensionStage Γ B) n))

theorem extension_prime {Γ : Set Formula} {B : Formula} (h : ¬ Derives Γ B) :
    IsPrime (extension Γ B) := by
  have hn := extension_not_derives h
  refine ⟨?_, ?_, ?_⟩
  · intro C hd
    by_contra hC
    exact hn (Derives.cut hd (extension_maximal hC))
  · intro hd
    exact hn (.falsumElim hd)
  · intro C D hCD
    by_contra hneither
    have hC : C ∉ extension Γ B := fun hC => hneither (Or.inl hC)
    have hD : D ∉ extension Γ B := fun hD => hneither (Or.inr hD)
    exact hn (.disjElim (.assumption hCD) (extension_maximal hC) (extension_maximal hD))

theorem extension_omits {Γ : Set Formula} {B : Formula} (h : ¬ Derives Γ B) :
    B ∉ extension Γ B := by
  intro hmem
  exact extension_not_derives h (.assumption hmem)

theorem missing_implication_extension {T : Set Formula} (hT : IsPrime T)
    {A B : Formula} (h : impl A B ∉ T) :
    IsPrime (extension (insert A T) B) ∧ T ⊆ extension (insert A T) B ∧
      A ∈ extension (insert A T) B ∧ B ∉ extension (insert A T) B := by
  have hn : ¬ Derives (insert A T) B := fun hd => h (hT.closed (.implIntro hd))
  refine ⟨extension_prime hn, ?_, ?_, extension_omits hn⟩
  · exact (Set.subset_insert A T).trans (extension_contains _ _)
  · exact extension_contains _ _ (Set.mem_insert A T)

theorem missing_negation_extension {T : Set Formula} (hT : IsPrime T)
    {A : Formula} (h : neg A ∉ T) :
    IsPrime (extension (insert A T) falsum) ∧
      T ⊆ extension (insert A T) falsum ∧ A ∈ extension (insert A T) falsum := by
  have hn : ¬ Derives (insert A T) falsum := fun hd => h (hT.closed (.negIntro hd))
  refine ⟨extension_prime hn, ?_, ?_⟩
  · exact (Set.subset_insert A T).trans (extension_contains _ _)
  · exact extension_contains _ _ (Set.mem_insert A T)

theorem prime_conj_iff {T : Set Formula} (hT : IsPrime T) (A B : Formula) :
    conj A B ∈ T ↔ A ∈ T ∧ B ∈ T := by
  constructor
  · intro h
    exact ⟨hT.closed (.conjElimLeft (.assumption h)),
      hT.closed (.conjElimRight (.assumption h))⟩
  · intro h
    exact hT.closed (.conjIntro (.assumption h.1) (.assumption h.2))

theorem prime_disj_iff {T : Set Formula} (hT : IsPrime T) (A B : Formula) :
    disj A B ∈ T ↔ A ∈ T ∨ B ∈ T := by
  constructor
  · exact fun h => hT.disjunction h
  · rintro (h | h)
    · exact hT.closed (.disjIntroLeft (.assumption h))
    · exact hT.closed (.disjIntroRight (.assumption h))

theorem prime_implication {T U : Set Formula} (hU : IsPrime U) (hTU : T ⊆ U)
    {A B : Formula} (h : impl A B ∈ T) (hA : A ∈ U) : B ∈ U := by
  exact hU.closed (.implElim (.assumption (hTU h)) (.assumption hA))

theorem prime_negation {T U : Set Formula} (hU : IsPrime U) (hTU : T ⊆ U)
    {A : Formula} (h : neg A ∈ T) : A ∉ U := by
  intro hA
  exact hU.consistent (.negElim (.assumption hA) (.assumption (hTU h)))

end Lemmatheca.ProofTheory.Intuitionistic.Canonical
