import Mathlib.ModelTheory.Definability
import Mathlib.ModelTheory.Encoding
import Lemmatheca.FirstOrderStructures.FirstOrderSemantics

open Lemmatheca.MathematicalLogic

/-! Definability, parameter-preserving automorphisms, and the cardinal bound on descriptions. -/

namespace Lemmatheca.ModelTheory.Definability

open FirstOrder FirstOrder.Language Cardinal

universe u v w u'

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]
variable {α : Type u'} {A : Set M} {s : Set (α → M)}

/-- An automorphism leaves each allowed parameter unchanged. -/
def Fixes (g : M → M) (A : Set M) : Prop := ∀ a ∈ A, g a = a

/-- Membership is unchanged when a map acts on every tuple coordinate. -/
def Invariant (g : M → M) (s : Set (α → M)) : Prop :=
  ∀ x, x ∈ s ↔ g ∘ x ∈ s

/-- A structure is rigid when every automorphism is the identity on its carrier. -/
def Rigid (L : Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ g : M ≃[L] M, ∀ x, g x = x

theorem fixes_symm (g : M ≃[L] M) (h : Fixes g A) : Fixes g.symm A := by
  intro a ha
  apply g.injective
  simpa using (h a ha).symm

theorem invariant_iff_image_eq (g : M ≃[L] M) :
    Invariant g s ↔ (fun x : α → M => g ∘ x) '' s = s := by
  constructor
  · intro h
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).mp hx
    · intro hy
      have hcomp : g ∘ (g.symm ∘ y) = y := by funext i; simp
      refine ⟨g.symm ∘ y, ?_, hcomp⟩
      exact (h (g.symm ∘ y)).mpr (hcomp.symm ▸ hy)
  · intro h x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have : y = x := by
        funext i
        exact g.injective (congrFun hxy i)
      exact this ▸ hy

theorem definable_invariant (hs : A.Definable L s) (g : M ≃[L] M)
    (hg : Fixes g A) : Invariant g s := by
  obtain ⟨φ, rfl⟩ := Set.definable_iff_exists_formula_sum.mp hs
  intro x
  change φ.Realize (Sum.elim (Subtype.val : A → M) x) ↔ φ.Realize (Sum.elim (Subtype.val : A → M) (g ∘ x))
  have heq : Sum.elim (Subtype.val : A → M) (g ∘ x) = g ∘ Sum.elim (Subtype.val : A → M) x := by
    funext a
    cases a with
    | inl a => exact (hg a a.property).symm
    | inr i => rfl
  rw [heq]
  exact (StrongHomClass.realize_formula g φ).symm

theorem finite_definable₁ (s : Set M) (hs : s.Finite) :
    (Set.univ : Set M).Definable₁ L s := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    exact Set.definable_empty (A := Set.univ) (L := L) (α := Fin 1)
  | @insert a s _ _ ih =>
    have ha := Set.Definable.singleton_of_mem (L := L) (Set.mem_univ a)
    change (Set.univ : Set M).Definable L {x : Fin 1 → M | x 0 ∈ insert a s}
    convert ha.union ih using 1
    ext x
    simp

section CardinalBounds

variable {L : Language.{u, u}} {M : Type u} [L.Structure M]

theorem card_definable_subsets_le [Infinite M] [Countable L.Symbols] :
    #{s : Set M // (Set.univ : Set M).Definable₁ L s} ≤ #M := by
  classical
  let Φ := L[[(Set.univ : Set M)]].Formula (Fin 1)
  let decode : Φ → {s : Set M // (Set.univ : Set M).Definable₁ L s} := fun φ =>
    ⟨{m | φ.Realize (fun _ => m)}, φ, by
      ext x
      have hx : (fun _ : Fin 1 => x 0) = x := by funext i; congr; exact Subsingleton.elim _ _
      simp only [Set.mem_ofPred_eq]
      rw [hx]⟩
  have hsurj : Function.Surjective decode := by
    rintro ⟨s, hs⟩
    obtain ⟨φ, hφ⟩ := hs
    refine ⟨φ, Subtype.ext ?_⟩
    ext m
    have hm := congrArg (fun t : Set (Fin 1 → M) => (fun _ => m) ∈ t) hφ
    change φ.Realize (fun _ => m) ↔ m ∈ s
    exact Iff.of_eq (by simpa only [Set.mem_ofPred_eq] using hm.symm)
  have hM : ℵ₀ ≤ #M := Cardinal.aleph0_le_mk M
  have hL : L.card ≤ #M := Cardinal.mk_le_aleph0.trans hM
  have hparams : L[[(Set.univ : Set M)]].card ≤ #M := by
    rw [Language.card_withConstants]
    simp only [Cardinal.lift_id, Cardinal.mk_univ]
    exact Cardinal.add_le_of_le hM hL le_rfl
  have hform : #Φ ≤ #M := by
    have hsig : #Φ ≤ #(Σ n, L[[(Set.univ : Set M)]].BoundedFormula (Fin 1) n) :=
      Cardinal.mk_le_of_injective (f := fun φ => (⟨0, φ⟩ : Σ n,
        L[[(Set.univ : Set M)]].BoundedFormula (Fin 1) n)) sigma_mk_injective
    refine hsig.trans (BoundedFormula.card_le.trans ?_)
    simp only [Cardinal.mk_fin, Cardinal.lift_natCast]
    exact max_le hM (Cardinal.add_le_of_le hM (Cardinal.one_le_aleph0.trans hM) (by simpa using hparams))
  exact (Cardinal.mk_le_of_surjective hsurj).trans hform

theorem exists_undefinable_subset [Infinite M] [Countable L.Symbols] :
    ∃ s : Set M, ¬ (Set.univ : Set M).Definable₁ L s := by
  classical
  by_contra h
  push Not at h
  let e : Set M ↪ {s : Set M // (Set.univ : Set M).Definable₁ L s} :=
    ⟨fun s => ⟨s, h s⟩, fun _ _ heq => congrArg Subtype.val heq⟩
  have hle : #(Set M) ≤ #M :=
    (Cardinal.mk_le_of_injective e.injective).trans card_definable_subsets_le
  rw [Cardinal.mk_set] at hle
  exact (Cardinal.cantor #M).not_ge hle

end CardinalBounds

end Lemmatheca.ModelTheory.Definability
