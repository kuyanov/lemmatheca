import Lemmatheca.ArithmeticNegativeTranslation.Interpretation

namespace Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation (negative context)
universe u v
variable {α : Type u}
noncomputable section
local instance arithmeticNegativeConservationFormulaEq {β : Type*} : DecidableEq (Formula β) := Classical.decEq _

/-- Inspect the entire native tree, including inside negations and binders. -/
def DisjunctionExistentialFree : ∀ {n}, BF α n → Prop
  | _, .falsum | _, .equal _ _ => True
  | _, .rel _ _ => False
  | _, .neg A | _, .all A => DisjunctionExistentialFree A
  | _, .conj A B | _, .impl A B =>
      DisjunctionExistentialFree A ∧ DisjunctionExistentialFree B
  | _, .disj _ _ | _, .ex _ => False

theorem fragment_map {β : Type v} {n m} (A : BF α n)
    (σ : Lemmatheca.ProofTheory.FirstOrder.ScopeSubst LA α β n m) :
    DisjunctionExistentialFree (A.map σ) ↔ DisjunctionExistentialFree A := by
  induction A generalizing m <;>
    simp_all [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, DisjunctionExistentialFree]

theorem fragment_open {n} (A : BF α n) :
    DisjunctionExistentialFree A.toFormula ↔ DisjunctionExistentialFree A := by
  exact fragment_map A _

theorem fragment_ofClassical {n} (D : LA.BoundedFormula α n) :
    DisjunctionExistentialFree
      (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D) := by
  induction D with
  | falsum => trivial
  | equal s t => trivial
  | rel R ts => exact R.elim
  | imp A B ihA ihB => exact ⟨ihA, ihB⟩
  | all A ih => exact ih

open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction hiding Formula

private def doubleNegate {δ : Type u} {Θ : Context δ} {F : Formula δ}
    (p : Certificate false Θ F) : Certificate false Θ (.neg (.neg F)) :=
  TheoryCertificate.negIntro (TheoryCertificate.negElim
    (p.weaken (Finset.subset_insert _ _))
    (TheoryCertificate.assumption (Finset.mem_insert_self _ _)))

private theorem removeEmptySlots (s : LA.Term (α ⊕ Fin 0)) :
    (s.relabel (Sum.elim id Fin.elim0)).relabel (Sum.inl : α → α ⊕ Fin 0) = s := by
  rw [Term.relabel_relabel]
  have h : ((Sum.inl : α → α ⊕ Fin 0) ∘ Sum.elim id Fin.elim0) = id := by
    funext x
    cases x with
    | inl a => rfl
    | inr i => exact i.elim0
  rw [h, Term.relabel_id]

private theorem openInstance {δ : Type u} (B : BF δ 1) :
    (B.rename (Sum.inl : δ → δ ⊕ Fin 1)).instantiate (.var (.inr 0)) = B.toFormula := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
  rw [map_comp]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr i => have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl

private def openAll {δ : Type u} {Θ : Context δ} (B : BF δ 1)
    (p : Certificate false Θ (.all B)) :
    Certificate false (Θ.image (fun A => A.rename (Sum.inl : δ → δ ⊕ Fin 1))) B.toFormula := by
  have pr := p.rename (Sum.inl : δ → δ ⊕ Fin 1)
  have pa : Certificate false (Θ.image (fun A => A.rename (Sum.inl : δ → δ ⊕ Fin 1)))
      (.all (B.rename Sum.inl)) := by
    simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, subst_all] using pr
  have q := TheoryCertificate.allElim (.var (.inr 0)) pa
  rw [openInstance] at q
  exact q

private structure FragmentConversions {δ : Type u} (F : Formula δ) where
  forward : ∀ {Θ : Context δ}, Certificate false Θ F → Certificate false Θ (negative F)
  backward : ∀ {Θ : Context δ}, Certificate false Θ (negative F) → Certificate false Θ F

private def convertFuel : (fuel : ℕ) → {δ : Type u} → (F : Formula δ) →
    F.depth < fuel → DisjunctionExistentialFree F → FragmentConversions F
  | 0, _, F, h, _ => False.elim (Nat.not_lt_zero _ h)
  | fuel+1, δ, F, h, hF => by
    cases F with
    | falsum => exact ⟨fun p => p, fun p => p⟩
    | equal s t =>
      refine ⟨fun p => doubleNegate p, ?_⟩
      intro Θ p
      have q : Certificate false (∅ : Context δ)
          (.impl (.neg (.neg (.equal s t))) (.equal s t)) := by
        simpa only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual,
          removeEmptySlots] using
          atomicDoubleNegation (s.relabel (Sum.elim id Fin.elim0))
            (t.relabel (Sum.elim id Fin.elim0))
      exact TheoryCertificate.impElim (q.weaken (Finset.empty_subset _)) p
    | rel R ts => exact R.elim
    | neg B =>
      have hb : B.depth < fuel := by simp only [depth] at h; omega
      let cb := convertFuel fuel B hb hF
      refine ⟨?_, ?_⟩
      · intro Θ p
        exact TheoryCertificate.negIntro (TheoryCertificate.negElim
          (cb.backward (TheoryCertificate.assumption (by simp)))
          (p.weaken (Finset.subset_insert _ _)))
      · intro Θ p
        exact TheoryCertificate.negIntro (TheoryCertificate.negElim
          (cb.forward (TheoryCertificate.assumption (by simp)))
          (p.weaken (Finset.subset_insert _ _)))
    | conj B C =>
      have hb : B.depth < fuel := by simp only [depth] at h; omega
      have hc : C.depth < fuel := by simp only [depth] at h; omega
      let cb := convertFuel fuel B hb hF.1
      let cc := convertFuel fuel C hc hF.2
      exact ⟨fun p => TheoryCertificate.conjIntro
          (cb.forward (TheoryCertificate.conjLeft p)) (cc.forward (TheoryCertificate.conjRight p)),
        fun p => TheoryCertificate.conjIntro
          (cb.backward (TheoryCertificate.conjLeft p)) (cc.backward (TheoryCertificate.conjRight p))⟩
    | impl B C =>
      have hb : B.depth < fuel := by simp only [depth] at h; omega
      have hc : C.depth < fuel := by simp only [depth] at h; omega
      let cb := convertFuel fuel B hb hF.1
      let cc := convertFuel fuel C hc hF.2
      refine ⟨?_, ?_⟩
      · intro Θ p
        exact TheoryCertificate.impIntro (cc.forward (TheoryCertificate.impElim
          (p.weaken (Finset.subset_insert _ _))
          (cb.backward (TheoryCertificate.assumption (by simp)))))
      · intro Θ p
        exact TheoryCertificate.impIntro (cc.backward (TheoryCertificate.impElim
          (p.weaken (Finset.subset_insert _ _))
          (cb.forward (TheoryCertificate.assumption (by simp)))))
    | all B =>
      have hb : B.toFormula.depth < fuel := by
        simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula, depth_map]
        simp only [depth] at h
        omega
      let cb := convertFuel fuel B.toFormula hb ((fragment_open B).mpr hF)
      refine ⟨?_, ?_⟩
      · intro Θ p
        apply TheoryCertificate.allIntro
        simpa only [negative, Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation.negative_open]
          using cb.forward (openAll B p)
      · intro Θ p
        apply TheoryCertificate.allIntro
        apply cb.backward
        simpa only [Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation.negative_open]
          using openAll (negative B) p
    | disj B C => exact hF.elim
    | ex B => exact hF.elim

variable {Γ : Context α}

/-- Actual constructive conversions work uniformly under arbitrary additional assumptions. -/
def toNegative (F : Formula α) (hF : DisjunctionExistentialFree F)
    (p : Certificate false Γ F) : Certificate false Γ (negative F) := by
  exact (convertFuel (F.depth+1) F (by omega) hF).forward p

def fromNegative (F : Formula α) (hF : DisjunctionExistentialFree F)
    (p : Certificate false Γ (negative F)) : Certificate false Γ F := by
  exact (convertFuel (F.depth+1) F (by omega) hF).backward p

theorem native_conservation (F : Sentence) (hF : DisjunctionExistentialFree F) :
    Provable true (∅ : Context Empty) F ↔ Provable false (∅ : Context Empty) F := by
  constructor
  · rintro ⟨p⟩
    exact ⟨fromNegative F hF (by
      simpa only [context, Finset.image_empty] using interpret p)⟩
  · rintro ⟨p⟩
    exact ⟨p.classicalize⟩

theorem pa_conservation (F : Sentence) (hF : DisjunctionExistentialFree F) :
    Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives
        Lemmatheca.ModelTheory.ArithmeticTheories.PA F.toClassical ↔
      Provable false (∅ : Context Empty) F := by
  exact (classical_iff_PA F).symm.trans (native_conservation F hF)

end
end Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
