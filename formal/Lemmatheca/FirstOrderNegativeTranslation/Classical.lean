import Lemmatheca.FirstOrderNegativeTranslation.Translation
import Lemmatheca.IntuitionisticFirstOrderDeduction.Classical

namespace Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a b
variable {L : Language.{u,v}} {α : Type a} {e : Bool}
noncomputable section
local instance negativeClassicalFormulaEq {β : Type*} : DecidableEq (Formula L β) := Classical.decEq _

open BoundedFormula
open NaturalDeduction hiding Formula

private def classDN {δ : Type a} {Θ : NaturalDeduction.Context L δ} {F : Formula L δ}
    (p : Derivation true e L Θ F) : Derivation true e L Θ (.neg (.neg F)) :=
  .negIntro (.negElim (p.weaken (Finset.subset_insert _ _)) (.assumption (by simp)))

private theorem class_open_instance {δ : Type a} (B : BoundedFormula L δ 1) :
    (B.rename (Sum.inl : δ → δ ⊕ Fin 1)).instantiate (.var (.inr 0)) = B.toFormula := by
  unfold BoundedFormula.rename BoundedFormula.subst BoundedFormula.instantiate
    BoundedFormula.instantiateSlots BoundedFormula.toFormula
  rw [map_comp]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr i => have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl

private def classOpenAll {δ : Type a} {Θ : NaturalDeduction.Context L δ}
    (B : BoundedFormula L δ 1) (p : Derivation true e L Θ (.all B)) :
    Derivation true e L (NaturalDeduction.liftContext Θ) B.toFormula := by
  have pr := p.rename (Sum.inl : δ → δ ⊕ Fin 1)
  have pa : Derivation true e L (NaturalDeduction.liftContext Θ) (.all (B.rename Sum.inl)) := by
    simpa only [BoundedFormula.rename, BoundedFormula.subst_all, NaturalDeduction.liftContext] using pr
  have q := Derivation.allElim (.var (.inr 0)) pa
  rw [class_open_instance] at q
  exact q

private def classCloseEx {δ : Type a} {Θ : NaturalDeduction.Context L (δ ⊕ Fin 1)}
    (B : BoundedFormula L δ 1) (p : Derivation true e L Θ B.toFormula) :
    Derivation true e L Θ ((.ex B : Formula L δ).rename Sum.inl) := by
  have q : Derivation true e L Θ
      ((B.rename (Sum.inl : δ → δ ⊕ Fin 1)).instantiate (.var (.inr 0))) :=
    (class_open_instance B).symm ▸ p
  simpa only [BoundedFormula.rename, BoundedFormula.subst_ex] using
    (Derivation.exIntro (B := B.rename (Sum.inl : δ → δ ⊕ Fin 1)) (.var (.inr 0)) q)

private structure ClassicalConversions {δ : Type a} (e : Bool) (F : Formula L δ) where
  forward : ∀ {Θ : NaturalDeduction.Context L δ},
    Derivation true e L Θ F → Derivation true e L Θ (negative F)
  backward : ∀ {Θ : NaturalDeduction.Context L δ},
    Derivation true e L Θ (negative F) → Derivation true e L Θ F

private def classConvertFuel : (fuel : ℕ) → {δ : Type a} → (F : Formula L δ) →
    F.depth < fuel → ClassicalConversions e F
  | 0, _, F, h => False.elim (Nat.not_lt_zero _ h)
  | fuel+1, δ, F, h => by
    cases F with
    | falsum => exact ⟨fun p => p, fun p => p⟩
    | equal s t => exact ⟨fun p => classDN p, fun p => p.doubleNegElim⟩
    | rel R ts => exact ⟨fun p => classDN p, fun p => p.doubleNegElim⟩
    | neg B =>
      have hb : B.depth < fuel := by simp only [depth] at h; omega
      let cb := classConvertFuel fuel B hb
      refine ⟨?_, ?_⟩
      · intro Θ p
        exact .negIntro (.negElim (cb.backward (.assumption (by simp)))
          (p.weaken (Finset.subset_insert _ _)))
      · intro Θ p
        exact .negIntro (.negElim (cb.forward (.assumption (by simp)))
          (p.weaken (Finset.subset_insert _ _)))
    | conj B C =>
      have hb : B.depth < fuel := by simp only [depth] at h; omega
      have hc : C.depth < fuel := by simp only [depth] at h; omega
      let cb := classConvertFuel fuel B hb
      let cc := classConvertFuel fuel C hc
      exact ⟨fun p => .conjIntro (cb.forward (.conjElimLeft p)) (cc.forward (.conjElimRight p)),
        fun p => .conjIntro (cb.backward (.conjElimLeft p)) (cc.backward (.conjElimRight p))⟩
    | impl B C =>
      have hb : B.depth < fuel := by simp only [depth] at h; omega
      have hc : C.depth < fuel := by simp only [depth] at h; omega
      let cb := classConvertFuel fuel B hb
      let cc := classConvertFuel fuel C hc
      refine ⟨?_, ?_⟩
      · intro Θ p
        exact .impIntro (cc.forward (.impElim (p.weaken (Finset.subset_insert _ _))
          (cb.backward (.assumption (by simp)))))
      · intro Θ p
        exact .impIntro (cc.backward (.impElim (p.weaken (Finset.subset_insert _ _))
          (cb.forward (.assumption (by simp)))))
    | disj B C =>
      have hb : B.depth < fuel := by simp only [depth] at h; omega
      have hc : C.depth < fuel := by simp only [depth] at h; omega
      let cb := classConvertFuel fuel B hb
      let cc := classConvertFuel fuel C hc
      refine ⟨?_, ?_⟩
      · intro Θ p
        exact classDN (.disjElim p
          (.disjIntroLeft (cb.forward (.assumption (by simp))))
          (.disjIntroRight (cc.forward (.assumption (by simp)))))
      · intro Θ p
        exact .disjElim p.doubleNegElim
          (.disjIntroLeft (cb.backward (.assumption (by simp))))
          (.disjIntroRight (cc.backward (.assumption (by simp))))
    | all B =>
      have hb : B.toFormula.depth < fuel := by
        simp only [BoundedFormula.toFormula, depth_map]; simp only [depth] at h; omega
      let cb := classConvertFuel fuel B.toFormula hb
      refine ⟨?_, ?_⟩
      · intro Θ p
        apply Derivation.allIntro
        simpa only [negative, negative_open] using cb.forward (classOpenAll B p)
      · intro Θ p
        apply Derivation.allIntro
        have q := classOpenAll (negative B) p
        apply cb.backward
        simpa only [negative_open] using q
    | ex B =>
      have hb : B.toFormula.depth < fuel := by
        simp only [BoundedFormula.toFormula, depth_map]; simp only [depth] at h; omega
      let cb := classConvertFuel fuel B.toFormula hb
      refine ⟨?_, ?_⟩
      · intro Θ p
        apply classDN
        apply Derivation.exElim p
        apply classCloseEx (negative B)
        simpa only [negative_open] using cb.forward (.assumption (by simp))
      · intro Θ p
        apply Derivation.exElim p.doubleNegElim
        apply classCloseEx B
        apply cb.backward
        simpa only [negative_open] using
          (Derivation.assumption (Finset.mem_insert_self (negative B).toFormula
            (NaturalDeduction.liftContext Θ)))

variable {Γ : NaturalDeduction.Context L α} {A : Formula L α}

def classicalTo (A : Formula L α) (p : NaturalDeduction.Derivation true e L Γ A) :
    NaturalDeduction.Derivation true e L Γ (negative A) := by
  exact (classConvertFuel (A.depth+1) A (by omega)).forward p

def classicalFrom (A : Formula L α) (p : NaturalDeduction.Derivation true e L Γ (negative A)) :
    NaturalDeduction.Derivation true e L Γ A := by
  exact (classConvertFuel (A.depth+1) A (by omega)).backward p

/-- Reverse the constructive interpretation using actual classical assumption replacement. -/
def reflect (p : NaturalDeduction.Derivation false e L (context Γ) (negative A)) :
    NaturalDeduction.Derivation true e L Γ A := by
  apply classicalFrom A
  apply p.classicalize.replace
  intro B hB
  have hm : ∃ C, C ∈ Γ ∧ negative C = B := Finset.mem_image.mp hB
  let C := Classical.choose hm
  have hC := Classical.choose_spec hm
  exact hC.2 ▸ classicalTo C (.assumption hC.1)

theorem raw_iff (Γ : NaturalDeduction.Context L α) (A : Formula L α) :
    RawDerives true e Γ A ↔ RawDerives false e (context Γ) (negative A) := by
  exact ⟨fun ⟨p⟩ => ⟨translate p⟩, fun ⟨p⟩ => ⟨reflect p⟩⟩

/-- Use additional supplied translated-assumption proofs in a specified target context. -/
def translateUnder {Δ : NaturalDeduction.Context L α}
    (p : NaturalDeduction.Derivation true e L Γ A)
    (supply : ∀ B ∈ Γ, NaturalDeduction.Derivation false e L Δ (negative B)) :
    NaturalDeduction.Derivation false e L Δ (negative A) := by
  apply (translate p).replace
  intro C hC
  have hm : ∃ B, B ∈ Γ ∧ negative B = C := Finset.mem_image.mp hC
  let B := Classical.choose hm
  have hB := Classical.choose_spec hm
  exact hB.2 ▸ supply B hB.1

end
end Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
