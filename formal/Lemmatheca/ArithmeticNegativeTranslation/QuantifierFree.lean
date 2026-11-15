import Lemmatheca.ArithmeticNegativeTranslation.Conservation

namespace Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation (negative context)
universe u v
variable {α : Type u}
noncomputable section
local instance arithmeticMatrixEq {δ : Type*} : DecidableEq (Formula δ) := Classical.decEq _

/-- A finite universal prefix followed by a genuinely native quantifier-free matrix. -/
def UniversalMatrix : ∀ {n}, BF α n → Prop
  | _, .all B => UniversalMatrix B
  | _, A => A.QuantifierFree

theorem universalMatrix_map {β : Type v} {n m} (A : BF α n)
    (σ : Lemmatheca.ProofTheory.FirstOrder.ScopeSubst LA α β n m) :
    UniversalMatrix (A.map σ) ↔ UniversalMatrix A := by
  induction A generalizing m <;>
    simp_all [map, UniversalMatrix, QuantifierFree]


open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction hiding Formula

private theorem matrix_of_qf {δ : Type u} {n} (A : BF δ n) (hA : A.QuantifierFree) :
    UniversalMatrix A := by
  cases A <;> simp_all [UniversalMatrix, QuantifierFree]

private def decideDoubleNegation {δ : Type u} {Θ : Context δ}
    (D : Formula δ) (hD : D.QuantifierFree)
    (p : Certificate false Θ (.neg (.neg D))) : Certificate false Θ D := by
  apply TheoryCertificate.disjElim
    ((quantifierFreeDecision D hD).weaken (Finset.empty_subset Θ))
  · exact TheoryCertificate.assumption (by simp)
  · exact TheoryCertificate.falsumElim (TheoryCertificate.negElim
      (TheoryCertificate.assumption (A := .neg D) (by simp))
      (p.weaken (Finset.subset_insert _ _)))

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

private structure MatrixConversions {δ : Type u} (F : Formula δ) where
  forward : ∀ {Θ : Context δ}, Certificate false Θ F → Certificate false Θ (negative F)
  backward : ∀ {Θ : Context δ}, Certificate false Θ (negative F) → Certificate false Θ F

private def matrixConvertFuel : (fuel : ℕ) → {δ : Type u} → (F : Formula δ) →
    F.depth < fuel → UniversalMatrix F → MatrixConversions F
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
      let cb := matrixConvertFuel fuel B hb (matrix_of_qf B hF)
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
      let cb := matrixConvertFuel fuel B hb (matrix_of_qf B hF.1)
      let cc := matrixConvertFuel fuel C hc (matrix_of_qf C hF.2)
      exact ⟨fun p => TheoryCertificate.conjIntro
          (cb.forward (TheoryCertificate.conjLeft p)) (cc.forward (TheoryCertificate.conjRight p)),
        fun p => TheoryCertificate.conjIntro
          (cb.backward (TheoryCertificate.conjLeft p)) (cc.backward (TheoryCertificate.conjRight p))⟩
    | impl B C =>
      have hb : B.depth < fuel := by simp only [depth] at h; omega
      have hc : C.depth < fuel := by simp only [depth] at h; omega
      let cb := matrixConvertFuel fuel B hb (matrix_of_qf B hF.1)
      let cc := matrixConvertFuel fuel C hc (matrix_of_qf C hF.2)
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
      let cb := matrixConvertFuel fuel B.toFormula hb ((universalMatrix_map B _).mpr hF)
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
    | disj B C =>
      have hb : B.depth < fuel := by simp only [depth] at h; omega
      have hc : C.depth < fuel := by simp only [depth] at h; omega
      let cb := matrixConvertFuel fuel B hb (matrix_of_qf B hF.1)
      let cc := matrixConvertFuel fuel C hc (matrix_of_qf C hF.2)
      refine ⟨?_, ?_⟩
      · intro Θ p
        apply TheoryCertificate.disjElim p
        · exact doubleNegate (TheoryCertificate.disjLeft
            (cb.forward (TheoryCertificate.assumption (by simp))))
        · exact doubleNegate (TheoryCertificate.disjRight
            (cc.forward (TheoryCertificate.assumption (by simp))))
      · intro Θ p
        have nn : Certificate false Θ (.neg (.neg (.disj B C))) := by
          apply TheoryCertificate.negIntro
          have hn : Certificate false (insert (.neg (.disj B C)) Θ)
              (.neg (.disj (negative B) (negative C))) := by
            apply TheoryCertificate.negIntro
            apply TheoryCertificate.disjElim
              (TheoryCertificate.assumption (A := .disj (negative B) (negative C)) (by simp))
            · exact TheoryCertificate.negElim
                (TheoryCertificate.disjLeft (B := C)
                  (cb.backward (TheoryCertificate.assumption (by simp))))
                (TheoryCertificate.assumption (A := .neg (.disj B C)) (by simp))
            · exact TheoryCertificate.negElim
                (TheoryCertificate.disjRight (A := B)
                  (cc.backward (TheoryCertificate.assumption (by simp))))
                (TheoryCertificate.assumption (A := .neg (.disj B C)) (by simp))
          exact TheoryCertificate.negElim hn (p.weaken (Finset.subset_insert _ _))
        exact decideDoubleNegation (.disj B C) hF nn
    | ex B => exact hF.elim


def quantifierFreeToNegative {Γ : Context α} (D : Formula α) (hD : D.QuantifierFree)
    (p : Certificate false Γ D) : Certificate false Γ (negative D) := by
  exact (matrixConvertFuel (D.depth+1) D (by omega) (matrix_of_qf D hD)).forward p


def quantifierFreeFromNegative {Γ : Context α} (D : Formula α) (hD : D.QuantifierFree)
    (p : Certificate false Γ (negative D)) : Certificate false Γ D := by
  exact (matrixConvertFuel (D.depth+1) D (by omega) (matrix_of_qf D hD)).backward p


def universalMatrixToNegative {Γ : Context α} (F : Formula α) (hF : UniversalMatrix F)
    (p : Certificate false Γ F) : Certificate false Γ (negative F) := by
  exact (matrixConvertFuel (F.depth+1) F (by omega) hF).forward p


def universalMatrixFromNegative {Γ : Context α} (F : Formula α) (hF : UniversalMatrix F)
    (p : Certificate false Γ (negative F)) : Certificate false Γ F := by
  exact (matrixConvertFuel (F.depth+1) F (by omega) hF).backward p


theorem universal_matrix_native_conservation (F : Sentence) (hF : UniversalMatrix F) :
    Provable true (∅ : Context Empty) F ↔ Provable false (∅ : Context Empty) F := by
  constructor
  · rintro ⟨p⟩
    exact ⟨universalMatrixFromNegative F hF (by
      simpa only [context, Finset.image_empty] using interpret p)⟩
  · rintro ⟨p⟩
    exact ⟨p.classicalize⟩


theorem universal_matrix_pa_conservation (F : Sentence) (hF : UniversalMatrix F) :
    Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives
        Lemmatheca.ModelTheory.ArithmeticTheories.PA F.toClassical ↔
      Provable false (∅ : Context Empty) F := by
  exact (classical_iff_PA F).symm.trans (universal_matrix_native_conservation F hF)


/-- The example has a single universal followed by native excluded middle for an equation. -/
def matrixDecisionExample : Sentence :=
  allUnit (.disj (termEqual (.var (.inr ())) zeroTerm)
    (.neg (termEqual (.var (.inr ())) zeroTerm)))

theorem matrixDecisionExample_scope :
    UniversalMatrix matrixDecisionExample ∧
      ¬ DisjunctionExistentialFree matrixDecisionExample := by
  simp [matrixDecisionExample, allUnit, bindUnit, map, UniversalMatrix,
    QuantifierFree, DisjunctionExistentialFree,
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual]


/-- Even a primitive additive order abbreviation has a native existential at its root. -/
theorem additiveOrder_not_matrix (s t : LA.Term α) :
    ¬ UniversalMatrix (exUnit (termEqual
      (addTerm (.var (.inr ())) (s.relabel Sum.inl)) (t.relabel Sum.inl))) := by
  simp [UniversalMatrix, exUnit, QuantifierFree]


end
end Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
