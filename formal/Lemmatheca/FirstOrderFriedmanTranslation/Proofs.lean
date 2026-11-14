import Lemmatheca.FirstOrderFriedmanTranslation.Syntax

/-! Actual raw proof operations. Fuel measures source formula depth only in
parameter explosion; proof translation recurses on the actual native input tree. -/
namespace Lemmatheca.ProofTheory.FirstOrder.FriedmanTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a
variable {L : Language.{u,v}} {α : Type a} {e : Bool}

noncomputable section
local instance friedmanProofFormulaEq {δ : Type*} : DecidableEq (Formula L δ) :=
  Classical.decEq _

private def parameterExplosionFuel (e : Bool) : (fuel : ℕ) → {δ : Type a} →
    (R : Formula L δ) → (r : L.Term δ) → (A : Formula L δ) → A.depth < fuel →
    NaturalDeduction.Derivation false e L {R} (formula R A)
  | 0, _, _, _, A, h => False.elim (Nat.not_lt_zero A.depth h)
  | fuel+1, δ, R, r, A, h => by
    cases A with
    | falsum => exact .assumption (Finset.mem_singleton_self _)
    | equal s t => exact .disjIntroRight (.assumption (Finset.mem_singleton_self _))
    | rel P ts => exact .disjIntroRight (.assumption (Finset.mem_singleton_self _))
    | neg A =>
        exact .impIntro (.assumption (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    | conj A B =>
        exact .conjIntro
          (parameterExplosionFuel e fuel R r A (by simp only [BoundedFormula.depth] at h; omega))
          (parameterExplosionFuel e fuel R r B (by simp only [BoundedFormula.depth] at h; omega))
    | disj A B =>
        exact .disjIntroLeft
          (parameterExplosionFuel e fuel R r A (by simp only [BoundedFormula.depth] at h; omega))
    | impl A B =>
        exact .impIntro ((parameterExplosionFuel e fuel R r B
          (by simp only [BoundedFormula.depth] at h; omega)).weaken (Finset.subset_insert _ _))
    | all B =>
        change NaturalDeduction.Derivation false e L {R} (.all (body R B))
        apply NaturalDeduction.Derivation.allIntro
        have hb : B.toFormula.depth < fuel := by
          simp only [BoundedFormula.depth] at h
          simp only [BoundedFormula.toFormula, BoundedFormula.depth_map]
          omega
        have p := parameterExplosionFuel e fuel (R.rename Sum.inl)
          (r.relabel (Sum.inl : δ → δ ⊕ Fin 1)) B.toFormula hb
        simpa only [body_open, NaturalDeduction.liftContext, Finset.image_singleton] using p
    | ex B =>
        change NaturalDeduction.Derivation false e L {R} (.ex (body R B))
        apply NaturalDeduction.Derivation.exIntro r
        rw [body_instantiate]
        apply parameterExplosionFuel e fuel R r (B.instantiate r)
        simp only [BoundedFormula.depth] at h
        simp only [BoundedFormula.instantiate, BoundedFormula.instantiateSlots,
          BoundedFormula.depth_map]
        omega

/-- The specified singleton-context proof; the original term is used by existence. -/
def parameterExplosion (e : Bool) (R : Formula L α) (r : L.Term α) (A : Formula L α) :
    NaturalDeduction.Derivation false e L {R} (formula R A) :=
  parameterExplosionFuel e (A.depth+1) R r A (Nat.lt_succ_self _)

/-- Feed the supplied parameter proof to the specified explosion construction. -/
def explode {Γ : NaturalDeduction.Context L α} (R : Formula L α) (r : L.Term α)
    (A : Formula L α) (pR : NaturalDeduction.Derivation false e L Γ R) :
    NaturalDeduction.Derivation false e L Γ (formula R A) := by
  apply (parameterExplosion e R r A).replace
  intro B hB
  rcases Finset.mem_singleton.mp hB with rfl
  exact pR

variable {Γ : NaturalDeduction.Context L α} {C : Formula L α}

def universalIntro (R : Formula L α) (B : BoundedFormula L α 1)
    (p : NaturalDeduction.Derivation false e L
      (context (R.rename Sum.inl) (NaturalDeduction.liftContext Γ))
      (formula (R.rename Sum.inl) B.toFormula)) :
    NaturalDeduction.Derivation false e L (context R Γ) (formula R (.all B)) := by
  change NaturalDeduction.Derivation false e L (context R Γ) (.all (body R B))
  apply NaturalDeduction.Derivation.allIntro
  simpa only [body_open, context_lift] using p

def universalElim (R : Formula L α) (B : BoundedFormula L α 1) (t : L.Term α)
    (p : NaturalDeduction.Derivation false e L (context R Γ) (formula R (.all B))) :
    NaturalDeduction.Derivation false e L (context R Γ) (formula R (B.instantiate t)) := by
  rw [← body_instantiate R B t]
  exact .allElim t p

def existentialIntro (R : Formula L α) (B : BoundedFormula L α 1) (t : L.Term α)
    (p : NaturalDeduction.Derivation false e L (context R Γ) (formula R (B.instantiate t))) :
    NaturalDeduction.Derivation false e L (context R Γ) (formula R (.ex B)) := by
  change NaturalDeduction.Derivation false e L (context R Γ) (.ex (body R B))
  apply NaturalDeduction.Derivation.exIntro t
  simpa only [body_instantiate] using p

def existentialElim (R : Formula L α) (B : BoundedFormula L α 1)
    (p : NaturalDeduction.Derivation false e L (context R Γ) (formula R (.ex B)))
    (pb : NaturalDeduction.Derivation false e L
      (context (R.rename Sum.inl) (insert B.toFormula (NaturalDeduction.liftContext Γ)))
      (formula (R.rename Sum.inl) (C.rename Sum.inl))) :
    NaturalDeduction.Derivation false e L (context R Γ) (formula R C) := by
  apply NaturalDeduction.Derivation.exElim (B := body R B) p
  simpa only [context_insert, context_lift, ← body_open, ← formula_rename] using pb

def equalityIntro (R : Formula L α) (t : L.Term α) (he : e = true) :
    NaturalDeduction.Derivation false e L (context R Γ)
      (formula R (NaturalDeduction.termEqual t t)) :=
  .disjIntroLeft (.equalIntro t he)

/-- The equality disjunct uses replacement in the translated body; the parameter
disjunct uses explosion with the supplied original term. -/
def equalityElim (R : Formula L α) (r : L.Term α) (B : BoundedFormula L α 1)
    (s t : L.Term α) (he : e = true)
    (peq : NaturalDeduction.Derivation false e L (context R Γ)
      (formula R (NaturalDeduction.termEqual s t)))
    (pb : NaturalDeduction.Derivation false e L (context R Γ)
      (formula R (B.instantiate s))) :
    NaturalDeduction.Derivation false e L (context R Γ) (formula R (B.instantiate t)) := by
  apply NaturalDeduction.Derivation.disjElim peq
  · rw [← body_instantiate R B t]
    apply NaturalDeduction.Derivation.equalElim (body R B) s t he
      (.assumption (Finset.mem_insert_self _ _))
    simpa only [body_instantiate] using pb.weaken (Finset.subset_insert _ _)
  · exact explode R r (B.instantiate t) (.assumption (Finset.mem_insert_self _ _))

/-- Recursion on this actual supplied intuitionistic tree, with arbitrary R,r. -/
def translate (R : Formula L α) (r : L.Term α) {A : Formula L α}
    (p : NaturalDeduction.Derivation false e L Γ A) :
    NaturalDeduction.Derivation false e L (context R Γ) (formula R A) := by
  clear C
  revert R r
  induction p with
  | assumption hA =>
      intro R r
      exact .assumption (Finset.mem_image.mpr ⟨_, hA, rfl⟩)
  | conjIntro _ _ ihA ihB => intro R r; exact .conjIntro (ihA R r) (ihB R r)
  | conjElimLeft _ ih => intro R r; exact .conjElimLeft (ih R r)
  | conjElimRight _ ih => intro R r; exact .conjElimRight (ih R r)
  | disjIntroLeft _ ih => intro R r; exact .disjIntroLeft (ih R r)
  | disjIntroRight _ ih => intro R r; exact .disjIntroRight (ih R r)
  | disjElim _ _ _ ihAB ihA ihB =>
      intro R r
      apply NaturalDeduction.Derivation.disjElim (ihAB R r)
      · simpa only [context_insert] using ihA R r
      · simpa only [context_insert] using ihB R r
  | impIntro _ ih =>
      intro R r
      apply NaturalDeduction.Derivation.impIntro
      simpa only [context_insert] using ih R r
  | impElim _ _ ihAB ihA => intro R r; exact .impElim (ihAB R r) (ihA R r)
  | negIntro _ ih =>
      intro R r
      apply NaturalDeduction.Derivation.impIntro
      simpa only [context_insert, formula] using ih R r
  | negElim _ _ ihA ihnA => intro R r; exact .impElim (ihnA R r) (ihA R r)
  | falsumElim _ ih => intro R r; exact explode R r _ (ih R r)
  | classicalContradiction hc _ _ => cases hc
  | allElim t _ ih => intro R r; exact universalElim R _ t (ih R r)
  | exIntro t _ ih => intro R r; exact existentialIntro R _ t (ih R r)
  | allIntro _ ih =>
      intro R r
      exact universalIntro R _ (ih (R.rename Sum.inl) (r.relabel Sum.inl))
  | exElim _ _ ihEx ihB =>
      intro R r
      exact existentialElim R _ (ihEx R r) (ihB (R.rename Sum.inl) (r.relabel Sum.inl))
  | equalIntro t he => intro R r; exact equalityIntro R t he
  | equalElim B s t he _ _ ihEq ihB =>
      intro R r
      exact equalityElim R r B s t he (ihEq R r) (ihB R r)

end
end Lemmatheca.ProofTheory.FirstOrder.FriedmanTranslation
