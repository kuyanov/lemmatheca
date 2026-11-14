import Lemmatheca.IntuitionisticPropositionalCutElimination.Calculus

namespace Lemmatheca.ProofTheory.Intuitionistic.CutFree

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

/-- The generalized replacement invariant for a single distinguished formula. -/
abbrev Replacement (A : PropFormula α) :=
  ∀ {Γ Δ : Finset (PropFormula α)} {C : PropFormula α},
    Proof Γ A → Proof Δ C → Δ ⊆ insert A Γ → Proof Γ C

/-- Principal reductions expected by the recursion on the consumer tree. -/
structure PrincipalReducers (A : PropFormula α) where
  bottom : ∀ {Γ C}, A = falsum → Proof Γ A → Proof Γ C
  conj : ∀ {Γ X Y C}, A = PropFormula.conj X Y → Proof Γ A →
    Proof (insert X (insert Y Γ)) C → Proof Γ C
  disj : ∀ {Γ X Y C}, A = PropFormula.disj X Y → Proof Γ A →
    Proof (insert X Γ) C → Proof (insert Y Γ) C → Proof Γ C
  impl : ∀ {Γ X Y C}, A = PropFormula.impl X Y → Proof Γ A →
    Proof Γ X → Proof (insert Y Γ) C → Proof Γ C
  neg : ∀ {Γ X C}, A = PropFormula.neg X → Proof Γ A → Proof Γ X → Proof Γ C

private theorem augment {Γ Δ : Finset (PropFormula α)} {A X : PropFormula α}
    (h : Δ ⊆ insert A Γ) : insert X Δ ⊆ insert A (insert X Γ) := by
  simpa only [Finset.insert_comm] using Finset.insert_subset_insert X h

private theorem augment₂ {Γ Δ : Finset (PropFormula α)} {A X Y : PropFormula α}
    (h : Δ ⊆ insert A Γ) :
    insert X (insert Y Δ) ⊆ insert A (insert X (insert Y Γ)) := by
  simpa only [Finset.insert_comm] using
    Finset.insert_subset_insert X (Finset.insert_subset_insert Y h)

private theorem subset_two (Γ : Finset (PropFormula α)) (X Y : PropFormula α) :
    Γ ⊆ insert X (insert Y Γ) :=
  (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)

/-- Recurse on a consumer, invoking the supplied handlers only at its principal uses. -/
def paste {A : PropFormula α} (r : PrincipalReducers A)
    {Γ Δ : Finset (PropFormula α)} {C : PropFormula α}
    (p : Proof Γ A) (q : Proof Δ C) (hΔ : Δ ⊆ insert A Γ) : Proof Γ C :=
  match q with
  | @Proof.atom _ _ _ a h =>
      if e : atom a = A then e.symm ▸ p
      else .atom ((Finset.mem_insert.mp (hΔ h)).resolve_left e)
  | .falsumLeft h =>
      if hΓ : falsum ∈ Γ then .falsumLeft hΓ
      else r.bottom ((Finset.mem_insert.mp (hΔ h)).resolve_right hΓ).symm p
  | @Proof.conjLeft _ _ _ X Y _ h q => by
      let q' := paste r (p.weaken (subset_two Γ X Y)) q (augment₂ hΔ)
      exact if hΓ : conj X Y ∈ Γ then .conjLeft hΓ q'
        else r.conj ((Finset.mem_insert.mp (hΔ h)).resolve_right hΓ).symm p q'
  | .conjRight q₁ q₂ => .conjRight (paste r p q₁ hΔ) (paste r p q₂ hΔ)
  | @Proof.disjLeft _ _ _ X Y _ h q₁ q₂ => by
      let qX := paste r (p.weaken (Finset.subset_insert X Γ)) q₁ (augment hΔ)
      let qY := paste r (p.weaken (Finset.subset_insert Y Γ)) q₂ (augment hΔ)
      exact if hΓ : disj X Y ∈ Γ then .disjLeft hΓ qX qY
        else r.disj ((Finset.mem_insert.mp (hΔ h)).resolve_right hΓ).symm p qX qY
  | .disjRightLeft q => .disjRightLeft (paste r p q hΔ)
  | .disjRightRight q => .disjRightRight (paste r p q hΔ)
  | @Proof.implLeft _ _ _ X Y _ h q₁ q₂ => by
      let qX := paste r p q₁ hΔ
      let qY := paste r (p.weaken (Finset.subset_insert Y Γ)) q₂ (augment hΔ)
      exact if hΓ : impl X Y ∈ Γ then .implLeft hΓ qX qY
        else r.impl ((Finset.mem_insert.mp (hΔ h)).resolve_right hΓ).symm p qX qY
  | @Proof.implRight _ _ _ X _ q =>
      .implRight (paste r (p.weaken (Finset.subset_insert X Γ)) q (augment hΔ))
  | @Proof.negLeft _ _ _ X _ h q => by
      let qX := paste r p q hΔ
      exact if hΓ : neg X ∈ Γ then .negLeft hΓ qX
        else r.neg ((Finset.mem_insert.mp (hΔ h)).resolve_right hΓ).symm p qX
  | @Proof.negRight _ _ _ X q =>
      .negRight (paste r (p.weaken (Finset.subset_insert X Γ)) q (augment hΔ))
termination_by structural q

def reduceConj {A B : PropFormula α}
    (kA : Replacement A) (kB : Replacement B)
    {Γ : Finset (PropFormula α)} {C : PropFormula α}
    (p : Proof Γ (conj A B)) (q : Proof (insert A (insert B Γ)) C) :
    Proof Γ C :=
  kB p.invertConj.2
    (kA (p.invertConj.1.weaken (Finset.subset_insert B Γ)) q (Finset.Subset.refl _))
    (Finset.Subset.refl _)

def reduceImpl {A B : PropFormula α}
    (kA : Replacement A) (kB : Replacement B)
    {Γ : Finset (PropFormula α)} {C : PropFormula α}
    (p : Proof Γ (impl A B)) (a : Proof Γ A) (q : Proof (insert B Γ) C) :
    Proof Γ C :=
  kB (kA a p.invertImpl (Finset.Subset.refl _)) q (Finset.Subset.refl _)

def reduceNeg {A : PropFormula α} (kA : Replacement A)
    {Γ : Finset (PropFormula α)} {C : PropFormula α}
    (p : Proof Γ (neg A)) (a : Proof Γ A) : Proof Γ C :=
  (kA a p.invertNeg (Finset.Subset.refl _)).explode

/-- A separate structural recursion on a disjunction producer carries both continuations. -/
def reduceDisj {A B : PropFormula α}
    (kA : Replacement A) (kB : Replacement B)
    {Γ : Finset (PropFormula α)} {C : PropFormula α}
    (p : Proof Γ (disj A B)) (qA : Proof (insert A Γ) C)
    (qB : Proof (insert B Γ) C) : Proof Γ C :=
  match p with
  | .falsumLeft h => .falsumLeft h
  | .disjRightLeft p => kA p qA (Finset.Subset.refl _)
  | .disjRightRight p => kB p qB (Finset.Subset.refl _)
  | @Proof.conjLeft _ _ _ X Y _ h p => .conjLeft h
      (reduceDisj kA kB p
        (qA.weaken (Finset.insert_subset_insert _ (subset_two Γ X Y)))
        (qB.weaken (Finset.insert_subset_insert _ (subset_two Γ X Y))))
  | @Proof.disjLeft _ _ _ X Y _ h p₁ p₂ => .disjLeft h
      (reduceDisj kA kB p₁
        (qA.weaken (Finset.insert_subset_insert _ (Finset.subset_insert X Γ)))
        (qB.weaken (Finset.insert_subset_insert _ (Finset.subset_insert X Γ))))
      (reduceDisj kA kB p₂
        (qA.weaken (Finset.insert_subset_insert _ (Finset.subset_insert Y Γ)))
        (qB.weaken (Finset.insert_subset_insert _ (Finset.subset_insert Y Γ))))
  | @Proof.implLeft _ _ _ _ Y _ h p₁ p₂ => .implLeft h p₁
      (reduceDisj kA kB p₂
        (qA.weaken (Finset.insert_subset_insert _ (Finset.subset_insert Y Γ)))
        (qB.weaken (Finset.insert_subset_insert _ (Finset.subset_insert Y Γ))))
  | .negLeft h p => .negLeft h p
termination_by sizeOf p
decreasing_by all_goals (simp_wf; omega)

/-- Formula recursion supplies all principal reducers and then pastes the consumer. -/
def Proof.replace (A : PropFormula α) : Replacement A :=
  match A with
  | .atom a => paste (A := .atom a) {
      bottom := fun h => nomatch h
      conj := fun h => nomatch h
      disj := fun h => nomatch h
      impl := fun h => nomatch h
      neg := fun h => nomatch h }
  | .falsum => paste (A := .falsum) {
      bottom := fun _ p => p.explode
      conj := fun h => nomatch h
      disj := fun h => nomatch h
      impl := fun h => nomatch h
      neg := fun h => nomatch h }
  | .conj X Y => paste (A := .conj X Y) {
      bottom := fun h => nomatch h
      conj := fun h p q => by
        cases h
        exact reduceConj (Proof.replace X) (Proof.replace Y) p q
      disj := fun h => nomatch h
      impl := fun h => nomatch h
      neg := fun h => nomatch h }
  | .disj X Y => paste (A := .disj X Y) {
      bottom := fun h => nomatch h
      conj := fun h => nomatch h
      disj := fun h p q₁ q₂ => by
        cases h
        exact reduceDisj (Proof.replace X) (Proof.replace Y) p q₁ q₂
      impl := fun h => nomatch h
      neg := fun h => nomatch h }
  | .impl X Y => paste (A := .impl X Y) {
      bottom := fun h => nomatch h
      conj := fun h => nomatch h
      disj := fun h => nomatch h
      impl := fun h p q₁ q₂ => by
        cases h
        exact reduceImpl (Proof.replace X) (Proof.replace Y) p q₁ q₂
      neg := fun h => nomatch h }
  | .neg X => paste (A := .neg X) {
      bottom := fun h => nomatch h
      conj := fun h => nomatch h
      disj := fun h => nomatch h
      impl := fun h => nomatch h
      neg := fun h p q => by
        cases h
        exact reduceNeg (Proof.replace X) p q }

/-- The split-context cut operation returns a genuine cut-free certificate. -/
def Proof.cut {Γ Δ : Finset (PropFormula α)} {A C : PropFormula α}
    (p : Proof Γ A) (q : Proof (insert A Δ) C) : Proof (Γ ∪ Δ) C :=
  Proof.replace A (p.weaken Finset.subset_union_left) q
    (Finset.insert_subset_insert _ Finset.subset_union_right)

end Lemmatheca.ProofTheory.Intuitionistic.CutFree
