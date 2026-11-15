import Lemmatheca.IntuitionisticPropositionalG4ip.Weight

namespace Lemmatheca.ProofTheory.Intuitionistic.G4ip
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

private def applyImpl {Γ : Context α} {A B : PropFormula α}
    (f : CutFree.Proof Γ (impl A B)) (a : CutFree.Proof Γ A) : CutFree.Proof Γ B :=
  CutFree.Proof.replace A a f.invertImpl (Finset.Subset.refl _)

private def replaceOne {Γ Θ : Context α} {F E : PropFormula α}
    (p : CutFree.Proof Γ E) (f : CutFree.Proof Θ F) (h : Γ.erase F ⊆ Θ) :
    CutFree.Proof Θ E :=
  CutFree.Proof.replace F f p (by
    intro X hX
    by_cases hx : X = F
    · exact Finset.mem_insert.mpr (Or.inl hx)
    · exact Finset.mem_insert.mpr (Or.inr (h (Finset.mem_erase.mpr ⟨hx, hX⟩))))

/-- Interpret the supplied primitive G4ip tree in the earlier actual cut-free calculus. -/
def Proof.toCutFree {Γ : Context α} {E : PropFormula α} (p : Proof Γ E) :
    CutFree.Proof Γ E :=
  match p with
  | .atom h => .atom h
  | .falsumLeft h => .falsumLeft h
  | .conjRight p q => .conjRight p.toCutFree q.toCutFree
  | .disjRightLeft p => .disjRightLeft p.toCutFree
  | .disjRightRight p => .disjRightRight p.toCutFree
  | .implRight p => .implRight p.toCutFree
  | .conjLeft h p => .conjLeft h (p.toCutFree.weaken (by
      intro X hX; simp only [remainder, Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto))
  | .disjLeft h p q => .disjLeft h
      (p.toCutFree.weaken (by
        intro X hX; simp only [remainder, Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto))
      (q.toCutFree.weaken (by
        intro X hX; simp only [remainder, Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto))
  | .atomImplLeft h hp p => .implLeft h (.atom hp)
      (p.toCutFree.weaken (by
        intro X hX; simp only [remainder, Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto))
  | .botImplLeft _ p => p.toCutFree.weaken (Finset.erase_subset _ _)
  | @Proof.conjImplLeft _ _ Γ A B C E h p => by
      let f : CutFree.Proof Γ (impl A (impl B C)) := .implRight (.implRight
        (.implLeft (A := conj A B) (B := C) (by simp [h])
          (.conjRight (CutFree.Proof.identity A (by simp)) (CutFree.Proof.identity B (by simp)))
          (CutFree.Proof.identity C (by simp))))
      exact replaceOne p.toCutFree f (by
        intro X hX; simp only [remainder, Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto)
  | @Proof.disjImplLeft _ _ Γ A B C E h p => by
      let fA : CutFree.Proof Γ (impl A C) := .implRight
        (.implLeft (A := disj A B) (B := C) (by simp [h]) (.disjRightLeft (CutFree.Proof.identity A (by simp)))
          (CutFree.Proof.identity C (by simp)))
      let fB : CutFree.Proof Γ (impl B C) := .implRight
        (.implLeft (A := disj A B) (B := C) (by simp [h]) (.disjRightRight (CutFree.Proof.identity B (by simp)))
          (CutFree.Proof.identity C (by simp)))
      let q := replaceOne p.toCutFree (fA.weaken (Finset.subset_insert (impl B C) Γ)) (by
        intro X hX; simp only [remainder, Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto)
      exact replaceOne q fB (by
        intro X hX; simp only [Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto)
  | @Proof.implImplLeft _ _ Γ A B C E h p q => by
      let bc : CutFree.Proof (insert A Γ) (impl B C) := .implRight
        (.implLeft (A := impl A B) (B := C) (by simp [h]) (.implRight (CutFree.Proof.identity B (by simp)))
          (CutFree.Proof.identity C (by simp)))
      let ab : CutFree.Proof (insert A Γ) (impl A B) := replaceOne p.toCutFree bc (by
        intro X hX; simp only [remainder, Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto)
      let ab' : CutFree.Proof Γ (impl A B) :=
        .implRight (applyImpl ab (CutFree.Proof.identity A (by simp)))
      let c : CutFree.Proof Γ C := applyImpl (CutFree.Proof.identity _ h) ab'
      exact replaceOne q.toCutFree c (by
        intro X hX; simp only [remainder, Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto)


/-- Inversion removes the selected conjunction, rather than merely retaining it. -/
def invertConjLeft {Γ : Context α} {A B E : PropFormula α}
    (_h : conj A B ∈ Γ) (p : CutFree.Proof Γ E) :
    CutFree.Proof (insert A (insert B (remainder Γ (conj A B)))) E := by
  apply replaceOne p (.conjRight (CutFree.Proof.identity A (by simp))
    (CutFree.Proof.identity B (by simp)))
  exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)

def invertDisjLeft {Γ : Context α} {A B E : PropFormula α}
    (_h : disj A B ∈ Γ) (p : CutFree.Proof Γ E) :
    CutFree.Proof (insert A (remainder Γ (disj A B))) E ×
    CutFree.Proof (insert B (remainder Γ (disj A B))) E := by
  constructor
  · exact replaceOne p (.disjRightLeft (CutFree.Proof.identity A (by simp)))
      (Finset.subset_insert _ _)
  · exact replaceOne p (.disjRightRight (CutFree.Proof.identity B (by simp)))
      (Finset.subset_insert _ _)

def invertAtomImplLeft {Γ : Context α} {a : α} {B E : PropFormula α}
    (_h : impl (atom a) B ∈ Γ) (_ha : atom a ∈ Γ) (p : CutFree.Proof Γ E) :
    CutFree.Proof (insert B (remainder Γ (impl (atom a) B))) E := by
  exact replaceOne p (.implRight (CutFree.Proof.identity B (by simp)))
    (Finset.subset_insert _ _)

def invertBotImplLeft {Γ : Context α} {B E : PropFormula α}
    (_h : impl falsum B ∈ Γ) (p : CutFree.Proof Γ E) :
    CutFree.Proof (remainder Γ (impl falsum B)) E := by
  exact replaceOne p (.implRight (.falsumLeft (by simp))) (Finset.Subset.refl _)

def invertConjImplLeft {Γ : Context α} {A B C E : PropFormula α}
    (_h : impl (conj A B) C ∈ Γ) (p : CutFree.Proof Γ E) :
    CutFree.Proof (insert (impl A (impl B C)) (remainder Γ (impl (conj A B) C))) E := by
  let Θ := insert (impl A (impl B C)) (remainder Γ (impl (conj A B) C))
  let ab : CutFree.Proof (insert (conj A B) Θ) (conj A B) := CutFree.Proof.identity _ (by simp)
  let curried : CutFree.Proof (insert (conj A B) Θ) (impl A (impl B C)) :=
    CutFree.Proof.identity _ (by simp [Θ])
  exact replaceOne p (.implRight (applyImpl (applyImpl curried ab.invertConj.1) ab.invertConj.2))
    (Finset.subset_insert _ _)

def invertDisjImplLeft {Γ : Context α} {A B C E : PropFormula α}
    (_h : impl (disj A B) C ∈ Γ) (p : CutFree.Proof Γ E) :
    CutFree.Proof (insert (impl A C) (insert (impl B C) (remainder Γ (impl (disj A B) C)))) E := by
  let Θ := insert (impl A C) (insert (impl B C) (remainder Γ (impl (disj A B) C)))
  let ac : CutFree.Proof (insert A (insert (disj A B) Θ)) (impl A C) :=
    CutFree.Proof.identity _ (by simp [Θ])
  let bc : CutFree.Proof (insert B (insert (disj A B) Θ)) (impl B C) :=
    CutFree.Proof.identity _ (by simp [Θ])
  let f : CutFree.Proof Θ (impl (disj A B) C) := .implRight
    (.disjLeft (by simp) (applyImpl ac (CutFree.Proof.identity A (by simp)))
      (applyImpl bc (CutFree.Proof.identity B (by simp))))
  exact replaceOne p f ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))

/-- Conditions after every closing or invertible G4ip option has been excluded. -/
structure Irreducible (Γ : Context α) (E : PropFormula α) : Prop where
  contextReduced : ReducedContext Γ
  goalReduced : NegationFree E
  noFalsum : falsum ∉ Γ
  noConj : ∀ A B, conj A B ∉ Γ
  noDisj : ∀ A B, disj A B ∉ Γ
  noBotImpl : ∀ B, impl falsum B ∉ Γ
  noConjImpl : ∀ A B C, impl (conj A B) C ∉ Γ
  noDisjImpl : ∀ A B C, impl (disj A B) C ∉ Γ
  noAtomPair : ∀ a B, impl (atom a) B ∈ Γ → atom a ∉ Γ
  noRightConj : ∀ A B, E ≠ conj A B
  noRightImpl : ∀ A B, E ≠ impl A B
  noAtomIdentity : ∀ a, E = atom a → atom a ∉ Γ

/-- The corrected producer-branch measure of a supplied old certificate. -/
def leftBranchLength {Γ : Context α} {E : PropFormula α} (p : CutFree.Proof Γ E) : ℕ :=
  match p with
  | .atom _ | .falsumLeft _ => 0
  | .conjRight p q | .disjLeft _ p q => 1 + max (leftBranchLength p) (leftBranchLength q)
  | .implLeft _ p _ => 1 + leftBranchLength p
  | .conjLeft _ p | .disjRightLeft p | .disjRightRight p | .implRight p |
      .negLeft _ p | .negRight p => 1 + leftBranchLength p

/-- Commute a last atomic implication past the left implication at its producer. -/
def atomicPermutation {Γ : Context α} {a : α} {B D F E : PropFormula α}
    (hAtom : impl (atom a) B ∈ Γ) (hOther : impl D F ∈ Γ)
    (r : CutFree.Proof Γ D) (s : CutFree.Proof (insert F Γ) (atom a))
    (q : CutFree.Proof (insert B Γ) E) : CutFree.Proof Γ E :=
  .implLeft hOther r
    (.implLeft (Finset.mem_insert_of_mem hAtom) s
      (q.weaken (by intro X hX; simp only [Finset.mem_insert] at hX ⊢; tauto)))

theorem atomicPermutation_length {Γ : Context α} {a : α} {B D F E : PropFormula α}
    (hAtom : impl (atom a) B ∈ Γ) (hOther : impl D F ∈ Γ)
    (r : CutFree.Proof Γ D) (s : CutFree.Proof (insert F Γ) (atom a))
    (q : CutFree.Proof (insert B Γ) E) :
    leftBranchLength (atomicPermutation hAtom hOther r s q) <
      leftBranchLength (CutFree.Proof.implLeft hAtom (CutFree.Proof.implLeft hOther r s) q) := by
  simp only [atomicPermutation, leftBranchLength]
  omega

/-- A final rule of one of the two irreducible non-atomic-input forms. -/
inductive Exposed (Γ : Context α) : PropFormula α → Type u
  | disjRightLeft {A B} (p : CutFree.Proof Γ A) : Exposed Γ (disj A B)
  | disjRightRight {A B} (p : CutFree.Proof Γ B) : Exposed Γ (disj A B)
  | implInput {A B C E} (h : impl (impl A B) C ∈ Γ)
      (p : CutFree.Proof Γ (impl A B)) (q : CutFree.Proof (insert C Γ) E) : Exposed Γ E

def Exposed.toCutFree {Γ : Context α} {E : PropFormula α} (p : Exposed Γ E) :
    CutFree.Proof Γ E :=
  match p with
  | .disjRightLeft p => .disjRightLeft p
  | .disjRightRight p => .disjRightRight p
  | .implInput h p q => .implLeft h p q

/-- Recursively permute the supplied tree; the inner recursion decreases leftBranchLength. -/
def expose {Γ : Context α} {E : PropFormula α} (h : Irreducible Γ E)
    (p : CutFree.Proof Γ E) : Exposed Γ E :=
  (measure (fun q : CutFree.Proof Γ E => leftBranchLength q)).wf.fix
    (C := fun _ => Exposed Γ E) (fun q recur => by
      cases q with
      | atom ha => exact (h.noAtomIdentity _ rfl ha).elim
      | falsumLeft hb => exact (h.noFalsum hb).elim
      | @conjLeft Γ A B E hf _ => exact (h.noConj A B hf).elim
      | conjRight _ _ => exact (h.noRightConj _ _ rfl).elim
      | @disjLeft Γ A B E hf _ _ => exact (h.noDisj A B hf).elim
      | disjRightLeft q => exact .disjRightLeft q
      | disjRightRight q => exact .disjRightRight q
      | implRight _ => exact (h.noRightImpl _ _ rfl).elim
      | @negLeft Γ A E hf _ => exact (h.contextReduced _ hf).elim
      | negRight _ => exact h.goalReduced.elim
      | @implLeft Γ A B E hf producer continuation =>
          cases A with
          | falsum => exact (h.noBotImpl B hf).elim
          | neg A => exact (h.contextReduced _ hf).1.elim
          | conj A D => exact (h.noConjImpl A D B hf).elim
          | disj A D => exact (h.noDisjImpl A D B hf).elim
          | impl A D => exact .implInput hf producer continuation
          | atom a =>
              cases producer with
              | atom ha => exact (h.noAtomPair a B hf ha).elim
              | falsumLeft hb => exact (h.noFalsum hb).elim
              | @conjLeft Γ A D E hg _ => exact (h.noConj A D hg).elim
              | @disjLeft Γ A D E hg _ _ => exact (h.noDisj A D hg).elim
              | @negLeft Γ A E hg _ => exact (h.contextReduced _ hg).elim
              | @implLeft Γ D F E hg r s =>
                  exact recur (atomicPermutation hf hg r s continuation)
                    (atomicPermutation_length hf hg r s continuation)) p

/-- Both exact smaller G4ip premises obtained from the old implication-input children. -/
def reduceImpInput {Γ : Context α} {A B C E : PropFormula α}
    (_h : impl (impl A B) C ∈ Γ) (p : CutFree.Proof Γ (impl A B))
    (q : CutFree.Proof (insert C Γ) E) :
    CutFree.Proof (insert (impl B C) (remainder Γ (impl (impl A B) C))) (impl A B) ×
    CutFree.Proof (insert C (remainder Γ (impl (impl A B) C))) E := by
  let Δ := remainder Γ (impl (impl A B) C)
  let Θ := insert (impl B C) Δ
  let f : CutFree.Proof (insert A Θ) (impl (impl A B) C) := .implRight
    (applyImpl (CutFree.Proof.identity (impl B C) (by simp [Θ]))
      (applyImpl (CutFree.Proof.identity (impl A B) (by simp))
        (CutFree.Proof.identity A (by simp))))
  have first : CutFree.Proof Θ (impl A B) := .implRight
    (replaceOne p.invertImpl f (by
      intro X hX; simp only [Δ, Θ, remainder, Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto))
  have second : CutFree.Proof (insert C Δ) E :=
    replaceOne q (.implRight (CutFree.Proof.identity C (by simp))) (by
      intro X hX; simp only [Δ, remainder, Finset.mem_insert, Finset.mem_erase] at hX ⊢; tauto)
  exact ⟨first, second⟩

/-- Outer recursion by sequent weight, with the supplied old tree at each goal. -/
private theorem reduced_insert {Γ : Context α} {A : PropFormula α}
    (hA : NegationFree A) (hΓ : ReducedContext Γ) : ReducedContext (insert A Γ) := by
  intro X hX
  rcases Finset.mem_insert.mp hX with rfl | hX
  · exact hA
  · exact hΓ X hX

private theorem reduced_erase {Γ : Context α} (hΓ : ReducedContext Γ) (F : PropFormula α) :
    ReducedContext (remainder Γ F) := by
  intro X hX
  exact hΓ X (Finset.mem_of_mem_erase hX)

noncomputable def fromCutFree {Γ : Context α} {E : PropFormula α}
    (hΓ : ReducedContext Γ) (hE : NegationFree E) (p : CutFree.Proof Γ E) : Proof Γ E :=
  (measure goalWeight).wf.fix
    (C := fun g : Goal α => ReducedContext g.1 → NegationFree g.2 →
      CutFree.Proof g.1 g.2 → Proof g.1 g.2)
    (fun g recur hΓ hE p => by
      classical
      obtain ⟨Γ, E⟩ := g
      by_cases hb : falsum ∈ Γ
      · exact .falsumLeft hb
      by_cases ha : ∃ a, E = atom a ∧ atom a ∈ Γ
      · let a := Classical.choose ha
        have hs := Classical.choose_spec ha
        exact hs.1.symm ▸ Proof.atom hs.2
      by_cases hrc : ∃ t : PropFormula α × PropFormula α, E = conj t.1 t.2
      · let t := Classical.choose hrc
        have he : E = conj t.1 t.2 := Classical.choose_spec hrc
        have hred : NegationFree (conj t.1 t.2) := he ▸ hE
        have old : CutFree.Proof Γ (conj t.1 t.2) := he ▸ p
        have h₁ : goalWeight (Γ, t.1) < goalWeight (Γ, E) := by
          rw [he]; exact rule_decrease (Backward.conjRightLeft Γ t.1 t.2)
        have h₂ : goalWeight (Γ, t.2) < goalWeight (Γ, E) := by
          rw [he]; exact rule_decrease (Backward.conjRightRight Γ t.1 t.2)
        exact he.symm ▸ Proof.conjRight
          (recur (Γ, t.1) h₁ hΓ hred.1 old.invertConj.1)
          (recur (Γ, t.2) h₂ hΓ hred.2 old.invertConj.2)
      by_cases hri : ∃ t : PropFormula α × PropFormula α, E = impl t.1 t.2
      · let t := Classical.choose hri
        have he : E = impl t.1 t.2 := Classical.choose_spec hri
        have hred : NegationFree (impl t.1 t.2) := he ▸ hE
        have old : CutFree.Proof Γ (impl t.1 t.2) := he ▸ p
        have hw : goalWeight (insert t.1 Γ, t.2) < goalWeight (Γ, E) := by
          rw [he]; exact rule_decrease (Backward.implRight Γ t.1 t.2)
        exact he.symm ▸ Proof.implRight
          (recur (insert t.1 Γ, t.2) hw (reduced_insert hred.1 hΓ) hred.2 old.invertImpl)
      by_cases hc : ∃ t : PropFormula α × PropFormula α, conj t.1 t.2 ∈ Γ
      · let t := Classical.choose hc
        have hf : conj t.1 t.2 ∈ Γ := Classical.choose_spec hc
        have hred := hΓ _ hf
        exact .conjLeft hf (recur _ (rule_decrease (Backward.conjLeft (E := E) hf))
          (reduced_insert hred.1 (reduced_insert hred.2 (reduced_erase hΓ _))) hE
          (invertConjLeft hf p))
      by_cases hd : ∃ t : PropFormula α × PropFormula α, disj t.1 t.2 ∈ Γ
      · let t := Classical.choose hd
        have hf : disj t.1 t.2 ∈ Γ := Classical.choose_spec hd
        have hred := hΓ _ hf
        let old := invertDisjLeft hf p
        exact .disjLeft hf
          (recur _ (rule_decrease (Backward.disjLeftLeft (E := E) hf))
            (reduced_insert hred.1 (reduced_erase hΓ _)) hE old.1)
          (recur _ (rule_decrease (Backward.disjLeftRight (E := E) hf))
            (reduced_insert hred.2 (reduced_erase hΓ _)) hE old.2)
      by_cases hat : ∃ t : α × PropFormula α, impl (atom t.1) t.2 ∈ Γ ∧ atom t.1 ∈ Γ
      · let t := Classical.choose hat
        have hs := Classical.choose_spec hat
        exact .atomImplLeft hs.1 hs.2
          (recur _ (rule_decrease (Backward.atomImplLeft (E := E) hs.1 hs.2))
            (reduced_insert (hΓ _ hs.1).2 (reduced_erase hΓ _)) hE
            (invertAtomImplLeft hs.1 hs.2 p))
      by_cases hbot : ∃ B, impl falsum B ∈ Γ
      · let B := Classical.choose hbot
        have hf : impl falsum B ∈ Γ := Classical.choose_spec hbot
        exact .botImplLeft hf (recur _ (rule_decrease (Backward.botImplLeft (E := E) hf))
          (reduced_erase hΓ _) hE (invertBotImplLeft hf p))
      by_cases hci : ∃ t : PropFormula α × PropFormula α × PropFormula α,
          impl (conj t.1 t.2.1) t.2.2 ∈ Γ
      · let t := Classical.choose hci
        have hf : impl (conj t.1 t.2.1) t.2.2 ∈ Γ := Classical.choose_spec hci
        have hred := hΓ _ hf
        exact .conjImplLeft hf
          (recur _ (rule_decrease (Backward.conjImplLeft (E := E) hf))
            (reduced_insert ⟨hred.1.1, hred.1.2, hred.2⟩ (reduced_erase hΓ _)) hE
            (invertConjImplLeft hf p))
      by_cases hdi : ∃ t : PropFormula α × PropFormula α × PropFormula α,
          impl (disj t.1 t.2.1) t.2.2 ∈ Γ
      · let t := Classical.choose hdi
        have hf : impl (disj t.1 t.2.1) t.2.2 ∈ Γ := Classical.choose_spec hdi
        have hred := hΓ _ hf
        exact .disjImplLeft hf
          (recur _ (rule_decrease (Backward.disjImplLeft (E := E) hf))
            (reduced_insert ⟨hred.1.1, hred.2⟩
              (reduced_insert ⟨hred.1.2, hred.2⟩ (reduced_erase hΓ _))) hE
            (invertDisjImplLeft hf p))
      have hir : Irreducible Γ E := {
        contextReduced := hΓ
        goalReduced := hE
        noFalsum := hb
        noConj := fun A B h => hc ⟨(A, B), h⟩
        noDisj := fun A B h => hd ⟨(A, B), h⟩
        noBotImpl := fun B h => hbot ⟨B, h⟩
        noConjImpl := fun A B C h => hci ⟨(A, B, C), h⟩
        noDisjImpl := fun A B C h => hdi ⟨(A, B, C), h⟩
        noAtomPair := fun a B h hp => hat ⟨(a, B), h, hp⟩
        noRightConj := fun A B h => hrc ⟨(A, B), h⟩
        noRightImpl := fun A B h => hri ⟨(A, B), h⟩
        noAtomIdentity := fun a h hp => ha ⟨a, h, hp⟩ }
      cases expose hir p with
      | @disjRightLeft A B old =>
          exact .disjRightLeft (recur _ (rule_decrease (Backward.disjRightLeft Γ A B)) hΓ hE.1 old)
      | @disjRightRight A B old =>
          exact .disjRightRight (recur _ (rule_decrease (Backward.disjRightRight Γ A B)) hΓ hE.2 old)
      | @implInput A B C E hf producer continuation =>
          have hred := hΓ _ hf
          let old := reduceImpInput hf producer continuation
          exact .implImplLeft hf
            (recur _ (rule_decrease (Backward.implImplLeftFirst (E := E) hf))
              (reduced_insert ⟨hred.1.2, hred.2⟩ (reduced_erase hΓ _)) hred.1 old.1)
            (recur _ (rule_decrease (Backward.implImplLeftSecond (E := E) hf))
              (reduced_insert hred.2 (reduced_erase hΓ _)) hE old.2)) (Γ, E) hΓ hE p

theorem reduced_iff {Γ : Context α} {E : PropFormula α}
    (hΓ : ReducedContext Γ) (hE : NegationFree E) :
    Nonempty (Proof Γ E) ↔ Derives (Γ : Set (PropFormula α)) E := by
  constructor
  · rintro ⟨p⟩
    exact p.toCutFree.to_natural
  · intro h
    obtain ⟨p⟩ := CutFree.from_natural h
    exact ⟨fromCutFree hΓ hE p⟩

theorem native_iff (Γ : Context α) (E : PropFormula α) :
    Derives (Γ : Set (PropFormula α)) E ↔
      Nonempty (Proof (Γ.image expandNegation) (expandNegation E)) := by
  have hΓ : ReducedContext (Γ.image expandNegation) := by
    intro A hA
    obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hA
    exact expandNegation_negationFree B
  rw [reduced_iff hΓ (expandNegation_negationFree E)]
  simpa only [Finset.coe_image] using expandNegation_derives_iff (Γ : Set (PropFormula α)) E

noncomputable def Proof.weaken {Γ Δ : Context α} {E : PropFormula α} (p : Proof Γ E)
    (h : Γ ⊆ Δ) (hΔ : ReducedContext Δ) (hE : NegationFree E) : Proof Δ E :=
  fromCutFree hΔ hE (p.toCutFree.weaken h)

noncomputable def Proof.identity {Γ : Context α} (A : PropFormula α)
    (hA : A ∈ Γ) (hΓ : ReducedContext Γ) : Proof Γ A :=
  fromCutFree hΓ (hΓ A hA) (CutFree.Proof.identity A hA)

noncomputable def Proof.cut {Γ : Context α} {A B : PropFormula α} (p : Proof Γ A)
    (q : Proof (insert A Γ) B) (hΓ : ReducedContext Γ) (hB : NegationFree B) :
    Proof Γ B :=
  fromCutFree hΓ hB (CutFree.Proof.replace A p.toCutFree q.toCutFree (Finset.Subset.refl _))

end Lemmatheca.ProofTheory.Intuitionistic.G4ip
