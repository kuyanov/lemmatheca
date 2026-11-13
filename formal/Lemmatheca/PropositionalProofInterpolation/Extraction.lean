import Lemmatheca.ClassicalPropositionalSequents.Properties
import Lemmatheca.PropositionalCutElimination.Transformations

/-! Specified Maehara extraction with covering finite-set splits. -/
namespace Lemmatheca.ProofTheory.ClassicalPropositional.Interpolation

universe u
variable {α : Type u} [DecidableEq α]

/-- All underlying atom names on a finite side, without signs. -/
def vocabulary (Γ : Sequent α) : Finset α := Γ.biUnion Nnf.atoms

/-- The induction permits overlap and extra alternatives in the two sides. -/
def Covers (Γ L R : Sequent α) : Prop := Γ ⊆ L ∪ R

/-- The actual middle formula, both primitive trees, and the common-vocabulary bound. -/
structure Witness (L R : Sequent α) where
  formula : Nnf α
  leftProof : Proof (insert formula L)
  rightProof : Proof (insert formula.dual R)
  common : formula.atoms ⊆ vocabulary L ∩ vocabulary R

private theorem vocabulary_insert (Γ : Sequent α) (A : Nnf α) :
    vocabulary (insert A Γ) = A.atoms ∪ vocabulary Γ := by
  simp [vocabulary]

private theorem atoms_of_mem {Γ : Sequent α} {A : Nnf α} (h : A ∈ Γ) :
    A.atoms ⊆ vocabulary Γ := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨A, h, hp⟩

private theorem drop_cover {Γ L R : Sequent α} {D : Nnf α}
    (h : Covers (insert D Γ) L R) : Covers Γ L R := by
  intro A hA
  exact h (Finset.mem_insert_of_mem hA)

private theorem insert_cover_left {Γ L R : Sequent α}
    (h : Covers Γ L R) (A : Nnf α) : Covers (insert A Γ) (insert A L) R := by
  intro B hB
  rcases Finset.mem_insert.mp hB with rfl | hB
  · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  · rcases Finset.mem_union.mp (h hB) with hL | hR
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hL)
    · exact Finset.mem_union_right _ hR

private theorem insert_cover_right {Γ L R : Sequent α}
    (h : Covers Γ L R) (A : Nnf α) : Covers (insert A Γ) L (insert A R) := by
  intro B hB
  rcases Finset.mem_insert.mp hB with rfl | hB
  · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  · rcases Finset.mem_union.mp (h hB) with hL | hR
    · exact Finset.mem_union_left _ hL
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hR)

private theorem principal_right {Γ L R : Sequent α} {D : Nnf α}
    (h : Covers (insert D Γ) L R) (hn : D ∉ L) : D ∈ R := by
  exact (Finset.mem_union.mp (h (Finset.mem_insert_self _ _))).resolve_left hn

/-- Structural context extension followed by the primitive disjunction rule. -/
def promoteLeft {Γ : Sequent α} {X Y : Nnf α} (p : Proof (insert X Γ)) :
    Proof (insert (.or X Y) Γ) := by
  apply Proof.orIntro
  have q := p.addContext {Y}
  simpa [Finset.union_singleton, Finset.insert_comm] using q

/-- The symmetric structural construction, preserving the prescribed disjunct order. -/
def promoteRight {Γ : Sequent α} {X Y : Nnf α} (p : Proof (insert Y Γ)) :
    Proof (insert (.or X Y) Γ) := by
  apply Proof.orIntro
  have q := p.addContext {X}
  simpa [Finset.union_singleton, Finset.insert_comm] using q

/-- The four ordered membership tests from the atomic-leaf table. -/
def atomic (p : α) (L R : Sequent α)
    (hp : Nnf.pos p ∈ L ∪ R) (hn : Nnf.neg p ∈ L ∪ R) : Witness L R :=
  if hpl : Nnf.pos p ∈ L then
    if hnl : Nnf.neg p ∈ L then
      { formula := .bot
        leftProof := .identity p (by simp [hpl]) (by simp [hnl])
        rightProof := .truth (by simp [Nnf.dual])
        common := by
          simp [Nnf.atoms] }
    else
      { formula := .neg p
        leftProof := .identity p (by simp [hpl]) (by simp)
        rightProof := .identity p (by simp [Nnf.dual])
          (Finset.mem_insert_of_mem ((Finset.mem_union.mp hn).resolve_left hnl))
        common := by
          simp only [Nnf.atoms, Finset.singleton_subset_iff, Finset.mem_inter]
          exact ⟨atoms_of_mem hpl (by simp [Nnf.atoms]),
            atoms_of_mem ((Finset.mem_union.mp hn).resolve_left hnl) (by simp [Nnf.atoms])⟩ }
  else
    if hnl : Nnf.neg p ∈ L then
      { formula := .pos p
        leftProof := .identity p (by simp) (by simp [hnl])
        rightProof := .identity p
          (Finset.mem_insert_of_mem ((Finset.mem_union.mp hp).resolve_left hpl))
          (by simp [Nnf.dual])
        common := by
          simp only [Nnf.atoms, Finset.singleton_subset_iff, Finset.mem_inter]
          exact ⟨atoms_of_mem hnl (by simp [Nnf.atoms]),
            atoms_of_mem ((Finset.mem_union.mp hp).resolve_left hpl) (by simp [Nnf.atoms])⟩ }
    else
      { formula := .top
        leftProof := .truth (by simp)
        rightProof := .identity p
          (Finset.mem_insert_of_mem ((Finset.mem_union.mp hp).resolve_left hpl))
          (Finset.mem_insert_of_mem ((Finset.mem_union.mp hn).resolve_left hnl))
        common := by
          simp [Nnf.atoms] }

/-- Truth selects a constant by testing the left side first. -/
def truth (L R : Sequent α) (ht : Nnf.top ∈ L ∪ R) : Witness L R :=
  if htl : Nnf.top ∈ L then
    { formula := .bot
      leftProof := .truth (Finset.mem_insert_of_mem htl)
      rightProof := .truth (by simp [Nnf.dual])
      common := by
        simp [Nnf.atoms] }
  else
    { formula := .top
      leftProof := .truth (by simp)
      rightProof := .truth (Finset.mem_insert_of_mem ((Finset.mem_union.mp ht).resolve_left htl))
      common := by
        simp [Nnf.atoms] }

/-- Restore a left principal disjunction without deleting a retained copy. -/
def disjunctionLeft {L R : Sequent α} {A B : Nnf α} (hD : Nnf.or A B ∈ L)
    (w : Witness (insert A (insert B L)) R) : Witness L R where
  formula := w.formula
  leftProof := by
    have p : Proof (insert A (insert B (insert w.formula L))) := by
      simpa [Finset.insert_comm] using w.leftProof
    have q := Proof.orIntro p
    simpa [Finset.insert_comm, hD] using q
  rightProof := w.rightProof
  common := by
    have ha : A.atoms ⊆ vocabulary L := fun p hp => atoms_of_mem hD (Finset.mem_union_left _ hp)
    have hb : B.atoms ⊆ vocabulary L := fun p hp => atoms_of_mem hD (Finset.mem_union_right _ hp)
    have hsub : vocabulary (insert A (insert B L)) ⊆ vocabulary L := by
      rw [vocabulary_insert, vocabulary_insert]
      exact Finset.union_subset ha (Finset.union_subset hb Finset.Subset.rfl)
    intro p hp
    have h := Finset.mem_inter.mp (w.common hp)
    exact Finset.mem_inter.mpr ⟨hsub h.1, h.2⟩

/-- Restore a right principal disjunction, retaining the prescribed interpolant. -/
def disjunctionRight {L R : Sequent α} {A B : Nnf α} (hD : Nnf.or A B ∈ R)
    (w : Witness L (insert A (insert B R))) : Witness L R where
  formula := w.formula
  leftProof := w.leftProof
  rightProof := by
    have p : Proof (insert A (insert B (insert w.formula.dual R))) := by
      simpa [Finset.insert_comm] using w.rightProof
    have q := Proof.orIntro p
    simpa [Finset.insert_comm, hD] using q
  common := by
    have ha : A.atoms ⊆ vocabulary R := fun p hp => atoms_of_mem hD (Finset.mem_union_left _ hp)
    have hb : B.atoms ⊆ vocabulary R := fun p hp => atoms_of_mem hD (Finset.mem_union_right _ hp)
    have hsub : vocabulary (insert A (insert B R)) ⊆ vocabulary R := by
      rw [vocabulary_insert, vocabulary_insert]
      exact Finset.union_subset ha (Finset.union_subset hb Finset.Subset.rfl)
    intro p hp
    have h := Finset.mem_inter.mp (w.common hp)
    exact Finset.mem_inter.mpr ⟨h.1, hsub h.2⟩

/-- A left principal conjunction combines the extracted formulas by disjunction. -/
def conjunctionLeft {L R : Sequent α} {A B : Nnf α} (hD : Nnf.and A B ∈ L)
    (wA : Witness (insert A L) R) (wB : Witness (insert B L) R) : Witness L R where
  formula := .or wA.formula wB.formula
  leftProof := by
    have pa : Proof (insert A (insert (.or wA.formula wB.formula) L)) := by
      simpa [Finset.insert_comm] using
        (promoteLeft (Y := wB.formula) wA.leftProof)
    have pb : Proof (insert B (insert (.or wA.formula wB.formula) L)) := by
      simpa [Finset.insert_comm] using
        (promoteRight (X := wA.formula) wB.leftProof)
    have q := Proof.andIntro pa pb
    simpa [Finset.insert_comm, hD] using q
  rightProof := Proof.andIntro wA.rightProof wB.rightProof
  common := by
    have ha : A.atoms ⊆ vocabulary L := fun p hp => atoms_of_mem hD (Finset.mem_union_left _ hp)
    have hb : B.atoms ⊆ vocabulary L := fun p hp => atoms_of_mem hD (Finset.mem_union_right _ hp)
    have hsubA : vocabulary (insert A L) ⊆ vocabulary L := by
      rw [vocabulary_insert]
      exact Finset.union_subset ha Finset.Subset.rfl
    have hsubB : vocabulary (insert B L) ⊆ vocabulary L := by
      rw [vocabulary_insert]
      exact Finset.union_subset hb Finset.Subset.rfl
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have h := Finset.mem_inter.mp (wA.common hp)
      exact Finset.mem_inter.mpr ⟨hsubA h.1, h.2⟩
    · have h := Finset.mem_inter.mp (wB.common hp)
      exact Finset.mem_inter.mpr ⟨hsubB h.1, h.2⟩

/-- A right principal conjunction combines the extracted formulas by conjunction. -/
def conjunctionRight {L R : Sequent α} {A B : Nnf α} (hD : Nnf.and A B ∈ R)
    (wA : Witness L (insert A R)) (wB : Witness L (insert B R)) : Witness L R where
  formula := .and wA.formula wB.formula
  leftProof := Proof.andIntro wA.leftProof wB.leftProof
  rightProof := by
    have pa : Proof (insert A (insert (.or wA.formula.dual wB.formula.dual) R)) := by
      simpa [Finset.insert_comm] using
        (promoteLeft (Y := wB.formula.dual) wA.rightProof)
    have pb : Proof (insert B (insert (.or wA.formula.dual wB.formula.dual) R)) := by
      simpa [Finset.insert_comm] using
        (promoteRight (X := wA.formula.dual) wB.rightProof)
    have q := Proof.andIntro pa pb
    simpa [Finset.insert_comm, hD, Nnf.dual] using q
  common := by
    have ha : A.atoms ⊆ vocabulary R := fun p hp => atoms_of_mem hD (Finset.mem_union_left _ hp)
    have hb : B.atoms ⊆ vocabulary R := fun p hp => atoms_of_mem hD (Finset.mem_union_right _ hp)
    have hsubA : vocabulary (insert A R) ⊆ vocabulary R := by
      rw [vocabulary_insert]
      exact Finset.union_subset ha Finset.Subset.rfl
    have hsubB : vocabulary (insert B R) ⊆ vocabulary R := by
      rw [vocabulary_insert]
      exact Finset.union_subset hb Finset.Subset.rfl
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have h := Finset.mem_inter.mp (wA.common hp)
      exact Finset.mem_inter.mpr ⟨h.1, hsubA h.2⟩
    · have h := Finset.mem_inter.mp (wB.common hp)
      exact Finset.mem_inter.mpr ⟨h.1, hsubB h.2⟩

/-- Actual structural recursion; the two factor certificates are reconstructed, not chosen. -/
def extract : {Γ : Sequent α} → (p : Proof Γ) →
    (L R : Sequent α) → Covers Γ L R → Witness L R
  | _, .identity p hp hn, L, R, hc => atomic p L R (hc hp) (hc hn)
  | _, .truth ht, L, R, hc => truth L R (hc ht)
  | _, @Proof.andIntro _ _ Γ A B pa pb, L, R, hc =>
      if hD : Nnf.and A B ∈ L then
        conjunctionLeft hD
          (extract pa (insert A L) R (insert_cover_left (drop_cover hc) A))
          (extract pb (insert B L) R (insert_cover_left (drop_cover hc) B))
      else
        conjunctionRight (principal_right hc hD)
          (extract pa L (insert A R) (insert_cover_right (drop_cover hc) A))
          (extract pb L (insert B R) (insert_cover_right (drop_cover hc) B))
  | _, @Proof.orIntro _ _ Γ A B pa, L, R, hc =>
      if hD : Nnf.or A B ∈ L then
        disjunctionLeft hD
          (extract pa (insert A (insert B L)) R
            (insert_cover_left (insert_cover_left (drop_cover hc) B) A))
      else
        disjunctionRight (principal_right hc hD)
          (extract pa L (insert A (insert B R))
            (insert_cover_right (insert_cover_right (drop_cover hc) B) A))
  | _, .botIntro pa, L, R, hc => extract pa L R (drop_cover hc)

/-- The specified composition first removes cuts from the supplied actual tree. -/
def extractWithCut {Γ : Sequent α} (p : CutProof Γ)
    (L R : Sequent α) (hc : Covers Γ L R) : Witness L R :=
  extract p.eliminate L R hc

end Lemmatheca.ProofTheory.ClassicalPropositional.Interpolation
