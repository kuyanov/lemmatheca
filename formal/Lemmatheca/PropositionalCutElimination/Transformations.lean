import Lemmatheca.PropositionalCutElimination.Structures

/-! Faithful targets for the explicit syntactic proof transformations. -/

namespace Lemmatheca.ProofTheory.ClassicalPropositional

universe u
variable {α : Type u} [DecidableEq α]

private def grow {Γ Δ : Sequent α} (p : Proof Γ) (h : Γ ⊆ Δ) : Proof Δ :=
  (Finset.union_eq_right.mpr h) ▸ p.addContext Δ

private def rebuildAnd {Γ R : Sequent α} (D A B : Nnf α) (h : .and A B ≠ D)
    (p : Proof ((insert A Γ).erase D ∪ R))
    (q : Proof ((insert B Γ).erase D ∪ R)) :
    Proof ((insert (.and A B) Γ).erase D ∪ R) := by
  have pa : Proof (insert A (Γ.erase D ∪ R)) := grow p (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
    aesop)
  have pb : Proof (insert B (Γ.erase D ∪ R)) := grow q (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
    aesop)
  exact grow (.andIntro pa pb) (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
    aesop)

private def rebuildOr {Γ R : Sequent α} (D A B : Nnf α) (h : .or A B ≠ D)
    (p : Proof ((insert A (insert B Γ)).erase D ∪ R)) :
    Proof ((insert (.or A B) Γ).erase D ∪ R) := by
  have pa : Proof (insert A (insert B (Γ.erase D ∪ R))) := grow p (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
    aesop)
  exact grow (.orIntro pa) (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
    aesop)

private def rebuildBot {Γ R : Sequent α} (D : Nnf α) (h : .bot ≠ D)
    (p : Proof (Γ.erase D ∪ R)) : Proof ((insert .bot Γ).erase D ∪ R) := by
  exact grow (.botIntro p) (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
    aesop)

/-- Remove every occurrence of falsity from the concluding context of a primitive tree. -/
def Proof.eraseBot : {Ξ : Sequent α} → (p : Proof Ξ) → Proof (Ξ.erase .bot)
  | _, .identity a hp hn => .identity a (by simpa using hp) (by simpa using hn)
  | _, .truth ht => .truth (by simpa using ht)
  | _, @Proof.andIntro _ _ Γ A B pa pb => by
      have r := rebuildAnd (Γ := Γ) (R := ∅) .bot A B (by simp)
        (by simpa using eraseBot pa) (by simpa using eraseBot pb)
      simpa using r
  | _, @Proof.orIntro _ _ Γ A B pa => by
      have r := rebuildOr (Γ := Γ) (R := ∅) .bot A B (by simp)
        (by simpa using eraseBot pa)
      simpa using r
  | _, @Proof.botIntro _ _ Γ pa => by simpa using eraseBot pa

private def invertAndChoice (B C : Nnf α) (left : Bool) :
    {Ξ : Sequent α} → Proof Ξ → Proof (insert (if left then B else C) (Ξ.erase (.and B C)))
  | _, .identity a hp hn => .identity a
      (Finset.mem_insert_of_mem (by simpa using hp))
      (Finset.mem_insert_of_mem (by simpa using hn))
  | _, .truth ht => .truth (Finset.mem_insert_of_mem (by simpa using ht))
  | _, @Proof.andIntro _ _ Γ A E pa pb => by
      have iha := invertAndChoice B C left pa
      have ihb := invertAndChoice B C left pb
      by_cases h : Nnf.and A E = Nnf.and B C
      · rcases Nnf.and.inj h with ⟨rfl, rfl⟩
        cases left
        · exact grow ihb (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_erase, Bool.false_eq_true,
              ite_false] at hx ⊢
            aesop)
        · exact grow iha (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_erase, ite_true] at hx ⊢
            aesop)
      · have r := rebuildAnd (Γ := Γ) (R := {if left then B else C})
          (.and B C) A E h
          (grow iha (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
              Finset.mem_erase] at hx ⊢
            aesop))
          (grow ihb (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
              Finset.mem_erase] at hx ⊢
            aesop))
        exact grow r (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_erase] at hx ⊢
          aesop)
  | _, @Proof.orIntro _ _ Γ A E pa => by
      have iha := invertAndChoice B C left pa
      have r := rebuildOr (Γ := Γ) (R := {if left then B else C})
        (.and B C) A E (by simp)
        (grow iha (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_erase] at hx ⊢
          aesop))
      exact grow r (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_erase] at hx ⊢
        aesop)
  | _, @Proof.botIntro _ _ Γ pa => by
      have iha := invertAndChoice B C left pa
      have r := rebuildBot (Γ := Γ) (R := {if left then B else C}) (.and B C) (by simp)
        (grow iha (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_erase] at hx ⊢
          aesop))
      exact grow r (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_erase] at hx ⊢
        aesop)

/-- Erase the displayed conjunction and insert its left child, including old copies. -/
def Proof.invertAndLeft (B C : Nnf α) {Ξ : Sequent α} (p : Proof Ξ) :
    Proof (insert B (Ξ.erase (.and B C))) :=
  invertAndChoice B C true p

/-- Erase the displayed conjunction and insert its right child, including old copies. -/
def Proof.invertAndRight (B C : Nnf α) {Ξ : Sequent α} (p : Proof Ξ) :
    Proof (insert C (Ξ.erase (.and B C))) :=
  invertAndChoice B C false p

/-- Erase the displayed disjunction and insert both of its children. -/
def Proof.invertOr (B C : Nnf α) :
    {Ξ : Sequent α} → Proof Ξ → Proof (insert B (insert C (Ξ.erase (.or B C))))
  | _, .identity a hp hn => .identity a
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by simpa using hp)))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by simpa using hn)))
  | _, .truth ht => .truth
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by simpa using ht)))
  | _, @Proof.andIntro _ _ Γ A E pa pb => by
      have iha := invertOr B C pa
      have ihb := invertOr B C pb
      have r := rebuildAnd (Γ := Γ) (R := {B, C}) (.or B C) A E (by simp)
        (grow iha (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_erase] at hx ⊢
          aesop))
        (grow ihb (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_erase] at hx ⊢
          aesop))
      exact grow r (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_erase] at hx ⊢
        aesop)
  | _, @Proof.orIntro _ _ Γ A E pa => by
      have iha := invertOr B C pa
      by_cases h : Nnf.or A E = Nnf.or B C
      · rcases Nnf.or.inj h with ⟨rfl, rfl⟩
        exact grow iha (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          aesop)
      · have r := rebuildOr (Γ := Γ) (R := {B, C}) (.or B C) A E h
          (grow iha (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
              Finset.mem_erase] at hx ⊢
            aesop))
        exact grow r (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_erase] at hx ⊢
          aesop)
  | _, @Proof.botIntro _ _ Γ pa => by
      have iha := invertOr B C pa
      have r := rebuildBot (Γ := Γ) (R := {B, C}) (.or B C) (by simp)
        (grow iha (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_erase] at hx ⊢
          aesop))
      exact grow r (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_erase] at hx ⊢
        aesop)

/-- Replace positive-literal identity leaves by the fixed supplied opposite-literal tree. -/
def Proof.replacePositive (p : α) {Δ Ξ : Sequent α}
    (q : Proof (insert (.neg p) Δ)) (r : Proof Ξ) :
    Proof (Ξ.erase (.pos p) ∪ Δ) :=
  match r with
  | .identity a hp hn => by
      by_cases h : a = p
      · subst a
        exact grow q (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨by simp, hn⟩
          · exact Or.inr hx)
      · exact .identity a
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simpa using h, hp⟩))
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hn⟩))
  | .truth ht => .truth (Finset.mem_union_left _ (by simpa using ht))
  | @Proof.andIntro _ _ Γ A B pa pb =>
      rebuildAnd (Γ := Γ) (R := Δ) (.pos p) A B (by simp)
        (replacePositive p q pa) (replacePositive p q pb)
  | @Proof.orIntro _ _ Γ A B pa =>
      rebuildOr (Γ := Γ) (R := Δ) (.pos p) A B (by simp) (replacePositive p q pa)
  | @Proof.botIntro _ _ Γ pa =>
      rebuildBot (Γ := Γ) (R := Δ) (.pos p) (by simp) (replacePositive p q pa)

/-- Compose actual cut-free premise trees by the formula-recursive cut transformation. -/
def Proof.cut : (A : Nnf α) → {Γ Δ : Sequent α} →
    Proof (insert A Γ) → Proof (insert A.dual Δ) → Proof (Γ ∪ Δ)
  | .pos a, Γ, Δ, p, q => by
      exact grow (replacePositive a q p) (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
        aesop)
  | .neg a, Γ, Δ, p, q => by
      exact grow (replacePositive a p q) (by
        intro x hx
        simp only [Nnf.dual, Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
        aesop)
  | .bot, Γ, Δ, p, _q => by
      exact grow p.eraseBot (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
        aesop)
  | .top, Γ, Δ, _p, q => by
      exact grow q.eraseBot (by
        intro x hx
        simp only [Nnf.dual, Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
        aesop)
  | .and B C, Γ, Δ, p, q => by
      have pB : Proof (insert B Γ) := grow (p.invertAndLeft B C) (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        aesop)
      have pC : Proof (insert C Γ) := grow (p.invertAndRight B C) (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        aesop)
      have qBC : Proof (insert B.dual (insert C.dual Δ)) :=
        grow (q.invertOr B.dual C.dual) (by
          intro x hx
          simp only [Nnf.dual, Finset.mem_insert, Finset.mem_erase] at hx ⊢
          aesop)
      have rB := cut B (Γ := Γ) (Δ := insert C.dual Δ) pB qBC
      have qC : Proof (insert C.dual (Γ ∪ Δ)) := grow rB (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢
        aesop)
      exact grow (cut C pC qC) (by
        intro x hx
        simp only [Finset.mem_union] at hx ⊢
        aesop)
  | .or B C, Γ, Δ, p, q => by
      have pBC : Proof (insert B (insert C Γ)) := grow (p.invertOr B C) (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        aesop)
      have qB : Proof (insert B.dual Δ) := grow (q.invertAndLeft B.dual C.dual) (by
        intro x hx
        simp only [Nnf.dual, Finset.mem_insert, Finset.mem_erase] at hx ⊢
        aesop)
      have qC : Proof (insert C.dual Δ) := grow (q.invertAndRight B.dual C.dual) (by
        intro x hx
        simp only [Nnf.dual, Finset.mem_insert, Finset.mem_erase] at hx ⊢
        aesop)
      have rB := cut B (Γ := insert C Γ) (Δ := Δ) pBC qB
      have pC : Proof (insert C (Γ ∪ Δ)) := grow rB (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢
        aesop)
      exact grow (cut C pC qC) (by
        intro x hx
        simp only [Finset.mem_union] at hx ⊢
        aesop)

/-- Rebuild a supplied six-rule finite tree using only the five primitive rules. -/
def CutProof.eliminate : {Γ : Sequent α} → CutProof Γ → Proof Γ
  | _, .identity a hp hn => .identity a hp hn
  | _, .truth ht => .truth ht
  | _, .andIntro p q => .andIntro p.eliminate q.eliminate
  | _, .orIntro p => .orIntro p.eliminate
  | _, .botIntro p => .botIntro p.eliminate
  | _, .cut A p q => Proof.cut A p.eliminate q.eliminate

/-- Adding cut proves exactly the original sequents. -/
theorem cut_derivability_iff (Γ : Sequent α) : CutDerives Γ ↔ Derives Γ := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.eliminate⟩
  · rintro ⟨p⟩
    exact ⟨CutProof.ofProof p⟩

end Lemmatheca.ProofTheory.ClassicalPropositional
