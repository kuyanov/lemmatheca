import Lemmatheca.ClassicalPropositionalSequents.Calculus

/-! Syntax bridges, structural proof transformations, and Boolean soundness. -/

namespace Lemmatheca.ProofTheory.ClassicalPropositional

open Lemmatheca.MathematicalLogic.Propositional

universe u
variable {α : Type u}

namespace Nnf

theorem dual_dual (A : Nnf α) : A.dual.dual = A := by
  induction A <;> simp_all [dual]

theorem eval_dual (v : α → Bool) (A : Nnf α) : A.dual.eval v = !(A.eval v) := by
  induction A <;> simp_all [dual, eval, Bool.not_and, Bool.not_or]

theorem eval_read (v : α → Bool) (A : Nnf α) :
    Lemmatheca.MathematicalLogic.Propositional.eval v A.read = A.eval v := by
  induction A <;> simp_all [read, eval,
    Lemmatheca.MathematicalLogic.Propositional.eval, verum]

theorem normalize_eval (v : α → Bool) (F : PropFormula α) (b : Bool) :
    (normalize F b).eval v =
      if b then Lemmatheca.MathematicalLogic.Propositional.eval v F
      else !(Lemmatheca.MathematicalLogic.Propositional.eval v F) := by
  induction F generalizing b <;> cases b <;>
    simp_all [normalize, eval, Lemmatheca.MathematicalLogic.Propositional.eval,
      Bool.not_and, Bool.not_or]

theorem negative_eq_dual (F : PropFormula α) : negative F = (positive F).dual := by
  have aux (F : PropFormula α) :
      negative F = (positive F).dual ∧ positive F = (negative F).dual := by
    induction F with
    | atom a => exact ⟨rfl, rfl⟩
    | falsum => exact ⟨rfl, rfl⟩
    | neg A ih => exact ⟨ih.2, ih.1⟩
    | conj A B ihA ihB =>
        exact ⟨congrArg₂ Nnf.or ihA.1 ihB.1, congrArg₂ Nnf.and ihA.2 ihB.2⟩
    | disj A B ihA ihB =>
        exact ⟨congrArg₂ Nnf.and ihA.1 ihB.1, congrArg₂ Nnf.or ihA.2 ihB.2⟩
    | impl A B ihA ihB =>
        exact ⟨congrArg₂ Nnf.and ihA.2 ihB.1, congrArg₂ Nnf.or ihA.1 ihB.2⟩
  exact (aux F).1

theorem positive_read (A : Nnf α) : positive A.read = A := by
  induction A <;> simp_all [positive, normalize, read, verum]

variable [DecidableEq α]

theorem atoms_dual (A : Nnf α) : A.dual.atoms = A.atoms := by
  induction A <;> simp_all [dual, atoms]

theorem atoms_read (A : Nnf α) :
    Lemmatheca.MathematicalLogic.Propositional.atoms A.read = A.atoms := by
  induction A <;> simp_all [read, atoms,
    Lemmatheca.MathematicalLogic.Propositional.atoms, verum]

theorem atoms_normalize (F : PropFormula α) (b : Bool) :
    (normalize F b).atoms = Lemmatheca.MathematicalLogic.Propositional.atoms F := by
  induction F generalizing b <;> cases b <;>
    simp_all [normalize, atoms, Lemmatheca.MathematicalLogic.Propositional.atoms]

end Nnf

variable [DecidableEq α]

namespace Proof

private theorem height_cast {Γ Δ : Sequent α} (h : Γ = Δ) (p : Proof Γ) :
    (cast (congrArg Proof h) p).height = p.height := by
  cases h
  rfl

/-- The literal context-extension construction preserves every branch length. -/
theorem add_context {Γ : Sequent α} (p : Proof Γ) (Θ : Sequent α) :
    (p.addContext Θ).height = p.height := by
  induction p <;> simp_all [addContext, height_cast, height]

/-- Every actual finite proof certificate has a valid conclusion. -/
theorem sound {Γ : Sequent α} (p : Proof Γ) : Valid Γ := by
  intro v
  induction p with
  | identity p hp hn =>
      cases he : v p with
      | false => exact ⟨.neg p, hn, by simp [Nnf.eval, he]⟩
      | true => exact ⟨.pos p, hp, he⟩
  | truth ht => exact ⟨.top, ht, rfl⟩
  | @andIntro Γ A B pa pb ihA ihB =>
      by_cases hg : SatisfiesSequent v Γ
      · rcases hg with ⟨C, hC, hc⟩
        exact ⟨C, Finset.mem_insert_of_mem hC, hc⟩
      · have ha : A.eval v = true := by
          rcases ihA with ⟨C, hC, hc⟩
          rcases Finset.mem_insert.mp hC with rfl | hC
          · exact hc
          · exact (hg ⟨C, hC, hc⟩).elim
        have hb : B.eval v = true := by
          rcases ihB with ⟨C, hC, hc⟩
          rcases Finset.mem_insert.mp hC with rfl | hC
          · exact hc
          · exact (hg ⟨C, hC, hc⟩).elim
        exact ⟨.and A B, by simp, Bool.and_eq_true_iff.mpr ⟨ha, hb⟩⟩
  | @orIntro Γ A B pa ih =>
      rcases ih with ⟨C, hC, hc⟩
      rcases Finset.mem_insert.mp hC with heq | hC
      · subst C
        exact ⟨.or A B, by simp, Bool.or_eq_true_iff.mpr (Or.inl hc)⟩
      · rcases Finset.mem_insert.mp hC with heq | hC
        · subst C
          exact ⟨.or A B, by simp, Bool.or_eq_true_iff.mpr (Or.inr hc)⟩
        · exact ⟨C, Finset.mem_insert_of_mem hC, hc⟩
  | botIntro _ ih =>
      rcases ih with ⟨C, hC, hc⟩
      exact ⟨C, Finset.mem_insert_of_mem hC, hc⟩

end Proof

theorem weakening {Γ Δ : Sequent α} (h : Derives Γ) (hsub : Γ ⊆ Δ) :
    Derives Δ := by
  rcases h with ⟨p⟩
  have hu : Γ ∪ Δ = Δ := Finset.union_eq_right.mpr hsub
  exact ⟨hu ▸ p.addContext Δ⟩

namespace Proof

/-- A chosen primitive-rule proof in an enlarged context. -/
noncomputable def weaken {Γ Δ : Sequent α} (p : Proof Γ) (hsub : Γ ⊆ Δ) : Proof Δ :=
  Classical.choice (weakening ⟨p⟩ hsub)

end Proof

/-- Atomic leaves suffice for an identity on every compound signed formula. -/
theorem identity_expansion (A : Nnf α) : Derives {A, A.dual} := by
  induction A with
  | pos p => exact ⟨.identity p (by simp) (by simp [Nnf.dual])⟩
  | neg p => exact ⟨.identity p (by simp [Nnf.dual]) (by simp)⟩
  | bot => exact ⟨.truth (by simp [Nnf.dual])⟩
  | top => exact ⟨.truth (by simp)⟩
  | and A B ihA ihB =>
      rcases ihA with ⟨pa⟩
      rcases ihB with ⟨pb⟩
      have qa : Proof (insert A.dual (insert B.dual {A})) := pa.weaken (by
        intro C hC
        simp only [Finset.mem_insert, Finset.mem_singleton] at hC ⊢
        rcases hC with rfl | rfl <;> simp)
      have qb : Proof (insert A.dual (insert B.dual {B})) := pb.weaken (by
        intro C hC
        simp only [Finset.mem_insert, Finset.mem_singleton] at hC ⊢
        rcases hC with rfl | rfl <;> simp)
      have ra : Proof (insert A {Nnf.or A.dual B.dual}) := by
        simpa [Finset.insert_comm, Finset.pair_comm] using Proof.orIntro qa
      have rb : Proof (insert B {Nnf.or A.dual B.dual}) := by
        simpa [Finset.insert_comm, Finset.pair_comm] using Proof.orIntro qb
      exact ⟨by simpa [Nnf.dual] using Proof.andIntro ra rb⟩
  | or A B ihA ihB =>
      rcases ihA with ⟨pa⟩
      rcases ihB with ⟨pb⟩
      have qa : Proof (insert A.dual {A, B}) := pa.weaken (by
        intro C hC
        simp only [Finset.mem_insert, Finset.mem_singleton] at hC ⊢
        rcases hC with rfl | rfl <;> simp)
      have qb : Proof (insert B.dual {A, B}) := pb.weaken (by
        intro C hC
        simp only [Finset.mem_insert, Finset.mem_singleton] at hC ⊢
        rcases hC with rfl | rfl <;> simp)
      have r : Proof (insert A (insert B {Nnf.and A.dual B.dual})) := by
        have hs : (insert (Nnf.and A.dual B.dual) {A, B} : Sequent α) =
            insert A (insert B {Nnf.and A.dual B.dual}) := by
          ext C
          simp [or_comm, or_assoc]
        exact hs ▸ Proof.andIntro qa qb
      exact ⟨by simpa [Nnf.dual] using Proof.orIntro r⟩

theorem empty_not_derivable : ¬ Derives (∅ : Sequent α) := by
  rintro ⟨p⟩
  have h := p.sound (fun _ => false)
  simp [SatisfiesSequent] at h

theorem bot_not_derivable : ¬ Derives ({Nnf.bot} : Sequent α) := by
  rintro ⟨p⟩
  have h := p.sound (fun _ => false)
  simp [SatisfiesSequent, Nnf.eval] at h

omit [DecidableEq α] in
theorem not_valid_empty : ¬ Valid (∅ : Sequent α) := by
  intro h
  have hfalse := h (fun _ => false)
  simp [SatisfiesSequent] at hfalse

omit [DecidableEq α] in
theorem valid_top : Valid ({Nnf.top} : Sequent α) := by
  intro v
  exact ⟨Nnf.top, by simp, rfl⟩

omit [DecidableEq α] in
theorem not_valid_bot : ¬ Valid ({Nnf.bot} : Sequent α) := by
  intro h
  have hfalse := h (fun _ => false)
  simp [SatisfiesSequent, Nnf.eval] at hfalse

/-- One fixed valuation interprets the exact encoded two-sided context. -/
theorem encode_satisfied_iff (v : α → Bool) (Λ Δ : Finset (PropFormula α)) :
    SatisfiesSequent v (encode Λ Δ) ↔
      ((∀ F ∈ Λ, Satisfies v F) → ∃ G ∈ Δ, Satisfies v G) := by
  classical
  simp only [SatisfiesSequent, encode, Finset.mem_union, Finset.mem_image,
    Nnf.negative, Nnf.positive, Satisfies]
  constructor
  · rintro ⟨A, hA, he⟩ hΛ
    rcases hA with ⟨F, hF, rfl⟩ | ⟨G, hG, rfl⟩
    · have htrue := hΛ F hF
      simp_all [Nnf.normalize_eval]
    · exact ⟨G, hG, by simpa [Nnf.normalize_eval] using he⟩
  · intro h
    by_cases hΛ : ∀ F ∈ Λ, Lemmatheca.MathematicalLogic.Propositional.eval v F = true
    · rcases h hΛ with ⟨G, hG, he⟩
      exact ⟨Nnf.normalize G true, Or.inr ⟨G, hG, rfl⟩,
        by simpa [Nnf.normalize_eval] using he⟩
    · push Not at hΛ
      rcases hΛ with ⟨F, hF, he⟩
      exact ⟨Nnf.normalize F false, Or.inl ⟨F, hF, rfl⟩,
        by simpa [Nnf.normalize_eval] using he⟩

/-- Encoding preserves the ordinary finite-premise semantic consequence. -/
theorem encode_singleton_valid_iff (Λ : Finset (PropFormula α)) (G : PropFormula α) :
    Valid (encode Λ {G}) ↔ Entails Λ G := by
  simp only [Valid, encode_satisfied_iff, Finset.mem_singleton,
    exists_eq_left, Entails, SatisfiesContext]

/-- An actual encoded proof establishes the ordinary native consequence. -/
theorem encoded_proof_entails (Λ : Finset (PropFormula α)) (G : PropFormula α)
    (h : Derives (encode Λ {G})) : Entails Λ G := by
  exact (encode_singleton_valid_iff Λ G).mp h.some.sound

/-- The no-hypothesis encoding states ordinary tautology. -/
theorem positive_proof_tautology (G : PropFormula α) (h : Derives {Nnf.positive G}) :
    Tautology G := by
  intro v
  have hs := h.some.sound v
  simpa [SatisfiesSequent, Nnf.positive, Nnf.normalize_eval, Satisfies] using hs

end Lemmatheca.ProofTheory.ClassicalPropositional
