import Lemmatheca.EqualityFreeFirstOrderSequents.Calculus

namespace Lemmatheca.ProofTheory.ClassicalFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w z
variable {L : Language.{u,v}} {α : Type w}

@[simp] private theorem rename_all (A : Nnf L α 1) (f : α → β) :
    A.all.rename f = (A.rename f).all := by
  exact Nnf.subst_all A _

@[simp] private theorem rename_ex (A : Nnf L α 1) (f : α → β) :
    A.ex.rename f = (A.rename f).ex := by
  exact Nnf.subst_ex A _

@[simp] private theorem liftContext_insert (A : Nnf L α 0) (Γ : Sequent L α) :
    liftContext (insert A Γ) = insert (A.rename Sum.inl) (liftContext Γ) := by
  simp only [liftContext, renameContext, Finset.image_insert]

/-- Contextual identity expansion recursively constructs actual raw certificates. -/
noncomputable def CoreProof.compoundIdentity : {α : Type w} →
    (A : Nnf L α 0) → (Γ : Sequent L α) → CoreProof L (insert A (insert A.dual Γ))
  | α, A, Γ => by
    match A with
    | .pos R ts => exact .identity R ts (by simp) (by simp [Nnf.dual])
    | .neg R ts => exact .identity R ts (by simp [Nnf.dual]) (by simp)
    | .bot => exact .truth (by simp [Nnf.dual])
    | .top => exact .truth (by simp)
    | .and A B =>
      have pa := CoreProof.compoundIdentity A (insert B.dual Γ)
      have pb := CoreProof.compoundIdentity B (insert A.dual Γ)
      have qa : CoreProof L (insert A (insert (.or A.dual B.dual) Γ)) := by
        simpa [Finset.insert_comm] using
          (CoreProof.orIntro (Γ := insert A Γ) (A := A.dual) (B := B.dual)
            (by simpa [Finset.insert_comm] using pa))
      have qb : CoreProof L (insert B (insert (.or A.dual B.dual) Γ)) := by
        simpa [Finset.insert_comm] using
          (CoreProof.orIntro (Γ := insert B Γ) (A := A.dual) (B := B.dual)
            (by simpa [Finset.insert_comm] using pb))
      simpa only [Nnf.dual] using CoreProof.andIntro qa qb
    | .or A B =>
      have pa := CoreProof.compoundIdentity A (insert B Γ)
      have pb := CoreProof.compoundIdentity B (insert A Γ)
      have qa : CoreProof L (insert A.dual (insert A (insert B Γ))) := by
        simpa [Finset.insert_comm] using pa
      have qb : CoreProof L (insert B.dual (insert A (insert B Γ))) := by
        simpa [Finset.insert_comm] using pb
      have q : CoreProof L (insert A (insert B (insert (.and A.dual B.dual) Γ))) := by
        simpa [Finset.insert_comm] using CoreProof.andIntro qa qb
      simpa only [Nnf.dual] using CoreProof.orIntro q
    | .all A =>
      have p := CoreProof.compoundIdentity A.toFormula (liftContext Γ)
      have q : CoreProof L
          (insert A.toFormula (liftContext (insert (.ex A.dual) Γ))) := by
        have q := CoreProof.exIntro (Γ := insert A.toFormula (liftContext Γ))
          (A.dual.rename (Sum.inl : α → α ⊕ Fin 1)) (.var (.inr 0))
          (by simpa [Nnf.instantiate_rename_fresh, Finset.insert_comm] using p)
        simpa [Finset.insert_comm] using q
      simpa only [Nnf.dual] using CoreProof.allIntro A q
    | .ex A =>
      have p := CoreProof.compoundIdentity A.toFormula (liftContext Γ)
      have q : CoreProof L
          (insert A.dual.toFormula (liftContext (insert (.ex A) Γ))) := by
        have q := CoreProof.exIntro (Γ := insert A.dual.toFormula (liftContext Γ))
          (A.rename (Sum.inl : α → α ⊕ Fin 1)) (.var (.inr 0))
          (by simpa [Nnf.instantiate_rename_fresh] using p)
        simpa [Finset.insert_comm] using q
      simpa [Nnf.dual, Finset.insert_comm] using CoreProof.allIntro A.dual q
termination_by α A _ => A.rank

decreasing_by
  all_goals simp_wf
  all_goals simp only [Nnf.rank]
  all_goals omega

noncomputable def compoundIdentity (A : Nnf L α 0) (Γ : Sequent L α) :
    Proof (insert A (insert A.dual Γ)) := by
  simpa only [Proof, renameContext, Finset.image_insert, Nnf.dual_rename] using
    CoreProof.compoundIdentity (A.rename (Sum.inl : α → α ⊕ ℕ))
      (renameContext Γ Sum.inl)

private theorem extend_zero {M : Type z} (a : α → M) (m : M) :
    Lemmatheca.ProofTheory.FirstOrder.extendAssignment (Sum.elim a Fin.elim0) m =
      Sum.elim a (fun _ : Fin 1 => m) := by
  funext x
  cases x with
  | inl x => rfl
  | inr i =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rfl

theorem CoreProof.sound {Γ : Sequent L α} (p : CoreProof L Γ)
    {M : Type z} [L.Structure M] (a : α → M) : SatisfiesSequent Γ a := by
  classical
  induction p with
  | @identity α Γ k R ts hp hn =>
    by_cases h : (Nnf.pos R ts).Realize a
    · exact ⟨.pos R ts, hp, h⟩
    · exact ⟨.neg R ts, hn, h⟩
  | truth ht => exact ⟨.top, ht, not_false⟩
  | @andIntro α Γ A B pa pb ihA ihB =>
    by_cases hΓ : SatisfiesSequent Γ a
    · obtain ⟨C, hC, hc⟩ := hΓ
      exact ⟨C, Finset.mem_insert_of_mem hC, hc⟩
    · have ha : A.Realize a := by
        obtain ⟨C, hC, hc⟩ := ihA a
        obtain rfl | hC := Finset.mem_insert.mp hC
        · exact hc
        · exact (hΓ ⟨C, hC, hc⟩).elim
      have hb : B.Realize a := by
        obtain ⟨C, hC, hc⟩ := ihB a
        obtain rfl | hC := Finset.mem_insert.mp hC
        · exact hc
        · exact (hΓ ⟨C, hC, hc⟩).elim
      exact ⟨.and A B, by simp, ha, hb⟩
  | @orIntro α Γ A B p ih =>
    obtain ⟨C, hC, hc⟩ := ih a
    obtain heq | hC := Finset.mem_insert.mp hC
    · subst C
      exact ⟨.or A B, by simp, Or.inl hc⟩
    · obtain heq | hC := Finset.mem_insert.mp hC
      · subst C
        exact ⟨.or A B, by simp, Or.inr hc⟩
      · exact ⟨C, Finset.mem_insert_of_mem hC, hc⟩
  | botIntro p ih =>
    obtain ⟨C, hC, hc⟩ := ih a
    exact ⟨C, Finset.mem_insert_of_mem hC, hc⟩
  | @allIntro α Γ A p ih =>
    by_cases hΓ : SatisfiesSequent Γ a
    · obtain ⟨C, hC, hc⟩ := hΓ
      exact ⟨C, Finset.mem_insert_of_mem hC, hc⟩
    · refine ⟨.all A, by simp, ?_⟩
      change ∀ m, A.realize (Lemmatheca.ProofTheory.FirstOrder.extendAssignment
        (Sum.elim a Fin.elim0) m)
      intro m
      obtain ⟨C, hC, hc⟩ := ih (Sum.elim a (fun _ => m))
      obtain rfl | hC := Finset.mem_insert.mp hC
      · simpa only [extend_zero] using (Nnf.realize_toFormula A _).mp hc
      · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
        have hb := (Nnf.realize_rename B Sum.inl (Sum.elim a (fun _ => m))).mp hc
        exact (hΓ ⟨B, hB, hb⟩).elim
  | @exIntro α Γ A t p ih =>
    obtain ⟨C, hC, hc⟩ := ih a
    obtain rfl | hC := Finset.mem_insert.mp hC
    · refine ⟨.ex A, by simp, ?_⟩
      change ∃ m, A.realize (Lemmatheca.ProofTheory.FirstOrder.extendAssignment
        (Sum.elim a Fin.elim0) m)
      exact ⟨t.realize a, by
        simpa only [extend_zero] using (Nnf.realize_instantiate A t a).mp hc⟩
    · exact ⟨C, Finset.mem_insert_of_mem hC, hc⟩

theorem proof_sound {Γ : Sequent L α} (p : Proof Γ)
    {M : Type z} [L.Structure M] [Nonempty M] (a : α → M) : SatisfiesSequent Γ a := by
  classical
  let b : α ⊕ ℕ → M := Sum.elim a (fun _ => Classical.choice ‹Nonempty M›)
  obtain ⟨B, hB, hb⟩ := CoreProof.sound p b
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
  exact ⟨A, hA, (Nnf.realize_rename A Sum.inl b).mp hb⟩

theorem sound {Γ : Sequent L α} (h : Derives Γ) : Valid.{u,v,w,z} Γ := by
  rcases h with ⟨p⟩
  intro M _ _ a
  exact proof_sound p a

theorem encoded_consequence (Λ Δ : Finset (EqualityFreeFormula L α))
    (p : Proof (encode Λ Δ)) {M : Type z} [L.Structure M] [Nonempty M]
    (a : α → M) (hΛ : ∀ F ∈ Λ, F.val.Realize a Fin.elim0) :
    ∃ F ∈ Δ, F.val.Realize a Fin.elim0 := by
  exact (encode_truth Λ Δ a).mp (proof_sound p a) hΛ

/-- The unique function interpretation and false relation interpretation on one point. -/
@[instance_reducible] def unitStructure (L : Language.{u,v}) : L.Structure PUnit where
  funMap _ _ := PUnit.unit
  RelMap _ _ := False

theorem empty_not_derivable : ¬ Derives (∅ : Sequent L α) := by
  rintro ⟨p⟩
  let _ : L.Structure PUnit.{1} := unitStructure L
  have h := proof_sound p (M := PUnit.{1}) (fun _ => PUnit.unit)
  simp only [SatisfiesSequent, Finset.notMem_empty, false_and, exists_false] at h

theorem falsum_not_derivable : ¬ Derives ({Nnf.bot} : Sequent L α) := by
  rintro ⟨p⟩
  let _ : L.Structure PUnit.{1} := unitStructure L
  have h := proof_sound p (M := PUnit.{1}) (fun _ => PUnit.unit)
  simp [SatisfiesSequent, Nnf.Realize, Nnf.realize, Nnf.read,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize] at h

/-- A raw existential singleton has no possible final inference without a term. -/
theorem no_raw_existential (A : Nnf L Empty 1) (h : ∀ _t : L.Term Empty, False) :
    ¬ Nonempty (CoreProof L {Nnf.ex A}) := by
  have q : ∀ {Γ : Sequent L Empty}, CoreProof L Γ → Γ ⊆ {Nnf.ex A} → False := by
    intro Γ p hs
    cases p with
    | identity R ts hp hn => simpa using hs hp
    | truth ht => simpa using hs ht
    | @andIntro _ Γ B C pb pc =>
      have hh := hs (Finset.mem_insert_self (Nnf.and B C) Γ)
      simp at hh
    | @orIntro _ Γ B C p =>
      have hh := hs (Finset.mem_insert_self (Nnf.or B C) Γ)
      simp at hh
    | @botIntro _ Γ p =>
      have hh := hs (Finset.mem_insert_self Nnf.bot Γ)
      simp at hh
    | @allIntro _ Γ B p =>
      have hh := hs (Finset.mem_insert_self (Nnf.all B) Γ)
      simp at hh
    | exIntro B t p => exact h t
  rintro ⟨p⟩
  exact q p (fun _ hm => hm)

end Lemmatheca.ProofTheory.ClassicalFirstOrder
