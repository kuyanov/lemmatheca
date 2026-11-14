import Lemmatheca.EqualityFreeFirstOrderCutElimination.Structures

/-! Generalized target-inclusion inversion removes retained finite-set copies.
The universal operation accepts an actual supplied term. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
namespace CoreProof

private theorem retain {Γ Δ : Sequent L α} {D : Nnf L α 0}
    (h : Γ ⊆ insert D Δ) (A : Nnf L α 0) :
    insert A Γ ⊆ insert D (insert A Δ) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · simp
  · rcases Finset.mem_insert.mp (h hx) with rfl | hx
    · simp
    · simp [hx]

private theorem lift_insert (A : Nnf L α 0) (Γ : Sequent L α) :
    liftContext (insert A Γ) = insert (A.rename Sum.inl) (liftContext Γ) := by
  simp only [liftContext, renameContext, Finset.image_insert]

private theorem lift_subset {Γ Δ : Sequent L α} (A : Nnf L α 0)
    (h : Γ ⊆ insert A Δ) :
    liftContext Γ ⊆ insert (A.rename Sum.inl) (liftContext Δ) := by
  rw [← lift_insert]
  exact Finset.image_subset_image h


/-- Bottom inversion, with the target arbitrary throughout tree recursion. -/
def invertBot {Ξ Δ : Sequent L α} (p : CoreProof L Ξ) (h : Ξ ⊆ insert .bot Δ) :
    CoreProof L Δ := by
  induction p with
  | identity R ts hp hn =>
      exact .identity R ts (by simpa using h hp) (by simpa using h hn)
  | truth ht => exact .truth (by simpa using h ht)
  | @andIntro α Γ A B p q ihP ihQ =>
      have hs : Γ ⊆ insert Nnf.bot Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.and A B ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ihP (retain hs A)
      have pb := ihQ (retain hs B)
      exact (Finset.insert_eq_of_mem ha) ▸ CoreProof.andIntro pa pb
  | @orIntro α Γ A B p ih =>
      have hs : Γ ⊆ insert Nnf.bot Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.or A B ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ih (retain (retain hs B) A)
      exact (Finset.insert_eq_of_mem ha) ▸ CoreProof.orIntro pa
  | @botIntro α Γ p ih =>
      exact ih (fun _ hm => h (Finset.mem_insert_of_mem hm))
  | @allIntro α Γ B p ih =>
      have hs : Γ ⊆ insert Nnf.bot Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.all B ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have hl : liftContext Γ ⊆ insert Nnf.bot (liftContext Δ) := by
        simpa only [Nnf.rename, Nnf.subst, Nnf.map] using lift_subset Nnf.bot hs
      have pa := ih (retain hl B.toFormula)
      exact (Finset.insert_eq_of_mem ha) ▸ CoreProof.allIntro B pa
  | @exIntro α Γ B t p ih =>
      have hs : Γ ⊆ insert Nnf.bot Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.ex B ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ih (retain hs (B.instantiate t))
      exact (Finset.insert_eq_of_mem ha) ▸ CoreProof.exIntro B t pa

private def invertAndChoice {Ξ : Sequent L α} (p : CoreProof L Ξ) :
    (B C : Nnf L α 0) → (left : Bool) → {Δ : Sequent L α} →
    Ξ ⊆ insert (.and B C) Δ → CoreProof L (insert (if left then B else C) Δ) := by
  induction p with
  | identity R ts hp hn =>
      intro B C left Δ h
      exact .identity R ts (Finset.mem_insert_of_mem (by simpa using h hp))
        (Finset.mem_insert_of_mem (by simpa using h hn))
  | truth ht =>
      intro B C left Δ h
      exact .truth (Finset.mem_insert_of_mem (by simpa using h ht))
  | @andIntro α Γ A E p q ihP ihQ =>
      intro B C left Δ h
      have hs : Γ ⊆ insert (.and B C) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      by_cases he : Nnf.and A E = Nnf.and B C
      · rcases Nnf.and.inj he with ⟨rfl, rfl⟩
        cases left
        · simpa using ihQ A E false (retain hs E)
        · simpa using ihP A E true (retain hs A)
      · have ha : Nnf.and A E ∈ Δ :=
          (Finset.mem_insert.mp (h (Finset.mem_insert_self _ _))).resolve_left he
        have pa := ihP B C left (retain hs A)
        have pb := ihQ B C left (retain hs E)
        have r := CoreProof.andIntro
          (Γ := insert (if left then B else C) Δ) (A := A) (B := E)
          (by simpa only [Finset.insert_comm] using pa)
          (by simpa only [Finset.insert_comm] using pb)
        exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)) ▸ r
  | @orIntro α Γ A E p ih =>
      intro B C left Δ h
      have hs : Γ ⊆ insert (.and B C) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.or A E ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ih B C left (retain (retain hs E) A)
      have r := CoreProof.orIntro (Γ := insert (if left then B else C) Δ) (A := A) (B := E)
        (by simpa only [Finset.insert_comm] using pa)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)) ▸ r
  | @botIntro α Γ p ih =>
      intro B C left Δ h
      have hs : Γ ⊆ insert (.and B C) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.bot ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)) ▸
        CoreProof.botIntro (ih B C left hs)
  | @allIntro α Γ F p ih =>
      intro B C left Δ h
      have hs : Γ ⊆ insert (.and B C) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.all F ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have hl : liftContext Γ ⊆
          insert (.and (B.rename Sum.inl) (C.rename Sum.inl)) (liftContext Δ) := by
        simpa only [Nnf.rename, Nnf.subst, Nnf.map] using lift_subset (.and B C) hs
      have pa := ih (B.rename Sum.inl) (C.rename Sum.inl) left (retain hl F.toFormula)
      have r := CoreProof.allIntro (Γ := insert (if left then B else C) Δ) F
        (by cases left <;> simpa [lift_insert, Finset.insert_comm] using pa)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)) ▸ r
  | @exIntro α Γ F t p ih =>
      intro B C left Δ h
      have hs : Γ ⊆ insert (.and B C) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.ex F ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ih B C left (retain hs (F.instantiate t))
      have r := CoreProof.exIntro (Γ := insert (if left then B else C) Δ) F t
        (by simpa only [Finset.insert_comm] using pa)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)) ▸ r

/-- Remove every retained copy of a conjunction and offer its left factor. -/
def invertAndLeft (B C : Nnf L α 0) {Ξ Δ : Sequent L α}
    (p : CoreProof L Ξ) (h : Ξ ⊆ insert (.and B C) Δ) :
    CoreProof L (insert B Δ) := by
  exact invertAndChoice p B C true h

def invertAndRight (B C : Nnf L α 0) {Ξ Δ : Sequent L α}
    (p : CoreProof L Ξ) (h : Ξ ⊆ insert (.and B C) Δ) :
    CoreProof L (insert C Δ) := by
  exact invertAndChoice p B C false h

private def invertOrAux {Ξ : Sequent L α} (p : CoreProof L Ξ) :
    (B C : Nnf L α 0) → {Δ : Sequent L α} →
    Ξ ⊆ insert (.or B C) Δ → CoreProof L (insert B (insert C Δ)) := by
  induction p with
  | identity R ts hp hn =>
      intro B C Δ h
      exact .identity R ts
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by simpa using h hp)))
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by simpa using h hn)))
  | truth ht =>
      intro B C Δ h
      exact .truth (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by simpa using h ht)))
  | @andIntro α Γ A E p q ihP ihQ =>
      intro B C Δ h
      have hs : Γ ⊆ insert (.or B C) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.and A E ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ihP B C (retain hs A)
      have pb := ihQ B C (retain hs E)
      have r := CoreProof.andIntro (Γ := insert B (insert C Δ)) (A := A) (B := E)
        (by simpa only [Finset.insert_comm] using pa)
        (by simpa only [Finset.insert_comm] using pb)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha))) ▸ r
  | @orIntro α Γ A E p ih =>
      intro B C Δ h
      have hs : Γ ⊆ insert (.or B C) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have pa := ih B C (retain (retain hs E) A)
      by_cases he : Nnf.or A E = Nnf.or B C
      · rcases Nnf.or.inj he with ⟨rfl, rfl⟩
        simpa [Finset.insert_comm] using pa
      · have ha : Nnf.or A E ∈ Δ :=
          (Finset.mem_insert.mp (h (Finset.mem_insert_self _ _))).resolve_left he
        have r := CoreProof.orIntro (Γ := insert B (insert C Δ)) (A := A) (B := E)
          (by simpa only [Finset.insert_comm] using pa)
        exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha))) ▸ r
  | @botIntro α Γ p ih =>
      intro B C Δ h
      have hs : Γ ⊆ insert (.or B C) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.bot ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha))) ▸
        CoreProof.botIntro (ih B C hs)
  | @allIntro α Γ F p ih =>
      intro B C Δ h
      have hs : Γ ⊆ insert (.or B C) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.all F ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have hl : liftContext Γ ⊆
          insert (.or (B.rename Sum.inl) (C.rename Sum.inl)) (liftContext Δ) := by
        simpa only [Nnf.rename, Nnf.subst, Nnf.map] using lift_subset (.or B C) hs
      have pa := ih (B.rename Sum.inl) (C.rename Sum.inl) (retain hl F.toFormula)
      have r := CoreProof.allIntro (Γ := insert B (insert C Δ)) F
        (by simpa only [lift_insert, Finset.insert_comm] using pa)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha))) ▸ r
  | @exIntro α Γ F t p ih =>
      intro B C Δ h
      have hs : Γ ⊆ insert (.or B C) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.ex F ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ih B C (retain hs (F.instantiate t))
      have r := CoreProof.exIntro (Γ := insert B (insert C Δ)) F t
        (by simpa only [Finset.insert_comm] using pa)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha))) ▸ r

/-- Remove every retained copy of a disjunction and offer both factors. -/
def invertOr (B C : Nnf L α 0) {Ξ Δ : Sequent L α}
    (p : CoreProof L Ξ) (h : Ξ ⊆ insert (.or B C) Δ) :
    CoreProof L (insert B (insert C Δ)) := by
  exact invertOrAux p B C h

private def closeParameter (t : L.Term α) : α ⊕ Fin 1 → L.Term α :=
  Sum.elim Term.var (fun _ => t)

private theorem close_open (B : Nnf L α 1) (t : L.Term α) :
    B.toFormula.subst (closeParameter t) = B.instantiate t := by
  unfold Nnf.toFormula Nnf.subst Nnf.instantiate Nnf.instantiateSlots
  rw [Nnf.map_comp]
  congr 1
  funext x
  cases x <;> rfl

private theorem close_lift (Γ : Sequent L α) (t : L.Term α) :
    substContext (liftContext Γ) (closeParameter t) = Γ := by
  simp only [liftContext, renameContext, substContext, Finset.image_image, Function.comp_def,
    Nnf.rename_subst, closeParameter, Sum.elim_inl, Nnf.subst_id]
  exact Finset.image_id'

private theorem instance_rename (B : Nnf L α 1) (t : L.Term α)
    {β : Type w} (f : α → β) :
    (B.rename f).instantiate (t.relabel f) = (B.instantiate t).rename f := by
  simpa only [Nnf.rename, term_subst_vars] using
    (Nnf.instantiate_subst B t (fun x => Term.var (f x))).symm

private theorem close_lifted_instance (B : Nnf L α 1) (t : L.Term α) :
    ((B.rename Sum.inl).instantiate (t.relabel Sum.inl)).subst (closeParameter t) =
      B.instantiate t := by
  rw [Nnf.instantiate_subst, Nnf.rename_subst]
  simp only [closeParameter, Sum.elim_inl, Nnf.subst_id, term_subst_relabel, term_subst_var]

private def invertAllAux {Ξ : Sequent L α} (p : CoreProof L Ξ) :
    (B : Nnf L α 1) → (t : L.Term α) → {Δ : Sequent L α} →
    Ξ ⊆ insert (.all B) Δ → CoreProof L (insert (B.instantiate t) Δ) := by
  induction p with
  | identity R ts hp hn =>
      intro B t Δ h
      exact .identity R ts (Finset.mem_insert_of_mem (by simpa using h hp))
        (Finset.mem_insert_of_mem (by simpa using h hn))
  | truth ht =>
      intro B t Δ h
      exact .truth (Finset.mem_insert_of_mem (by simpa using h ht))
  | @andIntro α Γ A E p q ihP ihQ =>
      intro B t Δ h
      have hs : Γ ⊆ insert (.all B) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.and A E ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ihP B t (retain hs A)
      have pb := ihQ B t (retain hs E)
      have r := CoreProof.andIntro (Γ := insert (B.instantiate t) Δ) (A := A) (B := E)
        (by simpa only [Finset.insert_comm] using pa)
        (by simpa only [Finset.insert_comm] using pb)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)) ▸ r
  | @orIntro α Γ A E p ih =>
      intro B t Δ h
      have hs : Γ ⊆ insert (.all B) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.or A E ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ih B t (retain (retain hs E) A)
      have r := CoreProof.orIntro (Γ := insert (B.instantiate t) Δ) (A := A) (B := E)
        (by simpa only [Finset.insert_comm] using pa)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)) ▸ r
  | @botIntro α Γ p ih =>
      intro B t Δ h
      have hs : Γ ⊆ insert (.all B) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.bot ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)) ▸
        CoreProof.botIntro (ih B t hs)
  | @allIntro α Γ C p ih =>
      intro B t Δ h
      have hs : Γ ⊆ insert (.all B) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have hl : liftContext Γ ⊆ insert (.all (B.rename Sum.inl)) (liftContext Δ) := by
        simpa only [Nnf.rename, Nnf.subst_all] using lift_subset (.all B) hs
      have pa := ih (B.rename Sum.inl) (t.relabel Sum.inl) (retain hl C.toFormula)
      by_cases he : Nnf.all C = Nnf.all B
      · cases Nnf.all.inj he
        have r := pa.substitute (closeParameter t)
        simpa only [substContext_insert, close_lifted_instance, close_open, close_lift,
          Finset.insert_idem] using r
      · have ha : Nnf.all C ∈ Δ :=
          (Finset.mem_insert.mp (h (Finset.mem_insert_self _ _))).resolve_left he
        have r := CoreProof.allIntro (Γ := insert (B.instantiate t) Δ) C
          (by simpa only [instance_rename, lift_insert, Finset.insert_comm] using pa)
        exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)) ▸ r
  | @exIntro α Γ C s p ih =>
      intro B t Δ h
      have hs : Γ ⊆ insert (.all B) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.ex C ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ih B t (retain hs (C.instantiate s))
      have r := CoreProof.exIntro (Γ := insert (B.instantiate t) Δ) C s
        (by simpa only [Finset.insert_comm] using pa)
      exact (Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)) ▸ r

/-- Instantiate a universal, including retained side copies, at this supplied term. -/
def invertAll (B : Nnf L α 1) (t : L.Term α) {Ξ Δ : Sequent L α}
    (p : CoreProof L Ξ) (h : Ξ ⊆ insert (.all B) Δ) :
    CoreProof L (insert (B.instantiate t) Δ) := by
  exact invertAllAux p B t h

end CoreProof
end
end Lemmatheca.ProofTheory.ClassicalFirstOrder
