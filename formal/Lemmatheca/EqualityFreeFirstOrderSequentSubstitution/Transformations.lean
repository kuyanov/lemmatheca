import Lemmatheca.EqualityFreeFirstOrderSequentSubstitution.Context

/-! Structural operations on actual seven-rule quantified sequent trees. The
height theorems refer to these specified operations and the existing raw height. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α β : Type w}
noncomputable section

private def castContext {Γ Δ : Sequent L α} (h : Γ = Δ) (p : CoreProof L Γ) : CoreProof L Δ := h ▸ p

@[simp] private theorem height_castContext {Γ Δ : Sequent L α} (h : Γ = Δ)
    (p : CoreProof L Γ) : (castContext h p).height = p.height := by
  subst Δ
  rfl

private def weakenWithHeight {α : Type w} {Γ : Sequent L α} (p : CoreProof L Γ) :
    ∀ {Δ : Sequent L α}, Γ ⊆ Δ → {q : CoreProof L Δ // q.height = p.height} := by
  classical
  induction p with
  | identity R ts hp hn =>
      intro Δ hs
      exact ⟨.identity R ts (hs hp) (hs hn), rfl⟩
  | truth ht => intro Δ hs; exact ⟨.truth (hs ht), rfl⟩
  | @andIntro α Γ A B p q ihP ihQ =>
      intro Δ hs
      have hsΓ : Γ ⊆ Δ := fun _ hm => hs (Finset.mem_insert_of_mem hm)
      obtain ⟨p',hp⟩ := ihP (Finset.insert_subset_insert A hsΓ)
      obtain ⟨q',hq⟩ := ihQ (Finset.insert_subset_insert B hsΓ)
      refine ⟨castContext (Finset.insert_eq_of_mem (hs (Finset.mem_insert_self _ _)))
        (.andIntro p' q'), ?_⟩
      simp only [height_castContext, CoreProof.height, hp, hq]
  | @orIntro α Γ A B p ih =>
      intro Δ hs
      have hsΓ : Γ ⊆ Δ := fun _ hm => hs (Finset.mem_insert_of_mem hm)
      obtain ⟨p',hp⟩ := ih (Finset.insert_subset_insert A (Finset.insert_subset_insert B hsΓ))
      refine ⟨castContext (Finset.insert_eq_of_mem (hs (Finset.mem_insert_self _ _)))
        (.orIntro p'), ?_⟩
      simp only [height_castContext, CoreProof.height, hp]
  | @botIntro α Γ p ih =>
      intro Δ hs
      have hsΓ : Γ ⊆ Δ := fun _ hm => hs (Finset.mem_insert_of_mem hm)
      obtain ⟨p',hp⟩ := ih hsΓ
      refine ⟨castContext (Finset.insert_eq_of_mem (hs (Finset.mem_insert_self _ _)))
        (.botIntro p'), ?_⟩
      simp only [height_castContext, CoreProof.height, hp]
  | @allIntro α Γ B p ih =>
      intro Δ hs
      have hsΓ : Γ ⊆ Δ := fun _ hm => hs (Finset.mem_insert_of_mem hm)
      have hl : liftContext Γ ⊆ liftContext Δ := Finset.image_subset_image hsΓ
      obtain ⟨p',hp⟩ := ih (Finset.insert_subset_insert B.toFormula hl)
      refine ⟨castContext (Finset.insert_eq_of_mem (hs (Finset.mem_insert_self _ _)))
        (.allIntro B p'), ?_⟩
      simp only [height_castContext, CoreProof.height, hp]
  | @exIntro α Γ B t p ih =>
      intro Δ hs
      have hsΓ : Γ ⊆ Δ := fun _ hm => hs (Finset.mem_insert_of_mem hm)
      obtain ⟨p',hp⟩ := ih (Finset.insert_subset_insert (B.instantiate t) hsΓ)
      refine ⟨castContext (Finset.insert_eq_of_mem (hs (Finset.mem_insert_self _ _)))
        (.exIntro B t p'), ?_⟩
      simp only [height_castContext, CoreProof.height, hp]

private def substituteWithHeight {α : Type w} {Γ : Sequent L α} (p : CoreProof L Γ) :
    ∀ {β : Type w} (σ : α → L.Term β),
      {q : CoreProof L (substContext Γ σ) // q.height = p.height} := by
  classical
  induction p with
  | identity R ts hp hn =>
      intro β σ
      refine ⟨.identity R (fun i => (ts i).subst
        (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope σ 0))
        (Finset.mem_image.mpr ⟨_,hp,rfl⟩) (Finset.mem_image.mpr ⟨_,hn,rfl⟩), rfl⟩
  | truth ht =>
      intro β σ
      exact ⟨.truth (Finset.mem_image.mpr ⟨_,ht,rfl⟩),rfl⟩
  | @andIntro α Γ A B p q ihP ihQ =>
      intro β σ
      obtain ⟨p',hp⟩ := ihP σ
      obtain ⟨q',hq⟩ := ihQ σ
      let pa := castContext (substContext_insert A Γ σ) p'
      let pb := castContext (substContext_insert B Γ σ) q'
      have hc : insert (.and (A.subst σ) (B.subst σ)) (substContext Γ σ) =
          substContext (insert (.and A B) Γ) σ := by
        rw [substContext_insert]
        rfl
      refine ⟨castContext hc (.andIntro pa pb), ?_⟩
      simp only [height_castContext, CoreProof.height, pa, pb, hp, hq]
  | @orIntro α Γ A B p ih =>
      intro β σ
      obtain ⟨p',hp⟩ := ih σ
      have hc : substContext (insert A (insert B Γ)) σ =
          insert (A.subst σ) (insert (B.subst σ) (substContext Γ σ)) := by
        rw [substContext_insert, substContext_insert]
      let pa := castContext hc p'
      have hd : insert (.or (A.subst σ) (B.subst σ)) (substContext Γ σ) =
          substContext (insert (.or A B) Γ) σ := by
        rw [substContext_insert]
        rfl
      refine ⟨castContext hd (.orIntro pa), ?_⟩
      simp only [height_castContext, CoreProof.height, pa, hp]
  | @botIntro α Γ p ih =>
      intro β σ
      obtain ⟨p',hp⟩ := ih σ
      have hc : insert Nnf.bot (substContext Γ σ) = substContext (insert .bot Γ) σ := by
        rw [substContext_insert]
        rfl
      refine ⟨castContext hc (.botIntro p'), ?_⟩
      simp only [height_castContext, CoreProof.height, hp]
  | @allIntro α Γ B p ih =>
      intro β σ
      obtain ⟨p',hp⟩ := ih (Lemmatheca.MathematicalLogic.FirstOrderProofs.liftSubst σ 1)
      have hc : substContext (insert B.toFormula (liftContext Γ))
          (Lemmatheca.MathematicalLogic.FirstOrderProofs.liftSubst σ 1) =
          insert (B.subst σ).toFormula (liftContext (substContext Γ σ)) := by
        rw [substContext_insert, liftContext_subst, ← Nnf.toFormula_subst]
      let pa := castContext hc p'
      have hd : insert (.all (B.subst σ)) (substContext Γ σ) =
          substContext (insert (.all B) Γ) σ := by
        rw [substContext_insert, Nnf.subst_all]
      refine ⟨castContext hd (.allIntro (B.subst σ) pa), ?_⟩
      simp only [height_castContext, CoreProof.height, pa, hp]
  | @exIntro α Γ B t p ih =>
      intro β σ
      obtain ⟨p',hp⟩ := ih σ
      have hc : substContext (insert (B.instantiate t) Γ) σ =
          insert ((B.subst σ).instantiate (t.subst σ)) (substContext Γ σ) := by
        rw [substContext_insert, Nnf.instantiate_subst]
      let pa := castContext hc p'
      have hd : insert (.ex (B.subst σ)) (substContext Γ σ) =
          substContext (insert (.ex B) Γ) σ := by
        rw [substContext_insert, Nnf.subst_ex]
      refine ⟨castContext hd (.exIntro (B.subst σ) (t.subst σ) pa), ?_⟩
      simp only [height_castContext, CoreProof.height, pa, hp]

namespace CoreProof
variable {Γ Δ : Sequent L α}

/-- Rebuild the supplied tree over a larger allowed sequent, retaining its rule shape. -/
def weaken (p : CoreProof L Γ) (h : Γ ⊆ Δ) : CoreProof L Δ := by
  exact (weakenWithHeight p h).val

theorem height_weaken (p : CoreProof L Γ) (h : Γ ⊆ Δ) :
    (p.weaken h).height = p.height := by
  exact (weakenWithHeight p h).property

/-- Substitute through the actual tree, protecting the new name at each universal premise. -/
def substitute (p : CoreProof L Γ) (σ : α → L.Term β) :
    CoreProof L (substContext Γ σ) := by
  exact (substituteWithHeight p σ).val

theorem height_substitute (p : CoreProof L Γ) (σ : α → L.Term β) :
    (p.substitute σ).height = p.height := by
  exact (substituteWithHeight p σ).property

/-- The variable-valued case accepts arbitrary, possibly noninjective maps. -/
def rename (p : CoreProof L Γ) (f : α → β) : CoreProof L (renameContext Γ f) := by
  exact p.substitute (fun x => .var (f x))

theorem height_rename (p : CoreProof L Γ) (f : α → β) :
    (p.rename f).height = p.height := by
  exact p.height_substitute (fun x => .var (f x))

end CoreProof

theorem raw_equiv_rename (Γ : Sequent L α) (e : α ≃ β) :
    Nonempty (CoreProof L Γ) ↔ Nonempty (CoreProof L (renameContext Γ e)) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.rename e⟩
  · rintro ⟨p⟩
    have he : (e.symm : β → α) ∘ (e : α → β) = id := funext e.symm_apply_apply
    have hc : renameContext (renameContext Γ e) e.symm = Γ := by
      rw [renameContext_comp, he, renameContext_id]
    exact ⟨castContext hc (p.rename e.symm)⟩

namespace Proof
variable {Γ Δ : Sequent L α}

/-- Enlarge the reserve-renamed side sequent using only the raw tree operation. -/
def weaken (p : Proof Γ) (h : Γ ⊆ Δ) : Proof Δ := by
  exact CoreProof.weaken p (Finset.image_subset_image h)

theorem height_weaken (p : Proof Γ) (h : Γ ⊆ Δ) :
    (Proof.weaken p h).height = p.height := by
  exact CoreProof.height_weaken p (Finset.image_subset_image h)

/-- The original free parameters are substituted and the reserve is preserved. -/
def substitute (p : Proof Γ) (σ : α → L.Term β) : Proof (substContext Γ σ) := by
  exact castContext (reserve_subst_context Γ σ) (CoreProof.substitute p (reserveSubst σ))

theorem height_substitute (p : Proof Γ) (σ : α → L.Term β) :
    (Proof.substitute p σ).height = p.height := by
  simp only [Proof.substitute, height_castContext, CoreProof.height_substitute]

def rename (p : Proof Γ) (f : α → β) : Proof (renameContext Γ f) := by
  exact Proof.substitute p (fun x => .var (f x))

theorem height_rename (p : Proof Γ) (f : α → β) :
    (Proof.rename p f).height = p.height := by
  exact Proof.height_substitute p (fun x => .var (f x))

end Proof
end
end Lemmatheca.ProofTheory.ClassicalFirstOrder
