import Lemmatheca.EqualityFreeFirstOrderCutElimination.Inversions

/-! Formula-rank cut construction, with literal and existential-consumer
height recursions; no semantic completeness is used. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section

/-- A split-context operation on supplied actual seven-rule trees. -/
abbrev CutOperation (A : Nnf L α 0) :=
  ∀ {Γ Δ : Sequent L α}, CoreProof L (insert A Γ) →
    CoreProof L (insert A.dual Δ) → CoreProof L (Γ ∪ Δ)

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

private theorem lift_subset {Γ Δ : Sequent L α} (A : Nnf L α 0)
    (h : Γ ⊆ insert A Δ) :
    liftContext Γ ⊆ insert (A.rename Sum.inl) (liftContext Δ) := by
  have hr : liftContext Γ ⊆ liftContext (insert A Δ) := Finset.image_subset_image h
  simpa only [liftContext, renameContext, Finset.image_insert] using hr

private theorem lift_union (Γ Δ : Sequent L α) :
    liftContext (Γ ∪ Δ) = liftContext Γ ∪ liftContext Δ := by
  simp only [liftContext, renameContext, Finset.image_union]

private def replacePositiveAux {Ξ : Sequent L α} (p : CoreProof L Ξ) :
    ∀ {k} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin 0))
    {Γ Δ : Sequent L α}, Ξ ⊆ insert (.pos R ts) Γ →
    CoreProof L (insert (.neg R ts) Δ) → CoreProof L (Γ ∪ Δ) := by
  induction p with
  | identity S ss hp hn =>
      intro k R ts Γ Δ h q
      have hnΓ : Nnf.neg S ss ∈ Γ := by simpa using h hn
      by_cases he : Nnf.pos S ss = Nnf.pos R ts
      · have he' : Nnf.neg S ss = Nnf.neg R ts := by
          simpa only [Nnf.dual] using congrArg Nnf.dual he
        exact q.weaken (by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact Finset.mem_union_left _ (he' ▸ hnΓ)
          · exact Finset.mem_union_right _ hx)
      · exact .identity S ss
          (Finset.mem_union_left _ ((Finset.mem_insert.mp (h hp)).resolve_left he))
          (Finset.mem_union_left _ hnΓ)
  | truth ht =>
      intro k R ts Γ Δ h q
      exact .truth (Finset.mem_union_left _ (by simpa using h ht))
  | @andIntro α Ξ A E p r ihP ihR =>
      intro k R ts Γ Δ h q
      have hs : Ξ ⊆ insert (.pos R ts) Γ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.and A E ∈ Γ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ihP R ts (retain hs A) q
      have pr := ihR R ts (retain hs E) q
      have z := CoreProof.andIntro
        (by simpa only [Finset.insert_union] using pa)
        (by simpa only [Finset.insert_union] using pr)
      exact (Finset.insert_eq_of_mem (Finset.mem_union_left _ ha)) ▸ z
  | @orIntro α Ξ A E p ih =>
      intro k R ts Γ Δ h q
      have hs : Ξ ⊆ insert (.pos R ts) Γ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.or A E ∈ Γ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ih R ts (retain (retain hs E) A) q
      have z := CoreProof.orIntro (by simpa only [Finset.insert_union] using pa)
      exact (Finset.insert_eq_of_mem (Finset.mem_union_left _ ha)) ▸ z
  | @botIntro α Ξ p ih =>
      intro k R ts Γ Δ h q
      have hs : Ξ ⊆ insert (.pos R ts) Γ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.bot ∈ Γ := by simpa using h (Finset.mem_insert_self _ _)
      exact (Finset.insert_eq_of_mem (Finset.mem_union_left _ ha)) ▸
        CoreProof.botIntro (ih R ts hs q)
  | @allIntro α Ξ B p ih =>
      intro k R ts Γ Δ h q
      have hs : Ξ ⊆ insert (.pos R ts) Γ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.all B ∈ Γ := by simpa using h (Finset.mem_insert_self _ _)
      let ts' : Fin k → L.Term ((α ⊕ Fin 1) ⊕ Fin 0) := fun i =>
        (ts i).subst (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope
          (fun x => Term.var (Sum.inl x)) 0)
      have hl : liftContext Ξ ⊆ insert (.pos R ts') (liftContext Γ) := by
        simpa only [Nnf.rename, Nnf.subst, Nnf.map] using lift_subset (.pos R ts) hs
      have q' : CoreProof L (insert (.neg R ts') (liftContext Δ)) := by
        simpa only [liftContext, renameContext, Finset.image_insert, Nnf.rename, Nnf.subst,
          Nnf.map] using q.rename (Sum.inl : α → α ⊕ Fin 1)
      have pa := ih R ts' (retain hl B.toFormula) q'
      have z := CoreProof.allIntro (Γ := Γ ∪ Δ) B
        (by simpa only [Finset.insert_union, lift_union] using pa)
      exact (Finset.insert_eq_of_mem (Finset.mem_union_left _ ha)) ▸ z
  | @exIntro α Ξ B t p ih =>
      intro k R ts Γ Δ h q
      have hs : Ξ ⊆ insert (.pos R ts) Γ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.ex B ∈ Γ := by simpa using h (Finset.mem_insert_self _ _)
      have pa := ih R ts (retain hs (B.instantiate t)) q
      have z := CoreProof.exIntro B t (by simpa only [Finset.insert_union] using pa)
      exact (Finset.insert_eq_of_mem (Finset.mem_union_left _ ha)) ▸ z

/-- Positive-literal leaf replacement with the generalized inclusion invariant. -/
def replacePositive {k} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin 0))
    {Ξ Γ Δ : Sequent L α} (p : CoreProof L Ξ)
    (h : Ξ ⊆ insert (.pos R ts) Γ) (q : CoreProof L (insert (.neg R ts) Δ)) :
    CoreProof L (Γ ∪ Δ) := by
  exact replacePositiveAux p R ts h q

private theorem instance_dual (B : Nnf L α 1) (t : L.Term α) :
    (B.instantiate t).dual = B.dual.instantiate t := by
  exact Nnf.map_dual B _

private def universalAux {Ξ : Sequent L α} (q : CoreProof L Ξ) :
    (B : Nnf L α 1) →
    (∀ {β : Type w} (A : Nnf L β 0), A.rank < B.rank + 1 → CutOperation A) →
    {Γ Δ : Sequent L α} → CoreProof L (insert (.all B) Γ) →
    Ξ ⊆ insert (.ex B.dual) Δ → CoreProof L (Γ ∪ Δ) := by
  induction q with
  | identity R ts hp hn =>
      intro B smaller Γ Δ p h
      exact .identity R ts (Finset.mem_union_right _ (by simpa using h hp))
        (Finset.mem_union_right _ (by simpa using h hn))
  | truth ht =>
      intro B smaller Γ Δ p h
      exact .truth (Finset.mem_union_right _ (by simpa using h ht))
  | @andIntro α Ξ A E q r ihQ ihR =>
      intro B smaller Γ Δ p h
      have hs : Ξ ⊆ insert (.ex B.dual) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.and A E ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have qa := ihQ B smaller p (retain hs A)
      have qr := ihR B smaller p (retain hs E)
      have z := CoreProof.andIntro (Γ := Γ ∪ Δ) (A := A) (B := E)
        (by simpa only [Finset.union_insert] using qa)
        (by simpa only [Finset.union_insert] using qr)
      exact (Finset.insert_eq_of_mem (Finset.mem_union_right _ ha)) ▸ z
  | @orIntro α Ξ A E q ih =>
      intro B smaller Γ Δ p h
      have hs : Ξ ⊆ insert (.ex B.dual) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.or A E ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have qa := ih B smaller p (retain (retain hs E) A)
      have z := CoreProof.orIntro (Γ := Γ ∪ Δ) (A := A) (B := E)
        (by simpa only [Finset.union_insert] using qa)
      exact (Finset.insert_eq_of_mem (Finset.mem_union_right _ ha)) ▸ z
  | @botIntro α Ξ q ih =>
      intro B smaller Γ Δ p h
      have hs : Ξ ⊆ insert (.ex B.dual) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.bot ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      exact (Finset.insert_eq_of_mem (Finset.mem_union_right _ ha)) ▸
        CoreProof.botIntro (ih B smaller p hs)
  | @allIntro α Ξ C q ih =>
      intro B smaller Γ Δ p h
      have hs : Ξ ⊆ insert (.ex B.dual) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : Nnf.all C ∈ Δ := by simpa using h (Finset.mem_insert_self _ _)
      have hl : liftContext Ξ ⊆ insert (.ex (B.rename Sum.inl).dual) (liftContext Δ) := by
        simpa only [Nnf.rename, Nnf.subst_ex, Nnf.dual_subst] using
          lift_subset (.ex B.dual) hs
      have p' : CoreProof L (insert (.all (B.rename Sum.inl)) (liftContext Γ)) := by
        simpa only [liftContext, renameContext, Finset.image_insert, Nnf.rename,
          Nnf.subst_all] using p.rename (Sum.inl : α → α ⊕ Fin 1)
      have smaller' : ∀ {β : Type w} (A : Nnf L β 0),
          A.rank < (B.rename (Sum.inl : α → α ⊕ Fin 1)).rank + 1 → CutOperation A := by
        intro β A hr
        exact smaller A (by simpa only [Nnf.rename, Nnf.subst, Nnf.rank_map] using hr)
      have qa := ih (B.rename Sum.inl) smaller' p' (retain hl C.toFormula)
      have z := CoreProof.allIntro (Γ := Γ ∪ Δ) C
        (by simpa only [Finset.union_insert, lift_union] using qa)
      exact (Finset.insert_eq_of_mem (Finset.mem_union_right _ ha)) ▸ z
  | @exIntro α Ξ C t q ih =>
      intro B smaller Γ Δ p h
      have hs : Ξ ⊆ insert (.ex B.dual) Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have qa := ih B smaller p (retain hs (C.instantiate t))
      by_cases he : Nnf.ex C = Nnf.ex B.dual
      · cases Nnf.ex.inj he
        have pi := p.invertAll B t (Finset.Subset.refl _)
        have qi : CoreProof L (insert (B.instantiate t).dual (Γ ∪ Δ)) := by
          simpa only [Finset.union_insert, instance_dual] using qa
        have hr : (B.instantiate t).rank < B.rank + 1 := by
          simpa only [Nnf.instantiate, Nnf.instantiateSlots, Nnf.rank_map] using Nat.lt_succ_self B.rank
        simpa only [Finset.union_left_idem, Finset.union_right_idem, Finset.union_self] using smaller (B.instantiate t) hr pi qi
      · have ha : Nnf.ex C ∈ Δ :=
          (Finset.mem_insert.mp (h (Finset.mem_insert_self _ _))).resolve_left he
        have z := CoreProof.exIntro (Γ := Γ ∪ Δ) C t
          (by simpa only [Finset.union_insert] using qa)
        exact (Finset.insert_eq_of_mem (Finset.mem_union_right _ ha)) ▸ z

/-- Traverse the actual existential-side tree. The lower-rank operations are
chosen uniformly before the producer, consumer and their contexts. -/
def cutUniversal (B : Nnf L α 1)
    (smaller : ∀ {β : Type w} (A : Nnf L β 0), A.rank < B.rank + 1 → CutOperation A)
    {Γ Ξ Δ : Sequent L α} (p : CoreProof L (insert (.all B) Γ))
    (q : CoreProof L Ξ) (h : Ξ ⊆ insert (.ex B.dual) Δ) :
    CoreProof L (Γ ∪ Δ) := by
  exact universalAux q B smaller p h

private def cutByRank (n : ℕ) :
    {β : Type w} → (A : Nnf L β 0) → A.rank = n → CutOperation A := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro β A hn Γ Δ p q
      have smaller : ∀ {γ : Type w} (D : Nnf L γ 0), D.rank < n → CutOperation D := by
        intro γ D hr
        exact ih D.rank hr D rfl
      cases A with
      | pos R ts => exact replacePositive R ts p (Finset.Subset.refl _) q
      | neg R ts =>
          simpa only [Finset.union_comm] using replacePositive R ts q (Finset.Subset.refl _) p
      | bot =>
          exact (p.invertBot (Finset.Subset.refl _)).weaken (Finset.subset_union_left)
      | top =>
          exact (q.invertBot (Finset.Subset.refl _)).weaken (Finset.subset_union_right)
      | and B C =>
          have hb : B.rank < n := by simp only [Nnf.rank] at hn; omega
          have hc : C.rank < n := by simp only [Nnf.rank] at hn; omega
          have pb := p.invertAndLeft B C (Finset.Subset.refl _)
          have pc := p.invertAndRight B C (Finset.Subset.refl _)
          have qb := q.invertOr B.dual C.dual (Finset.Subset.refl _)
          have rb := smaller B hb pb qb
          have qc : CoreProof L (insert C.dual (Γ ∪ Δ)) := by
            simpa only [Finset.union_insert] using rb
          simpa only [Finset.union_left_idem, Finset.union_right_idem, Finset.union_self] using smaller C hc pc qc
      | or B C =>
          have hb : B.rank < n := by simp only [Nnf.rank] at hn; omega
          have hc : C.rank < n := by simp only [Nnf.rank] at hn; omega
          have pb := p.invertOr B C (Finset.Subset.refl _)
          have qb := q.invertAndLeft B.dual C.dual (Finset.Subset.refl _)
          have qc := q.invertAndRight B.dual C.dual (Finset.Subset.refl _)
          have rb := smaller B hb (Γ := insert C Γ) pb qb
          have pc : CoreProof L (insert C (Γ ∪ Δ)) := by
            simpa only [Finset.insert_union] using rb
          simpa only [Finset.union_left_idem, Finset.union_right_idem, Finset.union_self] using smaller C hc pc qc
      | all B =>
          exact cutUniversal B (fun D hr => smaller D (by simpa only [Nnf.rank] using hn ▸ hr))
            p q (Finset.Subset.refl _)
      | ex B =>
          have hs : ∀ {γ : Type w} (D : Nnf L γ 0),
              D.rank < B.dual.rank + 1 → CutOperation D := by
            intro γ D hr
            exact smaller D (by
              rw [← hn]
              simpa only [Nnf.rank_dual, Nnf.rank] using hr)
          have z := cutUniversal (Γ := Δ) (Δ := Γ) B.dual hs q p
            (by simpa only [Nnf.dual_dual] using Finset.Subset.refl (insert (Nnf.ex B) Γ))
          simpa only [Finset.union_comm] using z

/-- Actual admissibility for every signed quantified cut formula. -/
def cut (A : Nnf L α 0) : CutOperation A := by
  exact cutByRank A.rank A rfl

end CoreProof

/-- Structural elimination retains the precise raw endsequent and name type. -/
def CutProof.eliminate {Γ : Sequent L α} (p : CutProof L Γ) : CoreProof L Γ := by
  induction p with
  | identity R ts hp hn => exact .identity R ts hp hn
  | truth ht => exact .truth ht
  | andIntro _ _ ihP ihQ => exact .andIntro ihP ihQ
  | orIntro _ ih => exact .orIntro ih
  | botIntro _ ih => exact .botIntro ih
  | allIntro B _ ih => exact .allIntro B ih
  | exIntro B t _ ih => exact .exIntro B t ih
  | cut A _ _ ihP ihQ => exact CoreProof.cut A ihP ihQ

/-- The identical transformation over the fixed public reserve. -/
def CutCertificate.eliminate {Γ : Sequent L α} (p : CutCertificate Γ) : Proof Γ := by
  exact CutProof.eliminate p

/-- Raw existence equivalence, without changing a parameter type. -/
theorem raw_cut_derivability_iff (Γ : Sequent L α) :
    Nonempty (CutProof L Γ) ↔ Nonempty (CoreProof L Γ) := by
  constructor
  · rintro ⟨p⟩; exact ⟨p.eliminate⟩
  · rintro ⟨p⟩; exact ⟨CutProof.ofCore p⟩

theorem cut_derivability_iff (Γ : Sequent L α) : CutDerives Γ ↔ Derives Γ := by
  exact raw_cut_derivability_iff _

/-- Compose supplied public cut-free trees over their same reserve. -/
def Proof.cut (A : Nnf L α 0) {Γ Δ : Sequent L α}
    (p : Proof (insert A Γ)) (q : Proof (insert A.dual Δ)) : Proof (Γ ∪ Δ) := by
  have p' : CoreProof L (insert (A.rename (Sum.inl : α → α ⊕ ℕ))
      (renameContext Γ Sum.inl)) := by
    simpa only [Proof, renameContext, Finset.image_insert] using p
  have q' : CoreProof L (insert (A.rename (Sum.inl : α → α ⊕ ℕ)).dual
      (renameContext Δ Sum.inl)) := by
    simpa only [Proof, renameContext, Finset.image_insert, Nnf.dual_rename] using q
  simpa only [Proof, renameContext, Finset.image_union] using CoreProof.cut (A.rename Sum.inl) p' q' 

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder
