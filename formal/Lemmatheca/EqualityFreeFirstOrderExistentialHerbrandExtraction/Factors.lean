import Lemmatheca.EqualityFreeFirstOrderExistentialHerbrandExtraction.Scope
import Lemmatheca.EqualityFreeFirstOrderSequentSubstitution.Transformations

/-! Actual five-rule factor trees, weak extraction, and syntactic reconstruction. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder.ExistentialHerbrand
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w w'
variable {L : Language.{u,v}} {α : Type w} {β : Type w'}
noncomputable section

private def enlarge {γ : Type*} [DecidableEq γ]
    {Γ Δ : Finset (PropNnf γ)} (p : PropProof Γ) (h : Γ ⊆ Δ) : PropProof Δ := by
  have he : Γ ∪ Δ = Δ := Finset.union_eq_right.mpr h
  exact he ▸ p.addContext Δ

private theorem qf_insert {A : Nnf L α 0} {Γ : Sequent L α} :
    ContextQF (insert A Γ) ↔ A.QuantifierFree ∧ ContextQF Γ := by
  simp [ContextQF]

private theorem readContext_insert (A : Nnf L α 0) (Γ : Sequent L α) :
    readContext (insert A Γ) = insert (propositionalize A) (readContext Γ) := by
  exact Finset.image_insert _ _ _

private theorem embedContext_insert (A : PropNnf (Atom L α))
    (Γ : Finset (PropNnf (Atom L α))) :
    embedContext (insert A Γ) = insert (embed A) (embedContext Γ) := by
  exact Finset.image_insert _ _ _

/-- Copy a QF first-order supplied tree into the existing five-rule calculus. -/
def toPropositional {Γ : Sequent L α} (p : CoreProof L Γ) (h : ContextQF Γ) :
    PropProof (readContext Γ) := by
  classical
  induction p with
  | identity R ts hp hn =>
      exact .identity ⟨_,R,fun i => (ts i).relabel (Sum.elim id Fin.elim0)⟩
        (Finset.mem_image.mpr ⟨_,hp,by simp [propositionalize]⟩) (Finset.mem_image.mpr ⟨_,hn,by simp [propositionalize]⟩)
  | truth ht => exact .truth (Finset.mem_image.mpr ⟨_,ht,by simp [propositionalize]⟩)
  | @andIntro α Γ A B p q ihp ihq =>
      have hf := (qf_insert.mp h).1
      have hs := (qf_insert.mp h).2
      have hab : A.QuantifierFree ∧ B.QuantifierFree := hf
      have pa := ihp (qf_insert.mpr ⟨hab.1,hs⟩)
      have pb := ihq (qf_insert.mpr ⟨hab.2,hs⟩)
      rw [readContext_insert] at pa pb ⊢
      simpa only [propositionalize] using ClassicalPropositional.Proof.andIntro pa pb
  | @orIntro α Γ A B p ih =>
      have hf := (qf_insert.mp h).1
      have hs := (qf_insert.mp h).2
      have hab : A.QuantifierFree ∧ B.QuantifierFree := hf
      have pa := ih (qf_insert.mpr ⟨hab.1,qf_insert.mpr ⟨hab.2,hs⟩⟩)
      rw [readContext_insert,readContext_insert] at pa
      rw [readContext_insert]
      simpa only [propositionalize] using ClassicalPropositional.Proof.orIntro pa
  | @botIntro α Γ p ih =>
      have pa := ih (qf_insert.mp h).2
      rw [readContext_insert]
      simpa only [propositionalize] using ClassicalPropositional.Proof.botIntro pa
  | @allIntro α Γ B p ih => exact False.elim ((qf_insert.mp h).1)
  | @exIntro α Γ B t p ih => exact False.elim ((qf_insert.mp h).1)

/-- Copy an existing propositional supplied tree into the same actual first-order syntax. -/
def fromPropositional {Γ : Finset (PropNnf (Atom L α))} (p : PropProof Γ) :
    CoreProof L (embedContext Γ) := by
  classical
  induction p with
  | identity a hp hn =>
      exact .identity a.relation (fun i => (a.terms i).relabel Sum.inl)
        (Finset.mem_image.mpr ⟨_,hp,rfl⟩) (Finset.mem_image.mpr ⟨_,hn,rfl⟩)
  | truth ht => exact .truth (Finset.mem_image.mpr ⟨_,ht,rfl⟩)
  | andIntro p q ihp ihq =>
      rw [embedContext_insert] at ihp ihq ⊢
      exact .andIntro ihp ihq
  | orIntro p ih =>
      rw [embedContext_insert,embedContext_insert] at ih
      rw [embedContext_insert]
      exact .orIntro ih
  | botIntro p ih =>
      rw [embedContext_insert]
      exact .botIntro ih

private theorem qf_or_proper {n} (A : Nnf L α n) (h : Weak A) :
    A.QuantifierFree ∨ ProperWeak A := by
  cases A <;> simp_all [Weak,ProperWeak,Nnf.QuantifierFree,Nnf.read,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.QuantifierFree]

private theorem qf_not_proper {n} (A : Nnf L α n) (h : A.QuantifierFree) :
    ¬ ProperWeak A := by
  cases A <;> simp_all [ProperWeak,Nnf.QuantifierFree,Nnf.read,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.QuantifierFree]

private theorem fixed_member {Δ Λ : Sequent L α} (hΛ : ContextProper Λ)
    {A : Nnf L α 0} (hA : ¬ ProperWeak A) (hm : A ∈ Δ ∪ Λ) : A ∈ Δ := by
  rcases Finset.mem_union.mp hm with hd | hl
  · exact hd
  · exact False.elim (hA (hΛ A hl))

private theorem proper_member {Δ Λ : Sequent L α} (hΔ : ContextQF Δ)
    {A : Nnf L α 0} (hA : ¬ A.QuantifierFree) (hm : A ∈ Δ ∪ Λ) : A ∈ Λ := by
  rcases Finset.mem_union.mp hm with hd | hl
  · exact False.elim (hA (hΔ A hd))
  · exact hl

@[simp] private theorem read_union (Δ Λ : Sequent L α) :
    readContext (Δ ∪ Λ) = readContext Δ ∪ readContext Λ := Finset.image_union _ _

@[simp] private theorem values_append {Λ : Sequent L α} (xs ys : List (OriginWitness Λ)) :
    values (xs ++ ys) = values xs ∪ values ys := by simp [values]

private def reorigin {Λ : Sequent L α} (B : Nnf L α 1) (t : L.Term α)
    (he : Nnf.ex B ∈ Λ) (w : OriginWitness (insert (B.instantiate t) Λ)) :
    OriginWitness Λ := by
  classical
  by_cases ho : w.origin ∈ Λ
  · exact ⟨w.origin,ho,w.witness⟩
  · have eq : w.origin = B.instantiate t := (Finset.mem_insert.mp w.member).resolve_right ho
    exact ⟨.ex B,he,.step B t (eq ▸ w.witness)⟩

private theorem reorigin_value {Λ : Sequent L α} (B : Nnf L α 1) (t : L.Term α)
    (he : Nnf.ex B ∈ Λ) (w : OriginWitness (insert (B.instantiate t) Λ)) :
    (reorigin B t he w).witness.value = w.witness.value := by
  classical
  by_cases ho : w.origin ∈ Λ
  · have heq : reorigin B t he w = ⟨w.origin,ho,w.witness⟩ := by
      unfold reorigin
      exact dite_eq_left ho
    exact congrArg (fun (z : OriginWitness Λ) => z.witness.value) heq
  · have eq : w.origin = B.instantiate t := (Finset.mem_insert.mp w.member).resolve_right ho
    have heq : reorigin B t he w = ⟨.ex B,he,.step B t (eq ▸ w.witness)⟩ := by
      unfold reorigin
      exact dite_eq_right ho
    have hv := congrArg (fun (z : OriginWitness Λ) => z.witness.value) heq
    refine hv.trans ?_
    cases w with
    | mk origin member witness =>
      dsimp at eq ⊢
      subst origin
      rfl

private theorem values_reorigin {Λ : Sequent L α} (B : Nnf L α 1) (t : L.Term α)
    (he : Nnf.ex B ∈ Λ) (ws : List (OriginWitness (insert (B.instantiate t) Λ))) :
    values (ws.map (reorigin B t he)) = values ws := by
  unfold values
  congr 1
  simp only [List.map_map]
  exact List.map_congr_left (fun w _ => reorigin_value B t he w)

/-- Fixed QF alternatives are kept separate from proper existential origins. -/
def extractWeak {Ξ : Sequent L α} (p : CoreProof L Ξ)
    (Δ Λ : Sequent L α) (hΔ : ContextQF Δ) (hΛ : ContextProper Λ)
    (h : Ξ ⊆ Δ ∪ Λ) : ExtractionResult Δ Λ := by
  classical
  induction p with
  | identity R ts hp hn =>
      have hdpos : Nnf.pos R ts ∈ Δ := fixed_member hΛ (by simp [ProperWeak]) (h hp)
      have hdneg : Nnf.neg R ts ∈ Δ := fixed_member hΛ (by simp [ProperWeak]) (h hn)
      refine ⟨hΔ,hΛ,[],?_⟩
      have base : PropProof (readContext Δ) := .identity
        ⟨_,R,fun i => (ts i).relabel (Sum.elim id Fin.elim0)⟩
        (Finset.mem_image.mpr ⟨_,hdpos,by simp [propositionalize]⟩)
        (Finset.mem_image.mpr ⟨_,hdneg,by simp [propositionalize]⟩)
      exact enlarge base Finset.subset_union_left
  | truth ht =>
      have hd : Nnf.top ∈ Δ := fixed_member hΛ (by simp [ProperWeak]) (h ht)
      refine ⟨hΔ,hΛ,[],?_⟩
      have base : PropProof (readContext Δ) := .truth
        (Finset.mem_image.mpr ⟨_,hd,by simp [propositionalize]⟩)
      exact enlarge base Finset.subset_union_left
  | @andIntro α Γ A B p q ihp ihq =>
      have hd : Nnf.and A B ∈ Δ := fixed_member hΛ (by simp [ProperWeak])
        (h (Finset.mem_insert_self _ _))
      have hab : A.QuantifierFree ∧ B.QuantifierFree := hΔ _ hd
      have hΓ : Γ ⊆ Δ ∪ Λ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : insert A Γ ⊆ insert A Δ ∪ Λ := by intro C hc; simpa using
        (Finset.insert_subset_insert A hΓ hc)
      have hb : insert B Γ ⊆ insert B Δ ∪ Λ := by intro C hc; simpa using
        (Finset.insert_subset_insert B hΓ hc)
      let ea := ihp (insert A Δ) Λ (qf_insert.mpr ⟨hab.1,hΔ⟩) hΛ ha
      let eb := ihq (insert B Δ) Λ (qf_insert.mpr ⟨hab.2,hΔ⟩) hΛ hb
      let ws := ea.witnesses ++ eb.witnesses
      let T := readContext Δ ∪ readContext (values ws)
      have hla : values ea.witnesses ⊆ values ws := by
        dsimp [ws]; rw [values_append]; exact Finset.subset_union_left
      have hlb : values eb.witnesses ⊆ values ws := by
        dsimp [ws]; rw [values_append]; exact Finset.subset_union_right
      have pa : PropProof (insert (propositionalize A) T) := enlarge ea.factor (by
        rw [readContext_insert]; intro C hc
        rcases Finset.mem_union.mp hc with hc | hc
        · rcases Finset.mem_insert.mp hc with rfl | hc
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hc)
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.image_subset_image hla hc)))
      have pb : PropProof (insert (propositionalize B) T) := enlarge eb.factor (by
        rw [readContext_insert]; intro C hc
        rcases Finset.mem_union.mp hc with hc | hc
        · rcases Finset.mem_insert.mp hc with rfl | hc
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hc)
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.image_subset_image hlb hc)))
      refine ⟨hΔ,hΛ,ws,?_⟩
      apply enlarge (ClassicalPropositional.Proof.andIntro pa pb)
      apply Finset.insert_subset_iff.mpr
      refine ⟨?_,Finset.Subset.refl T⟩
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨.and A B,hd,by simp [propositionalize]⟩
  | @orIntro α Γ A B p ih =>
      have hd : Nnf.or A B ∈ Δ := fixed_member hΛ (by simp [ProperWeak])
        (h (Finset.mem_insert_self _ _))
      have hab : A.QuantifierFree ∧ B.QuantifierFree := hΔ _ hd
      have hΓ : Γ ⊆ Δ ∪ Λ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have ha : insert A (insert B Γ) ⊆ insert A (insert B Δ) ∪ Λ := by
        intro C hc; simpa using (Finset.insert_subset_insert A (Finset.insert_subset_insert B hΓ) hc)
      let e := ih (insert A (insert B Δ)) Λ (qf_insert.mpr ⟨hab.1,qf_insert.mpr ⟨hab.2,hΔ⟩⟩) hΛ ha
      let T := readContext Δ ∪ readContext (values e.witnesses)
      have pa : PropProof (insert (propositionalize A) (insert (propositionalize B) T)) := by
        simpa only [readContext_insert,Finset.insert_union] using e.factor
      refine ⟨hΔ,hΛ,e.witnesses,?_⟩
      apply enlarge (ClassicalPropositional.Proof.orIntro pa)
      apply Finset.insert_subset_iff.mpr
      refine ⟨?_,Finset.Subset.refl T⟩
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨.or A B,hd,by simp [propositionalize]⟩
  | @botIntro α Γ p ih =>
      exact ih Δ Λ hΔ hΛ (fun _ hm => h (Finset.mem_insert_of_mem hm))
  | @allIntro α Γ B p ih =>
      have hd : Nnf.all B ∈ Δ := fixed_member hΛ (by simp [ProperWeak])
        (h (Finset.mem_insert_self _ _))
      exact False.elim (hΔ _ hd)
  | @exIntro α Γ B t p ih =>
      have he : Nnf.ex B ∈ Λ := proper_member hΔ (by exact fun hf => hf)
        (h (Finset.mem_insert_self _ _))
      have hw : Weak (B.instantiate t) :=
        (weak_map B _).mpr (hΛ _ he)
      have hΓ : Γ ⊆ Δ ∪ Λ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      by_cases hc : (B.instantiate t).QuantifierFree
      · have hi : insert (B.instantiate t) Γ ⊆ insert (B.instantiate t) Δ ∪ Λ := by
          intro C hm; simpa using (Finset.insert_subset_insert (B.instantiate t) hΓ hm)
        let e := ih (insert (B.instantiate t) Δ) Λ (qf_insert.mpr ⟨hc,hΔ⟩) hΛ hi
        let w : OriginWitness Λ := ⟨.ex B,he,.step B t (.terminal _ hc)⟩
        let ws := e.witnesses ++ [w]
        refine ⟨hΔ,hΛ,ws,?_⟩
        apply enlarge e.factor
        have heq : values ws = insert (B.instantiate t) (values e.witnesses) := by
          dsimp [ws]
          rw [values_append]
          simp [values,w,Witness.value,Finset.union_comm]
        rw [heq,readContext_insert,readContext_insert]
        intro C hm
        simp only [Finset.mem_union,Finset.mem_insert] at hm ⊢
        tauto
      · have hp : ProperWeak (B.instantiate t) := (qf_or_proper _ hw).resolve_left hc
        have hi : insert (B.instantiate t) Γ ⊆ Δ ∪ insert (B.instantiate t) Λ := by
          intro C hm
          rcases Finset.mem_insert.mp hm with rfl | hm
          · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          · rcases Finset.mem_union.mp (hΓ hm) with hd | hl
            · exact Finset.mem_union_left _ hd
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hl)
        have hΛ' : ContextProper (insert (B.instantiate t) Λ) := by
          intro C hm; rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hp
          · exact hΛ _ hm
        let e := ih Δ (insert (B.instantiate t) Λ) hΔ hΛ' hi
        refine ⟨hΔ,hΛ,e.witnesses.map (reorigin B t he),?_⟩
        rw [values_reorigin]
        exact e.factor


/-- Apply the genuine existential constructors at every recorded supplied term. -/
def closeWitness {F : Nnf L α 0} (w : Witness F) {Γ : Sequent L α}
    (p : CoreProof L (insert w.value Γ)) : CoreProof L (insert F Γ) := by
  induction w with
  | terminal A h => exact p
  | step B t w ih => exact .exIntro B t (ih p)

private theorem list_image {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (xs : List γ) (f : γ → δ) : xs.toFinset.image f = (xs.map f).toFinset := by
  ext a
  simp

private def closeList {F : Nnf L α 0} (ws : List (Witness F)) {Γ : Sequent L α}
    (p : CoreProof L (Γ ∪ (ws.map Witness.value).toFinset)) : CoreProof L (insert F Γ) := by
  classical
  induction ws generalizing Γ with
  | nil =>
      have q : CoreProof L Γ := by simpa using p
      exact q.weaken (Finset.subset_insert _ _)
  | cons w ws ih =>
      have q : CoreProof L (insert w.value (Γ ∪ (ws.map Witness.value).toFinset)) := by
        simpa only [List.map_cons,List.toFinset_cons,Finset.union_insert] using p
      have qc := closeWitness w q
      have qi : CoreProof L (insert F Γ ∪ (ws.map Witness.value).toFinset) := by
        simpa only [Finset.insert_union] using qc
      simpa only [Finset.insert_idem] using ih qi

private theorem instantiate_qf {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (ts : Fin n → L.Term α) : (A.instantiateSlots ts).QuantifierFree :=
  (Nnf.quantifierFree_map _ _).mpr h

/-- Reconstruct the exact singleton from the actual nonempty tuple/factor data. -/
def reconstruct {n} (A : Nnf L α n) (H : Certificate A) :
    CoreProof L {existsBlock A} := by
  let ws := H.tuples.map (Witness.ofTuple A H.matrix_qf)
  have heq : embedContext
      (H.tuples.map (fun ts => propositionalize (A.instantiateSlots ts))).toFinset =
      (ws.map Witness.value).toFinset := by
    unfold embedContext ws
    rw [list_image]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro ts hts
    dsimp only [Function.comp_apply]
    rw [embed_propositionalize _ (instantiate_qf A H.matrix_qf ts),Witness.value_tuple A H.matrix_qf,
      Witness.tuple_ofTuple]
  have p : CoreProof L (∅ ∪ (ws.map Witness.value).toFinset) := by
    simpa only [Finset.empty_union,heq] using fromPropositional H.factor
  exact closeList ws p

/-- Fold a finite set of list alternatives by actual bottom/disjunction rules. -/
def foldFactor {γ : Type*} [DecidableEq γ] {Γ : Finset (PropNnf γ)}
    (xs : List (PropNnf γ)) (p : PropProof (Γ ∪ xs.toFinset)) :
    PropProof (insert (disjunction xs) Γ) := by
  classical
  induction xs generalizing Γ with
  | nil =>
      have q : PropProof Γ := by simpa using p
      exact .botIntro q
  | cons A xs ih =>
      have q : PropProof (insert A Γ ∪ xs.toFinset) := by
        simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using p
      have q' := ih q
      have q'' : PropProof (insert A (insert (disjunction xs) Γ)) := by
        simpa only [Finset.insert_comm] using q'
      exact .orIntro q''

def Certificate.disjunctionProof {n} {A : Nnf L α n} (H : Certificate A) :
    PropProof {disjunction (H.tuples.map (fun ts => propositionalize (A.instantiateSlots ts)))} := by
  have p : PropProof (∅ ∪ (H.tuples.map (fun ts => propositionalize (A.instantiateSlots ts))).toFinset) := by
    simpa only [Finset.empty_union] using H.factor
  exact foldFactor _ p

/-- Retain every NNF constructor while replacing each whole atom by its image. -/
def renameAtoms {γ δ : Type*} (f : γ → δ) : PropNnf γ → PropNnf δ
  | .pos a => .pos (f a)
  | .neg a => .neg (f a)
  | .bot => .bot
  | .top => .top
  | .and A B => .and (renameAtoms f A) (renameAtoms f B)
  | .or A B => .or (renameAtoms f A) (renameAtoms f B)

/-- Actual rule copying remains valid for noninjective atom maps. -/
def mapFactorAtoms {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (f : γ → δ) {Γ : Finset (PropNnf γ)} (p : PropProof Γ) :
    PropProof (Γ.image (renameAtoms f)) := by
  classical
  induction p with
  | identity a hp hn =>
      exact .identity (f a) (Finset.mem_image.mpr ⟨_,hp,rfl⟩)
        (Finset.mem_image.mpr ⟨_,hn,rfl⟩)
  | truth ht => exact .truth (Finset.mem_image.mpr ⟨_,ht,rfl⟩)
  | andIntro p q ihp ihq =>
      simp only [Finset.image_insert] at ihp ihq ⊢
      exact .andIntro ihp ihq
  | orIntro p ih =>
      simp only [Finset.image_insert] at ih ⊢
      exact .orIntro ih
  | botIntro p ih =>
      simp only [Finset.image_insert] at ⊢
      exact .botIntro ih

private theorem drop_subst (t : L.Term (α ⊕ Fin 0)) (σ : α → L.Term β) :
    (t.subst (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope σ 0)).relabel
      (Sum.elim id Fin.elim0) = (t.relabel (Sum.elim id Fin.elim0)).subst σ := by
  rw [Lemmatheca.MathematicalLogic.FirstOrderProofs.term_relabel_subst,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel]
  congr 1
  funext x
  cases x with
  | inl a =>
      simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,Term.relabel_relabel]
  | inr i => exact Fin.elim0 i

theorem propositionalize_subst (A : Nnf L α 0) (h : A.QuantifierFree)
    (σ : α → L.Term β) :
    propositionalize (A.subst σ) =
      renameAtoms (Lemmatheca.MathematicalLogic.HerbrandModels.Atom.subst σ) (propositionalize A) := by
  cases A with
  | pos R ts =>
      simp only [Nnf.subst,Nnf.map,propositionalize,renameAtoms,
        Lemmatheca.MathematicalLogic.HerbrandModels.Atom.subst,drop_subst]
  | neg R ts =>
      simp only [Nnf.subst,Nnf.map,propositionalize,renameAtoms,
        Lemmatheca.MathematicalLogic.HerbrandModels.Atom.subst,drop_subst]
  | bot => simp [Nnf.subst,Nnf.map,propositionalize,renameAtoms]
  | top => simp [Nnf.subst,Nnf.map,propositionalize,renameAtoms]
  | and A B =>
      simpa only [Nnf.subst,Nnf.map,propositionalize,renameAtoms] using
        congrArg₂ ClassicalPropositional.Nnf.and
          (propositionalize_subst A h.1 σ) (propositionalize_subst B h.2 σ)
  | or A B =>
      simpa only [Nnf.subst,Nnf.map,propositionalize,renameAtoms] using
        congrArg₂ ClassicalPropositional.Nnf.or
          (propositionalize_subst A h.1 σ) (propositionalize_subst B h.2 σ)
  | all B => exact False.elim h
  | ex B => exact False.elim h
termination_by A

private theorem instantiateSlots_subst {n} (A : Nnf L α n)
    (ts : Fin n → L.Term α) (σ : α → L.Term β) :
    (A.instantiateSlots ts).subst σ =
      (A.subst σ).instantiateSlots (fun i => (ts i).subst σ) := by
  unfold Nnf.instantiateSlots Nnf.subst
  rw [Nnf.map_comp,Nnf.map_comp]
  congr 1
  funext x
  cases x <;> simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_relabel_subst,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars,Term.subst]

/-- Substitution transforms the stored tuple list and its existing factor tree. -/
def Certificate.substitute {n} {A : Nnf L α n} (H : Certificate A)
    (σ : α → L.Term β) : Certificate (A.subst σ) := by
  refine ⟨(Nnf.quantifierFree_map _ _).mpr H.matrix_qf,
    H.tuples.map (fun ts i => (ts i).subst σ),?_,?_⟩
  · intro he
    exact H.nonempty (List.map_eq_nil_iff.mp he)
  · have p := mapFactorAtoms (Lemmatheca.MathematicalLogic.HerbrandModels.Atom.subst σ) H.factor
    have heq :
        (H.tuples.map (fun ts => propositionalize (A.instantiateSlots ts))).toFinset.image
          (renameAtoms (Lemmatheca.MathematicalLogic.HerbrandModels.Atom.subst σ)) =
        ((H.tuples.map (fun ts i => (ts i).subst σ)).map
          (fun ts => propositionalize ((A.subst σ).instantiateSlots ts))).toFinset := by
      rw [list_image]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro ts hts
      dsimp only [Function.comp_apply]
      rw [← propositionalize_subst _ (instantiate_qf A H.matrix_qf ts),instantiateSlots_subst]
    exact heq ▸ p

theorem Certificate.substitute_tuples {n} {A : Nnf L α n} (H : Certificate A)
    (σ : α → L.Term β) :
    (H.substitute σ).tuples = H.tuples.map (fun ts i => (ts i).subst σ) := by rfl

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder.ExistentialHerbrand
