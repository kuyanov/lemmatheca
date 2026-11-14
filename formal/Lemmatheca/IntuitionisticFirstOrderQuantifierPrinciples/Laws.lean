import Lemmatheca.IntuitionisticFirstOrderDeduction.Classical

namespace Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a
variable {L : Language.{u,v}} {α : Type a} {e : Bool}
noncomputable section
set_option maxHeartbeats 1200000
local instance quantifierLawFormulaEq {β : Type a} : DecidableEq (Formula L β) :=
  Classical.decEq _

/-- Include a complete formula into a scope with one unused slot. -/
def vacuous (A : Formula L α) : BoundedFormula L α 1 :=
  A.map (Sum.elim (fun x => .var (.inl x)) Fin.elim0)

theorem vacuous_open (A : Formula L α) :
    (vacuous A).toFormula = A.rename Sum.inl := by
  simp only [vacuous, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr x => exact x.elim0

theorem vacuous_instantiate (A : Formula L α) (t : L.Term α) :
    (vacuous A).instantiate t = A := by
  simp only [vacuous, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp]
  have h : (fun x : α ⊕ Fin 0 =>
      ((Sum.elim (fun x => .var (.inl x)) Fin.elim0 x : L.Term (α ⊕ Fin 1))).subst
        (Sum.elim (fun x => .var (.inl x)) (fun _ => t.relabel Sum.inl))) = Term.var := by
    funext x
    cases x with
    | inl x => rfl
    | inr x => exact x.elim0
  rw [h, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_id]

private theorem open_instance (P : BoundedFormula L α 1) :
    (P.rename (Sum.inl : α → α ⊕ Fin 1)).instantiate (.var (.inr 0)) = P.toFormula := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr x => have hx : x = 0 := Subsingleton.elim _ _; subst x; rfl

private def openAll {Γ : NaturalDeduction.Context L α} {P : BoundedFormula L α 1}
    (h : NaturalDeduction.Proof false e L Γ (.all P)) :
    NaturalDeduction.Proof false e L (NaturalDeduction.liftContext Γ) P.toFormula := by
  have hr := h.rename (Sum.inl : α → α ⊕ Fin 1)
  have he : (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.all P).rename
      (Sum.inl : α → α ⊕ Fin 1) = .all (P.rename Sum.inl) :=
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all P _
  rw [he] at hr
  have hp := NaturalDeduction.Proof.allElim (.var (.inr 0)) hr
  rw [open_instance] at hp
  exact hp

private theorem rename_ex {β : Type a} (P : BoundedFormula L α 1) (f : α → β) :
    (P.ex).rename f = (P.rename f).ex :=
  Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex P _

/-- Specified conversions of actual supplied public intuitionistic certificates. -/
structure CertificateEquivalence (e : Bool) (L : Language.{u,v}) {α : Type a}
    (Γ : NaturalDeduction.Context L α) (A B : Formula L α) where
  forward : NaturalDeduction.Proof false e L Γ A → NaturalDeduction.Proof false e L Γ B
  backward : NaturalDeduction.Proof false e L Γ B → NaturalDeduction.Proof false e L Γ A

def allConjunction (Γ : NaturalDeduction.Context L α) (P Q : BoundedFormula L α 1) :
    CertificateEquivalence e L Γ (.all (.conj P Q)) (.conj (.all P) (.all Q)) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact .conjIntro (.allIntro (.conjElimLeft (openAll h)))
      (.allIntro (.conjElimRight (openAll h)))
  · intro h
    exact .allIntro (.conjIntro (openAll (.conjElimLeft h)) (openAll (.conjElimRight h)))

def exDisjunction (Γ : NaturalDeduction.Context L α) (P Q : BoundedFormula L α 1) :
    CertificateEquivalence e L Γ (.ex (.disj P Q)) (.disj (.ex P) (.ex Q)) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply NaturalDeduction.Proof.exElim h
    have hp : NaturalDeduction.Proof false e L
        (insert (P.disj Q).toFormula (NaturalDeduction.liftContext Γ))
        (.disj P.toFormula Q.toFormula) := .assumption (Finset.mem_insert_self _ _)
    have hleft : NaturalDeduction.Proof false e L
        (insert P.toFormula (insert (P.disj Q).toFormula (NaturalDeduction.liftContext Γ)))
        (.disj (.ex (P.rename Sum.inl)) (.ex (Q.rename Sum.inl))) := by
      apply NaturalDeduction.Proof.disjIntroLeft
      apply NaturalDeduction.Proof.exIntro (.var (.inr 0))
      rw [open_instance]
      exact .assumption (Finset.mem_insert_self _ _)
    have hright : NaturalDeduction.Proof false e L
        (insert Q.toFormula (insert (P.disj Q).toFormula (NaturalDeduction.liftContext Γ)))
        (.disj (.ex (P.rename Sum.inl)) (.ex (Q.rename Sum.inl))) := by
      apply NaturalDeduction.Proof.disjIntroRight
      apply NaturalDeduction.Proof.exIntro (.var (.inr 0))
      rw [open_instance]
      exact .assumption (Finset.mem_insert_self _ _)
    simpa only [NaturalDeduction.liftContext, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using
      NaturalDeduction.Proof.disjElim hp hleft hright
  · intro h
    apply NaturalDeduction.Proof.disjElim h
    · apply NaturalDeduction.Proof.exElim (.assumption (Finset.mem_insert_self _ _))
      have hp : NaturalDeduction.Proof false e L
          (insert P.toFormula (NaturalDeduction.liftContext (insert (.ex P) Γ)))
          (.ex ((P.disj Q).rename Sum.inl)) := by
        apply NaturalDeduction.Proof.exIntro (.var (.inr 0))
        rw [open_instance]
        exact .disjIntroLeft (.assumption (Finset.mem_insert_self _ _))
      simpa only [rename_ex] using hp
    · apply NaturalDeduction.Proof.exElim (.assumption (Finset.mem_insert_self _ _))
      have hp : NaturalDeduction.Proof false e L
          (insert Q.toFormula (NaturalDeduction.liftContext (insert (.ex Q) Γ)))
          (.ex ((P.disj Q).rename Sum.inl)) := by
        apply NaturalDeduction.Proof.exIntro (.var (.inr 0))
        rw [open_instance]
        exact .disjIntroRight (.assumption (Finset.mem_insert_self _ _))
      simpa only [rename_ex] using hp

def exConjunction (Γ : NaturalDeduction.Context L α) (P Q : BoundedFormula L α 1) :
    NaturalDeduction.Proof false e L Γ (.impl (.ex (.conj P Q)) (.conj (.ex P) (.ex Q))) := by
  apply NaturalDeduction.Proof.impIntro
  apply NaturalDeduction.Proof.exElim (.assumption (Finset.mem_insert_self _ _))
  have hp : NaturalDeduction.Proof false e L
      (insert (P.conj Q).toFormula (NaturalDeduction.liftContext (insert (.ex (.conj P Q)) Γ)))
      (.conj (.ex (P.rename Sum.inl)) (.ex (Q.rename Sum.inl))) := by
    apply NaturalDeduction.Proof.conjIntro
    · apply NaturalDeduction.Proof.exIntro (.var (.inr 0))
      rw [open_instance]
      exact .conjElimLeft (.assumption (Finset.mem_insert_self _ _))
    · apply NaturalDeduction.Proof.exIntro (.var (.inr 0))
      rw [open_instance]
      exact .conjElimRight (.assumption (Finset.mem_insert_self _ _))
  simpa only [NaturalDeduction.liftContext, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using hp

def allDisjunction (Γ : NaturalDeduction.Context L α) (P Q : BoundedFormula L α 1) :
    NaturalDeduction.Proof false e L Γ (.impl (.disj (.all P) (.all Q)) (.all (.disj P Q))) := by
  apply NaturalDeduction.Proof.impIntro
  apply NaturalDeduction.Proof.disjElim (.assumption (Finset.mem_insert_self _ _))
  · exact .allIntro (.disjIntroLeft (openAll (.assumption (Finset.mem_insert_self _ _))))
  · exact .allIntro (.disjIntroRight (openAll (.assumption (Finset.mem_insert_self _ _))))

def allImplication (Γ : NaturalDeduction.Context L α) (A : Formula L α) (P : BoundedFormula L α 1) :
    CertificateEquivalence e L Γ (.all (.impl (vacuous A) P)) (.impl A (.all P)) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply NaturalDeduction.Proof.impIntro
    apply NaturalDeduction.Proof.allIntro
    have hi := openAll (h.weaken (Finset.subset_insert A Γ))
    have ha : NaturalDeduction.Proof false e L
        (NaturalDeduction.liftContext (insert A Γ)) (vacuous A).toFormula := by
      rw [vacuous_open]
      exact .assumption (Finset.mem_image.mpr ⟨A, Finset.mem_insert_self _ _, rfl⟩)
    exact .impElim hi ha
  · intro h
    apply NaturalDeduction.Proof.allIntro
    apply NaturalDeduction.Proof.impIntro
    change NaturalDeduction.Proof false e L (insert (vacuous A).toFormula
      (NaturalDeduction.liftContext Γ)) P.toFormula
    rw [vacuous_open]
    have hr : NaturalDeduction.Proof false e L (NaturalDeduction.liftContext Γ)
        (.impl (A.rename Sum.inl) (.all (P.rename Sum.inl))) := by
      have hi := h.rename (Sum.inl : α → α ⊕ Fin 1)
      simpa only [NaturalDeduction.liftContext, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all] using hi
    have hu := NaturalDeduction.Proof.impElim
      (hr.weaken (Finset.subset_insert _ _)) (.assumption (Finset.mem_insert_self _ _))
    have hp := NaturalDeduction.Proof.allElim (.var (.inr 0)) hu
    rw [open_instance] at hp
    exact hp

def exImplication (Γ : NaturalDeduction.Context L α) (A : Formula L α) (P : BoundedFormula L α 1) :
    CertificateEquivalence e L Γ (.impl (.ex P) A) (.all (.impl P (vacuous A))) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply NaturalDeduction.Proof.allIntro
    apply NaturalDeduction.Proof.impIntro
    change NaturalDeduction.Proof false e L (insert P.toFormula
      (NaturalDeduction.liftContext Γ)) (vacuous A).toFormula
    rw [vacuous_open]
    have hr : NaturalDeduction.Proof false e L (NaturalDeduction.liftContext Γ)
        (.impl (.ex (P.rename Sum.inl)) (A.rename Sum.inl)) := by
      have hi := h.rename (Sum.inl : α → α ⊕ Fin 1)
      simpa only [NaturalDeduction.liftContext, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using hi
    apply NaturalDeduction.Proof.impElim (hr.weaken (Finset.subset_insert _ _))
    apply NaturalDeduction.Proof.exIntro (.var (.inr 0))
    rw [open_instance]
    exact .assumption (Finset.mem_insert_self _ _)
  · intro h
    apply NaturalDeduction.Proof.impIntro
    apply NaturalDeduction.Proof.exElim (.assumption (Finset.mem_insert_self _ _))
    have hi := (openAll (h.weaken (Finset.subset_insert (.ex P) Γ))).weaken
      (Finset.subset_insert P.toFormula _)
    have hp := NaturalDeduction.Proof.impElim hi
      (NaturalDeduction.Proof.assumption (Finset.mem_insert_self _ _))
    change NaturalDeduction.Proof false e L _ (vacuous A).toFormula at hp
    rw [vacuous_open] at hp
    exact hp

def negExistential (Γ : NaturalDeduction.Context L α) (P : BoundedFormula L α 1) :
    CertificateEquivalence e L Γ (.neg (.ex P)) (.all (.neg P)) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply NaturalDeduction.Proof.allIntro
    apply NaturalDeduction.Proof.negIntro
    have hr : NaturalDeduction.Proof false e L (NaturalDeduction.liftContext Γ)
        (.neg (.ex (P.rename Sum.inl))) := by
      have hi := h.rename (Sum.inl : α → α ⊕ Fin 1)
      simpa only [NaturalDeduction.liftContext, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using hi
    apply NaturalDeduction.Proof.negElim ?_ (hr.weaken (Finset.subset_insert _ _))
    apply NaturalDeduction.Proof.exIntro (.var (.inr 0))
    rw [open_instance]
    exact .assumption (Finset.mem_insert_self _ _)
  · intro h
    apply NaturalDeduction.Proof.negIntro
    apply NaturalDeduction.Proof.exElim (.assumption (Finset.mem_insert_self _ _))
    exact .negElim (.assumption (Finset.mem_insert_self _ _))
      ((openAll (h.weaken (Finset.subset_insert (.ex P) Γ))).weaken
        (Finset.subset_insert P.toFormula _))

def negativeWitness (Γ : NaturalDeduction.Context L α) (P : BoundedFormula L α 1) :
    NaturalDeduction.Proof false e L Γ (.impl (.ex (.neg P)) (.neg (.all P))) := by
  apply NaturalDeduction.Proof.impIntro
  apply NaturalDeduction.Proof.negIntro
  apply NaturalDeduction.Proof.exElim
    (.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  exact .negElim
    ((openAll (NaturalDeduction.Proof.assumption (Finset.mem_insert_self _ _))).weaken
      (Finset.subset_insert P.neg.toFormula _))
    (.assumption (Finset.mem_insert_self _ _))

/-- The constant-domain schema with its independence condition encoded by vacuous lift. -/
def constantDomain (A : Formula L α) (P : BoundedFormula L α 1) : Formula L α :=
  .impl (.all (.disj (vacuous A) P)) (.disj A (.all P))

end
end Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples
