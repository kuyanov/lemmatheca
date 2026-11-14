import Lemmatheca.ClassicalFirstOrderDeductionTranslations.Macros

/-! Syntactic translations connect the actual old Prop-valued calculus and the
native Type-valued certificates. The reverse old relation yields Nonempty only. -/
namespace Lemmatheca.ProofTheory.FirstOrder.ClassicalPresentation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w} {c e : Bool}
noncomputable section
local instance translationsFullFormulaEq {K : Language.{u,v}} {δ : Type*} :
    DecidableEq (Formula K δ) := Classical.decEq _
local instance translationsSmallFormulaEq {K : Language.{u,v}} {δ : Type*} :
    DecidableEq (K.Formula δ) := Classical.decEq _

variable {β : Type w}

open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction (Derivation)
open Lemmatheca.MathematicalLogic.FirstOrderProofs (CoreProof)

private theorem expand_insert (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) (A : Formula L α) :
    expandContext (insert A Γ) = insert A.toClassical (expandContext Γ) := by
  simp only [expandContext, Finset.image_insert]
private theorem include_insert (Γ : Finset (L.Formula α)) (A : L.Formula α) :
    includeContext (insert A Γ) = insert (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical A) (includeContext Γ) := by
  simp only [includeContext, Finset.image_insert]
private theorem toClassical_rename (A : Formula L α) (f : α → β) :
    (A.rename f).toClassical = _root_.FirstOrder.Language.Formula.relabel f A.toClassical := by
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_subst, Lemmatheca.MathematicalLogic.FirstOrderProofs.formula_subst_vars]
private theorem expand_lift (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) :
    expandContext (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ) = Lemmatheca.MathematicalLogic.FirstOrderProofs.liftContext (expandContext Γ) := by
  simp only [expandContext, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext, Lemmatheca.MathematicalLogic.FirstOrderProofs.liftContext, Finset.image_image]
  congr 1
  funext A
  exact toClassical_rename A Sum.inl
private theorem include_lift (Γ : Finset (L.Formula α)) :
    includeContext (Lemmatheca.MathematicalLogic.FirstOrderProofs.liftContext Γ) = Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext (includeContext Γ) := by
  simp only [includeContext, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext, Lemmatheca.MathematicalLogic.FirstOrderProofs.liftContext, Finset.image_image]
  congr 1
  funext A
  exact ofClassical_rename A Sum.inl
private theorem expand_include (Γ : Finset (L.Formula α)) :
    expandContext (includeContext Γ) = Γ := by
  simp [expandContext, includeContext, Finset.image_image, Function.comp_def]

/-- Induction on the actual small proof, implementing all abbreviated rules by macros. -/
theorem raw_ofSmall {Γ : Finset (L.Formula α)} {D : L.Formula α}
    (h : Lemmatheca.MathematicalLogic.FirstOrderProofs.CoreProof L Γ D) :
    Nonempty (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true true L (includeContext Γ) (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D)) := by
  induction h with
  | assumption hA => exact ⟨.assumption (Finset.mem_image.mpr ⟨_,hA,rfl⟩)⟩
  | conjIntro _ _ ihA ihB =>
      rcases ihA with ⟨p⟩; rcases ihB with ⟨q⟩
      exact ⟨Raw.conjIntro p q⟩
  | conjElimLeft _ ih =>
      rcases ih with ⟨p⟩; exact ⟨Raw.conjLeft p⟩
  | conjElimRight _ ih =>
      rcases ih with ⟨p⟩; exact ⟨Raw.conjRight p⟩
  | disjIntroLeft _ ih =>
      rcases ih with ⟨p⟩; exact ⟨Raw.disjLeft p⟩
  | disjIntroRight _ ih =>
      rcases ih with ⟨p⟩; exact ⟨Raw.disjRight p⟩
  | disjElim _ _ _ ihAB ihA ihB =>
      rcases ihAB with ⟨p⟩; rcases ihA with ⟨q⟩; rcases ihB with ⟨r⟩
      exact ⟨Raw.disjElim p (by simpa only [include_insert] using q)
        (by simpa only [include_insert] using r)⟩
  | impIntro _ ih =>
      rcases ih with ⟨p⟩
      exact ⟨.impIntro (by simpa only [include_insert] using p)⟩
  | impElim _ _ ihAB ihA =>
      rcases ihAB with ⟨p⟩; rcases ihA with ⟨q⟩; exact ⟨.impElim p q⟩
  | negIntro _ ih =>
      rcases ih with ⟨p⟩
      exact ⟨.impIntro (by simpa only [include_insert] using p)⟩
  | negElim _ _ ihA ihN =>
      rcases ihA with ⟨p⟩; rcases ihN with ⟨q⟩; exact ⟨.impElim q p⟩
  | falsumElim _ ih =>
      rcases ih with ⟨p⟩; exact ⟨.falsumElim p⟩
  | @classicalContradiction α Γ A _ ih =>
      rcases ih with ⟨p⟩
      have q : Derivation true true L (insert (codeNeg (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical A)) (includeContext Γ))
          .falsum := by
        simpa only [include_insert, codeNeg, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical, _root_.FirstOrder.Language.BoundedFormula.not] using p
      refine ⟨.classicalContradiction rfl ?_⟩
      exact .impElim ((Derivation.impIntro q).weaken (Finset.subset_insert _ _))
        (Raw.negToCode (.assumption (Finset.mem_insert_self _ _)))
  | allElim t _ ih =>
      rcases ih with ⟨p⟩
      exact ⟨by simpa only [ofClassical_instantiate] using Derivation.allElim t p⟩
  | exIntro t _ ih =>
      rcases ih with ⟨p⟩
      exact ⟨Raw.exIntro t (by simpa only [ofClassical_instantiate] using p)⟩
  | allIntro _ ih =>
      rcases ih with ⟨p⟩
      exact ⟨.allIntro (by simpa only [include_lift, ofClassical_toFormula] using p)⟩
  | exElim _ _ ihEx ihB =>
      rcases ihEx with ⟨p⟩; rcases ihB with ⟨q⟩
      exact ⟨Raw.exElim p (by simpa only [include_insert, include_lift,
        ofClassical_toFormula, ofClassical_rename] using q)⟩
  | equalIntro t => exact ⟨.equalIntro t rfl⟩
  | equalElim D s t _ _ ihEq ihD =>
      rcases ihEq with ⟨p⟩; rcases ihD with ⟨q⟩
      exact ⟨by
        simpa only [ofClassical_instantiate] using
          (Derivation.equalElim (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D)
            s t rfl p (by simpa only [ofClassical_instantiate] using q))⟩

/-- Read each native rule as its actual existing small-calculus rule. -/
theorem raw_toSmall {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} {A : Formula L α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ A) : Lemmatheca.MathematicalLogic.FirstOrderProofs.CoreProof L (expandContext Γ) A.toClassical := by
  induction p with
  | assumption hA => exact .assumption (Finset.mem_image.mpr ⟨_, hA, rfl⟩)
  | conjIntro _ _ ihA ihB => exact .conjIntro ihA ihB
  | conjElimLeft _ ih => exact .conjElimLeft ih
  | conjElimRight _ ih => exact .conjElimRight ih
  | disjIntroLeft _ ih => exact .disjIntroLeft ih
  | disjIntroRight _ ih => exact .disjIntroRight ih
  | disjElim _ _ _ ihAB ihA ihB =>
      exact .disjElim ihAB (by simpa only [expand_insert] using ihA)
        (by simpa only [expand_insert] using ihB)
  | impIntro _ ih =>
      exact .impIntro (by simpa only [expand_insert] using ih)
  | impElim _ _ ihAB ihA => exact .impElim ihAB ihA
  | @negIntro α Γ A _ ih =>
      apply CoreProof.negIntro
      change CoreProof L (insert A.toClassical (expandContext Γ))
        (_root_.FirstOrder.Language.BoundedFormula.falsum : L.Formula α)
      simpa only [expand_insert, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical] using ih
  | negElim _ _ ihA ihN => exact .negElim ihA ihN
  | falsumElim _ ih => exact .falsumElim ih
  | @classicalContradiction α Γ A _ _ ih =>
      apply CoreProof.classicalContradiction
      change CoreProof L (insert A.toClassical.not (expandContext Γ))
        (_root_.FirstOrder.Language.BoundedFormula.falsum : L.Formula α)
      simpa only [expand_insert, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical] using ih
  | allElim t _ ih =>
      simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_instantiate] using CoreProof.allElim t ih
  | exIntro t _ ih =>
      exact .exIntro t (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_instantiate] using ih)
  | allIntro _ ih =>
      exact .allIntro (by simpa only [expand_lift, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_toFormula] using ih)
  | exElim _ _ ihEx ihB =>
      exact .exElim ihEx (by simpa only [expand_insert, expand_lift,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_toFormula, toClassical_rename] using ihB)
  | equalIntro t _ => exact .equalIntro t
  | equalElim D s t _ _ _ ihEq ihD =>
      simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_instantiate] using
        CoreProof.equalElim D.toClassical s t ihEq
          (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_instantiate] using ihD)

theorem raw_small_iff (Γ : Finset (L.Formula α)) (D : L.Formula α) :
    Lemmatheca.MathematicalLogic.FirstOrderProofs.CoreProof L Γ D ↔
      Nonempty (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true true L (includeContext Γ) (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D)) := by
  constructor
  · exact raw_ofSmall
  · rintro ⟨p⟩
    simpa only [expand_include, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_ofClassical] using raw_toSmall p

private theorem expanded_open {n} (B : BF L α n) :
    expanded B.toFormula = (expanded B).toFormula := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
  rw [expanded_map]

private theorem instantiate_fresh (B : BF L α 1) :
    (B.rename (Sum.inl : α → α ⊕ Fin 1)).instantiate (.var (.inr 0)) = B.toFormula := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr i => rw [Fin.eq_zero i]; rfl

private theorem codeEx_rename (B : BF L α 1) (f : α → β) :
    (codeEx B).rename f = codeEx (B.rename f) := by
  simp only [codeEx, codeNeg, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all]

private theorem all_rename (B : BF L α 1) (f : α → β) :
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.all B).rename f = Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.all (B.rename f) := by
  exact Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all B (fun x => .var (f x))
private theorem ex_rename (B : BF L α 1) (f : α → β) :
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex B).rename f = Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex (B.rename f) := by
  exact Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex B (fun x => .var (f x))

private abbrev Conversions (e : Bool) (A : Formula L α) :=
  (∀ {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α}, Derivation true e L Γ A → Derivation true e L Γ (expanded A)) ×
  (∀ {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α}, Derivation true e L Γ (expanded A) → Derivation true e L Γ A)

/-- Source-depth recursion, generalized over all free-name types and contexts.
The two maps are built together, using the already proved exact code rules. -/
private def conversions (e : Bool) (A : Formula L α) : Conversions e A := by
  let build : (n : ℕ) → ∀ {β : Type w} (B : Formula L β), B.depth < n → Conversions e B := by
    intro n
    induction n with
    | zero => intro β B h; exact False.elim (Nat.not_lt_zero _ h)
    | succ n ih =>
      intro β B h
      cases B with
      | falsum => exact ⟨fun p => p, fun p => p⟩
      | equal s t => exact ⟨fun p => p, fun p => p⟩
      | rel R ts => exact ⟨fun p => p, fun p => p⟩
      | neg C =>
        have hc : C.depth < n := by change C.depth + 1 < n+1 at h; omega
        let ic := ih C hc
        constructor
        · intro Γ p
          apply Derivation.impIntro
          exact .negElim (ic.2 (.assumption (Finset.mem_insert_self _ _)))
            (p.weaken (Finset.subset_insert _ _))
        · intro Γ p
          apply Derivation.negIntro
          exact .impElim (p.weaken (Finset.subset_insert _ _))
            (ic.1 (.assumption (Finset.mem_insert_self _ _)))
      | conj C D =>
        have hc : C.depth < n := by change max C.depth D.depth + 1 < n+1 at h; omega
        have hd : D.depth < n := by change max C.depth D.depth + 1 < n+1 at h; omega
        let ic := ih C hc; let id := ih D hd
        exact ⟨fun p => Raw.conjIntro (ic.1 (.conjElimLeft p)) (id.1 (.conjElimRight p)),
          fun p => .conjIntro (ic.2 (Raw.conjLeft p)) (id.2 (Raw.conjRight p))⟩
      | disj C D =>
        have hc : C.depth < n := by change max C.depth D.depth + 1 < n+1 at h; omega
        have hd : D.depth < n := by change max C.depth D.depth + 1 < n+1 at h; omega
        let ic := ih C hc; let id := ih D hd
        constructor
        · intro Γ p
          exact .disjElim p
            (Raw.disjLeft (ic.1 (.assumption (Finset.mem_insert_self _ _))))
            (Raw.disjRight (id.1 (.assumption (Finset.mem_insert_self _ _))))
        · intro Γ p
          exact Raw.disjElim p
            (.disjIntroLeft (ic.2 (.assumption (Finset.mem_insert_self _ _))))
            (.disjIntroRight (id.2 (.assumption (Finset.mem_insert_self _ _))))
      | impl C D =>
        have hc : C.depth < n := by change max C.depth D.depth + 1 < n+1 at h; omega
        have hd : D.depth < n := by change max C.depth D.depth + 1 < n+1 at h; omega
        let ic := ih C hc; let id := ih D hd
        constructor
        · intro Γ p
          apply Derivation.impIntro
          exact id.1 (.impElim (p.weaken (Finset.subset_insert _ _))
            (ic.2 (.assumption (Finset.mem_insert_self _ _))))
        · intro Γ p
          apply Derivation.impIntro
          exact id.2 (.impElim (p.weaken (Finset.subset_insert _ _))
            (ic.1 (.assumption (Finset.mem_insert_self _ _))))
      | all C =>
        have hc : C.toFormula.depth < n := by
          change C.depth + 1 < n+1 at h
          simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map] using (show C.depth < n by omega)
        let ic := ih C.toFormula hc
        constructor
        · intro Γ p
          apply Derivation.allIntro
          have pl : Derivation true e L (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ) (.all (C.rename Sum.inl)) := by
            simpa only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext, all_rename] using p.rename (Sum.inl : β → β ⊕ Fin 1)
          have pc := Derivation.allElim (.var (.inr 0)) pl
          rw [instantiate_fresh] at pc
          change Derivation true e L (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ) (expanded C).toFormula
          rw [← expanded_open]
          exact ic.1 pc
        · intro Γ p
          change Derivation true e L Γ (.all (expanded C)) at p
          apply Derivation.allIntro
          have pl : Derivation true e L (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ) (.all ((expanded C).rename Sum.inl)) := by
            simpa only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext, all_rename] using p.rename (Sum.inl : β → β ⊕ Fin 1)
          have pc := Derivation.allElim (.var (.inr 0)) pl
          rw [instantiate_fresh] at pc
          exact ic.2 (by simpa only [expanded_open] using pc)
      | ex C =>
        have hc : C.toFormula.depth < n := by
          change C.depth + 1 < n+1 at h
          simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map] using (show C.depth < n by omega)
        let ic := ih C.toFormula hc
        constructor
        · intro Γ p
          apply Derivation.exElim p
          have pc := ic.1 (Derivation.assumption
            (Finset.mem_insert_self C.toFormula (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ)))
          have pi : Derivation true e L (insert C.toFormula (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ))
              (((expanded C).rename Sum.inl).instantiate (.var (.inr 0))) := by
            simpa only [instantiate_fresh, expanded_open] using pc
          change Derivation true e L
            (insert C.toFormula (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ))
            ((codeEx (expanded C)).rename (Sum.inl : β → β ⊕ Fin 1))
          rw [codeEx_rename]
          exact Raw.exIntro (.var (.inr 0)) pi
        · intro Γ p
          apply Raw.exElim p
          have pc := ic.2 (by
            simpa only [expanded_open] using
              (Derivation.assumption (Finset.mem_insert_self (expanded C).toFormula
                (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ)) : Derivation true e L
                  (insert (expanded C).toFormula (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ)) (expanded C).toFormula))
          have pi : Derivation true e L (insert (expanded C).toFormula (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ))
              ((C.rename Sum.inl).instantiate (.var (.inr 0))) := by
            simpa only [instantiate_fresh] using pc
          simpa only [ex_rename] using Derivation.exIntro (.var (.inr 0)) pi
  exact build (A.depth+1) A (Nat.lt_succ_self _)

private theorem include_expand (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) :
    includeContext (expandContext Γ) = Γ.image expanded := by
  simp only [includeContext, expandContext, Finset.image_image]
  rfl

/-- Convert the supplied full proof to exactly the expansion of its conclusion. -/
def Raw.toExpanded {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} {A : Formula L α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ A) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ (expanded A) := by
  exact (conversions e A).1 p

/-- Convert a supplied expansion proof back to its specified original full formula. -/
def Raw.fromExpanded {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} (A : Formula L α)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ (expanded A)) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ A := by
  exact (conversions e A).2 p

theorem raw_full_iff (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) (A : Formula L α) :
    Nonempty (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true true L Γ A) ↔
      Lemmatheca.MathematicalLogic.FirstOrderProofs.CoreProof L (expandContext Γ) A.toClassical := by
  constructor
  · rintro ⟨p⟩; exact raw_toSmall p
  · intro h
    rcases raw_ofSmall h with ⟨q⟩
    have q' : Derivation true true L (Γ.image expanded) (expanded A) := by
      simpa only [include_expand, expanded] using q
    have supply : ∀ B ∈ Γ.image expanded, Derivation true true L Γ B := by
      intro B hB
      have hx := Finset.mem_image.mp hB
      let F := Classical.choose hx
      have hF := Classical.choose_spec hx
      have pF : Derivation true true L Γ (expanded F) :=
        Raw.toExpanded (.assumption hF.1)
      exact hF.2 ▸ pF
    exact ⟨Raw.fromExpanded A (q'.replace supply)⟩

end
end Lemmatheca.ProofTheory.FirstOrder.ClassicalPresentation
