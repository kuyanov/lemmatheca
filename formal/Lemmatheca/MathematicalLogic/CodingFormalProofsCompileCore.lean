import Lemmatheca.MathematicalLogic.CodingFormalProofsCompiler

namespace Lemmatheca.MathematicalLogic.CodingFormalProofs
open FirstOrder FirstOrder.Language FirstOrderProofs
universe u v w
variable {L : Language.{u,v}} (S : EffectiveSignature L)
noncomputable section
local instance {α : Type*} : DecidableEq (L.Formula α) := Classical.decEq _

private theorem named_form_isForm {n e : ℕ} (h : namedForm S n e = true) :
    isForm S n e = true := by
  simp only [namedForm, Bool.and_eq_true] at h
  exact h.1

private theorem fresh_for_context (Γ : List (L.Formula ℕ)) (φ : L.BoundedFormula ℕ 1)
    (A : L.Formula ℕ) :
    ∃ c, occursAux c (namedCode S φ) = false ∧ occursAux c (namedCode S A) = false ∧
      contextFresh c (contextCode S Γ) = true := by
  let es := namedCode S φ :: namedCode S A :: Γ.map (namedCode S)
  let c := freshAux S es
  have hf (e : ℕ) (he : e ∈ es) (hv : ∃ n, isForm S n e = true) : occursAux c e = false :=
    freshAux_absent S es e he hv
  refine ⟨c, hf _ (by simp [es]) ⟨1, named_form_isForm S (named_body_valid S φ)⟩,
    hf _ (by simp [es]) ⟨0, named_form_isForm S (named_formula_valid S A)⟩, ?_⟩
  simp only [contextFresh, contextCode, Seq.code, Seq.decode, Denumerable.ofNat_encode,
    List.all_map, List.all_eq_true]
  intro B hB
  have hb := hf _ (by
    change namedCode S B ∈ namedCode S φ :: namedCode S A :: Γ.map (namedCode S)
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨B, hB, rfl⟩))) ⟨0, named_form_isForm S (named_formula_valid S B)⟩
  simp only [Function.comp_apply, hb, Bool.not_false]

private theorem instantiate_parameter {α : Type w} (φ : L.BoundedFormula α 1)
    (σ : α → L.Term ℕ) (c : ℕ) :
    φ.toFormula.subst (Sum.elim σ (fun _ => .var c)) = FirstOrderProofs.instantiate (φ.subst σ) (.var c) := by
  rw [← instantiate_lifted φ, instantiate_subst, formula_subst_subst]
  rfl

private theorem lifted_context_substitution {α : Type w} (Γ : Finset (L.Formula α))
    (σ : α → L.Term ℕ) (c : ℕ) :
    (liftContext Γ).image (fun a => a.subst (Sum.elim σ (fun _ : Fin 1 => .var c))) =
      Γ.image (fun a => a.subst σ) := by
  simp only [liftContext, Finset.image_image, Function.comp_def, formula_relabel_subst,
    Sum.elim_inl]

/-- Compile the actual core calculus, allowing any substitution of its original
names and a listed target context containing its substituted assumptions. -/
theorem core_coded {α : Type w} {Γ : Finset (L.Formula α)} {A : L.Formula α}
    (h : CoreProof L Γ A) :
    ∀ (σ : α → L.Term ℕ) (Δ : List (L.Formula ℕ)),
      Γ.image (fun a => a.subst σ) ⊆ Δ.toFinset →
      ∃ d, Der S d (contextCode S Δ) (namedCode S (A.subst σ)) := by
  induction h with
  | assumption hA =>
    intro σ Δ hsub
    exact code_assumption S Δ _ (List.mem_toFinset.mp (hsub (Finset.mem_image.mpr ⟨_, hA, rfl⟩)))
  | conjIntro _ _ ihA ihB =>
    intro σ Δ hsub
    simpa only [formula_subst_inf] using code_conjIntro S Δ _ _ (ihA σ Δ hsub) (ihB σ Δ hsub)
  | conjElimLeft _ ih =>
    intro σ Δ hsub
    apply code_conjElimLeft S Δ
    simpa only [formula_subst_inf] using ih σ Δ hsub
  | conjElimRight _ ih =>
    intro σ Δ hsub
    apply code_conjElimRight S Δ
    simpa only [formula_subst_inf] using ih σ Δ hsub
  | disjIntroLeft _ ih =>
    intro σ Δ hsub
    simpa only [formula_subst_sup] using code_disjIntroLeft S Δ _ _ (ih σ Δ hsub)
  | disjIntroRight _ ih =>
    intro σ Δ hsub
    simpa only [formula_subst_sup] using code_disjIntroRight S Δ _ _ (ih σ Δ hsub)
  | @disjElim α Γ A B C _ _ _ ihAB ihA ihB =>
    intro σ Δ hsub
    apply code_disjElim S Δ (A.subst σ) (B.subst σ) (C.subst σ)
    · simpa only [formula_subst_sup] using ihAB σ Δ hsub
    · exact ihA σ _ (by simpa only [Finset.image_insert, List.toFinset_cons] using Finset.insert_subset_insert _ hsub)
    · exact ihB σ _ (by simpa only [Finset.image_insert, List.toFinset_cons] using Finset.insert_subset_insert _ hsub)
  | @impIntro α Γ A B _ ih =>
    intro σ Δ hsub
    simpa only [formula_subst_imp] using code_impIntro S Δ (A.subst σ) (B.subst σ)
      (ih σ _ (by simpa only [Finset.image_insert, List.toFinset_cons] using Finset.insert_subset_insert _ hsub))
  | @impElim α Γ A B _ _ ihAB ihA =>
    intro σ Δ hsub
    apply code_impElim S Δ (A.subst σ) (B.subst σ)
    · simpa only [formula_subst_imp] using ihAB σ Δ hsub
    · exact ihA σ Δ hsub
  | @negIntro α Γ A _ ih =>
    intro σ Δ hsub
    simpa only [formula_subst_not, formula_subst_bot] using code_negIntro S Δ (A.subst σ)
      (by simpa only [formula_subst_bot] using
        ih σ _ (by simpa only [Finset.image_insert, List.toFinset_cons] using Finset.insert_subset_insert _ hsub))
  | @negElim α Γ A _ _ ihA ihN =>
    intro σ Δ hsub
    simpa only [formula_subst_bot] using code_negElim S Δ (A.subst σ)
      (ihA σ Δ hsub) (by simpa only [formula_subst_not] using ihN σ Δ hsub)
  | falsumElim _ ih =>
    intro σ Δ hsub
    apply code_falsumElim S Δ
    simpa only [formula_subst_bot] using ih σ Δ hsub
  | @classicalContradiction α Γ A _ ih =>
    intro σ Δ hsub
    apply code_classicalContradiction S Δ (A.subst σ)
    have hp := ih σ ((A.subst σ).not :: Δ)
      (by simpa only [Finset.image_insert, List.toFinset_cons, formula_subst_not] using Finset.insert_subset_insert _ hsub)
    simpa only [formula_subst_bot] using hp
  | @allElim α Γ φ t _ ih =>
    intro σ Δ hsub
    simpa only [instantiate_subst] using code_allElim S Δ (φ.subst σ) (t.subst σ)
      (by simpa only [formula_subst_all] using ih σ Δ hsub)
  | @exIntro α Γ φ t _ ih =>
    intro σ Δ hsub
    simpa only [formula_subst_ex] using code_exIntro S Δ (φ.subst σ) (t.subst σ)
      (by simpa only [instantiate_subst] using ih σ Δ hsub)
  | @allIntro α Γ φ _ ih =>
    intro σ Δ hsub
    obtain ⟨c, hc, _, hctx⟩ := fresh_for_context S Δ (φ.subst σ) (⊥ : L.Formula ℕ)
    have hp := ih (Sum.elim σ (fun _ => .var c)) Δ
      (by simpa only [lifted_context_substitution] using hsub)
    simpa only [formula_subst_all] using code_allIntro S Δ (φ.subst σ) c hc hctx
      (by simpa only [instantiate_parameter] using hp)
  | @exElim α Γ C φ _ _ ihEx ihC =>
    intro σ Δ hsub
    obtain ⟨c, hcφ, hcC, hctx⟩ := fresh_for_context S Δ (φ.subst σ) (C.subst σ)
    apply code_exElim S Δ (φ.subst σ) (C.subst σ) c hcφ hcC hctx
    · simpa only [formula_subst_ex] using ihEx σ Δ hsub
    · have hp := ihC (Sum.elim σ (fun _ => .var c))
        (FirstOrderProofs.instantiate (φ.subst σ) (.var c) :: Δ)
        (by simpa only [Finset.image_insert, List.toFinset_cons,
          lifted_context_substitution, instantiate_parameter] using Finset.insert_subset_insert _ hsub)
      simpa only [formula_relabel_subst, Sum.elim_inl] using hp
  | equalIntro t =>
    intro σ Δ _
    simpa only [formula_subst_equal] using code_equalIntro S Δ (t.subst σ)
  | @equalElim α Γ φ s t _ _ ihEq ihP =>
    intro σ Δ hsub
    simpa only [instantiate_subst] using code_equalElim S Δ (φ.subst σ) (s.subst σ) (t.subst σ)
      (by simpa only [formula_subst_equal] using ihEq σ Δ hsub)
      (by simpa only [instantiate_subst] using ihP σ Δ hsub)

theorem proof_coded (Γ : List (L.Formula ℕ)) (A : L.Formula ℕ)
    (h : FirstOrderProofs.Proof L Γ.toFinset A) :
    ∃ d, Der S d (contextCode S Γ) (namedCode S A) := by
  let σ : ℕ ⊕ ℕ → L.Term ℕ := Sum.elim Term.var (fun _ => .var 0)
  have hp := core_coded S h σ Γ (by
    simp only [Finset.image_image, Function.comp_def,
      formula_relabel_subst, σ, Sum.elim_inl, formula_subst_var, Finset.image_id']
    exact Finset.Subset.refl _)
  simpa only [formula_relabel_subst, σ, Sum.elim_inl, formula_subst_var] using hp

end
end Lemmatheca.MathematicalLogic.CodingFormalProofs
