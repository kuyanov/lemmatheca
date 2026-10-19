import Lemmatheca.MathematicalLogic.CodingFormalProofsConstructors

namespace Lemmatheca.MathematicalLogic.CodingFormalProofs
open FirstOrder FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} (S : EffectiveSignature L)
noncomputable section
local instance : DecidableEq (L.Formula ℕ) := Classical.decEq _

@[simp] theorem namedCode_bot : namedCode S (⊥ : L.Formula ℕ) = botCode := rfl
@[simp] theorem namedCode_imp (A B : L.Formula ℕ) :
    namedCode S (A.imp B) = impCode (namedCode S A) (namedCode S B) := rfl
@[simp] theorem namedCode_neg (A : L.Formula ℕ) :
    namedCode S A.not = negCode (namedCode S A) := rfl
@[simp] theorem namedCode_and (A B : L.Formula ℕ) :
    namedCode S (A ⊓ B) = andCode (namedCode S A) (namedCode S B) := rfl
@[simp] theorem namedCode_or (A B : L.Formula ℕ) :
    namedCode S (A ⊔ B) = orCode (namedCode S A) (namedCode S B) := rfl
@[simp] theorem contextCode_cons (A : L.Formula ℕ) (Γ : List (L.Formula ℕ)) :
    contextCode S (A :: Γ) = contextInsert (namedCode S A) (contextCode S Γ) := by
  exact FiniteSequenceCoding.code_cons _ _

theorem code_assumption (Γ : List (L.Formula ℕ)) (A : L.Formula ℕ) (hA : A ∈ Γ) :
    ∃ d, Der S d (contextCode S Γ) (namedCode S A) := by
  let d := node 100 [contextCode S Γ, namedCode S A]
  have dpos : 0 < d := by dsimp [d, node]; omega
  have hm : namedCode S A ∈ Seq.decode (contextCode S Γ) := by
    simp only [contextCode, Seq.code, Seq.decode, Denumerable.ofNat_encode, List.mem_map]
    exact ⟨A, hA, rfl⟩
  have dform : namedForm S 0 (namedCode S A) = true := named_formula_valid S (A)
  simp only [d] at dpos
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, dpos, hm]

theorem code_conjIntro (Γ : List (L.Formula ℕ)) (A B : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (A)))
    (h1 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (B)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (A ⊓ B)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  obtain ⟨q, qcheck, qctx, qcon⟩ := h1
  let d := node 101 [contextCode S Γ, namedCode S (A ⊓ B), p, q]
  have plt : p < d := child_lt (by simp)
  have qlt : q < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (A ⊓ B)) = true := named_formula_valid S ((A ⊓ B))
  simp only [d] at plt qlt dpos
  simp only [namedCode_and] at plt qlt dpos dform
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon, qlt, qcheck, qctx, qcon]

theorem code_conjElimLeft (Γ : List (L.Formula ℕ)) (A B : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (A ⊓ B)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (A)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  let d := node 102 [contextCode S Γ, namedCode S (A), p, namedCode S B]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (A)) = true := named_formula_valid S ((A))
  simp only [d] at plt dpos
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon]

theorem code_conjElimRight (Γ : List (L.Formula ℕ)) (A B : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (A ⊓ B)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (B)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  let d := node 103 [contextCode S Γ, namedCode S (B), p, namedCode S A]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (B)) = true := named_formula_valid S ((B))
  simp only [d] at plt dpos
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon]

theorem code_disjIntroLeft (Γ : List (L.Formula ℕ)) (A B : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (A)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (A ⊔ B)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  let d := node 104 [contextCode S Γ, namedCode S (A ⊔ B), p, namedCode S B]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (A ⊔ B)) = true := named_formula_valid S ((A ⊔ B))
  simp only [d] at plt dpos
  simp only [namedCode_or] at plt dpos dform
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon]

theorem code_disjIntroRight (Γ : List (L.Formula ℕ)) (A B : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (B)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (A ⊔ B)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  let d := node 105 [contextCode S Γ, namedCode S (A ⊔ B), p, namedCode S A]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (A ⊔ B)) = true := named_formula_valid S ((A ⊔ B))
  simp only [d] at plt dpos
  simp only [namedCode_or] at plt dpos dform
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon]

theorem code_disjElim (Γ : List (L.Formula ℕ)) (A B C : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (A ⊔ B)))
    (h1 : ∃ d, Der S d (contextCode S (A :: Γ)) (namedCode S (C)))
    (h2 : ∃ d, Der S d (contextCode S (B :: Γ)) (namedCode S (C)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (C)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  obtain ⟨q, qcheck, qctx, qcon⟩ := h1
  obtain ⟨r, rcheck, rctx, rcon⟩ := h2
  let d := node 106 [contextCode S Γ, namedCode S (C), p, q, r, namedCode S A, namedCode S B]
  have plt : p < d := child_lt (by simp)
  have qlt : q < d := child_lt (by simp)
  have rlt : r < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (C)) = true := named_formula_valid S ((C))
  simp only [d] at plt qlt rlt dpos
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon, qlt, qcheck, qctx, qcon, rlt, rcheck, rctx, rcon]

theorem code_impIntro (Γ : List (L.Formula ℕ)) (A B : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (A :: Γ)) (namedCode S (B)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (A.imp B)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  let d := node 107 [contextCode S Γ, namedCode S (A.imp B), p, namedCode S A]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (A.imp B)) = true := named_formula_valid S ((A.imp B))
  simp only [d] at plt dpos
  simp only [namedCode_imp] at plt dpos dform
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon]

theorem code_impElim (Γ : List (L.Formula ℕ)) (A B : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (A.imp B)))
    (h1 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (A)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (B)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  obtain ⟨q, qcheck, qctx, qcon⟩ := h1
  let d := node 108 [contextCode S Γ, namedCode S (B), p, q]
  have plt : p < d := child_lt (by simp)
  have qlt : q < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (B)) = true := named_formula_valid S ((B))
  simp only [d] at plt qlt dpos
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon, qlt, qcheck, qctx, qcon]

theorem code_negIntro (Γ : List (L.Formula ℕ)) (A : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (A :: Γ)) (namedCode S (⊥ : L.Formula ℕ)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (A.not)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  let d := node 109 [contextCode S Γ, namedCode S (A.not), p, namedCode S A]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (A.not)) = true := named_formula_valid S ((A.not))
  simp only [d] at plt dpos
  simp only [namedCode_neg] at plt dpos dform
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon]

theorem code_negElim (Γ : List (L.Formula ℕ)) (A : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (A)))
    (h1 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (A.not)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (⊥ : L.Formula ℕ)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  obtain ⟨q, qcheck, qctx, qcon⟩ := h1
  let d := node 110 [contextCode S Γ, namedCode S (⊥ : L.Formula ℕ), p, q]
  have plt : p < d := child_lt (by simp)
  have qlt : q < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (⊥ : L.Formula ℕ)) = true := named_formula_valid S (⊥ : L.Formula ℕ)
  simp only [d] at plt qlt dpos
  simp only [namedCode_bot] at plt qlt dpos dform
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon, qlt, qcheck, qctx, qcon]

theorem code_falsumElim (Γ : List (L.Formula ℕ)) (A : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (⊥ : L.Formula ℕ)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (A)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  let d := node 111 [contextCode S Γ, namedCode S (A), p]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (A)) = true := named_formula_valid S ((A))
  simp only [d] at plt dpos
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon]

theorem code_classicalContradiction (Γ : List (L.Formula ℕ)) (A : L.Formula ℕ)
    (h0 : ∃ d, Der S d (contextCode S (A.not :: Γ)) (namedCode S (⊥ : L.Formula ℕ)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (A)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  let d := node 112 [contextCode S Γ, namedCode S (A), p]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (A)) = true := named_formula_valid S ((A))
  simp only [d] at plt dpos
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, plt, pcheck, pctx, pcon]

@[simp] theorem namedCode_all (φ : L.BoundedFormula ℕ 1) :
    namedCode S φ.all = allCode (namedCode S φ) := rfl
@[simp] theorem namedCode_ex (φ : L.BoundedFormula ℕ 1) :
    namedCode S φ.ex = exCode (namedCode S φ) := rfl
@[simp] theorem namedCode_equal (s t : L.Term ℕ) :
    namedCode S (s.equal t) = equalCode (termCode S auxName s) (termCode S auxName t) := by
  simp [namedCode, formulaCode, Term.equal, Term.bdEqual, termCode_relabel, Function.comp_def]
@[simp] theorem namedTerm_code (t : L.Term ℕ) :
    namedTerm S (termCode S auxName t) = true :=
  (named_term_recognition_iff S _).mpr ⟨t, rfl⟩

theorem code_allElim (Γ : List (L.Formula ℕ)) (φ : L.BoundedFormula ℕ 1) (t : L.Term ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (φ.all)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (FirstOrderProofs.instantiate φ t)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  let d := node 113 [contextCode S Γ, namedCode S (FirstOrderProofs.instantiate φ t), p, namedCode S φ, termCode S auxName t]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (FirstOrderProofs.instantiate φ t)) = true := named_formula_valid S ((FirstOrderProofs.instantiate φ t))
  simp only [d] at plt dpos
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, named_instantiate, plt, pcheck, pctx, pcon]

theorem code_exIntro (Γ : List (L.Formula ℕ)) (φ : L.BoundedFormula ℕ 1) (t : L.Term ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (FirstOrderProofs.instantiate φ t)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (φ.ex)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  let d := node 114 [contextCode S Γ, namedCode S (φ.ex), p, namedCode S φ, termCode S auxName t]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (φ.ex)) = true := named_formula_valid S ((φ.ex))
  simp only [d] at plt dpos
  simp only [namedCode_ex] at plt dpos dform
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, named_instantiate, plt, pcheck, pctx, pcon]

theorem code_equalIntro (Γ : List (L.Formula ℕ)) (t : L.Term ℕ)
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (t.equal t)) := by
  let d := node 117 [contextCode S Γ, namedCode S (t.equal t), termCode S auxName t]
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (t.equal t)) = true := named_formula_valid S ((t.equal t))
  simp only [d] at dpos
  simp only [namedCode_equal] at dpos dform
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, dpos]

theorem code_equalElim (Γ : List (L.Formula ℕ)) (φ : L.BoundedFormula ℕ 1) (s t : L.Term ℕ)
    (h0 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (s.equal t)))
    (h1 : ∃ d, Der S d (contextCode S (Γ)) (namedCode S (FirstOrderProofs.instantiate φ s)))
    : ∃ d, Der S d (contextCode S Γ) (namedCode S (FirstOrderProofs.instantiate φ t)) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  obtain ⟨q, qcheck, qctx, qcon⟩ := h1
  let d := node 118 [contextCode S Γ, namedCode S (FirstOrderProofs.instantiate φ t), p, q, namedCode S φ, termCode S auxName s, termCode S auxName t]
  have plt : p < d := child_lt (by simp)
  have qlt : q < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have dform : namedForm S 0 (namedCode S (FirstOrderProofs.instantiate φ t)) = true := named_formula_valid S ((FirstOrderProofs.instantiate φ t))
  simp only [d] at plt qlt dpos
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, dpos, contextIncluded_refl, named_instantiate, plt, pcheck, pctx, pcon, qlt, qcheck, qctx, qcon]

theorem code_allIntro (Γ : List (L.Formula ℕ)) (φ : L.BoundedFormula ℕ 1) (c : ℕ)
    (hφ : occursAux c (namedCode S φ) = false)
    (hΓ : contextFresh c (contextCode S Γ) = true)
    (h : ∃ d, Der S d (contextCode S Γ)
      (namedCode S (FirstOrderProofs.instantiate φ (.var c)))) :
    ∃ d, Der S d (contextCode S Γ) (namedCode S φ.all) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h
  let d := node 115 [contextCode S Γ, namedCode S φ.all, p, namedCode S φ, c]
  have plt : p < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have hi : instantiate S (namedCode S φ) (auxName c) =
      namedCode S (FirstOrderProofs.instantiate φ (.var c)) := named_instantiate S φ (.var c)
  have dform : namedForm S 0 (namedCode S φ.all) = true := named_formula_valid S (φ.all)
  simp only [d] at plt dpos
  simp only [namedCode_all] at plt dpos dform
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, plt,
    pcheck, pctx, pcon, dpos, hφ, hΓ, hi, contextIncluded_refl]

theorem code_exElim (Γ : List (L.Formula ℕ)) (φ : L.BoundedFormula ℕ 1) (C : L.Formula ℕ) (c : ℕ)
    (hφ : occursAux c (namedCode S φ) = false)
    (hC : occursAux c (namedCode S C) = false)
    (hΓ : contextFresh c (contextCode S Γ) = true)
    (h0 : ∃ d, Der S d (contextCode S Γ) (namedCode S φ.ex))
    (h1 : ∃ d, Der S d
      (contextCode S (FirstOrderProofs.instantiate φ (.var c) :: Γ)) (namedCode S C)) :
    ∃ d, Der S d (contextCode S Γ) (namedCode S C) := by
  obtain ⟨p, pcheck, pctx, pcon⟩ := h0
  obtain ⟨q, qcheck, qctx, qcon⟩ := h1
  let d := node 116 [contextCode S Γ, namedCode S C, p, q, namedCode S φ, c]
  have plt : p < d := child_lt (by simp)
  have qlt : q < d := child_lt (by simp)
  have dpos : 0 < d := by dsimp [d, node]; omega
  have hi : instantiate S (namedCode S φ) (auxName c) =
      namedCode S (FirstOrderProofs.instantiate φ (.var c)) := named_instantiate S φ (.var c)
  have dform : namedForm S 0 (namedCode S C) = true := named_formula_valid S (C)
  simp only [d] at plt qlt dpos
  refine ⟨d, ?_, by simp [d], by simp [d]⟩
  rw [derivationCheck_eq_local]
  simp [dform, d, localCheck, node_tag, node_args, arg_node, proofHistory_entry, plt, qlt,
    pcheck, pctx, pcon, qcheck, qctx, qcon, dpos, hφ, hC, hΓ, hi, contextIncluded_refl]

end
end Lemmatheca.MathematicalLogic.CodingFormalProofs
