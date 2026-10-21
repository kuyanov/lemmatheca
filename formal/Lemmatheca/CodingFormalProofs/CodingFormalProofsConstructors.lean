import Lemmatheca.CodingFormalProofs.CodingFormalProofsOperations
import Lemmatheca.CodingFormalProofs.CodingFormalProofsRelabel
import Lemmatheca.CodingFormalProofs.CodingFormalProofsChecker

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.CodingFormalProofs
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

@[simp] theorem named_formula_valid (a : L.Formula ℕ) :
    namedForm S 0 (namedCode S a) = true :=
  (named_recognition_iff S 0 _).mpr ⟨a, rfl⟩

@[simp] theorem named_body_valid (a : L.BoundedFormula ℕ 1) :
    namedForm S 1 (namedCode S a) = true :=
  (named_recognition_iff S 1 _).mpr ⟨a, rfl⟩

@[simp] theorem contextCode_valid (Γ : List (L.Formula ℕ)) :
    (Seq.decode (contextCode S Γ)).all (namedForm S 0) = true := by
  simp [contextCode, Seq.code, Seq.decode, List.all_eq_true]

theorem named_imp_iff (a b : ℕ) :
    namedForm S 0 (impCode a b) = true ↔
      namedForm S 0 a = true ∧ namedForm S 0 b = true := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := (named_recognition_iff S 0 _).mp h
    have ht := congrArg tag hA
    cases A with
    | falsum => simp [namedCode, formulaCode, botCode, impCode, node_tag] at ht
    | equal s t => simp [namedCode, formulaCode, equalCode, impCode, node_tag] at ht
    | rel r ts => simp [namedCode, formulaCode, impCode, node_tag] at ht
    | all p => simp [namedCode, formulaCode, allCode, impCode, node_tag] at ht
    | imp p q =>
      have ha := congrArg args hA
      simp [namedCode, formulaCode, impCode, node_args] at ha
      exact ⟨(named_recognition_iff S 0 a).mpr ⟨p, ha.1⟩,
        (named_recognition_iff S 0 b).mpr ⟨q, ha.2⟩⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨A, rfl⟩ := (named_recognition_iff S 0 a).mp ha
    obtain ⟨B, rfl⟩ := (named_recognition_iff S 0 b).mp hb
    exact (named_recognition_iff S 0 _).mpr ⟨A.imp B, rfl⟩

@[simp] theorem arg_node (t : ℕ) (aa : List ℕ) (i : ℕ) :
    arg (node t aa) i = aa[i]?.getD 0 := by
  simp [arg, node_args]

@[simp] theorem proofContext_node (t γ a : ℕ) (rest : List ℕ) :
    proofContext (node t (γ :: a :: rest)) = γ := by
  simp [proofContext, arg_node]

@[simp] theorem proofConclusion_node (t γ a : ℕ) (rest : List ℕ) :
    proofConclusion (node t (γ :: a :: rest)) = a := by
  simp [proofConclusion, arg_node]

theorem contextIncluded_refl (γ : ℕ) : contextIncluded γ γ = true := by
  simp [contextIncluded, List.all_eq_true]

theorem contextIncluded_append_left (γ δ : ℕ) :
    contextIncluded γ (Seq.append γ δ) = true := by
  simp only [contextIncluded, Seq.append, Seq.decode, Denumerable.ofNat_encode, List.all_eq_true,
    decide_eq_true_eq, List.mem_append]
  intro x hx
  exact Or.inl hx

theorem contextIncluded_append_right (γ δ : ℕ) :
    contextIncluded δ (Seq.append γ δ) = true := by
  simp only [contextIncluded, Seq.append, Seq.decode, Denumerable.ofNat_encode, List.all_eq_true,
    decide_eq_true_eq, List.mem_append]
  intro x hx
  exact Or.inr hx

end Lemmatheca.ProofTheory.CodingFormalProofs
