import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityBasic
import Lemmatheca.MathematicalLogic.CodingFormalProofsEffective

/-! Proof search recovers a total numerical function from a graph formula that
strongly represents it in the actual Robinson theory and shared proof calculus.
The coding bridge below concerns the corpus's existing sentence codes. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticRepresentability

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories FirstOrderProofs
open CodingFormalProofs

noncomputable section

private theorem primrec_termCode_subst {α β γ : Type*} [Primcodable γ]
    (t : language.Term α) (name : β → ℕ) (σ : γ → α → language.Term β)
    (hσ : ∀ i, Primrec (fun x => termCode arithmeticSignature name (σ x i))) :
    Primrec (fun x => termCode arithmeticSignature name (t.subst (σ x))) := by
  induction t with
  | var i => exact hσ i
  | func f ts ih =>
    exact primrec_node.comp (Primrec.const 2)
      (Primrec.list_cons.comp (Primrec.const (arithFunctionCode f))
        (Primrec.list_ofFn ih))

private theorem primrec_formulaCode_subst {α β γ : Type*} [Primcodable γ]
    {k : ℕ} (φ : language.BoundedFormula α k) (name : β → ℕ)
    (σ : γ → α → language.Term β)
    (hσ : ∀ i, Primrec (fun x => termCode arithmeticSignature name (σ x i))) :
    Primrec (fun x => formulaCode arithmeticSignature name (φ.subst (σ x))) := by
  have hlift (k : ℕ) : ∀ i : α ⊕ Fin k, Primrec (fun x =>
      termCode arithmeticSignature (Sum.elim name (fun j => boundName j.val))
        ((Sum.elim (Term.relabel Sum.inl ∘ σ x) (Term.var ∘ Sum.inr)) i)) := by
    intro i
    cases i with
    | inl i =>
      simpa only [Sum.elim_inl, Function.comp_apply, termCode_relabel,
        Sum.elim_comp_inl] using hσ i
    | inr i => exact Primrec.const (boundName i.val)
  induction φ with
  | falsum => exact Primrec.const botCode
  | equal s t =>
    exact primrec_node.comp (Primrec.const 4)
      (Primrec.list_cons.comp
        (primrec_termCode_subst s _ _ (hlift _))
        (Primrec.list_cons.comp (primrec_termCode_subst t _ _ (hlift _))
          (Primrec.const [])))
  | rel r ts => exact r.elim
  | imp a b iha ihb =>
    exact primrec_node.comp (Primrec.const 6)
      (Primrec.list_cons.comp iha (Primrec.list_cons.comp ihb (Primrec.const [])))
  | all a ih =>
    exact primrec_node.comp (Primrec.const 7)
      (Primrec.list_cons.comp ih (Primrec.const []))

/-- Substituting numerals into a fixed formula computes the codes used by the
existing proof checker, rather than a separately chosen syntax encoding. -/
theorem numeralInstance_code_primrec {α γ : Type*} [Primcodable γ]
    (φ : language.Formula α) (v : γ → α → ℕ)
    (hv : ∀ i, Primrec (fun x => v x i)) :
    Primrec (fun x => sentenceCode arithmeticSignature (numeralInstance φ (v x))) := by
  apply primrec_formulaCode_subst φ Empty.elim (fun x i => numeral (v x i))
  intro i
  exact ((numeral_primrec 0 1).comp (hv i)).of_eq fun x =>
    arithmetic_numeral_code (v x i)

/-- The effective presentation enumerates exactly the seven actual Q axioms. -/
theorem Q_code_enumerable : CodeEnumerable arithmeticSignature Q := by
  let codes := [sentenceCode arithmeticSignature qSuccNeZero,
    sentenceCode arithmeticSignature qSuccInjective,
    sentenceCode arithmeticSignature qPredecessor,
    sentenceCode arithmeticSignature qAddZero,
    sentenceCode arithmeticSignature qAddSucc,
    sentenceCode arithmeticSignature qMulZero,
    sentenceCode arithmeticSignature qMulSucc]
  have hc : PrimrecPred (fun n => n ∈ codes) := by
    have hh : PrimrecRel (fun a b : ℕ => a = b) := Primrec.eq
    exact (hh.exists_mem_list.comp (Primrec.const codes) Primrec.id).of_eq (by simp)
  apply hc.computablePred.to_re.of_eq
  intro n
  simp [codes, Q, eq_comm]

theorem realize_numeralInstance {α M : Type*} [language.Structure M]
    (φ : language.Formula α) (v : α → ℕ) :
    M ⊨ numeralInstance φ v ↔ φ.Realize (fun i => numeralValue M (v i)) := by
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simp only [numeralInstance, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_subst, numeralValue, he]

/-- The actual Q theorems at numeral graph instances recover precisely the
value of a strongly represented total function. -/
theorem numeralInstance_derives_iff {n : ℕ} {f : (Fin n → ℕ) → ℕ}
    {φ : language.Formula (Fin n ⊕ Unit)} (h : StronglyRepresents f φ)
    (x : Fin n → ℕ) (b : ℕ) :
    Derives Q (numeralInstance φ (extend x b)) ↔ b = f x := by
  constructor
  · intro hb
    have : ℕ ⊨ Q := nat_models_Q
    have hn : ℕ ⊨ numeralInstance φ (extend x b) := by
      unfold Sentence.Realize
      apply derives_sound hb
      intro B hB
      exact Theory.realize_sentence_of_mem Q hB
    have hh := (realize_numeralInstance φ (extend x b)).mp hn
    have hv : (fun i => numeralValue ℕ (extend x b i)) =
        extend (fun i => numeralValue ℕ (x i)) (numeralValue ℕ b) := by
      funext i
      cases i <;> rfl
    rw [hv] at hh
    simpa only [numeral_value_nat] using
      (stronglyRepresents_modelwise h x (numeralValue ℕ b)).mp hh
  · rintro rfl
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    apply (realize_numeralInstance φ (extend x (f x))).mpr
    have hv : (fun i => numeralValue M (extend x (f x) i)) =
        extend (fun i => numeralValue M (x i)) (numeralValue M (f x)) := by
      funext i
      cases i <;> rfl
    rw [hv]
    exact (stronglyRepresents_modelwise h x (numeralValue M (f x))).mpr rfl

/-- Numeralwise representation makes a total finite-arity function computable
by searching genuine proof certificates for its graph instances. -/
theorem computable_of_stronglyRepresents {n : ℕ} {f : (Fin n → ℕ) → ℕ}
    {φ : language.Formula (Fin n ⊕ Unit)} (h : StronglyRepresents f φ) :
    Computable f := by
  obtain ⟨E, hE, hT⟩ := enumerable_theory_certificates arithmeticSignature Q Q_code_enumerable
  let code (x : Fin n → ℕ) (b : ℕ) :=
    sentenceCode arithmeticSignature (numeralInstance φ (extend x b))
  have hc : Primrec₂ code := by
    apply numeralInstance_code_primrec φ (fun p : (Fin n → ℕ) × ℕ => extend p.1 p.2)
    intro i
    cases i with
    | inl i => exact Primrec.fin_app.comp Primrec.fst (Primrec.const i)
    | inr i => exact Primrec.snd
  let P (x : Fin n → ℕ) (w : ℕ) : Prop :=
    certificateCheck arithmeticSignature E w.unpair.1 (code x w.unpair.2) = true
  have hP : PrimrecRel P :=
    Primrec.eq.comp
      ((primrec_certificateCheck arithmeticSignature E hE).comp
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (hc.comp Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      (Primrec.const true)
  have hex (x : Fin n → ℕ) : ∃ w, P x w := by
    have hd : Derives (theory arithmeticSignature E) (numeralInstance φ (extend x (f x))) := by
      rw [hT]
      exact (numeralInstance_derives_iff h x (f x)).mpr rfl
    obtain ⟨p, hp⟩ := (certificate_iff_derives arithmeticSignature E _).mpr hd
    exact ⟨Nat.pair p (f x), by simpa [P, code] using hp⟩
  have hs : Computable (fun x => Nat.find (hex x)) :=
    Computable.find hP.computablePred hex
  apply (Computable.snd.comp (Computable.unpair.comp hs)).of_eq
  intro x
  have hp := Nat.find_spec (hex x)
  have hd : Derives (theory arithmeticSignature E)
      (numeralInstance φ (extend x (Nat.find (hex x)).unpair.2)) :=
    (certificate_iff_derives arithmeticSignature E _).mp ⟨_, hp⟩
  rw [hT] at hd
  exact (numeralInstance_derives_iff h x _).mp hd

end
end Lemmatheca.MathematicalLogic.ArithmeticRepresentability
