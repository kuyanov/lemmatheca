import Lemmatheca.MathematicalLogic.FormalizedProvabilityBasic
import Lemmatheca.MathematicalLogic.FormalizedProvabilityTransformations

/-! Three levels of reasoning about a specified proof predicate: external
certificate manipulation, numeralwise Q-proofs, and internal derivability
conditions. The last are defined, not silently inferred from the first two. -/
namespace Lemmatheca.MathematicalLogic.FormalizedProvability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs CodingFormalProofs
noncomputable section

/-- The sentence instance demanded by the second derivability condition. -/
def modusPonensSentence {T : language.Theory} (P : ProofRepresentation T)
    (σ τ : language.Sentence) : language.Sentence :=
  (provabilitySentence P (σ.imp τ)).imp
    ((provabilitySentence P σ).imp (provabilitySentence P τ))

/-- The sentence instance demanded by positive introspection. -/
def introspectionSentence {T : language.Theory} (P : ProofRepresentation T)
    (σ : language.Sentence) : language.Sentence :=
  (provabilitySentence P σ).imp
    (provabilitySentence P (provabilitySentence P σ))

/-- D2 is an internal proof schema, rather than merely standard-model truth. -/
def DerivabilityTwo {T : language.Theory} (P : ProofRepresentation T) : Prop :=
  ∀ σ τ : language.Sentence, Derives T (modusPonensSentence P σ τ)

/-- D3 is an internal proof schema, rather than an external application of D1. -/
def DerivabilityThree {T : language.Theory} (P : ProofRepresentation T) : Prop :=
  ∀ σ : language.Sentence, Derives T (introspectionSentence P σ)

/-- Combining external proofs gives truth of D2 in the standard model. -/
theorem modusPonensSentence_standard {T : language.Theory} (P : ProofRepresentation T)
    (σ τ : language.Sentence) : ℕ ⊨ modusPonensSentence P σ τ := by
  simp only [modusPonensSentence, Sentence.realize_imp, provabilitySentence_standard]
  intro himp hσ
  have hh := derives_cut hσ (derives_imp_iff.mp himp)
  simpa only [Set.union_self] using hh

/-- D1 gives standard truth of positive introspection, without supplying D3. -/
theorem introspectionSentence_standard {T : language.Theory} (P : ProofRepresentation T)
    (hQ : Q ⊆ T) (σ : language.Sentence) : ℕ ⊨ introspectionSentence P σ := by
  simp only [introspectionSentence, Sentence.realize_imp, provabilitySentence_standard]
  exact derivability_one P hQ σ

/-- A specified syntactic consistency sentence for this proof predicate. -/
def consistencySentence {T : language.Theory} (P : ProofRepresentation T) :
    language.Sentence := (provabilitySentence P ⊥).not

/-- The consistency sentence is true exactly when the actual calculus is consistent. -/
theorem consistencySentence_standard {T : language.Theory} (P : ProofRepresentation T) :
    ℕ ⊨ consistencySentence P ↔ Consistent T := by
  rw [consistencySentence, Sentence.realize_not, provabilitySentence_standard]
  rfl

/-- Standard reflection for every sentence is exactly standard-model soundness. -/
theorem standard_reflection_iff_sound {T : language.Theory} (P : ProofRepresentation T) :
    (∀ σ : language.Sentence, ℕ ⊨ (provabilitySentence P σ).imp σ) ↔
      ∀ σ : language.Sentence, Derives T σ → ℕ ⊨ σ := by
  simp only [Sentence.realize_imp, provabilitySentence_standard]

/-- A numeralwise instance of the certified modus-ponens transformation, proved
in Q for every fixed triple of codes; proof codes are not quantified internally. -/
theorem modusPonens_numeralwise (E : ℕ → ℕ → Bool) (hE : Primrec₂ E)
    (p q a b : ℕ) (hb : isSentence arithmeticSignature b = true) :
    Derives Q ((proofInstance (certificateRepresentation E hE) p (impCode a b)).imp
      ((proofInstance (certificateRepresentation E hE) q a).imp
        (proofInstance (certificateRepresentation E hE) (modusPonensCertificate p q b) b))) := by
  let P := certificateRepresentation E hE
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  simp only [Sentence.realize_imp, proofInstance, realize_numeralInstance]
  rw [proofFormula_numerals P M p (impCode a b),
    proofFormula_numerals P M q a,
    proofFormula_numerals P M (modusPonensCertificate p q b) b]
  simp only [P, certificateRepresentation_check]
  intro hp hq
  exact modusPonensCertificate_accepted arithmeticSignature E p q a b hp hq hb

/-- The actual syntactic operation which inserts a numeral in the chosen
provability formula. It is defined also on numbers which are not sentence codes. -/
def provabilityCode {T : language.Theory} (P : ProofRepresentation T) (n : ℕ) : ℕ :=
  sentenceCode arithmeticSignature
    (numeralInstance (provabilityFormula P) (fun _ => n))

theorem provabilityCode_primitive {T : language.Theory} (P : ProofRepresentation T) :
    Primrec (provabilityCode P) :=
  numeralInstance_code_primrec (provabilityFormula P) (fun n _ => n) (fun _ => Primrec.id)

/-- A successful external proof has an external proof of its provability
instance in the same actual certificate system. -/
theorem introspection_certificate_exists (E : ℕ → ℕ → Bool) (hE : Primrec₂ E)
    (hQ : Q ⊆ theory arithmeticSignature E) (p n : ℕ)
    (hp : certificateCheck arithmeticSignature E p n = true) :
    ∃ q, certificateCheck arithmeticSignature E q
      (provabilityCode (certificateRepresentation E hE) n) = true := by
  have hs : isSentence arithmeticSignature n = true := by
    simp only [certificateCheck, Bool.and_eq_true] at hp
    exact hp.1.1.2
  obtain ⟨σ, hσ⟩ := (sentence_recognition_iff arithmeticSignature n).mp hs
  have hσp : Derives (theory arithmeticSignature E) σ := by
    apply (certificate_iff_derives arithmeticSignature E σ).mp
    exact ⟨p, hσ ▸ hp⟩
  have hh := derivability_one (certificateRepresentation E hE) hQ σ hσp
  have hc := (certificate_iff_derives arithmeticSignature E _).mpr hh
  simpa only [provabilitySentence, provabilityCode, hσ] using hc

/-- Searching genuine proofs gives a total computable introspection compiler.
Its correctness is conditional only on the input being an accepted certificate;
invalid inputs also terminate. No primitive-recursive bound is asserted. -/
theorem computable_introspection_compiler (E : ℕ → ℕ → Bool) (hE : Primrec₂ E)
    (hQ : Q ⊆ theory arithmeticSignature E) :
    ∃ f : ℕ × ℕ → ℕ, Computable f ∧ ∀ p n,
      certificateCheck arithmeticSignature E p n = true →
      certificateCheck arithmeticSignature E (f (p, n))
        (provabilityCode (certificateRepresentation E hE) n) = true := by
  let R (x : ℕ × ℕ) (q : ℕ) : Prop :=
    certificateCheck arithmeticSignature E x.1 x.2 ≠ true ∨
      certificateCheck arithmeticSignature E q
        (provabilityCode (certificateRepresentation E hE) x.2) = true
  have hr : PrimrecRel R := by
    apply PrimrecPred.or
    · exact (Primrec.eq.comp ((primrec_certificateCheck arithmeticSignature E hE).comp
        (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
        (Primrec.const true)).not
    · exact Primrec.eq.comp
        ((primrec_certificateCheck arithmeticSignature E hE).comp Primrec.snd
          ((provabilityCode_primitive (certificateRepresentation E hE)).comp
            (Primrec.snd.comp Primrec.fst))) (Primrec.const true)
  have hex (x : ℕ × ℕ) : ∃ q, R x q := by
    by_cases hx : certificateCheck arithmeticSignature E x.1 x.2 = true
    · obtain ⟨q, hq⟩ := introspection_certificate_exists E hE hQ x.1 x.2 hx
      exact ⟨q, Or.inr hq⟩
    · exact ⟨0, Or.inl hx⟩
  refine ⟨fun x => Nat.find (hex x), Computable.find hr.computablePred hex, ?_⟩
  intro p n hp
  exact (Nat.find_spec (hex (p, n))).resolve_left (not_not.mpr hp)

end
end Lemmatheca.MathematicalLogic.FormalizedProvability
