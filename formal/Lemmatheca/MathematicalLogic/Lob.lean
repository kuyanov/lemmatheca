import Lemmatheca.MathematicalLogic.DiagonalLemma

/-! Löb's argument for unary arithmetic formulas in the shared first-order
syntax. Every proof obligation uses the actual finite natural-deduction calculus. -/
namespace Lemmatheca.MathematicalLogic.Lob
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open FirstOrderProofs CodingFormalProofs DiagonalLemma
noncomputable section

/-- The box substitutes the actual sentence code into the fixed unary formula. -/
def box (P : language.Formula Unit) (A : language.Sentence) : language.Sentence :=
  numeralInstance P (fun _ => sentenceCode arithmeticSignature A)

/-- External necessitation and the two internally derived implications. -/
structure DerivabilityConditions (T : language.Theory) (P : language.Formula Unit) : Prop where
  one : ∀ A : language.Sentence, Derives T A → Derives T (box P A)
  two : ∀ A B : language.Sentence,
    Derives T ((box P (A.imp B)).imp ((box P A).imp (box P B)))
  three : ∀ A : language.Sentence,
    Derives T ((box P A).imp (box P (box P A)))

/-- The specified diagonal sentence for the target implication. -/
def lobSentence (P : language.Formula Unit) (A : language.Sentence) : language.Sentence :=
  fixedPoint (P.imp (A.relabel Empty.elim))

/-- A syntactic consistency formula, without an assumed standard meaning. -/
def consistency (P : language.Formula Unit) : language.Sentence := (box P ⊥).not

private theorem mp {T : language.Theory} {A B : language.Sentence}
    (h : Derives T (A.imp B)) (hA : Derives T A) : Derives T B := by
  have hh := derives_cut hA (derives_imp_iff.mp h)
  simpa only [Set.union_self] using hh

private theorem lift {T : language.Theory} {A B : language.Sentence}
    (h : Derives T B) : Derives (insert A T) B :=
  derives_mono h (Set.subset_insert _ _)

private theorem iffLeft {T : language.Theory} {A B : language.Sentence}
    (h : Derives T (A.iff B)) : Derives T (A.imp B) := by
  obtain ⟨Γ, hΓ, hp⟩ := h
  exact ⟨Γ, hΓ, Proof.conjElimLeft hp⟩

private theorem iffRight {T : language.Theory} {A B : language.Sentence}
    (h : Derives T (A.iff B)) : Derives T (B.imp A) := by
  obtain ⟨Γ, hΓ, hp⟩ := h
  exact ⟨Γ, hΓ, Proof.conjElimRight hp⟩

private theorem closed_instance (A : language.Sentence) (n : ℕ) :
    numeralInstance (A.relabel (Empty.elim : Empty → Unit)) (fun _ => n) = A := by
  unfold numeralInstance
  rw [formula_relabel_subst]
  change A.subst (fun _ : Empty => numeral n) = A
  have he : (fun _ : Empty => numeral n) =
      (Term.var : Empty → language.Term Empty) := by
    funext i
    exact i.elim
  rw [he, formula_subst_var]

theorem boxed_implication {T : language.Theory} {P : language.Formula Unit}
    (d : DerivabilityConditions T P) {A B : language.Sentence}
    (h : Derives T (A.imp B)) : Derives T ((box P A).imp (box P B)) := by
  exact mp (d.two A B) (d.one (A.imp B) h)

theorem lob_equivalence (P : language.Formula Unit) (A : language.Sentence)
    (T : language.Theory) (hQ : Q ⊆ T) :
    Derives T ((lobSentence P A).iff ((box P (lobSentence P A)).imp A)) := by
  have h := fixedPoint_in_extension (P.imp (A.relabel Empty.elim)) T hQ
  have he : numeralSubstitution (P.imp (A.relabel Empty.elim))
      (sentenceCode arithmeticSignature (lobSentence P A)) =
      (box P (lobSentence P A)).imp A := by
    unfold numeralSubstitution numeralInstance
    rw [formula_subst_imp]
    change (box P (lobSentence P A)).imp
      (numeralInstance (A.relabel Empty.elim) (fun _ =>
        sentenceCode arithmeticSignature (lobSentence P A))) = _
    rw [closed_instance]
  change Derives T ((lobSentence P A).iff
    (numeralSubstitution (P.imp (A.relabel Empty.elim))
      (sentenceCode arithmeticSignature (lobSentence P A)))) at h
  rw [he] at h
  exact h

theorem boxed_lob_sentence {T : language.Theory} {P : language.Formula Unit}
    (d : DerivabilityConditions T P) (hQ : Q ⊆ T) (A : language.Sentence) :
    Derives T ((box P (lobSentence P A)).imp (box P A)) := by
  let L := lobSentence P A
  have hfirst := boxed_implication d (iffLeft (lob_equivalence P A T hQ))
  apply derives_imp_iff.mpr
  have hu : Derives (insert (box P L) T) (box P L) :=
    derives_assumption (Set.mem_insert _ _)
  have hi := mp (lift hfirst) hu
  have hh := mp (lift (d.two (box P L) A)) hi
  exact mp hh (mp (lift (d.three L)) hu)

/-- Löb's hypothesis is an actual derivation of the reflection implication. -/
theorem lob {T : language.Theory} {P : language.Formula Unit}
    (d : DerivabilityConditions T P) (hQ : Q ⊆ T) (A : language.Sentence)
    (h : Derives T ((box P A).imp A)) : Derives T A := by
  let L := lobSentence P A
  have hstep : Derives T ((box P L).imp A) := by
    apply derives_imp_iff.mpr
    have hu : Derives (insert (box P L) T) (box P L) :=
      derives_assumption (Set.mem_insert _ _)
    exact mp (lift h) (mp (lift (boxed_lob_sentence d hQ A)) hu)
  have hL : Derives T L := mp (iffRight (lob_equivalence P A T hQ)) hstep
  exact mp hstep (d.one L hL)

theorem reflection_iff {T : language.Theory} {P : language.Formula Unit}
    (d : DerivabilityConditions T P) (hQ : Q ⊆ T) (A : language.Sentence) :
    Derives T ((box P A).imp A) ↔ Derives T A := by
  constructor
  · exact lob d hQ A
  · intro h
    exact derives_imp_iff.mpr (lift h)

theorem second_incompleteness {T : language.Theory} {P : language.Formula Unit}
    (d : DerivabilityConditions T P) (hQ : Q ⊆ T) (hT : Consistent T) :
    ¬ Derives T (consistency P) := by
  intro h
  exact hT (lob d hQ ⊥ h)

/-- The actual fixed point of the unnegated unary predicate is provable. -/
theorem henkin_sentence {T : language.Theory} {P : language.Formula Unit}
    (d : DerivabilityConditions T P) (hQ : Q ⊆ T) :
    Derives T (fixedPoint P) := by
  apply lob d hQ (fixedPoint P)
  exact iffRight (fixedPoint_in_extension P T hQ)

end
end Lemmatheca.MathematicalLogic.Lob
