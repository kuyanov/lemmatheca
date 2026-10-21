import Lemmatheca.EffectiveTheories.CertifiedProofSearch

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! An explicit primitive-recursive transformation of the existing certified
proof records. Both axiom-certificate lists are retained, in their original order. -/
namespace Lemmatheca.ProofTheory.CodingFormalProofs
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

/-- Combine certificates of an implication and its antecedent. -/
def modusPonensCertificate (p q b : ℕ) : ℕ :=
  Seq.code [modusPonensRecord (Seq.entry p 0) (Seq.entry q 0) b,
    Seq.append (Seq.entry p 1) (Seq.entry q 1)]

theorem modusPonensCertificate_primitive :
    Primrec (fun x : ℕ × ℕ × ℕ => modusPonensCertificate x.1 x.2.1 x.2.2) := by
  unfold modusPonensCertificate modusPonensRecord proofContext Seq.entry Seq.append Seq.code
  fun_prop

theorem modusPonensCertificate_accepted (E : ℕ → ℕ → Bool) (p q a b : ℕ)
    (hp : certificateCheck S E p (impCode a b) = true)
    (hq : certificateCheck S E q a = true) (hb : isSentence S b = true) :
    certificateCheck S E (modusPonensCertificate p q b) b = true := by
  simp only [certificateCheck, Bool.and_eq_true, decide_eq_true_eq] at hp hq
  rcases hp with ⟨⟨⟨⟨⟨_, hpd⟩, hpc⟩, _⟩, hpl⟩, hpw⟩
  rcases hq with ⟨⟨⟨⟨⟨_, hqd⟩, hqc⟩, _⟩, hql⟩, hqw⟩
  have hd : derivationCheck S
      (modusPonensRecord (Seq.entry p 0) (Seq.entry q 0) b) = true := by
    apply modusPonens_accepted S _ _ _ hpd hqd
    simpa only [Seq.entry, hqc] using hpc
  have hl : (Seq.decode (Seq.append
      (proofContext (Seq.entry p 0)) (proofContext (Seq.entry q 0)))).length =
      (Seq.decode (Seq.append (Seq.entry p 1) (Seq.entry q 1))).length := by
    simpa only [Seq.append, Seq.decode, FiniteSequenceCoding.decode_code,
      List.length_append, Seq.entry] using congrArg₂ (· + ·) hpl hql
  have hw : ((Seq.decode (Seq.append
      (proofContext (Seq.entry p 0)) (proofContext (Seq.entry q 0)))).zip
      (Seq.decode (Seq.append (Seq.entry p 1) (Seq.entry q 1)))).all
      (fun aw => isSentence S aw.1 && E aw.1 aw.2) = true := by
    simpa only [Seq.append, Seq.decode, FiniteSequenceCoding.decode_code,
      List.zip_append hpl, List.all_append, Bool.and_eq_true, Seq.entry] using
      (show _ ∧ _ from ⟨hpw, hqw⟩)
  simpa only [certificateCheck, modusPonensCertificate, Seq.decode, Seq.code,
    FiniteSequenceCoding.decode_code, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.length_cons, List.length_nil, modusPonensRecord,
    proofContext_node, proofConclusion_node, Bool.and_eq_true, decide_eq_true_eq] using
    (show (((((2 = 2 ∧ _ = true) ∧ b = b) ∧ _ = true) ∧ _) ∧ _) from
      ⟨⟨⟨⟨⟨rfl, hd⟩, rfl⟩, hb⟩, hl⟩, hw⟩)

end Lemmatheca.ProofTheory.CodingFormalProofs
