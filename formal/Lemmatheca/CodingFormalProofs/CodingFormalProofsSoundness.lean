import Lemmatheca.CodingFormalProofs.CodingFormalProofsCompiler

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.CodingFormalProofs
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
noncomputable section
local instance : DecidableEq (L.Formula ℕ) := Classical.decEq _

private theorem absence_irrel {n : ℕ} (B : L.BoundedFormula ℕ n) (c : ℕ)
    (di dj : DecidableEq ℕ)
    (h : c ∉ @BoundedFormula.freeVarFinset L ℕ di n B) :
    c ∉ @BoundedFormula.freeVarFinset L ℕ dj n B := by
  have heq : di = dj := Subsingleton.elim _ _
  cases heq
  exact h

private theorem decode_named_context (es : List ℕ)
    (h : es.all (namedForm S 0) = true) :
    ∃ Γ : List (L.Formula ℕ), Γ.map (namedCode S) = es := by
  induction es with
  | nil => exact ⟨[], rfl⟩
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨A, hA⟩ := (named_recognition_iff S 0 e).mp h.1
    obtain ⟨Γ, hΓ⟩ := ih h.2
    exact ⟨A :: Γ, by simp [hA, hΓ]⟩

private theorem contextIncluded_sound (Γ Δ : List (L.Formula ℕ))
    (h : contextIncluded (contextCode S Γ) (contextCode S Δ) = true) :
    Γ.toFinset ⊆ Δ.toFinset := by
  simp only [contextIncluded, contextCode, Seq.decode, Seq.code, Denumerable.ofNat_encode,
    List.all_eq_true, decide_eq_true_eq] at h
  intro A hA
  obtain ⟨B, hB, heq⟩ := List.mem_map.mp (h _ (List.mem_map.mpr ⟨A, List.mem_toFinset.mp hA, rfl⟩))
  have : B = A := named_code_injective S heq
  subst B
  exact List.mem_toFinset.mpr hB

private theorem contextFresh_sound (c : ℕ) (Γ : List (L.Formula ℕ))
    (h : contextFresh c (contextCode S Γ) = true) :
    ∀ B ∈ Γ.toFinset, c ∉ B.freeVarFinset := by
  simp only [contextFresh, contextCode, Seq.decode, Seq.code, Denumerable.ofNat_encode,
    List.all_map, List.all_eq_true] at h
  intro B hB hc
  have hb := h B (List.mem_toFinset.mp hB)
  have ho := (occursAux_correct S B c).mpr hc
  simp only [Function.comp_apply, ho, Bool.not_true] at hb
  cases hb

set_option maxHeartbeats 400000 in
theorem checker_sound (d : ℕ) (Γ : List (L.Formula ℕ)) (A : L.Formula ℕ)
    (hd : Der S d (contextCode S Γ) (namedCode S A)) : FirstOrderProofs.Proof L Γ.toFinset A := by
  induction d using Nat.strong_induction_on generalizing Γ A with
  | h d ih =>
    obtain ⟨hcheck, hctx, hcon⟩ := hd
    have premise (p : ℕ) (Δ : List (L.Formula ℕ)) (C : L.Formula ℕ)
        (hp : 0 < Seq.entry (proofHistory S d) p)
        (hc : proofConclusion p = namedCode S C)
        (hs : contextIncluded (proofContext p) (contextCode S Δ) = true) :
        FirstOrderProofs.Proof L Δ.toFinset C := by
      obtain ⟨hlt, hpcheck⟩ := (proofHistory_positive S d p).mp hp
      obtain ⟨Ψ, hΨ⟩ := decode_named_context S _ (derivation_well_formed S p hpcheck).2
      have hΨcode : contextCode S Ψ = proofContext p := by
        rw [contextCode, hΨ]
        exact FiniteSequenceCoding.code_decode _
      apply FirstOrderProofs.Proof.weakening (ih p hlt Ψ C ⟨hpcheck, hΨcode.symm, hc⟩)
      exact contextIncluded_sound S Ψ Δ (hΨcode ▸ hs)
    have child_formula (p : ℕ) (hp : 0 < Seq.entry (proofHistory S d) p) :
        ∃ C : L.Formula ℕ, namedCode S C = proofConclusion p := by
      exact (named_recognition_iff S 0 _).mp
        (derivation_well_formed S p ((proofHistory_positive S d p).mp hp).2).1
    rw [derivationCheck_eq_local] at hcheck
    dsimp only [localCheck] at hcheck
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨⟨⟨_, _⟩, _⟩, hrule⟩ := hcheck
    rw [hctx, hcon] at hrule
    split at hrule
    all_goals try simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hrule
    case h_1 =>
      rcases hrule with ⟨_, hA⟩
      simp only [contextCode, Seq.decode, Seq.code, Denumerable.ofNat_encode, List.mem_map] at hA
      obtain ⟨B, hB, heq⟩ := hA
      have : B = A := named_code_injective S heq
      subst B
      exact FirstOrderProofs.Proof.assumption (List.mem_toFinset.mpr hB)
    case h_2 =>
      rcases hrule with ⟨_, hp, _, hps, hq, _, hqs, heq⟩
      obtain ⟨B, hB⟩ := child_formula _ hp
      obtain ⟨C, hC⟩ := child_formula _ hq
      rw [← hB, ← hC] at heq
      have : A = B ⊓ C := named_code_injective S heq
      subst A
      exact FirstOrderProofs.Proof.conjIntro (premise _ Γ B hp hB.symm hps)
        (premise _ Γ C hq hC.symm hqs)
    case h_3 =>
      rcases hrule with ⟨_, hB, hp, hc, hs⟩
      obtain ⟨B, hB⟩ := (named_recognition_iff S 0 _).mp hB
      rw [← hB] at hc
      exact FirstOrderProofs.Proof.conjElimLeft (premise _ Γ (A ⊓ B) hp hc hs)
    case h_4 =>
      rcases hrule with ⟨_, hB, hp, hc, hs⟩
      obtain ⟨B, hB⟩ := (named_recognition_iff S 0 _).mp hB
      rw [← hB] at hc
      exact FirstOrderProofs.Proof.conjElimRight (premise _ Γ (B ⊓ A) hp hc hs)
    case h_5 =>
      rcases hrule with ⟨_, hp, _, hs, hC, heq⟩
      obtain ⟨B, hB⟩ := child_formula _ hp
      obtain ⟨C, hC⟩ := (named_recognition_iff S 0 _).mp hC
      rw [← hB, ← hC] at heq
      have : A = B ⊔ C := named_code_injective S heq
      subst A
      exact FirstOrderProofs.Proof.disjIntroLeft (premise _ Γ B hp hB.symm hs)
    case h_6 =>
      rcases hrule with ⟨_, hp, _, hs, hB, heq⟩
      obtain ⟨C, hC⟩ := child_formula _ hp
      obtain ⟨B, hB⟩ := (named_recognition_iff S 0 _).mp hB
      rw [← hB, ← hC] at heq
      have : A = B ⊔ C := named_code_injective S heq
      subst A
      exact FirstOrderProofs.Proof.disjIntroRight (premise _ Γ C hp hC.symm (by simpa only [contextCode_cons] using hs))
    case h_7 =>
      rcases hrule with ⟨_, hB, hC, hp, hpc, hps, hq, hqc, hqs, hr, hrc, hrs⟩
      obtain ⟨B, hB⟩ := (named_recognition_iff S 0 _).mp hB
      obtain ⟨C, hC⟩ := (named_recognition_iff S 0 _).mp hC
      rw [← hB, ← hC] at hpc
      rw [← hB] at hqs
      rw [← hC] at hrs
      apply FirstOrderProofs.Proof.disjElim (premise _ Γ (B ⊔ C) hp hpc hps)
      · simpa only [List.toFinset_cons] using premise _ (B :: Γ) A hq hqc (by simpa only [contextCode_cons] using hqs)
      · simpa only [List.toFinset_cons] using premise _ (C :: Γ) A hr hrc (by simpa only [contextCode_cons] using hrs)
    case h_8 =>
      rcases hrule with ⟨_, hB, heq, hp, _, hs⟩
      obtain ⟨B, hB⟩ := (named_recognition_iff S 0 _).mp hB
      obtain ⟨C, hC⟩ := child_formula _ hp
      rw [← hB, ← hC] at heq
      have : A = B.imp C := named_code_injective S heq
      subst A
      rw [← hB] at hs
      apply FirstOrderProofs.Proof.impIntro
      simpa only [List.toFinset_cons] using premise _ (B :: Γ) C hp hC.symm (by simpa only [contextCode_cons] using hs)
    case h_9 =>
      rcases hrule with ⟨_, hp, hc, hs, hq, _, hqs⟩
      obtain ⟨B, hB⟩ := child_formula _ hq
      rw [← hB] at hc
      exact FirstOrderProofs.Proof.impElim (premise _ Γ (B.imp A) hp hc hs)
        (premise _ Γ B hq hB.symm hqs)
    case h_10 =>
      rcases hrule with ⟨_, hB, heq, hp, hc, hs⟩
      obtain ⟨B, hB⟩ := (named_recognition_iff S 0 _).mp hB
      rw [← hB] at heq hs
      have : A = B.not := named_code_injective S heq
      subst A
      apply FirstOrderProofs.Proof.negIntro
      simpa only [List.toFinset_cons] using premise _ (B :: Γ) ⊥ hp hc (by simpa only [contextCode_cons] using hs)
    case h_11 =>
      rcases hrule with ⟨_, heq, hp, _, hs, hq, hc, hqs⟩
      have : A = ⊥ := named_code_injective S heq
      subst A
      obtain ⟨B, hB⟩ := child_formula _ hp
      rw [← hB] at hc
      exact FirstOrderProofs.Proof.negElim (premise _ Γ B hp hB.symm hs)
        (premise _ Γ B.not hq hc hqs)
    case h_12 =>
      rcases hrule with ⟨_, hp, hc, hs⟩
      exact FirstOrderProofs.Proof.falsumElim (premise _ Γ ⊥ hp hc hs)
    case h_13 =>
      rcases hrule with ⟨_, hp, hc, hs⟩
      apply FirstOrderProofs.Proof.classicalContradiction
      simpa only [List.toFinset_cons] using premise _ (A.not :: Γ) ⊥ hp hc (by simpa only [contextCode_cons, namedCode_neg] using hs)
    case h_14 =>
      rcases hrule with ⟨_, hB, ht, heq, hp, hc, hs⟩
      obtain ⟨B, hB⟩ := (named_recognition_iff S 1 _).mp hB
      obtain ⟨t, ht⟩ := (named_term_recognition_iff S _).mp ht
      rw [← hB, ← ht, named_instantiate] at heq
      have : A = FirstOrderProofs.instantiate B t := named_code_injective S heq
      subst A
      rw [← hB] at hc
      exact FirstOrderProofs.Proof.allElim t (premise _ Γ B.all hp hc hs)
    case h_15 =>
      rcases hrule with ⟨_, hB, ht, heq, hp, hc, hs⟩
      obtain ⟨B, hB⟩ := (named_recognition_iff S 1 _).mp hB
      obtain ⟨t, ht⟩ := (named_term_recognition_iff S _).mp ht
      rw [← hB] at heq
      have : A = B.ex := named_code_injective S heq
      subst A
      rw [← hB, ← ht, named_instantiate] at hc
      exact FirstOrderProofs.Proof.exIntro t
        (premise _ Γ (FirstOrderProofs.instantiate B t) hp hc hs)
    case h_16 =>
      rcases hrule with ⟨_, hB, heq, hp, hc, hs, hf, hΓ⟩
      obtain ⟨B, hB⟩ := (named_recognition_iff S 1 _).mp hB
      rw [← hB] at heq hf hc
      have : A = B.all := named_code_injective S heq
      subst A
      have hnf : arg d 4 ∉ B.freeVarFinset := by
        intro hmem
        have ho := (occursAux_correct S B _).mpr hmem
        simp only [ho, Bool.not_true] at hf
        cases hf
      apply FirstOrderProofs.Proof.allIntroParameter (φ := B) (arg d 4)
      · exact absence_irrel B _ _ _ hnf
      · intro C hC
        exact absence_irrel C _ _ _ (contextFresh_sound S _ Γ hΓ C hC)
      · have hv : termCode S auxName (Term.var (arg d 4) : L.Term ℕ) = auxName (arg d 4) := rfl
        rw [← hv, named_instantiate] at hc
        exact premise _ Γ _ hp hc hs
    case h_17 =>
      rcases hrule with ⟨_, hB, hp, hpc, hps, hq, hqc, hqs, hfB, hfA, hΓ⟩
      obtain ⟨B, hB⟩ := (named_recognition_iff S 1 _).mp hB
      rw [← hB] at hpc hqs hfB
      have hnfB : arg d 5 ∉ B.freeVarFinset := by
        intro hmem
        have ho := (occursAux_correct S B _).mpr hmem
        simp only [ho, Bool.not_true] at hfB
        cases hfB
      have hnfA : arg d 5 ∉ A.freeVarFinset := by
        intro hmem
        have ho := (occursAux_correct S A _).mpr hmem
        simp only [ho, Bool.not_true] at hfA
        cases hfA
      apply FirstOrderProofs.Proof.exElimParameter (φ := B) (arg d 5)
      · exact absence_irrel B _ _ _ hnfB
      · intro C hC
        exact absence_irrel C _ _ _ (contextFresh_sound S _ Γ hΓ C hC)
      · exact absence_irrel A _ _ _ hnfA
      · exact premise _ Γ B.ex hp hpc hps
      · have hv : termCode S auxName (Term.var (arg d 5) : L.Term ℕ) = auxName (arg d 5) := rfl
        rw [← hv, named_instantiate] at hqs
        simpa only [List.toFinset_cons] using
          premise _ (FirstOrderProofs.instantiate B (.var (arg d 5)) :: Γ) A hq hqc (by simpa only [contextCode_cons] using hqs)
    case h_18 =>
      rcases hrule with ⟨_, ht, heq⟩
      obtain ⟨t, ht⟩ := (named_term_recognition_iff S _).mp ht
      rw [← ht] at heq
      have : A = t.equal t := named_code_injective S (by simpa only [namedCode_equal] using heq)
      subst A
      exact FirstOrderProofs.Proof.equalIntro t
    case h_19 =>
      rcases hrule with ⟨_, hB, hs, ht, heq, hp, hpc, hps, hq, hqc, hqs⟩
      obtain ⟨B, hB⟩ := (named_recognition_iff S 1 _).mp hB
      obtain ⟨s, hs⟩ := (named_term_recognition_iff S _).mp hs
      obtain ⟨t, ht⟩ := (named_term_recognition_iff S _).mp ht
      rw [← hB, ← ht, named_instantiate] at heq
      have : A = FirstOrderProofs.instantiate B t := named_code_injective S heq
      subst A
      rw [← hs, ← ht] at hpc
      rw [← hB, ← hs, named_instantiate] at hqc
      exact FirstOrderProofs.Proof.equalElim B s t
        (premise _ Γ (s.equal t) hp (by simpa only [namedCode_equal] using hpc) hps)
        (premise _ Γ (FirstOrderProofs.instantiate B s) hq hqc hqs)
    case h_20 => cases hrule

end
end Lemmatheca.ProofTheory.CodingFormalProofs
