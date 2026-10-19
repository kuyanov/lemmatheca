import Lemmatheca.MathematicalLogic.CodingFormalProofsCompileCore
import Lemmatheca.MathematicalLogic.CodingFormalProofsSoundness

namespace Lemmatheca.MathematicalLogic.CodingFormalProofs
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
noncomputable local instance : DecidableEq (L.Formula ℕ) := Classical.decEq _

theorem checked_sequent_iff (Γ : List (L.Formula ℕ)) (a : L.Formula ℕ) :
    (∃ d, Der S d (contextCode S Γ) (namedCode S a)) ↔ FirstOrderProofs.Proof L Γ.toFinset a := by
  constructor
  · rintro ⟨d, hd⟩
    exact checker_sound S d Γ a hd
  · exact proof_coded S Γ a


private theorem list_toFinset_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (xs : List α) : (xs.map f).toFinset = xs.toFinset.image f := by
  ext x
  simp

private theorem certified_context (E : ℕ → ℕ → Bool) (es ws : List ℕ)
    (hlen : es.length = ws.length)
    (hall : (es.zip ws).all (fun aw => isSentence S aw.1 && E aw.1 aw.2) = true) :
    ∃ Γ : List L.Sentence, Γ.map (sentenceCode S) = es ∧
      ∀ B ∈ Γ, B ∈ theory S E := by
  induction es generalizing ws with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons e es ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨A, hA⟩ := (sentence_recognition_iff S e).mp hall.1.1
      obtain ⟨Γ, hΓ, htheory⟩ := ih ws (Nat.succ.inj hlen) hall.2
      refine ⟨A :: Γ, by simp [hA, hΓ], ?_⟩
      intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · exact ⟨w, hA ▸ hall.1.2⟩
      · exact htheory B hB

private theorem context_witnesses (E : ℕ → ℕ → Bool) (Γ : List L.Sentence)
    (hΓ : ∀ B ∈ Γ, B ∈ theory S E) :
    ∃ ws : List ℕ, (Γ.map (sentenceCode S)).length = ws.length ∧
      ((Γ.map (sentenceCode S)).zip ws).all
        (fun aw => isSentence S aw.1 && E aw.1 aw.2) = true := by
  induction Γ with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons A Γ ih =>
    obtain ⟨w, hw⟩ := hΓ A (by simp)
    obtain ⟨ws, hlen, hall⟩ := ih (fun B hB => hΓ B (by simp [hB]))
    refine ⟨w :: ws, by simp [hlen], ?_⟩
    have hA : isSentence S (sentenceCode S A) = true :=
      (sentence_recognition_iff S _).mpr ⟨A, rfl⟩
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons,
      hA, hw, hall, Bool.and_self]

theorem certificate_iff_derives (E : ℕ → ℕ → Bool) (A : L.Sentence) :
    (∃ p, certificateCheck S E p (sentenceCode S A) = true) ↔ FirstOrderProofs.Derives (theory S E) A := by
  classical
  let f : Empty → ℕ := Empty.elim
  constructor
  · rintro ⟨p, hp⟩
    dsimp only [certificateCheck] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨Γ, hΓ, htheory⟩ := certified_context S E _ _ hp.1.2 hp.2
    let Δ := Γ.map (fun B => B.relabel f)
    have hctx : contextCode S Δ = proofContext ((Seq.decode p)[0]?.getD 0) := by
      rw [contextCode]
      simp only [Δ, List.map_map, Function.comp_def, f, sentence_as_named_code, hΓ]
      exact FiniteSequenceCoding.code_decode _
    have hp' : FirstOrderProofs.Proof L Δ.toFinset (A.relabel f) :=
      (checked_sequent_iff S Δ (A.relabel f)).mp
        ⟨_, hp.1.1.1.1.2, hctx.symm, by simpa only [f, sentence_as_named_code] using hp.1.1.1.2⟩
    refine ⟨Γ.toFinset, ?_, ?_⟩
    · intro B hB
      exact htheory B (List.mem_toFinset.mp hB)
    · apply FirstOrderProofs.Proof.parameterCloseMap f (by intro x; cases x)
      simpa only [Δ, list_toFinset_map] using hp'
  · rintro ⟨Γ, hΓ, hp⟩
    let Δ := Γ.toList.map (fun B => B.relabel f)
    have hproof : FirstOrderProofs.Proof L Δ.toFinset (A.relabel f) := by
      simpa only [Δ, list_toFinset_map, Finset.toList_toFinset] using
        FirstOrderProofs.Proof.rename f hp
    obtain ⟨d, hd, hctx, hcon⟩ := (checked_sequent_iff S Δ (A.relabel f)).mpr hproof
    obtain ⟨ws, hlen, hall⟩ := context_witnesses S E Γ.toList
      (fun B hB => hΓ (Finset.mem_toList.mp hB))
    have hctx' : Seq.decode (proofContext d) = Γ.toList.map (sentenceCode S) := by
      rw [hctx, contextCode]
      simp only [Δ, List.map_map, Function.comp_def, f, sentence_as_named_code,
        Seq.decode, Seq.code, Denumerable.ofNat_encode]
    have hA : isSentence S (sentenceCode S A) = true :=
      (sentence_recognition_iff S _).mpr ⟨A, rfl⟩
    refine ⟨Seq.code [d, Seq.code ws], ?_⟩
    simp only [certificateCheck, Seq.decode, Seq.code, Denumerable.ofNat_encode,
      List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ,
      List.length_cons, List.length_nil, hd, hcon, f, sentence_as_named_code,
      hctx', hlen, hA, hall, decide_true, Bool.and_self]

theorem modusPonens_accepted (d e b : ℕ) (hd : derivationCheck S d = true)
    (he : derivationCheck S e = true) (hab : proofConclusion d = impCode (proofConclusion e) b) :
    derivationCheck S (modusPonensRecord d e b) = true := by
  have hwd := derivation_well_formed S d hd
  have hwe := derivation_well_formed S e he
  have hb : namedForm S 0 b = true := by
    rw [hab] at hwd
    exact ((named_imp_iff S (proofConclusion e) b).mp hwd.1).2
  have hγ : (Seq.decode (Seq.append (proofContext d) (proofContext e))).all
      (namedForm S 0) = true := by
    simp only [Seq.append, Seq.decode, FiniteSequenceCoding.decode_code, List.all_append,
      hwd.2, hwe.2, Bool.and_true]
  have hp : d < modusPonensRecord d e b := child_lt (by simp)
  have hq : e < modusPonensRecord d e b := child_lt (by simp)
  have hpos : 0 < modusPonensRecord d e b := by unfold modusPonensRecord node; omega
  dsimp only [modusPonensRecord] at hp hq hpos
  rw [derivationCheck_eq_local]
  simp [localCheck, modusPonensRecord, node_tag, node_args, arg_node,
    proofHistory_entry, hp, hq, hd, he, hb, hγ, hpos, hab,
    contextIncluded_append_left, contextIncluded_append_right]


theorem implication_accepted (d γ a : ℕ) (hd : derivationCheck S d = true)
    (hγ : (Seq.decode γ).all (namedForm S 0) = true) (ha : namedForm S 0 a = true)
    (hsub : contextIncluded (proofContext d) (contextInsert a γ) = true) :
    derivationCheck S (implicationRecord d γ a) = true := by
  have hwd := derivation_well_formed S d hd
  have hcon : namedForm S 0 (impCode a (proofConclusion d)) = true :=
    (named_imp_iff S a (proofConclusion d)).mpr ⟨ha, hwd.1⟩
  have hp : d < implicationRecord d γ a := child_lt (by simp)
  have hpos : 0 < implicationRecord d γ a := by unfold implicationRecord node; omega
  dsimp only [implicationRecord] at hp hpos
  rw [derivationCheck_eq_local]
  simp [localCheck, implicationRecord, node_tag, node_args, arg_node,
    proofHistory_entry, hp, hd, hγ, ha, hcon, hsub, hpos]





end Lemmatheca.MathematicalLogic.CodingFormalProofs
