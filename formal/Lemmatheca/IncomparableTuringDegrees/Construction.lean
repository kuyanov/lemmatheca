import Lemmatheca.IncomparableTuringDegrees.Prefixes
import Lemmatheca.TuringDegrees.Degrees

/-! A definite finite-extension construction meeting both diagonal requirements. -/
namespace Lemmatheca.ComputabilityTheory.IncomparableTuringDegrees

open OracleComputation OracleProgramNumberings UniversalComputation

noncomputable section

def parameters (e u v : ℕ) : ℕ := Nat.pair e (Nat.pair u v)

def Good (p w : ℕ) : Prop :=
  Prefix p.unpair.2.unpair.1 w ∧
    0 < certificateValue w p.unpair.1 (wordLength p.unpair.2.unpair.2)

def HasExtension (p : ℕ) : Prop := ∃ w, Good p w

def selected (p : ℕ) : ℕ := by
  classical
  exact if h : HasExtension p then Nat.find h else 0

def oppositeOutput (z : ℕ) : ℕ := if z = 1 then 1 else 0

def finish (a p w : ℕ) : ℕ :=
  let u := p.unpair.2.unpair.1
  let v := p.unpair.2.unpair.2
  if a = 0 then Nat.pair (appendBit u 0) (appendBit v 0)
  else Nat.pair (appendBit w 0)
    (appendBit v (oppositeOutput (certificateValue w p.unpair.1 (wordLength v))))

def extendState (p : ℕ) : ℕ :=
  finish (indicator HasExtension p) p (selected p)

def extend (e u v : ℕ) : ℕ × ℕ := (extendState (parameters e u v)).unpair

def Requirement (e : ℕ) (A B : Set ℕ) : Prop :=
  ¬ TuringDegrees.Reduces (decodeCode e) B A

def round (e s : ℕ) : ℕ :=
  let t := extend e s.unpair.1 s.unpair.2
  let r := extend e t.2 t.1
  Nat.pair r.2 r.1

def stage : ℕ → ℕ
  | 0 => Nat.pair 0 0
  | n + 1 => round n (stage n)

def leftWord (n : ℕ) : ℕ := (stage n).unpair.1
def rightWord (n : ℕ) : ℕ := (stage n).unpair.2
def leftSet : Set ℕ := unionSet leftWord
def rightSet : Set ℕ := unionSet rightWord

theorem parameters_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => parameters p.1.1 p.1.2 p.2) := by
  exact Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem good_primitive : PrimrecPred (fun z : ℕ × ℕ => Good z.1 z.2) := by
  have hp : Primrec (fun z : ℕ × ℕ => z.1) := Primrec.fst
  have hw : Primrec (fun z : ℕ × ℕ => z.2) := Primrec.snd
  have he := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hu := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hp)))
  have hv := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hp)))
  exact (prefix_primitive.comp (hu.pair hw)).and
    (Primrec.nat_lt.comp (Primrec.const 0)
      (certificate_primitive.comp ((hw.pair he).pair (FiniteSequenceCoding.primrec_length.comp hv))))

theorem selected_spec (p : ℕ) (h : HasExtension p) :
    Good p (selected p) ∧ ∀ w < selected p, ¬ Good p w := by
  classical
  simpa only [selected, dite_eq_left h] using
    (show Good p (Nat.find h) ∧ ∀ w < Nat.find h, ¬ Good p w from
      ⟨Nat.find_spec h, fun _ hw => Nat.find_min h hw⟩)

theorem oppositeOutput_spec (y : ℕ) :
    oppositeOutput (y + 1) = (if y = 0 then 1 else 0) ∧
      oppositeOutput (y + 1) ≠ y ∧ oppositeOutput (y + 1) < 2 := by
  by_cases h : y = 0
  · subst y
    simp [oppositeOutput]
  · simpa [oppositeOutput, h] using (Ne.symm h)

theorem finish_primitive :
    Primrec (fun z : (ℕ × ℕ) × ℕ => finish z.1.1 z.1.2 z.2) := by
  classical
  have ha : Primrec (fun z : (ℕ × ℕ) × ℕ => z.1.1) := Primrec.fst.comp Primrec.fst
  have hp : Primrec (fun z : (ℕ × ℕ) × ℕ => z.1.2) := Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun z : (ℕ × ℕ) × ℕ => z.2) := Primrec.snd
  have he := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hu := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hp)))
  have hv := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hp)))
  have hcv := certificate_primitive.comp ((hw.pair he).pair (FiniteSequenceCoding.primrec_length.comp hv))
  have hb := Primrec.ite (Primrec.eq.comp hcv (Primrec.const 1)) (Primrec.const 1) (Primrec.const 0)
  exact Primrec.ite (Primrec.eq.comp ha (Primrec.const 0))
    (Primrec₂.natPair.comp (appendBit_primitive.comp hu (Primrec.const 0))
      (appendBit_primitive.comp hv (Primrec.const 0)))
    (Primrec₂.natPair.comp (appendBit_primitive.comp hw (Primrec.const 0))
      (appendBit_primitive.comp hv hb))

theorem extend_success (e u v : ℕ) (h : HasExtension (parameters e u v)) :
    extend e u v =
      (appendBit (selected (parameters e u v)) 0,
        appendBit v (oppositeOutput
          (certificateValue (selected (parameters e u v)) e (wordLength v)))) := by
  classical
  unfold extend extendState
  have hc : indicator HasExtension (parameters e u v) = 1 := by simp [indicator, h]
  rw [hc]
  simp [finish, parameters]

theorem extend_failure (e u v : ℕ) (h : ¬ HasExtension (parameters e u v)) :
    extend e u v = (appendBit u 0, appendBit v 0) := by
  classical
  unfold extend extendState
  have hc : indicator HasExtension (parameters e u v) = 0 := by simp [indicator, h]
  rw [hc]
  simp [finish, parameters]

theorem extend_growth (e u v : ℕ) :
    Prefix u (extend e u v).1 ∧ Prefix v (extend e u v).2 ∧
      wordLength u < wordLength (extend e u v).1 ∧
      wordLength v < wordLength (extend e u v).2 := by
  classical
  by_cases h : HasExtension (parameters e u v)
  · rw [extend_success e u v h]
    dsimp only [Prod.fst, Prod.snd]
    have hs := (selected_spec _ h).1
    have hp : Prefix u (selected (parameters e u v)) := by
      simpa only [Good, parameters, Nat.unpair_pair] using hs.1
    have hl := appendBit_spec (selected (parameters e u v)) 0
    have hr := appendBit_spec v (oppositeOutput
      (certificateValue (selected (parameters e u v)) e (wordLength v)))
    exact ⟨prefix_trans hp hl.2.1, hr.2.1, by have := hp.1; omega, by omega⟩
  · rw [extend_failure e u v h]
    dsimp only [Prod.fst, Prod.snd]
    have hl := appendBit_spec u 0
    have hr := appendBit_spec v 0
    exact ⟨hl.2.1, hr.2.1, by omega, by omega⟩

theorem requirement_iff (e : ℕ) (A B : Set ℕ) :
    Requirement e A B ↔
      ∃ x, phi A e x ≠ Part.some (indicator (fun q => q ∈ B) x) := by
  classical
  simp only [Requirement, TuringDegrees.Reduces, OracleProgramNumberings.phi, not_forall]

theorem extend_correct (e u v : ℕ) (A B : Set ℕ)
    (hA : Realizes (extend e u v).1 A) (hB : Realizes (extend e u v).2 B) :
    Requirement e A B := by
  classical
  apply (requirement_iff e A B).mpr
  let m := wordLength v
  refine ⟨m, ?_⟩
  intro heq
  by_cases h : HasExtension (parameters e u v)
  · rw [extend_success e u v h] at hA hB
    dsimp only [Prod.fst, Prod.snd] at hA hB
    let w := selected (parameters e u v)
    have hg : 0 < certificateValue w e m := by
      simpa only [Good, parameters, Nat.unpair_pair, w, m] using (selected_spec _ h).1.2
    let y := certificateValue w e m - 1
    have hy : certificateValue w e m = y + 1 := by omega
    have hwA : Realizes w A := realizes_prefix (appendBit_spec w 0).2.1 hA
    have hmem := certificate_sound A w e m y hwA hy
    have hmy : y = indicator (fun q => q ∈ B) m :=
      Part.mem_unique hmem (by rw [heq]; exact Part.mem_some _)
    let b := oppositeOutput (certificateValue w e m)
    have hb : b < 2 := by simpa only [b, hy] using (oppositeOutput_spec y).2.2
    have hbm : wordBit (appendBit v b) m = b := by
      simpa only [m, Nat.mod_eq_of_lt hb] using (appendBit_spec v b).2.2
    have hchar : indicator (fun q => q ∈ B) m = b :=
      (hB m (by rw [(appendBit_spec v b).1]; dsimp [m]; omega)).symm.trans hbm
    have hne : b ≠ y := by simpa only [b, hy] using (oppositeOutput_spec y).2.1
    exact hne (hchar.symm.trans hmy.symm)
  · rw [extend_failure e u v h] at hA hB
    dsimp only [Prod.fst, Prod.snd] at hA hB
    have huA := realizes_prefix (appendBit_spec u 0).2.1 hA
    have hmem : indicator (fun q => q ∈ B) m ∈ phi A e m := by
      rw [heq]
      exact Part.mem_some _
    obtain ⟨w, hw, _, hval⟩ := prefix_adequacy A u e m _ huA hmem
    apply h
    refine ⟨w, ?_⟩
    simpa only [Good, parameters, Nat.unpair_pair, m] using
      (show Prefix u w ∧ 0 < certificateValue w e m from ⟨hw, by rw [hval]; omega⟩)

theorem requirements_exclude_reduction (A B : Set ℕ)
    (h : ∀ e, Requirement e A B) : ¬ TuringDegrees.Reducible B A := by
  rintro ⟨c, hc⟩
  apply h (encodeCode c)
  simpa only [TuringDegrees.Reduces, decode_encode] using hc

theorem round_growth (e s : ℕ) :
    Prefix s.unpair.1 (round e s).unpair.1 ∧
      Prefix s.unpair.2 (round e s).unpair.2 ∧
      wordLength s.unpair.1 + 2 ≤ wordLength (round e s).unpair.1 ∧
      wordLength s.unpair.2 + 2 ≤ wordLength (round e s).unpair.2 := by
  let t := extend e s.unpair.1 s.unpair.2
  let r := extend e t.2 t.1
  have ht := extend_growth e s.unpair.1 s.unpair.2
  have hr := extend_growth e t.2 t.1
  have hround : (round e s).unpair = (r.2, r.1) := by
    change (Nat.pair r.2 r.1).unpair = _
    exact Nat.unpair_pair _ _
  rw [hround]
  change Prefix s.unpair.1 r.2 ∧ Prefix s.unpair.2 r.1 ∧
    wordLength s.unpair.1 + 2 ≤ wordLength r.2 ∧
    wordLength s.unpair.2 + 2 ≤ wordLength r.1
  refine ⟨prefix_trans ht.1 hr.2.1, prefix_trans ht.2.1 hr.1, ?_, ?_⟩
  · have h1 := ht.2.2.1
    have h2 := hr.2.2.2
    dsimp [t, r] at h1 h2 ⊢
    omega
  · have h1 := ht.2.2.2
    have h2 := hr.2.2.1
    dsimp [t, r] at h1 h2 ⊢
    omega

theorem round_requirements (e s : ℕ) (A B : Set ℕ)
    (hA : Realizes (round e s).unpair.1 A)
    (hB : Realizes (round e s).unpair.2 B) :
    Requirement e A B ∧ Requirement e B A := by
  let t := extend e s.unpair.1 s.unpair.2
  let r := extend e t.2 t.1
  have hround : (round e s).unpair = (r.2, r.1) := by
    change (Nat.pair r.2 r.1).unpair = _
    exact Nat.unpair_pair _ _
  rw [hround] at hA hB
  change Realizes r.2 A at hA
  change Realizes r.1 B at hB
  have hg := extend_growth e t.2 t.1
  have hfirst := extend_correct e s.unpair.1 s.unpair.2 A B
    (realizes_prefix hg.2.1 hA) (realizes_prefix hg.1 hB)
  exact ⟨hfirst, extend_correct e t.2 t.1 B A hB hA⟩

theorem stage_prefixes (n : ℕ) :
    Prefix (leftWord n) (leftWord (n + 1)) ∧
      Prefix (rightWord n) (rightWord (n + 1)) := by
  exact ⟨(round_growth n (stage n)).1, (round_growth n (stage n)).2.1⟩

theorem stage_lengths (n : ℕ) :
    n ≤ wordLength (leftWord n) ∧ n ≤ wordLength (rightWord n) := by
  induction n with
  | zero => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | succ n ih =>
      have hg := round_growth n (stage n)
      have hl := hg.2.2.1
      have hr := hg.2.2.2
      change n ≤ wordLength (stage n).unpair.1 ∧ n ≤ wordLength (stage n).unpair.2 at ih
      change n + 1 ≤ wordLength (round n (stage n)).unpair.1 ∧
        n + 1 ≤ wordLength (round n (stage n)).unpair.2
      constructor <;> omega

theorem stage_realizes (n : ℕ) : Realizes (leftWord n) leftSet ∧
    Realizes (rightWord n) rightSet := by
  exact ⟨(coherent_union leftWord (fun n => (stage_prefixes n).1)
    (fun n => (stage_lengths n).1)).1 n,
    (coherent_union rightWord (fun n => (stage_prefixes n).2)
      (fun n => (stage_lengths n).2)).1 n⟩

theorem constructed_requirements (e : ℕ) :
    Requirement e leftSet rightSet ∧ Requirement e rightSet leftSet := by
  exact round_requirements e (stage e) leftSet rightSet
    (stage_realizes (e + 1)).1 (stage_realizes (e + 1)).2

theorem constructed_incomparable :
    ¬ TuringDegrees.Reducible leftSet rightSet ∧
      ¬ TuringDegrees.Reducible rightSet leftSet := by
  exact ⟨requirements_exclude_reduction rightSet leftSet (fun e => (constructed_requirements e).2),
    requirements_exclude_reduction leftSet rightSet (fun e => (constructed_requirements e).1)⟩

end
end Lemmatheca.ComputabilityTheory.IncomparableTuringDegrees
