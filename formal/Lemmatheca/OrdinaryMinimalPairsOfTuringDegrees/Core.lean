import Lemmatheca.IncomparableTuringDegrees.Prefixes
import Lemmatheca.TuringDegrees.Joins

/-! Ordinary minimal pairs through actual finite oracle certificates. -/
namespace Lemmatheca.ComputabilityTheory.OrdinaryMinimalPairs

open OracleComputation OracleProgramNumberings UniversalComputation IncomparableTuringDegrees

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section
local instance minimalPairsPropDecidable : DecidablePred (fun p : Prop => p) :=
  Classical.propDecidable

/-- Both degrees are nonzero and every common lower degree is zero. -/
def MinimalPair (a b : TuringDegrees.Degree) : Prop :=
  a ≠ TuringDegrees.zeroDegree ∧ b ≠ TuringDegrees.zeroDegree ∧
    ∀ c, c ≤ a → c ≤ b → c = TuringDegrees.zeroDegree

def SetMinimalPair (A B : Set ℕ) : Prop :=
  ¬ ComputablePred (fun x => x ∈ A) ∧ ¬ ComputablePred (fun x => x ∈ B) ∧
    ∀ C : Set ℕ, TuringDegrees.Reducible C A → TuringDegrees.Reducible C B →
      ComputablePred (fun x => x ∈ C)

def CommonRequirement (e f : ℕ) (A B : Set ℕ) : Prop :=
  ∀ g : ℕ → ℕ,
    (∀ x, phi A e x = Part.some (g x)) →
    (∀ x, phi B f x = Part.some (g x)) → Computable g

/-- The candidate code is exactly the paired triple (input,(left word,right word)). -/
def DisagreementCandidate (e f u v t : ℕ) : Prop :=
  let x := t.unpair.1
  let a := t.unpair.2.unpair.1
  let b := t.unpair.2.unpair.2
  Prefix u a ∧ Prefix v b ∧ 0 < certificateValue a e x ∧
    0 < certificateValue b f x ∧ certificateValue a e x ≠ certificateValue b f x

def HasDisagreement (e f u v : ℕ) : Prop := ∃ t, DisagreementCandidate e f u v t

def selected (e f u v : ℕ) : ℕ :=
  if h : HasDisagreement e f u v then Nat.find h else 0

/-- This is an ordinary numerical search; it does not query either final oracle. -/
def SearchCandidate (e u x w : ℕ) : Prop :=
  Prefix u w ∧ 0 < certificateValue w e x

def searchPartial (e u x : ℕ) : Part ℕ :=
  (Nat.rfind (fun w => Part.some (decide (SearchCandidate e u x w)))).map
    (fun w => certificateValue w e x - 1)

theorem search_candidate_primitive (e u : ℕ) :
    PrimrecPred (fun z : ℕ × ℕ => SearchCandidate e u z.1 z.2) := by
  have hp : PrimrecPred (fun z : ℕ × ℕ => Prefix u z.2) :=
    prefix_primitive.comp ((Primrec.const u).pair Primrec.snd)
  have hv : Primrec (fun z : ℕ × ℕ => certificateValue z.2 e z.1) :=
    IncomparableTuringDegrees.certificate_primitive.comp
      ((Primrec.snd.pair (Primrec.const e)).pair Primrec.fst)
  exact hp.and (Primrec.nat_lt.comp (Primrec.const 0) hv)

theorem search_recursive (e u : ℕ) : Nat.Partrec (searchPartial e u) := by
  have hc : Computable₂ (fun x w => decide (SearchCandidate e u x w)) :=
    (search_candidate_primitive e u).decide.to_comp
  have hr := Partrec.rfind hc.partrec₂
  have hv : Primrec (fun z : ℕ × ℕ => certificateValue z.2 e z.1) :=
    IncomparableTuringDegrees.certificate_primitive.comp
      ((Primrec.snd.pair (Primrec.const e)).pair Primrec.fst)
  have ho := (Primrec.nat_sub.comp hv (Primrec.const 1)).to_comp
  exact Partrec.nat_iff.mp (hr.map ho.to₂)

/-- One fixed ordinary program, chosen using only e and the old left word. -/
def searchCode (e u : ℕ) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (search_recursive e u))

def settle (e f u v : ℕ) : ℕ × ℕ :=
  if HasDisagreement e f u v then
    (appendBit (selected e f u v).unpair.2.unpair.1 0,
      appendBit (selected e f u v).unpair.2.unpair.2 0)
  else (appendBit u 0, appendBit v 0)

def diagonalBit (e u : ℕ) : ℕ :=
  if 0 ∈ phi ∅ e (wordLength u) then 1 else 0

def diagonalWord (e u : ℕ) : ℕ := appendBit u (diagonalBit e u)

def round (n : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  settle n.unpair.1 n.unpair.2 (diagonalWord n s.1) (diagonalWord n s.2)

def stage : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 => round n (stage n)

def leftWord (n : ℕ) : ℕ := (stage n).1

def rightWord (n : ℕ) : ℕ := (stage n).2

def leftSet : Set ℕ := unionSet leftWord

def rightSet : Set ℕ := unionSet rightWord

theorem minimal_pair_iff_sets (A B : Set ℕ) :
    MinimalPair (TuringDegrees.degree A) (TuringDegrees.degree B) ↔ SetMinimalPair A B := by
  constructor
  · rintro ⟨ha,hb,hc⟩
    refine ⟨fun h => ha ((TuringDegrees.degree_eq_zero_iff A).mpr h),
      fun h => hb ((TuringDegrees.degree_eq_zero_iff B).mpr h), ?_⟩
    intro C hCA hCB
    exact (TuringDegrees.degree_eq_zero_iff C).mp (hc (TuringDegrees.degree C) hCA hCB)
  · rintro ⟨ha,hb,hc⟩
    refine ⟨fun h => ha ((TuringDegrees.degree_eq_zero_iff A).mp h),
      fun h => hb ((TuringDegrees.degree_eq_zero_iff B).mp h), ?_⟩
    intro c hca hcb
    obtain ⟨C,rfl⟩ := TuringDegrees.degree_surjective c
    exact (TuringDegrees.degree_eq_zero_iff C).mpr (hc C hca hcb)

theorem candidate_primitive (e f u v : ℕ) :
    PrimrecPred (DisagreementCandidate e f u v) := by
  have hx : Primrec (fun t : ℕ => t.unpair.1) := Primrec.fst.comp Primrec.unpair
  have ha : Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hb : Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hca := IncomparableTuringDegrees.certificate_primitive.comp ((ha.pair (Primrec.const e)).pair hx)
  have hcb := IncomparableTuringDegrees.certificate_primitive.comp ((hb.pair (Primrec.const f)).pair hx)
  exact (prefix_primitive.comp ((Primrec.const u).pair ha)).and
    ((prefix_primitive.comp ((Primrec.const v).pair hb)).and
      ((Primrec.nat_lt.comp (Primrec.const 0) hca).and
        ((Primrec.nat_lt.comp (Primrec.const 0) hcb).and ((Primrec.eq.comp hca hcb).not))))

theorem selected_spec (e f u v : ℕ) (h : HasDisagreement e f u v) :
    DisagreementCandidate e f u v (selected e f u v) ∧
      ∀ t < selected e f u v, ¬ DisagreementCandidate e f u v t := by
  simpa only [selected, dite_eq_left h] using
    (show DisagreementCandidate e f u v (Nat.find h) ∧
      ∀ t < Nat.find h, ¬ DisagreementCandidate e f u v t from
        ⟨Nat.find_spec h, fun _ ht => Nat.find_min h ht⟩)

theorem split_excludes_common (e f u v t : ℕ) (A B : Set ℕ)
    (ht : DisagreementCandidate e f u v t)
    (hA : Realizes t.unpair.2.unpair.1 A) (hB : Realizes t.unpair.2.unpair.2 B) :
    ¬ ∃ g : ℕ → ℕ, (∀ x, phi A e x = Part.some (g x)) ∧
      (∀ x, phi B f x = Part.some (g x)) := by
  rintro ⟨g,he,hf⟩
  obtain ⟨_,_,ha,hb,hn⟩ := ht
  let x := t.unpair.1
  let a := t.unpair.2.unpair.1
  let b := t.unpair.2.unpair.2
  let y := certificateValue a e x - 1
  let z := certificateValue b f x - 1
  have hy : certificateValue a e x = y + 1 := by dsimp [y,a,x]; omega
  have hz : certificateValue b f x = z + 1 := by dsimp [z,b,x]; omega
  have hy' : y = g x := Part.mem_unique (certificate_sound A a e x y hA hy)
    (by rw [he]; exact Part.mem_some _)
  have hz' : z = g x := Part.mem_unique (certificate_sound B b f x z hB hz)
    (by rw [hf]; exact Part.mem_some _)
  exact hn (by change certificateValue a e x = certificateValue b f x; omega)

theorem search_code_eval (e u x : ℕ) :
    (searchCode e u).eval x = searchPartial e u x := by
  exact congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp (search_recursive e u))) x

theorem search_result_certificate (e u x y : ℕ)
    (hy : y ∈ searchPartial e u x) :
    ∃ w, Prefix u w ∧ certificateValue w e x = y + 1 ∧
      ∀ z < w, ¬ SearchCandidate e u x z := by
  obtain ⟨w,hw,heq⟩ := (Part.mem_map_iff _).mp hy
  have hgood : SearchCandidate e u x w := by
    simpa using Nat.rfind_spec hw
  refine ⟨w,hgood.1,?_,?_⟩
  · have := hgood.2
    omega
  · intro z hz
    simpa using Nat.rfind_min hw hz

theorem no_split_search (e f u v : ℕ) (A B : Set ℕ) (g : ℕ → ℕ)
    (hn : ¬ HasDisagreement e f u v) (hA : Realizes u A) (hB : Realizes v B)
    (he : ∀ x, phi A e x = Part.some (g x))
    (hf : ∀ x, phi B f x = Part.some (g x)) :
    ∀ x, (searchCode e u).eval x = Part.some (g x) := by
  intro x
  obtain ⟨w,hw,_,hc⟩ := prefix_adequacy A u e x (g x) hA
    (by rw [he]; exact Part.mem_some _)
  have hex : ∃ z, SearchCandidate e u x z := ⟨w,hw,by rw [hc]; omega⟩
  let z := Nat.find hex
  have hz : SearchCandidate e u x z := Nat.find_spec hex
  have hmin : ∀ k < z, ¬ SearchCandidate e u x k := fun k hk => Nat.find_min hex hk
  have hr : z ∈ Nat.rfind (fun w => Part.some (decide (SearchCandidate e u x w))) := by
    apply Nat.mem_rfind.mpr
    exact ⟨by simpa using hz,fun {k} hk => by simpa using hmin k hk⟩
  let y := certificateValue z e x - 1
  have hy : certificateValue z e x = y + 1 := by dsimp [y]; have := hz.2; omega
  obtain ⟨b,hb,_,hbval⟩ := prefix_adequacy B v f x (g x) hB
    (by rw [hf]; exact Part.mem_some _)
  have heq : y = g x := by
    by_contra hne
    apply hn
    refine ⟨Nat.pair x (Nat.pair z b), ?_⟩
    simp only [DisagreementCandidate, Nat.unpair_pair]
    exact ⟨hz.1,hb,by rw [hy]; omega,by rw [hbval]; omega,by omega⟩
  rw [search_code_eval]
  apply Part.eq_some_iff.mpr
  change g x ∈ (Nat.rfind (fun w => Part.some (decide (SearchCandidate e u x w)))).map _
  rw [← heq]
  exact Part.mem_map _ hr

theorem no_split_computable (e f u v : ℕ) (A B : Set ℕ) (g : ℕ → ℕ)
    (hn : ¬ HasDisagreement e f u v) (hA : Realizes u A) (hB : Realizes v B)
    (he : ∀ x, phi A e x = Part.some (g x))
    (hf : ∀ x, phi B f x = Part.some (g x)) : Computable g := by
  have hp := Partrec.nat_iff.mpr
    (Nat.Partrec.Code.exists_code.mpr ⟨searchCode e u,rfl⟩)
  exact hp.of_eq_tot (fun x => by
    rw [no_split_search e f u v A B g hn hA hB he hf x]
    exact Part.mem_some _)

theorem settle_growth (e f u v : ℕ) :
    Prefix u (settle e f u v).1 ∧ Prefix v (settle e f u v).2 ∧
      wordLength u < wordLength (settle e f u v).1 ∧
      wordLength v < wordLength (settle e f u v).2 := by
  by_cases h : HasDisagreement e f u v
  · rw [settle, ite_eq_left h]
    obtain ⟨hu,hv,_,_,_⟩ := (selected_spec e f u v h).1
    have ha := appendBit_spec (selected e f u v).unpair.2.unpair.1 0
    have hb := appendBit_spec (selected e f u v).unpair.2.unpair.2 0
    exact ⟨prefix_trans hu ha.2.1,prefix_trans hv hb.2.1,
      by dsimp; have := hu.1; omega,by dsimp; have := hv.1; omega⟩
  · rw [settle, ite_eq_right h]
    have ha := appendBit_spec u 0
    have hb := appendBit_spec v 0
    exact ⟨ha.2.1,hb.2.1,by dsimp; omega,by dsimp; omega⟩

theorem settle_correct (e f u v : ℕ) (A B : Set ℕ)
    (hA : Realizes (settle e f u v).1 A) (hB : Realizes (settle e f u v).2 B) :
    CommonRequirement e f A B := by
  intro g he hf
  by_cases h : HasDisagreement e f u v
  · rw [settle, ite_eq_left h] at hA hB
    exact False.elim (split_excludes_common e f u v (selected e f u v) A B
      (selected_spec e f u v h).1
      (realizes_prefix (appendBit_spec _ 0).2.1 hA)
      (realizes_prefix (appendBit_spec _ 0).2.1 hB) ⟨g,he,hf⟩)
  · rw [settle, ite_eq_right h] at hA hB
    exact no_split_computable e f u v A B g h
      (realizes_prefix (appendBit_spec u 0).2.1 hA)
      (realizes_prefix (appendBit_spec v 0).2.1 hB) he hf

theorem diagonal_growth (e u : ℕ) :
    Prefix u (diagonalWord e u) ∧ wordLength (diagonalWord e u) = wordLength u + 1 := by
  exact ⟨(appendBit_spec u (diagonalBit e u)).2.1,
    (appendBit_spec u (diagonalBit e u)).1⟩

theorem diagonal_correct (e u : ℕ) (A : Set ℕ) (hA : Realizes (diagonalWord e u) A) :
    phi ∅ e (wordLength u) ≠ Part.some (indicator (fun x => x ∈ A) (wordLength u)) := by
  have hb : diagonalBit e u < 2 := by unfold diagonalBit; split <;> omega
  have hbit : indicator (fun x => x ∈ A) (wordLength u) = diagonalBit e u := by
    have hlen := (diagonal_growth e u).2
    exact (hA (wordLength u) (by omega)).symm.trans
      (by simpa only [diagonalWord,Nat.mod_eq_of_lt hb] using
        (appendBit_spec u (diagonalBit e u)).2.2)
  intro heq
  by_cases h : 0 ∈ phi ∅ e (wordLength u)
  · have hb' : diagonalBit e u = 1 := by simp [diagonalBit,h]
    have hm : 1 ∈ phi ∅ e (wordLength u) := by
      rw [heq,hbit,hb']; exact Part.mem_some _
    have := Part.mem_unique h hm
    omega
  · have hb' : diagonalBit e u = 0 := by simp [diagonalBit,h]
    apply h
    rw [heq,hbit,hb']
    exact Part.mem_some _

theorem round_growth (n : ℕ) (s : ℕ × ℕ) :
    Prefix s.1 (round n s).1 ∧ Prefix s.2 (round n s).2 ∧
      wordLength s.1 + 2 ≤ wordLength (round n s).1 ∧
      wordLength s.2 + 2 ≤ wordLength (round n s).2 := by
  have hd1 := diagonal_growth n s.1
  have hd2 := diagonal_growth n s.2
  have hs := settle_growth n.unpair.1 n.unpair.2 (diagonalWord n s.1) (diagonalWord n s.2)
  refine ⟨prefix_trans hd1.1 hs.1,prefix_trans hd2.1 hs.2.1,?_,?_⟩
  · change wordLength s.1 + 2 ≤ wordLength
      (settle n.unpair.1 n.unpair.2 (diagonalWord n s.1) (diagonalWord n s.2)).1
    have := hs.2.2.1
    omega
  · change wordLength s.2 + 2 ≤ wordLength
      (settle n.unpair.1 n.unpair.2 (diagonalWord n s.1) (diagonalWord n s.2)).2
    have := hs.2.2.2
    omega

theorem stage_prefixes (n : ℕ) :
    Prefix (leftWord n) (leftWord (n + 1)) ∧
      Prefix (rightWord n) (rightWord (n + 1)) := by
  exact ⟨(round_growth n (stage n)).1,(round_growth n (stage n)).2.1⟩

theorem stage_lengths (n : ℕ) :
    n ≤ wordLength (leftWord n) ∧ n ≤ wordLength (rightWord n) := by
  induction n with
  | zero => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | succ n ih =>
    have hg := round_growth n (stage n)
    change n + 1 ≤ wordLength (round n (stage n)).1 ∧
      n + 1 ≤ wordLength (round n (stage n)).2
    change n ≤ wordLength (stage n).1 ∧ n ≤ wordLength (stage n).2 at ih
    exact ⟨by have := hg.2.2.1; omega,by have := hg.2.2.2; omega⟩

theorem stage_realizes (n : ℕ) : Realizes (leftWord n) leftSet ∧
    Realizes (rightWord n) rightSet := by
  exact ⟨(coherent_union leftWord (fun n => (stage_prefixes n).1)
    (fun n => (stage_lengths n).1)).1 n,
    (coherent_union rightWord (fun n => (stage_prefixes n).2)
      (fun n => (stage_lengths n).2)).1 n⟩

theorem constructed_requirements (e f : ℕ) : CommonRequirement e f leftSet rightSet := by
  let n := Nat.pair e f
  have hs := stage_realizes (n + 1)
  have hc := settle_correct e f (diagonalWord n (stage n).1)
    (diagonalWord n (stage n).2) leftSet rightSet
  apply hc
  · simpa only [leftWord,stage,round,n,Nat.unpair_pair] using hs.1
  · simpa only [rightWord,stage,round,n,Nat.unpair_pair] using hs.2

theorem constructed_noncomputable :
    ¬ ComputablePred (fun x => x ∈ leftSet) ∧
      ¬ ComputablePred (fun x => x ∈ rightSet) := by
  have hdiag (e : ℕ) :
      phi ∅ e (wordLength (leftWord e)) ≠
        Part.some (indicator (fun x => x ∈ leftSet) (wordLength (leftWord e))) ∧
      phi ∅ e (wordLength (rightWord e)) ≠
        Part.some (indicator (fun x => x ∈ rightSet) (wordLength (rightWord e))) := by
    have hr := stage_realizes (e + 1)
    have hg := settle_growth e.unpair.1 e.unpair.2
      (diagonalWord e (leftWord e)) (diagonalWord e (rightWord e))
    refine ⟨diagonal_correct e (leftWord e) leftSet ?_,
      diagonal_correct e (rightWord e) rightSet ?_⟩
    · exact realizes_prefix hg.1 hr.1
    · exact realizes_prefix hg.2.1 hr.2
  constructor
  · intro hA
    obtain ⟨c,hc⟩ := (TuringDegrees.reducible_empty_iff leftSet).mpr hA
    have he : ∀ x, phi ∅ (encodeCode c) x =
        Part.some (indicator (fun q => q ∈ leftSet) x) := by
      simpa only [TuringDegrees.Reduces,OracleProgramNumberings.phi,decode_encode] using hc
    exact (hdiag (encodeCode c)).1 (he _)
  · intro hB
    obtain ⟨c,hc⟩ := (TuringDegrees.reducible_empty_iff rightSet).mpr hB
    have he : ∀ x, phi ∅ (encodeCode c) x =
        Part.some (indicator (fun q => q ∈ rightSet) x) := by
      simpa only [TuringDegrees.Reduces,OracleProgramNumberings.phi,decode_encode] using hc
    exact (hdiag (encodeCode c)).2 (he _)

theorem constructed_common_lower (C : Set ℕ)
    (hA : TuringDegrees.Reducible C leftSet) (hB : TuringDegrees.Reducible C rightSet) :
    ComputablePred (fun x => x ∈ C) := by
  obtain ⟨c,hc⟩ := hA
  obtain ⟨d,hd⟩ := hB
  have hg : Computable (indicator (fun x => x ∈ C)) :=
    constructed_requirements (encodeCode c) (encodeCode d) _
      (by simpa only [TuringDegrees.Reduces,OracleProgramNumberings.phi,decode_encode] using hc)
      (by simpa only [TuringDegrees.Reduces,OracleProgramNumberings.phi,decode_encode] using hd)
  exact (decidable_iff_characteristic _).mpr ⟨_,hg,fun _ => rfl⟩

theorem constructed_minimal_pair : SetMinimalPair leftSet rightSet := by
  exact ⟨constructed_noncomputable.1,constructed_noncomputable.2,constructed_common_lower⟩

theorem constructed_degree_pair :
    MinimalPair (TuringDegrees.degree leftSet) (TuringDegrees.degree rightSet) := by
  exact (minimal_pair_iff_sets leftSet rightSet).mpr constructed_minimal_pair

theorem minimal_pair_consequences (a b : TuringDegrees.Degree) (h : MinimalPair a b) :
    TuringDegrees.zeroDegree < a ∧ TuringDegrees.zeroDegree < b ∧
      ¬ a ≤ b ∧ ¬ b ≤ a ∧ IsGLB ({a,b} : Set TuringDegrees.Degree) TuringDegrees.zeroDegree := by
  refine ⟨lt_of_le_of_ne (TuringDegrees.zeroDegree_le a) (Ne.symm h.1),
    lt_of_le_of_ne (TuringDegrees.zeroDegree_le b) (Ne.symm h.2.1),
    fun hab => h.1 (h.2.2 a le_rfl hab),fun hba => h.2.1 (h.2.2 b hba le_rfl),?_⟩
  refine ⟨fun _ _ => TuringDegrees.zeroDegree_le _,fun c hc => ?_⟩
  exact le_of_eq (h.2.2 c (hc (by simp)) (hc (by simp)))

theorem degree_consequences :
    TuringDegrees.zeroDegree < TuringDegrees.degree leftSet ∧
      TuringDegrees.zeroDegree < TuringDegrees.degree rightSet ∧
      ¬ TuringDegrees.degree leftSet ≤ TuringDegrees.degree rightSet ∧
      ¬ TuringDegrees.degree rightSet ≤ TuringDegrees.degree leftSet ∧
      IsGLB ({TuringDegrees.degree leftSet,TuringDegrees.degree rightSet} :
        Set TuringDegrees.Degree) TuringDegrees.zeroDegree := by
  exact minimal_pair_consequences _ _ constructed_degree_pair

end
end Lemmatheca.ComputabilityTheory.OrdinaryMinimalPairs
