import Lemmatheca.RogersIsomorphismTheorem.Probes
import Lemmatheca.PaddingAndInjectiveReductions.Padding
import Lemmatheca.MyhillsIsomorphismTheorem.Matching

/-! The specified translated padding family and both injective compiler maps. -/
namespace Lemmatheca.ComputabilityTheory.Rogers

open UniversalComputation UniformSelfReference

noncomputable section

def forwardCompiler {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (n : ℕ) : ℕ :=
  PaddingAndInjectiveReductions.pad (C.forward n) n

theorem forward_compiler_properties {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    Computable (forwardCompiler C) ∧ Function.Injective (forwardCompiler C) ∧
      ∀ n x, phi (forwardCompiler C n) x = ψ n x := by
  refine ⟨PaddingAndInjectiveReductions.pad_primitive.to_comp.comp
    C.forward_computable Computable.id, ?_, ?_⟩
  · intro n m h
    exact (PaddingAndInjectiveReductions.pad_injective h).2
  · intro n x
    exact (PaddingAndInjectiveReductions.pad_eval (C.forward n) n x).trans (C.forward_eval n x)

def history {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e : ℕ) : ℕ → List ℕ
  | 0 => [e]
  | k + 1 => history C e k ++ [nextEquivalent C e (FiniteSequenceCoding.code (history C e k))]

def translatedPad {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e k : ℕ) : ℕ :=
  (history C e k)[k]?.getD 0

theorem history_length {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e k : ℕ) :
    (history C e k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [history, ih]

private theorem history_prefix {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ)
    (e l k : ℕ) (hlk : l ≤ k) : (history C e l).IsPrefix (history C e k) := by
  induction k with
  | zero =>
    have : l = 0 := by omega
    subst l
    exact List.prefix_refl _
  | succ k ih =>
    by_cases hl : l ≤ k
    · exact (ih hl).trans (List.prefix_append _ _)
    · have : l = k + 1 := by omega
      subst l
      exact List.prefix_refl _

theorem history_invariants {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e k : ℕ) :
    (∀ i ∈ history C e k, ∀ x, phi i x = phi e x) ∧
      ((history C e k).map C.backward).Nodup ∧
      ∀ l ≤ k, (history C e l).IsPrefix (history C e k) := by
  have hinv (n : ℕ) :
      (∀ i ∈ history C e n, ∀ x, phi i x = phi e x) ∧
      ((history C e n).map C.backward).Nodup := by
    induction n with
    | zero => simp [history]
    | succ n ih =>
      have hne : FiniteSequenceCoding.decode (FiniteSequenceCoding.code (history C e n)) ≠ [] := by
        rw [FiniteSequenceCoding.decode_code]
        intro hz
        have hh := history_length C e n
        rw [hz] at hh
        simp at hh
      have hu := next_equivalent_spec C e (FiniteSequenceCoding.code (history C e n)) hne
        (by simpa only [FiniteSequenceCoding.decode_code] using ih.1)
      constructor
      · intro i hi x
        rcases List.mem_append.mp hi with hi | hi
        · exact ih.1 i hi x
        · have heq : i = nextEquivalent C e (FiniteSequenceCoding.code (history C e n)) := by
            simpa only [List.mem_singleton] using hi
          subst i
          exact hu.1 x
      · simp only [history, List.map_append, List.map_singleton, List.nodup_append]
        refine ⟨ih.2, by simp, ?_⟩
        intro a ha b hb
        have hb' : b = C.backward (nextEquivalent C e (FiniteSequenceCoding.code (history C e n))) := by
          simpa only [List.mem_singleton] using hb
        subst b
        intro heq
        apply hu.2
        simpa only [forbidden, FiniteSequenceCoding.decode_code, ← heq] using ha
  exact ⟨(hinv k).1, (hinv k).2, fun l h => history_prefix C e l k h⟩

theorem history_computable {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    Computable₂ (history C) := by
  have hs : Computable₂ (fun p : ℕ × ℕ => fun q : ℕ × List ℕ =>
      q.2 ++ [nextEquivalent C p.1 (FiniteSequenceCoding.code q.2)]) := by
    exact (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      ((next_equivalent_computable C).comp (Computable.fst.comp Computable.fst)
        (Primrec.encode.to_comp.comp (Computable.snd.comp Computable.snd)))).to₂
  exact (Computable.nat_rec Computable.snd
    ((Computable.list_cons.comp Computable.fst (Computable.const []))) hs).of_eq
      (fun p => by induction p.2 <;> simp_all [history])

theorem translated_padding {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    Computable₂ (translatedPad C) ∧
      (∀ e k x, phi (translatedPad C e k) x = phi e x) ∧
      ∀ e, Function.Injective (fun k => C.backward (translatedPad C e k)) := by
  have hc : Computable₂ (translatedPad C) :=
    (Primrec.option_getD.to_comp.comp
      (Computable.list_getElem?.comp (history_computable C) Computable.snd)
      (Computable.const 0))
  have hread (e k t : ℕ) (hkt : k ≤ t) :
      translatedPad C e k = (history C e t)[k]'(by rw [history_length]; omega) := by
    unfold translatedPad
    rw [List.getElem?_eq_getElem (by rw [history_length]; omega)]
    exact (history_prefix C e k t hkt).getElem (by rw [history_length]; omega)
  refine ⟨hc, ?_, ?_⟩
  · intro e k x
    rw [hread e k k (Nat.le_refl k)]
    exact (history_invariants C e k).1 _ (List.getElem_mem _) x
  · intro e k l hkl
    have hnd := (history_invariants C e (max k l)).2.1
    have hk : k < ((history C e (max k l)).map C.backward).length := by
      simp only [List.length_map, history_length]; omega
    have hl : l < ((history C e (max k l)).map C.backward).length := by
      simp only [List.length_map, history_length]; omega
    apply (hnd.getElem_inj_iff (hi := hk) (hj := hl)).mp
    simpa only [List.getElem_map, ← hread e k (max k l) (le_max_left _ _),
      ← hread e l (max k l) (le_max_right _ _)] using hkl

def escapePosition {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e lcode : ℕ) : ℕ :=
  PrimitiveRecursion.boundedSearch
    (fun p k => C.backward (translatedPad C p.1 k) ∉ FiniteSequenceCoding.decode p.2)
    (e, lcode) (FiniteSequenceCoding.length lcode + 1)

def escapingIndex {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e lcode : ℕ) : ℕ :=
  translatedPad C e (escapePosition C e lcode)

private theorem bounded_search_computable {α : Type*} [Primcodable α]
    (R : α → ℕ → Prop) [DecidableRel R] (hR : Computable (fun p : α × ℕ => decide (R p.1 p.2))) :
    Computable₂ (PrimitiveRecursion.boundedSearch R) := by
  have hstep : Computable₂ (fun x : α => fun p : ℕ × ℕ =>
      if p.2 < p.1 then p.2 else if R x p.1 then p.1 else p.1 + 1) := by
    have ht : Computable (fun t : α × (ℕ × ℕ) => decide (t.2.2 < t.2.1)) :=
      Primrec.nat_lt.decide.to_comp.comp (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.snd)
    have hu : Computable (fun t : α × (ℕ × ℕ) => decide (R t.1 t.2.1)) :=
      hR.comp (Computable.fst.pair (Computable.fst.comp Computable.snd))
    exact (Computable.cond ht (Computable.snd.comp Computable.snd)
      (Computable.cond hu (Computable.fst.comp Computable.snd)
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))).of_eq
        (fun t => by simp)
  exact (Computable.nat_rec Computable.snd (Computable.const 0)
    ((hstep.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂)).of_eq
    (fun p => by
      unfold PrimitiveRecursion.boundedSearch
      congr 1
      funext n u
      by_cases hlt : u < n
      · simp [hlt]
      · by_cases hr : R p.1 n <;> simp [hlt, hr])

private theorem list_membership_computable :
    Computable₂ (fun (l : List ℕ) j => decide (j ∈ l)) :=
  ((PrimrecRel.exists_mem_list Primrec.eq).decide.to_comp).of_eq (fun _ => by simp)

theorem translated_escape {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    Computable₂ (escapePosition C) ∧ Computable₂ (escapingIndex C) ∧
      ∀ e lcode,
        escapePosition C e lcode ≤ FiniteSequenceCoding.length lcode ∧
        C.backward (escapingIndex C e lcode) ∉ FiniteSequenceCoding.decode lcode ∧
        (∀ k < escapePosition C e lcode,
          C.backward (translatedPad C e k) ∈ FiniteSequenceCoding.decode lcode) ∧
        ∀ x, phi (escapingIndex C e lcode) x = phi e x := by
  have hpad := translated_padding C
  let R (p : ℕ × ℕ) (k : ℕ) :=
    C.backward (translatedPad C p.1 k) ∉ FiniteSequenceCoding.decode p.2
  have ht : Computable (fun t : (ℕ × ℕ) × ℕ => decide (R t.1 t.2)) := by
    have hm : Computable (fun t : (ℕ × ℕ) × ℕ =>
        decide (C.backward (translatedPad C t.1.1 t.2) ∈ FiniteSequenceCoding.decode t.1.2)) :=
      list_membership_computable.comp
        ((Primrec.ofNat (List ℕ)).to_comp.comp (Computable.snd.comp Computable.fst))
        (C.backward_computable.comp
          (hpad.1.comp (Computable.fst.comp Computable.fst) Computable.snd))
    exact (Primrec.not.to_comp.comp hm).of_eq (fun _ => by simp [R])
  have hpos : Computable₂ (escapePosition C) :=
    (bounded_search_computable R ht).comp Computable.id
      (Computable.succ.comp (FiniteSequenceCoding.primrec_length.to_comp.comp Computable.snd))
  have hq : Computable₂ (escapingIndex C) := hpad.1.comp Computable.fst hpos
  refine ⟨hpos, hq, ?_⟩
  intro e lcode
  let m := FiniteSequenceCoding.length lcode
  have hex : ∃ k < m + 1, R (e, lcode) k := by
    by_contra hn
    have hall : ∀ k < m + 1,
        C.backward (translatedPad C e k) ∈ FiniteSequenceCoding.decode lcode := by
      intro k hk
      exact Classical.not_not.mp (fun hh => hn ⟨k, hk, hh⟩)
    have hnd := (List.nodup_range (n := m + 1)).map (hpad.2.2 e)
    have hle := hnd.length_le_of_subset (l₂ := FiniteSequenceCoding.decode lcode) (by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      exact hall k (List.mem_range.mp hk))
    simp only [List.length_map, List.length_range] at hle
    change m + 1 ≤ m at hle
    omega
  obtain ⟨k, hk, hr⟩ := hex
  have hs := PrimitiveRecursion.boundedSearch_spec R (e, lcode) (m + 1)
  have hlt : escapePosition C e lcode < m + 1 := by
    have hne : PrimitiveRecursion.boundedSearch R (e, lcode) (m + 1) ≠ m + 1 := by
      intro heq
      exact hs.2.2.mp heq k hk hr
    change PrimitiveRecursion.boundedSearch R (e, lcode) (m + 1) < m + 1
    omega
  have hsuccess := hs.2.1 hlt
  refine ⟨by omega, hsuccess.1, ?_, hpad.2.1 e _⟩
  intro i hi
  exact Classical.not_not.mp (hsuccess.2 i hi)

def chosenHistory {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) : ℕ → List ℕ
  | 0 => []
  | e + 1 => chosenHistory C e ++
    [C.backward (escapingIndex C e (FiniteSequenceCoding.code (chosenHistory C e)))]

def reverseCompiler {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e : ℕ) : ℕ :=
  C.backward (escapingIndex C e (FiniteSequenceCoding.code (chosenHistory C e)))

theorem chosen_history_spec {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e : ℕ) :
    chosenHistory C e = (List.range e).map (reverseCompiler C) ∧
      (chosenHistory C e).length = e ∧
      (chosenHistory C (e + 1))[e]?.getD 0 = reverseCompiler C e := by
  have heq : chosenHistory C e = (List.range e).map (reverseCompiler C) := by
    induction e with
    | zero => rfl
    | succ e ih => simp only [chosenHistory, List.range_succ, List.map_append,
        List.map_singleton, ← ih]; rfl
  have hlen : (chosenHistory C e).length = e := by rw [heq]; simp
  refine ⟨heq, hlen, ?_⟩
  rw [chosenHistory, List.getElem?_append_right (by omega)]
  simp [hlen, reverseCompiler]

theorem reverse_compiler_properties {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    Computable (chosenHistory C) ∧ Computable (reverseCompiler C) ∧
      Function.Injective (reverseCompiler C) ∧
      ∀ e x, ψ (reverseCompiler C e) x = phi e x := by
  have hesc := translated_escape C
  have hstep : Computable₂ (fun n : ℕ => fun p : ℕ × List ℕ =>
      p.2 ++ [C.backward (escapingIndex C p.1 (FiniteSequenceCoding.code p.2))]) := by
    exact (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (C.backward_computable.comp (hesc.2.1.comp (Computable.fst.comp Computable.snd)
        (Primrec.encode.to_comp.comp (Computable.snd.comp Computable.snd))))).to₂
  have hJ : Computable (chosenHistory C) :=
    (Computable.nat_rec Computable.id (Computable.const []) hstep).of_eq
      (fun e => by induction e <;> simp_all [chosenHistory])
  have hG : Computable (reverseCompiler C) :=
    C.backward_computable.comp (hesc.2.1.comp Computable.id (Primrec.encode.to_comp.comp hJ))
  have hfresh (e : ℕ) : reverseCompiler C e ∉ chosenHistory C e := by
    simpa only [reverseCompiler, FiniteSequenceCoding.decode_code] using
      (hesc.2.2 e (FiniteSequenceCoding.code (chosenHistory C e))).2.1
  have hinj : Function.Injective (reverseCompiler C) := by
    intro i j hij
    by_contra hne
    have hless (i j : ℕ) (hlt : i < j) (heq : reverseCompiler C i = reverseCompiler C j) : False := by
      apply hfresh j
      rw [(chosen_history_spec C j).1]
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hlt, heq⟩
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · exact hless i j hijlt hij
    · exact hless j i hjilt hij.symm
  refine ⟨hJ, hG, hinj, ?_⟩
  intro e x
  exact (C.backward_eval _ x).trans
    ((hesc.2.2 e (FiniteSequenceCoding.code (chosenHistory C e))).2.2.2 x)

def permutation {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) : ℕ → ℕ :=
  Myhill.forward (reverseCompiler C) (forwardCompiler C)

def inversePermutation {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) : ℕ → ℕ :=
  Myhill.backward (reverseCompiler C) (forwardCompiler C)

/-- Both inverse laws and every partial value concern the displayed matching maps. -/
theorem rogers_isomorphism {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    Computable (permutation C) ∧ Computable (inversePermutation C) ∧
      Function.LeftInverse (inversePermutation C) (permutation C) ∧
      Function.RightInverse (inversePermutation C) (permutation C) ∧
      ∀ e x, ψ (permutation C e) x = phi e x := by
  have hF := forward_compiler_properties C
  have hG := reverse_compiler_properties C
  have hh := Myhill.labelled_bijection phi ψ (reverseCompiler C) (forwardCompiler C)
    hG.2.1 hF.1 hG.2.2.1 hF.2.1
    (fun e => funext (fun x => (hG.2.2.2 e x).symm))
    (fun n => funext (fun x => (hF.2.2 n x).symm))
  exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, fun e x =>
    (congrFun (hh.2.2.2.2 e) x).symm⟩

theorem acceptable_isomorphism {ψ : ℕ → ℕ → Part ℕ} (hψ : Acceptable ψ) :
    ∃ C : Compilers ψ,
      Computable (permutation C) ∧ Computable (inversePermutation C) ∧
      Function.LeftInverse (inversePermutation C) (permutation C) ∧
      Function.RightInverse (inversePermutation C) (permutation C) ∧
      ∀ e x, ψ (permutation C e) x = phi e x := by
  obtain ⟨C⟩ := hψ.2
  exact ⟨C, rogers_isomorphism C⟩

def recode {ψ θ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (D : Compilers θ) : ℕ → ℕ :=
  permutation D ∘ inversePermutation C

theorem two_numberings_isomorphic {ψ θ : ℕ → ℕ → Part ℕ}
    (C : Compilers ψ) (D : Compilers θ) :
    Computable (recode C D) ∧ Computable (recode D C) ∧
      Function.LeftInverse (recode D C) (recode C D) ∧
      Function.RightInverse (recode D C) (recode C D) ∧
      (∀ n x, θ (recode C D n) x = ψ n x) ∧
      ∀ n x, ψ (recode D C n) x = θ n x := by
  have hC := rogers_isomorphism C
  have hD := rogers_isomorphism D
  refine ⟨hD.1.comp hC.2.1, hC.1.comp hD.2.1, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp only [recode, Function.comp_apply]
    exact (congrArg (permutation C) (hD.2.2.1 (inversePermutation C n))).trans
      (hC.2.2.2.1 n)
  · intro n
    dsimp only [recode, Function.comp_apply]
    exact (congrArg (permutation D) (hC.2.2.1 (inversePermutation D n))).trans
      (hD.2.2.2.1 n)
  · intro n x
    dsimp only [recode, Function.comp_apply]
    exact (hD.2.2.2.2 (inversePermutation C n) x).trans
      ((hC.2.2.2.2 (inversePermutation C n) x).symm.trans
        (congrArg (fun j => ψ j x) (hC.2.2.2.1 n)))
  · intro n x
    dsimp only [recode, Function.comp_apply]
    exact (hC.2.2.2.2 (inversePermutation D n) x).trans
      ((hD.2.2.2.2 (inversePermutation D n) x).symm.trans
        (congrArg (fun j => θ j x) (hD.2.2.2.1 n)))

end
end Lemmatheca.ComputabilityTheory.Rogers
