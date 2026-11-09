import Lemmatheca.DominationAndHyperimmuneDegrees.Parity
import Lemmatheca.LimitComputability.LimitLemma

/-! First correct prefix times, rather than final settling moduli. -/
namespace Lemmatheca.ComputabilityTheory.HyperimmuneDegrees

open OracleComputation TuringDegrees UniversalComputation
open OracleProgramNumberings (identityCode QueryFree)
open BusyBeaverFunctions LimitComputability Classical

noncomputable section
set_option backward.isDefEq.respectTransparency false

def CorrectPrefix (a : Approximation) (A : Set ℕ) (n s : ℕ) : Prop :=
  n < s ∧ ∀ x ≤ n, a s x = indicator A x

theorem correct_prefix_exists (a : Approximation) (A : Set ℕ) (ha : Converges a A) (n : ℕ) :
    ∃ s, CorrectPrefix a A n s := by
  obtain ⟨t, ht⟩ := finite_prefix_stabilization a A ha (n + 1)
  refine ⟨max t (n + 1), ?_, ?_⟩
  · have := le_max_right t (n + 1); omega
  · intro x hx
    exact ht _ (le_max_left _ _) x (by omega)

def firstCorrectPrefix (a : Approximation) (A : Set ℕ) (ha : Converges a A) (n : ℕ) : ℕ :=
  Nat.find (correct_prefix_exists a A ha n)

theorem first_correct_prefix_spec (a : Approximation) (A : Set ℕ)
    (ha : Converges a A) (n : ℕ) :
    CorrectPrefix a A n (firstCorrectPrefix a A ha n) ∧
      ∀ s, s < firstCorrectPrefix a A ha n → ¬ CorrectPrefix a A n s := by
  exact ⟨Nat.find_spec (correct_prefix_exists a A ha n),
    fun s hs => Nat.find_min (correct_prefix_exists a A ha n) hs⟩

def differentBit (z : ℕ) : ℕ := if z.unpair.1 = z.unpair.2 then 0 else 1

def approximationInput (z : ℕ) : ℕ := Nat.pair z.unpair.1.unpair.2 z.unpair.2.unpair.1

theorem differentBit_computable : Computable differentBit := by
  exact (Primrec.ite
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
    (Primrec.const 0) (Primrec.const 1)).to_comp

theorem approximationInput_computable : Computable approximationInput := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact (Primrec₂.natPair.comp (hr.comp hl) (hl.comp hr)).to_comp

private def mismatchFold (lhs rhs : Code) : Code :=
  .prec .zero (.comp maxCode (.pair (.comp .right .right)
    (.comp (embed (ordinaryProgram differentBit differentBit_computable)) (.pair lhs rhs))))

private theorem mismatch_fold_eval (A : Set ℕ) (lhs rhs : Code) (l r : ℕ → ℕ → ℕ)
    (hl : ∀ p i v, eval A lhs (Nat.pair p (Nat.pair i v)) = Part.some (l p i))
    (hr : ∀ p i v, eval A rhs (Nat.pair p (Nat.pair i v)) = Part.some (r p i))
    (p m : ℕ) :
    eval A (mismatchFold lhs rhs) (Nat.pair p m) =
      Part.some (if ∀ i < m, l p i = r p i then 0 else 1) := by
  classical
  let step : Code := .comp maxCode (.pair (.comp .right .right)
    (.comp (embed (ordinaryProgram differentBit differentBit_computable)) (.pair lhs rhs)))
  have hs (i v : ℕ) : eval A step (Nat.pair p (Nat.pair i v)) =
      Part.some (max v (if l p i = r p i then 0 else 1)) := by
    simp [step, eval, maxCode, pairMax, eval_embed, ordinaryProgram_eval, hl, hr, differentBit]
  change eval A (.prec .zero step) (Nat.pair p m) = _
  induction m with
  | zero => rw [eval_prec_zero]; simp [eval]
  | succ m ih =>
    rw [eval_prec_succ, ih, Part.bind_some, hs]
    have he : (∀ i < m + 1, l p i = r p i) ↔
        (∀ i < m, l p i = r p i) ∧ l p m = r p m := by
      constructor
      · intro h
        exact ⟨fun i hi => h i (by omega), h m (by omega)⟩
      · rintro ⟨h, hm⟩ i hi
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
        · exact h i hi
        · exact hm
    apply congrArg Part.some
    split_ifs <;> aesop


/-- At input (n,s), fold the mismatch bits for coordinates zero through n. -/
def prefixAgreementProgram (aCode : Nat.Partrec.Code) : Code :=
  .comp (.prec .zero
    (.comp maxCode (.pair (.comp .right .right)
      (.comp (embed (ordinaryProgram differentBit differentBit_computable))
        (.pair
          (.comp (embed aCode) (embed (ordinaryProgram approximationInput approximationInput_computable)))
          (.comp .query (.comp .left .right)))))))
    (.pair identityCode (.comp .succ .left))

/-- This program family depends only on the supplied ordinary approximation code. -/
def correctPrefixProgram (aCode : Nat.Partrec.Code) : Code :=
  .comp (.find' (prefixAgreementProgram aCode)) (.pair identityCode .succ)

theorem prefix_agreement_eval (aCode : Nat.Partrec.Code) (a : Approximation)
    (hc : ∀ s x, Nat.Partrec.Code.eval aCode (Nat.pair s x) = Part.some (a s x))
    (A : Set ℕ) (n s : ℕ) :
    eval A (prefixAgreementProgram aCode) (Nat.pair n s) =
      Part.some (if ∀ x ≤ n, a s x = indicator A x then 0 else 1) := by
  let lhs : Code := .comp (embed aCode) (embed (ordinaryProgram approximationInput approximationInput_computable))
  let rhs : Code := .comp .query (.comp .left .right)
  have hl (p i v : ℕ) : eval A lhs (Nat.pair p (Nat.pair i v)) = Part.some (a p.unpair.2 i) := by
    simp [lhs, eval, eval_embed, ordinaryProgram_eval, approximationInput, hc]
  have hr (p i v : ℕ) : eval A rhs (Nat.pair p (Nat.pair i v)) = Part.some (indicator A i) := by
    simp [rhs, eval]
    rfl
  have hi : eval A (.pair identityCode (.comp .succ .left)) (Nat.pair n s) =
      Part.some (Nat.pair (Nat.pair n s) (n + 1)) := by
    simp [eval, OracleProgramNumberings.identity_eval]
  change (eval A (.pair identityCode (.comp .succ .left)) (Nat.pair n s)).bind
    (eval A (mismatchFold lhs rhs)) = _
  rw [hi, Part.bind_some]
  simpa only [Nat.unpair_pair, Nat.lt_succ_iff] using
    mismatch_fold_eval A lhs rhs (fun p i => a p.unpair.2 i) (fun _ i => indicator A i)
      hl hr (Nat.pair n s) (n + 1)

theorem correct_prefix_program_eval (aCode : Nat.Partrec.Code) (a : Approximation)
    (hc : ∀ s x, Nat.Partrec.Code.eval aCode (Nat.pair s x) = Part.some (a s x))
    (A : Set ℕ) (ha : Converges a A) (n : ℕ) :
    eval A (correctPrefixProgram aCode) n = Part.some (firstCorrectPrefix a A ha n) := by
  classical
  let r := firstCorrectPrefix a A ha n
  have hs := first_correct_prefix_spec a A ha n
  have hi : eval A (.pair identityCode .succ) n = Part.some (Nat.pair n (n + 1)) := by
    simp [eval, OracleProgramNumberings.identity_eval]
  change (eval A (.pair identityCode .succ) n).bind
    (eval A (.find' (prefixAgreementProgram aCode))) = _
  rw [hi, Part.bind_some]
  apply Part.eq_some_iff.mpr
  rw [eval_find]
  refine ⟨by have := hs.1.1; omega, ?_, ?_⟩
  · rw [prefix_agreement_eval aCode a hc A n r]
    have hx : ∀ x ≤ n, a r x = indicator A x := hs.1.2
    simp only [ite_eq_left hx, Part.mem_some_iff]
  · intro i hni hir
    have hn : ¬ ∀ x ≤ n, a i x = indicator A x := by
      intro hx
      exact hs.2 i hir ⟨by omega, hx⟩
    refine ⟨1, ?_, by decide⟩
    rw [prefix_agreement_eval aCode a hc A n i]
    simp [hn]

theorem first_correct_prefix_relative (a : Approximation) (ha : Computable₂ a)
    (A : Set ℕ) (hA : Converges a A) :
    PartialComputable A (fun n => Part.some (firstCorrectPrefix a A hA n)) := by
  have hl : Computable (fun z : ℕ => z.unpair.1) := (Primrec.fst.comp Primrec.unpair).to_comp
  have hr : Computable (fun z : ℕ => z.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
  let c := ordinaryProgram (fun z => a z.unpair.1 z.unpair.2) (ha.comp hl hr)
  have hc (s x : ℕ) : Nat.Partrec.Code.eval c (Nat.pair s x) = Part.some (a s x) := by
    simp [c, ordinaryProgram_eval]
  exact ⟨correctPrefixProgram c, funext (correct_prefix_program_eval c a hc A hA)⟩

def QuietInterval (a : Approximation) (h : ℕ → ℕ) (x n : ℕ) : Prop :=
  ∀ i < h n - n, a (n + 1 + i) x = a (n + 1) x

def quietStageInput (z : ℕ) : ℕ :=
  Nat.pair (z.unpair.1.unpair.2 + 1 + z.unpair.2.unpair.1) z.unpair.1.unpair.1

def quietCandidateInput (z : ℕ) : ℕ :=
  Nat.pair (z.unpair.1.unpair.2 + 1) z.unpair.1.unpair.1

def subtractionValue (z : ℕ) : ℕ := z.unpair.1 - z.unpair.2

def recoveryInput (z : ℕ) : ℕ := Nat.pair (z.unpair.2 + 1) z.unpair.1

theorem quietStageInput_computable : Computable quietStageInput := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact (Primrec₂.natPair.comp
    (Primrec.nat_add.comp (Primrec.succ.comp (hr.comp hl)) (hl.comp hr))
    (hl.comp hl)).to_comp

theorem quietCandidateInput_computable : Computable quietCandidateInput := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact (Primrec₂.natPair.comp (Primrec.succ.comp (hr.comp hl)) (hl.comp hl)).to_comp

theorem subtractionValue_computable : Computable subtractionValue := by
  exact (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).to_comp

theorem recoveryInput_computable : Computable recoveryInput := by
  exact (Primrec₂.natPair.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))
    (Primrec.fst.comp Primrec.unpair)).to_comp

/-- At (x,n), test the entire finite interval n<s≤h(n); zero means all answers agree. -/
def quietProgram (aCode hCode : Nat.Partrec.Code) : Code :=
  .comp
    (.prec .zero
      (.comp maxCode (.pair (.comp .right .right)
        (.comp (embed (ordinaryProgram differentBit differentBit_computable))
          (.pair
            (.comp (embed aCode) (embed (ordinaryProgram quietStageInput quietStageInput_computable)))
            (.comp (embed aCode) (embed (ordinaryProgram quietCandidateInput quietCandidateInput_computable))))))))
    (.pair identityCode
      (.comp (embed (ordinaryProgram subtractionValue subtractionValue_computable))
        (.pair (.comp (embed hCode) .right) .right)))

/-- Fix both numerical codes before any limiting oracle or convergence proof is supplied. -/
def recoveryCode (aCode hCode : Nat.Partrec.Code) : Nat.Partrec.Code :=
  erase .zero
    (.comp (embed aCode)
      (.comp (embed (ordinaryProgram recoveryInput recoveryInput_computable))
        (.pair identityCode
          (.comp (.find' (quietProgram aCode hCode)) (.pair identityCode identityCode)))))

theorem quiet_program_eval (aCode hCode : Nat.Partrec.Code) (a : Approximation) (h : ℕ → ℕ)
    (ha : ∀ s x, Nat.Partrec.Code.eval aCode (Nat.pair s x) = Part.some (a s x))
    (hh : ∀ n, Nat.Partrec.Code.eval hCode n = Part.some (h n)) (A : Set ℕ) (x n : ℕ) :
    eval A (quietProgram aCode hCode) (Nat.pair x n) =
      Part.some (if QuietInterval a h x n then 0 else 1) := by
  let lhs : Code := .comp (embed aCode) (embed (ordinaryProgram quietStageInput quietStageInput_computable))
  let rhs : Code := .comp (embed aCode) (embed (ordinaryProgram quietCandidateInput quietCandidateInput_computable))
  have hl (p i v : ℕ) : eval A lhs (Nat.pair p (Nat.pair i v)) =
      Part.some (a (p.unpair.2 + 1 + i) p.unpair.1) := by
    simp [lhs, eval, eval_embed, ordinaryProgram_eval, quietStageInput, ha]
  have hr (p i v : ℕ) : eval A rhs (Nat.pair p (Nat.pair i v)) =
      Part.some (a (p.unpair.2 + 1) p.unpair.1) := by
    simp [rhs, eval, eval_embed, ordinaryProgram_eval, quietCandidateInput, ha]
  let input : Code := .pair identityCode
    (.comp (embed (ordinaryProgram subtractionValue subtractionValue_computable))
      (.pair (.comp (embed hCode) .right) .right))
  have hi : eval A input (Nat.pair x n) = Part.some (Nat.pair (Nat.pair x n) (h n - n)) := by
    simp [input, eval, OracleProgramNumberings.identity_eval, eval_embed,
      ordinaryProgram_eval, subtractionValue, hh]
  change (eval A input (Nat.pair x n)).bind (eval A (mismatchFold lhs rhs)) = _
  rw [hi, Part.bind_some]
  have hf := mismatch_fold_eval A lhs rhs
    (fun p i => a (p.unpair.2 + 1 + i) p.unpair.1)
    (fun p _ => a (p.unpair.2 + 1) p.unpair.1) hl hr (Nat.pair x n) (h n - n)
  simp only [Nat.unpair_pair] at hf
  by_cases hq : QuietInterval a h x n
  · rw [ite_eq_left hq]
    dsimp only [QuietInterval] at hq
    simpa only [ite_eq_left hq] using hf
  · rw [ite_eq_right hq]
    dsimp only [QuietInterval] at hq
    simpa only [ite_eq_right hq] using hf

private theorem query_free_embed (c : Nat.Partrec.Code) : QueryFree (embed c) := by
  induction c <;> simp_all [embed, QueryFree]

theorem quiet_program_query_free (aCode hCode : Nat.Partrec.Code) :
    QueryFree (quietProgram aCode hCode) := by
  simp [quietProgram, maxCode, QueryFree, query_free_embed, identityCode]

theorem recovery_program_eval (aCode hCode : Nat.Partrec.Code) (a : Approximation) (h : ℕ → ℕ)
    (ha : ∀ s x, Nat.Partrec.Code.eval aCode (Nat.pair s x) = Part.some (a s x))
    (hh : ∀ n, Nat.Partrec.Code.eval hCode n = Part.some (h n))
    (A : Set ℕ) (hA : Converges a A) (hb : Majorizes h (firstCorrectPrefix a A hA)) (x : ℕ) :
    Nat.Partrec.Code.eval (recoveryCode aCode hCode) x = Part.some (indicator A x) := by
  classical
  have hex : ∃ n, x ≤ n ∧ QuietInterval a h x n := by
    obtain ⟨t, ht⟩ := hA x
    refine ⟨max x t, le_max_left _ _, ?_⟩
    intro i hi
    rw [ht _ (by have := le_max_right x t; omega),
      ht _ (by have := le_max_right x t; omega)]
  let n := Nat.find hex
  have hn : x ≤ n ∧ QuietInterval a h x n := Nat.find_spec hex
  have hfind : eval (∅ : Set ℕ) (.find' (quietProgram aCode hCode)) (Nat.pair x x) =
      Part.some n := by
    apply Part.eq_some_iff.mpr
    rw [eval_find]
    refine ⟨hn.1, ?_, ?_⟩
    · rw [quiet_program_eval aCode hCode a h ha hh ∅ x n]
      simp only [ite_eq_left hn.2, Part.mem_some_iff]
    · intro i hxi hin
      have hq : ¬ QuietInterval a h x i := fun hi => Nat.find_min hex hin ⟨hxi, hi⟩
      refine ⟨1, ?_, by decide⟩
      rw [quiet_program_eval aCode hCode a h ha hh ∅ x i]
      simp only [ite_eq_right hq, Part.mem_some_iff]
  have hr := (first_correct_prefix_spec a A hA n).1
  have hb' : firstCorrectPrefix a A hA n ≤ h n := hb n
  have hreturn : a (n + 1) x = indicator A x := by
    have hi : firstCorrectPrefix a A hA n - n - 1 < h n - n := by
      have := hr.1
      omega
    have ht : n + 1 + (firstCorrectPrefix a A hA n - n - 1) =
        firstCorrectPrefix a A hA n := by have := hr.1; omega
    have hq := hn.2 _ hi
    rw [ht] at hq
    exact hq.symm.trans (hr.2 x hn.1)
  let search : Code := .comp (.find' (quietProgram aCode hCode)) (.pair identityCode identityCode)
  have hs : eval (∅ : Set ℕ) search x = Part.some n := by
    have hi : eval (∅ : Set ℕ) (.pair identityCode identityCode) x = Part.some (Nat.pair x x) := by
      simp [eval, OracleProgramNumberings.identity_eval]
    change (eval (∅ : Set ℕ) (.pair identityCode identityCode) x).bind _ = _
    rw [hi, Part.bind_some, hfind]
  have hp : eval (∅ : Set ℕ) (.pair identityCode search) x = Part.some (Nat.pair x n) := by
    change (eval (∅ : Set ℕ) identityCode x).bind _ = _
    rw [OracleProgramNumberings.identity_eval, Part.bind_some, hs, Part.map_some]
  have hz (q : ℕ) : Nat.Partrec.Code.eval .zero q =
      Part.some (indicator (fun n => n ∈ (∅ : Set ℕ)) q) := by
    simp [Nat.Partrec.Code.eval, indicator]
    rfl
  unfold recoveryCode
  rw [erase_eval ∅ .zero hz]
  change (eval (∅ : Set ℕ) (.comp (embed (ordinaryProgram recoveryInput recoveryInput_computable))
    (.pair identityCode search)) x).bind (eval (∅ : Set ℕ) (embed aCode)) = _
  have hi : eval (∅ : Set ℕ) (.comp (embed (ordinaryProgram recoveryInput recoveryInput_computable))
      (.pair identityCode search)) x = Part.some (Nat.pair (n + 1) x) := by
    change (eval (∅ : Set ℕ) (.pair identityCode search) x).bind _ = _
    rw [hp, Part.bind_some, eval_embed, ordinaryProgram_eval]
    simp only [recoveryInput, Nat.unpair_pair]
  rw [hi, Part.bind_some, eval_embed, ha, hreturn]

theorem computable_of_prefix_bound (a : Approximation) (ha : Computable₂ a)
    (A : Set ℕ) (hA : Converges a A) (h : ℕ → ℕ) (hh : Computable h)
    (hb : Majorizes h (firstCorrectPrefix a A hA)) :
    ComputablePred (fun x => x ∈ A) := by
  have hl : Computable (fun z : ℕ => z.unpair.1) := (Primrec.fst.comp Primrec.unpair).to_comp
  have hr : Computable (fun z : ℕ => z.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
  let aCode := ordinaryProgram (fun z => a z.unpair.1 z.unpair.2) (ha.comp hl hr)
  let hCode := ordinaryProgram h hh
  have hca (s x : ℕ) : Nat.Partrec.Code.eval aCode (Nat.pair s x) = Part.some (a s x) := by
    simp [aCode, ordinaryProgram_eval]
  have hch (n : ℕ) : Nat.Partrec.Code.eval hCode n = Part.some (h n) :=
    ordinaryProgram_eval h hh n
  have hc : Computable (indicator A) := by
    change Partrec (fun x => Part.some (indicator A x))
    apply Partrec.nat_iff.mpr
    exact Nat.Partrec.Code.exists_code.mpr
      ⟨recoveryCode aCode hCode, funext (recovery_program_eval aCode hCode a h hca hch A hA hb)⟩
  exact (decidable_iff_characteristic (fun x => x ∈ A)).mpr ⟨indicator A, hc, fun _ => rfl⟩

theorem first_correct_prefix_hyperimmune (a : Approximation) (ha : Computable₂ a)
    (A : Set ℕ) (hA : Converges a A) (hnot : ¬ ComputablePred (fun x => x ∈ A)) :
    HyperimmuneFunction (firstCorrectPrefix a A hA) := by
  intro hb
  obtain ⟨h, hh, hbound⟩ := (computable_bounds_equivalent _).mp hb
  exact hnot (computable_of_prefix_bound a ha A hA h hh hbound)

theorem noncomputable_below_halting_hyperimmune (A : Set ℕ)
    (hAK : Reducible A haltingDiagonal) (hnot : ¬ ComputablePred (fun x => x ∈ A)) :
    HasHyperimmuneDegree A := by
  obtain ⟨a, hc, _, ha⟩ := (limit_lemma A).mpr hAK
  exact ⟨firstCorrectPrefix a A ha, first_correct_prefix_relative a hc A ha,
    first_correct_prefix_hyperimmune a hc A ha hnot⟩

theorem noncomputable_delta_two_hyperimmune (A : Set ℕ)
    (hA : ArithmeticalHierarchy.Delta ∅ 2 A) (hnot : ¬ ComputablePred (fun x => x ∈ A)) :
    HasHyperimmuneDegree A := by
  exact noncomputable_below_halting_hyperimmune A
    ((limit_lemma A).mp ((limit_delta_two A).mpr hA)) hnot

theorem noncomputable_ce_hyperimmune (A : Set ℕ) (hA : REPred (fun x => x ∈ A))
    (hnot : ¬ ComputablePred (fun x => x ∈ A)) : HasHyperimmuneDegree A := by
  exact noncomputable_below_halting_hyperimmune A
    ((limit_lemma A).mp (enumerable_limit A hA)) hnot

theorem hyperimmune_free_below_halting_computable (A : Set ℕ) (hA : HyperimmuneFree A)
    (hAK : Reducible A haltingDiagonal) : ComputablePred (fun x => x ∈ A) := by
  classical
  by_contra hn
  exact (hyperimmune_or_free A).mp (noncomputable_below_halting_hyperimmune A hAK hn) hA

theorem noncomputable_low_hyperimmune (A : Set ℕ)
    (hlow : Equivalent (TuringJump.jump A) haltingDiagonal)
    (hnot : ¬ ComputablePred (fun x => x ∈ A)) : HasHyperimmuneDegree A := by
  exact noncomputable_below_halting_hyperimmune A
    (reducible_trans (manyOne_imp_reducible (TuringJump.oracle_manyOne_jump A).1) hlow.1) hnot

end
end Lemmatheca.ComputabilityTheory.HyperimmuneDegrees
