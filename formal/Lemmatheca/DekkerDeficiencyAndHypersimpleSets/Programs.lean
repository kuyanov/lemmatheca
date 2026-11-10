import Lemmatheca.DekkerDeficiencyAndHypersimpleSets.Basic

namespace Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets

open UniversalComputation OracleComputation HyperimmuneDegrees
open BusyBeaverFunctions (ordinaryProgram equalityBit equalityBit_computable)

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false
local notation "OCode" => Nat.Partrec.Code


-- The established oracle minimization identity specializes exactly to ordinary code.
theorem ordinary_find_spec (c : OCode) (a m j : ℕ) :
    j ∈ (Nat.Partrec.Code.rfind' c).eval (Nat.pair a m) ↔
      m ≤ j ∧ 0 ∈ c.eval (Nat.pair a j) ∧
        ∀ i, m ≤ i → i < j → ∃ v, v ∈ c.eval (Nat.pair a i) ∧ 0 < v := by
  rw [← eval_embed (∅ : Set ℕ) (Nat.Partrec.Code.rfind' c) (Nat.pair a m)]
  change j ∈ eval (∅ : Set ℕ) (.find' (embed c)) (Nat.pair a m) ↔ _
  rw [eval_find]
  simp only [eval_embed]

def lowerFailure (w : ℕ) : ℕ := if w.unpair.1 < w.unpair.2 then 0 else 1

theorem lower_failure_primitive : Primrec lowerFailure := by
  exact Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)) (Primrec.const 0) (Primrec.const 1)

-- At input (s,t), return zero just when the later value is smaller.
def deficiencyTestCode (p : OCode) : OCode :=
  .comp (ordinaryProgram lowerFailure lower_failure_primitive.to_comp)
    (.pair (.comp p .right) (.comp p .left))

def deficiencyCode (p : OCode) : OCode :=
  .comp .zero (.comp (.rfind' (deficiencyTestCode p)) (.pair Nat.Partrec.Code.id (.comp .succ Nat.Partrec.Code.id)))

theorem deficiency_code_spec (a : ℕ → ℕ) (p : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n)) (s : ℕ) :
    ((deficiencyCode p).eval s).Dom ↔ s ∈ deficiency a := by
  have test (t : ℕ) : (deficiencyTestCode p).eval (Nat.pair s t) =
      Part.some (if a t < a s then 0 else 1) := by
    simp [deficiencyTestCode, Nat.Partrec.Code.eval, Seq.seq, Part.bind_eq_bind, BusyBeaverFunctions.ordinaryProgram_eval,
      hp, lowerFailure]
  have hi : (Nat.Partrec.Code.pair Nat.Partrec.Code.id
      (.comp .succ Nat.Partrec.Code.id)).eval s = Part.some (Nat.pair s (s+1)) := by
    simp [Nat.Partrec.Code.eval, Seq.seq, Part.bind_eq_bind, Nat.Partrec.Code.eval_id]
  change ((((Nat.Partrec.Code.pair Nat.Partrec.Code.id
    (.comp .succ Nat.Partrec.Code.id)).eval s).bind
      (Nat.Partrec.Code.eval (.rfind' (deficiencyTestCode p)))).bind
        (fun _ => Part.some 0)).Dom ↔ _
  rw [hi, Part.bind_some]
  simp only [Part.bind_dom, Part.some_dom]
  constructor
  · rintro ⟨hd, _⟩
    obtain ⟨t, ht⟩ := Part.dom_iff_mem.mp hd
    have ht' := (ordinary_find_spec (deficiencyTestCode p) s (s+1) t).mp ht
    have hlt : a t < a s := by
      rw [test] at ht'
      by_contra h
      simpa [h] using ht'.2.1
    exact ⟨t, by omega, hlt⟩
  · rintro ⟨t, hst, hlt⟩
    have hex : ∃ u, s+1 ≤ u ∧ a u < a s := ⟨t, by omega, hlt⟩
    let u := Nat.find hex
    have hu : s+1 ≤ u ∧ a u < a s := Nat.find_spec hex
    refine ⟨?_, trivial⟩
    apply Part.dom_iff_mem.mpr
    refine ⟨u, (ordinary_find_spec (deficiencyTestCode p) s (s+1) u).mpr ⟨hu.1, ?_, ?_⟩⟩
    · rw [test]; simp [hu.2]
    · intro i hsi hiu
      have hnot : ¬ a i < a s := fun h => Nat.find_min hex hiu ⟨hsi,h⟩
      refine ⟨1, ?_, by decide⟩
      rw [test]; simp [hnot]

theorem deficiency_code_output (a : ℕ → ℕ) (p : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n)) (s : ℕ) (hs : s ∈ deficiency a) :
    (deficiencyCode p).eval s = Part.some 0 := by
  have hi : (Nat.Partrec.Code.pair Nat.Partrec.Code.id
      (.comp .succ Nat.Partrec.Code.id)).eval s = Part.some (Nat.pair s (s+1)) := by
    simp [Nat.Partrec.Code.eval, Seq.seq, Part.bind_eq_bind, Nat.Partrec.Code.eval_id]
  have hd := (deficiency_code_spec a p hp s).mpr hs
  change ((((Nat.Partrec.Code.pair Nat.Partrec.Code.id
    (.comp .succ Nat.Partrec.Code.id)).eval s).bind
      (Nat.Partrec.Code.eval (.rfind' (deficiencyTestCode p)))).bind
        (fun _ => Part.some 0)).Dom at hd
  rw [hi, Part.bind_some] at hd
  have hr := Part.Dom.of_bind hd
  change (((Nat.Partrec.Code.pair Nat.Partrec.Code.id
    (.comp .succ Nat.Partrec.Code.id)).eval s).bind
      (Nat.Partrec.Code.eval (.rfind' (deficiencyTestCode p)))).bind
        (fun _ => Part.some 0) = _
  rw [hi, Part.bind_some]
  exact Part.Dom.bind hr (fun _ => Part.some 0)

-- Input (x,k); count equality bits at the positions strictly below k.
def prefixRangeCode (p : OCode) : OCode :=
  .prec .zero
    (.comp (ordinaryProgram pairMax pairMax_computable) (.pair (.comp .right .right)
      (.comp (ordinaryProgram equalityBit equalityBit_computable)
        (.pair (.comp p (.comp .left .right)) .left))))

def rangeCode (p : OCode) : OCode :=
  .comp (prefixRangeCode p) (.pair .left (.comp .succ .right))

theorem prefix_range_eval (a : ℕ → ℕ) (p : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n)) (x k : ℕ) :
    (prefixRangeCode p).eval (Nat.pair x k) =
      Part.some (indicator (fun x => ∃ i < k, a i = x) x) := by
  let step : OCode :=
    .comp (ordinaryProgram pairMax pairMax_computable) (.pair (.comp .right .right)
      (.comp (ordinaryProgram equalityBit equalityBit_computable)
        (.pair (.comp p (.comp .left .right)) .left)))
  have hs (i v : ℕ) : step.eval (Nat.pair x (Nat.pair i v)) =
      Part.some (max v (if a i = x then 1 else 0)) := by
    simp [step, Nat.Partrec.Code.eval, Seq.seq, Part.bind_eq_bind, BusyBeaverFunctions.ordinaryProgram_eval,
      hp, pairMax, equalityBit]
  change (Nat.Partrec.Code.prec .zero step).eval (Nat.pair x k) = _
  induction k with
  | zero =>
    rw [Nat.Partrec.Code.eval_prec_zero]
    change Part.some 0 = _
    simp [indicator]
  | succ k ih =>
    rw [Nat.Partrec.Code.eval_prec_succ, ih]
    simp only [Part.bind_eq_bind, Part.bind_some]
    rw [hs]
    have he : (∃ i < k+1, a i = x) ↔ (∃ i < k, a i = x) ∨ a k = x := by
      constructor
      · rintro ⟨i, hi, hv⟩
        by_cases hik : i < k
        · exact Or.inl ⟨i,hik,hv⟩
        · have hei : i = k := by omega
          exact Or.inr (hei ▸ hv)
      · rintro (⟨i,hi,hv⟩ | hv)
        · exact ⟨i,by omega,hv⟩
        · exact ⟨k,by omega,hv⟩
    unfold indicator
    simp only [he]
    by_cases h0 : ∃ i < k, a i = x <;> by_cases h1 : a k = x <;> simp [h0,h1]

theorem range_code_eval (a : ℕ → ℕ) (p : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n)) (x k : ℕ) :
    (rangeCode p).eval (Nat.pair x k) =
      Part.some (indicator (fun x => ∃ i ≤ k, a i = x) x) := by
  have hi : (Nat.Partrec.Code.pair .left (.comp .succ .right)).eval (Nat.pair x k) =
      Part.some (Nat.pair x (k+1)) := by simp [Nat.Partrec.Code.eval, Seq.seq]
  change ((Nat.Partrec.Code.pair .left (.comp .succ .right)).eval (Nat.pair x k)).bind _ = _
  rw [hi, Part.bind_some, prefix_range_eval a p hp x (k+1)]
  simp only [Nat.lt_succ_iff]

def recoverFailure (w : ℕ) : ℕ :=
  if w.unpair.1 = 0 ∧ w.unpair.2.unpair.1 < w.unpair.2.unpair.2 then 0 else 1

theorem recover_failure_primitive : Primrec recoverFailure := by
  have h : PrimrecPred (fun w : ℕ =>
      w.unpair.1 = 0 ∧ w.unpair.2.unpair.1 < w.unpair.2.unpair.2) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)).and
      (Primrec.nat_lt.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  exact Primrec.ite h (Primrec.const 0) (Primrec.const 1)

def recoverTestCode (p : OCode) : Code :=
  .comp (embed (ordinaryProgram recoverFailure recover_failure_primitive.to_comp))
    (.pair (.comp .query .right) (.pair .left (.comp (embed p) .right)))

def recoverSearchCode (p : OCode) : Code :=
  .comp (.find' (recoverTestCode p)) (.pair OracleProgramNumberings.identityCode .zero)

def recoverCode (p : OCode) : Code :=
  .comp (embed (rangeCode p)) (.pair OracleProgramNumberings.identityCode (recoverSearchCode p))

def firstNondeficientAbove (a : ℕ → ℕ) (ha : Function.Injective a) (x : ℕ) : ℕ :=
  Nat.find (nondeficient_values_unbounded a ha x)

theorem first_nondeficient_above_spec (a : ℕ → ℕ) (ha : Function.Injective a) (x : ℕ) :
    firstNondeficientAbove a ha x ∈ nondeficient a ∧
      x < a (firstNondeficientAbove a ha x) ∧
      ∀ t, t ∈ nondeficient a → x < a t → firstNondeficientAbove a ha x ≤ t := by
  have hex := nondeficient_values_unbounded a ha x
  change Nat.find hex ∈ nondeficient a ∧ x < a (Nat.find hex) ∧
    ∀ t, t ∈ nondeficient a → x < a t → Nat.find hex ≤ t
  exact ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun t ht hx => Nat.find_min' hex ⟨ht,hx⟩⟩

theorem recover_search_eval (a : ℕ → ℕ) (ha : Function.Injective a) (p : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n)) (x : ℕ) :
    eval (deficiency a) (recoverSearchCode p) x = Part.some (firstNondeficientAbove a ha x) := by
  let u := firstNondeficientAbove a ha x
  let P : ℕ → Prop := fun s => s ∈ nondeficient a ∧ x < a s
  have hu : P u := ⟨(first_nondeficient_above_spec a ha x).1,
    (first_nondeficient_above_spec a ha x).2.1⟩
  have hmin (t : ℕ) (ht : P t) : u ≤ t :=
    (first_nondeficient_above_spec a ha x).2.2 t ht.1 ht.2
  have test (t : ℕ) : eval (deficiency a) (recoverTestCode p) (Nat.pair x t) =
      Part.some (if P t then 0 else 1) := by
    by_cases hd : t ∈ deficiency a <;> by_cases hx : x < a t <;>
      simp [recoverTestCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
        hp, recoverFailure, indicator, P, nondeficient, hd, hx]
  have hi : eval (deficiency a) (.pair OracleProgramNumberings.identityCode .zero) x =
      Part.some (Nat.pair x 0) := by simp [eval, OracleProgramNumberings.identity_eval]
  change (eval (deficiency a) (.pair OracleProgramNumberings.identityCode .zero) x).bind _ = _
  rw [hi, Part.bind_some]
  apply Part.eq_some_iff.mpr
  rw [eval_find]
  refine ⟨Nat.zero_le _, ?_, ?_⟩
  · rw [test]
    change 0 ∈ Part.some (if P u then 0 else 1)
    rw [ite_eq_left hu]
    exact Part.mem_some 0
  · intro t _ htu
    have hnt : ¬ P t := fun h => Nat.not_le_of_gt htu (hmin t h)
    refine ⟨1, ?_, by decide⟩
    rw [test, ite_eq_right hnt]
    exact Part.mem_some 1

theorem recover_code_eval (a : ℕ → ℕ) (ha : Function.Injective a) (p : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n)) (x : ℕ) :
    eval (deficiency a) (recoverCode p) x = Part.some (indicator (Set.range a) x) := by
  let u := firstNondeficientAbove a ha x
  have hi : eval (deficiency a) (.pair OracleProgramNumberings.identityCode (recoverSearchCode p)) x =
      Part.some (Nat.pair x u) := by
    change (eval (deficiency a) OracleProgramNumberings.identityCode x).bind _ = _
    rw [OracleProgramNumberings.identity_eval, Part.bind_some, recover_search_eval a ha p hp,
      Part.map_some]
  change (eval (deficiency a) (.pair OracleProgramNumberings.identityCode (recoverSearchCode p)) x).bind _ = _
  rw [hi, Part.bind_some, eval_embed, range_code_eval a p hp x u]
  have he := bounded_range_membership a ha u x
    (first_nondeficient_above_spec a ha x).1 (first_nondeficient_above_spec a ha x).2.1
  unfold indicator
  simp only [Membership.mem, Set.Mem] at he ⊢
  simp only [← he]

theorem recover_reduction (a : ℕ → ℕ) (ha : Function.Injective a) (p : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n)) :
    TuringDegrees.Reduces (recoverCode p) (Set.range a) (deficiency a) := by
  intro x
  simpa only [Membership.mem, Set.Mem] using recover_code_eval a ha p hp x

def prefixFold (w : ℕ) : ℕ :=
  max w.unpair.1 (if w.unpair.2.unpair.1 = 1 ∧ w.unpair.2.unpair.2 = 0 then 1 else 0)

theorem prefix_fold_primitive : Primrec prefixFold := by
  have h : PrimrecPred (fun w : ℕ =>
      w.unpair.2.unpair.1 = 1 ∧ w.unpair.2.unpair.2 = 0) :=
    (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))) (Primrec.const 1)).and
      (Primrec.eq.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))) (Primrec.const 0))
  exact Primrec.nat_max.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.ite h (Primrec.const 1) (Primrec.const 0))

-- The recursion step input is (s,(x,oldBit)).
def prefixStepCode (p : OCode) : Code :=
  .comp (embed (ordinaryProgram prefixFold prefix_fold_primitive.to_comp))
    (.pair (.comp .right .right)
      (.pair (.comp .query (.comp .left .right))
        (.comp (embed (prefixRangeCode p)) (.pair (.comp .left .right) .left))))

def prefixDecisionCode (p : OCode) : Code :=
  .comp (.prec .zero (prefixStepCode p))
    (.pair OracleProgramNumberings.identityCode (embed p))

theorem prefix_decision_eval (a : ℕ → ℕ) (ha : Function.Injective a) (p : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n)) (s : ℕ) :
    eval (Set.range a) (prefixDecisionCode p) s = Part.some (indicator (deficiency a) s) := by
  let R : ℕ → Prop := fun x => x ∈ Set.range a ∧ ∀ i < s, a i ≠ x
  have step (x v : ℕ) : eval (Set.range a) (prefixStepCode p) (Nat.pair s (Nat.pair x v)) =
      Part.some (max v (if R x then 1 else 0)) := by
    by_cases hx : ∃ y, a y = x <;> by_cases hseen : ∃ i < s, a i = x
    · have hr : ¬ R x := by rintro ⟨_,h⟩;obtain ⟨i,hi,he⟩ := hseen;exact h i hi he
      simp [prefixStepCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
        prefix_range_eval a p hp, prefixFold, indicator, hx, hseen, hr]
    · have hr : R x := ⟨hx,by simpa using hseen⟩
      simp [prefixStepCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
        prefix_range_eval a p hp, prefixFold, indicator, hx, hseen, hr]
    · have hr : ¬ R x := fun h => hx h.1
      simp [prefixStepCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
        prefix_range_eval a p hp, prefixFold, indicator, hx, hseen, hr]
    · have hr : ¬ R x := fun h => hx h.1
      simp [prefixStepCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
        prefix_range_eval a p hp, prefixFold, indicator, hx, hseen, hr]
  have rec_eval : ∀ k, eval (Set.range a) (.prec .zero (prefixStepCode p)) (Nat.pair s k) =
      Part.some (if ∃ x < k, R x then 1 else 0) := by
    intro k
    induction k with
    | zero => simp [eval]
    | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_some, step]
      have he : (∃ x < k+1, R x) ↔ (∃ x < k, R x) ∨ R k := by
        constructor
        · rintro ⟨x,hx,hr⟩
          by_cases hk : x < k
          · exact Or.inl ⟨x,hk,hr⟩
          · have hxe : x=k := by omega
            exact Or.inr (hxe ▸ hr)
        · rintro (⟨x,hx,hr⟩|hr)
          · exact ⟨x,by omega,hr⟩
          · exact ⟨k,by omega,hr⟩
      simp only [he]
      by_cases h0 : ∃ x < k, R x <;> by_cases h1 : R k <;> simp [h0,h1]
  have hi : eval (Set.range a) (.pair OracleProgramNumberings.identityCode (embed p)) s =
      Part.some (Nat.pair s (a s)) := by
    simp [eval, OracleProgramNumberings.identity_eval, eval_embed, hp]
  change (eval (Set.range a) (.pair OracleProgramNumberings.identityCode (embed p)) s).bind _ = _
  rw [hi, Part.bind_some, rec_eval]
  change Part.some (if ∃ x < a s, x ∈ Set.range a ∧ ∀ i < s, a i ≠ x then 1 else 0) =
    Part.some (if s ∈ deficiency a then 1 else 0)
  simp only [← deficiency_prefix_iff a ha s]

theorem prefix_decision_zero (a : ℕ → ℕ) (ha : Function.Injective a) (p : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n)) (s : ℕ) (hs : a s = 0) :
    eval (Set.range a) (prefixDecisionCode p) s = Part.some 0 := by
  rw [prefix_decision_eval a ha p hp]
  have hn : s ∉ deficiency a := by
    rintro ⟨t, _, ht⟩
    rw [hs] at ht
    omega
  change Part.some (if s ∈ deficiency a then 1 else 0) = _
  rw [ite_eq_right hn]

theorem deficiency_reduction (a : ℕ → ℕ) (ha : Function.Injective a) (p : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n)) :
    TuringDegrees.Reduces (prefixDecisionCode p) (deficiency a) (Set.range a) := by
  intro x
  simpa only [Membership.mem, Set.Mem] using prefix_decision_eval a ha p hp x

end
end Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets
