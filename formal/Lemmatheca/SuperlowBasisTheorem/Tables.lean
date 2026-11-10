import Lemmatheca.SuperlowBasisTheorem.Histories

/-! The literal all-history query set, its maximum, and direct finite-word replay. -/
namespace Lemmatheca.ComputabilityTheory.SuperlowBasisTheorem

open UniversalComputation OracleComputation OracleProgramNumberings
open LowBasisTheorem StrongReductions PostsTheorem

noncomputable section
set_option backward.isDefEq.respectTransparency false

def historyQueries (δ : ℕ → ℕ) (e : ℕ) : List ℕ :=
  (binaryRows (e + 1)).flatMap (fun η => (List.range (e + 1)).map
    (fun i => δ (FiniteSequenceCoding.cons i (forcedHistory η i))))

def historyQuerySet (δ : ℕ → ℕ) (e : ℕ) : Finset ℕ :=
  (historyQueries δ e).toFinset

def historyWidth (δ : ℕ → ℕ) (e : ℕ) : ℕ :=
  ((historyQueries δ e).map Nat.succ).foldl max 0

theorem history_query_set_spec (δ : ℕ → ℕ) (e q : ℕ) :
    q ∈ historyQuerySet δ e ↔ ∃ η ∈ binaryRows (e + 1), ∃ i ≤ e,
      q = δ (FiniteSequenceCoding.cons i (forcedHistory η i)) := by
  simp only [historyQuerySet, List.mem_toFinset, historyQueries, List.mem_flatMap,
    List.mem_map, List.mem_range, Nat.lt_succ_iff]
  aesop

theorem history_width_computable (δ : ℕ → ℕ) (hδ : Primrec δ) :
    Computable (historyWidth δ) := by
  have hcell : Primrec (fun p : (ℕ × List ℕ) × ℕ =>
      δ (FiniteSequenceCoding.cons p.2 (forcedHistory p.1.2 p.2))) :=
    hδ.comp (FiniteSequenceCoding.primrec_cons.comp Primrec.snd
      (forced_history_primitive.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
  have hrow : Primrec (fun p : ℕ × List ℕ =>
      (List.range (p.1 + 1)).map (fun i => δ (FiniteSequenceCoding.cons i (forcedHistory p.2 i)))) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)) hcell.to₂
  have hqueries : Primrec (historyQueries δ) :=
    Primrec.list_flatMap (binaryRows_primrec.comp Primrec.succ) hrow.to₂
  have hs : Primrec (fun e => (historyQueries δ e).map Nat.succ) :=
    Primrec.list_map hqueries (Primrec.succ.comp Primrec.snd).to₂
  have hm := Primrec.list_foldl hs (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact hm.to_comp

private theorem fold_max_ge_start (l : List ℕ) (z : ℕ) : z ≤ l.foldl max z := by
  induction l generalizing z with
  | nil => exact le_rfl
  | cons a l ih => exact (le_max_left z a).trans (ih (max z a))

private theorem fold_max_ge_mem (l : List ℕ) (a z : ℕ) (ha : a ∈ l) : a ≤ l.foldl max z := by
  induction l generalizing z with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact (le_max_right z a).trans (fold_max_ge_start l (max z a))
    · exact ih (max z b) ha

theorem query_lt_width (δ : ℕ → ℕ) (e q : ℕ) (hq : q ∈ historyQuerySet δ e) :
    q < historyWidth δ e := by
  have hm : q + 1 ∈ (historyQueries δ e).map Nat.succ :=
    List.mem_map.mpr ⟨q, List.mem_toFinset.mp hq, rfl⟩
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self q) (fold_max_ge_mem _ _ 0 hm)

theorem actual_queries_in_set (δ : ℕ → ℕ) (C : Set ℕ) (e : ℕ) :
    ∀ p ∈ answerTrace δ C e, p.1 ∈ historyQuerySet δ e := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have hin : i ≤ e := by have := List.mem_range.mp hi; omega
  apply (history_query_set_spec δ e _).mpr
  refine ⟨answerWord δ C (e + 1), (answer_word_spec δ C (e + 1)).1, i, hin, ?_⟩
  rw [(answer_word_spec δ C (e + 1)).2 i (by omega)]

theorem jump_trace_bounded (δ : ℕ → ℕ) (hδ : Primrec δ) (C : Set ℕ) (e : ℕ) :
    Derives (jumpCode δ hδ) e (answerTrace δ C e) (answerBit δ C e) ∧
      Consistent C (answerTrace δ C e) ∧
      ∀ p ∈ answerTrace δ C e, p.1 < historyWidth δ e := by
  have ht := jump_code_trace δ hδ C e
  exact ⟨ht.1, ht.2.1, fun p hp =>
    query_lt_width δ e p.1 (actual_queries_in_set δ C e p hp)⟩

def replayHistory (δ : ℕ → ℕ) (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => if beta w (δ (FiniteSequenceCoding.cons e (replayHistory δ w e))) = 1
      then replayHistory δ w e else FiniteSequenceCoding.cons e (replayHistory δ w e)

def historyLookup (δ : ℕ → ℕ) (e w : ℕ) : ℕ :=
  beta w (δ (FiniteSequenceCoding.cons e (replayHistory δ w e)))

def historyData (δ : ℕ → ℕ) : TableData := ⟨historyWidth δ, historyLookup δ⟩

theorem replay_finite_oracle (δ : ℕ → ℕ) (w : ℕ) :
    replayHistory δ w = answerHistory δ (finiteOracle w) ∧
      (fun e => historyLookup δ e w) = answerBit δ (finiteOracle w) := by
  have hh : replayHistory δ w = answerHistory δ (finiteOracle w) := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [replayHistory, answerHistory, ih, finiteOracle, Membership.mem, Set.Mem, Set.ofPred]
  refine ⟨hh, ?_⟩
  funext e
  dsimp only [historyLookup, answerBit]
  rw [hh]
  simpa only [Membership.mem, Set.Mem] using
    (finiteOracle_indicator w (δ (FiniteSequenceCoding.cons e (answerHistory δ (finiteOracle w) e)))).symm

theorem history_lookup_computable (δ : ℕ → ℕ) (hδ : Primrec δ) :
    Computable (fun p : ℕ × ℕ => historyLookup δ p.1 p.2) := by
  let g : ℕ → ℕ × ℕ → ℕ := fun w p =>
    if beta w (δ (FiniteSequenceCoding.cons p.1 p.2)) = 1 then p.2
      else FiniteSequenceCoding.cons p.1 p.2
  have hcons : Primrec (fun p : ℕ × (ℕ × ℕ) => FiniteSequenceCoding.cons p.2.1 p.2.2) :=
    FiniteSequenceCoding.primrec_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : ℕ × (ℕ × ℕ) => beta p.1 (δ (FiniteSequenceCoding.cons p.2.1 p.2.2))) :=
    beta_primitive.comp Primrec.fst (hδ.comp hcons)
  have hg : Primrec₂ g :=
    Primrec.ite (Primrec.eq.comp hb (Primrec.const 1)) (Primrec.snd.comp Primrec.snd) hcons
  have hr : Primrec (fun p : ℕ × ℕ => replayHistory δ p.1 p.2) := by
    have h := Primrec.nat_rec (Primrec.const 0) hg
    refine h.of_eq ?_
    intro w n
    induction n with
    | zero => rfl
    | succ n ih => simp only [g, replayHistory, ih]
  exact (beta_primitive.comp Primrec.snd
    (hδ.comp (FiniteSequenceCoding.primrec_cons.comp Primrec.fst
      (hr.comp (Primrec.snd.pair Primrec.fst))))).to_comp

theorem history_scheme (δ : ℕ → ℕ) (hδ : Primrec δ) : IsScheme (historyData δ) := by
  exact ⟨history_width_computable δ hδ, history_lookup_computable δ hδ,
    fun e w => beta_bits w _⟩

theorem history_prefix_replay (δ : ℕ → ℕ) (C : Set ℕ) (e : ℕ) :
    (∀ i ≤ e, replayHistory δ (prefixCode C (historyWidth δ e)) i = answerHistory δ C i) ∧
      historyLookup δ e (prefixCode C (historyWidth δ e)) = answerBit δ C e := by
  have hq (i : ℕ) (hi : i ≤ e) :
      δ (FiniteSequenceCoding.cons i (answerHistory δ C i)) < historyWidth δ e := by
    apply query_lt_width δ e _
    apply (history_query_set_spec δ e _).mpr
    refine ⟨answerWord δ C (e + 1), (answer_word_spec δ C (e + 1)).1, i, hi, ?_⟩
    rw [(answer_word_spec δ C (e + 1)).2 i (by omega)]
  have hb (i : ℕ) (hi : i ≤ e) :
      beta (prefixCode C (historyWidth δ e)) (δ (FiniteSequenceCoding.cons i (answerHistory δ C i))) =
        indicator C (δ (FiniteSequenceCoding.cons i (answerHistory δ C i))) := by
    simpa only [Membership.mem, Set.Mem] using
      (prefixCode_spec C (historyWidth δ e)).2 _ (hq i hi)
  have hh : ∀ i ≤ e,
      replayHistory δ (prefixCode C (historyWidth δ e)) i = answerHistory δ C i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      simp only [replayHistory, ih (by omega), hb i (by omega)]
      by_cases h : C (δ (FiniteSequenceCoding.cons i (answerHistory δ C i)))
      · simp [answerHistory, indicator, Membership.mem, Set.Mem, h]
      · simp [answerHistory, indicator, Membership.mem, Set.Mem, h]
  refine ⟨hh, ?_⟩
  dsimp only [historyLookup]
  rw [hh e le_rfl, hb e le_rfl]
  rfl

theorem history_table_recorded_bit (δ : ℕ → ℕ) (e : ℕ) :
    historyLookup δ e (prefixCode haltingDiagonal (historyWidth δ e)) = recordedBit δ e := by
  exact (history_prefix_replay δ haltingDiagonal e).2.trans
    (congrFun (halting_histories δ).2 e)

end
end Lemmatheca.ComputabilityTheory.SuperlowBasisTheorem
