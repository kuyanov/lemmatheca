import Lemmatheca.LowBasisTheorem.Restricted

/-! Histories, finite-level compactness, and the actual jump-decision oracle program. -/
namespace Lemmatheca.ComputabilityTheory.LowBasisTheorem

open ComputableTreesAndPaths IncomparableTuringDegrees PostsTheorem
open UniversalComputation OracleComputation OracleProgramNumberings TuringDegrees
open Classical

noncomputable section
set_option backward.isDefEq.respectTransparency false

def history (δ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => if δ (FiniteSequenceCoding.cons e (history δ e)) ∈ haltingDiagonal
      then history δ e else FiniteSequenceCoding.cons e (history δ e)

def recordedBit (δ : ℕ → ℕ) (e : ℕ) : ℕ :=
  indicator (fun q => q ∈ haltingDiagonal) (δ (FiniteSequenceCoding.cons e (history δ e)))

theorem history_survival (T : Set ℕ) (hT : IsBinaryTree T)
    (hc : ComputablePred (fun u => u ∈ T)) (hi : ∀ n, HasLevel T n) :
    (∀ e n, HasLevel (restricted T (history (failureQuery T hc) e)) n) ∧
      ∀ e, restricted T (history (failureQuery T hc) (e + 1)) ⊆
        restricted T (history (failureQuery T hc) e) := by
  classical
  have hl : ∀ e n, HasLevel (restricted T (history (failureQuery T hc) e)) n := by
    intro e
    induction e with
    | zero => intro n; simpa only [history, restricted_zero] using hi n
    | succ e ih =>
      intro n
      by_cases hq : failureQuery T hc
          (FiniteSequenceCoding.cons e (history (failureQuery T hc) e)) ∈ haltingDiagonal
      · simpa only [history, ite_eq_left hq] using ih n
      · have hf : ¬ Failed T (FiniteSequenceCoding.cons e (history (failureQuery T hc) e)) :=
          fun hf => hq ((failure_query_correct T hc _).mpr hf)
        have hs : HasLevel
            (restricted T (FiniteSequenceCoding.cons e (history (failureQuery T hc) e))) n := by
          by_contra hn
          exact hf ⟨n, (empty_level_iff T hT _ n).mpr hn⟩
        simpa only [history, ite_eq_right hq] using hs
  refine ⟨hl, fun e => ?_⟩
  by_cases hq : failureQuery T hc
      (FiniteSequenceCoding.cons e (history (failureQuery T hc) e)) ∈ haltingDiagonal
  · simp only [history, ite_eq_left hq]
    exact Set.Subset.rfl
  · simp only [history, ite_eq_right hq]
    exact (restricted_subsets T _ e).1

def intersectionTree (S : ℕ → Set ℕ) : Set ℕ := {u | ∀ e, u ∈ S e}

theorem nested_levels (S : ℕ → Set ℕ) (hS : ∀ e, IsBinaryTree (S e))
    (hn : ∀ e, S (e + 1) ⊆ S e) (hi : ∀ e n, HasLevel (S e) n) :
    IsBinaryTree (intersectionTree S) ∧
      (∀ n, HasLevel (intersectionTree S) n) ∧
      ∃ X, ∀ e, Path (S e) X := by
  classical
  have hm {i j : ℕ} (hij : i ≤ j) : S j ⊆ S i := by
    induction j, hij using Nat.le_induction with
    | base => exact Set.Subset.rfl
    | succ j _ ih => exact (hn j).trans ih
  have ht : IsBinaryTree (intersectionTree S) := by
    refine ⟨fun u hu => (hS 0).1 u (hu 0), ?_⟩
    intro u v hu hv hp e
    exact (hS e).2 u v hu (hv e) hp
  have hl : ∀ n, HasLevel (intersectionTree S) n := by
    intro n
    by_contra hlevel
    have hex : ∀ u ∈ binaryLevel n, ∃ e, u ∉ S e := by
      intro u hu
      by_contra hbad
      push Not at hbad
      exact hlevel ⟨u, hbad, ((binary_level_spec n u).mp hu).2⟩
    let f : ℕ → ℕ := fun u => if hu : u ∈ binaryLevel n then
      Classical.choose (hex u hu) else 0
    have hf (u : ℕ) (hu : u ∈ binaryLevel n) : u ∉ S (f u) := by
      dsimp [f]
      rw [dite_eq_left hu]
      exact Classical.choose_spec (hex u hu)
    let m := (binaryLevel n).toFinset.sup f
    obtain ⟨u, hu, hlen⟩ := hi m n
    have hb : u ∈ binaryLevel n := (binary_level_spec n u).mpr ⟨(hS m).1 u hu, hlen⟩
    have hfm : f u ≤ m := Finset.le_sup (List.mem_toFinset.mpr hb)
    exact hf u hb (hm hfm hu)
  obtain ⟨X, hX⟩ := (all_levels_path _ ht).mp hl
  exact ⟨ht, hl, X, fun e n => hX n e⟩

theorem exact_jump (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T))
    (X : Set ℕ) (hX : ∀ e, Path (restricted T (history (failureQuery T hc) e)) X)
    (e : ℕ) :
    indicator (fun j => j ∈ TuringJump.jump X) e = recordedBit (failureQuery T hc) e := by
  classical
  let l := history (failureQuery T hc) e
  have hd : FiniteSequenceCoding.decode (FiniteSequenceCoding.cons e l) =
      e :: FiniteSequenceCoding.decode l := by
    rw [← FiniteSequenceCoding.code_decode l, ← FiniteSequenceCoding.code_cons,
      FiniteSequenceCoding.decode_code, FiniteSequenceCoding.decode_code]
  by_cases hq : failureQuery T hc (FiniteSequenceCoding.cons e l) ∈ haltingDiagonal
  · have hj : e ∈ TuringJump.jump X := by
      by_contra hj
      have hp : Path (restricted T (FiniteSequenceCoding.cons e l)) X := by
        apply (restricted_paths T _ X).mpr
        have hold := (restricted_paths T l X).mp (hX e)
        refine ⟨hold.1, ?_⟩
        intro j hjl
        rw [hd] at hjl
        rcases List.mem_cons.mp hjl with rfl | hjl
        · exact hj
        · exact hold.2 j hjl
      obtain ⟨m, hempty⟩ := (failure_query_correct T hc _).mp hq
      exact hempty (prefixCode X m)
        ((binary_level_spec m _).mpr ⟨prefix_code_valid X m, (prefixCode_spec X m).1⟩) (hp m)
    simp [recordedBit, l, indicator, hq, hj]
  · have hj : e ∉ TuringJump.jump X := by
      have hnext := hX (e + 1)
      change Path (restricted T (if failureQuery T hc (FiniteSequenceCoding.cons e l) ∈
        haltingDiagonal then l else FiniteSequenceCoding.cons e l)) X at hnext
      rw [ite_eq_right hq] at hnext
      exact ((restricted_paths T _ X).mp hnext).2 e (by rw [hd]; simp)
    simp [recordedBit, l, indicator, hq, hj]

def candidateInput (δ : ℕ → ℕ) (z : ℕ) : ℕ :=
  δ (FiniteSequenceCoding.cons z.unpair.1 z.unpair.2)

theorem candidate_input_primitive (δ : ℕ → ℕ) (hδ : Primrec δ) :
    Primrec (candidateInput δ) := by
  exact hδ.comp (FiniteSequenceCoding.primrec_cons.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

def candidateCode (δ : ℕ → ℕ) (hδ : Primrec δ) : OracleComputation.Code :=
  .comp .query (embed (ordinaryCode (candidateInput δ)
    (Primrec.nat_iff.mp (candidate_input_primitive δ hδ))))

def retainInput (z : ℕ) : ℕ :=
  if z.unpair.2 = 0 then FiniteSequenceCoding.cons z.unpair.1.unpair.1 z.unpair.1.unpair.2
  else z.unpair.1.unpair.2

theorem retain_input_primitive : Primrec retainInput := by
  have hz : PrimrecPred (fun z : ℕ => z.unpair.2 = 0) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0)
  exact Primrec.ite hz
    (FiniteSequenceCoding.primrec_cons.comp
      ((Primrec.fst.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair))
      ((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair)))
    ((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair))

def stepCode (δ : ℕ → ℕ) (hδ : Primrec δ) : OracleComputation.Code :=
  .comp (embed (ordinaryCode retainInput (Primrec.nat_iff.mp retain_input_primitive)))
    (.pair identityCode (candidateCode δ hδ))

def historyCode (δ : ℕ → ℕ) (hδ : Primrec δ) : OracleComputation.Code :=
  .comp (.prec .zero (.comp (stepCode δ hδ) .right)) (.pair .zero identityCode)

def jumpCode (δ : ℕ → ℕ) (hδ : Primrec δ) : OracleComputation.Code :=
  .comp (candidateCode δ hδ) (.pair identityCode (historyCode δ hδ))

theorem history_code_eval (δ : ℕ → ℕ) (hδ : Primrec δ) (e : ℕ) :
    eval haltingDiagonal (historyCode δ hδ) e = Part.some (history δ e) := by
  have hq (z : ℕ) : eval haltingDiagonal (candidateCode δ hδ) z =
      Part.some (indicator (fun q => q ∈ haltingDiagonal) (candidateInput δ z)) := by
    simp only [candidateCode, eval, eval_embed, ordinaryCode_eval, Part.bind_some]
  have hs (e l : ℕ) : eval haltingDiagonal (stepCode δ hδ) (Nat.pair e l) =
      Part.some (if δ (FiniteSequenceCoding.cons e l) ∈ haltingDiagonal then l
        else FiniteSequenceCoding.cons e l) := by
    simp only [stepCode, eval, identity_eval, hq, Part.bind_some, Part.map_some,
      eval_embed, ordinaryCode_eval]
    simp [retainInput, candidateInput, indicator, Nat.unpair_pair]
  have hr (k : ℕ) : eval haltingDiagonal
      (.prec .zero (.comp (stepCode δ hδ) .right)) (Nat.pair 0 k) =
      Part.some (history δ k) := by
    induction k with
    | zero => simp [eval, history]
    | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_some]
      change (eval haltingDiagonal .right (Nat.pair 0 (Nat.pair k (history δ k)))).bind
        (eval haltingDiagonal (stepCode δ hδ)) = _
      simp only [eval, Nat.unpair_pair, Part.bind_some]
      exact hs k (history δ k)
  change (eval haltingDiagonal (.pair .zero identityCode) e).bind
    (eval haltingDiagonal (.prec .zero (.comp (stepCode δ hδ) .right))) = _
  have hp : eval haltingDiagonal (.pair .zero identityCode) e =
      Part.some (Nat.pair 0 e) := by
    simp only [eval, identity_eval, Part.bind_some, Part.map_some]
  rw [hp, Part.bind_some]
  exact hr e

theorem jump_code_eval (δ : ℕ → ℕ) (hδ : Primrec δ) (e : ℕ) :
    eval haltingDiagonal (jumpCode δ hδ) e = Part.some (recordedBit δ e) := by
  have hp : eval haltingDiagonal (.pair identityCode (historyCode δ hδ)) e =
      Part.some (Nat.pair e (history δ e)) := by
    simp only [eval, identity_eval, history_code_eval, Part.bind_some, Part.map_some]
  change (eval haltingDiagonal (.pair identityCode (historyCode δ hδ)) e).bind
    (eval haltingDiagonal (candidateCode δ hδ)) = _
  rw [hp, Part.bind_some]
  simp only [candidateCode, eval, eval_embed, ordinaryCode_eval, Part.bind_some]
  simp only [candidateInput, Nat.unpair_pair, recordedBit]

theorem jump_code_reduces (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T))
    (X : Set ℕ) (hX : ∀ e, Path (restricted T (history (failureQuery T hc) e)) X) :
    Reduces (jumpCode (failureQuery T hc) (failure_query_primitive T hc))
      (TuringJump.jump X) haltingDiagonal := by
  intro e
  rw [jump_code_eval, exact_jump T hc X hX e]

end
end Lemmatheca.ComputabilityTheory.LowBasisTheorem
