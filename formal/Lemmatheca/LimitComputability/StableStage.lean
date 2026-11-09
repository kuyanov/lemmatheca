import Lemmatheca.LimitComputability.Approximation
import Lemmatheca.TuringJump.Recoding

/-! The specified future-change index and actual least-stable-stage oracle program. -/
namespace Lemmatheca.ComputabilityTheory.LimitComputability

open UniversalComputation OracleComputation OracleProgramNumberings TuringJump

noncomputable section

set_option backward.isDefEq.respectTransparency false

def FutureChange (a : Approximation) (x s : ℕ) : Prop :=
  ∃ r, s < r ∧ a r x ≠ a s x

def futureChangeSet (a : Approximation) : Set ℕ :=
  {w | FutureChange a w.unpair.1 w.unpair.2}

theorem future_change_enumerable (a : Approximation) (ha : Computable₂ a) :
    REPred (futureChangeSet a) := by
  classical
  have hleft : Computable (fun p : ℕ × ℕ => a p.2 p.1.unpair.1) :=
    ha.comp Computable.snd ((Computable.fst.comp Computable.unpair).comp Computable.fst)
  have hright : Computable (fun p : ℕ × ℕ => a p.1.unpair.2 p.1.unpair.1) :=
    ha.comp ((Computable.snd.comp Computable.unpair).comp Computable.fst)
      ((Computable.fst.comp Computable.unpair).comp Computable.fst)
  have hne : ComputablePred (fun p : ℕ × ℕ => a p.2 p.1.unpair.1 ≠ a p.1.unpair.2 p.1.unpair.1) :=
    (Primrec.eq.decide.to_comp.comp hleft hright).computablePred.not
  have hlt : ComputablePred (fun p : ℕ × ℕ => p.1.unpair.2 < p.2) :=
    (Primrec.nat_lt.comp ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst) Primrec.snd).computablePred
  have hboth : ComputablePred (fun p : ℕ × ℕ =>
      p.1.unpair.2 < p.2 ∧ a p.2 p.1.unpair.1 ≠ a p.1.unpair.2 p.1.unpair.1) := by
    apply Computable.computablePred
    simpa only [Bool.decide_and] using Primrec.and.to_comp.comp hlt.decide hne.decide
  exact (enumerable_iff_decidable_certificate (futureChangeSet a)).mpr
    ⟨fun w r => w.unpair.2 < r ∧ a r w.unpair.1 ≠ a w.unpair.2 w.unpair.1,
      hboth, fun _ => Iff.rfl⟩

def changeRecognizerIndex (a : Approximation) (ha : Computable₂ a) : ℕ :=
  Classical.choose ((enumerable_iff_index (futureChangeSet a)).mp (future_change_enumerable a ha))

theorem change_recognizer_spec (a : Approximation) (ha : Computable₂ a) (w : ℕ) :
    FutureChange a w.unpair.1 w.unpair.2 ↔
      (UniversalComputation.phi (changeRecognizerIndex a ha) w).Dom := by
  exact Classical.choose_spec
    ((enumerable_iff_index (futureChangeSet a)).mp (future_change_enumerable a ha)) w

def changeIndexInput (a : Approximation) (ha : Computable₂ a) (w : ℕ) : ℕ :=
  ordinaryFreeze (changeRecognizerIndex a ha) w

def changeIndex (a : Approximation) (ha : Computable₂ a) (x s : ℕ) : ℕ :=
  changeIndexInput a ha (Nat.pair x s)

theorem change_index_primitive (a : Approximation) (ha : Computable₂ a) :
    Primrec (changeIndexInput a ha) := by
  exact ordinary_freeze_primitive.comp (Primrec.const (changeRecognizerIndex a ha)) Primrec.id

theorem change_index_correct (a : Approximation) (ha : Computable₂ a) (x s : ℕ) :
    FutureChange a x s ↔ changeIndex a ha x s ∈ haltingDiagonal := by
  change FutureChange a x s ↔
    (UniversalComputation.phi (ordinaryFreeze (changeRecognizerIndex a ha) (Nat.pair x s))
      (changeIndex a ha x s)).Dom
  rw [ordinary_freeze_eval]
  simpa only [Nat.unpair_pair] using change_recognizer_spec a ha (Nat.pair x s)

private def totalCode (f : ℕ → ℕ) (hf : Computable f) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec))

private theorem totalCode_eval (f : ℕ → ℕ) (hf : Computable f) (x : ℕ) :
    (totalCode f hf).eval x = Part.some (f x) := by
  exact congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec))) x

def futureQueryCode (a : Approximation) (ha : Computable₂ a) : Code :=
  .comp .query (embed (totalCode (changeIndexInput a ha) (change_index_primitive a ha).to_comp))

def stableSearchCode (a : Approximation) (ha : Computable₂ a) : Code :=
  .comp (.find' (futureQueryCode a ha)) (.pair identityCode .zero)

def stableSearch (a : Approximation) (x : ℕ) : Part ℕ := by
  classical
  exact Nat.rfind (fun s => Part.some (decide (¬FutureChange a x s)))

theorem stable_search_eval (a : Approximation) (ha : Computable₂ a) (x : ℕ) :
    eval haltingDiagonal (stableSearchCode a ha) x = stableSearch a x := by
  classical
  have hq (s : ℕ) : eval haltingDiagonal (futureQueryCode a ha) (Nat.pair x s) =
      Part.some (if FutureChange a x s then 1 else 0) := by
    unfold futureQueryCode
    rw [eval, eval_embed, totalCode_eval, Part.bind_some]
    change Part.some (indicator haltingDiagonal (changeIndex a ha x s)) = _
    congr 1
    change (if changeIndex a ha x s ∈ haltingDiagonal then 1 else 0) = _
    rw [← change_index_correct]
  simp only [stableSearchCode, eval, identity_eval, Part.map_some, Part.bind_some,
    Nat.unpair_pair, Nat.add_zero, hq]
  rw [Part.map_id' (fun _ => rfl)]
  unfold stableSearch
  congr 1
  funext t
  congr 1
  by_cases h : FutureChange a x t <;> simp [h]

theorem stable_stage_exists (a : Approximation) (A : Set ℕ) (ha : Converges a A) (x : ℕ) :
    ∃ s, ¬FutureChange a x s := by
  obtain ⟨t, ht⟩ := ha x
  refine ⟨t, ?_⟩
  rintro ⟨r, htr, hne⟩
  exact hne ((ht r (by omega)).trans (ht t le_rfl).symm)

def stableStage (a : Approximation) (A : Set ℕ) (ha : Converges a A) (x : ℕ) : ℕ := by
  classical
  exact Nat.find (stable_stage_exists a A ha x)

theorem stable_stage_spec (a : Approximation) (A : Set ℕ) (ha : Converges a A) (x : ℕ) :
    ¬FutureChange a x (stableStage a A ha x) ∧
      (∀ s < stableStage a A ha x, FutureChange a x s) ∧
      a (stableStage a A ha x) x = indicator A x := by
  classical
  have hs : ¬FutureChange a x (stableStage a A ha x) :=
    Nat.find_spec (stable_stage_exists a A ha x)
  have hmin : ∀ s < stableStage a A ha x, FutureChange a x s := by
    intro s hlt
    by_contra hn
    have hh : stableStage a A ha x ≤ s := Nat.find_min' _ hn
    omega
  refine ⟨hs, hmin, ?_⟩
  obtain ⟨t, ht⟩ := ha x
  let r := max t (stableStage a A ha x + 1)
  have hsr : stableStage a A ha x < r := by dsimp [r]; omega
  have he : a r x = a (stableStage a A ha x) x := by
    by_contra hn
    exact hs ⟨r, hsr, hn⟩
  exact he.symm.trans (ht r (by dsimp [r]; omega))

theorem stable_search_total (a : Approximation) (A : Set ℕ)
    (hc : Computable₂ a) (ha : Converges a A) (x : ℕ) :
    eval haltingDiagonal (stableSearchCode a hc) x = Part.some (stableStage a A ha x) := by
  classical
  rw [stable_search_eval]
  apply Part.eq_some_iff.mpr
  unfold stableSearch
  rw [Nat.mem_rfind]
  refine ⟨?_, ?_⟩
  · simp [(stable_stage_spec a A ha x).1]
  · intro t ht
    simp [(stable_stage_spec a A ha x).2.1 t ht]

private theorem approximation_input_computable (a : Approximation) (ha : Computable₂ a) :
    Computable (fun w : ℕ => a w.unpair.1 w.unpair.2) := by
  exact ha.comp (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair)

def stableDecisionCode (a : Approximation) (ha : Computable₂ a) : Code :=
  .comp (embed (totalCode (fun w : ℕ => a w.unpair.1 w.unpair.2)
    (approximation_input_computable a ha))) (.pair (stableSearchCode a ha) identityCode)

theorem stable_decision_eval (a : Approximation) (A : Set ℕ)
    (hc : Computable₂ a) (ha : Converges a A) (x : ℕ) :
    eval haltingDiagonal (stableDecisionCode a hc) x = Part.some (indicator A x) := by
  unfold stableDecisionCode
  rw [eval]
  have hp : eval haltingDiagonal (.pair (stableSearchCode a hc) identityCode) x =
      Part.some (Nat.pair (stableStage a A ha x) x) := by
    simp only [eval, stable_search_total a A hc ha, identity_eval, Part.bind_some, Part.map_some]
  rw [hp, Part.bind_some, eval_embed, totalCode_eval]
  simpa only [Nat.unpair_pair] using
    congrArg Part.some (stable_stage_spec a A ha x).2.2

theorem limit_reducible (A : Set ℕ) (hA : LimitComputable A) :
    TuringDegrees.Reducible A haltingDiagonal := by
  obtain ⟨a, hc, _, ha⟩ := hA
  exact ⟨stableDecisionCode a hc, stable_decision_eval a A hc ha⟩

end
end Lemmatheca.ComputabilityTheory.LimitComputability
