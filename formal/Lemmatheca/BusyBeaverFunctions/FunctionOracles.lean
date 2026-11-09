import Lemmatheca.OracleComputation.Closure
import Lemmatheca.TuringDegrees.Degrees

/-! Natural-valued functions as graph oracles, with actual common query programs. -/
namespace Lemmatheca.ComputabilityTheory.BusyBeaverFunctions

open Nat.Partrec (Code)
open OracleComputation TuringDegrees UniversalComputation

noncomputable section

/-- An implementation helper selecting an ordinary program for a supplied computable function. -/
def ordinaryProgram (f : ℕ → ℕ) (hf : Computable f) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec))

theorem ordinaryProgram_eval (f : ℕ → ℕ) (hf : Computable f) (x : ℕ) :
    Nat.Partrec.Code.eval (ordinaryProgram f hf) x = Part.some (f x) := by
  exact congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec))) x

/-- Pairing turns the graph of a total natural-valued function into a set of naturals. -/
def graph (f : ℕ → ℕ) : Set ℕ := {z | f z.unpair.1 = z.unpair.2}

/-- One fixed search program retrieves a function value from its graph set. -/
def graphLookup : OracleComputation.Code :=
  .comp (.find' complementQuery) (embed (.pair Nat.Partrec.Code.id .zero))

theorem graphLookup_eval (f : ℕ → ℕ) (x : ℕ) :
    eval (graph f) graphLookup x = Part.some (f x) := by
  classical
  have hpair : Nat.Partrec.Code.eval (.pair Nat.Partrec.Code.id .zero) x =
      Part.some (Nat.pair x 0) := by
    change Nat.pair <$> Nat.Partrec.Code.eval Nat.Partrec.Code.id x <*>
      Nat.Partrec.Code.eval .zero x = _
    rw [Nat.Partrec.Code.eval_id,
      show Nat.Partrec.Code.eval .zero x = Part.some 0 from Nat.Partrec.Code.eval_const 0 x]
    simp [Seq.seq]
  change (eval (graph f) (embed (.pair Nat.Partrec.Code.id .zero)) x).bind
    (eval (graph f) (.find' complementQuery)) = _
  rw [eval_embed, hpair, Part.bind_some]
  apply Part.eq_some_iff.mpr
  rw [eval_find]
  refine ⟨Nat.zero_le _, ?_, ?_⟩
  · rw [complement_query_eval]
    simp [indicator, graph]
  · intro i _ hi
    refine ⟨1, ?_, by decide⟩
    rw [complement_query_eval]
    simp [indicator, graph, Nat.ne_of_gt hi]

def equalityBit (z : ℕ) : ℕ := if z.unpair.1 = z.unpair.2 then 1 else 0

theorem equalityBit_computable : Computable equalityBit := by
  exact (Primrec.ite
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
    (Primrec.const 1) (Primrec.const 0)).to_comp

def graphDecider (c : OracleComputation.Code) : OracleComputation.Code :=
  .comp (embed (ordinaryProgram equalityBit equalityBit_computable))
    (.pair (.comp c .left) .right)

theorem graphDecider_eval (A : Set ℕ) (f : ℕ → ℕ) (c : OracleComputation.Code)
    (hc : ∀ x, eval A c x = Part.some (f x)) (z : ℕ) :
    eval A (graphDecider c) z = Part.some (indicator (fun q => q ∈ graph f) z) := by
  classical
  have hinner : eval A (.pair (.comp c .left) .right) z =
      Part.some (Nat.pair (f z.unpair.1) z.unpair.2) := by
    simp [eval, hc]
  change (eval A (.pair (.comp c .left) .right) z).bind
    (eval A (embed (ordinaryProgram equalityBit equalityBit_computable))) = _
  rw [hinner, Part.bind_some, eval_embed, ordinaryProgram_eval]
  by_cases h : f z.unpair.1 = z.unpair.2 <;> simp [equalityBit, graph, indicator, h]

theorem function_computable_iff_graph_reducible (A : Set ℕ) (f : ℕ → ℕ) :
    PartialComputable A (fun x => Part.some (f x)) ↔ Reducible (graph f) A := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨graphDecider c, graphDecider_eval A f c (fun x => congrFun hc x)⟩
  · rintro ⟨c, hc⟩
    refine ⟨subst c graphLookup, funext (fun x => ?_)⟩
    rw [subst_eval (graph f) A c hc, graphLookup_eval]

theorem computable_graph {f : ℕ → ℕ} (hf : Computable f) :
    ComputablePred (fun z => z ∈ graph f) := by
  change ComputablePred (fun z : ℕ => f z.unpair.1 = z.unpair.2)
  exact (Primrec.eq.decide.to_comp.comp
    (hf.comp (Primrec.fst.comp Primrec.unpair).to_comp)
    (Primrec.snd.comp Primrec.unpair).to_comp).computablePred

end
end Lemmatheca.ComputabilityTheory.BusyBeaverFunctions
