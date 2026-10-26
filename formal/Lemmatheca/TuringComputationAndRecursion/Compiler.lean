import Lemmatheca.TuringComputationAndRecursion.Routines
import Lemmatheca.MachinesAndComputationHistories.MachinesAndComputationHistories

/-! A finite construction tree has exactly the shared finite-arity closure rules.
Its compiler is a structural operation on those trees, with actual finite tables
at every constructor, rather than a choice of an unrelated existing machine. -/
namespace Lemmatheca.ComputabilityTheory.RecursiveTapeCompiler

open CounterPrograms PartialRecursiveFunctions

inductive Code : ℕ → Type
  | zero (n : ℕ) : Code n
  | succ : Code 1
  | proj {n : ℕ} (i : Fin n) : Code n
  | comp {m n : ℕ} (h : Code m) (g : Fin m → Code n) : Code n
  | prec {n : ℕ} (g : Code n) (h : Code (n + 2)) : Code (n + 1)
  | search {n : ℕ} (f : Code (n + 1)) : Code n

def Code.eval : {n : ℕ} → Code n → PFunction n
  | _, .zero _ => fun _ => Part.some 0
  | _, .succ => fun x => Part.some (x.get 0 + 1)
  | _, .proj i => fun x => Part.some (x.get i)
  | _, .comp h g => strictComp h.eval (fun i => (g i).eval)
  | _, .prec g h => partialRec g.eval h.eval
  | _, .search f => minimize f.eval

def compile : {n : ℕ} → Code n → Routine n
  | _, .zero n => zeroRoutine n
  | _, .succ => successorRoutine
  | _, .proj i => projectionRoutine i
  | _, .comp h g => compositionRoutine (compile h) (fun i => compile (g i))
  | _, .prec g h => primitiveRecursionRoutine (compile g) (compile h)
  | _, .search f => minimizationRoutine (compile f)

theorem code_recursive {n : ℕ} (c : Code n) : Recursive c.eval := by
  induction c with
  | zero n => exact .zero n
  | succ => exact .succ
  | proj i => exact .proj i
  | comp h g ihh ihg => exact .comp ihh ihg
  | prec g h ihg ihh => exact .prec ihg ihh
  | search f ih => exact .search ih

theorem recursive_code {n : ℕ} (f : PFunction n) (hf : Recursive f) :
    ∃ c : Code n, c.eval = f := by
  classical
  induction hf with
  | zero n => exact ⟨.zero n,rfl⟩
  | succ => exact ⟨.succ,rfl⟩
  | proj i => exact ⟨.proj i,rfl⟩
  | @comp m n h g _ _ ihh ihg =>
      obtain ⟨ch,hch⟩ := ihh
      choose cg hcg using ihg
      refine ⟨.comp ch cg, ?_⟩
      simp only [Code.eval,hch]
      congr 1
      exact funext hcg
  | prec _ _ ihg ihh =>
      obtain ⟨cg,hcg⟩ := ihg
      obtain ⟨ch,hch⟩ := ihh
      exact ⟨.prec cg ch,by simp only [Code.eval,hcg,hch]⟩
  | search _ ih =>
      obtain ⟨cf,hcf⟩ := ih
      exact ⟨.search cf,by simp only [Code.eval,hcf]⟩

theorem compile_clean {n : ℕ} (c : Code n) : Clean (compile c) c.eval := by
  induction c with
  | zero n => exact zero_clean n
  | succ => exact successor_clean
  | proj i => exact projection_clean i
  | comp h g ihh ihg => exact composition_clean _ _ _ _ ihh ihg
  | prec g h ihg ihh => exact primitive_recursion_clean _ _ _ _ ihg ihh
  | search f ih => exact minimization_clean _ _ ih

theorem finite_arity_counter_compiler {n : ℕ} (f : PFunction n) (hf : Recursive f) :
    ∃ c : Code n, c.eval = f ∧ Clean (compile c) f ∧ routineEval (compile c) = f := by
  obtain ⟨c,hc⟩ := recursive_code f hf
  have hclean : Clean (compile c) f := hc ▸ compile_clean c
  exact ⟨c,hc,hclean,clean_eval (compile c) f hclean⟩

end Lemmatheca.ComputabilityTheory.RecursiveTapeCompiler
