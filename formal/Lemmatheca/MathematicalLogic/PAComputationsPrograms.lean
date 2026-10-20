import Lemmatheca.MathematicalLogic.PAComputations

/-! Both finite-arity primitive-recursive conventions describe the same programs. -/
namespace Lemmatheca.MathematicalLogic.PAComputations
open Lemmatheca.MathematicalLogic
open ArithmeticRepresentability

private theorem get_ofFn_function {n : ℕ} (x : Fin n → ℕ) :
    (List.Vector.ofFn x).get = x := funext (List.Vector.get_ofFn x)

theorem Program.eval_primitive {n : ℕ} (p : Program n) :
    Nat.Primrec' (fun v : PrimitiveRecursion.Args n => p.eval v.get) := by
  induction p with
  | zero => exact Nat.Primrec'.zero
  | succ =>
    simpa only [Program.eval, List.Vector.get_zero, Nat.succ_eq_add_one] using Nat.Primrec'.succ
  | proj i => exact Nat.Primrec'.get i
  | comp f g ihf ihg =>
    simpa only [Program.eval, get_ofFn_function] using
      Nat.Primrec'.comp (fun i v => (g i).eval v.get) ihf ihg
  | prec f g ihf ihg =>
    have h := PrimitiveRecursion.lastRec_primrec ihf ihg
    convert h using 1
    funext v
    simp only [Program.eval, primitiveRecFunction, PrimitiveRecursion.lastRec,
      PrimitiveRecursion.initialPart]
    simpa only [get_ofFn_function] using
      primitiveRec_lastRec (fun w => f.eval w.get) (fun w => g.eval w.get)
        (fun i => v.get i.castSucc) (v.get (Fin.last _))

end Lemmatheca.MathematicalLogic.PAComputations
