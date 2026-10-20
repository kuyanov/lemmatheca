import Lemmatheca.MathematicalLogic.PAListFold

/-! A parameterized fold compiled into the concrete numerical list traversal.
The parameter is carried explicitly in each accumulator state. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u

/-- Input order for `h` is parameter, current element, accumulator. -/
def paramFoldStep (h : Program 3) : Program 2 :=
  .comp squarePair ![
    .comp unpairLeft ![.proj 1],
    .comp h ![.comp unpairLeft ![.proj 1], .proj 0,
      .comp unpairRight ![.proj 1] ] ]

/-- Inputs are parameter, list code, initial accumulator. -/
def paramFold (h : Program 3) : Program 3 :=
  .comp unpairRight ![
    .comp (foldInto (paramFoldStep h)) ![.proj 1, .comp squarePair ![.proj 0, .proj 2] ] ]

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem paramFoldStep_value (h : Program 3) (p a z : M) :
    (paramFoldStep h).value ![a, squarePair.value ![p, z] ] =
      squarePair.value ![p, h.value ![p, a, z] ] := by
  simp only [paramFoldStep, Program.value_comp_two, Program.value_comp_one,
    Program.value_comp_three, Program.value_proj, Matrix.cons_val_zero,
    Matrix.cons_val_one, unpairLeft_pair_value, unpairRight_pair_value]

theorem paramFold_value (h : Program 3) (p c z : M) :
    (paramFold h).value ![p, c, z] =
      unpairRight.value ![(foldInto (paramFoldStep h)).value ![c, squarePair.value ![p, z] ] ] := by
  simp only [paramFold, Program.value_comp_one, Program.value_comp_two,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem paramFold_parameter_value (h : Program 3) (c p z : M) :
    unpairLeft.value ![(foldInto (paramFoldStep h)).value ![c, squarePair.value ![p, z] ] ] = p := by
  have hall : ∀ c : M, ∀ p z,
      unpairLeft.value ![(foldInto (paramFoldStep h)).value ![c, squarePair.value ![p, z] ] ] = p := by
    apply definable_strong_induction
      (fun c => ∀ p z,
        unpairLeft.value ![(foldInto (paramFoldStep h)).value ![c, squarePair.value ![p, z] ] ] = p)
    · change DPred (fun v : Fin 1 → M => ∀ p z,
        unpairLeft.value ![(foldInto (paramFoldStep h)).value ![v 0, squarePair.value ![p, z] ] ] = p)
      pa_definable
    · intro c ih p z
      by_cases hc : c = zeroValue M
      · subst c
        rw [foldInto_zero_value, unpairLeft_pair_value]
      · rw [← cons_head_tail_value c hc, foldInto_cons_value, paramFoldStep_value]
        exact ih _ (tail_smaller_value c hc) p _
  exact hall c p z

theorem paramFold_raw_value (h : Program 3) (c p z : M) :
    (foldInto (paramFoldStep h)).value ![c, squarePair.value ![p, z] ] =
      squarePair.value ![p, (paramFold h).value ![p, c, z] ] := by
  rw [paramFold_value]
  have he := pair_unpair_value ((foldInto (paramFoldStep h)).value ![c, squarePair.value ![p, z] ])
  rw [paramFold_parameter_value] at he
  exact he.symm

theorem paramFold_zero_value (h : Program 3) (p z : M) :
    (paramFold h).value ![p, zeroValue M, z] = z := by
  rw [paramFold_value, foldInto_zero_value, unpairRight_pair_value]

theorem paramFold_cons_value (h : Program 3) (p a c z : M) :
    (paramFold h).value ![p, listCons.value ![a, c], z] =
      (paramFold h).value ![p, c, h.value ![p, a, z] ] := by
  rw [paramFold_value, foldInto_cons_value, paramFoldStep_value, paramFold_value]

end Internal
end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms
