import Lemmatheca.PaListsAndSyntax.PAListFold

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Concrete list reversal and append programs, with their constructor laws in
every PA model.  The fusion argument uses definable strong induction on codes;
it does not identify nonstandard codes with external finite lists. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u

def listReverse : Program 1 :=
  .comp (foldInto listCons) ![.proj 0, constant 0]

def listAppend : Program 2 :=
  .comp (foldInto listCons) ![.comp listReverse ![.proj 0], .proj 1]

def lengthStep : Program 2 := .comp .succ ![.proj 1]

def listLength : Program 1 :=
  .comp (foldInto lengthStep) ![.proj 0, constant 0]

def listTails : Program 2 :=
  .prec (.proj 0) (.comp listTail ![.proj 2])

def listEntry : Program 2 := .comp listHead ![listTails]

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem listReverse_value (c : M) :
    listReverse.value ![c] = (foldInto listCons).value ![c, zeroValue M] := by
  simp only [listReverse, Program.value_comp_two, Program.value_proj,
    Matrix.cons_val_zero, constant_value, numeral_value_zero]

theorem listAppend_value (c d : M) :
    listAppend.value ![c, d] =
      (foldInto listCons).value ![(foldInto listCons).value ![c, zeroValue M], d] := by
  simp only [listAppend, Program.value_comp_two, Program.value_comp_one,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, listReverse_value]

/-- The accumulator fusion law, including at internally finite nonstandard
codes.  The induction predicate is arithmetic-definable. -/
theorem foldCons_fusion_value (c x z : M) :
    (foldInto listCons).value ![(foldInto listCons).value ![c, x], z] =
      (foldInto listCons).value ![x,
        (foldInto listCons).value ![(foldInto listCons).value ![c, zeroValue M], z] ] := by
  let R : M → M → M := fun c z => (foldInto listCons).value ![c, z]
  let C : M → M → M := fun a c => listCons.value ![a, c]
  have hz (z : M) : R (zeroValue M) z = z := foldInto_zero_value listCons z
  have hs (a c z : M) : R (C a c) z = R c (C a z) :=
    foldInto_cons_value listCons a c z
  have step (a t : M)
      (ht : ∀ x z, R (R t x) z = R x (R (R t (zeroValue M)) z)) :
      ∀ x z, R (R (C a t) x) z = R x (R (R (C a t) (zeroValue M)) z) := by
    intro x z
    have hrev : R (R (C a t) (zeroValue M)) z = C a (R (R t (zeroValue M)) z) := by
      rw [hs, ht, hs, hz]
    rw [hs, ht, hs, hrev]
  have hall : ∀ c, ∀ x z, R (R c x) z = R x (R (R c (zeroValue M)) z) := by
    apply definable_strong_induction
      (fun c => ∀ x z, R (R c x) z = R x (R (R c (zeroValue M)) z))
    · change DPred (fun v : Fin 1 → M => ∀ x z,
        (foldInto listCons).value ![(foldInto listCons).value ![v 0, x], z] =
          (foldInto listCons).value ![x,
            (foldInto listCons).value ![(foldInto listCons).value ![v 0, zeroValue M], z] ])
      pa_definable
    · intro c ih
      by_cases hc : c = zeroValue M
      · subst c
        intro x z
        simp only [hz]
      · have ht := ih (listTail.value ![c]) (tail_smaller_value c hc)
        have hd : C (listHead.value ![c]) (listTail.value ![c]) = c :=
          cons_head_tail_value c hc
        simpa only [hd] using step (listHead.value ![c]) (listTail.value ![c]) ht
  exact hall c x z

theorem listAppend_zero_value (d : M) :
    listAppend.value ![zeroValue M, d] = d := by
  rw [listAppend_value, foldInto_zero_value, foldInto_zero_value]

theorem listAppend_cons_value (a c d : M) :
    listAppend.value ![listCons.value ![a, c], d] =
      listCons.value ![a, listAppend.value ![c, d] ] := by
  rw [listAppend_value, foldInto_cons_value, foldCons_fusion_value,
    foldInto_cons_value, foldInto_zero_value, listAppend_value]

theorem lengthStep_value (a z : M) :
    lengthStep.value ![a, z] = succValue M z := by
  simp only [lengthStep, Program.value_comp_one, Program.value_proj,
    Matrix.cons_val_one, Program.value_succ, Matrix.cons_val_zero]

theorem foldLength_successor_value (c z : M) :
    (foldInto lengthStep).value ![c, succValue M z] =
      succValue M ((foldInto lengthStep).value ![c, z]) := by
  let F : M → M → M := fun c z => (foldInto lengthStep).value ![c, z]
  have hz (z : M) : F (zeroValue M) z = z := foldInto_zero_value lengthStep z
  have hs (a c z : M) : F (listCons.value ![a, c]) z = F c (succValue M z) := by
    dsimp only [F]
    rw [foldInto_cons_value, lengthStep_value]
  have hall : ∀ c, ∀ z, F c (succValue M z) = succValue M (F c z) := by
    apply definable_strong_induction
      (fun c => ∀ z, F c (succValue M z) = succValue M (F c z))
    · change DPred (fun v : Fin 1 → M => ∀ z,
        (foldInto lengthStep).value ![v 0, succValue M z] =
          succValue M ((foldInto lengthStep).value ![v 0, z]))
      pa_definable
    · intro c ih z
      by_cases hc : c = zeroValue M
      · subst c
        rw [hz, hz]
      · have ht := ih (listTail.value ![c]) (tail_smaller_value c hc)
        have hd := cons_head_tail_value c hc
        have hstep :
            F (listCons.value ![listHead.value ![c], listTail.value ![c] ]) (succValue M z) =
              succValue M (F (listCons.value ![listHead.value ![c], listTail.value ![c] ]) z) := by
          rw [hs, ht, hs]
        simpa only [hd] using hstep
  exact hall c z

theorem listLength_value (c : M) :
    listLength.value ![c] = (foldInto lengthStep).value ![c, zeroValue M] := by
  simp only [listLength, Program.value_comp_two, Program.value_proj,
    Matrix.cons_val_zero, constant_value, numeral_value_zero]

theorem listLength_zero_value : listLength.value ![zeroValue M] = zeroValue M := by
  rw [listLength_value, foldInto_zero_value]

theorem listLength_cons_value (a c : M) :
    listLength.value ![listCons.value ![a, c] ] = succValue M (listLength.value ![c]) := by
  rw [listLength_value, foldInto_cons_value, lengthStep_value,
    foldLength_successor_value, listLength_value]

theorem listTails_zero_value (c : M) :
    listTails.value ![c, zeroValue M] = c := by
  have h := Program.value_rec_zero (Program.proj (0 : Fin 1))
    (Program.comp listTail ![Program.proj (2 : Fin 3)]) ![c]
  have hv : Fin.snoc (![c] : Fin 1 → M) (zeroValue M) = ![c, zeroValue M] := by
    funext i
    fin_cases i <;> rfl
  simpa only [listTails, hv, Program.value_proj, Matrix.cons_val_zero] using h

theorem listTails_successor_value (c i : M) :
    listTails.value ![c, succValue M i] = listTail.value ![listTails.value ![c, i] ] := by
  have h := Program.value_rec_succ (Program.proj (0 : Fin 1))
    (Program.comp listTail ![Program.proj (2 : Fin 3)]) ![c] i
  have hv (k : M) : Fin.snoc (![c] : Fin 1 → M) k = ![c, k] := by
    funext j
    fin_cases j <;> rfl
  have hl (a b d : M) :
      Fin.snoc (α := fun _ : Fin 3 => M) (![a, b] : Fin 2 → M) d (2 : Fin 3) = d := by
    simp [Fin.snoc]
  simpa only [listTails, hv, Program.value_comp_one, Program.value_proj, hl]
    using h

theorem listTails_cons_successor_value (a c i : M) :
    listTails.value ![listCons.value ![a, c], succValue M i] =
      listTails.value ![c, i] := by
  apply definable_induction
    (fun i => listTails.value ![listCons.value ![a, c], succValue M i] =
      listTails.value ![c, i])
  · change DPred (fun v : Fin 1 → M =>
      listTails.value ![listCons.value ![a, c], succValue M (v 0)] =
        listTails.value ![c, v 0])
    pa_definable
  · rw [listTails_successor_value, listTails_zero_value,
      tail_cons_value, listTails_zero_value]
  · intro i hi
    rw [listTails_successor_value, hi, listTails_successor_value]

theorem listEntry_value (c i : M) :
    listEntry.value ![c, i] = listHead.value ![listTails.value ![c, i] ] := by
  rw [listEntry, Program.value_comp_one]

theorem listEntry_zero_value (c : M) :
    listEntry.value ![c, zeroValue M] = listHead.value ![c] := by
  rw [listEntry_value, listTails_zero_value]

theorem listEntry_cons_zero_value (a c : M) :
    listEntry.value ![listCons.value ![a, c], zeroValue M] = a := by
  rw [listEntry_zero_value, head_cons_value]

theorem listEntry_cons_successor_value (a c i : M) :
    listEntry.value ![listCons.value ![a, c], succValue M i] =
      listEntry.value ![c, i] := by
  rw [listEntry_value, listTails_cons_successor_value, listEntry_value]

end Internal

local instance listProgramsLocalInstance1 : ℕ ⊨ PA := nat_models_PA

theorem value_nat_eq_eval {n : ℕ} (p : Program n) (x : Fin n → ℕ) :
    p.value x = p.eval x := by
  simpa only [numeral_value_nat] using p.value_numerals (M := ℕ) x

theorem listAppend_eval_zero (d : ℕ) : listAppend.eval ![0, d] = d := by
  have h := listAppend_zero_value (M := ℕ) d
  change listAppend.value ![0, d] = d at h
  simpa only [value_nat_eq_eval] using h

theorem listAppend_eval_cons (a c d : ℕ) :
    listAppend.eval ![FiniteSequenceCoding.cons a c, d] =
      FiniteSequenceCoding.cons a (listAppend.eval ![c, d]) := by
  simpa only [value_nat_eq_eval, listCons_eval, Matrix.cons_val_zero,
    Matrix.cons_val_one] using listAppend_cons_value (M := ℕ) a c d

theorem listAppend_eval_code (s : List ℕ) (d : ℕ) :
    listAppend.eval ![FiniteSequenceCoding.code s, d] =
      FiniteSequenceCoding.code (s ++ FiniteSequenceCoding.decode d) := by
  induction s with
  | nil =>
      change listAppend.eval ![0, d] = FiniteSequenceCoding.code (FiniteSequenceCoding.decode d)
      rw [FiniteSequenceCoding.code_decode]
      exact listAppend_eval_zero d
  | cons a s ih =>
      rw [FiniteSequenceCoding.code_cons, listAppend_eval_cons, ih,
        List.cons_append, FiniteSequenceCoding.code_cons]

theorem listAppend_eval (x : Fin 2 → ℕ) :
    listAppend.eval x = FiniteSequenceCoding.append (x 0) (x 1) := by
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hx, ← FiniteSequenceCoding.code_decode (x 0), listAppend_eval_code]
  rfl

theorem listLength_eval_zero : listLength.eval ![0] = 0 := by
  have h := listLength_zero_value (M := ℕ)
  change listLength.value ![0] = 0 at h
  simpa only [value_nat_eq_eval] using h

theorem listLength_eval_cons (a c : ℕ) :
    listLength.eval ![FiniteSequenceCoding.cons a c] = listLength.eval ![c] + 1 := by
  have h := listLength_cons_value (M := ℕ) a c
  change listLength.value ![listCons.value ![a, c] ] = listLength.value ![c] + 1 at h
  simpa only [value_nat_eq_eval, listCons_eval, Matrix.cons_val_zero,
    Matrix.cons_val_one] using h

theorem listLength_eval_code (s : List ℕ) :
    listLength.eval ![FiniteSequenceCoding.code s] = s.length := by
  induction s with
  | nil => exact listLength_eval_zero
  | cons a s ih =>
      rw [FiniteSequenceCoding.code_cons, listLength_eval_cons, ih, List.length_cons]

theorem listLength_eval (x : Fin 1 → ℕ) :
    listLength.eval x = FiniteSequenceCoding.length (x 0) := by
  have hx : x = ![x 0] := by
    funext i
    fin_cases i
    rfl
  have h := listLength_eval_code (FiniteSequenceCoding.decode (x 0))
  rw [FiniteSequenceCoding.code_decode] at h
  simpa only [← hx, FiniteSequenceCoding.length] using h

theorem listTails_eval_zero (c : ℕ) : listTails.eval ![c, 0] = c := by
  have h := listTails_zero_value (M := ℕ) c
  change listTails.value ![c, 0] = c at h
  simpa only [value_nat_eq_eval] using h

theorem listTails_eval_successor (c i : ℕ) :
    listTails.eval ![c, i + 1] = FiniteSequenceCoding.tail (listTails.eval ![c, i]) := by
  have h := listTails_successor_value (M := ℕ) c i
  change listTails.value ![c, i + 1] = listTail.value ![listTails.value ![c, i] ] at h
  simpa only [value_nat_eq_eval, tail_eval, Matrix.cons_val_zero] using h

theorem listTails_eval_pair (c i : ℕ) :
    listTails.eval ![c, i] = FiniteSequenceCoding.tails c i := by
  induction i with
  | zero => exact listTails_eval_zero c
  | succ i ih =>
      rw [listTails_eval_successor, ih]
      simp only [FiniteSequenceCoding.tails, Function.iterate_succ_apply']

theorem listTails_eval (x : Fin 2 → ℕ) :
    listTails.eval x = FiniteSequenceCoding.tails (x 0) (x 1) := by
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hx, listTails_eval_pair]

theorem listEntry_eval (x : Fin 2 → ℕ) :
    listEntry.eval x = FiniteSequenceCoding.entry (x 0) (x 1) := by
  have h := listEntry_value (M := ℕ) (x 0) (x 1)
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  simpa only [value_nat_eq_eval, head_eval, Matrix.cons_val_zero,
    listTails_eval, Matrix.cons_val_one, ← FiniteSequenceCoding.entry_eq_head,
    ← hx] using h

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms
