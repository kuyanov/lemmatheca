import Lemmatheca.MathematicalLogic.PAProofProgramsPairing

/-! A concrete primitive-recursive fold over the actual numerical list codes.
The iteration bound is the input code itself.  The proofs below take place in
arbitrary PA models; decreasing tails justify that bound internally. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u

def foldStep (h : Program 2) : Program 1 :=
  .comp select ![unpairLeft,
    .comp squarePair ![
      .comp listTail ![unpairLeft],
      .comp h ![.comp listHead ![unpairLeft], unpairRight] ],
    .proj 0]

def foldState (h : Program 2) : Program 3 :=
  .prec squarePair (.comp (foldStep h) ![.proj 3])

def foldInto (h : Program 2) : Program 2 :=
  .comp unpairRight ![.comp (foldState h) ![.proj 0, .proj 1, .proj 0] ]

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance : DecidableEq M := Classical.decEq M

@[fun_prop] theorem program_single_definable {α : Type} (p : Program 1)
    (f : (α → M) → M)
    (hf : (Set.univ : Set M).DefinableFun language f) :
    (Set.univ : Set M).DefinableFun language (fun x => p.value ![f x]) := by
  apply p.value_definable.comp
  intro i
  fin_cases i
  exact hf

@[fun_prop] theorem program_triple_definable {α : Type} (p : Program 3)
    (f g k : (α → M) → M)
    (hf : (Set.univ : Set M).DefinableFun language f)
    (hg : (Set.univ : Set M).DefinableFun language g)
    (hk : (Set.univ : Set M).DefinableFun language k) :
    (Set.univ : Set M).DefinableFun language (fun x => p.value ![f x, g x, k x]) := by
  apply p.value_definable.comp
  intro i
  fin_cases i
  · exact hf
  · exact hg
  · exact hk

theorem foldStep_pair_value (h : Program 2) (c z : M) :
    (foldStep h).value ![squarePair.value ![c, z] ] =
      if c = zeroValue M then squarePair.value ![c, z] else
        squarePair.value ![listTail.value ![c], h.value ![listHead.value ![c], z] ] := by
  simp only [foldStep, Program.value_comp_three, Program.value_comp_two,
    Program.value_comp_one, Program.value_proj, Matrix.cons_val_zero,
    unpairLeft_pair_value, unpairRight_pair_value, select_value]

theorem foldState_zero_value (h : Program 2) (c z : M) :
    (foldState h).value ![c, z, zeroValue M] = squarePair.value ![c, z] := by
  have h₀ := Program.value_rec_zero squarePair
    (Program.comp (foldStep h) ![Program.proj (3 : Fin 4)]) ![c, z]
  convert h₀ using 1
  congr 1
  funext i
  fin_cases i <;> rfl

theorem foldState_successor_value (h : Program 2) (c z k : M) :
    (foldState h).value ![c, z, succValue M k] =
      (foldStep h).value ![(foldState h).value ![c, z, k] ] := by
  have hs := Program.value_rec_succ squarePair
    (Program.comp (foldStep h) ![Program.proj (3 : Fin 4)]) ![c, z] k
  have hv (b : M) : Fin.snoc (![c, z] : Fin 2 → M) b = ![c, z, b] := by
    funext i
    fin_cases i <;> rfl
  simpa [foldState, hv, Program.value_comp_one, Program.value_proj, Fin.snoc] using hs

theorem foldInto_value (h : Program 2) (c z : M) :
    (foldInto h).value ![c, z] =
      unpairRight.value ![(foldState h).value ![c, z, c] ] := by
  simp only [foldInto, Program.value_comp_one, Program.value_comp_three,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem foldState_empty_value (h : Program 2) (z k : M) :
    (foldState h).value ![zeroValue M, z, k] = squarePair.value ![zeroValue M, z] := by
  apply definable_induction
    (fun k => (foldState h).value ![zeroValue M, z, k] =
      squarePair.value ![zeroValue M, z])
  · change DPred (fun v : Fin 1 → M =>
      (foldState h).value ![zeroValue M, z, v 0] = squarePair.value ![zeroValue M, z])
    pa_definable
  · exact foldState_zero_value h _ _
  · intro k hk
    rw [foldState_successor_value, hk, foldStep_pair_value, ite_eq_left rfl]

theorem foldState_shift_value (h : Program 2) (c z : M) (hc : c ≠ zeroValue M)
    (k : M) :
    (foldState h).value ![c, z, succValue M k] =
      (foldState h).value ![listTail.value ![c], h.value ![listHead.value ![c], z], k] := by
  apply definable_induction
    (fun k => (foldState h).value ![c, z, succValue M k] =
      (foldState h).value ![listTail.value ![c], h.value ![listHead.value ![c], z], k])
  · change DPred (fun v : Fin 1 → M =>
      (foldState h).value ![c, z, succValue M (v 0)] =
        (foldState h).value ![listTail.value ![c], h.value ![listHead.value ![c], z], v 0])
    pa_definable
  · rw [foldState_successor_value, foldState_zero_value, foldStep_pair_value,
      ite_eq_right hc, foldState_zero_value]
  · intro k hk
    rw [foldState_successor_value h c z (succValue M k), hk,
      foldState_successor_value]

theorem foldInto_zero_value (h : Program 2) (z : M) :
    (foldInto h).value ![zeroValue M, z] = z := by
  rw [foldInto_value, foldState_zero_value, unpairRight_pair_value]

theorem successor_le_successor_value_iff (a b : M) :
    leValue M (succValue M a) (succValue M b) ↔ leValue M a b := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, successor_injective ?_⟩
    rw [← add_successor_value]
    exact hd
  · rintro ⟨d, hd⟩
    exact ⟨d, by rw [add_successor_value, hd]⟩

theorem foldState_stable_value (h : Program 2) (c z k : M)
    (hck : leValue M c k) :
    (foldState h).value ![c, z, k] = (foldState h).value ![c, z, c] := by
  have hs : ∀ c : M, ∀ z k l : M, leValue M c k → leValue M c l →
      (foldState h).value ![c, z, k] = (foldState h).value ![c, z, l] := by
    apply definable_strong_induction
    · change DPred (fun v : Fin 1 → M => ∀ z k l : M,
        leValue M (v 0) k → leValue M (v 0) l →
          (foldState h).value ![v 0, z, k] = (foldState h).value ![v 0, z, l])
      pa_definable
    · intro c ih z k l hk hl
      by_cases hc : c = zeroValue M
      · rw [hc, foldState_empty_value, foldState_empty_value]
      · have hkn : k ≠ zeroValue M := by
          intro hkz
          exact hc (le_antisymm_value (hkz ▸ hk) (zero_le_value c))
        have hln : l ≠ zeroValue M := by
          intro hlz
          exact hc (le_antisymm_value (hlz ▸ hl) (zero_le_value c))
        obtain ⟨k', rfl⟩ := PAComputations.predecessor k hkn
        obtain ⟨l', rfl⟩ := PAComputations.predecessor l hln
        rw [foldState_shift_value h c z hc, foldState_shift_value h c z hc]
        exact ih (listTail.value ![c]) (tail_smaller_value c hc) _ _ _
          ((successor_le_successor_value_iff _ _).mp
            (le_trans_value (tail_smaller_value c hc) hk))
          ((successor_le_successor_value_iff _ _).mp
            (le_trans_value (tail_smaller_value c hc) hl))
  exact hs c z k c hck (le_refl_value c)

theorem foldInto_cons_value (h : Program 2) (a c z : M) :
    (foldInto h).value ![listCons.value ![a, c], z] =
      (foldInto h).value ![c, h.value ![a, z] ] := by
  have hc : listCons.value ![a, c] = succValue M (squarePair.value ![a, c]) := by
    simp only [listCons, Program.value_comp, Program.value_succ]
  have hcn : listCons.value ![a, c] ≠ zeroValue M := by
    rw [hc]
    exact successor_ne_zero _
  have hb : leValue M c (squarePair.value ![a, c]) := by
    apply (successor_le_successor_value_iff _ _).mp
    have ht := tail_smaller_value (listCons.value ![a, c]) hcn
    rwa [tail_cons_value, hc] at ht
  have hs : (foldState h).value ![listCons.value ![a, c], z, listCons.value ![a, c] ] =
      (foldState h).value ![c, h.value ![a, z], c] := by
    calc
      _ = (foldState h).value ![listCons.value ![a, c], z,
          succValue M (squarePair.value ![a, c])] := by rw [← hc]
      _ = (foldState h).value ![listTail.value ![listCons.value ![a, c] ],
          h.value ![listHead.value ![listCons.value ![a, c] ], z],
          squarePair.value ![a, c] ] := foldState_shift_value h _ _ hcn _
      _ = (foldState h).value ![c, h.value ![a, z], squarePair.value ![a, c] ] := by
        rw [head_cons_value, tail_cons_value]
      _ = _ := foldState_stable_value h _ _ _ hb
  rw [foldInto_value, hs, ← foldInto_value]

end Internal
end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms
