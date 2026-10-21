import Lemmatheca.PaListsAndSyntax.PAProofPairAlgebra

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Explicit bounded-search programs for the corpus's square pairing and its
actual list head/tail operations. Model identities are additional proof targets,
not inferred from equality on ordinary natural numbers. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u

def boundedMax {n : ℕ} (test : Program (n + 1)) : Program (n + 1) :=
  .prec (constant 0)
    (.comp select ![
      .comp test (Fin.snoc (fun i : Fin n => Program.proj (i.castAdd 2))
        (.proj (Fin.last n).castSucc)),
      .proj (Fin.last n).castSucc,
      .proj (Fin.last (n + 1))])

def leq : Program 2 := .comp zeroTest ![.comp subtraction ![.proj 0, .proj 1] ]
def squareTest : Program 2 :=
  .comp leq ![.comp multiplication ![.proj 1, .proj 1], .proj 0]

def squareRoot : Program 1 :=
  .comp (boundedMax squareTest) ![.proj 0, .comp .succ ![.proj 0] ]

def squareRemainder : Program 1 :=
  .comp subtraction ![.proj 0, .comp multiplication ![squareRoot, squareRoot] ]

def unpairLeft : Program 1 :=
  .comp select ![.comp less ![squareRemainder, squareRoot], squareRemainder, squareRoot]

def unpairRight : Program 1 :=
  .comp select ![.comp less ![squareRemainder, squareRoot], squareRoot,
    .comp subtraction ![squareRemainder, squareRoot] ]

def listHead : Program 1 :=
  .comp select ![.proj 0, .comp unpairLeft ![.comp predecessor ![.proj 0] ], constant 0]

def listTail : Program 1 :=
  .comp select ![.proj 0, .comp unpairRight ![.comp predecessor ![.proj 0] ], constant 0]

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance proofProgramsPairingLocalInstance1 : DecidableEq M := Classical.decEq M
local instance proofProgramsPairingLocalInstance2 (P : Prop) : Decidable P := Classical.propDecidable P

theorem boundedMax_zero_value {n : ℕ} (test : Program (n + 1)) (x : Fin n → M) :
    (boundedMax test).value (Fin.snoc x (zeroValue M)) = zeroValue M := by
  rw [boundedMax, Program.value_rec_zero, constant_value, numeral_value_zero]

theorem boundedMax_successor_value {n : ℕ} (test : Program (n + 1))
    (x : Fin n → M) (k : M) :
    (boundedMax test).value (Fin.snoc x (succValue M k)) =
      if test.value (Fin.snoc x k) = zeroValue M then
        (boundedMax test).value (Fin.snoc x k) else k := by
  have ht (u : M) :
      (Program.comp test (Fin.snoc (fun i : Fin n => Program.proj (i.castAdd 2))
        (.proj (Fin.last n).castSucc))).value (Fin.snoc (Fin.snoc x k) u) =
        test.value (Fin.snoc x k) := by
    rw [Program.value_comp]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Program.value_proj, Fin.snoc_castSucc]
    · rw [Fin.snoc_castSucc, Program.value_proj, Fin.snoc_castSucc]
      change (Fin.snoc (Fin.snoc x k) u : Fin (n + 2) → M) i.castSucc.castSucc = x i
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  change (Program.prec _ _).value _ = _
  rw [Program.value_rec_succ, Program.value_comp_three, select_value, ht]
  simp only [Program.value_proj, Fin.snoc_castSucc, Fin.snoc_last]
  rfl

theorem leq_value (a b : M) :
    leq.value ![a, b] = if leValue M a b then numeralValue M 1 else zeroValue M := by
  simp only [leq, Program.value_comp_one, Program.value_comp_two,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, zeroTest_value]
  simp only [subtraction_zero_iff]

theorem squareTest_value (c i : M) :
    squareTest.value ![c, i] =
      if leValue M (mulValue M i i) c then numeralValue M 1 else zeroValue M := by
  simp only [squareTest, Program.value_comp_two, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, multiplication_value, leq_value]

theorem squarePair_value (a b : M) :
    squarePair.value ![a, b] =
      if leValue M (succValue M a) b then addValue M (mulValue M b b) a
      else addValue M (addValue M (mulValue M a a) a) b := by
  simp only [squarePair, Program.value_comp_three, Program.value_comp_two,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, multiplication_value,
    addition_value, less_value, select_value]
  by_cases h : leValue M (succValue M a) b
  · simp only [h, ↓reduceIte, numeral_value_succ, numeral_value_zero,
      successor_ne_zero]
  · simp only [h, ↓reduceIte]

theorem listCons_value (a b : M) :
    listCons.value ![a, b] = succValue M (squarePair.value ![a, b]) := by
  rw [listCons, Program.value_comp, Program.value_succ]

def RootBounds (c s : M) : Prop :=
  leValue M (mulValue M s s) c ∧
    ¬ leValue M (mulValue M (succValue M s) (succValue M s)) c

theorem root_exists_model (c : M) : ∃ s : M, RootBounds c s := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have hg (a : M) : a * a < succValue M a * succValue M a :=
    mul_self_lt_mul_self (zero_le_value a)
      ((successor_le_iff_lt a (succValue M a)).mp (le_refl_value _))
  apply definable_induction (fun d => ∃ s : M, RootBounds d s)
  · change DPred (fun v : Fin 1 → M => ∃ s : M,
      leValue M (mulValue M s s) (v 0) ∧
        ¬leValue M (mulValue M (succValue M s) (succValue M s)) (v 0))
    pa_definable
  · refine ⟨zeroValue M, ?_, ?_⟩
    · simpa only [mul_zero_value] using le_refl_value (zeroValue M)
    · have h := hg (zeroValue M)
      change (0 : M) * 0 < _ at h
      rw [mul_zero] at h
      exact not_le.mpr h
  · intro d hd
    obtain ⟨s, hs, hsu⟩ := hd
    have hu : d < succValue M s * succValue M s := lt_of_not_ge hsu
    have hdu : succValue M d ≤ succValue M s * succValue M s :=
      (successor_le_iff_lt _ _).mpr hu
    by_cases he : succValue M d = succValue M s * succValue M s
    · refine ⟨succValue M s, ?_, ?_⟩
      · change succValue M s * succValue M s ≤ succValue M d
        exact le_of_eq he.symm
      exact not_le.mpr (he ▸ hg (succValue M s))
    · refine ⟨s, ?_, not_le.mpr (lt_of_le_of_ne hdu he)⟩
      exact le_trans_value hs (le_successor_value d)

theorem root_bound_model {c s : M} (hs : RootBounds c s) : leValue M s c := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  by_cases hz : s = zeroValue M
  · exact hz ▸ zero_le_value c
  · have hp : zeroValue M < s := lt_of_le_of_ne (zero_le_value s) (Ne.symm hz)
    have h1 : (1 : M) ≤ s := (successor_le_iff_lt (zeroValue M) s).mpr hp
    have hsq : s ≤ s * s := by
      have hm := mul_le_mul_value h1 s
      change s * (1 : M) ≤ s * s at hm
      simpa only [mul_one] using hm
    exact le_trans hsq hs.1

theorem root_test_model {c s : M} (hs : RootBounds c s) (i : M) :
    leValue M (mulValue M i i) c ↔ leValue M i s := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  constructor
  · intro hi
    by_contra hn
    have hlt : s < i := by exact lt_of_not_ge hn
    have hsi : succValue M s ≤ i := (successor_le_iff_lt s i).mpr hlt
    exact hs.2 (le_trans (mul_self_le_mul_self (zero_le_value _) hsi) hi)
  · intro hi
    have hsq : i * i ≤ s * s := mul_self_le_mul_self (zero_le_value _) hi
    exact le_trans hsq hs.1

theorem boundedMax_root_value {c s : M} (hs : RootBounds c s) (b : M) :
    (leValue M b s →
      (boundedMax squareTest).value ![c, b] = predecessor.value ![b]) ∧
    (leValue M (succValue M s) b →
      (boundedMax squareTest).value ![c, b] = s) := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have hsnoc (d : M) : Fin.snoc ![c] d = ![c, d] := by
    ext i
    fin_cases i <;> simp
  have hz1 : numeralValue M 1 ≠ zeroValue M := by
    rw [numeral_value_succ, numeral_value_zero]
    exact successor_ne_zero _
  have hall : ∀ b : M,
      (leValue M b s →
        (boundedMax squareTest).value ![c, b] = predecessor.value ![b]) ∧
      (leValue M (succValue M s) b →
        (boundedMax squareTest).value ![c, b] = s) := by
    apply definable_induction
    · change DPred (fun v : Fin 1 → M =>
        (leValue M (v 0) s →
          (boundedMax squareTest).value ![c, v 0] = predecessor.value ![v 0]) ∧
        (leValue M (succValue M s) (v 0) →
          (boundedMax squareTest).value ![c, v 0] = s))
      pa_definable
    · constructor
      · intro _
        rw [show ![c, zeroValue M] = Fin.snoc ![c] (zeroValue M) from by ext i; fin_cases i <;> simp,
          boundedMax_zero_value, predecessor_zero]
      · intro h
        have hh : s < zeroValue M := (successor_le_iff_lt _ _).mp h
        exact False.elim ((not_lt_of_ge (zero_le_value s)) hh)
    · intro k hk
      have heq : (boundedMax squareTest).value ![c, succValue M k] =
          if squareTest.value ![c, k] = zeroValue M then
            (boundedMax squareTest).value ![c, k] else k :=
        by
          simpa only [hsnoc] using boundedMax_successor_value squareTest ![c] k
      rw [squareTest_value] at heq
      by_cases hks : leValue M k s
      · have htest := (root_test_model hs k).mpr hks
        simp only [htest, ↓reduceIte, hz1] at heq
        constructor
        · intro _
          rw [heq, predecessor_successor]
        · intro h
          have hsk : s ≤ k := by
            by_contra hn
            have hlt : k < s := lt_of_not_ge hn
            have hstep : succValue M k ≤ s := (successor_le_iff_lt _ _).mpr hlt
            have hbad := le_trans_value h hstep
            exact ((successor_le_iff_lt s s).mp hbad).2 (le_refl_value _)
          exact heq.trans (le_antisymm hks hsk)
      · have htest : ¬ leValue M (mulValue M k k) c :=
          fun h => hks ((root_test_model hs k).mp h)
        simp only [htest, ↓reduceIte] at heq
        have hsk : leValue M (succValue M s) k :=
          (successor_le_iff_lt s k).mpr (by
            have hh : s < k := lt_of_not_ge hks
            exact hh)
        have hvalue := hk.2 hsk
        constructor
        · intro h
          exact False.elim (hks (le_trans_value (le_successor_value k) h))
        · intro _
          exact heq.trans hvalue
  exact hall b

theorem squareRoot_bounds (c : M) : RootBounds c (squareRoot.value ![c]) := by
  obtain ⟨s, hs⟩ := root_exists_model c
  have hb : leValue M (succValue M s) (succValue M c) := by
    have hb := root_bound_model hs
    exact (successor_le_iff_lt s (succValue M c)).mpr
      ⟨le_trans_value hb (le_successor_value c), fun hn =>
        ((successor_le_iff_lt c c).mp (le_trans_value hn hb)).2 (le_refl_value _)⟩
  have hv := (boundedMax_root_value hs (succValue M c)).2 hb
  have he : squareRoot.value ![c] = s := by
    simpa only [squareRoot, Program.value_comp_two, Program.value_comp_one,
      Program.value_proj, Program.value_succ, Matrix.cons_val_zero] using hv
  exact he.symm ▸ hs

theorem squareRoot_unique {c s : M} (hs : RootBounds c s) :
    squareRoot.value ![c] = s := by
  exact le_antisymm_value
    ((root_test_model hs _).mp (squareRoot_bounds c).1)
    ((root_test_model (squareRoot_bounds c) _).mp hs.1)

theorem unpairLeft_value (c : M) :
    unpairLeft.value ![c] =
      if leValue M (succValue M (subtraction.value ![c,
        mulValue M (squareRoot.value ![c]) (squareRoot.value ![c]) ]))
          (squareRoot.value ![c]) then
        subtraction.value ![c, mulValue M (squareRoot.value ![c]) (squareRoot.value ![c]) ]
      else squareRoot.value ![c] := by
  simp only [unpairLeft, squareRemainder, Program.value_comp_three,
    Program.value_comp_two, Program.value_proj, Matrix.cons_val_zero,
    multiplication_value, less_value, select_value]
  split_ifs <;> simp_all [numeral_value_succ, numeral_value_zero, successor_ne_zero]

theorem unpairRight_value (c : M) :
    unpairRight.value ![c] =
      if leValue M (succValue M (subtraction.value ![c,
        mulValue M (squareRoot.value ![c]) (squareRoot.value ![c]) ]))
          (squareRoot.value ![c]) then squareRoot.value ![c]
      else subtraction.value ![subtraction.value ![c,
        mulValue M (squareRoot.value ![c]) (squareRoot.value ![c]) ],
          squareRoot.value ![c] ] := by
  simp only [unpairRight, squareRemainder, Program.value_comp_three,
    Program.value_comp_two, Program.value_proj, Matrix.cons_val_zero,
    multiplication_value, less_value, select_value]
  split_ifs <;> simp_all [numeral_value_succ, numeral_value_zero, successor_ne_zero]

theorem unpairLeft_pair_value (a b : M) :
    unpairLeft.value ![squarePair.value ![a, b] ] = a := by
  have hp : squarePair.value ![a, b] = squarePairModel a b := squarePair_value a b
  rw [hp, unpairLeft_value]
  exact (unpairModel_pair a b _ (squareRoot_bounds (squarePairModel a b))).1

theorem unpairRight_pair_value (a b : M) :
    unpairRight.value ![squarePair.value ![a, b] ] = b := by
  have hp : squarePair.value ![a, b] = squarePairModel a b := squarePair_value a b
  rw [hp, unpairRight_value]
  exact (unpairModel_pair a b _ (squareRoot_bounds (squarePairModel a b))).2

theorem pair_unpair_value (c : M) :
    squarePair.value ![unpairLeft.value ![c], unpairRight.value ![c] ] = c := by
  rw [squarePair_value, unpairLeft_value, unpairRight_value]
  exact squarePairModel_unpair c _ (squareRoot_bounds c)

theorem head_zero_value : listHead.value ![zeroValue M] = zeroValue M := by
  simp only [listHead, Program.value_comp_three, Program.value_comp_one,
    Program.value_proj, Matrix.cons_val_zero, select_value, constant_value,
    numeral_value_zero, ↓reduceIte]

theorem tail_zero_value : listTail.value ![zeroValue M] = zeroValue M := by
  simp only [listTail, Program.value_comp_three, Program.value_comp_one,
    Program.value_proj, Matrix.cons_val_zero, select_value, constant_value,
    numeral_value_zero, ↓reduceIte]

theorem head_cons_value (a c : M) : listHead.value ![listCons.value ![a, c] ] = a := by
  simp only [listHead, Program.value_comp_three, Program.value_comp_one,
    Program.value_proj, Matrix.cons_val_zero, select_value, listCons_value,
    successor_ne_zero, ↓reduceIte, predecessor_successor, unpairLeft_pair_value]

theorem tail_cons_value (a c : M) : listTail.value ![listCons.value ![a, c] ] = c := by
  simp only [listTail, Program.value_comp_three, Program.value_comp_one,
    Program.value_proj, Matrix.cons_val_zero, select_value, listCons_value,
    successor_ne_zero, ↓reduceIte, predecessor_successor, unpairRight_pair_value]

theorem cons_head_tail_value (c : M) (hc : c ≠ zeroValue M) :
    listCons.value ![listHead.value ![c], listTail.value ![c] ] = c := by
  obtain ⟨d, rfl⟩ := PAComputations.predecessor c hc
  simp only [listHead, listTail, Program.value_comp_three, Program.value_comp_one,
    Program.value_proj, Matrix.cons_val_zero, select_value, successor_ne_zero,
    ↓reduceIte, predecessor_successor, listCons_value, pair_unpair_value]

theorem tail_smaller_value (c : M) (hc : c ≠ zeroValue M) :
    leValue M (succValue M (listTail.value ![c])) c := by
  obtain ⟨d, rfl⟩ := PAComputations.predecessor c hc
  simp only [listTail, Program.value_comp_three, Program.value_comp_one,
    Program.value_proj, Matrix.cons_val_zero, select_value, successor_ne_zero,
    ↓reduceIte, predecessor_successor]
  have hb := squarePairModel_right_le (unpairLeft.value ![d]) (unpairRight.value ![d])
  have hp : squarePairModel (unpairLeft.value ![d]) (unpairRight.value ![d]) = d := by
    change (if leValue M (succValue M (unpairLeft.value ![d])) (unpairRight.value ![d]) then _ else _) = d
    rw [← squarePair_value]
    exact pair_unpair_value d
  rw [hp] at hb
  obtain ⟨k, hk⟩ := hb
  exact ⟨k, by rw [add_successor_value, hk]⟩

end Internal

theorem leValue_nat (a b : ℕ) : leValue ℕ a b ↔ a ≤ b := by
  change (∃ d : ℕ, d + a = b) ↔ a ≤ b
  constructor
  · rintro ⟨d, rfl⟩
    omega
  · intro h
    exact ⟨b - a, Nat.sub_add_cancel h⟩

theorem squareRoot_eval (x : Fin 1 → ℕ) : squareRoot.eval x = Nat.sqrt (x 0) := by
  let : ℕ ⊨ PA := nat_models_PA
  have hv : x = ![x 0] := by ext i; fin_cases i; rfl
  rw [hv]
  have h := squareRoot_bounds (M := ℕ) (x 0)
  unfold RootBounds at h
  rw [Program.value_nat] at h
  change leValue ℕ (squareRoot.eval ![x 0] * squareRoot.eval ![x 0]) (x 0) ∧
    ¬leValue ℕ ((squareRoot.eval ![x 0] + 1) * (squareRoot.eval ![x 0] + 1)) (x 0) at h
  simp only [leValue_nat] at h
  exact Nat.eq_sqrt.mpr ⟨h.1, Nat.lt_of_not_ge h.2⟩

theorem unpairLeft_eval (x : Fin 1 → ℕ) : unpairLeft.eval x = (Nat.unpair (x 0)).1 := by
  classical
  let : ℕ ⊨ PA := nat_models_PA
  have hv : x = ![x 0] := by ext i; fin_cases i; rfl
  rw [hv]
  have h := unpairLeft_value (M := ℕ) (x 0)
  simp only [Program.value_nat, subtraction_eval, squareRoot_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  change unpairLeft.eval ![x 0] =
    if leValue ℕ ((x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0)) + 1) (Nat.sqrt (x 0)) then
      x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0) else Nat.sqrt (x 0) at h
  simp only [leValue_nat, Nat.add_one_le_iff] at h
  simp only [Nat.unpair, Matrix.cons_val_zero]
  split_ifs with hh <;> simpa only [hh, ↓reduceIte] using h

theorem unpairRight_eval (x : Fin 1 → ℕ) : unpairRight.eval x = (Nat.unpair (x 0)).2 := by
  classical
  let : ℕ ⊨ PA := nat_models_PA
  have hv : x = ![x 0] := by ext i; fin_cases i; rfl
  rw [hv]
  have h := unpairRight_value (M := ℕ) (x 0)
  simp only [Program.value_nat, subtraction_eval, squareRoot_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  change unpairRight.eval ![x 0] =
    if leValue ℕ ((x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0)) + 1) (Nat.sqrt (x 0)) then Nat.sqrt (x 0) else
      x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0) - Nat.sqrt (x 0) at h
  simp only [leValue_nat, Nat.add_one_le_iff] at h
  simp only [Nat.unpair, Matrix.cons_val_zero]
  split_ifs with hh <;> simpa only [hh, ↓reduceIte] using h

theorem head_eval (x : Fin 1 → ℕ) : listHead.eval x = FiniteSequenceCoding.head (x 0) := by
  simp only [listHead, Program.eval, select_eval, predecessor_eval,
    unpairLeft_eval, constant_eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rfl

theorem tail_eval (x : Fin 1 → ℕ) : listTail.eval x = FiniteSequenceCoding.tail (x 0) := by
  simp only [listTail, Program.eval, select_eval, predecessor_eval,
    unpairRight_eval, constant_eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rfl

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms
