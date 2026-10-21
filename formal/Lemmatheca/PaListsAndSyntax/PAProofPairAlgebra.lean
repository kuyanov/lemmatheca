import Lemmatheca.PaListsAndSyntax.PAProofProgramsOrder

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Arithmetic of the exact square pairing, proved in every PA model.  These
lemmas do not obtain the internal inverse equations from standard evaluation. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance proofPairAlgebraLocalInstance1 (P : Prop) : Decidable P := Classical.propDecidable P

def squarePairModel (a b : M) : M :=
  if leValue M (succValue M a) b then addValue M (mulValue M b b) a
    else addValue M (addValue M (mulValue M a a) a) b

def squareRootBounds (c s : M) : Prop :=
  leValue M (mulValue M s s) c ∧
    ¬ leValue M (mulValue M (succValue M s) (succValue M s)) c

theorem successor_eq_add_one_model (a : M) :
    let := modelSemiring M; succValue M a = a + 1 := by
  let := modelSemiring M
  exact (add_one_value a).symm

theorem squarePairModel_left_le (a b : M) : leValue M a (squarePairModel a b) := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have ha : 0 ≤ a := zero_le_value a
  have hb : 0 ≤ b := zero_le_value b
  dsimp only [squarePairModel]
  split_ifs
  · change a ≤ b * b + a
    exact le_add_of_nonneg_left (mul_nonneg hb hb)
  · change a ≤ a * a + a + b
    exact le_trans (le_add_of_nonneg_left (mul_nonneg ha ha))
      (le_add_of_nonneg_right hb)

theorem squarePairModel_right_le (a b : M) : leValue M b (squarePairModel a b) := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have ha : 0 ≤ a := zero_le_value a
  have hb : 0 ≤ b := zero_le_value b
  dsimp only [squarePairModel]
  split_ifs with h
  · have hab : a < b := (successor_le_iff_lt a b).mp h
    have hb1 : 1 ≤ b := by
      have hne : b ≠ zeroValue M := by
        intro hz
        have hab' : a < zeroValue M := hz ▸ hab
        exact not_lt_of_ge ha hab'
      have hh := one_le_nonzero_model b hne
      rw [numeral_value_succ, numeral_value_zero] at hh
      change 1 ≤ b at hh
      exact hh
    change b ≤ b * b + a
    calc
      b = b * 1 := (mul_one b).symm
      _ ≤ b * b := mul_le_mul_of_nonneg_left hb1 hb
      _ ≤ b * b + a := le_add_of_nonneg_right ha
  · change b ≤ a * a + a + b
    exact le_add_of_nonneg_left (add_nonneg (mul_nonneg ha ha) ha)

theorem squarePairModel_root_bounds (a b : M) :
    squareRootBounds (squarePairModel a b)
      (let := modelLinearOrder M; max a b) := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have ha : 0 ≤ a := zero_le_value a
  have hb : 0 ≤ b := zero_le_value b
  by_cases h : leValue M (succValue M a) b
  · have hab : a < b := (successor_le_iff_lt a b).mp h
    rw [max_eq_right hab.le]
    dsimp only [squareRootBounds, squarePairModel]
    rw [ite_eq_left h]
    change b * b ≤ b * b + a ∧ ¬ succValue M b * succValue M b ≤ b * b + a
    rw [successor_eq_add_one_model]
    constructor
    · exact le_add_of_nonneg_right ha
    · apply not_le_of_gt
      calc
        b * b + a < b * b + b := add_lt_add_right hab _
        _ < (b + 1) * (b + 1) := by
          have hpos : 0 < b + 1 := lt_add_of_le_of_pos hb zero_lt_one
          calc
            b * b + b < (b * b + b) + (b + 1) := lt_add_of_pos_right _ hpos
            _ = (b + 1) * (b + 1) := by ring
  · have hba : b ≤ a := le_of_not_gt (fun hab => h ((successor_le_iff_lt a b).mpr hab))
    rw [max_eq_left hba]
    dsimp only [squareRootBounds, squarePairModel]
    rw [ite_eq_right h]
    change a * a ≤ a * a + a + b ∧ ¬ succValue M a * succValue M a ≤ a * a + a + b
    rw [successor_eq_add_one_model]
    constructor
    · exact le_trans (le_add_of_nonneg_right ha) (le_add_of_nonneg_right hb)
    · apply not_le_of_gt
      calc
        a * a + a + b ≤ a * a + a + a := add_le_add_right hba _
        _ < (a + 1) * (a + 1) := by
          calc
            a * a + a + a < (a * a + a + a) + 1 := lt_add_of_pos_right _ zero_lt_one
            _ = (a + 1) * (a + 1) := by ring

theorem squareRootBounds_unique (c s t : M)
    (hs : squareRootBounds c s) (ht : squareRootBounds c t) : s = t := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  apply le_antisymm
  · by_contra h
    have hst : succValue M t ≤ s := (successor_le_iff_lt t s).mpr (lt_of_not_ge h)
    apply ht.2
    exact le_trans (mul_self_le_mul_self (zero_le_value _) hst) hs.1
  · by_contra h
    have hts : succValue M s ≤ t := (successor_le_iff_lt s t).mpr (lt_of_not_ge h)
    apply hs.2
    exact le_trans (mul_self_le_mul_self (zero_le_value _) hts) ht.1

def squareRemainderModel (c s : M) : M := subtraction.value ![c, mulValue M s s]

def unpairLeftModel (c s : M) : M :=
  if leValue M (succValue M (squareRemainderModel c s)) s
    then squareRemainderModel c s else s

def unpairRightModel (c s : M) : M :=
  if leValue M (succValue M (squareRemainderModel c s)) s then s
    else subtraction.value ![squareRemainderModel c s, s]

theorem squareRemainderModel_equation (c s : M) (hs : squareRootBounds c s) :
    addValue M (squareRemainderModel c s) (mulValue M s s) = c :=
  (subtraction_spec c (mulValue M s s)).1 hs.1

theorem squareRemainderModel_le (c s : M) (hs : squareRootBounds c s) :
    leValue M (squareRemainderModel c s) (addValue M s s) := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have he := squareRemainderModel_equation c s hs
  have hupper := hs.2
  change squareRemainderModel c s + s * s = c at he
  change ¬ succValue M s * succValue M s ≤ c at hupper
  rw [successor_eq_add_one_model] at hupper
  by_contra hn
  have hgt : succValue M (s + s) ≤ squareRemainderModel c s := by
    apply (successor_le_iff_lt (s + s) _).mpr
    change s + s < squareRemainderModel c s
    exact lt_of_not_ge hn
  rw [successor_eq_add_one_model] at hgt
  apply hupper
  calc
    (s + 1) * (s + 1) = s * s + ((s + s) + 1) := by ring
    _ ≤ s * s + squareRemainderModel c s := add_le_add_right hgt _
    _ = c := (add_comm _ _).trans he

theorem squarePairModel_unpair (c s : M) (hs : squareRootBounds c s) :
    squarePairModel (unpairLeftModel c s) (unpairRightModel c s) = c := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have he := squareRemainderModel_equation c s hs
  change squareRemainderModel c s + s * s = c at he
  by_cases h : leValue M (succValue M (squareRemainderModel c s)) s
  · simp only [unpairLeftModel, unpairRightModel, h, ↓reduceIte, squarePairModel]
    change s * s + squareRemainderModel c s = c
    exact (add_comm _ _).trans he
  · have hsr : s ≤ squareRemainderModel c s :=
      le_of_not_gt (fun hr => h ((successor_le_iff_lt _ _).mpr hr))
    have hsub := (subtraction_spec (squareRemainderModel c s) s).1 hsr
    have hr := squareRemainderModel_le c s hs
    change subtraction.value ![squareRemainderModel c s, s] + s = squareRemainderModel c s at hsub
    change squareRemainderModel c s ≤ s + s at hr
    have hsmall : subtraction.value ![squareRemainderModel c s, s] ≤ s := by
      apply (add_le_add_iff_right s).mp
      rw [hsub]
      exact hr
    have hn : ¬ leValue M (succValue M s) (subtraction.value ![squareRemainderModel c s, s]) :=
      fun hh => not_lt_of_ge hsmall ((successor_le_iff_lt _ _).mp hh)
    simp only [unpairLeftModel, unpairRightModel, h, ↓reduceIte, squarePairModel]
    rw [ite_eq_right hn]
    change s * s + s + subtraction.value ![squareRemainderModel c s, s] = c
    calc
      _ = (subtraction.value ![squareRemainderModel c s, s] + s) + s * s := by ac_rfl
      _ = c := by rw [hsub]; exact he

theorem squareRemainderModel_pair_of_lt (a b : M)
    (h : leValue M (succValue M a) b) :
    squareRemainderModel (squarePairModel a b) b = a := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have hab : a < b := (successor_le_iff_lt a b).mp h
  have he := squareRemainderModel_equation (squarePairModel a b) b (by
    simpa only [max_eq_right hab.le] using
      squarePairModel_root_bounds a b)
  apply add_right_cancel (b := b * b)
  calc
    squareRemainderModel (squarePairModel a b) b + b * b = squarePairModel a b := he
    _ = b * b + a := by simp only [squarePairModel, h, ↓reduceIte]; rfl
    _ = a + b * b := add_comm _ _

theorem squareRemainderModel_pair_of_not_lt (a b : M)
    (h : ¬ leValue M (succValue M a) b) :
    squareRemainderModel (squarePairModel a b) a = addValue M a b := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have hba : b ≤ a := le_of_not_gt (fun hh => h ((successor_le_iff_lt a b).mpr hh))
  have he := squareRemainderModel_equation (squarePairModel a b) a (by
    simpa only [max_eq_left hba] using squarePairModel_root_bounds a b)
  change squareRemainderModel (squarePairModel a b) a = a + b
  apply add_right_cancel (b := a * a)
  calc
    squareRemainderModel (squarePairModel a b) a + a * a = squarePairModel a b := he
    _ = a * a + a + b := by simp only [squarePairModel, h, ↓reduceIte]; rfl
    _ = (a + b) + a * a := by ac_rfl

theorem unpairModel_pair (a b s : M) (hs : squareRootBounds (squarePairModel a b) s) :
    unpairLeftModel (squarePairModel a b) s = a ∧
      unpairRightModel (squarePairModel a b) s = b := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have hsmax := squareRootBounds_unique _ _ _ hs (squarePairModel_root_bounds a b)
  by_cases h : leValue M (succValue M a) b
  · have hab : a < b := (successor_le_iff_lt a b).mp h
    have hmax : max a b = b := max_eq_right hab.le
    rw [hmax] at hsmax
    subst s
    simp only [unpairLeftModel, unpairRightModel, squareRemainderModel_pair_of_lt a b h,
      h, ↓reduceIte, and_self]
  · have hba : b ≤ a := le_of_not_gt (fun hh => h ((successor_le_iff_lt a b).mpr hh))
    rw [max_eq_left hba] at hsmax
    subst s
    have ha : a ≤ addValue M a b := by
      change a ≤ a + b
      exact le_add_of_nonneg_right (zero_le_value b)
    have hn : ¬ leValue M (succValue M (addValue M a b)) a :=
      fun hh => not_lt_of_ge ha ((successor_le_iff_lt _ _).mp hh)
    simp only [unpairLeftModel, unpairRightModel,
      squareRemainderModel_pair_of_not_lt a b h, hn, ↓reduceIte, true_and]
    have hsub := (subtraction_spec (addValue M a b) a).1 ha
    change subtraction.value ![a + b, a] + a = a + b at hsub
    change subtraction.value ![a + b, a] = b
    apply add_right_cancel (b := a)
    exact hsub.trans (add_comm _ _)

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms
