import Lemmatheca.OracleProgramNumberings.Enumerable
import Lemmatheca.TuringDegrees.Reductions

/-! Relative diagonal halting in the actual nine-form oracle numbering. -/
namespace Lemmatheca.ComputabilityTheory.TuringJump

open OracleComputation OracleProgramNumberings

noncomputable section

def jump (A : Set ℕ) : Set ℕ := {e | (phi A e e).Dom}

def diagonalCode : Code := .comp universalCode (.pair identityCode identityCode)

def diagonalIndex : ℕ := encodeCode diagonalCode

theorem diagonal_eval (A : Set ℕ) (e : ℕ) :
    phi A diagonalIndex e = phi A e e := by
  unfold phi diagonalIndex
  rw [decode_encode]
  simp only [diagonalCode, eval, identity_eval, Part.bind_some, Part.map_some]
  exact universal_code_eval A e e

theorem jump_eq_domain (A : Set ℕ) : jump A = relativeDomain A diagonalIndex := by
  ext e
  change (phi A e e).Dom ↔ (phi A diagonalIndex e).Dom
  rw [diagonal_eval]

theorem jump_ce (A : Set ℕ) : RelativeCE A (jump A) := by
  exact (relative_ce_iff_index A (jump A)).mpr ⟨diagonalIndex, jump_eq_domain A⟩

theorem jump_certificate (A : Set ℕ) (e : ℕ) :
    e ∈ jump A ↔ ∃ k, 0 < boundedValue A k e e := by
  exact phi_domain_certificate A e e

def freeze (e x : ℕ) : ℕ :=
  encodeCode (.comp (decodeCode e) (constantCode x))

theorem freeze_eq (e x : ℕ) : freeze e x = 7 + 4 * Nat.pair e (constantIndex x) := by
  simp only [freeze, encodeCode, encode_decode, constantIndex]

theorem freeze_primitive : Primrec₂ freeze := by
  exact (compIndex_primitive.comp Primrec.fst
    (constantIndex_primitive.comp Primrec.snd)).of_eq (fun p => (freeze_eq p.1 p.2).symm)

theorem freeze_eval (A : Set ℕ) (e x y : ℕ) :
    phi A (freeze e x) y = phi A e x := by
  simp only [phi, freeze, decode_encode, eval, constant_eval, Part.bind_some]

theorem freeze_membership (A : Set ℕ) (e x : ℕ) :
    x ∈ relativeDomain A e ↔ freeze e x ∈ jump A := by
  change (phi A e x).Dom ↔ (phi A (freeze e x) (freeze e x)).Dom
  rw [freeze_eval]

def gateTestValue (b z : ℕ) : ℕ := if z = b then 0 else 1

theorem gate_test_primitive (b : ℕ) : Nat.Primrec (gateTestValue b) := by
  apply Primrec.nat_iff.mp
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const b))
    (Primrec.const 0) (Primrec.const 1)

def gateTestCode (b : ℕ) : Code :=
  embed (ordinaryCode (gateTestValue b) (gate_test_primitive b))

private theorem embed_query_free (c : Nat.Partrec.Code) : QueryFree (embed c) := by
  induction c <;> simp_all [embed, QueryFree]

theorem gate_test_query_free (b : ℕ) : QueryFree (gateTestCode b) := by
  unfold gateTestCode
  apply embed_query_free

theorem gate_test_eval (A : Set ℕ) (b z : ℕ) :
    eval A (gateTestCode b) z = Part.some (gateTestValue b z) := by
  simp only [gateTestCode, eval_embed, ordinaryCode_eval]

def gateCode (b : ℕ) : Code :=
  .comp (.find' (.comp (gateTestCode b) .left)) (.pair identityCode .zero)

theorem gate_eval (A : Set ℕ) (b z : ℕ) :
    eval A (gateCode b) z = if z = b then Part.some 0 else Part.none := by
  have hp : eval A (.pair identityCode .zero) z = Part.some (Nat.pair z 0) := by
    simp only [eval, identity_eval, Part.bind_some, Part.map_some]
  change (eval A (.pair identityCode .zero) z).bind
    (eval A (.find' (.comp (gateTestCode b) .left))) = _
  rw [hp, Part.bind_some]
  have ht (j : ℕ) : eval A (.comp (gateTestCode b) .left) (Nat.pair z j) =
      Part.some (gateTestValue b z) := by
    simp only [eval, Nat.unpair_pair, Part.bind_some, gate_test_eval]
  by_cases hz : z = b
  · rw [ite_eq_left hz]
    apply Part.eq_some_iff.mpr
    apply (eval_find A (.comp (gateTestCode b) .left) z 0 0).mpr
    refine ⟨le_rfl, ?_, fun i _ hi => False.elim (Nat.not_lt_zero i hi)⟩
    rw [ht]
    simp [gateTestValue, hz]
  · rw [ite_eq_right hz]
    apply Part.eq_none_iff.mpr
    intro y hy
    have hh := ((eval_find A (.comp (gateTestCode b) .left) z 0 y).mp hy).2.1
    rw [ht] at hh
    simp [gateTestValue, hz] at hh

def queryGateIndex (b : ℕ) : ℕ := encodeCode (.comp (gateCode b) .query)

def queryMap (b x : ℕ) : ℕ := freeze (queryGateIndex b) x

theorem query_map_primitive (b : ℕ) : Primrec (queryMap b) := by
  exact freeze_primitive.comp (Primrec.const (queryGateIndex b)) Primrec.id

theorem query_map_correct (A : Set ℕ) (b x : ℕ) :
    queryMap b x ∈ jump A ↔ UniversalComputation.indicator (fun n => n ∈ A) x = b := by
  change (phi A (freeze (queryGateIndex b) x) (queryMap b x)).Dom ↔ _
  rw [freeze_eval]
  unfold phi queryGateIndex
  rw [decode_encode]
  change ((Part.some (UniversalComputation.indicator (fun n => n ∈ A) x)).bind
    (eval A (gateCode b))).Dom ↔ _
  rw [Part.bind_some, gate_eval]
  split_ifs <;> simp_all

theorem membership_maps (A : Set ℕ) (x : ℕ) :
    (x ∈ A ↔ queryMap 1 x ∈ jump A) ∧
      (x ∉ A ↔ queryMap 0 x ∈ jump A) := by
  classical
  rw [query_map_correct, query_map_correct]
  by_cases hx : x ∈ A <;> simp [UniversalComputation.indicator, hx]

theorem oracle_manyOne_jump (A : Set ℕ) :
    ManyOneReducible (fun x => x ∈ A) (fun e => e ∈ jump A) ∧
      ManyOneReducible (fun x => x ∈ Aᶜ) (fun e => e ∈ jump A) := by
  exact ⟨⟨queryMap 1, (query_map_primitive 1).to_comp, fun x => (membership_maps A x).1⟩,
    ⟨queryMap 0, (query_map_primitive 0).to_comp, fun x => (membership_maps A x).2⟩⟩

theorem relative_decidable_iff_reducible (A S : Set ℕ) :
    RelativeDecidable A S ↔ TuringDegrees.Reducible S A := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun x => congrFun hc x⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, funext hc⟩

def diagonalAgainst (c : Code) : Code := .comp (gateCode 0) c

theorem diagonal_against (A : Set ℕ) (c : Code)
    (hc : TuringDegrees.Reduces c (jump A) A) :
    encodeCode (diagonalAgainst c) ∈ jump A ↔
      encodeCode (diagonalAgainst c) ∉ jump A := by
  classical
  change (eval A (decodeCode (encodeCode (diagonalAgainst c)))
    (encodeCode (diagonalAgainst c))).Dom ↔ _
  rw [decode_encode]
  change ((eval A c (encodeCode (diagonalAgainst c))).bind
    (eval A (gateCode 0))).Dom ↔ _
  rw [hc, Part.bind_some, gate_eval]
  by_cases hp : encodeCode (diagonalAgainst c) ∈ jump A <;>
    simp [UniversalComputation.indicator, hp]

theorem jump_not_decidable (A : Set ℕ) : ¬ RelativeDecidable A (jump A) := by
  rintro ⟨c, hc⟩
  have hh := diagonal_against A c (fun x => congrFun hc x)
  by_cases hp : encodeCode (diagonalAgainst c) ∈ jump A
  · exact (hh.mp hp) hp
  · exact hp (hh.mpr hp)

theorem jump_strict (A : Set ℕ) :
    TuringDegrees.Reducible A (jump A) ∧ ¬ TuringDegrees.Reducible (jump A) A := by
  exact ⟨TuringDegrees.manyOne_imp_reducible (oracle_manyOne_jump A).1,
    fun h => jump_not_decidable A ((relative_decidable_iff_reducible A (jump A)).mpr h)⟩

theorem jump_complement_not_ce (A : Set ℕ) : ¬ RelativeCE A (jump A)ᶜ := by
  intro hc
  exact jump_not_decidable A ((relative_two_sided_recognition A (jump A)).mpr ⟨jump_ce A, hc⟩)

theorem relative_ce_preimage (A S : Set ℕ) (g : ℕ → ℕ)
    (hS : RelativeCE A S) (hg : Computable g) :
    RelativeCE A {x | g x ∈ S} := by
  obtain ⟨c, rfl⟩ := hS
  obtain ⟨r, hr⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hg.partrec)
  refine ⟨.comp c (embed r), ?_⟩
  ext x
  change (eval A c (g x)).Dom ↔ (eval A (.comp c (embed r)) x).Dom
  change _ ↔ ((eval A (embed r) x).bind (eval A c)).Dom
  rw [eval_embed, show r.eval x = Part.some (g x) from congrFun hr x, Part.bind_some]

theorem relative_ce_iff_jump (A S : Set ℕ) :
    RelativeCE A S ↔ ManyOneReducible (fun x => x ∈ S) (fun e => e ∈ jump A) := by
  constructor
  · intro hS
    obtain ⟨e, rfl⟩ := (relative_ce_iff_index A S).mp hS
    exact ⟨freeze e, (freeze_primitive.comp (Primrec.const e) Primrec.id).to_comp,
      freeze_membership A e⟩
  · rintro ⟨g, hg, hred⟩
    have h := relative_ce_preimage A (jump A) g (jump_ce A) hg
    have heq : S = {x | g x ∈ jump A} := Set.ext hred
    rwa [← heq] at h

theorem two_reductions_decide (A S : Set ℕ)
    (hS : ManyOneReducible (fun x => x ∈ S) (fun e => e ∈ jump A))
    (hSc : ManyOneReducible (fun x => x ∈ Sᶜ) (fun e => e ∈ jump A)) :
    RelativeDecidable A S := by
  exact (relative_two_sided_recognition A S).mpr
    ⟨(relative_ce_iff_jump A S).mpr hS, (relative_ce_iff_jump A Sᶜ).mpr hSc⟩

end
end Lemmatheca.ComputabilityTheory.TuringJump
