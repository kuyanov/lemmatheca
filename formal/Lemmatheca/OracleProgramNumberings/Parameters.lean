import Lemmatheca.OracleProgramNumberings.Coding

/-! Oracle-independent parameter insertion into the actual numbered syntax. -/
namespace Lemmatheca.ComputabilityTheory.OracleProgramNumberings

open OracleComputation

def constantCode : ℕ → Code
  | 0 => .zero
  | a + 1 => .comp .succ (constantCode a)

def identityCode : Code := .pair .left .right

def QueryFree : Code → Prop
  | .zero | .succ | .left | .right => True
  | .query => False
  | .pair c d | .comp c d | .prec c d => QueryFree c ∧ QueryFree d
  | .find' c => QueryFree c

def constantIndex (a : ℕ) : ℕ := encodeCode (constantCode a)

def specialize (e a : ℕ) : ℕ :=
  encodeCode (.comp (decodeCode e) (.pair (constantCode a) identityCode))

noncomputable def ordinaryCode (f : ℕ → ℕ) (hf : Nat.Primrec f) : Nat.Partrec.Code :=
  Classical.choose (UniversalComputation.searchFree_complete hf)

theorem ordinaryCode_eval (f : ℕ → ℕ) (hf : Nat.Primrec f) (x : ℕ) :
    Nat.Partrec.Code.eval (ordinaryCode f hf) x = Part.some (f x) :=
  congrFun (Classical.choose_spec (UniversalComputation.searchFree_complete hf)).2 x

def concatInput (w : ℕ) : ℕ :=
  FiniteSequenceCoding.append w.unpair.1 w.unpair.2

theorem concatInput_primitive : Nat.Primrec concatInput :=
  Primrec.nat_iff.mp (FiniteSequenceCoding.primrec_append.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

noncomputable def concatCode : Code := embed (ordinaryCode concatInput concatInput_primitive)

noncomputable def tupleSpecialize {m : ℕ} (e : ℕ) (a : List.Vector ℕ m) : ℕ :=
  encodeCode (.comp (decodeCode e)
    (.comp concatCode (.pair (constantCode (FiniteSequenceCoding.code a.toList)) identityCode)))

theorem constant_eval (A : Set ℕ) (a x : ℕ) :
    eval A (constantCode a) x = Part.some a := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [constantCode, eval, ih, Part.bind_some]

theorem identity_eval (A : Set ℕ) (x : ℕ) : eval A identityCode x = Part.some x := by
  simp [identityCode, eval]

theorem parameters_query_free (a : ℕ) :
    QueryFree (constantCode a) ∧ QueryFree identityCode := by
  constructor
  · induction a <;> simp_all [constantCode, QueryFree]
  · trivial

theorem constantIndex_primitive : Primrec constantIndex := by
  have h : Primrec (Nat.rec 0 (fun _ v => 7 + 4 * Nat.pair 1 v)) :=
    Primrec.nat_rec₁ 0 (Primrec.nat_add.comp (Primrec.const 7)
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp (Primrec.const 1) Primrec.snd)))
  apply h.of_eq
  intro a
  induction a <;> simp_all [constantIndex, constantCode, encodeCode]

theorem specialize_primitive : Primrec₂ specialize := by
  have h := compIndex_primitive.comp Primrec.fst
    (pairIndex_primitive.comp (constantIndex_primitive.comp Primrec.snd)
      (Primrec.const (encodeCode identityCode)))
  exact h.of_eq fun _ => by simp [specialize, compIndex, pairIndex, constantIndex,
    encodeCode, encode_decode]

theorem specialize_eval (A : Set ℕ) (e a x : ℕ) :
    phi A (specialize e a) x = phi A e (Nat.pair a x) := by
  simp only [phi, specialize, decode_encode, eval, constant_eval, identity_eval,
    Part.bind_some, Part.map_some]

theorem tupleSpecialize_primitive (m : ℕ) : Primrec₂ (@tupleSpecialize m) := by
  have h := compIndex_primitive.comp Primrec.fst
    (compIndex_primitive.comp (Primrec.const (encodeCode concatCode))
      (pairIndex_primitive.comp
        (constantIndex_primitive.comp (Primrec.encode.comp
          ((@Primrec.vector_toList ℕ _ m).comp Primrec.snd)))
        (Primrec.const (encodeCode identityCode))))
  exact h.of_eq fun _ => by simp [tupleSpecialize, compIndex, pairIndex, constantIndex,
    encodeCode, encode_decode]

theorem tupleSpecialize_eval (A : Set ℕ) {m n : ℕ} (e : ℕ)
    (a : List.Vector ℕ m) (x : List.Vector ℕ n) :
    phi A (tupleSpecialize e a) (FiniteSequenceCoding.code x.toList) =
      phi A e (FiniteSequenceCoding.code (a.toList ++ x.toList)) := by
  simp only [phi, tupleSpecialize, decode_encode, eval, constant_eval, identity_eval,
    Part.bind_some, Part.map_some, concatCode, eval_embed, ordinaryCode_eval,
    concatInput, Nat.unpair_pair, FiniteSequenceCoding.append_code]

end Lemmatheca.ComputabilityTheory.OracleProgramNumberings
