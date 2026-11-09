import Lemmatheca.TuringJump.IndexMaps

/-! The actual ordinary/oracle recodings, with original diagonal inputs frozen. -/
namespace Lemmatheca.ComputabilityTheory.TuringJump

open OracleComputation OracleProgramNumberings

noncomputable section

def embedIndex (i : ℕ) : ℕ := encodeCode (embed (Denumerable.ofNat Nat.Partrec.Code i))

def eraseZeroIndex (e : ℕ) : ℕ := Encodable.encode (erase .zero (decodeCode e))

theorem embed_index_primitive : Primrec embedIndex := by
  let F (c : Nat.Partrec.Code) : ℕ :=
    c.recOn 0 1 2 3
      (fun _ _ u v => pairIndex u v) (fun _ _ u v => compIndex u v)
      (fun _ _ u v => precIndex u v) (fun _ u => findIndex u)
  have h : Primrec (fun i : ℕ => F (Denumerable.ofNat Nat.Partrec.Code i)) := by
    apply Nat.Partrec.Code.primrec_recOn (Primrec.ofNat Nat.Partrec.Code)
      (Primrec.const 0) (Primrec.const 1) (Primrec.const 2) (Primrec.const 3)
    · exact pairIndex_primitive.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact compIndex_primitive.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact precIndex_primitive.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact findIndex_primitive.comp (Primrec.snd.comp Primrec.snd)
  apply h.of_eq
  intro i
  have he (c : Nat.Partrec.Code) : F c = encodeCode (embed c) := by
    induction c <;> simp_all [F, embed, encodeCode, pairIndex, compIndex, precIndex, findIndex]
  exact he (Denumerable.ofNat Nat.Partrec.Code i)

private theorem ordinary_binary_index_primitive (t : ℕ) :
    Primrec₂ (fun u v : ℕ => 4 * Nat.pair u v + t) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec₂.natPair)
    (Primrec.const t)

theorem erase_zero_index_primitive : Primrec eraseZeroIndex := by
  let F (c : Code) : ℕ :=
    Code.recOn (motive := fun _ => ℕ) c 0 1 2 3 0
      (fun _ _ u v => 4 * Nat.pair u v + 4) (fun _ _ u v => 4 * Nat.pair u v + 6)
      (fun _ _ u v => 4 * Nat.pair u v + 5) (fun _ u => 4 * u + 7)
  have h : Primrec (fun e : ℕ => F (decodeCode e)) := by
    apply primrec_recOn (Primrec.ofNat Code)
      (Primrec.const 0) (Primrec.const 1) (Primrec.const 2) (Primrec.const 3) (Primrec.const 0)
    · exact (ordinary_binary_index_primitive 4).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact (ordinary_binary_index_primitive 6).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact (ordinary_binary_index_primitive 5).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec.snd.comp Primrec.snd)) (Primrec.const 7)
  apply h.of_eq
  intro e
  have he (c : Code) : F c = Encodable.encode (erase .zero c) := by
    induction c <;> simp_all [F, erase, Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode] <;> omega
  exact he (decodeCode e)

theorem embed_index_eval (A : Set ℕ) (i x : ℕ) :
    phi A (embedIndex i) x = UniversalComputation.phi i x := by
  simp only [phi, embedIndex, decode_encode, eval_embed, UniversalComputation.phi]

theorem erase_zero_index_eval (e x : ℕ) :
    UniversalComputation.phi (eraseZeroIndex e) x = phi ∅ e x := by
  unfold UniversalComputation.phi eraseZeroIndex
  rw [Denumerable.ofNat_encode]
  exact erase_eval ∅ .zero (fun q => by
    change Part.some 0 = Part.some (UniversalComputation.indicator (fun n => n ∈ (∅ : Set ℕ)) q)
    simp [UniversalComputation.indicator]) (decodeCode e) x

def ordinaryFreeze (i x : ℕ) : ℕ :=
  Encodable.encode (Nat.Partrec.Code.comp (Denumerable.ofNat Nat.Partrec.Code i)
    (Nat.Partrec.Code.const x))

theorem ordinary_freeze_primitive : Primrec₂ ordinaryFreeze := by
  exact Primrec.encode.comp (Nat.Partrec.Code.primrec₂_comp.comp
    ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.fst)
    (Nat.Partrec.Code.primrec_const.comp Primrec.snd))

set_option backward.isDefEq.respectTransparency false in
theorem ordinary_freeze_eval (i x y : ℕ) :
    UniversalComputation.phi (ordinaryFreeze i x) y = UniversalComputation.phi i x := by
  simp only [UniversalComputation.phi, ordinaryFreeze, Denumerable.ofNat_encode,
    Nat.Partrec.Code.eval, Nat.Partrec.Code.eval_const, Part.bind_eq_bind, Part.bind_some]

def ordinaryToEmptyJump (i : ℕ) : ℕ := freeze (embedIndex i) i

def emptyJumpToOrdinary (e : ℕ) : ℕ := ordinaryFreeze (eraseZeroIndex e) e

theorem ordinary_to_empty_primitive : Primrec ordinaryToEmptyJump := by
  exact freeze_primitive.comp embed_index_primitive Primrec.id

theorem empty_to_ordinary_primitive : Primrec emptyJumpToOrdinary := by
  exact ordinary_freeze_primitive.comp erase_zero_index_primitive Primrec.id

theorem ordinary_to_empty_membership (i : ℕ) :
    i ∈ UniversalComputation.haltingDiagonal ↔ ordinaryToEmptyJump i ∈ jump ∅ := by
  change (UniversalComputation.phi i i).Dom ↔
    (phi ∅ (freeze (embedIndex i) i) (ordinaryToEmptyJump i)).Dom
  rw [freeze_eval, embed_index_eval]

theorem empty_to_ordinary_membership (e : ℕ) :
    e ∈ jump ∅ ↔ emptyJumpToOrdinary e ∈ UniversalComputation.haltingDiagonal := by
  change (phi ∅ e e).Dom ↔
    (UniversalComputation.phi (ordinaryFreeze (eraseZeroIndex e) e) (emptyJumpToOrdinary e)).Dom
  rw [ordinary_freeze_eval, erase_zero_index_eval]

theorem empty_jump_equiv_halting :
    ManyOneEquiv (fun e => e ∈ jump ∅) (fun i => i ∈ UniversalComputation.haltingDiagonal) := by
  exact ⟨⟨emptyJumpToOrdinary, empty_to_ordinary_primitive.to_comp, empty_to_ordinary_membership⟩,
    ⟨ordinaryToEmptyJump, ordinary_to_empty_primitive.to_comp, ordinary_to_empty_membership⟩⟩

theorem computable_jump_equiv_empty (A : Set ℕ)
    (hA : ComputablePred (fun n => n ∈ A)) :
    ManyOneEquiv (fun e => e ∈ jump A) (fun e => e ∈ jump ∅) := by
  have h0 : TuringDegrees.Reducible ∅ A :=
    ⟨.zero, fun x => by simp [eval, UniversalComputation.indicator]⟩
  exact ⟨jump_monotone ((TuringDegrees.reducible_empty_iff A).mpr hA), jump_monotone h0⟩

theorem computable_jump_equiv_halting (A : Set ℕ)
    (hA : ComputablePred (fun n => n ∈ A)) :
    ManyOneEquiv (fun e => e ∈ jump A) (fun i => i ∈ UniversalComputation.haltingDiagonal) := by
  exact (computable_jump_equiv_empty A hA).trans empty_jump_equiv_halting

theorem jump_undecidable (A : Set ℕ) :
    ¬ ComputablePred (fun e => e ∈ jump A) := by
  intro hJ
  obtain ⟨r, _, hr⟩ := TuringDegrees.computable_uniform (jump A) hJ
  exact jump_not_decidable A ((relative_decidable_iff_reducible A (jump A)).mpr
    ⟨embed r, hr A⟩)

end
end Lemmatheca.ComputabilityTheory.TuringJump
