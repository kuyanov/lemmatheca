import Lemmatheca.FiniteInjuryAndPostsProblem.Construction

/-! Ordinary primitive-recursive stages and the actual ordinary recognizer indices. -/
namespace Lemmatheca.ComputabilityTheory.FiniteInjury

open PostsTheorem OracleComputation OracleProgramNumberings PrimitiveRecursion

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false


private theorem aCode_prim : Primrec aCode := Primrec.fst
private theorem bCode_prim : Primrec bCode := Primrec.fst.comp Primrec.snd
private theorem dCode_prim : Primrec dCode := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem rCode_prim : Primrec rCode := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

private theorem packState_prim : Primrec packState :=
  Primrec₂.natPair.comp aCode_prim
    (Primrec₂.natPair.comp bCode_prim (Primrec₂.natPair.comp dCode_prim rCode_prim))

private theorem unpackState_prim : Primrec unpackState :=
  (Primrec.fst.comp Primrec.unpair).pair
    (((Primrec.fst.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)).pair
      (((Primrec.fst.comp Primrec.unpair).comp
        ((Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair))).pair
        ((Primrec.snd.comp Primrec.unpair).comp
          ((Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)))))

private theorem targetCode_prim : Primrec₂ targetCode :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
    (Primrec.const 0)) (aCode_prim.comp Primrec.fst) (bCode_prim.comp Primrec.fst)

private theorem oracleCode_prim : Primrec₂ oracleCode :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
    (Primrec.const 0)) (bCode_prim.comp Primrec.fst) (aCode_prim.comp Primrec.fst)

private theorem flag_prim : Primrec₂ flag :=
  beta_primitive.comp (dCode_prim.comp Primrec.fst) Primrec.snd

private theorem restraint_prim : Primrec₂ restraint :=
  FiniteSequenceCoding.primrec_entry.comp (rCode_prim.comp Primrec.fst) Primrec.snd

theorem tabulate_primitive {α : Type*} [Primcodable α] {f : α → ℕ → ℕ}
    (hf : Primrec₂ f) : Primrec₂ (fun a n => tabulate n (f a)) := by
  have hm : Primrec (fun p : α × ℕ => (List.range p.2).map (f p.1)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (hf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.encode.comp hm

theorem reservoir_predicate_primitive :
    PrimrecPred (fun p : ℕ × ℕ => p.2 ∈ reservoir p.1) := by
  simpa only [reservoir, Set.mem_ofPred_eq] using
    (Primrec.eq.comp ((Primrec.fst.comp Primrec.unpair).comp Primrec.snd) Primrec.fst)

theorem eligible_primitive :
    PrimrecPred (fun p : (ℕ × State × ℕ) × ℕ =>
      Eligible p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let P := (ℕ × State × ℕ) × ℕ
  have hs : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have hz : Primrec (fun p : P => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun p : P => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec (fun p : P => p.2) := Primrec.snd
  have hf : PrimrecPred (fun p : P => flag p.1.2.1 p.1.2.2 = 0) :=
    Primrec.eq.comp (flag_prim.comp hz hi) (Primrec.const 0)
  have hb : PrimrecPred (fun p : P => beta (targetCode p.1.2.1 p.1.2.2) p.2 = 0) :=
    Primrec.eq.comp (beta_primitive.comp (targetCode_prim.comp hz hi) hx) (Primrec.const 0)
  have hr : PrimrecRel (fun p : P => fun j => restraint p.1.2.1 j ≤ p.2) :=
    Primrec.nat_le.comp (restraint_prim.comp (hz.comp Primrec.fst) Primrec.snd)
      (hx.comp Primrec.fst)
  have hbound : PrimrecPred (fun p : P => ∀ j < p.1.2.2, restraint p.1.2.1 j ≤ p.2) :=
    (bounded_forall_primrec hr).comp Primrec.id hi
  have hpack : Primrec (fun p : P => pack4 (oracleCode p.1.2.1 p.1.2.2)
      (p.1.1 + 1) (p.1.2.2 / 2) p.2) :=
    Primrec₂.natPair.comp (oracleCode_prim.comp hz hi)
      (Primrec₂.natPair.comp (Primrec.succ.comp hs)
        (Primrec₂.natPair.comp (Primrec.nat_div.comp hi (Primrec.const 2)) hx))
  have hv : Primrec (fun p : P => finiteValue (oracleCode p.1.2.1 p.1.2.2)
      (p.1.1 + 1) (p.1.2.2 / 2) p.2) :=
    (finiteValue_primitive.comp hpack).of_eq (fun _ => by
      simp only [finiteValueInput, pack4, Nat.unpair_pair])
  exact (Primrec.nat_le.comp hi hs).and ((Primrec.nat_le.comp hx hs).and
    ((reservoir_predicate_primitive.comp (hi.pair hx)).and
      (hf.and (hb.and (hbound.and (Primrec.eq.comp hv (Primrec.const 1)))))))

theorem witness_primitive :
    Primrec (fun p : ℕ × State × ℕ => witness p.1 p.2.1 p.2.2) := by
  exact (boundedSearch_primrec (R := fun p : ℕ × State × ℕ => Eligible p.1 p.2.1 p.2.2)
    eligible_primitive).comp Primrec.id (Primrec.succ.comp Primrec.fst)

theorem priority_primitive : Primrec₂ priority := by
  have hw : Primrec (fun p : (ℕ × State) × ℕ => witness p.1.1 p.1.2 p.2) :=
    witness_primitive.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have hR : PrimrecRel (fun p : ℕ × State => fun i => witness p.1 p.2 i < p.1 + 1) :=
    Primrec.nat_lt.comp hw (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
  exact (boundedSearch_primrec hR).comp Primrec.id (Primrec.succ.comp Primrec.fst)

theorem next_primitive : Primrec₂ next := by
  let P := ℕ × State
  have hp : Primrec (fun p : P => priority p.1 p.2) := priority_primitive
  have hHas : PrimrecPred (fun p : P => HasAction p.1 p.2) :=
    Primrec.nat_lt.comp hp (Primrec.succ.comp Primrec.fst)
  have hw : Primrec (fun p : P => chosenWitness p.1 p.2) :=
    witness_primitive.comp (Primrec.fst.pair (Primrec.snd.pair hp))
  have hpf : Primrec (fun p : P × ℕ => priority p.1.1 p.1.2) := hp.comp Primrec.fst
  have hAct : PrimrecPred (fun p : P × ℕ => HasAction p.1.1 p.1.2) := hHas.comp Primrec.fst
  have hParity : PrimrecPred (fun p : P × ℕ => priority p.1.1 p.1.2 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hpf (Primrec.const 2)) (Primrec.const 0)
  have hWitness : PrimrecPred (fun p : P × ℕ => p.2 = chosenWitness p.1.1 p.1.2) :=
    Primrec.eq.comp Primrec.snd (hw.comp Primrec.fst)
  have hA : Primrec (fun p : P × ℕ => beta (aCode p.1.2) p.2) :=
    beta_primitive.comp (aCode_prim.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hB : Primrec (fun p : P × ℕ => beta (bCode p.1.2) p.2) :=
    beta_primitive.comp (bCode_prim.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hleft : Primrec₂ (fun p : P => fun x =>
      if HasAction p.1 p.2 ∧ priority p.1 p.2 % 2 = 0 ∧ x = chosenWitness p.1 p.2 then 1
      else beta (aCode p.2) x) :=
    Primrec.ite (hAct.and (hParity.and hWitness)) (Primrec.const 1) hA
  have hright : Primrec₂ (fun p : P => fun x =>
      if HasAction p.1 p.2 ∧ priority p.1 p.2 % 2 ≠ 0 ∧ x = chosenWitness p.1 p.2 then 1
      else beta (bCode p.2) x) :=
    Primrec.ite (hAct.and (hParity.not.and hWitness)) (Primrec.const 1) hB
  have hlt : PrimrecPred (fun p : P × ℕ => p.2 < priority p.1.1 p.1.2) :=
    Primrec.nat_lt.comp Primrec.snd hpf
  have heq : PrimrecPred (fun p : P × ℕ => p.2 = priority p.1.1 p.1.2) :=
    Primrec.eq.comp Primrec.snd hpf
  have hflag : Primrec (fun p : P × ℕ => flag p.1.2 p.2) :=
    flag_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hrest : Primrec (fun p : P × ℕ => restraint p.1.2 p.2) :=
    restraint_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hflags : Primrec₂ (fun p : P => fun j =>
      if HasAction p.1 p.2 then
        if j < priority p.1 p.2 then flag p.2 j else if j = priority p.1 p.2 then 1 else 0
      else flag p.2 j) :=
    Primrec.ite hAct (Primrec.ite hlt hflag
      (Primrec.ite heq (Primrec.const 1) (Primrec.const 0))) hflag
  have hrestr : Primrec₂ (fun p : P => fun j =>
      if HasAction p.1 p.2 then
        if j < priority p.1 p.2 then restraint p.2 j
        else if j = priority p.1 p.2 then p.1 + 1 else 0
      else restraint p.2 j) :=
    Primrec.ite hAct (Primrec.ite hlt hrest
      (Primrec.ite heq (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 0))) hrest
  have hbound : Primrec (fun p : P => p.1 + 1) := Primrec.succ.comp Primrec.fst
  exact ((tabulate_primitive hleft).comp Primrec.id hbound).pair
    (((tabulate_primitive hright).comp Primrec.id hbound).pair
      (((tabulate_primitive hflags).comp Primrec.id hbound).pair
        ((tabulate_primitive hrestr).comp Primrec.id hbound)))

theorem next_number_primitive : Primrec₂ nextNumber := by
  exact packState_prim.comp (next_primitive.comp Primrec.fst (unpackState_prim.comp Primrec.snd))

theorem stage_primitive : Primrec stage := by
  apply (Primrec.nat_rec₁ (0, 0, 0, 0) next_primitive).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (next n) ih

theorem state_number_primitive : Primrec stateNumber := by
  exact packState_prim.comp stage_primitive

theorem action_primitive : Primrec action := by
  have hp : Primrec (fun s => priority s (stage s)) :=
    priority_primitive.comp Primrec.id stage_primitive
  exact Primrec.ite (Primrec.nat_lt.comp hp Primrec.succ)
    (Primrec.succ.comp hp) (Primrec.const 0)

theorem stage_bits_primitive : Primrec₂ leftBit ∧ Primrec₂ rightBit := by
  exact ⟨beta_primitive.comp (aCode_prim.comp (stage_primitive.comp Primrec.fst)) Primrec.snd,
    beta_primitive.comp (bCode_prim.comp (stage_primitive.comp Primrec.fst)) Primrec.snd⟩

def stateProgram : Nat.Partrec.Code :=
  ordinaryCode stateNumber (Primrec.nat_iff.mp state_number_primitive)

theorem state_program_eval (s : ℕ) :
    stateProgram.eval s = Part.some (stateNumber s) := by
  exact ordinaryCode_eval stateNumber (Primrec.nat_iff.mp state_number_primitive) s

def leftRecognizer (x : ℕ) : Part ℕ :=
  Nat.rfind (fun s => Part.some (decide (leftBit s x = 1)))

def rightRecognizer (x : ℕ) : Part ℕ :=
  Nat.rfind (fun s => Part.some (decide (rightBit s x = 1)))

theorem left_recognizer_recursive : Nat.Partrec leftRecognizer := by
  have hp : Computable₂ (fun x s => decide (leftBit s x = 1)) :=
    (Primrec.eq.decide.comp (stage_bits_primitive.1.comp Primrec.snd Primrec.fst)
      (Primrec.const 1)).to_comp
  exact Partrec.nat_iff.mp (Partrec.rfind hp.partrec₂)

theorem right_recognizer_recursive : Nat.Partrec rightRecognizer := by
  have hp : Computable₂ (fun x s => decide (rightBit s x = 1)) :=
    (Primrec.eq.decide.comp (stage_bits_primitive.2.comp Primrec.snd Primrec.fst)
      (Primrec.const 1)).to_comp
  exact Partrec.nat_iff.mp (Partrec.rfind hp.partrec₂)

def leftRecognizerCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp left_recognizer_recursive)

def rightRecognizerCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp right_recognizer_recursive)

def leftRecognizerIndex : ℕ := Encodable.encode leftRecognizerCode
def rightRecognizerIndex : ℕ := Encodable.encode rightRecognizerCode

theorem left_recognizer_eval (x : ℕ) :
    UniversalComputation.phi leftRecognizerIndex x = leftRecognizer x := by
  unfold UniversalComputation.phi leftRecognizerIndex
  rw [Denumerable.ofNat_encode]
  exact congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp left_recognizer_recursive)) x

theorem right_recognizer_eval (x : ℕ) :
    UniversalComputation.phi rightRecognizerIndex x = rightRecognizer x := by
  unfold UniversalComputation.phi rightRecognizerIndex
  rw [Denumerable.ofNat_encode]
  exact congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp right_recognizer_recursive)) x

theorem recognizer_domains (x : ℕ) :
    ((UniversalComputation.phi leftRecognizerIndex x).Dom ↔ x ∈ leftSet) ∧
      ((UniversalComputation.phi rightRecognizerIndex x).Dom ↔ x ∈ rightSet) := by
  rw [left_recognizer_eval, right_recognizer_eval]
  constructor
  · simp [leftRecognizer, Nat.rfind_dom, leftSet, leftStage, leftBit, finiteOracle]
  · simp [rightRecognizer, Nat.rfind_dom, rightSet, rightStage, rightBit, finiteOracle]

theorem constructed_enumerable : REPred leftSet ∧ REPred rightSet := by
  exact ⟨(UniversalComputation.enumerable_iff_index leftSet).mpr
      ⟨leftRecognizerIndex, fun x => (recognizer_domains x).1.symm⟩,
    (UniversalComputation.enumerable_iff_index rightSet).mpr
      ⟨rightRecognizerIndex, fun x => (recognizer_domains x).2.symm⟩⟩

end
end Lemmatheca.ComputabilityTheory.FiniteInjury
