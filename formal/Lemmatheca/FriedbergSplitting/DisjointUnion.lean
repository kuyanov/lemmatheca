import Lemmatheca.FriedbergSplitting.Scheduler
import Lemmatheca.TuringDegrees.Joins
import Lemmatheca.OracleProgramNumberings.Parameters

/-! Guarded oracle programs recovering c.e. pieces from their disjoint union. -/
namespace Lemmatheca.ComputabilityTheory.FriedbergSplitting

open EffectiveEnumerations UniversalComputation OracleComputation OracleProgramNumberings TuringDegrees

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def firstUnionStage (a b x : ℕ) : Part ℕ :=
  Nat.rfind fun s => Part.some (decide (stageTest a s x = 1 ∨ stageTest b s x = 1))

def guardedPiece (a b i z : ℕ) : Part ℕ :=
  if z.unpair.1 = 0 then Part.some 0
  else (firstUnionStage a b z.unpair.2).map (fun s =>
    if i % 2 = 0 then stageTest a s z.unpair.2 else stageTest b s z.unpair.2)

theorem guarded_piece_recursive (a b i : ℕ) : Nat.Partrec (guardedPiece a b i) := by
  have ha : Primrec (fun p : ℕ × ℕ => stageTest a p.2 p.1) :=
    stage_test_primitive.comp (((Primrec.const a).pair Primrec.snd).pair Primrec.fst)
  have hb : Primrec (fun p : ℕ × ℕ => stageTest b p.2 p.1) :=
    stage_test_primitive.comp (((Primrec.const b).pair Primrec.snd).pair Primrec.fst)
  have ht : Computable₂ (fun x s => decide (stageTest a s x = 1 ∨ stageTest b s x = 1)) :=
    (PrimitiveRecursiveAutomation.orPred
      (Primrec.eq.decide.comp ha (Primrec.const 1))
      (Primrec.eq.decide.comp hb (Primrec.const 1))).to_comp
  have hf : Partrec (firstUnionStage a b) := Partrec.rfind ht.partrec₂
  have hs : Partrec (fun z : ℕ => firstUnionStage a b z.unpair.2) :=
    hf.comp (Computable.snd.comp Computable.unpair)
  have hout : Computable₂ (fun (z s : ℕ) =>
      if i % 2 = 0 then stageTest a s z.unpair.2 else stageTest b s z.unpair.2) := by
    by_cases hi : i % 2 = 0
    · simpa only [ite_eq_left hi] using
        ((canonical_test_data a).1.comp Computable.snd
          (Computable.snd.comp (Computable.unpair.comp Computable.fst))).to₂
    · simpa only [ite_eq_right hi] using
        ((canonical_test_data b).1.comp Computable.snd
          (Computable.snd.comp (Computable.unpair.comp Computable.fst))).to₂
  have hz : Computable (fun z : ℕ => decide (z.unpair.1 = 0)) :=
    Primrec.eq.decide.to_comp.comp (Computable.fst.comp Computable.unpair) (Computable.const 0)
  exact Partrec.nat_iff.mp ((Partrec.cond hz (Partrec.const' (Part.some 0)) (hs.map hout)).of_eq
    (fun z => by simp [guardedPiece]))

def guardedCode (a b i : ℕ) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (guarded_piece_recursive a b i))

def pieceProgram (a b i : ℕ) : OracleComputation.Code :=
  .comp (embed (guardedCode a b i)) (.pair .query identityCode)

theorem guarded_code_eval (a b i z : ℕ) :
    Nat.Partrec.Code.eval (guardedCode a b i) z = guardedPiece a b i z := by
  exact congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp (guarded_piece_recursive a b i))) z

theorem piece_program_reduces (a b i : ℕ) (hi : i < 2)
    (hd : Disjoint (indexSet a) (indexSet b)) :
    Reduces (pieceProgram a b i) (if i = 0 then indexSet a else indexSet b)
      (indexSet a ∪ indexSet b) := by
  intro x
  simp only [pieceProgram, eval, identity_eval, Part.bind_some, Part.map_some,
    eval_embed, guarded_code_eval]
  by_cases hx : x ∈ indexSet a ∪ indexSet b
  · have hu : indicator (fun n => n ∈ indexSet a ∪ indexSet b) x = 1 := by
      simp [indicator, hx]
    have hdom : (firstUnionStage a b x).Dom := by
      rcases hx with hax | hbx
      · obtain ⟨s, hs⟩ := (stage_union a x).mp hax
        have hh := (stage_test_spec a s x).2.mpr hs
        exact Nat.rfind_dom.mpr ⟨s, by simp [hh], fun _ => trivial⟩
      · obtain ⟨s, hs⟩ := (stage_union b x).mp hbx
        have hh := (stage_test_spec b s x).2.mpr hs
        exact Nat.rfind_dom.mpr ⟨s, by simp [hh], fun _ => trivial⟩
    let s := (firstUnionStage a b x).get hdom
    have hs : s ∈ firstUnionStage a b x := Part.get_mem hdom
    have hor : stageTest a s x = 1 ∨ stageTest b s x = 1 := by
      simpa only [firstUnionStage, Part.mem_some_iff, true_eq_decide_iff] using
        Nat.rfind_spec hs
    have hinc (e : ℕ) (he : stageTest e s x = 1) : x ∈ indexSet e :=
      (stage_union e x).mpr ⟨s, (stage_test_spec e s x).2.mp he⟩
    have ha : stageTest a s x = indicator (fun n => n ∈ indexSet a) x := by
      by_cases hax : x ∈ indexSet a
      · have hbn : stageTest b s x ≠ 1 := fun hh => Set.disjoint_left.mp hd hax (hinc b hh)
        have hh := hor.resolve_right hbn
        simp [indicator, hax, hh]
      · have han : stageTest a s x ≠ 1 := fun hh => hax (hinc a hh)
        have hh := (stage_test_spec a s x).1.resolve_right han
        simp [indicator, hax, hh]
    have hb : stageTest b s x = indicator (fun n => n ∈ indexSet b) x := by
      by_cases hbx : x ∈ indexSet b
      · have han : stageTest a s x ≠ 1 := fun hh => Set.disjoint_left.mp hd (hinc a hh) hbx
        have hh := hor.resolve_left han
        simp [indicator, hbx, hh]
      · have hbn : stageTest b s x ≠ 1 := fun hh => hbx (hinc b hh)
        have hh := (stage_test_spec b s x).1.resolve_right hbn
        simp [indicator, hbx, hh]
    have hsome : firstUnionStage a b x = Part.some s := Part.eq_some_iff.mpr hs
    by_cases hi0 : i = 0
    · subst i
      simpa only [guardedPiece, Nat.unpair_pair, hu, Nat.one_ne_zero, ↓reduceIte, hsome, Part.map_some, Nat.zero_mod] using congrArg Part.some ha
    · have hi1 : i = 1 := by omega
      subst i
      simpa only [guardedPiece, Nat.unpair_pair, hu, Nat.one_ne_zero, ↓reduceIte, hsome, Part.map_some, Nat.mod_self, Nat.reduceMod] using congrArg Part.some hb
  · have hu : indicator (fun n => n ∈ indexSet a ∪ indexSet b) x = 0 := by
      simp [indicator, hx]
    have hside : x ∉ (if i = 0 then indexSet a else indexSet b) := by
      split <;> intro hh
      · exact hx (Or.inl hh)
      · exact hx (Or.inr hh)
    simp only [guardedPiece, Nat.unpair_pair, hu, ↓reduceIte]
    change Part.some 0 = Part.some (if x ∈ (if i = 0 then indexSet a else indexSet b : Set ℕ) then 1 else 0)
    rw [ite_eq_right hside]

def unionBit (z : ℕ) : ℕ := max z.unpair.1 z.unpair.2

def unionBitCode : Nat.Partrec.Code :=
  ordinaryCode unionBit (Primrec.nat_iff.mp (Primrec.nat_max.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))

def evenInputCode : Nat.Partrec.Code :=
  ordinaryCode (fun x => 2 * x)
    (Primrec.nat_iff.mp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))

def oddInputCode : Nat.Partrec.Code :=
  ordinaryCode (fun x => 2 * x + 1)
    (Primrec.nat_iff.mp (Primrec.succ.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))

def unionProgram : OracleComputation.Code :=
  .comp (embed unionBitCode) (.pair
    (.comp .query (embed evenInputCode)) (.comp .query (embed oddInputCode)))

theorem union_program_reduces (A B : Set ℕ) :
    Reduces unionProgram (A ∪ B) (join A B) := by
  intro x
  have he : indicator (fun n => n ∈ join A B) (2 * x) = indicator (fun n => n ∈ A) x := by
    simp [join_indicator]
  have ho : indicator (fun n => n ∈ join A B) (2 * x + 1) = indicator (fun n => n ∈ B) x := by
    have hm : (2 * x + 1) % 2 = 1 := by omega
    have hv : (2 * x + 1) / 2 = x := by omega
    simp [join_indicator, hm, hv]
  simp only [unionProgram, eval, eval_embed, unionBitCode, evenInputCode, oddInputCode,
    ordinaryCode_eval, Part.bind_some, Part.map_some, unionBit, Nat.unpair_pair, he, ho]
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [indicator, ha, hb]

theorem disjoint_union_join (A B : Set ℕ) (hA : REPred A) (hB : REPred B)
    (hd : Disjoint A B) : Equivalent (A ∪ B) (join A B) := by
  obtain ⟨a, ha⟩ := (enumerable_iff_index A).mp hA
  obtain ⟨b, hb⟩ := (enumerable_iff_index B).mp hB
  have hea : A = indexSet a := Set.ext ha
  have heb : B = indexSet b := Set.ext hb
  subst A B
  refine ⟨⟨unionProgram, union_program_reduces _ _⟩, (join_reducible_iff _ _ _).mpr ?_⟩
  exact ⟨⟨pieceProgram a b 0, piece_program_reduces a b 0 (by decide) hd⟩,
    ⟨pieceProgram a b 1, piece_program_reduces a b 1 (by decide) hd⟩⟩

end
end Lemmatheca.ComputabilityTheory.FriedbergSplitting
