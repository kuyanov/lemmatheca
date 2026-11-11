import Lemmatheca.EnumerationReducibility.Transcripts
import Lemmatheca.OracleProgramNumberings.Schemes

namespace Lemmatheca.ComputabilityTheory.EnumerationReducibility
open UniversalComputation
open OracleComputation (Code)

/-- Finite positive information about T(B), checked by finitely many B-queries. -/
def evidenceTest (q : ℕ → ℕ) (d : ℕ) : Bool :=
  (FiniteSequenceCoding.decode d).all (fun z =>
    if z % 2 = 0 then q (z/2) == 1 else q (z/2) == 0)

/-- u=((e,x),w), w=(b,(d,t)); zero means that this candidate succeeds. -/
def oracleCandidate (q : ℕ → ℕ) (u : ℕ) : ℕ :=
  let e := u.unpair.1.unpair.1
  let x := u.unpair.1.unpair.2
  let w := u.unpair.2
  let b := w.unpair.1
  let d := w.unpair.2.unpair.1
  let t := w.unpair.2.unpair.2
  if decide (b ≤ 1) && stageCheck e t (Nat.pair (tag x b) d) && evidenceTest q d
  then 0 else 1

private theorem totalInfo_parity (B : Set ℕ) (z : ℕ) :
    z ∈ totalInfo B ↔ if z % 2 = 0 then z/2 ∈ B else z/2 ∉ B := by
  have hm : z % 2 < 2 := Nat.mod_lt z (by decide)
  by_cases hz : z % 2 = 0
  · have he : z = 2*(z/2) := by omega
    rw [ite_eq_left hz]; rw [he]
    simpa using (totalInfo_exactly_one B (z/2)).1
  · have he : z = 2*(z/2)+1 := by omega
    rw [ite_eq_right hz]; rw [he]
    simpa [show (2*(z/2)+1)/2=z/2 by omega] using (totalInfo_exactly_one B (z/2)).2.1

theorem evidenceTest_correct (B : Set ℕ) (d : ℕ) :
    evidenceTest (indicator (fun n => n ∈ B)) d = true ↔
      (finiteSet d : Set ℕ) ⊆ totalInfo B := by
  classical
  simp only [evidenceTest, List.all_eq_true, Bool.ite_eq_true_distrib, beq_iff_eq]
  constructor
  · intro h z hz
    rw [totalInfo_parity]
    have ht := h z (by simpa [finiteSet] using hz)
    by_cases he : z%2=0 <;> simpa [he,indicator] using ht
  · intro h z hz
    have ht := (totalInfo_parity B z).mp (h (by simpa [finiteSet] using hz))
    by_cases he : z%2=0 <;> simpa [he,indicator] using ht

private theorem up_of_eq {n : ℕ} {F G : (ℕ → ℕ) → PartialRecursiveFunctions.Args n → ℕ}
    (h : OracleProgramNumberings.UniformPrimitive F) (he : ∀ q v, F q v = G q v) :
    OracleProgramNumberings.UniformPrimitive G := (funext (fun q => funext (he q))) ▸ h

private theorem up_apply {m n : ℕ} (f : PartialRecursiveFunctions.Args m → ℕ) (hf : Primrec f)
    (g : Fin m → (ℕ → ℕ) → PartialRecursiveFunctions.Args n → ℕ)
    (hg : ∀ i, OracleProgramNumberings.UniformPrimitive (g i)) :
    OracleProgramNumberings.UniformPrimitive (fun q v => f (List.Vector.ofFn (fun i => g i q v))) :=
  .comp (OracleProgramNumberings.uniform_ordinary_primitive f (Nat.Primrec'.prim_iff.mpr hf)) hg

private theorem up_precomp {m n : ℕ}
    {F : (ℕ → ℕ) → PartialRecursiveFunctions.Args m → ℕ}
    (h : OracleProgramNumberings.UniformPrimitive F)
    (g : Fin m → PartialRecursiveFunctions.Args n → ℕ) (hg : ∀ i, Primrec (g i)) :
    OracleProgramNumberings.UniformPrimitive (fun q v => F q (List.Vector.ofFn (fun i => g i v))) :=
  .comp h (fun i => OracleProgramNumberings.uniform_ordinary_primitive (g i)
    (Nat.Primrec'.prim_iff.mpr (hg i)))

private theorem get_pr {n : ℕ} (i : Fin n) :
    Primrec (fun v : PartialRecursiveFunctions.Args n => v.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

private def evidenceStep (q : ℕ → ℕ) (v : PartialRecursiveFunctions.Args 3) : ℕ :=
  if v.get 2 = 1 ∧ (if FiniteSequenceCoding.entry (v.get 0) (v.get 1) % 2 = 0
    then q (FiniteSequenceCoding.entry (v.get 0) (v.get 1) / 2) = 1
    else q (FiniteSequenceCoding.entry (v.get 0) (v.get 1) / 2) = 0) then 1 else 0

private theorem evidenceStep_uniform : OracleProgramNumberings.UniformPrimitive evidenceStep := by
  let f (v : PartialRecursiveFunctions.Args 4) : ℕ :=
    if v.get 2 = 1 ∧ (if FiniteSequenceCoding.entry (v.get 0) (v.get 1) % 2 = 0
      then v.get 3 = 1 else v.get 3 = 0) then 1 else 0
  have hentry := FiniteSequenceCoding.primrec_entry.comp (get_pr (0 : Fin 4)) (get_pr 1)
  have he := Primrec.eq.comp (Primrec.nat_mod.comp hentry (Primrec.const 2)) (Primrec.const 0)
  have hb := Primrec.eq.comp (get_pr (3 : Fin 4)) (Primrec.const 1)
  have hz := Primrec.eq.comp (get_pr (3 : Fin 4)) (Primrec.const 0)
  have hc : PrimrecPred (fun v : PartialRecursiveFunctions.Args 4 =>
      if FiniteSequenceCoding.entry (v.get 0) (v.get 1) % 2 = 0 then v.get 3 = 1 else v.get 3 = 0) :=
    ((he.and hb).or (he.not.and hz)).of_eq (fun _ => by simp only [ite_prop_iff_or])
  have hp : Primrec f := Primrec.ite ((Primrec.eq.comp (get_pr 2) (Primrec.const 1)).and hc)
    (Primrec.const 1) (Primrec.const 0)
  let g : Fin 4 → (ℕ → ℕ) → PartialRecursiveFunctions.Args 3 → ℕ :=
    Fin.cases (fun _ v => v.get 0) (Fin.cases (fun _ v => v.get 1)
      (Fin.cases (fun _ v => v.get 2)
        (fun _ q v => q (FiniteSequenceCoding.entry (v.get 0) (v.get 1) / 2))))
  have hg : ∀ i, OracleProgramNumberings.UniformPrimitive (g i) := by
    intro i
    fin_cases i
    · exact .proj 0
    · exact .proj 1
    · exact .proj 2
    · change OracleProgramNumberings.UniformPrimitive
        (fun q (v : PartialRecursiveFunctions.Args 3) => q (FiniteSequenceCoding.entry (v.get 0) (v.get 1) / 2))
      apply up_of_eq (up_precomp OracleProgramNumberings.UniformPrimitive.query
        (fun _ (v : PartialRecursiveFunctions.Args 3) => FiniteSequenceCoding.entry (v.get 0) (v.get 1) / 2)
        (fun _ => Primrec.nat_div.comp (FiniteSequenceCoding.primrec_entry.comp (get_pr 0) (get_pr 1))
          (Primrec.const 2)))
      intro q v
      simp
  exact up_of_eq (up_apply f hp g hg) (fun _ _ => rfl)

private def evidenceRec (q : ℕ → ℕ) (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => evidenceStep q (List.Vector.cons d (List.Vector.cons k
      (List.Vector.cons (evidenceRec q d k) List.Vector.nil)))

private theorem evidenceRec_uniform : OracleProgramNumberings.UniformPrimitive
    (fun q (v : PartialRecursiveFunctions.Args 2) => evidenceRec q (v.get 0) (v.get 1)) := by
  have hbase : OracleProgramNumberings.UniformPrimitive
      (fun _ (_ : PartialRecursiveFunctions.Args 1) => 1) :=
    OracleProgramNumberings.uniform_ordinary_primitive _ (Nat.Primrec'.prim_iff.mpr (Primrec.const 1))
  apply up_of_eq (OracleProgramNumberings.UniformPrimitive.prec hbase evidenceStep_uniform)
  intro q v
  have hr (a : PartialRecursiveFunctions.Args 1) (k : ℕ) :
      PrimitiveRecursion.recValue (fun _ : PartialRecursiveFunctions.Args 1 => 1)
        (fun a j u => evidenceStep q (a ++ List.Vector.cons j (List.Vector.cons u List.Vector.nil))) a k =
      evidenceRec q (a.get 0) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change evidenceStep q (a ++ List.Vector.cons k (List.Vector.cons
        (PrimitiveRecursion.recValue (fun _ : PartialRecursiveFunctions.Args 1 => 1)
          (fun a j u => evidenceStep q (a ++ List.Vector.cons j (List.Vector.cons u List.Vector.nil))) a k)
        List.Vector.nil)) = evidenceStep q (List.Vector.cons (a.get 0)
          (List.Vector.cons k (List.Vector.cons (evidenceRec q (a.get 0) k) List.Vector.nil)))
      rw [ih]
      congr 1
      apply List.Vector.toList_injective
      rcases a with ⟨l,hl⟩
      cases l with
      | nil => simp at hl
      | cons a l =>
        have : l = [] := by simpa using hl
        subst l
        rfl
  simpa [PrimitiveRecursion.lastRec, PrimitiveRecursion.initialPart] using
    hr (PrimitiveRecursion.initialPart v) (v.get 1)

private theorem evidenceRec_correct (q : ℕ → ℕ) (d k : ℕ) (hk : k ≤ FiniteSequenceCoding.length d) :
    evidenceRec q d k = if ((FiniteSequenceCoding.decode d).take k).all (fun z =>
      if z%2=0 then q (z/2)==1 else q (z/2)==0) then 1 else 0 := by
  induction k with
  | zero => simp [evidenceRec]
  | succ k ih =>
    rw [evidenceRec, ih (by omega), List.take_succ_eq_append_getElem (by exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)]
    have hi : k < (FiniteSequenceCoding.decode d).length := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
    simp only [evidenceStep]
    change (if (if ((FiniteSequenceCoding.decode d).take k).all (fun z =>
        if z%2=0 then q (z/2) == 1 else q (z/2) == 0) then 1 else 0) = 1 ∧
        (if FiniteSequenceCoding.entry d k % 2 = 0 then q (FiniteSequenceCoding.entry d k / 2) = 1
        else q (FiniteSequenceCoding.entry d k / 2) = 0) then 1 else 0) = _
    simp only [FiniteSequenceCoding.entry, List.getElem?_eq_getElem hi, Option.getD_some,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true]
    split <;> split <;> split <;> simp_all

private theorem evidenceValue_uniform : OracleProgramNumberings.UniformPrimitive
    (fun q (v : PartialRecursiveFunctions.Args 1) => if evidenceTest q (v.get 0) then 1 else 0) := by
  let g : Fin 2 → PartialRecursiveFunctions.Args 1 → ℕ :=
    Fin.cases (fun v => v.get 0) (fun _ v => FiniteSequenceCoding.length (v.get 0))
  have hg : ∀ i, Primrec (g i) := fun i =>
    Fin.cases (get_pr 0) (fun _ => FiniteSequenceCoding.primrec_length.comp (get_pr 0)) i
  apply up_of_eq (up_precomp evidenceRec_uniform g hg)
  intro q v
  change evidenceRec q (v.get 0) (FiniteSequenceCoding.length (v.get 0)) = _
  simpa [evidenceTest, FiniteSequenceCoding.length] using
    evidenceRec_correct q (v.get 0) (FiniteSequenceCoding.length (v.get 0)) le_rfl

set_option maxHeartbeats 1200000 in
theorem oracleCandidate_uniform :
    OracleProgramNumberings.UniformPrimitive
      (fun q (v : PartialRecursiveFunctions.Args 1) => oracleCandidate q (v.get 0)) := by
  let f (v : PartialRecursiveFunctions.Args 2) : ℕ :=
    let u := v.get 0
    if u.unpair.2.unpair.1 ≤ 1 ∧
      stageCheck u.unpair.1.unpair.1 u.unpair.2.unpair.2.unpair.2
        (Nat.pair (tag u.unpair.1.unpair.2 u.unpair.2.unpair.1) u.unpair.2.unpair.2.unpair.1) = true ∧
      v.get 1 = 1 then 0 else 1
  have hu := Primrec.unpair.comp (get_pr (0 : Fin 2))
  have heu := Primrec.unpair.comp (Primrec.fst.comp hu)
  have hwu := Primrec.unpair.comp (Primrec.snd.comp hu)
  have hdu := Primrec.unpair.comp (Primrec.snd.comp hwu)
  have he := Primrec.fst.comp heu
  have hx := Primrec.snd.comp heu
  have hb := Primrec.fst.comp hwu
  have hd := Primrec.fst.comp hdu
  have ht := Primrec.snd.comp hdu
  have htag := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hx)
    (Primrec.nat_sub.comp (Primrec.const 1) hb)
  have hstage := stageCheck_primitive.comp ((he.pair ht).pair (Primrec₂.natPair.comp htag hd))
  have hf : Primrec f := Primrec.ite ((Primrec.nat_le.comp hb (Primrec.const 1)).and
    ((Primrec.eq.comp hstage (Primrec.const true)).and
      (Primrec.eq.comp (get_pr 1) (Primrec.const 1)))) (Primrec.const 0) (Primrec.const 1)
  let g : Fin 2 → (ℕ → ℕ) → PartialRecursiveFunctions.Args 1 → ℕ :=
    Fin.cases (fun _ v => v.get 0) (fun _ q v => if evidenceTest q (v.get 0).unpair.2.unpair.2.unpair.1 then 1 else 0)
  have hg : ∀ i, OracleProgramNumberings.UniformPrimitive (g i) := by
    intro i
    fin_cases i
    · exact .proj 0
    · apply up_of_eq (up_precomp evidenceValue_uniform
        (fun _ (v : PartialRecursiveFunctions.Args 1) => (v.get 0).unpair.2.unpair.2.unpair.1)
        (fun _ => Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
          (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (get_pr 0))))))))
      intro q v
      rfl
  apply up_of_eq (up_apply f hf g hg)
  intro q v
  simp only [f, g, List.Vector.get_ofFn, Fin.cases_zero, oracleCandidate, tag]
  change (if _ ∧ _ ∧ (if evidenceTest q _ then 1 else 0) = 1 then 0 else 1) = _
  simp only [ite_eq_left_iff, Nat.zero_ne_one, imp_false,
    Bool.and_eq_true, decide_eq_true_eq]
  split <;> simp_all

noncomputable def candidateVectorCode : Code := Classical.choose
  (OracleProgramNumberings.uniform_primitive_program oracleCandidate_uniform)

noncomputable def candidateCode : Code :=
  .comp candidateVectorCode (.pair OracleProgramNumberings.identityCode .zero)

theorem candidateCode_eval (B : Set ℕ) (u : ℕ) :
    OracleComputation.eval B candidateCode u =
      Part.some (oracleCandidate (indicator (fun n => n ∈ B)) u) := by
  have hs := (Classical.choose_spec
    (OracleProgramNumberings.uniform_primitive_program oracleCandidate_uniform)).2 B
    (List.Vector.cons u List.Vector.nil)
  change OracleComputation.eval B candidateVectorCode (Nat.pair u 0) = _ at hs
  simpa only [candidateCode, OracleComputation.eval, OracleProgramNumberings.identity_eval,
    Part.bind_some, Part.map_some, List.Vector.get_zero, List.Vector.head_cons] using hs

/-- Search candidates in numerical order and project the successful bit. -/
noncomputable def decisionMaster : Code :=
  .comp .left (.comp (.find' candidateCode) (.pair OracleProgramNumberings.identityCode .zero))

/-- The ordinary finite program K_e(x)=pair(e,x). -/
def prependCode (e : ℕ) : Nat.Partrec.Code :=
  Nat.Partrec.Code.curry (.pair .left .right) e

noncomputable def decisionCompiler (e : ℕ) : Code :=
  .comp decisionMaster (OracleComputation.embed (prependCode e))

noncomputable def decisionSearch (B : Set ℕ) (e x : ℕ) : Part ℕ :=
  (Nat.rfind (fun w => Part.some (decide
    (oracleCandidate (indicator (fun n => n ∈ B)) (Nat.pair (Nat.pair e x) w) = 0)))).map
      (fun w => w.unpair.1)

theorem prependCode_eval (e x : ℕ) :
    Nat.Partrec.Code.eval (prependCode e) x = Part.some (Nat.pair e x) := by
  simp [prependCode, Nat.Partrec.Code.eval_curry, Nat.Partrec.Code.eval,
    Seq.seq]

theorem decisionCompiler_primitive :
    Primrec (fun e => OracleProgramNumberings.encodeCode (decisionCompiler e)) := by
  have he : ∀ e, OracleComputation.embed (Nat.Partrec.Code.const e) =
      OracleProgramNumberings.constantCode e := by
    intro e
    induction e <;> simp_all [Nat.Partrec.Code.const, OracleComputation.embed,
      OracleProgramNumberings.constantCode]
  have hp := OracleProgramNumberings.compIndex_primitive.comp
    (Primrec.const (OracleProgramNumberings.encodeCode decisionMaster))
    (OracleProgramNumberings.compIndex_primitive.comp
      (Primrec.const (OracleProgramNumberings.encodeCode OracleProgramNumberings.identityCode))
      (OracleProgramNumberings.pairIndex_primitive.comp
        OracleProgramNumberings.constantIndex_primitive
        (Primrec.const (OracleProgramNumberings.encodeCode OracleProgramNumberings.identityCode))))
  apply hp.of_eq
  intro e
  simp only [decisionCompiler, prependCode, Nat.Partrec.Code.curry,
    OracleComputation.embed, Nat.Partrec.Code.id, he,
    OracleProgramNumberings.compIndex, OracleProgramNumberings.pairIndex,
    OracleProgramNumberings.constantIndex, OracleProgramNumberings.identityCode,
    OracleProgramNumberings.encodeCode]

theorem decisionCompiler_eval (B : Set ℕ) (e x : ℕ) :
    OracleComputation.eval B (decisionCompiler e) x = decisionSearch B e x := by
  simp only [decisionCompiler, OracleComputation.eval, OracleComputation.eval_embed,
    prependCode_eval, Part.bind_some, decisionMaster, OracleComputation.eval,
    OracleProgramNumberings.identity_eval, Part.map_some, Nat.unpair_pair, Nat.add_zero,
    candidateCode_eval, Part.map_some, decisionSearch]
  apply Part.ext
  intro y
  simp only [Part.mem_bind_iff, Part.mem_some_iff, Part.mem_map_iff]
  aesop

theorem decisionCompiler_correct (A B : Set ℕ) (e : ℕ)
    (h : operator e (totalInfo B) = totalInfo A) :
    TuringDegrees.Reduces (decisionCompiler e) A B := by
  intro x
  rw [decisionCompiler_eval]
  let b := indicator (fun n => n ∈ A) x
  have hb : b ≤ 1 := by
    classical
    simp only [b,indicator]
    split <;> omega
  have ht : tag x b ∈ operator e (totalInfo B) := by
    rw [h]; exact (tag_bits A x b hb).mpr rfl
  obtain ⟨d,hd,hB⟩ := ht
  obtain ⟨t,ht⟩ := (EffectiveEnumerations.stage_union e (Nat.pair (tag x b) d)).mp hd
  have hw : oracleCandidate (indicator (fun n => n ∈ B))
      (Nat.pair (Nat.pair e x) (Nat.pair b (Nat.pair d t))) = 0 := by
    simp only [oracleCandidate, Nat.unpair_pair, (stageCheck_correct e t _).mpr ht,
      (evidenceTest_correct B d).mpr hB, decide_eq_true hb, Bool.true_and, ↓reduceIte]
  have hdom : (Nat.rfind (fun w => Part.some (decide
      (oracleCandidate (indicator (fun n => n ∈ B)) (Nat.pair (Nat.pair e x) w) = 0)))).Dom := by
    apply Nat.rfind_dom'.mpr
    refine ⟨Nat.pair b (Nat.pair d t), by simp [hw], ?_⟩
    intro m hm; exact Part.some_dom _
  let w := Part.get _ hdom
  have hm := Part.get_mem hdom
  have hs := Nat.rfind_spec hm
  have hsuccess : oracleCandidate (indicator (fun n => n ∈ B)) (Nat.pair (Nat.pair e x) w) = 0 := by
    exact of_decide_eq_true (Part.mem_some_iff.mp hs).symm
  have hp : w.unpair.1 ≤ 1 ∧
      stageCheck e w.unpair.2.unpair.2 (Nat.pair (tag x w.unpair.1) w.unpair.2.unpair.1) = true ∧
      evidenceTest (indicator (fun n => n ∈ B)) w.unpair.2.unpair.1 = true := by
    simp only [oracleCandidate, Nat.unpair_pair] at hsuccess
    split_ifs at hsuccess with hh
    · simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hh
  have hmem : tag x w.unpair.1 ∈ operator e (totalInfo B) :=
    ⟨w.unpair.2.unpair.1,
      (EffectiveEnumerations.stage_union e _).mpr ⟨_, (stageCheck_correct e _ _).mp hp.2.1⟩,
      (evidenceTest_correct B _).mp hp.2.2⟩
  rw [h] at hmem
  have hbit := (tag_bits A x w.unpair.1 hp.1).mp hmem
  apply Part.eq_some_iff.mpr
  change b ∈ (Nat.rfind _).map _
  rw [Part.mem_map_iff]
  exact ⟨w,hm,hbit⟩

theorem totalInfo_reducible_iff (A B : Set ℕ) :
    Reducible (totalInfo A) (totalInfo B) ↔ TuringDegrees.Reducible A B := by
  constructor
  · rintro ⟨e,he⟩
    exact ⟨decisionCompiler e,decisionCompiler_correct A B e he⟩
  · rintro ⟨c,hc⟩
    exact ⟨transcriptIndex (OracleProgramNumberings.encodeCode c),turing_to_enumeration A B c hc⟩

end Lemmatheca.ComputabilityTheory.EnumerationReducibility
