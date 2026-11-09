import Lemmatheca.OracleProgramNumberings.Enumerable

/-! Genuine alternating numerical prefixes over total oracle-decidable matrices. -/
namespace Lemmatheca.ComputabilityTheory.ArithmeticalHierarchy

set_option backward.isDefEq.respectTransparency false

open OracleComputation
namespace FSC
export FiniteSequenceCoding (code decode entry length)
end FSC

abbrev Tuple (k : ℕ) := Fin k → ℕ

def tupleCode {k : ℕ} (v : Tuple k) : ℕ := FSC.code (List.ofFn v)

def tupleDecode (k c : ℕ) : Tuple k := fun i => FSC.entry c i.val

def appendTuple {k n : ℕ} (v : Tuple k) (w : Tuple n) : Tuple (k + n) := Fin.append v w

def snocTuple {k : ℕ} (v : Tuple k) (y : ℕ) : Tuple (k + 1) := Fin.lastCases y v

noncomputable def FiniteDecidable (A : Set ℕ) {k : ℕ} (P : Tuple k → Prop) : Prop :=
  OracleProgramNumberings.RelativeDecidable A {c | P (tupleDecode k c)}

noncomputable def MatrixDecidable (A : Set ℕ) {n : ℕ}
    (R : ℕ → Tuple n → Prop) : Prop :=
  OracleProgramNumberings.RelativeDecidable A
    {w | R w.unpair.1 (tupleDecode n w.unpair.2)}

def quantify : (n : ℕ) → Bool → (Tuple n → Prop) → Prop
  | 0, _, R => R Fin.elim0
  | n + 1, true, R => ∃ y, quantify n false (fun v => R (Fin.cons y v))
  | n + 1, false, R => ∀ y, quantify n true (fun v => R (Fin.cons y v))

noncomputable def Level (A : Set ℕ) (n : ℕ) (p : Bool) (P : ℕ → Prop) : Prop :=
  ∃ R : ℕ → Tuple n → Prop,
    MatrixDecidable A R ∧ ∀ x, P x ↔ quantify n p (R x)

noncomputable def Sigma (A : Set ℕ) (n : ℕ) (P : ℕ → Prop) : Prop := Level A n true P
noncomputable def Pi (A : Set ℕ) (n : ℕ) (P : ℕ → Prop) : Prop := Level A n false P
noncomputable def Delta (A : Set ℕ) (n : ℕ) (P : ℕ → Prop) : Prop :=
  Sigma A n P ∧ Pi A n P

noncomputable def FiniteLevel (A : Set ℕ) (n : ℕ) (p : Bool)
    {k : ℕ} (P : Tuple k → Prop) : Prop := Level A n p (fun c => P (tupleDecode k c))

noncomputable def FiniteDelta (A : Set ℕ) (n : ℕ) {k : ℕ}
    (P : Tuple k → Prop) : Prop := FiniteLevel A n true P ∧ FiniteLevel A n false P

def blockQuantify : List ℕ → Bool → (List ℕ → Prop) → Prop
  | [], _, R => R []
  | k :: ks, true, R => ∃ v : Tuple k,
      blockQuantify ks false (fun rest => R (List.ofFn v ++ rest))
  | k :: ks, false, R => ∀ v : Tuple k,
      blockQuantify ks true (fun rest => R (List.ofFn v ++ rest))

noncomputable def BlockLevel (A : Set ℕ) (ks : List ℕ) (p : Bool)
    (P : ℕ → Prop) : Prop :=
  ∃ R : ℕ → List ℕ → Prop,
    OracleProgramNumberings.RelativeDecidable A {w | R w.unpair.1 (FSC.decode w.unpair.2)} ∧
      ∀ x, P x ↔ blockQuantify ks p (R x)

private theorem rdec_preimage (A : Set ℕ) (S : Set ℕ) (f : ℕ → ℕ)
    (hf : Computable f) (hS : OracleProgramNumberings.RelativeDecidable A S) :
    OracleProgramNumberings.RelativeDecidable A {x | f x ∈ S} := by
  obtain ⟨c, hc⟩ := hS
  obtain ⟨d, hd⟩ := ordinary_inclusion A (Partrec.nat_iff.mp hf.partrec)
  refine ⟨.comp c d, ?_⟩
  funext x
  change (eval A d x).bind (eval A c) = _
  have hdx : eval A d x = Part.some (f x) := by
    simpa only [PFun.coe_val] using congrFun hd x
  rw [hdx, Part.bind_some, congrFun hc]
  rfl

private theorem rdec_congr {A : Set ℕ} {S T : Set ℕ}
    (hS : OracleProgramNumberings.RelativeDecidable A S) (h : ∀ x, x ∈ S ↔ x ∈ T) :
    OracleProgramNumberings.RelativeDecidable A T := by
  have : S = T := Set.ext h
  simpa only [← this] using hS

private theorem rdec_empty (S : Set ℕ) :
    OracleProgramNumberings.RelativeDecidable ∅ S ↔ ComputablePred (fun x => x ∈ S) := by
  classical
  rw [OracleProgramNumberings.RelativeDecidable,
    computable_oracle_iff ∅ ⟨inferInstance, Computable.const false⟩]
  constructor
  · intro h
    apply (UniversalComputation.decidable_iff_characteristic _).mpr
    exact ⟨_, Partrec.nat_iff.mpr h, fun _ => rfl⟩
  · intro h
    obtain ⟨f, hf, he⟩ := (UniversalComputation.decidable_iff_characteristic _).mp h
    have hh : f = UniversalComputation.indicator (fun x => x ∈ S) := funext he
    have hr : Nat.Partrec (fun x => Part.some (f x)) :=
      (Partrec.nat_iff.mp hf.partrec).of_eq (fun _ => rfl)
    simpa only [hh] using hr

private theorem cp_preimage {α β : Type} [Primcodable α] [Primcodable β]
    {P : β → Prop} (hP : ComputablePred P) {f : α → β} (hf : Computable f) :
    ComputablePred (fun x => P (f x)) := by
  obtain ⟨b, hb, rfl⟩ := ComputablePred.computable_iff.mp hP
  exact ⟨inferInstance, by simpa using hb.comp hf⟩

theorem tuple_decode_code {k : ℕ} (v : Tuple k) : tupleDecode k (tupleCode v) = v := by
  funext i
  simp [tupleDecode, tupleCode, FSC.entry]

theorem tuple_decode_surjective (k : ℕ) : Function.Surjective (tupleDecode k) := by
  intro v
  exact ⟨tupleCode v, tuple_decode_code v⟩

theorem tupleCode_primitive (k : ℕ) : Primrec (@tupleCode k) := by
  exact Primrec.encode.comp (Primrec.list_ofFn (fun i =>
    Primrec.fin_app.comp Primrec.id (Primrec.const i)))

theorem tupleDecode_primitive (k : ℕ) : Primrec (tupleDecode k) := by
  apply Primrec.fin_curry.mpr
  exact FiniteSequenceCoding.primrec_entry.comp Primrec.fst
    (Primrec.fin_val.comp Primrec.snd)

theorem tuple_code_zero : tupleCode (Fin.elim0 : Tuple 0) = 0 := by
  rfl

theorem finite_decidable_iff_program (A : Set ℕ) {k : ℕ} (P : Tuple k → Prop) :
    FiniteDecidable A P ↔ ∃ c : Code, ∀ v,
      eval A c (tupleCode v) = Part.some (@ite ℕ (P v) (Classical.propDecidable _) 1 0) := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun v => ?_⟩
    simpa [UniversalComputation.indicator, tuple_decode_code] using congrFun hc (tupleCode v)
  · rintro ⟨c, hc⟩
    let f : ℕ → ℕ := fun z => tupleCode (tupleDecode k z)
    have hf : Primrec f := (tupleCode_primitive k).comp (tupleDecode_primitive k)
    obtain ⟨d, hd⟩ := ordinary_inclusion A (Partrec.nat_iff.mp hf.to_comp.partrec)
    refine ⟨.comp c d, ?_⟩
    funext z
    change (eval A d z).bind (eval A c) = _
    have hdz : eval A d z = Part.some (f z) := by
      simpa only [PFun.coe_val] using congrFun hd z
    rw [hdz, Part.bind_some]
    exact hc (tupleDecode k z)

theorem finite_decidable_empty_iff {k : ℕ} (P : Tuple k → Prop) :
    FiniteDecidable ∅ P ↔ ComputablePred P := by
  rw [FiniteDecidable, rdec_empty]
  constructor
  · intro h
    exact (cp_preimage h (tupleCode_primitive k).to_comp).of_eq (fun v => by simp [tuple_decode_code])
  · intro h
    exact cp_preimage h (tupleDecode_primitive k).to_comp

theorem level_zero_iff (A : Set ℕ) (p : Bool) (P : ℕ → Prop) :
    Level A 0 p P ↔ OracleProgramNumberings.RelativeDecidable A {x | P x} := by
  constructor
  · rintro ⟨R, hR, he⟩
    have hp : Primrec (fun x => Nat.pair x 0) := Primrec₂.natPair.comp Primrec.id (Primrec.const 0)
    apply rdec_congr (rdec_preimage A _ _ hp.to_comp hR)
    intro x
    simp only [Set.mem_ofPred_eq, Nat.unpair_pair]
    have hzero : tupleDecode 0 0 = Fin.elim0 := Subsingleton.elim _ _
    rw [hzero]
    exact (he x).symm
  · intro hP
    refine ⟨fun x _ => P x, ?_, fun _ => Iff.rfl⟩
    exact rdec_preimage A _ _ (Primrec.fst.comp Primrec.unpair).to_comp hP

theorem finite_level_zero_iff (A : Set ℕ) (p : Bool) {k : ℕ} (P : Tuple k → Prop) :
    FiniteLevel A 0 p P ↔ FiniteDecidable A P := by
  exact level_zero_iff A p _

private theorem pr_tuple {α : Type} [Primcodable α] {k : ℕ} {f : α → Tuple k}
    (hf : ∀ i, Primrec (fun x => f x i)) : Primrec f := by
  exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr hf).swap

private theorem pr_cons {α : Type} [Primcodable α] {n : ℕ}
    {a : α → ℕ} {v : α → Tuple n} (ha : Primrec a) (hv : Primrec v) :
    Primrec (fun x : α => (Fin.cons (a x) (v x) : Tuple (n + 1))) := by
  apply pr_tuple
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [Fin.cons_zero] using ha
  · simpa only [Fin.cons_succ, id_eq] using Primrec.fin_app.comp hv (Primrec.const i)

private theorem pr_append {α : Type} [Primcodable α] {k n : ℕ}
    {v : α → Tuple k} {w : α → Tuple n} (hv : Primrec v) (hw : Primrec w) :
    Primrec (fun x => appendTuple (v x) (w x)) := by
  apply pr_tuple
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [appendTuple, Fin.append_left, id_eq] using Primrec.fin_app.comp hv (Primrec.const i)
  · simpa only [appendTuple, Fin.append_right, id_eq] using Primrec.fin_app.comp hw (Primrec.const i)

private theorem matrix_map {A : Set ℕ} {n m : ℕ} {R : ℕ → Tuple n → Prop}
    (hR : MatrixDecidable A R) (f : ℕ → Tuple m → ℕ) (g : ℕ → Tuple m → Tuple n)
    (hf : Primrec (fun w : ℕ => f w.unpair.1 (tupleDecode m w.unpair.2)))
    (hg : Primrec (fun w : ℕ => g w.unpair.1 (tupleDecode m w.unpair.2))) :
    MatrixDecidable A (fun x v => R (f x v) (g x v)) := by
  have hp := Primrec₂.natPair.comp hf ((tupleCode_primitive n).comp hg)
  apply rdec_congr (rdec_preimage A _ _ hp.to_comp hR)
  intro z
  simp only [Set.mem_ofPred_eq, Nat.unpair_pair, tuple_decode_code]

private theorem quantify_congr {n : ℕ} (p : Bool) {R S : Tuple n → Prop}
    (h : ∀ v, R v ↔ S v) : quantify n p R ↔ quantify n p S := by
  induction n generalizing p with
  | zero => exact h _
  | succ n ih =>
    cases p <;> simp only [quantify]
    · exact forall_congr' (fun y => ih _ (fun v => h (Fin.cons y v)))
    · exact exists_congr (fun y => ih _ (fun v => h (Fin.cons y v)))

private theorem level_congr {A : Set ℕ} {n : ℕ} {p : Bool} {P Q : ℕ → Prop}
    (hP : Level A n p P) (h : ∀ x, P x ↔ Q x) : Level A n p Q := by
  obtain ⟨R, hR, he⟩ := hP
  exact ⟨R, hR, fun x => (h x).symm.trans (he x)⟩

private theorem level_ord_preimage {A : Set ℕ} {n : ℕ} {p : Bool} {P : ℕ → Prop}
    (hP : Level A n p P) (f : ℕ → ℕ) (hf : Primrec f) :
    Level A n p (fun x => P (f x)) := by
  obtain ⟨R, hR, he⟩ := hP
  refine ⟨fun x v => R (f x) v, ?_, fun x => he (f x)⟩
  exact matrix_map hR (fun x _ => f x) (fun _ v => v)
    (hf.comp (Primrec.fst.comp Primrec.unpair))
    ((tupleDecode_primitive n).comp (Primrec.snd.comp Primrec.unpair))

private theorem matrix_cons {A : Set ℕ} {n : ℕ} {R : ℕ → Tuple (n + 1) → Prop}
    (hR : MatrixDecidable A R) :
    MatrixDecidable A (fun w v => R w.unpair.1 (Fin.cons w.unpair.2 v)) := by
  exact matrix_map hR (fun w _ => w.unpair.1) (fun w v => Fin.cons w.unpair.2 v)
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
    (pr_cons (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      ((tupleDecode_primitive n).comp (Primrec.snd.comp Primrec.unpair)))

private theorem matrix_uncons {A : Set ℕ} {n : ℕ} {R : ℕ → Tuple n → Prop}
    (hR : MatrixDecidable A R) :
    MatrixDecidable A (fun x (v : Tuple (n + 1)) => R (Nat.pair x (v 0)) (fun i => v i.succ)) := by
  exact matrix_map hR (fun x v => Nat.pair x (v 0)) (fun _ v i => v i.succ)
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
      (FiniteSequenceCoding.primrec_entry.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0)))
    (pr_tuple (fun i => FiniteSequenceCoding.primrec_entry.comp
      (Primrec.snd.comp Primrec.unpair) (Primrec.const i.succ.val)))

theorem sigma_succ_iff (A : Set ℕ) (n : ℕ) (P : ℕ → Prop) :
    Sigma A (n + 1) P ↔ ∃ R : ℕ → ℕ → Prop,
      Pi A n (fun w => R w.unpair.1 w.unpair.2) ∧ ∀ x, P x ↔ ∃ y, R x y := by
  constructor
  · rintro ⟨M, hM, he⟩
    refine ⟨fun x y => quantify n false (fun v => M x (Fin.cons y v)), ?_, ?_⟩
    · exact ⟨fun w v => M w.unpair.1 (Fin.cons w.unpair.2 v), matrix_cons hM, fun _ => Iff.rfl⟩
    · exact he
  · rintro ⟨R, ⟨M, hM, he⟩, hP⟩
    refine ⟨fun x v => M (Nat.pair x (v 0)) (fun i => v i.succ), matrix_uncons hM, ?_⟩
    intro x
    exact (hP x).trans (exists_congr (fun y => by simpa only [Nat.unpair_pair, Fin.cons_zero,
      Fin.cons_succ] using (he (Nat.pair x y))))

theorem pi_succ_iff (A : Set ℕ) (n : ℕ) (P : ℕ → Prop) :
    Pi A (n + 1) P ↔ ∃ R : ℕ → ℕ → Prop,
      Sigma A n (fun w => R w.unpair.1 w.unpair.2) ∧ ∀ x, P x ↔ ∀ y, R x y := by
  constructor
  · rintro ⟨M, hM, he⟩
    refine ⟨fun x y => quantify n true (fun v => M x (Fin.cons y v)), ?_, ?_⟩
    · exact ⟨fun w v => M w.unpair.1 (Fin.cons w.unpair.2 v), matrix_cons hM, fun _ => Iff.rfl⟩
    · exact he
  · rintro ⟨R, ⟨M, hM, he⟩, hP⟩
    refine ⟨fun x v => M (Nat.pair x (v 0)) (fun i => v i.succ), matrix_uncons hM, ?_⟩
    intro x
    exact (hP x).trans (forall_congr' (fun y => by simpa only [Nat.unpair_pair, Fin.cons_zero,
      Fin.cons_succ] using (he (Nat.pair x y))))

theorem finite_matrix_normal_form (A : Set ℕ) (n : ℕ) (p : Bool) {k : ℕ}
    (P : Tuple k → Prop) :
    FiniteLevel A n p P ↔ ∃ R : Tuple (k + n) → Prop,
      FiniteDecidable A R ∧ ∀ x, P x ↔ quantify n p (fun y => R (appendTuple x y)) := by
  constructor
  · rintro ⟨M, hM, he⟩
    let pre : Tuple (k+n) → Tuple k := fun v i => v (i.castAdd n)
    let post : Tuple (k+n) → Tuple n := fun v i => v (i.natAdd k)
    let R : Tuple (k+n) → Prop := fun v => M (tupleCode (pre v)) (post v)
    have hp : Primrec (fun c => pre (tupleDecode (k+n) c)) :=
      pr_tuple (fun i => FiniteSequenceCoding.primrec_entry.comp Primrec.id (Primrec.const (i.castAdd n).val))
    have hs : Primrec (fun c => post (tupleDecode (k+n) c)) :=
      pr_tuple (fun i => FiniteSequenceCoding.primrec_entry.comp Primrec.id (Primrec.const (i.natAdd k).val))
    have hcode := Primrec₂.natPair.comp ((tupleCode_primitive k).comp hp)
      ((tupleCode_primitive n).comp hs)
    refine ⟨R, ?_, fun x => ?_⟩
    · apply rdec_congr (rdec_preimage A _ _ hcode.to_comp hM)
      intro c
      simp only [Set.mem_ofPred_eq, Nat.unpair_pair, tuple_decode_code]
      rfl
    · have hpre (y : Tuple n) : pre (appendTuple x y) = x := by
        funext i
        exact Fin.append_left x y i
      have hpost (y : Tuple n) : post (appendTuple x y) = y := by
        funext i
        exact Fin.append_right x y i
      have hx := he (tupleCode x)
      simp only [tuple_decode_code] at hx
      exact hx.trans (quantify_congr p (fun y => by
        dsimp only [R]
        rw [hpre, hpost]))
  · rintro ⟨R, hR, he⟩
    let M : ℕ → Tuple n → Prop := fun c y => R (appendTuple (tupleDecode k c) y)
    have ha := pr_append ((tupleDecode_primitive k).comp (Primrec.fst.comp Primrec.unpair))
      ((tupleDecode_primitive n).comp (Primrec.snd.comp Primrec.unpair))
    refine ⟨M, ?_, fun c => he (tupleDecode k c)⟩
    apply rdec_congr (rdec_preimage A _ _ ((tupleCode_primitive (k+n)).comp ha).to_comp hR)
    intro c
    simp only [Set.mem_ofPred_eq, tuple_decode_code]
    rfl

theorem unary_finite_bridge (A : Set ℕ) (n : ℕ) (p : Bool) (P : ℕ → Prop) :
    FiniteLevel A n p (fun v : Tuple 1 => P (v 0)) ↔ Level A n p P := by
  constructor
  · intro h
    have hh := level_ord_preimage h (fun x => tupleCode (fun _ : Fin 1 => x))
      ((tupleCode_primitive 1).comp (pr_tuple (fun _ => Primrec.id)))
    exact level_congr hh (fun x => by simp only [tuple_decode_code])
  · intro h
    exact level_ord_preimage h (fun c => tupleDecode 1 c 0)
      (FiniteSequenceCoding.primrec_entry.comp Primrec.id (Primrec.const 0))

private def expandBlocks : (ks : List ℕ) → Tuple ks.length → List ℕ
  | [], _ => []
  | k :: ks, v => List.ofFn (tupleDecode k (v 0)) ++ expandBlocks ks (fun i => v i.succ)

private theorem expandBlocks_primitive (ks : List ℕ) : Primrec (expandBlocks ks) := by
  induction ks with
  | nil => exact Primrec.const []
  | cons k ks ih =>
    have hh : Primrec (fun v : Tuple (k :: ks).length => List.ofFn (tupleDecode k (v 0))) :=
      Primrec.list_ofFn (fun i => FiniteSequenceCoding.primrec_entry.comp
        (Primrec.fin_app.comp Primrec.id (Primrec.const 0)) (Primrec.const i.val))
    have ht : Primrec (fun v : Tuple (k :: ks).length => (fun i : Fin ks.length => v i.succ)) :=
      pr_tuple (fun i => Primrec.fin_app.comp Primrec.id (Primrec.const i.succ))
    exact Primrec.list_append.comp hh (ih.comp ht)

private theorem block_expand (ks : List ℕ) (p : Bool) (R : List ℕ → Prop) :
    blockQuantify ks p R ↔ quantify ks.length p (fun v => R (expandBlocks ks v)) := by
  induction ks generalizing p R with
  | nil => rfl
  | cons k ks ih =>
    cases p
    · change (∀ v : Tuple k, blockQuantify ks true (fun rest => R (List.ofFn v ++ rest))) ↔
        ∀ c : ℕ, quantify ks.length true (fun v => R (expandBlocks (k::ks) (Fin.cons c v)))
      simp only [expandBlocks, Fin.cons_zero, Fin.cons_succ]
      constructor
      · intro h c
        exact (ih true _).mp (h (tupleDecode k c))
      · intro h v
        have hh := h (tupleCode v)
        simp only [tuple_decode_code] at hh
        exact (ih true _).mpr hh
    · change (∃ v : Tuple k, blockQuantify ks false (fun rest => R (List.ofFn v ++ rest))) ↔
        ∃ c : ℕ, quantify ks.length false (fun v => R (expandBlocks (k::ks) (Fin.cons c v)))
      simp only [expandBlocks, Fin.cons_zero, Fin.cons_succ]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨tupleCode v, by simpa only [tuple_decode_code] using (ih false _).mp hv⟩
      · rintro ⟨c, hc⟩
        exact ⟨tupleDecode k c, (ih false _).mpr hc⟩

private theorem decode_cons (n a : ℕ) (s : List ℕ) :
    tupleDecode (n+1) (FSC.code (a::s)) = Fin.cons a (tupleDecode n (FSC.code s)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [tupleDecode, FSC.entry]
  · simp [tupleDecode, FSC.entry]

private theorem singleton_blocks (n : ℕ) (p : Bool) (R : Tuple n → Prop) :
    blockQuantify (List.replicate n 1) p (fun s => R (tupleDecode n (FSC.code s))) ↔
      quantify n p R := by
  induction n generalizing p with
  | zero =>
    change R (tupleDecode 0 (FSC.code [])) ↔ R Fin.elim0
    rw [Subsingleton.elim (tupleDecode 0 (FSC.code [])) Fin.elim0]
  | succ n ih =>
    cases p
    · simp only [List.replicate_succ, blockQuantify, quantify]
      have h (v : Tuple 1) :
          blockQuantify (List.replicate n 1) true
            (fun rest => R (tupleDecode (n+1) (FSC.code (List.ofFn v ++ rest)))) ↔
          quantify n true (fun w => R (Fin.cons (v 0) w)) := by
        simpa only [List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append,
          decode_cons] using ih true (fun w => R (Fin.cons (v 0) w))
      simp_rw [h]
      exact ⟨fun hv y => hv (fun _ => y), fun hy v => hy (v 0)⟩
    · simp only [List.replicate_succ, blockQuantify, quantify]
      have h (v : Tuple 1) :
          blockQuantify (List.replicate n 1) false
            (fun rest => R (tupleDecode (n+1) (FSC.code (List.ofFn v ++ rest)))) ↔
          quantify n false (fun w => R (Fin.cons (v 0) w)) := by
        simpa only [List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append,
          decode_cons] using ih false (fun w => R (Fin.cons (v 0) w))
      simp_rw [h]
      exact ⟨fun ⟨v,hv⟩ => ⟨v 0,hv⟩, fun ⟨y,hy⟩ => ⟨fun _ => y,hy⟩⟩

theorem block_compression (A : Set ℕ) (ks : List ℕ) (p : Bool) (P : ℕ → Prop) :
    BlockLevel A ks p P → Level A ks.length p P := by
  rintro ⟨R, hR, he⟩
  refine ⟨fun x v => R x (expandBlocks ks v), ?_, fun x => (he x).trans (block_expand ks p (R x))⟩
  have hc := Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.encode.comp ((expandBlocks_primitive ks).comp
      ((tupleDecode_primitive ks.length).comp (Primrec.snd.comp Primrec.unpair))))
  apply rdec_congr (rdec_preimage A _ _ hc.to_comp hR)
  intro z
  simp only [Set.mem_ofPred_eq, Nat.unpair_pair, FiniteSequenceCoding.decode_code]

theorem block_normal_form (A : Set ℕ) (n : ℕ) (p : Bool) (P : ℕ → Prop) :
    Level A n p P ↔ ∃ ks : List ℕ, ks.length = n ∧ BlockLevel A ks p P := by
  constructor
  · rintro ⟨M, hM, he⟩
    refine ⟨List.replicate n 1, List.length_replicate, fun x s => M x (tupleDecode n (FSC.code s)), ?_, ?_⟩
    · simpa only [MatrixDecidable, FiniteSequenceCoding.code_decode] using hM
    · intro x
      exact (he x).trans (singleton_blocks n p (M x)).symm
  · rintro ⟨ks, hlen, h⟩
    simpa only [hlen] using block_compression A ks p P h

end Lemmatheca.ComputabilityTheory.ArithmeticalHierarchy
