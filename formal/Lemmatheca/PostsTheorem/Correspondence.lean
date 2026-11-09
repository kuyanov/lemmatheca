import Lemmatheca.PostsTheorem.FiniteCertificates
import Lemmatheca.ArithmeticalHierarchy.FirstLevel
import Lemmatheca.TuringJump.Degrees

/-! Absorption, finite-arity recoding and Post's genuine quantifier-class equivalences. -/
namespace Lemmatheca.ComputabilityTheory.PostsTheorem

open OracleComputation OracleProgramNumberings ArithmeticalHierarchy TuringJump TuringDegrees

set_option backward.isDefEq.respectTransparency false

private theorem level_congr {B : Set ℕ} {n : ℕ} {p : Bool} {P Q : ℕ → Prop}
    (hP : Level B n p P) (h : ∀ x, P x ↔ Q x) : Level B n p Q := by
  obtain ⟨R, hR, he⟩ := hP
  exact ⟨R, hR, fun x => (h x).symm.trans (he x)⟩

private theorem ci_of_comp (B : Set ℕ) {f : ℕ → ℕ} (hf : Computable f) :
    ComputableIn B f := by
  exact ordinary_inclusion B (Partrec.nat_iff.mp hf.partrec)

private theorem rdec_of_pred (B : Set ℕ) {P : ℕ → Prop} (hP : ComputablePred P) :
    RelativeDecidable B {x | P x} := by
  obtain ⟨r, _, hr⟩ := computable_uniform {x | P x} hP
  exact ⟨embed r, funext (hr B)⟩

private theorem level_decidable (B : Set ℕ) (n : ℕ) (p : Bool) (P : ℕ → Prop)
    (hP : RelativeDecidable B {x | P x}) : Level B n p P := by
  induction n with
  | zero => exact (level_zero_iff B p P).mpr hP
  | succ n ih => exact level_padding B n p p P ih

private theorem level_ordinary (B : Set ℕ) (n : ℕ) (p : Bool) (P : ℕ → Prop)
    (hP : ComputablePred P) : Level B n p P :=
  level_decidable B n p P (rdec_of_pred B hP)

private theorem agreement_level (B A : Set ℕ) (n : ℕ) (p : Bool)
    (hA : Level B n p A) (hAc : Level B n p (fun q => q ∉ A)) :
    Level B n p (fun w => Agreement w.unpair.1 w.unpair.2 A) := by
  classical
  have hu : Primrec (fun z : ℕ => z.unpair.1.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair)
  have hq : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hbeta := beta_primitive.comp hu hq
  have hbit (b : ℕ) : Level B n p (fun z => beta z.unpair.1.unpair.1 z.unpair.2 = b) :=
    level_ordinary B n p _ ((Primrec.eq.comp hbeta (Primrec.const b)).computablePred)
  have hpos := computable_preimage B n p A (fun z => z.unpair.2)
    (ci_of_comp B hq.to_comp) hA
  have hneg := computable_preimage B n p (fun q => q ∉ A) (fun z => z.unpair.2)
    (ci_of_comp B hq.to_comp) hAc
  have heq : Level B n p (fun z =>
      beta z.unpair.1.unpair.1 z.unpair.2 =
        UniversalComputation.indicator (fun q => q ∈ A) z.unpair.2) := by
    apply level_congr (level_or B n p _ _
      (level_and B n p _ _ (hbit 1) hpos) (level_and B n p _ _ (hbit 0) hneg))
    intro z
    rcases beta_bits z.unpair.1.unpair.1 z.unpair.2 with hb | hb <;>
      by_cases ha : z.unpair.2 ∈ A <;> simp [UniversalComputation.indicator, hb, ha]
    all_goals exact ha
  exact bounded_forall B n p
    (fun w q => beta w.unpair.1 q = UniversalComputation.indicator (fun t => t ∈ A) q)
    (fun w => w.unpair.2) (ci_of_comp B hq.to_comp) heq

theorem agreement_delta (B A : Set ℕ) (n : ℕ) (hA : Sigma B n A) :
    Delta B (n + 1) (fun w => Agreement w.unpair.1 w.unpair.2 A) := by
  have hAc := (level_complement B n true A).mp hA
  exact ⟨agreement_level B A (n + 1) true
      (level_padding B n true true A hA) (level_padding B n false true _ hAc),
    agreement_level B A (n + 1) false
      (level_padding B n true false A hA) (level_padding B n false false _ hAc)⟩

theorem agreement_decidable (B A : Set ℕ) (hA : RelativeDecidable B A) :
    RelativeDecidable B {w | Agreement w.unpair.1 w.unpair.2 A} := by
  have hpos := (level_zero_iff B true A).mpr hA
  have hneg := (level_complement B 0 false A).mp ((level_zero_iff B false A).mpr hA)
  exact (level_zero_iff B true _).mp (agreement_level B A 0 true hpos hneg)

theorem oracle_absorption (B A S : Set ℕ) (n : ℕ)
    (hA : Sigma B n A) (hS : RelativeCE A S) : Sigma B (n + 1) S := by
  obtain ⟨e, rfl⟩ := (relative_ce_iff_index A S).mp hS
  have hag : Sigma B (n + 1) (fun w => Agreement w.unpair.1 w.unpair.2 A) := by
    cases n with
    | zero =>
      exact level_decidable B 1 true _
        (agreement_decidable B A ((level_zero_iff B true A).mp hA))
    | succ n => exact (agreement_delta B A (n + 1) hA).1
  have hx : Primrec (fun w : ℕ => w.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hv : Primrec (fun w : ℕ => w.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hu : Primrec (fun w : ℕ => w.unpair.2.unpair.1) := hx.comp hv
  have hk : Primrec (fun w : ℕ => w.unpair.2.unpair.2) := hv.comp hv
  have hpack : Primrec (fun w : ℕ => pack4 w.unpair.2.unpair.1 w.unpair.2.unpair.2 e w.unpair.1) :=
    Primrec₂.natPair.comp hu (Primrec₂.natPair.comp hk
      (Primrec₂.natPair.comp (Primrec.const e) hx))
  have hval : Primrec (fun w : ℕ => finiteValue w.unpair.2.unpair.1 w.unpair.2.unpair.2 e w.unpair.1) :=
    (finiteValue_primitive.comp hpack).of_eq (fun w => by
      simp only [finiteValueInput, pack4, Nat.unpair_pair])
  have hcheck : Level B (n + 1) true (fun w =>
      finiteCheck w.unpair.2.unpair.1 w.unpair.2.unpair.2 e w.unpair.1) :=
    level_ordinary B (n + 1) true _
      ((Primrec.nat_lt.comp (Primrec.const 0) hval).computablePred)
  have hag' := computable_preimage B (n + 1) true _ (fun w => w.unpair.2)
    (ci_of_comp B hv.to_comp) hag
  have hboth := level_and B (n + 1) true _ _ hcheck hag'
  have hex := positive_exists B (n + 1) (by omega)
    (fun x v => finiteCheck v.unpair.1 v.unpair.2 e x ∧ Agreement v.unpair.1 v.unpair.2 A) hboth
  apply level_congr hex
  intro x
  change (∃ v : ℕ, finiteCheck v.unpair.1 v.unpair.2 e x ∧ Agreement v.unpair.1 v.unpair.2 A) ↔
    (phi A e x).Dom
  constructor
  · rintro ⟨v, hc, ha⟩
    exact (finite_certificate_domain A e x).mpr ⟨v.unpair.1, v.unpair.2, hc, ha⟩
  · intro h
    obtain ⟨u, k, hc, ha⟩ := (finite_certificate_domain A e x).mp h
    exact ⟨Nat.pair u k, by simpa only [Nat.unpair_pair] using And.intro hc ha⟩

theorem finite_oracle_absorption (B A : Set ℕ) (n : ℕ) {k : ℕ}
    (P : Tuple k → Prop) (hA : Sigma B n A)
    (hP : RelativeCE A {c | P (tupleDecode k c)}) : FiniteLevel B (n + 1) true P := by
  exact oracle_absorption B A {c | P (tupleDecode k c)} n hA hP

def normalizeTuple (k c : ℕ) : ℕ := tupleCode (tupleDecode k c)

theorem normalizeTuple_primitive (k : ℕ) : Nat.Primrec (normalizeTuple k) := by
  exact Primrec.nat_iff.mp ((tupleCode_primitive k).comp (tupleDecode_primitive k))

noncomputable def normalizeTupleCode (k : ℕ) : Code :=
  embed (ordinaryCode (normalizeTuple k) (normalizeTuple_primitive k))

theorem normalizeTuple_eval (A : Set ℕ) (k c : ℕ) :
    eval A (normalizeTupleCode k) c = Part.some (tupleCode (tupleDecode k c)) := by
  rw [normalizeTupleCode, eval_embed, ordinaryCode_eval]
  rfl

theorem finite_ce_iff_program (A : Set ℕ) {k : ℕ} (P : Tuple k → Prop) :
    RelativeCE A {c | P (tupleDecode k c)} ↔
      ∃ c : Code, ∀ v, P v ↔ (eval A c (tupleCode v)).Dom := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun v => ?_⟩
    have hv := Set.ext_iff.mp hc (tupleCode v)
    simpa only [Set.mem_ofPred_eq, tuple_decode_code] using hv
  · rintro ⟨c, hc⟩
    refine ⟨.comp c (normalizeTupleCode k), Set.ext fun x => ?_⟩
    change P (tupleDecode k x) ↔ (eval A (.comp c (normalizeTupleCode k)) x).Dom
    rw [eval, normalizeTuple_eval, Part.bind_some]
    exact hc (tupleDecode k x)

theorem sigma_iff_ce (B : Set ℕ) (n : ℕ) (S : Set ℕ) :
    Sigma B (n + 1) S ↔ RelativeCE (iterate B n) S := by
  classical
  induction n generalizing S with
  | zero => exact sigma_one_iff_ce B S
  | succ n ih =>
      have hj : Sigma B (n + 1) (iterate B (n + 1)) :=
        (ih (iterate B (n + 1))).mpr (jump_ce (iterate B n))
      constructor
      · intro hs
        obtain ⟨R, hR, hp⟩ := (sigma_succ_iff B (n + 1) S).mp hs
        let Q : Set ℕ := {w | ¬R w.unpair.1 w.unpair.2}
        have hQ : Sigma B (n + 1) Q :=
          (level_complement B (n + 1) false _).mp hR
        have hc : RelativeCE (iterate B n) Q := (ih Q).mp hQ
        have hm : ManyOneReducible Q (iterate B (n + 1)) :=
          (relative_ce_iff_jump (iterate B n) Q).mp hc
        have hd : Reducible Q (iterate B (n + 1)) := manyOne_imp_reducible hm
        have hr : RelativeDecidable (iterate B (n + 1)) Qᶜ :=
          (relative_decidable_iff_reducible _ _).mpr
            (reducible_trans (complement_equivalent Q).2 hd)
        have he : Qᶜ = {w | R w.unpair.1 w.unpair.2} := by
          ext w
          change (¬¬R w.unpair.1 w.unpair.2) ↔ R w.unpair.1 w.unpair.2
          exact not_not
        rw [he] at hr
        exact (relative_ce_iff_decidable_certificate (iterate B (n + 1)) S).mpr
          ⟨R, hr, hp⟩
      · intro hs
        exact oracle_absorption B (iterate B (n + 1)) S (n + 1) hj hs

theorem iterate_sigma (B : Set ℕ) (n : ℕ) : Sigma B n (iterate B n) := by
  cases n with
  | zero => exact (level_zero_iff B true B).mpr ⟨.query, rfl⟩
  | succ n => exact (sigma_iff_ce B n (iterate B (n + 1))).mpr (jump_ce (iterate B n))

theorem sigma_iff_manyOne (B : Set ℕ) (n : ℕ) (S : Set ℕ) :
    Sigma B (n + 1) S ↔ ManyOneReducible S (iterate B (n + 1)) := by
  exact (sigma_iff_ce B n S).trans (relative_ce_iff_jump (iterate B n) S)

theorem delta_iff_reducible (B : Set ℕ) (n : ℕ) (S : Set ℕ) :
    Delta B (n + 1) S ↔ Reducible S (iterate B n) := by
  have hpi : Pi B (n + 1) S ↔ RelativeCE (iterate B n) Sᶜ :=
    (level_complement B (n + 1) false S).trans (sigma_iff_ce B n Sᶜ)
  change (Sigma B (n + 1) S ∧ Pi B (n + 1) S) ↔ _
  rw [sigma_iff_ce, hpi, ← relative_two_sided_recognition]
  exact relative_decidable_iff_reducible (iterate B n) S

theorem finite_sigma_iff_ce (B : Set ℕ) (n : ℕ) {k : ℕ} (P : Tuple k → Prop) :
    FiniteLevel B (n + 1) true P ↔ RelativeCE (iterate B n) {c | P (tupleDecode k c)} := by
  exact sigma_iff_ce B n {c | P (tupleDecode k c)}

theorem finite_sigma_iff_manyOne (B : Set ℕ) (n : ℕ) {k : ℕ} (P : Tuple k → Prop) :
    FiniteLevel B (n + 1) true P ↔
      ManyOneReducible (fun c => P (tupleDecode k c)) (iterate B (n + 1)) := by
  exact sigma_iff_manyOne B n {c | P (tupleDecode k c)}

theorem finite_delta_iff_decidable (B : Set ℕ) (n : ℕ) {k : ℕ} (P : Tuple k → Prop) :
    FiniteDelta B (n + 1) P ↔ FiniteDecidable (iterate B n) P := by
  exact (delta_iff_reducible B n {c | P (tupleDecode k c)}).trans
    (relative_decidable_iff_reducible (iterate B n) {c | P (tupleDecode k c)}).symm

end Lemmatheca.ComputabilityTheory.PostsTheorem
