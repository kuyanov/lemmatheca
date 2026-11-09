import Lemmatheca.ArithmeticalHierarchy.Closure

/-! Actual certificate and search-program bridges at the first level. -/
namespace Lemmatheca.ComputabilityTheory.ArithmeticalHierarchy

open OracleComputation

def searchCode (r : Code) : Code :=
  .comp (.find' (.comp (embed zeroTest) r)) (.pair OracleProgramNumberings.identityCode .zero)

theorem searchCode_eval (A : Set ℕ) (r : Code) (R : ℕ → ℕ → Prop)
    (hr : ∀ x t, eval A r (Nat.pair x t) =
      Part.some (@ite ℕ (R x t) (Classical.propDecidable _) 1 0)) (x : ℕ) :
    eval A (searchCode r) x =
      Nat.rfind (fun t => Part.some (@decide (R x t) (Classical.propDecidable _))) := by
  classical
  have hv (w : ℕ) : eval A (.comp (embed zeroTest) r) w =
      Part.some (if R w.unpair.1 w.unpair.2 then 0 else 1) := by
    change (eval A r w).bind (eval A (embed zeroTest)) = _
    have hw := hr w.unpair.1 w.unpair.2
    rw [Nat.pair_unpair] at hw
    rw [hw, Part.bind_some, eval_embed, zeroTest_eval]
    split <;> simp_all
  change (eval A (.pair OracleProgramNumberings.identityCode .zero) x).bind
    (eval A (.find' (.comp (embed zeroTest) r))) = _
  have hp : eval A (.pair OracleProgramNumberings.identityCode .zero) x =
      Part.some (Nat.pair x 0) := by
    simp [eval, OracleProgramNumberings.identity_eval]
  rw [hp, Part.bind_some, eval]
  simp only [Nat.unpair_pair, Nat.add_zero, hv, Part.map_some]
  change (Nat.rfind (fun t => Part.some (decide ((if R x t then 0 else 1) = 0)))).map
    (fun t => t) = _
  rw [Part.map_id' (fun _ => rfl)]
  congr 1
  funext t
  by_cases ht : R x t <;> simp [ht]

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
  have he : S = T := Set.ext h
  simpa only [← he] using hS

theorem one_matrix_iff (A : Set ℕ) (R : ℕ → ℕ → Prop) :
    MatrixDecidable A (fun x (v : Tuple 1) => R x (v 0)) ↔
      OracleProgramNumberings.RelativeDecidableRelation A R := by
  constructor
  · intro h
    let v (w : ℕ) : Tuple 1 := fun _ => w.unpair.2
    have hv : Primrec v :=
      Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr
        (fun _ => Primrec.snd.comp Primrec.unpair)).swap
    let f (w : ℕ) := Nat.pair w.unpair.1 (tupleCode (v w))
    have hf : Primrec f := Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.unpair) ((tupleCode_primitive 1).comp hv)
    apply rdec_congr (rdec_preimage A _ f hf.to_comp h)
    intro w
    change R (f w).unpair.1 (tupleDecode 1 (f w).unpair.2 0) ↔
      R w.unpair.1 w.unpair.2
    simp only [f, Nat.unpair_pair, tuple_decode_code, v]
  · intro h
    let f (w : ℕ) := Nat.pair w.unpair.1 (tupleDecode 1 w.unpair.2 0)
    have hf : Primrec f := Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
      (FiniteSequenceCoding.primrec_entry.comp
        (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))
    apply rdec_congr (rdec_preimage A _ f hf.to_comp h)
    intro w
    change R (f w).unpair.1 (f w).unpair.2 ↔
      R w.unpair.1 (tupleDecode 1 w.unpair.2 0)
    simp only [f, Nat.unpair_pair]

theorem sigma_one_iff_ce (A : Set ℕ) (P : ℕ → Prop) :
    Sigma A 1 P ↔ OracleProgramNumberings.RelativeCE A {x | P x} := by
  rw [sigma_succ_iff, OracleProgramNumberings.relative_ce_iff_decidable_certificate]
  apply exists_congr
  intro R
  exact and_congr (level_zero_iff A false _) Iff.rfl

theorem pi_one_iff_complement_ce (A : Set ℕ) (P : ℕ → Prop) :
    Pi A 1 P ↔ OracleProgramNumberings.RelativeCE A {x | ¬P x} := by
  exact (level_complement A 1 false P).trans (sigma_one_iff_ce A (fun x => ¬P x))

theorem delta_one_iff_decidable (A : Set ℕ) (P : ℕ → Prop) :
    Delta A 1 P ↔ OracleProgramNumberings.RelativeDecidable A {x | P x} := by
  unfold Delta
  rw [sigma_one_iff_ce, pi_one_iff_complement_ce]
  exact (OracleProgramNumberings.relative_two_sided_recognition A {x | P x}).symm

theorem finite_sigma_one_iff_ce (A : Set ℕ) {k : ℕ} (P : Tuple k → Prop) :
    FiniteLevel A 1 true P ↔
      OracleProgramNumberings.RelativeCE A {c | P (tupleDecode k c)} := by
  exact sigma_one_iff_ce A (fun c => P (tupleDecode k c))

theorem finite_pi_one_iff_complement_ce (A : Set ℕ) {k : ℕ} (P : Tuple k → Prop) :
    FiniteLevel A 1 false P ↔
      OracleProgramNumberings.RelativeCE A {c | ¬P (tupleDecode k c)} := by
  exact pi_one_iff_complement_ce A (fun c => P (tupleDecode k c))

theorem finite_delta_one_iff_decidable (A : Set ℕ) {k : ℕ} (P : Tuple k → Prop) :
    FiniteDelta A 1 P ↔ FiniteDecidable A P := by
  exact delta_one_iff_decidable A (fun c => P (tupleDecode k c))

theorem ordinary_sigma_one_iff_re (P : ℕ → Prop) : Sigma ∅ 1 P ↔ REPred P := by
  rw [sigma_one_iff_ce]
  constructor
  · rintro ⟨c, hc⟩
    apply (UniversalComputation.enumerable_iff_domain P).mpr
    refine ⟨eval ∅ c, (computable_oracle_iff ∅
      ⟨inferInstance, Computable.const false⟩ _).mp ⟨c, rfl⟩, ?_⟩
    exact fun x => Set.ext_iff.mp hc x
  · intro h
    obtain ⟨f, hf, hp⟩ := (UniversalComputation.enumerable_iff_domain P).mp h
    obtain ⟨c, hc⟩ := ordinary_inclusion ∅ hf
    refine ⟨c, Set.ext fun x => ?_⟩
    change P x ↔ (eval ∅ c x).Dom
    rw [congrFun hc x]
    exact hp x

end Lemmatheca.ComputabilityTheory.ArithmeticalHierarchy
