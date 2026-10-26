import Lemmatheca.OracleProgramNumberings.Universal

/-! Relative domains, certificates and the actual uniform race program. -/
namespace Lemmatheca.ComputabilityTheory.OracleProgramNumberings

open OracleComputation
open PartialRecursiveFunctions (Args)

set_option backward.isDefEq.respectTransparency false

noncomputable def relativeDomain (A : Set ℕ) (e : ℕ) : Set ℕ :=
  {x | (phi A e x).Dom}

noncomputable def RelativeCE (A S : Set ℕ) : Prop :=
  ∃ c : Code, S = {x | (eval A c x).Dom}

noncomputable def RelativeDecidable (A S : Set ℕ) : Prop :=
  PartialComputable A (fun x => Part.some (UniversalComputation.indicator (fun n => n ∈ S) x))

noncomputable def RelativePrimitivePredicate {n : ℕ} (A : Set ℕ)
    (R : Args n → Prop) : Prop :=
  RelativePrimitive A (fun v => @ite ℕ (R v) (Classical.propDecidable _) 1 0)

noncomputable def RelativePrimitiveRelation (A : Set ℕ) (R : ℕ → ℕ → Prop) : Prop :=
  RelativePrimitivePredicate A (fun v : Args 2 => R (v.get 0) (v.get 1))

noncomputable def RelativeDecidableRelation (A : Set ℕ) (R : ℕ → ℕ → Prop) : Prop :=
  PartialComputable A
    (fun w => Part.some (UniversalComputation.indicator (fun z => R z.unpair.1 z.unpair.2) w))

noncomputable def certificate (A : Set ℕ) (e x k : ℕ) : Prop :=
  0 < boundedValue A k e x

def raceFirstInput : Code :=
  .pair .right (.pair (.comp .left .left) (.comp .right (.comp .right .left)))

def raceSecondInput : Code := .pair .right (.comp .right .left)

noncomputable def raceValues : Code :=
  .pair (.comp boundedCode raceFirstInput) (.comp boundedCode raceSecondInput)

def raceFailure (w : ℕ) : ℕ :=
  if w.unpair.1 = 0 ∧ w.unpair.2 = 0 then 1 else 0

theorem raceFailure_primitive : Nat.Primrec raceFailure := by
  apply Primrec.nat_iff.mp
  exact Primrec.ite (PrimrecPred.and
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0))
    (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0)))
      (Primrec.const 1) (Primrec.const 0)

noncomputable def raceTest : Code :=
  .comp (embed (ordinaryCode raceFailure raceFailure_primitive)) raceValues

noncomputable def raceAllowanceSearch : Code :=
  .comp (.find' raceTest) (.pair identityCode .zero)

def positiveFirstCode : Code := .comp (embed zeroTest) (.comp (embed zeroTest) .left)

noncomputable def raceCode : Code :=
  .comp positiveFirstCode
    (.comp raceValues (.pair identityCode raceAllowanceSearch))

noncomputable def firstRaceAllowance (A : Set ℕ) (e d x : ℕ) : Part ℕ :=
  Nat.rfind (fun k => Part.some
    (decide (0 < boundedValue A k e x ∨ 0 < boundedValue A k d x)))

theorem relative_ce_iff_index (A S : Set ℕ) :
    RelativeCE A S ↔ ∃ e, S = relativeDomain A e := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨encodeCode c, by simpa only [relativeDomain, phi, decode_encode] using hc⟩
  · rintro ⟨e, he⟩
    exact ⟨decodeCode e, he⟩

theorem relative_primitive_relation_decidable (A : Set ℕ) (R : ℕ → ℕ → Prop)
    (hR : RelativePrimitiveRelation A R) : RelativeDecidableRelation A R := by
  classical
  obtain ⟨c, hc⟩ := relative_primitive_program A _ hR
  refine ⟨.comp c (.pair .left (.pair .right .zero)), ?_⟩
  funext w
  let v : Args 2 := List.Vector.ofFn (Fin.cases w.unpair.1 (fun _ => w.unpair.2))
  have hv := hc v
  change eval A c (Nat.pair w.unpair.1 (Nat.pair w.unpair.2 0)) =
    Part.some (if R w.unpair.1 w.unpair.2 then 1 else 0) at hv
  simpa only [eval, Part.bind_some, Part.map_some, UniversalComputation.indicator] using hv

private theorem uniform_precomp {m n : ℕ} {F : (ℕ → ℕ) → Args m → ℕ}
    (hF : UniformPrimitive F) (g : Fin m → Args n → ℕ) (hg : ∀ i, Primrec (g i)) :
    UniformPrimitive (fun q v => F q (List.Vector.ofFn (fun i => g i v))) :=
  .comp hF (fun i => uniform_ordinary_primitive (g i) (Nat.Primrec'.prim_iff.mpr (hg i)))

theorem certificate_relative_primitive (A : Set ℕ) (e : ℕ) :
    RelativePrimitiveRelation A (fun x k => certificate A e x k) := by
  classical
  let g : Fin 3 → Args 2 → ℕ := Fin.cases (fun v => v.get 1)
    (Fin.cases (fun _ => e) (fun _ v => v.get 0))
  have hg : ∀ i, Primrec (g i) := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) i
    · exact Primrec.vector_get.comp Primrec.id (Primrec.const 1)
    · exact Primrec.const e
    · exact Primrec.vector_get.comp Primrec.id (Primrec.const 0)
  have hb := uniform_precomp boundedFamily_primitive g hg
  let positive (v : Args 1) : ℕ := if 0 < v.get 0 then 1 else 0
  have hp : Primrec positive := Primrec.ite
    (Primrec.nat_lt.comp (Primrec.const 0)
      (Primrec.vector_get.comp Primrec.id (Primrec.const 0)))
    (Primrec.const 1) (Primrec.const 0)
  have hs := UniformPrimitive.comp
    (uniform_ordinary_primitive positive (Nat.Primrec'.prim_iff.mpr hp)) (fun _ : Fin 1 => hb)
  refine ⟨_, hs, ?_⟩
  funext v
  simp [positive, boundedFamily, g, certificate, tableValue_correct]
  rfl

private theorem decidable_certificate_program (A : Set ℕ) (R : ℕ → ℕ → Prop)
    (hR : RelativeDecidableRelation A R) :
    ∃ c : Code, ∀ x, (eval A c x).Dom ↔ ∃ t, R x t := by
  classical
  obtain ⟨c, hc⟩ := hR
  let d : Code := .comp (.find' (.comp (embed zeroTest) c)) (.pair identityCode .zero)
  refine ⟨d, fun x => ?_⟩
  have hv (w : ℕ) : eval A (.comp (embed zeroTest) c) w =
      Part.some (if R w.unpair.1 w.unpair.2 then 0 else 1) := by
    change (eval A c w).bind (eval A (embed zeroTest)) = _
    rw [congrFun hc w, Part.bind_some, eval_embed, zeroTest_eval]
    simp [UniversalComputation.indicator]
  have he : eval A d x = Nat.rfind (fun t => Part.some (decide (R x t))) := by
    change (eval A (.pair identityCode .zero) x).bind
      (eval A (.find' (.comp (embed zeroTest) c))) = _
    have hp : eval A (.pair identityCode .zero) x = Part.some (Nat.pair x 0) := by
      simp [eval, identity_eval]
    rw [hp, Part.bind_some, eval]
    simp only [Nat.unpair_pair, Nat.add_zero, hv, Part.map_some]
    change (Nat.rfind (fun t => Part.some (decide ((if R x t then 0 else 1) = 0)))).map
      (fun t => t) = _
    rw [Part.map_id' (fun _ => rfl)]
    congr 1
    funext t
    by_cases ht : R x t <;> simp [ht]
  rw [he, Nat.rfind_dom]
  simp

theorem relative_ce_iff_primitive_certificate (A S : Set ℕ) :
    RelativeCE A S ↔ ∃ R : ℕ → ℕ → Prop,
      RelativePrimitiveRelation A R ∧ ∀ x, x ∈ S ↔ ∃ t, R x t := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := (relative_ce_iff_index A S).mp h
    exact ⟨certificate A e, certificate_relative_primitive A e,
      fun x => phi_domain_certificate A e x⟩
  · rintro ⟨R, hR, hS⟩
    obtain ⟨c, hc⟩ := decidable_certificate_program A R
      (relative_primitive_relation_decidable A R hR)
    exact ⟨c, Set.ext fun x => (hS x).trans (hc x).symm⟩

theorem relative_ce_iff_decidable_certificate (A S : Set ℕ) :
    RelativeCE A S ↔ ∃ R : ℕ → ℕ → Prop,
      RelativeDecidableRelation A R ∧ ∀ x, x ∈ S ↔ ∃ t, R x t := by
  constructor
  · intro h
    obtain ⟨R, hR, hS⟩ := (relative_ce_iff_primitive_certificate A S).mp h
    exact ⟨R, relative_primitive_relation_decidable A R hR, hS⟩
  · rintro ⟨R, hR, hS⟩
    obtain ⟨c, hc⟩ := decidable_certificate_program A R hR
    exact ⟨c, Set.ext fun x => (hS x).trans (hc x).symm⟩

private theorem race_values_eval (A : Set ℕ) (e d x k : ℕ) :
    eval A raceValues (Nat.pair (Nat.pair e (Nat.pair d x)) k) =
      Part.some (Nat.pair (boundedValue A k e x) (boundedValue A k d x)) := by
  simp only [raceValues, raceFirstInput, raceSecondInput, eval, Nat.unpair_pair,
    Part.bind_some, Part.map_some, bounded_code_eval]

private theorem race_test_eval (A : Set ℕ) (e d x k : ℕ) :
    eval A raceTest (Nat.pair (Nat.pair e (Nat.pair d x)) k) =
      Part.some (if boundedValue A k e x = 0 ∧ boundedValue A k d x = 0 then 1 else 0) := by
  change (eval A raceValues _).bind (eval A (embed _)) = _
  rw [race_values_eval, Part.bind_some, eval_embed, ordinaryCode_eval]
  simp only [raceFailure, Nat.unpair_pair]

private theorem race_search_eval (A : Set ℕ) (e d x : ℕ) :
    eval A raceAllowanceSearch (Nat.pair e (Nat.pair d x)) = firstRaceAllowance A e d x := by
  simp only [raceAllowanceSearch, eval, identity_eval, Part.map_some, Part.bind_some,
    Nat.unpair_pair, Nat.add_zero, race_test_eval, Part.map_some]
  change (Nat.rfind (fun k => Part.some (decide
    ((if boundedValue A k e x = 0 ∧ boundedValue A k d x = 0 then 1 else 0) = 0)))).map
      (fun j => j) = _
  rw [Part.map_id' (fun _ => rfl)]
  congr 1
  funext k
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  split <;> omega

private theorem positive_first_eval (A : Set ℕ) (w : ℕ) :
    eval A positiveFirstCode w = Part.some (if 0 < w.unpair.1 then 1 else 0) := by
  simp only [positiveFirstCode, eval, Part.bind_some, eval_embed, zeroTest_eval]
  split <;> simp_all

theorem race_code_eval (A : Set ℕ) (e d x : ℕ) :
    eval A raceCode (Nat.pair e (Nat.pair d x)) =
      (firstRaceAllowance A e d x).map
        (fun k => if 0 < boundedValue A k e x then 1 else 0) := by
  change (((eval A identityCode (Nat.pair e (Nat.pair d x))).bind fun u =>
    (eval A raceAllowanceSearch (Nat.pair e (Nat.pair d x))).map (Nat.pair u)).bind
      (eval A raceValues)).bind (eval A positiveFirstCode) = _
  rw [identity_eval, race_search_eval, Part.bind_some]
  simp only [Part.bind_map, race_values_eval, positive_first_eval,
    Nat.unpair_pair, Part.bind_some_eq_map]

theorem race_code_domain (A : Set ℕ) (e d x : ℕ) :
    (eval A raceCode (Nat.pair e (Nat.pair d x))).Dom ↔
      (phi A e x).Dom ∨ (phi A d x).Dom := by
  rw [race_code_eval]
  change (firstRaceAllowance A e d x).Dom ↔ _
  unfold firstRaceAllowance
  rw [Nat.rfind_dom, phi_domain_certificate, phi_domain_certificate]
  simp [exists_or]

theorem race_on_complements (A S : Set ℕ) (e d : ℕ)
    (he : relativeDomain A e = S) (hd : relativeDomain A d = Sᶜ) (x : ℕ) :
    eval A raceCode (Nat.pair e (Nat.pair d x)) =
      Part.some (UniversalComputation.indicator (fun n => n ∈ S) x) := by
  classical
  have hE : (phi A e x).Dom ↔ x ∈ S := by
    change x ∈ relativeDomain A e ↔ _
    rw [he]
  have hD : (phi A d x).Dom ↔ x ∉ S := by
    change x ∈ relativeDomain A d ↔ _
    rw [hd]
    rfl
  have hh : (eval A raceCode (Nat.pair e (Nat.pair d x))).Dom :=
    (race_code_domain A e d x).mpr (by
      by_cases hx : x ∈ S
      · exact Or.inl (hE.mpr hx)
      · exact Or.inr (hD.mpr hx))
  rw [race_code_eval] at hh ⊢
  change (firstRaceAllowance A e d x).Dom at hh
  obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp hh
  have hp : 0 < boundedValue A k e x ∨ 0 < boundedValue A k d x := by
    exact of_decide_eq_true (Part.mem_some_iff.mp (Nat.rfind_spec hk)).symm
  have hepos : 0 < boundedValue A k e x → x ∈ S := fun hv =>
    hE.mp ((phi_domain_certificate A e x).mpr ⟨k, hv⟩)
  have hdpos : 0 < boundedValue A k d x → x ∉ S := fun hv =>
    hD.mp ((phi_domain_certificate A d x).mpr ⟨k, hv⟩)
  apply Part.eq_some_iff.mpr
  rw [Part.mem_map_iff]
  refine ⟨k, hk, ?_⟩
  unfold UniversalComputation.indicator
  split_ifs <;> aesop

theorem relative_two_sided_recognition (A S : Set ℕ) :
    RelativeDecidable A S ↔ RelativeCE A S ∧ RelativeCE A Sᶜ := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    have hr : RelativeDecidableRelation A (fun x _ => x ∈ S) := by
      refine ⟨.comp c .left, ?_⟩
      funext w
      simp only [eval, Part.bind_some, congrFun hc, UniversalComputation.indicator]
    have hrc : RelativeDecidableRelation A (fun x _ => x ∈ Sᶜ) := by
      refine ⟨.comp (embed zeroTest) (.comp c .left), ?_⟩
      funext w
      simp only [eval, Part.bind_some, congrFun hc, eval_embed, zeroTest_eval]
      simp [UniversalComputation.indicator]
    constructor
    · exact (relative_ce_iff_decidable_certificate A S).mpr
        ⟨fun x _ => x ∈ S, hr, fun _ => by simp⟩
    · exact (relative_ce_iff_decidable_certificate A Sᶜ).mpr
        ⟨fun x _ => x ∈ Sᶜ, hrc, fun _ => by simp⟩
  · rintro ⟨hS, hSc⟩
    obtain ⟨e, he⟩ := (relative_ce_iff_index A S).mp hS
    obtain ⟨d, hd⟩ := (relative_ce_iff_index A Sᶜ).mp hSc
    let input : Code := .pair (constantCode e) (.pair (constantCode d) identityCode)
    refine ⟨.comp raceCode input, ?_⟩
    funext x
    change (eval A input x).bind (eval A raceCode) = _
    have hi : eval A input x = Part.some (Nat.pair e (Nat.pair d x)) := by
      simp only [input, eval, constant_eval, identity_eval, Part.map_some, Part.bind_some]
    rw [hi, Part.bind_some, race_on_complements A S e d he.symm hd.symm x]

end Lemmatheca.ComputabilityTheory.OracleProgramNumberings
