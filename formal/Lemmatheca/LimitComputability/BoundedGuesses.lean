import Lemmatheca.LimitComputability.Approximation
import Lemmatheca.PostsTheorem.FiniteCertificates

/-! Ordinary finite-stage substitution into the actual bounded oracle evaluator. -/
namespace Lemmatheca.ComputabilityTheory.LimitComputability

open UniversalComputation OracleComputation OracleProgramNumberings
open PartialRecursiveFunctions (Args)

noncomputable section

set_option backward.isDefEq.respectTransparency false

def haltingIndex : ℕ :=
  Classical.choose ((enumerable_iff_index haltingDiagonal).mp haltingDiagonal_enumerable)

theorem halting_index_spec (x : ℕ) :
    x ∈ haltingDiagonal ↔ (UniversalComputation.phi haltingIndex x).Dom := by
  exact Classical.choose_spec ((enumerable_iff_index haltingDiagonal).mp haltingDiagonal_enumerable) x

def haltingStage (s : ℕ) : Set ℕ := EffectiveEnumerations.stage haltingIndex s

def haltingTest (s x : ℕ) : ℕ := EffectiveEnumerations.stageTest haltingIndex s x

theorem halting_stage_data :
    Primrec₂ haltingTest ∧ Binary haltingTest ∧
      (∀ s x, haltingTest s x = 1 ↔ x ∈ haltingStage s) ∧
      Monotone haltingStage ∧ (∀ x, x ∈ haltingDiagonal ↔ ∃ s, x ∈ haltingStage s) ∧
      (∀ s, (haltingStage s).Finite) ∧ haltingStage 0 = ∅ := by
  have hp : Primrec₂ haltingTest :=
    EffectiveEnumerations.stage_test_primitive.comp
      (((Primrec.const haltingIndex).pair Primrec.fst).pair Primrec.snd)
  refine ⟨hp, fun s x => (EffectiveEnumerations.stage_test_spec haltingIndex s x).1,
    fun s x => (EffectiveEnumerations.stage_test_spec haltingIndex s x).2,
    EffectiveEnumerations.stage_monotone haltingIndex, ?_, ?_, ?_⟩
  · intro x
    exact (halting_index_spec x).trans (EffectiveEnumerations.stage_union haltingIndex x)
  · intro s
    exact (EffectiveEnumerations.stage_bounds haltingIndex s).2.1
  · exact (EffectiveEnumerations.stage_bounds haltingIndex 0).2.2

theorem halting_stage_converges : Converges haltingTest haltingDiagonal := by
  have he : haltingDiagonal = EffectiveEnumerations.indexSet haltingIndex :=
    Set.ext halting_index_spec
  rw [he]
  exact canonical_stage_converges haltingIndex

private theorem haltingTest_indicator (s x : ℕ) :
    haltingTest s x = indicator (haltingStage s) x := by
  rfl

theorem halting_prefix_agreement (u : ℕ) :
    ∃ t, ∀ s, t ≤ s → ∀ q < u,
      indicator (haltingStage s) q = indicator haltingDiagonal q := by
  obtain ⟨t, ht⟩ := finite_prefix_stabilization haltingTest haltingDiagonal halting_stage_converges u
  refine ⟨t, fun s hs q hq => ?_⟩
  exact (haltingTest_indicator s q).symm.trans (ht s hs q hq)


private theorem appendTwo_primitive (n : ℕ) :
    Primrec (fun p : Args n × ℕ × ℕ => p.1 ++
      List.Vector.cons p.2.1 (List.Vector.cons p.2.2 List.Vector.nil)) := by
  apply Primrec.vector_toList_iff.mp
  simpa only [List.Vector.toList_append, List.Vector.toList_cons, List.Vector.toList_nil] using
    Primrec.list_append.comp (Primrec.vector_toList.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])))

private theorem initial_primitive (n : ℕ) : Primrec (@PrimitiveRecursion.initialPart n) :=
  Primrec.vector_ofFn (fun i => Primrec.vector_get.comp Primrec.id (Primrec.const i.castSucc))

theorem uniform_family_substitution_primitive {n : ℕ}
    {F : (ℕ → ℕ) → Args n → ℕ} (hF : UniformPrimitive F)
    (q : ℕ → ℕ → ℕ) (hq : Primrec₂ q) :
    Primrec (fun p : ℕ × Args n => F (q p.1) p.2) := by
  induction hF with
  | zero n => exact Primrec.const 0
  | succ => exact Primrec.succ.comp (Primrec.vector_get.comp Primrec.snd (Primrec.const 0))
  | proj i => exact Primrec.vector_get.comp Primrec.snd (Primrec.const i)
  | query =>
    exact hq.comp Primrec.fst (Primrec.vector_get.comp Primrec.snd (Primrec.const 0))
  | @comp m n h g hh hg ihh ihg =>
    exact ihh.comp (Primrec.fst.pair (Primrec.vector_ofFn ihg))
  | @prec n g h hg hh ihg ihh =>
    let H (p : ℕ × Args n) (t : ℕ) := PrimitiveRecursion.recValue (g (q p.1))
      (fun v j z => h (q p.1) (v ++ List.Vector.cons j (List.Vector.cons z List.Vector.nil))) p.2 t
    have hmove : Primrec (fun p : (ℕ × Args n) × (ℕ × ℕ) =>
        (p.1.1, p.1.2 ++ List.Vector.cons p.2.1 (List.Vector.cons p.2.2 List.Vector.nil))) :=
      (Primrec.fst.comp Primrec.fst).pair
        ((appendTwo_primitive n).comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
    have hrec : Primrec₂ H := by
      apply (Primrec.nat_rec ihg (ihh.comp hmove).to₂).of_eq
      intro p t
      rfl
    exact (hrec.comp
      (Primrec.fst.pair ((initial_primitive n).comp Primrec.snd))
      (Primrec.vector_get.comp Primrec.snd (Primrec.const (Fin.last n)))).of_eq (fun _ => rfl)

def stageValue (s e x : ℕ) : ℕ := tableValue (haltingTest s) s e x

def stageValueInput (w : ℕ) : ℕ :=
  stageValue w.unpair.1 w.unpair.2.unpair.1 w.unpair.2.unpair.2

theorem stage_value_primitive : Primrec stageValueInput := by
  let g : Fin 3 → ℕ → ℕ := Fin.cases (fun w => w.unpair.1)
    (Fin.cases (fun w => w.unpair.2.unpair.1) (fun _ w => w.unpair.2.unpair.2))
  have hg : ∀ i, Primrec (g i) := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) i
    · exact Primrec.fst.comp Primrec.unpair
    · exact (Primrec.fst.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)
    · exact (Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)
  have h := (uniform_family_substitution_primitive boundedFamily_primitive haltingTest
    halting_stage_data.1).comp
      ((Primrec.fst.comp Primrec.unpair).pair (Primrec.vector_ofFn hg))
  exact h.of_eq (fun w => by simp only [boundedFamily, List.Vector.get_ofFn, g]; rfl)

theorem stage_value_identity (s e x : ℕ) :
    stageValue s e x = OracleProgramNumberings.boundedValue (haltingStage s) s e x := by
  unfold stageValue
  have hq : haltingTest s = indicator (fun x => x ∈ haltingStage s) := rfl
  rw [hq]
  exact tableValue_correct (haltingStage s) s e x

def boundedGuess (s e x : ℕ) : ℕ := if x < s ∧ stageValue s e x = 2 then 1 else 0

def boundedGuessInput (w : ℕ) : ℕ :=
  boundedGuess w.unpair.1 w.unpair.2.unpair.1 w.unpair.2.unpair.2

theorem bounded_guess_primitive : Primrec boundedGuessInput := by
  have hs : Primrec (fun w : ℕ => w.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hx : Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)
  exact (Primrec.ite ((Primrec.nat_lt.comp hx hs).and
    (Primrec.eq.comp stage_value_primitive (Primrec.const 2))) (Primrec.const 1)
      (Primrec.const 0)).of_eq (fun _ => rfl)

theorem bounded_guess_computable (e : ℕ) :
    Computable₂ (fun s x => boundedGuess s e x) := by
  have hp : Computable (fun p : ℕ × ℕ => Nat.pair p.1 (Nat.pair e p.2)) :=
    Primrec₂.natPair.to_comp.comp Computable.fst
      (Primrec₂.natPair.to_comp.comp (Computable.const e) Computable.snd)
  exact (bounded_guess_primitive.to_comp.comp hp).of_eq
    (fun p => by simp only [boundedGuessInput, Nat.unpair_pair])

theorem bounded_guess_bits_bounds (e : ℕ) :
    Binary (fun s x => boundedGuess s e x) ∧ ∀ s x, boundedGuess s e x = 1 → x < s := by
  constructor
  · intro s x
    dsimp only [boundedGuess]
    split <;> simp
  · intro s x h
    unfold boundedGuess at h
    split at h
    · exact ‹x < s ∧ stageValue s e x = 2›.1
    · contradiction

theorem fixed_allowance_replay (k e x y : ℕ)
    (h : OracleProgramNumberings.boundedValue haltingDiagonal k e x = y + 1) :
    ∃ t, ∀ s, t ≤ s →
      OracleProgramNumberings.boundedValue (haltingStage s) k e x = y + 1 ∧
      OracleProgramNumberings.boundedValue (haltingStage s) s e x = y + 1 := by
  obtain ⟨t, ht⟩ := halting_prefix_agreement k
  have hk : bounded haltingDiagonal k (decodeCode e) x = some y :=
    (OracleProgramNumberings.boundedValue_output haltingDiagonal k e x y).mp h
  refine ⟨max t k, fun s hs => ?_⟩
  have he : bounded (haltingStage s) k (decodeCode e) x =
      bounded haltingDiagonal k (decodeCode e) x :=
    PostsTheorem.bounded_query_dependence _ _ k (ht s (by omega)) (decodeCode e) x
  have hks : bounded (haltingStage s) k (decodeCode e) x = some y := he.trans hk
  refine ⟨(OracleProgramNumberings.boundedValue_output _ _ _ _ _).mpr hks, ?_⟩
  apply (OracleProgramNumberings.boundedValue_output _ _ _ _ _).mpr
  have hle : k ≤ s := by omega
  simpa only [bounded, Nat.add_sub_of_le hle] using
    bounded_monotone (indicator (fun n => n ∈ haltingStage s)) k (s - k) (decodeCode e) x y hks

theorem bounded_guesses_converge (e : ℕ) (A : Set ℕ)
    (h : ∀ x, OracleProgramNumberings.phi haltingDiagonal e x = Part.some (indicator A x)) :
    Converges (fun s x => boundedGuess s e x) A := by
  classical
  intro x
  have hv : indicator A x ∈ eval haltingDiagonal (decodeCode e) x :=
    Part.eq_some_iff.mp (h x)
  obtain ⟨k, hk⟩ := (bounded_complete haltingDiagonal (decodeCode e) x (indicator A x)).mp hv
  have hval := (OracleProgramNumberings.boundedValue_output haltingDiagonal k e x (indicator A x)).mpr hk
  obtain ⟨t, ht⟩ := fixed_allowance_replay k e x (indicator A x) hval
  refine ⟨max t (x + 1), fun s hs => ?_⟩
  have hsx : x < s := by omega
  have he := (ht s (by omega)).2
  have hg : stageValue s e x = indicator A x + 1 :=
    (stage_value_identity s e x).trans he
  by_cases hx : A x
  · have hi : indicator A x = 1 := by simp [indicator, hx]
    have hv : stageValue s e x = 2 := by omega
    simp [boundedGuess, hsx, hv, indicator, hx]
  · have hi : indicator A x = 0 := by simp [indicator, hx]
    have hv : stageValue s e x = 1 := by omega
    simp [boundedGuess, hsx, hv, indicator, hx]

theorem reducible_limit (A : Set ℕ) (hA : TuringDegrees.Reducible A haltingDiagonal) :
    LimitComputable A := by
  obtain ⟨c, hc⟩ := hA
  let e := encodeCode c
  have he : ∀ x, OracleProgramNumberings.phi haltingDiagonal e x = Part.some (indicator A x) := by
    intro x
    simpa only [e, OracleProgramNumberings.phi, decode_encode, Membership.mem, Set.Mem] using hc x
  exact ⟨fun s x => boundedGuess s e x, bounded_guess_computable e,
    (bounded_guess_bits_bounds e).1, bounded_guesses_converge e A he⟩

end
end Lemmatheca.ComputabilityTheory.LimitComputability
