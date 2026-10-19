import Mathlib.Computability.Halting
import Lemmatheca.MathematicalLogic.PrimitiveRecursion
import Lemmatheca.MathematicalLogic.FirstOrderProofs

/-! Numerical certified proof search. A presentation supplies finite tests; its
completeness and consistency are hypotheses establishing termination and correctness,
not extra algorithms queried by the search. -/

namespace Lemmatheca.MathematicalLogic.EffectiveTheories

structure ProofPresentation where
  sentence : ℕ → Bool
  negation : ℕ → ℕ
  check : ℕ → ℕ → Bool
  sentence_primitive : Primrec sentence
  negation_primitive : Primrec negation
  check_primitive : Primrec₂ check
  negation_sentence : ∀ n, sentence n = true → sentence (negation n) = true
  check_sentence : ∀ p n, check p n = true → sentence n = true

def Provable (P : ProofPresentation) (n : ℕ) : Prop := ∃ p, P.check p n = true

def Complete (P : ProofPresentation) : Prop :=
  ∀ n, P.sentence n = true → Provable P n ∨ Provable P (P.negation n)

def Consistent (P : ProofPresentation) : Prop :=
  ∀ n, P.sentence n = true → ¬ (Provable P n ∧ Provable P (P.negation n))

def stage (P : ProofPresentation) (n s : ℕ) : Bool :=
  (List.range (s + 1)).any fun p => P.check p n

def enumerate (P : ProofPresentation) (t : ℕ) : Option ℕ :=
  let p := t.unpair.1
  let n := t.unpair.2
  if P.sentence n && P.check p n then some n else none

/-- A sequential bounded-stage search. Invalid sentence codes are rejected before
any proof search. -/
def search (P : ProofPresentation) (n : ℕ) : Part Bool :=
  if P.sentence n then
    (Nat.rfind fun s => Part.some (stage P n s || stage P (P.negation n) s)).map
      (fun s => stage P n s)
  else Part.some false

noncomputable def decision (P : ProofPresentation) (h : ∀ n, (search P n).Dom) (n : ℕ) : Bool :=
  (search P n).get (h n)

theorem stage_primitive (P : ProofPresentation) : Primrec₂ (stage P) := by
  have hr : PrimrecRel (fun p n : ℕ => P.check p n = true) :=
    Primrec.eq.comp P.check_primitive (Primrec.const true)
  have hb := hr.exists_lt.decide.comp (Primrec.succ.comp Primrec.snd) Primrec.fst
  exact hb.of_eq fun ⟨n, s⟩ => by
    apply Bool.eq_iff_iff.mpr
    simp [stage, Nat.lt_succ_iff]


theorem stage_spec (P : ProofPresentation) (n s : ℕ) :
    stage P n s = true ↔ ∃ p ≤ s, P.check p n = true := by
  simp [stage, List.any_eq_true, Nat.lt_succ_iff]


theorem enumeration_primitive (P : ProofPresentation) : Primrec (enumerate P) := by
  have hs := P.sentence_primitive.comp (Primrec.snd.comp Primrec.unpair)
  have hp := P.check_primitive.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  exact (Primrec.cond (Primrec.and.comp hs hp)
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const none)).of_eq
      fun t => by simp [enumerate, Bool.cond_eq_ite]


theorem enumeration_exact (P : ProofPresentation) (n : ℕ) :
    Provable P n ↔ ∃ t, enumerate P t = some n := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨Nat.pair p n, ?_⟩
    simp [enumerate, hp, P.check_sentence p n hp]
  · rintro ⟨t, ht⟩
    simp only [enumerate] at ht
    split at ht
    · have hn := Option.some.inj ht
      subst n
      exact ⟨_, (Bool.and_eq_true_iff.mp (by assumption)).2⟩
    · contradiction


theorem theorem_set_enumerable (P : ProofPresentation) : REPred (Provable P) := by
  have hf : Partrec (fun n => Nat.rfind (fun p => Part.some (P.check p n))) :=
    Partrec.rfind P.check_primitive.swap.to_comp.partrec
  apply hf.dom_re.of_eq
  intro n
  exact (Nat.rfind_dom (p := fun p => Part.some (P.check p n))).trans
    (by
      constructor
      · rintro ⟨p, hp, _⟩
        exact ⟨p, (Part.mem_some_iff.mp hp).symm⟩
      · rintro ⟨p, hp⟩
        exact ⟨p, Part.mem_some_iff.mpr hp.symm, fun _ => trivial⟩)


theorem search_recursive (P : ProofPresentation) : Partrec (search P) := by
  have hs := (stage_primitive P).to_comp
  have hn := P.negation_primitive.to_comp
  have ht : Computable₂ (fun n s => stage P n s || stage P (P.negation n) s) :=
    Primrec.or.to_comp.comp hs (hs.comp (hn.comp Computable.fst) Computable.snd)
  have hf := (Partrec.rfind ht.partrec.to₂).map hs
  exact (Partrec.cond P.sentence_primitive.to_comp hf (Computable.const false).partrec).of_eq
    fun n => by simp [search, Bool.cond_eq_ite]


theorem search_total (P : ProofPresentation) (h : Complete P) :
    ∀ n, (search P n).Dom := by
  intro n
  by_cases hn : P.sentence n = true
  · simp only [search, hn, ↓reduceIte]
    change (Nat.rfind _).Dom
    apply Nat.rfind_dom.mpr
    obtain ⟨p, hp⟩ | ⟨p, hp⟩ := h n hn
    · exact ⟨p, by simp [(stage_spec P n p).mpr ⟨p, le_rfl, hp⟩], fun _ => trivial⟩
    · exact ⟨p, by simp [(stage_spec P (P.negation n) p).mpr ⟨p, le_rfl, hp⟩],
        fun _ => trivial⟩
  · simp [search, hn]


theorem search_correct (P : ProofPresentation) (hc : Complete P) (hk : Consistent P)
    (n : ℕ) : true ∈ search P n ↔ Provable P n := by
  by_cases hn : P.sentence n = true
  · simp only [search, hn, ↓reduceIte, Part.mem_map_iff]
    constructor
    · rintro ⟨s, _, hs⟩
      obtain ⟨p, _, hp⟩ := (stage_spec P n s).mp hs
      exact ⟨p, hp⟩
    · intro hp
      obtain ⟨s, hs⟩ := Part.dom_iff_mem.mp (search_total P hc n)
      simp only [search, hn, ↓reduceIte, Part.mem_map_iff] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      have hh := Nat.rfind_spec ht
      have hh' : stage P n t = true ∨ stage P (P.negation n) t = true :=
        Bool.or_eq_true_iff.mp (Part.mem_some_iff.mp hh).symm
      obtain hp' | hn' := hh'
      · exact ⟨t, ht, hp'⟩
      · obtain ⟨p, _, hh⟩ := (stage_spec P (P.negation n) t).mp hn'
        exact False.elim (hk n hn ⟨hp, p, hh⟩)
  · have hp : ¬ Provable P n := by
      rintro ⟨p, h⟩
      exact hn (P.check_sentence p n h)
    simp [search, hn, hp]


theorem decision_computable (P : ProofPresentation) (ht : ∀ n, (search P n).Dom) :
    Computable (decision P ht) := by
  exact (search_recursive P).of_eq_tot fun n => Part.get_mem (ht n)


theorem decision_spec (P : ProofPresentation) (hc : Complete P) (hk : Consistent P)
    (n : ℕ) : decision P (search_total P hc) n = true ↔ Provable P n := by
  rw [← search_correct P hc hk]
  change (search P n).get (search_total P hc n) = true ↔ true ∈ search P n
  exact ⟨fun h => h ▸ Part.get_mem _, fun h => Part.mem_unique (Part.get_mem _) h⟩


theorem complete_effective_decidable (P : ProofPresentation)
    (hc : Complete P) (hk : Consistent P) : ComputablePred (Provable P) := by
  apply ComputablePred.computable_iff.mpr
  exact ⟨decision P (search_total P hc), decision_computable P (search_total P hc),
    funext fun n => propext (decision_spec P hc hk n).symm⟩


theorem search_stalls (P : ProofPresentation) (n : ℕ) (hs : P.sentence n = true)
    (hp : ¬ Provable P n) (hn : ¬ Provable P (P.negation n)) :
    search P n = Part.none := by
  apply Part.eq_none_iff.mpr
  intro a ha
  simp only [search, hs, ↓reduceIte, Part.mem_map_iff] at ha
  obtain ⟨s, hh, _⟩ := ha
  have ht : stage P n s = true ∨ stage P (P.negation n) s = true :=
    Bool.or_eq_true_iff.mp (Part.mem_some_iff.mp (Nat.rfind_spec hh)).symm
  obtain h | h := ht
  · obtain ⟨p, _, hh⟩ := (stage_spec P n s).mp h
    exact hp ⟨p, hh⟩
  · obtain ⟨p, _, hh⟩ := (stage_spec P (P.negation n) s).mp h
    exact hn ⟨p, hh⟩

/-- The certificate presentation decides actual natural-deduction theoremhood,
not merely an unrelated numerical predicate. -/
theorem actual_complete_decidable {L : FirstOrder.Language} (T : L.Theory)
    (P : ProofPresentation) (code : L.Sentence → ℕ)
    (hrange : ∀ n, P.sentence n = true ↔ ∃ A, code A = n)
    (hneg : ∀ A, P.negation (code A) = code A.not)
    (hproof : ∀ A, Provable P (code A) ↔ FirstOrderProofs.Derives T A)
    (hk : FirstOrderProofs.Consistent T)
    (hc : ∀ A, FirstOrderProofs.Derives T A ∨ FirstOrderProofs.Derives T A.not) :
    ComputablePred (fun n => ∃ A, code A = n ∧ FirstOrderProofs.Derives T A) := by
  have hcomp : Complete P := by
    intro n hn
    obtain ⟨A, rfl⟩ := (hrange n).mp hn
    simpa only [hproof, hneg] using hc A
  have hcons : Consistent P := by
    intro n hn hboth
    obtain ⟨A, rfl⟩ := (hrange n).mp hn
    rw [hneg, hproof, hproof] at hboth
    apply hk
    simpa only [Set.union_self] using FirstOrderProofs.derives_cut hboth.1
      (FirstOrderProofs.derives_imp_iff.mp hboth.2)
  apply (complete_effective_decidable P hcomp hcons).of_eq
  intro n
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h
    obtain ⟨A, rfl⟩ := (hrange n).mp (P.check_sentence p n hp)
    exact ⟨A, rfl, (hproof A).mp ⟨p, hp⟩⟩
  · rintro ⟨A, rfl, h⟩
    exact (hproof A).mpr h


end Lemmatheca.MathematicalLogic.EffectiveTheories
