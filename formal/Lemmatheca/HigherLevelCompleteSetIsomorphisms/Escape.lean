import Lemmatheca.UniformOracleFixedPoints.Dispatch
import Lemmatheca.OraclePadding.Halting
import Lemmatheca.CreativeSetsAndComputableIsomorphism.Escape

/-! Common oracle selectors and ordinary finite-image escape. -/
namespace Lemmatheca.ComputabilityTheory.HigherCompleteIsomorphism

open OracleComputation OracleProgramNumberings OraclePadding
open CreativeIsomorphism (imageValues)

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def Compatible (A : Set ℕ) (e : ℕ) (L : List ℕ) : Prop :=
  ∀ j ∈ L, j ∈ haltsZero A ↔ e ∈ haltsZero A

def ReducesZero (A : Set ℕ) (g : ℕ → ℕ) (C : Set ℕ) : Prop :=
  ∀ e, e ∈ haltsZero A ↔ g e ∈ C

def divergenceIndex : ℕ := encodeCode (.find' (.comp .succ .zero))

def firstTransformer (g : ℕ → ℕ) (t p : ℕ) : ℕ :=
  if g t ∈ imageValues g (FiniteSequenceCoding.decode p.unpair.2)
  then divergenceIndex else p.unpair.1

def secondTransformer (g : ℕ → ℕ) (t c : ℕ) : ℕ :=
  if g t ∈ imageValues g (FiniteSequenceCoding.decode c)
  then constantIndex 1 else divergenceIndex

theorem fixed_programs (A : Set ℕ) (x : ℕ) :
    phi A divergenceIndex x = Part.none ∧
      phi A (constantIndex 1) x = Part.some 1 := by
  constructor
  · change eval A (decodeCode divergenceIndex) x = Part.none
    rw [divergenceIndex, decode_encode]
    obtain ⟨⟨a, m⟩, rfl⟩ := Nat.pairEquiv.surjective x
    apply Part.eq_none_iff.mpr
    intro y hy
    have hz := ((eval_find A (.comp .succ .zero) a m y).mp hy).2.1
    simp [eval] at hz
  · simp [phi, constantIndex, decode_encode, constant_eval]

private theorem membership_computable :
    Computable₂ (fun (L : List ℕ) j => decide (j ∈ L)) := by
  exact ((PrimrecRel.exists_mem_list Primrec.eq).decide.to_comp).of_eq
    (fun p => by simp)

theorem transformers_computable {g : ℕ → ℕ} (hg : Computable g) :
    Computable₂ (firstTransformer g) ∧ Computable₂ (secondTransformer g) := by
  have hfirst : Computable (fun p : ℕ × ℕ =>
      imageValues g (FiniteSequenceCoding.decode p.2.unpair.2)) :=
    (CreativeIsomorphism.image_values_computable hg).comp
      ((Primrec.ofNat (List ℕ)).to_comp.comp
        (Computable.snd.comp (Computable.unpair.comp Computable.snd)))
  have hsecond : Computable (fun p : ℕ × ℕ =>
      imageValues g (FiniteSequenceCoding.decode p.2)) :=
    (CreativeIsomorphism.image_values_computable hg).comp
      ((Primrec.ofNat (List ℕ)).to_comp.comp Computable.snd)
  have ht1 := membership_computable.comp hfirst (hg.comp Computable.fst)
  have ht2 := membership_computable.comp hsecond (hg.comp Computable.fst)
  constructor
  · exact (Computable.cond ht1 (Computable.const divergenceIndex)
      (Computable.fst.comp (Computable.unpair.comp Computable.snd))).of_eq
        (fun p => by simp [firstTransformer])
  · exact (Computable.cond ht2 (Computable.const (constantIndex 1))
      (Computable.const divergenceIndex)).of_eq
        (fun p => by simp [secondTransformer])

def firstSelector (N : ℕ → ℕ) (e : ℕ) (L : List ℕ) : ℕ :=
  N (Nat.pair e (FiniteSequenceCoding.code L))

def secondSelector (M : ℕ → ℕ) (L : List ℕ) : ℕ :=
  M (FiniteSequenceCoding.code L)

def IsFirstSelector (g N : ℕ → ℕ) : Prop :=
  ∀ A : Set ℕ, ∀ e L x,
    phi A (firstSelector N e L) x =
      if g (firstSelector N e L) ∈ imageValues g L then Part.none else phi A e x

def IsSecondSelector (g M : ℕ → ℕ) : Prop :=
  ∀ A : Set ℕ, ∀ L x,
    phi A (secondSelector M L) x =
      if g (secondSelector M L) ∈ imageValues g L then Part.some 1 else Part.none

theorem common_selectors {g : ℕ → ℕ} (hg : Computable g) :
    ∃ N M : ℕ → ℕ, Primrec N ∧ Primrec M ∧ IsFirstSelector g N ∧ IsSecondSelector g M := by
  obtain ⟨hF1, hF2⟩ := transformers_computable hg
  obtain ⟨N, hN, hn⟩ := UniformOracleFixedPoints.parameterized_recursion hF1
  obtain ⟨M, hM, hm⟩ := UniformOracleFixedPoints.parameterized_recursion hF2
  refine ⟨N, M, hN, hM, ?_, ?_⟩
  · intro A e L x
    have hh := hn A (Nat.pair e (FiniteSequenceCoding.code L)) x
    change phi A (firstSelector N e L) x =
      phi A (firstTransformer g (firstSelector N e L)
        (Nat.pair e (FiniteSequenceCoding.code L))) x at hh
    rw [hh]
    by_cases hc : g (firstSelector N e L) ∈ imageValues g L
    · simpa [firstTransformer, FiniteSequenceCoding.decode_code, hc] using (fixed_programs A x).1
    · simp [firstTransformer, hc]
  · intro A L x
    have hh := hm A (FiniteSequenceCoding.code L) x
    change phi A (secondSelector M L) x =
      phi A (secondTransformer g (secondSelector M L) (FiniteSequenceCoding.code L)) x at hh
    rw [hh]
    by_cases hc : g (secondSelector M L) ∈ imageValues g L
    · simpa [secondTransformer, FiniteSequenceCoding.decode_code, hc] using (fixed_programs A x).2
    · simpa [secondTransformer, FiniteSequenceCoding.decode_code, hc] using (fixed_programs A x).1

theorem selectors_primitive {N M : ℕ → ℕ} (hN : Primrec N) (hM : Primrec M) :
    Primrec₂ (firstSelector N) ∧ Primrec (secondSelector M) := by
  constructor
  · exact ((hN.comp
      (Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd)))).to₂
  · exact hM.comp Primrec.encode

theorem first_cases {A C : Set ℕ} {g N : ℕ → ℕ} {e : ℕ} {L : List ℕ}
    (hred : ReducesZero A g C) (hn : IsFirstSelector g N) (hL : Compatible A e L) :
    (g (firstSelector N e L) ∉ imageValues g L →
      (∀ x, phi A (firstSelector N e L) x = phi A e x) ∧
        (firstSelector N e L ∈ haltsZero A ↔ e ∈ haltsZero A)) ∧
    (g (firstSelector N e L) ∈ imageValues g L → e ∉ haltsZero A) := by
  constructor
  · intro hfresh
    have heq : ∀ x, phi A (firstSelector N e L) x = phi A e x := by
      intro x
      simpa [hfresh] using hn A e L x
    exact ⟨heq, by change (phi A _ 0).Dom ↔ (phi A e 0).Dom; rw [heq]⟩
  · intro hc he
    obtain ⟨j, hj, hjeq⟩ := (CreativeIsomorphism.image_values_membership g L _).mp hc
    have hjhalt : j ∈ haltsZero A := (hL j hj).mpr he
    have hnhalt : firstSelector N e L ∈ haltsZero A :=
      (hred _).mpr (hjeq ▸ (hred j).mp hjhalt)
    change (phi A (firstSelector N e L) 0).Dom at hnhalt
    rw [hn A e L 0] at hnhalt
    simp [hc] at hnhalt

theorem second_escapes {A C : Set ℕ} {g N M : ℕ → ℕ} {e : ℕ} {L : List ℕ}
    (hred : ReducesZero A g C) (hn : IsFirstSelector g N) (hm : IsSecondSelector g M)
    (hL : Compatible A e L) (hc : g (firstSelector N e L) ∈ imageValues g L) :
    g (secondSelector M L) ∉ imageValues g L ∧
      secondSelector M L ∉ haltsZero A ∧ e ∉ haltsZero A := by
  have he : e ∉ haltsZero A := (first_cases hred hn hL).2 hc
  have hfresh : g (secondSelector M L) ∉ imageValues g L := by
    intro hmcoll
    have hmhalt : secondSelector M L ∈ haltsZero A := by
      change (phi A (secondSelector M L) 0).Dom
      rw [hm A L 0]
      simp [hmcoll]
    obtain ⟨j, hj, hjeq⟩ := (CreativeIsomorphism.image_values_membership g L _).mp hmcoll
    have hjhalt : j ∈ haltsZero A :=
      (hred j).mpr (hjeq.symm ▸ (hred _).mp hmhalt)
    exact he ((hL j hj).mp hjhalt)
  refine ⟨hfresh, ?_, he⟩
  change ¬ (phi A (secondSelector M L) 0).Dom
  rw [hm A L 0]
  simp [hfresh]

def escapeStep (g N M : ℕ → ℕ) (e : ℕ) (L : List ℕ) : ℕ :=
  if g (firstSelector N e L) ∈ imageValues g L then secondSelector M L
  else firstSelector N e L

theorem escape_step_computable {g N M : ℕ → ℕ}
    (hg : Computable g) (hN : Primrec N) (hM : Primrec M) :
    Computable₂ (escapeStep g N M) := by
  have hn := (selectors_primitive hN hM).1.to_comp
  have hm := (selectors_primitive hN hM).2.to_comp
  have ht : Computable (fun p : ℕ × List ℕ =>
      decide (g (firstSelector N p.1 p.2) ∈ imageValues g p.2)) :=
    membership_computable.comp ((CreativeIsomorphism.image_values_computable hg).comp Computable.snd)
      (hg.comp hn)
  change Computable (fun p : ℕ × List ℕ => escapeStep g N M p.1 p.2)
  exact (Computable.cond ht (hm.comp Computable.snd) hn).of_eq
    (fun p => by simp [escapeStep])

theorem escape_step_spec {A C : Set ℕ} {g N M : ℕ → ℕ} {e : ℕ} {L : List ℕ}
    (hred : ReducesZero A g C) (hn : IsFirstSelector g N) (hm : IsSecondSelector g M)
    (hL : Compatible A e L) :
    g (escapeStep g N M e L) ∉ imageValues g L ∧
      (escapeStep g N M e L ∈ haltsZero A ↔ e ∈ haltsZero A) := by
  by_cases hc : g (firstSelector N e L) ∈ imageValues g L
  · have h := second_escapes hred hn hm hL hc
    simp only [escapeStep, ite_eq_left hc]
    exact ⟨h.1, iff_of_false h.2.1 h.2.2⟩
  · simp only [escapeStep, ite_eq_right hc]
    exact ⟨hc, ((first_cases hred hn hL).1 hc).2⟩

def queryHistory (g N M : ℕ → ℕ) (e : ℕ) : ℕ → List ℕ
  | 0 => [e]
  | k + 1 => queryHistory g N M e k ++ [escapeStep g N M e (queryHistory g N M e k)]

def query (g N M : ℕ → ℕ) (e : ℕ) : ℕ → ℕ
  | 0 => e
  | k + 1 => escapeStep g N M e (queryHistory g N M e k)

theorem query_history_identity (g N M : ℕ → ℕ) (e k : ℕ) :
    queryHistory g N M e k = (List.range (k + 1)).map (query g N M e) := by
  induction k with
  | zero => simp [queryHistory, query]
  | succ k ih =>
    simpa [queryHistory, List.range_succ, query] using
      congrArg (fun L => L ++ [query g N M e (k + 1)]) ih

theorem query_computable {g N M : ℕ → ℕ}
    (hg : Computable g) (hN : Primrec N) (hM : Primrec M) :
    Computable₂ (queryHistory g N M) ∧ Computable₂ (query g N M) := by
  have ht := escape_step_computable hg hN hM
  have hbase : Computable (fun p : ℕ × ℕ => [p.1]) :=
    Computable.list_cons.comp Computable.fst (Computable.const [])
  have hstep : Computable₂ (fun p : ℕ × ℕ => fun t : ℕ × List ℕ =>
      t.2 ++ [escapeStep g N M p.1 t.2]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (ht.comp (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.snd))).to₂
  have hh : Computable₂ (queryHistory g N M) :=
    by
      change Computable (fun p : ℕ × ℕ => queryHistory g N M p.1 p.2)
      exact (Computable.nat_rec Computable.snd hbase hstep).of_eq
        (fun p => by induction p.2 <;> simp [queryHistory, *])
  refine ⟨hh, ?_⟩
  have hsucc : Computable₂ (fun e k => escapeStep g N M e (queryHistory g N M e k)) :=
    (ht.comp Computable.fst hh).to₂
  change Computable (fun p : ℕ × ℕ => query g N M p.1 p.2)
  exact (Computable.nat_casesOn Computable.snd Computable.fst
    (hsucc.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂).of_eq
    (fun p => by cases p.2 <;> rfl)

theorem query_invariants {A C : Set ℕ} {g N M : ℕ → ℕ}
    (hred : ReducesZero A g C) (hn : IsFirstSelector g N) (hm : IsSecondSelector g M) :
    (∀ e k, (queryHistory g N M e k).length = k + 1 ∧
      Compatible A e (queryHistory g N M e k) ∧
        (imageValues g (queryHistory g N M e k)).Nodup) ∧
    (∀ e k, query g N M e k ∈ haltsZero A ↔ e ∈ haltsZero A) ∧
      ∀ e, Function.Injective (fun k => g (query g N M e k)) := by
  have hprefix : ∀ e k, Compatible A e (queryHistory g N M e k) ∧
      (imageValues g (queryHistory g N M e k)).Nodup := by
    intro e k
    induction k with
    | zero => simp [queryHistory, Compatible, imageValues]
    | succ k ih =>
      have hs := escape_step_spec hred hn hm ih.1
      constructor
      · intro j hj
        simp only [queryHistory, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact ih.1 j hj
        · exact hs.2
      · simpa only [queryHistory, imageValues, List.map_append, List.map_singleton,
          List.concat_eq_append] using List.Nodup.concat hs.1 ih.2
  have hquery : ∀ e k, query g N M e k ∈ haltsZero A ↔ e ∈ haltsZero A := by
    intro e k
    apply (hprefix e k).1
    rw [query_history_identity]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩
  refine ⟨?_, hquery, ?_⟩
  · intro e k
    refine ⟨?_, (hprefix e k).1, (hprefix e k).2⟩
    simp [query_history_identity]
  · intro e
    have hne : ∀ i j, i < j → g (query g N M e i) ≠ g (query g N M e j) := by
      intro i j hij
      cases j with
      | zero => omega
      | succ j =>
        have hs := (escape_step_spec hred hn hm (hprefix e j).1).1
        have hmem : query g N M e i ∈ queryHistory g N M e j := by
          rw [query_history_identity]
          exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
        have himage : g (query g N M e i) ∈ imageValues g (queryHistory g N M e j) :=
          (CreativeIsomorphism.image_values_membership g _ _).mpr ⟨_, hmem, rfl⟩
        intro heq
        apply hs
        change g (query g N M e (j + 1)) ∈ _
        exact heq ▸ himage
    intro i j heq
    rcases lt_trichotomy i j with hlt | he | hgt
    · exact False.elim (hne i j hlt heq)
    · exact he
    · exact False.elim (hne j i hgt heq.symm)
  
  /-- The finite search is defined for all supplied selectors. Under the selector
  and reduction hypotheses, its first success is at most the forbidden list length. -/

def avoidancePosition (g N M : ℕ → ℕ) (e : ℕ) (F : List ℕ) : ℕ :=
  Myhill.boundedSearch (fun k => decide (g (query g N M e k) ∉ F)) (F.length + 1)

def avoidImage (g N M : ℕ → ℕ) (e : ℕ) (F : List ℕ) : ℕ :=
  g (query g N M e (avoidancePosition g N M e F))

private theorem rec_computable {α σ : Type*} [Primcodable α] [Primcodable σ]
    {b : α → σ} {s : α → ℕ × σ → σ}
    (hb : Computable b) (hs : Computable₂ s) :
    Computable₂ (fun a n => Nat.rec (motive := fun _ => σ) (b a) (fun i v => s a (i, v)) n) := by
  exact Computable.nat_rec Computable.snd (hb.comp Computable.fst)
    (hs.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂

private theorem bounded_search_computable {α : Type*} [Primcodable α]
    {p : α → ℕ → Bool} (hp : Computable₂ p) :
    Computable₂ (fun a n => Myhill.boundedSearch (p a) n) := by
  have hs : Computable₂ (fun a (q : ℕ × ℕ) =>
      if p a q.2 then q.2 else q.1 + 1) := by
    exact (Computable.cond
      (hp.comp Computable.fst (Computable.snd.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
      (Computable.succ.comp (Computable.fst.comp Computable.snd))).of_eq
        (fun _ => by simp only [Bool.cond_eq_ite])
  apply (rec_computable (Computable.const 0) hs).of_eq
  rintro ⟨a, n⟩
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun u => if p a u then u else n + 1) ih

private theorem bounded_search_invariant (p : ℕ → Bool) (n : ℕ) :
    Myhill.boundedSearch p n ≤ n ∧
      (∀ i < Myhill.boundedSearch p n, p i = false) ∧
      (Myhill.boundedSearch p n < n → p (Myhill.boundedSearch p n) = true) := by
  induction n with
  | zero => simp [Myhill.boundedSearch]
  | succ n ih =>
    by_cases hp : p (Myhill.boundedSearch p n) = true
    · rw [Myhill.boundedSearch, ite_eq_left hp]
      exact ⟨by omega, ih.2.1, fun _ => hp⟩
    · have hp' : p (Myhill.boundedSearch p n) = false := Bool.eq_false_iff.mpr hp
      have he : Myhill.boundedSearch p n = n := by
        by_contra hn
        exact hp (ih.2.2 (by omega))
      rw [Myhill.boundedSearch, ite_eq_right hp]
      refine ⟨le_rfl, ?_, by omega⟩
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · exact ih.2.1 i (by omega)
      · simpa [he] using hp'

private theorem bounded_search_success (p : ℕ → Bool) {k n : ℕ}
    (hk : k < n) (hp : p k = true) :
    Myhill.boundedSearch p n ≤ k ∧ p (Myhill.boundedSearch p n) = true := by
  have hi := bounded_search_invariant p n
  have hl : Myhill.boundedSearch p n ≤ k := by
    by_contra h
    have := hi.2.1 k (by omega)
    simp [hp] at this
  exact ⟨hl, hi.2.2 (by omega)⟩

private theorem finite_image_escape (f : ℕ → ℕ) (hf : Function.Injective f) (F : List ℕ) :
    ∃ k ≤ F.length, f k ∉ F := by
  by_contra! h
  have hs : (Finset.range (F.length + 1)).image f ⊆ F.toFinset := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (h k (by simpa using Finset.mem_range.mp hk))
  have hc := Finset.card_le_card hs
  have hl := List.toFinset_card_le F
  rw [Finset.card_image_of_injective _ hf, Finset.card_range] at hc
  omega

theorem avoidance_computable {g N M : ℕ → ℕ}
    (hg : Computable g) (hN : Primrec N) (hM : Primrec M) :
    Computable₂ (avoidancePosition g N M) ∧ Computable₂ (avoidImage g N M) := by
  have hq := (query_computable hg hN hM).2
  have ht : Computable₂ (fun p : ℕ × List ℕ => fun k =>
      decide (g (query g N M p.1 k) ∉ p.2)) := by
    change Computable (fun p : (ℕ × List ℕ) × ℕ =>
      decide (g (query g N M p.1.1 p.2) ∉ p.1.2))
    exact (Primrec.not.to_comp.comp
      (membership_computable.comp (Computable.snd.comp Computable.fst)
        (hg.comp (hq.comp (Computable.fst.comp Computable.fst) Computable.snd)))).of_eq
      (fun p => by simp)
  have ha : Computable₂ (avoidancePosition g N M) := by
    exact (bounded_search_computable ht).comp Computable.id
      (Computable.succ.comp (Computable.list_length.comp Computable.snd))
  refine ⟨ha, ?_⟩
  exact hg.comp (hq.comp Computable.fst ha)

theorem avoidance_spec {A C : Set ℕ} {g N M : ℕ → ℕ}
    (hred : ReducesZero A g C) (hn : IsFirstSelector g N) (hm : IsSecondSelector g M)
    (e : ℕ) (F : List ℕ) :
    avoidancePosition g N M e F ≤ F.length ∧ avoidImage g N M e F ∉ F ∧
      (∀ k < avoidancePosition g N M e F, g (query g N M e k) ∈ F) ∧
        (e ∈ haltsZero A ↔ avoidImage g N M e F ∈ C) := by
  obtain ⟨k, hk, hfresh⟩ := finite_image_escape
    (fun k => g (query g N M e k)) ((query_invariants hred hn hm).2.2 e) F
  have hs := bounded_search_success
    (fun k => decide (g (query g N M e k) ∉ F)) (by omega : k < F.length + 1)
    (by simpa using hfresh)
  have hf : avoidImage g N M e F ∉ F := by
    exact of_decide_eq_true hs.2
  refine ⟨le_trans hs.1 hk, hf, ?_, ?_⟩
  · intro i hi
    have hfalse := (bounded_search_invariant
      (fun k => decide (g (query g N M e k) ∉ F)) (F.length + 1)).2.1 i hi
    simpa using hfalse
  · exact ((query_invariants hred hn hm).2.1 e _).symm.trans (hred _)

def outputHistory (g N M : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | e + 1 => outputHistory g N M e ++ [avoidImage g N M e (outputHistory g N M e)]

def replacement (g N M : ℕ → ℕ) (e : ℕ) : ℕ :=
  avoidImage g N M e (outputHistory g N M e)

theorem output_history_identity (g N M : ℕ → ℕ) (e : ℕ) :
    outputHistory g N M e = (List.range e).map (replacement g N M) := by
  induction e with
  | zero => rfl
  | succ e ih =>
    simpa [outputHistory, List.range_succ, replacement] using
      congrArg (fun L => L ++ [replacement g N M e]) ih

theorem replacement_computable {g N M : ℕ → ℕ}
    (hg : Computable g) (hN : Primrec N) (hM : Primrec M) :
    Computable (outputHistory g N M) ∧ Computable (replacement g N M) := by
  have hr := (avoidance_computable hg hN hM).2
  have hs : Computable₂ (fun (_ : ℕ) (p : ℕ × List ℕ) =>
      p.2 ++ [avoidImage g N M p.1 p.2]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hr.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd))).to₂
  have hh : Computable (outputHistory g N M) := by
    exact (Computable.nat_rec Computable.id (Computable.const []) hs).of_eq
      (fun e => by
        have he (k : ℕ) :
            Nat.rec ([] : List ℕ) (fun i L => L ++ [avoidImage g N M i L]) k =
              outputHistory g N M k := by
          induction k with
          | zero => rfl
          | succ k ih => exact congrArg (fun L => L ++ [avoidImage g N M k L]) ih
        exact he e)
  exact ⟨hh, hr.comp Computable.id hh⟩

theorem replacement_spec {g N M : ℕ → ℕ} (hg : Computable g)
    (hN : Primrec N) (hM : Primrec M) (hn : IsFirstSelector g N) (hm : IsSecondSelector g M) :
    Computable (replacement g N M) ∧ ∀ A C : Set ℕ, ReducesZero A g C →
      Function.Injective (replacement g N M) ∧
        ∀ e, e ∈ haltsZero A ↔ replacement g N M e ∈ C := by
  have hcomp := (replacement_computable hg hN hM).2
  refine ⟨hcomp, ?_⟩
  intro A C hred
  have hne : ∀ i j, i < j → replacement g N M i ≠ replacement g N M j := by
    intro i j hij heq
    have hs := (avoidance_spec hred hn hm j (outputHistory g N M j)).2.1
    change replacement g N M j ∉ outputHistory g N M j at hs
    have hmemb : replacement g N M i ∈ outputHistory g N M j := by
      rw [output_history_identity]
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hij, rfl⟩
    exact hs (heq ▸ hmemb)
  refine ⟨?_, fun e => (avoidance_spec hred hn hm e _).2.2.2⟩
  intro i j heq
  rcases lt_trichotomy i j with hlt | he | hgt
  · exact False.elim (hne i j hlt heq)
  · exact he
  · exact False.elim (hne j i hgt heq.symm)

theorem injective_upgrade (A C : Set ℕ) :
    ManyOneReducible (haltsZero A) C → (haltsZero A) ≤₁ C := by
  rintro ⟨g, hg, hred⟩
  obtain ⟨N, M, hN, hM, hn, hm⟩ := common_selectors hg
  obtain ⟨hcomp, hspec⟩ := replacement_spec hg hN hM hn hm
  exact ⟨replacement g N M, hcomp, (hspec A C hred).1, (hspec A C hred).2⟩

end
end Lemmatheca.ComputabilityTheory.HigherCompleteIsomorphism
