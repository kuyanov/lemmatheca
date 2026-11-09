import Lemmatheca.UniformSelfReference.Uniform
import Lemmatheca.PaddingAndInjectiveReductions.Halting
import Lemmatheca.MyhillsIsomorphismTheorem.Matching

/-! The ordinary halting-specific injectivization. All algorithms take numerical
queries and finite lists. The target membership predicate is only a proof invariant. -/
namespace Lemmatheca.ComputabilityTheory.CreativeIsomorphism

open UniversalComputation RicesTheorem UniformSelfReference RecursionTheorem

/-- A list representing the finite set of already used images. -/
def imageValues (g : ℕ → ℕ) (L : List ℕ) : List ℕ := L.map g

def Compatible (e : ℕ) (L : List ℕ) : Prop :=
  ∀ j ∈ L, j ∈ haltsZero ↔ e ∈ haltsZero

def ReducesZero (g : ℕ → ℕ) (C : Set ℕ) : Prop :=
  ∀ e, e ∈ haltsZero ↔ g e ∈ C

def firstRule (g : ℕ → ℕ) (a e : ℕ) (L : List ℕ) (z : ℕ) : Part ℕ :=
  if g a ∈ imageValues g L then Part.none else phi e z

def secondRule (g : ℕ → ℕ) (a : ℕ) (L : List ℕ) (_z : ℕ) : Part ℕ :=
  if g a ∈ imageValues g L then Part.some 1 else Part.none

/-- The parameter for the first partial family is the pair of the old query and
its numerical list code. -/
def firstFamily (g : ℕ → ℕ) (a p z : ℕ) : Part ℕ :=
  firstRule g a p.unpair.1 (FiniteSequenceCoding.decode p.unpair.2) z

def secondFamily (g : ℕ → ℕ) (a lcode z : ℕ) : Part ℕ :=
  secondRule g a (FiniteSequenceCoding.decode lcode) z

def firstSelector (q e : ℕ) (L : List ℕ) : ℕ :=
  selector q (Nat.pair e (FiniteSequenceCoding.code L))

def secondSelector (q : ℕ) (L : List ℕ) : ℕ :=
  selector q (FiniteSequenceCoding.code L)

def IsFirstSelector (g : ℕ → ℕ) (q : ℕ) : Prop :=
  ∀ e L z, phi (firstSelector q e L) z = firstRule g (firstSelector q e L) e L z

def IsSecondSelector (g : ℕ → ℕ) (q : ℕ) : Prop :=
  ∀ L z, phi (secondSelector q L) z = secondRule g (secondSelector q L) L z

theorem image_values_computable {g : ℕ → ℕ} (hg : Computable g) :
    Computable (imageValues g) := by
  let build (l : List ℕ) : ℕ → List ℕ :=
    Nat.rec [] (fun k old => old ++ [g (l[k]?.getD 0)])
  have hstep : Computable₂ (fun l : List ℕ => fun p : ℕ × List ℕ =>
      p.2 ++ [g (l[p.1]?.getD 0)]) := by
    exact (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hg.comp (Primrec.option_getD.to_comp.comp
        (Computable.list_getElem?.comp Computable.fst (Computable.fst.comp Computable.snd))
        (Computable.const 0)))).to₂
  have hc : Computable (fun l : List ℕ => build l l.length) :=
    Computable.nat_rec Computable.list_length (Computable.const []) hstep
  apply hc.of_eq
  intro l
  have he (k : ℕ) : build l k = (List.range k).map (fun i => g (l[i]?.getD 0)) := by
    induction k with
    | zero => rfl
    | succ k ih => simp [build, List.range_succ, ih]
  rw [he]
  apply List.ext_getElem
  · simp [imageValues]
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simp [imageValues, List.getElem?_eq_getElem hi]

theorem image_values_membership (g : ℕ → ℕ) (L : List ℕ) (y : ℕ) :
    y ∈ imageValues g L ↔ ∃ j ∈ L, g j = y := by
  simp [imageValues]

theorem selectors_primitive (qn qm : ℕ) :
    Primrec₂ (firstSelector qn) ∧ Primrec (secondSelector qm) := by
  constructor
  · exact ((selector_primitive qn).comp
      (Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd))).to₂
  · exact (selector_primitive qm).comp Primrec.encode

private theorem membership_computable :
    Computable₂ (fun (l : List ℕ) j => decide (j ∈ l)) := by
  exact ((PrimrecRel.exists_mem_list Primrec.eq).decide.to_comp).of_eq
    (fun p => by simp)

theorem first_family_partial {g : ℕ → ℕ} (hg : Computable g) :
    Partrec (fun t : ℕ × (ℕ × ℕ) => firstFamily g t.1 t.2.1 t.2.2) := by
  have hlist : Computable (fun t : ℕ × (ℕ × ℕ) =>
      imageValues g (FiniteSequenceCoding.decode t.2.1.unpair.2)) :=
    (image_values_computable hg).comp ((Primrec.ofNat (List ℕ)).to_comp.comp
      (Computable.snd.comp (Computable.unpair.comp (Computable.fst.comp Computable.snd))))
  have ht : Computable (fun t : ℕ × (ℕ × ℕ) =>
      decide (g t.1 ∈ imageValues g (FiniteSequenceCoding.decode t.2.1.unpair.2))) :=
    membership_computable.comp hlist (hg.comp Computable.fst)
  exact (Partrec.cond ht Partrec.none
    (phi_recursive.comp
      (Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd))).of_eq
    (fun t => by simp [firstFamily, firstRule])

theorem second_family_partial {g : ℕ → ℕ} (hg : Computable g) :
    Partrec (fun t : ℕ × (ℕ × ℕ) => secondFamily g t.1 t.2.1 t.2.2) := by
  have hlist : Computable (fun t : ℕ × (ℕ × ℕ) =>
      imageValues g (FiniteSequenceCoding.decode t.2.1)) :=
    (image_values_computable hg).comp ((Primrec.ofNat (List ℕ)).to_comp.comp
      (Computable.fst.comp Computable.snd))
  have ht : Computable (fun t : ℕ × (ℕ × ℕ) =>
      decide (g t.1 ∈ imageValues g (FiniteSequenceCoding.decode t.2.1))) :=
    membership_computable.comp hlist (hg.comp Computable.fst)
  exact (Partrec.cond ht (Partrec.const' (Part.some 1)) Partrec.none).of_eq
    (fun t => by simp [secondFamily, secondRule])

/-- The complete numerical bridge from the family index to the exact selector
n(e,L)=s(s(r,r),pair(e,code L)), chosen before e and L vary. -/
theorem first_selector_exists {g : ℕ → ℕ} (hg : Computable g) :
    ∃ p r : ℕ,
      (∀ a b z, phi p (Nat.pair a (Nat.pair b z)) = firstFamily g a b z) ∧
      AuxiliaryIndex (partialFamilyCompiler p) r ∧
      IsFirstSelector g (selfSpecialize r) := by
  obtain ⟨p, hp⟩ := partial_family_index (first_family_partial hg)
  obtain ⟨r, hr, _, hh⟩ := specified_partial_family_selector p hp
  refine ⟨p, r, hp, hr, ?_⟩
  intro e L z
  simpa [firstSelector, firstFamily, Nat.unpair_pair, FiniteSequenceCoding.decode_code]
    using hh (Nat.pair e (FiniteSequenceCoding.code L)) z

theorem second_selector_exists {g : ℕ → ℕ} (hg : Computable g) :
    ∃ p r : ℕ,
      (∀ a b z, phi p (Nat.pair a (Nat.pair b z)) = secondFamily g a b z) ∧
      AuxiliaryIndex (partialFamilyCompiler p) r ∧
      IsSecondSelector g (selfSpecialize r) := by
  obtain ⟨p, hp⟩ := partial_family_index (second_family_partial hg)
  obtain ⟨r, hr, _, hh⟩ := specified_partial_family_selector p hp
  refine ⟨p, r, hp, hr, ?_⟩
  intro L z
  simpa [secondSelector, secondFamily, FiniteSequenceCoding.decode_code]
    using hh (FiniteSequenceCoding.code L) z

theorem first_cases {g : ℕ → ℕ} {C : Set ℕ} {qn e : ℕ} {L : List ℕ}
    (hred : ReducesZero g C) (hn : IsFirstSelector g qn) (hL : Compatible e L) :
    (g (firstSelector qn e L) ∉ imageValues g L →
      (∀ z, phi (firstSelector qn e L) z = phi e z) ∧
        (firstSelector qn e L ∈ haltsZero ↔ e ∈ haltsZero)) ∧
    (g (firstSelector qn e L) ∈ imageValues g L → e ∉ haltsZero) := by
  constructor
  · intro hfresh
    have heq : ∀ z, phi (firstSelector qn e L) z = phi e z := by
      intro z
      simpa [firstRule, hfresh] using hn e L z
    exact ⟨heq, by change (phi _ 0).Dom ↔ (phi e 0).Dom; rw [heq]⟩
  · intro hc he
    obtain ⟨j, hj, hjeq⟩ := (image_values_membership g L _).mp hc
    have hjhalt : j ∈ haltsZero := (hL j hj).mpr he
    have hnhalt : firstSelector qn e L ∈ haltsZero :=
      (hred _).mpr (hjeq ▸ (hred j).mp hjhalt)
    change (phi (firstSelector qn e L) 0).Dom at hnhalt
    rw [hn e L 0] at hnhalt
    simp only [firstRule, ite_eq_left hc, Part.not_none_dom] at hnhalt

theorem second_escapes {g : ℕ → ℕ} {C : Set ℕ} {qn qm e : ℕ} {L : List ℕ}
    (hred : ReducesZero g C) (hn : IsFirstSelector g qn) (hm : IsSecondSelector g qm)
    (hL : Compatible e L) (hcollision : g (firstSelector qn e L) ∈ imageValues g L) :
    g (secondSelector qm L) ∉ imageValues g L ∧
      secondSelector qm L ∉ haltsZero ∧ e ∉ haltsZero := by
  have he : e ∉ haltsZero := (first_cases hred hn hL).2 hcollision
  have hfresh : g (secondSelector qm L) ∉ imageValues g L := by
    intro hc
    have hmhalt : secondSelector qm L ∈ haltsZero := by
      change (phi (secondSelector qm L) 0).Dom
      rw [hm L 0]
      simp [secondRule, hc]
    obtain ⟨j, hj, hjeq⟩ := (image_values_membership g L _).mp hc
    have hjhalt : j ∈ haltsZero :=
      (hred j).mpr (hjeq.symm ▸ (hred _).mp hmhalt)
    exact he ((hL j hj).mp hjhalt)
  refine ⟨hfresh, ?_, he⟩
  change ¬ (phi (secondSelector qm L) 0).Dom
  rw [hm L 0]
  simp [secondRule, hfresh]

def escapeStep (g : ℕ → ℕ) (qn qm e : ℕ) (L : List ℕ) : ℕ :=
  if g (firstSelector qn e L) ∈ imageValues g L then secondSelector qm L
  else firstSelector qn e L

theorem escape_step_computable {g : ℕ → ℕ} (hg : Computable g) (qn qm : ℕ) :
    Computable₂ (escapeStep g qn qm) := by
  have hn := (selectors_primitive qn qm).1.to_comp
  have hm := (selectors_primitive qn qm).2.to_comp
  have ht : Computable (fun p : ℕ × List ℕ =>
      decide (g (firstSelector qn p.1 p.2) ∈ imageValues g p.2)) :=
    membership_computable.comp ((image_values_computable hg).comp Computable.snd)
      (hg.comp hn)
  change Computable (fun p : ℕ × List ℕ => escapeStep g qn qm p.1 p.2)
  exact (Computable.cond ht (hm.comp Computable.snd) hn).of_eq
    (fun p => by simp [escapeStep])

theorem escape_step_spec {g : ℕ → ℕ} {C : Set ℕ} {qn qm e : ℕ} {L : List ℕ}
    (hred : ReducesZero g C) (hn : IsFirstSelector g qn) (hm : IsSecondSelector g qm)
    (hL : Compatible e L) :
    g (escapeStep g qn qm e L) ∉ imageValues g L ∧
      (escapeStep g qn qm e L ∈ haltsZero ↔ e ∈ haltsZero) := by
  by_cases hc : g (firstSelector qn e L) ∈ imageValues g L
  · have h := second_escapes hred hn hm hL hc
    simp only [escapeStep, ite_eq_left hc]
    exact ⟨h.1, iff_of_false h.2.1 h.2.2⟩
  · simp only [escapeStep, ite_eq_right hc]
    exact ⟨hc, ((first_cases hred hn hL).1 hc).2⟩

def queryHistory (g : ℕ → ℕ) (qn qm e : ℕ) : ℕ → List ℕ
  | 0 => [e]
  | k + 1 => queryHistory g qn qm e k ++ [escapeStep g qn qm e (queryHistory g qn qm e k)]

def query (g : ℕ → ℕ) (qn qm e : ℕ) : ℕ → ℕ
  | 0 => e
  | k + 1 => escapeStep g qn qm e (queryHistory g qn qm e k)

theorem query_history_identity (g : ℕ → ℕ) (qn qm e k : ℕ) :
    queryHistory g qn qm e k = (List.range (k + 1)).map (query g qn qm e) := by
  induction k with
  | zero => simp [queryHistory, query]
  | succ k ih =>
    simpa [queryHistory, List.range_succ, query] using
      congrArg (fun L => L ++ [query g qn qm e (k + 1)]) ih

theorem query_computable {g : ℕ → ℕ} (hg : Computable g) (qn qm : ℕ) :
    Computable₂ (queryHistory g qn qm) ∧ Computable₂ (query g qn qm) := by
  have ht := escape_step_computable hg qn qm
  have hbase : Computable (fun p : ℕ × ℕ => [p.1]) :=
    Computable.list_cons.comp Computable.fst (Computable.const [])
  have hstep : Computable₂ (fun p : ℕ × ℕ => fun t : ℕ × List ℕ =>
      t.2 ++ [escapeStep g qn qm p.1 t.2]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (ht.comp (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.snd))).to₂
  have hh : Computable₂ (queryHistory g qn qm) :=
    by
      change Computable (fun p : ℕ × ℕ => queryHistory g qn qm p.1 p.2)
      exact (Computable.nat_rec Computable.snd hbase hstep).of_eq
        (fun p => by induction p.2 <;> simp [queryHistory, *])
  refine ⟨hh, ?_⟩
  have hsucc : Computable₂ (fun e k => escapeStep g qn qm e (queryHistory g qn qm e k)) :=
    (ht.comp Computable.fst hh).to₂
  change Computable (fun p : ℕ × ℕ => query g qn qm p.1 p.2)
  exact (Computable.nat_casesOn Computable.snd Computable.fst
    (hsucc.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂).of_eq
    (fun p => by cases p.2 <;> rfl)

theorem query_invariants {g : ℕ → ℕ} {C : Set ℕ} {qn qm : ℕ}
    (hred : ReducesZero g C) (hn : IsFirstSelector g qn) (hm : IsSecondSelector g qm) :
    (∀ e k, Compatible e (queryHistory g qn qm e k) ∧
      (imageValues g (queryHistory g qn qm e k)).Nodup) ∧
    (∀ e k, query g qn qm e k ∈ haltsZero ↔ e ∈ haltsZero) ∧
    ∀ e, Function.Injective (fun k => g (query g qn qm e k)) := by
  have hprefix : ∀ e k, Compatible e (queryHistory g qn qm e k) ∧
      (imageValues g (queryHistory g qn qm e k)).Nodup := by
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
  have hquery : ∀ e k, query g qn qm e k ∈ haltsZero ↔ e ∈ haltsZero := by
    intro e k
    apply (hprefix e k).1
    rw [query_history_identity]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩
  refine ⟨hprefix, hquery, ?_⟩
  intro e
  have hne : ∀ i j, i < j → g (query g qn qm e i) ≠ g (query g qn qm e j) := by
    intro i j hij
    cases j with
    | zero => omega
    | succ j =>
      have hs := (escape_step_spec hred hn hm (hprefix e j).1).1
      have hmem : query g qn qm e i ∈ queryHistory g qn qm e j := by
        rw [query_history_identity]
        exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
      have himage : g (query g qn qm e i) ∈ imageValues g (queryHistory g qn qm e j) :=
        (image_values_membership g _ _).mpr ⟨_, hmem, rfl⟩
      intro heq
      apply hs
      change g (query g qn qm e (j + 1)) ∈ _
      exact heq ▸ himage
  intro i j heq
  rcases lt_trichotomy i j with hlt | he | hgt
  · exact False.elim (hne i j hlt heq)
  · exact he
  · exact False.elim (hne j i hgt heq.symm)

/-- The finite search is defined for all supplied selectors. Under the selector
and reduction hypotheses, its first success is at most the forbidden list length. -/
def avoidancePosition (g : ℕ → ℕ) (qn qm e : ℕ) (F : List ℕ) : ℕ :=
  Myhill.boundedSearch (fun k => decide (g (query g qn qm e k) ∉ F)) (F.length + 1)

def avoidImage (g : ℕ → ℕ) (qn qm e : ℕ) (F : List ℕ) : ℕ :=
  g (query g qn qm e (avoidancePosition g qn qm e F))

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

theorem avoidance_computable {g : ℕ → ℕ} (hg : Computable g) (qn qm : ℕ) :
    Computable₂ (avoidancePosition g qn qm) ∧ Computable₂ (avoidImage g qn qm) := by
  have hq := (query_computable hg qn qm).2
  have ht : Computable₂ (fun p : ℕ × List ℕ => fun k =>
      decide (g (query g qn qm p.1 k) ∉ p.2)) := by
    change Computable (fun p : (ℕ × List ℕ) × ℕ =>
      decide (g (query g qn qm p.1.1 p.2) ∉ p.1.2))
    exact (Primrec.not.to_comp.comp
      (membership_computable.comp (Computable.snd.comp Computable.fst)
        (hg.comp (hq.comp (Computable.fst.comp Computable.fst) Computable.snd)))).of_eq
      (fun p => by simp)
  have ha : Computable₂ (avoidancePosition g qn qm) := by
    exact (bounded_search_computable ht).comp Computable.id
      (Computable.succ.comp (Computable.list_length.comp Computable.snd))
  refine ⟨ha, ?_⟩
  exact hg.comp (hq.comp Computable.fst ha)

theorem avoidance_spec {g : ℕ → ℕ} {C : Set ℕ} {qn qm : ℕ}
    (hred : ReducesZero g C) (hn : IsFirstSelector g qn) (hm : IsSecondSelector g qm)
    (e : ℕ) (F : List ℕ) :
    avoidancePosition g qn qm e F ≤ F.length ∧
      avoidImage g qn qm e F ∉ F ∧
      (∀ k < avoidancePosition g qn qm e F, g (query g qn qm e k) ∈ F) ∧
      (e ∈ haltsZero ↔ avoidImage g qn qm e F ∈ C) := by
  obtain ⟨k, hk, hfresh⟩ := finite_image_escape
    (fun k => g (query g qn qm e k)) ((query_invariants hred hn hm).2.2 e) F
  have hs := bounded_search_success
    (fun k => decide (g (query g qn qm e k) ∉ F)) (by omega : k < F.length + 1)
    (by simpa using hfresh)
  have hf : avoidImage g qn qm e F ∉ F := by
    exact of_decide_eq_true hs.2
  refine ⟨le_trans hs.1 hk, hf, ?_, ?_⟩
  · intro i hi
    have hfalse := (bounded_search_invariant
      (fun k => decide (g (query g qn qm e k) ∉ F)) (F.length + 1)).2.1 i hi
    simpa using hfalse
  · exact ((query_invariants hred hn hm).2.1 e _).symm.trans (hred _)

def outputHistory (g : ℕ → ℕ) (qn qm : ℕ) : ℕ → List ℕ
  | 0 => []
  | e + 1 => outputHistory g qn qm e ++ [avoidImage g qn qm e (outputHistory g qn qm e)]

def replacement (g : ℕ → ℕ) (qn qm e : ℕ) : ℕ :=
  avoidImage g qn qm e (outputHistory g qn qm e)

theorem output_history_identity (g : ℕ → ℕ) (qn qm e : ℕ) :
    outputHistory g qn qm e = (List.range e).map (replacement g qn qm) := by
  induction e with
  | zero => rfl
  | succ e ih =>
    simpa [outputHistory, List.range_succ, replacement] using
      congrArg (fun L => L ++ [replacement g qn qm e]) ih

theorem replacement_computable {g : ℕ → ℕ} (hg : Computable g) (qn qm : ℕ) :
    Computable (outputHistory g qn qm) ∧ Computable (replacement g qn qm) := by
  have hr := (avoidance_computable hg qn qm).2
  have hs : Computable₂ (fun (_ : ℕ) (p : ℕ × List ℕ) =>
      p.2 ++ [avoidImage g qn qm p.1 p.2]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hr.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd))).to₂
  have hh : Computable (outputHistory g qn qm) := by
    exact (Computable.nat_rec Computable.id (Computable.const []) hs).of_eq
      (fun e => by
        have he (k : ℕ) :
            Nat.rec ([] : List ℕ) (fun i L => L ++ [avoidImage g qn qm i L]) k =
              outputHistory g qn qm k := by
          induction k with
          | zero => rfl
          | succ k ih => exact congrArg (fun L => L ++ [avoidImage g qn qm k L]) ih
        exact he e)
  exact ⟨hh, hr.comp Computable.id hh⟩

theorem replacement_spec {g : ℕ → ℕ} {C : Set ℕ} {qn qm : ℕ}
    (hg : Computable g) (hred : ReducesZero g C)
    (hn : IsFirstSelector g qn) (hm : IsSecondSelector g qm) :
    Computable (replacement g qn qm) ∧ Function.Injective (replacement g qn qm) ∧
      ∀ e, e ∈ haltsZero ↔ replacement g qn qm e ∈ C := by
  have hcomp := (replacement_computable hg qn qm).2
  have hne : ∀ i j, i < j → replacement g qn qm i ≠ replacement g qn qm j := by
    intro i j hij heq
    have hs := (avoidance_spec hred hn hm j (outputHistory g qn qm j)).2.1
    change replacement g qn qm j ∉ outputHistory g qn qm j at hs
    have hmemb : replacement g qn qm i ∈ outputHistory g qn qm j := by
      rw [output_history_identity]
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hij, rfl⟩
    exact hs (heq ▸ hmemb)
  refine ⟨hcomp, ?_, fun e => (avoidance_spec hred hn hm e _).2.2.2⟩
  intro i j heq
  rcases lt_trichotomy i j with hlt | he | hgt
  · exact False.elim (hne i j hlt heq)
  · exact he
  · exact False.elim (hne j i hgt heq.symm)

theorem injective_upgrade (C : Set ℕ) : haltsZero ≤₀ C → haltsZero ≤₁ C := by
  rintro ⟨g, hg, hred⟩
  obtain ⟨_, rn, _, _, hn⟩ := first_selector_exists hg
  obtain ⟨_, rm, _, _, hm⟩ := second_selector_exists hg
  exact ⟨replacement g (selfSpecialize rn) (selfSpecialize rm),
    replacement_spec hg hred hn hm⟩

end Lemmatheca.ComputabilityTheory.CreativeIsomorphism
