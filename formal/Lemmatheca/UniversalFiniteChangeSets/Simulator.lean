import Lemmatheca.FiniteMindChanges.Operations
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursiveAutomation

/-! A total revision-capped simulation of every ordinary approximation candidate. -/
namespace Lemmatheca.ComputabilityTheory.UniversalFiniteChangeSets

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges

set_option backward.isDefEq.respectTransparency false

abbrev State := ℕ × (ℕ × ℕ)

def step (n e x s : ℕ) (z : State) : State :=
  if z.2.2 < n then
    let v := boundedValue s e (Nat.pair z.1 x)
    if v = 1 ∨ v = 2 then
      (z.1 + 1, (v - 1, z.2.2 + if v - 1 = z.2.1 then 0 else 1))
    else z
  else z

def simulation (n e x : ℕ) : ℕ → State
  | 0 => (0, (0, 0))
  | s + 1 => step n e x s (simulation n e x s)

def universalGuess (n e s x : ℕ) : ℕ := (simulation n e x s).2.1

def rowSet (n e : ℕ) : Set ℕ :=
  {x | ∃ t, ∀ s, t ≤ s → universalGuess n e s x = 1}

def Presents (e : ℕ) (a : Approximation) : Prop :=
  ∀ k x, phi e (Nat.pair k x) = Part.some (a k x)

theorem simulation_invariants (n e x s : ℕ) :
    ((simulation n e x s).2.1 = 0 ∨ (simulation n e x s).2.1 = 1) ∧
      (simulation n e x s).2.2 ≤ n ∧
      (simulation n e x s).2.2 = changeCount (universalGuess n e) s x ∧
      (simulation n e x s).1 ≤ (simulation n e x (s + 1)).1 := by
  induction s with
  | zero =>
      simp [simulation, changeCount]
  | succ s ih =>
      have hnext : ∀ t, (simulation n e x t).1 ≤ (simulation n e x (t + 1)).1 := by
        intro t
        simp only [simulation, step]
        split_ifs <;> simp
      refine ⟨?_, ?_, ?_, hnext (s + 1)⟩
      · rcases ih.1 with h | h <;>
          simp only [simulation, step] <;> split_ifs with hc hv <;> simp_all
        all_goals omega
      · simp only [simulation, step]
        split_ifs with hc hv he <;> simp_all <;> omega
      · change (step n e x s (simulation n e x s)).2.2 =
          changeCount (universalGuess n e) s x +
            if (step n e x s (simulation n e x s)).2.1 =
              (simulation n e x s).2.1 then 0 else 1
        simp only [step]
        split_ifs with hc hv he <;> simp_all

theorem guess_computable :
    Computable (fun p : ((ℕ × ℕ) × ℕ) × ℕ =>
      universalGuess p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hs : Primrec (fun p : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × State) =>
      step p.1.1.1.1 p.1.1.1.2 p.1.2 p.2.1 p.2.2) := by
    unfold step
    have ht : Primrec (fun p : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × State) =>
        ((p.2.1, p.1.1.1.2), Nat.pair p.2.2.1 p.1.2)) := by fun_prop
    have hv := boundedValue_primitive.comp ht
    have hc : Primrec (fun p : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × State) =>
        decide (boundedValue p.2.1 p.1.1.1.2 (Nat.pair p.2.2.1 p.1.2) = 1 ∨
          boundedValue p.2.1 p.1.1.1.2 (Nat.pair p.2.2.1 p.1.2) = 2)) :=
      PrimitiveRecursiveAutomation.orPred (by fun_prop) (by fun_prop)
    exact PrimitiveRecursiveAutomation.ite (by fun_prop)
      (PrimitiveRecursiveAutomation.ite hc (by fun_prop) (by fun_prop)) (by fun_prop)
  have hr : Computable (fun p : ((ℕ × ℕ) × ℕ) × ℕ =>
      simulation p.1.1.1 p.1.1.2 p.2 p.1.2) := by
    apply (Computable.nat_rec (Computable.snd.comp Computable.fst)
      (Computable.const (0, (0, 0))) hs.to_comp.to₂).of_eq
    intro p
    induction p.1.2 with
    | zero => rfl
    | succ s ih => simp only [simulation, ih]
  exact (Computable.fst.comp (Computable.snd.comp hr)).of_eq fun _ => rfl

theorem row_converges (n e : ℕ) :
    Converges (universalGuess n e) (rowSet n e) := by
  classical
  have hb : Binary (universalGuess n e) := fun s x => (simulation_invariants n e x s).1
  have hn : AtMostChanges (universalGuess n e) n := by
    intro s x
    have h := simulation_invariants n e x s
    omega
  obtain ⟨A, hA⟩ := bounded_counts_converge (universalGuess n e) n hb hn
  have heq : rowSet n e = A := by
    ext x
    obtain ⟨t, ht⟩ := hA x
    constructor
    · rintro ⟨u, hu⟩
      have h₁ := ht (max t u) (le_max_left _ _)
      have h₂ := hu (max t u) (le_max_right _ _)
      by_contra hx
      have hx' : ¬ A x := hx
      simp [indicator, hx'] at h₁
      omega
    · intro hx
      refine ⟨t, fun s hs => ?_⟩
      have hx' : A x := hx
      simpa [indicator, hx'] using ht s hs
  rw [heq]
  exact hA

theorem presents_exists (a : Approximation) (ha : Computable₂ a) :
    ∃ e, Presents e a := by
  have hf : Computable (fun z : ℕ => a z.unpair.1 z.unpair.2) :=
    ha.comp (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair)
  obtain ⟨e, he⟩ := phi_complete (Partrec.nat_iff.mp hf.partrec)
  refine ⟨e, fun k x => ?_⟩
  simp [he]

private theorem supplied_value (e : ℕ) (a : Approximation) (hp : Presents e a)
    (s k x : ℕ) (h : boundedValue s e (Nat.pair k x) = 1 ∨
      boundedValue s e (Nat.pair k x) = 2) :
    boundedValue s e (Nat.pair k x) - 1 = a k x := by
  have hv : boundedValue s e (Nat.pair k x) =
      (boundedValue s e (Nat.pair k x) - 1) + 1 := by omega
  exact Part.mem_unique ((phi_output e (Nat.pair k x) _).mpr ⟨s, hv⟩)
    (Part.eq_some_iff.mp (hp k x))

private theorem cursor_monotone (n e x : ℕ) :
    Monotone (fun s => (simulation n e x s).1) :=
  monotone_nat_of_le_succ fun s => (simulation_invariants n e x s).2.2.2

private theorem exhausted_constant (a : Approximation) (n r x : ℕ)
    (hn : AtMostChanges a n) (h : changeCount a r x = n) :
    ∀ t, r ≤ t → a t x = a r x := by
  intro t ht
  by_contra he
  have hstrict := changeCount_strict_of_ne a x ht (Ne.symm he)
  have hbound := hn t x
  omega

theorem faithful_prefix (n e : ℕ) (a : Approximation) (hp : Presents e a)
    (_hb : Binary a) (hz : StartsZero a) (hn : AtMostChanges a n) (x s : ℕ) :
    (simulation n e x s).2.1 = a ((simulation n e x s).1 - 1) x ∧
      (simulation n e x s).2.2 = changeCount a ((simulation n e x s).1 - 1) x ∧
      ((simulation n e x s).2.2 = n →
        ∀ t, (simulation n e x s).1 - 1 ≤ t →
          a t x = (simulation n e x s).2.1) := by
  have hcore : ∀ s,
      (simulation n e x s).2.1 = a ((simulation n e x s).1 - 1) x ∧
      (simulation n e x s).2.2 = changeCount a ((simulation n e x s).1 - 1) x := by
    intro s
    induction s with
    | zero => simp [simulation, changeCount, hz x]
    | succ s ih =>
        by_cases hc : (simulation n e x s).2.2 < n
        · by_cases hv : boundedValue s e (Nat.pair (simulation n e x s).1 x) = 1 ∨
              boundedValue s e (Nat.pair (simulation n e x s).1 x) = 2
          · have ha := supplied_value e a hp s (simulation n e x s).1 x hv
            simp only [simulation, step, ite_eq_left hc, ite_eq_left hv, Nat.add_sub_cancel]
            constructor
            · exact ha
            · rw [ha, ih.1, ih.2]
              by_cases hk : (simulation n e x s).1 = 0
              · simp [hk, hz x, changeCount]
              · have hk' : (simulation n e x s).1 =
                    ((simulation n e x s).1 - 1) + 1 := by omega
                conv_rhs => rw [hk', changeCount]
                rw [← hk']
          · simpa only [simulation, step, ite_eq_left hc, ite_eq_right hv] using ih
        · simpa only [simulation, step, ite_eq_right hc] using ih
  refine ⟨(hcore s).1, (hcore s).2, ?_⟩
  intro he t ht
  have hh : changeCount a ((simulation n e x s).1 - 1) x = n := by
    rw [← (hcore s).2, he]
  exact (exhausted_constant a n _ x hn hh t ht).trans (hcore s).1.symm

theorem progress_or_exhaustion (n e : ℕ) (a : Approximation) (hp : Presents e a)
    (hb : Binary a) (hz : StartsZero a) (hn : AtMostChanges a n) (x m : ℕ) :
    ∃ s, m ≤ (simulation n e x s).1 ∨ (simulation n e x s).2.2 = n := by
  induction m with
  | zero => exact ⟨0, Or.inl (Nat.zero_le _)⟩
  | succ m ih =>
      obtain ⟨t, ht | ht⟩ := ih
      · by_cases hm : m + 1 ≤ (simulation n e x t).1
        · exact ⟨t, Or.inl hm⟩
        have hmt : (simulation n e x t).1 = m := by omega
        have hav : a m x ∈ phi e (Nat.pair m x) := Part.eq_some_iff.mp (hp m x)
        obtain ⟨k, hk⟩ := (phi_output e (Nat.pair m x) _).mp hav
        let u := max t k
        have hcur : m ≤ (simulation n e x u).1 := by
          rw [← hmt]
          exact cursor_monotone n e x (le_max_left _ _)
        by_cases hm' : m + 1 ≤ (simulation n e x u).1
        · exact ⟨u, Or.inl hm'⟩
        have hmu : (simulation n e x u).1 = m := by omega
        by_cases hc : (simulation n e x u).2.2 = n
        · exact ⟨u, Or.inr hc⟩
        have hcn : (simulation n e x u).2.2 < n := by
          have hcount := (faithful_prefix n e a hp hb hz hn x u).2.1
          have hbound := hn ((simulation n e x u).1 - 1) x
          omega
        have hval : boundedValue u e (Nat.pair m x) = a m x + 1 :=
          (boundedValue_output _ _ _ _).mpr
            (Nat.Partrec.Code.evaln_mono (le_max_right t k)
              ((boundedValue_output _ _ _ _).mp hk))
        have hv : boundedValue u e (Nat.pair m x) = 1 ∨
            boundedValue u e (Nat.pair m x) = 2 := by
          rcases hb m x with h | h <;> simp [hval, h]
        refine ⟨u + 1, Or.inl ?_⟩
        simp [simulation, step, hcn, hmu, hv]
      · exact ⟨t, Or.inr ht⟩

theorem faithful_limits (n e : ℕ) (a : Approximation) (A : Set ℕ)
    (hp : Presents e a) (hb : Binary a) (hz : StartsZero a)
    (hn : AtMostChanges a n) (hl : Converges a A) : rowSet n e = A := by
  classical
  have hlim : Converges (universalGuess n e) A := by
    intro x
    obtain ⟨t, ht⟩ := hl x
    obtain ⟨s, hcur | hfull⟩ := progress_or_exhaustion n e a hp hb hz hn x (t + 1)
    · refine ⟨s, fun u hu => ?_⟩
      have hm : (simulation n e x s).1 ≤ (simulation n e x u).1 := cursor_monotone n e x hu
      have hind : t ≤ (simulation n e x u).1 - 1 := by omega
      exact (faithful_prefix n e a hp hb hz hn x u).1.trans (ht _ hind)
    · have hprefix := faithful_prefix n e a hp hb hz hn x s
      have hbval : (simulation n e x s).2.1 = indicator A x := by
        have he := hprefix.2.2 hfull (max t ((simulation n e x s).1 - 1))
          (le_max_right _ _)
        exact he.symm.trans (ht _ (le_max_left _ _))
      refine ⟨s, fun u hu => ?_⟩
      have hm : (simulation n e x s).1 ≤ (simulation n e x u).1 := cursor_monotone n e x hu
      have he := hprefix.2.2 hfull ((simulation n e x u).1 - 1) (by omega)
      exact (faithful_prefix n e a hp hb hz hn x u).1.trans (he.trans hbval)
  ext x
  obtain ⟨t, ht⟩ := hlim x
  constructor
  · rintro ⟨u, hu⟩
    have h₁ := ht (max t u) (le_max_left _ _)
    have h₂ := hu (max t u) (le_max_right _ _)
    by_contra hx
    have hx' : ¬ A x := hx
    simp [indicator, hx'] at h₁
    omega
  · intro hx
    refine ⟨t, fun s hs => ?_⟩
    have hx' : A x := hx
    simpa [indicator, hx'] using ht s hs

theorem zero_simulation (e x s : ℕ) : simulation 0 e x s = (0, (0, 0)) := by
  induction s with
  | zero => rfl
  | succ s ih => simp [simulation, step, ih]

theorem partial_first_simulation (n e x : ℕ) (h : ¬ (phi e (Nat.pair 0 x)).Dom) :
    ∀ s, simulation n e x s = (0, (0, 0)) := by
  have hv : ∀ s, boundedValue s e (Nat.pair 0 x) = 0 := by
    intro s
    by_contra hn
    have hp : boundedValue s e (Nat.pair 0 x) =
        (boundedValue s e (Nat.pair 0 x) - 1) + 1 := by omega
    have hm := (phi_output e (Nat.pair 0 x) _).mpr ⟨s, hp⟩
    exact h (Part.dom_iff_mem.mpr ⟨_, hm⟩)
  intro s
  induction s with
  | zero => rfl
  | succ s ih => simp [simulation, step, ih, hv]

end Lemmatheca.ComputabilityTheory.UniversalFiniteChangeSets
