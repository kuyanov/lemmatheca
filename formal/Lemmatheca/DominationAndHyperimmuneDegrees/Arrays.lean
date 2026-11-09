import Lemmatheca.DominationAndHyperimmuneDegrees.Principal
import Lemmatheca.SimpleSets.Immunity

/-! Strong arrays with computable complete finite descriptions. -/
namespace Lemmatheca.ComputabilityTheory.HyperimmuneDegrees

open OracleComputation TuringDegrees UniversalComputation
open EffectiveEnumerations

noncomputable section
set_option backward.isDefEq.respectTransparency false

def arraySet (d : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (FiniteSequenceCoding.decode (d n)).toFinset

def StrongArray (d : ℕ → ℕ) : Prop :=
  Computable d ∧ ∀ i j, i ≠ j → Disjoint (arraySet d i) (arraySet d j)

def ArrayHits (d : ℕ → ℕ) (X : Set ℕ) : Prop :=
  ∀ n, ∃ x, x ∈ arraySet d n ∧ x ∈ X

def arrayMaximum (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((List.range (n + 1)).flatMap (fun i => FiniteSequenceCoding.decode (d i))).foldl max 0

private theorem fold_max_le (xs : List ℕ) (a b : ℕ) :
    xs.foldl max a ≤ b ↔ a ≤ b ∧ ∀ x ∈ xs, x ≤ b := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, and_assoc]

theorem array_maximum_computable (d : ℕ → ℕ) (hd : Computable d) :
    Computable (arrayMaximum d) := by
  have hc : Computable (fun i => FiniteSequenceCoding.decode (d i)) :=
    (Primrec.ofNat (List ℕ)).to_comp.comp hd
  let grow : ℕ → List ℕ := Nat.rec (FiniteSequenceCoding.decode (d 0))
    (fun k previous => previous ++ FiniteSequenceCoding.decode (d (k + 1)))
  have hs : Computable₂ (fun (_ : ℕ) (p : ℕ × List ℕ) =>
      p.2 ++ FiniteSequenceCoding.decode (d (p.1 + 1))) :=
    (Primrec.list_append.to_comp.comp (Computable.snd.comp Computable.snd)
      ((hc.comp Computable.succ).comp (Computable.fst.comp Computable.snd))).to₂
  have hg : Computable grow := Computable.nat_rec Computable.id (Computable.const _) hs
  have he : ∀ n, grow n = (List.range (n + 1)).flatMap (fun i => FiniteSequenceCoding.decode (d i)) := by
    intro n
    induction n with
    | zero => simp [grow]
    | succ n ih =>
      change grow n ++ FiniteSequenceCoding.decode (d (n + 1)) = _
      rw [ih]
      simp [List.range_succ]
  have hfold : Primrec (fun l : List ℕ => l.foldl max 0) :=
    Primrec.list_foldl Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact hfold.to_comp.comp (hg.of_eq he)

theorem array_hits_bounds_principal (X : Set ℕ) (hX : X.Infinite) (d : ℕ → ℕ)
    (hd : StrongArray d) (hh : ArrayHits d X) :
    Majorizes (arrayMaximum d) (increasingList X hX) := by
  classical
  intro n
  by_contra hn
  let p := increasingList X hX
  have hlt : arrayMaximum d n < p n := by exact lt_of_not_ge hn
  let value : Fin (n + 1) → ℕ := fun i => Classical.choose (hh i.val)
  have hvD (i : Fin (n + 1)) : value i ∈ arraySet d i.val := (Classical.choose_spec (hh i.val)).1
  have hvX (i : Fin (n + 1)) : value i ∈ X := (Classical.choose_spec (hh i.val)).2
  have hvH (i : Fin (n + 1)) : value i ≤ arrayMaximum d n := by
    apply ((fold_max_le _ 0 (arrayMaximum d n)).mp le_rfl).2
    apply List.mem_flatMap.mpr
    exact ⟨i.val, List.mem_range.mpr i.isLt, List.mem_toFinset.mp (hvD i)⟩
  have hex (i : Fin (n + 1)) : ∃ j : Fin n, p j.val = value i := by
    obtain ⟨j, hj, he⟩ := (increasing_list_correct X hX).2 n (value i) (hvX i)
      ((hvH i).trans hlt.le)
    have hjn : j < n := by
      by_contra h
      have heq : j = n := by omega
      subst j
      have hb := (hvH i).trans_lt hlt
      change value i < increasingList X hX n at hb
      omega
    exact ⟨⟨j, hjn⟩, he⟩
  let rank : Fin (n + 1) → Fin n := fun i => Classical.choose (hex i)
  have hr (i : Fin (n + 1)) : p (rank i).val = value i := Classical.choose_spec (hex i)
  have hinj : Function.Injective rank := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    have heq : value i = value j := (hr i).symm.trans
      ((congrArg (fun z : Fin n => p z.val) hij).trans (hr j))
    have hj : value i ∈ arraySet d j.val := by
      rw [heq]
      exact hvD j
    exact Finset.disjoint_left.mp (hd.2 i.val j.val hne) (hvD i) hj
  have hcard := Fintype.card_le_of_injective rank hinj
  simp only [Fintype.card_fin] at hcard
  omega

def intervalEndpoints (h : ℕ → ℕ) : ℕ → ℕ :=
  Nat.rec 0 (fun _ b => 1 + max b (h b))

def intervalArray (h : ℕ → ℕ) (n : ℕ) : ℕ :=
  FiniteSequenceCoding.code (List.range' (intervalEndpoints h n)
    (intervalEndpoints h (n + 1) - intervalEndpoints h n))

private theorem interval_membership (h : ℕ → ℕ) (n x : ℕ) :
    x ∈ arraySet (intervalArray h) n ↔
      intervalEndpoints h n ≤ x ∧ x < intervalEndpoints h (n + 1) := by
  have hl : intervalEndpoints h n ≤ intervalEndpoints h (n + 1) := by
    change intervalEndpoints h n ≤ 1 + max (intervalEndpoints h n) (h (intervalEndpoints h n))
    have := le_max_left (intervalEndpoints h n) (h (intervalEndpoints h n))
    omega
  simp only [arraySet, intervalArray, FiniteSequenceCoding.decode_code, List.mem_toFinset,
    List.mem_range'_1, Nat.add_sub_of_le hl]

theorem interval_array_spec (h : ℕ → ℕ) (hh : Computable h) :
    StrongArray (intervalArray h) ∧ StrictMono (intervalEndpoints h) ∧
      ∀ n x, x ∈ arraySet (intervalArray h) n ↔
        intervalEndpoints h n ≤ x ∧ x < intervalEndpoints h (n + 1) := by
  have hb : StrictMono (intervalEndpoints h) := by
    apply strictMono_nat_of_lt_succ
    intro n
    change intervalEndpoints h n < 1 + max (intervalEndpoints h n) (h (intervalEndpoints h n))
    have := le_max_left (intervalEndpoints h n) (h (intervalEndpoints h n))
    omega
  have hs : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ) => 1 + max p.2 (h p.2)) :=
    (Primrec.nat_add.to_comp.comp (Computable.const 1)
      (Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
        (hh.comp (Computable.snd.comp Computable.snd)))).to₂
  have hc : Computable (intervalEndpoints h) :=
    Computable.nat_rec Computable.id (Computable.const 0) hs
  have hr : Primrec (fun p : ℕ × ℕ => List.range' p.1 p.2) := by
    simpa only [List.range'_eq_map_range] using
      (Primrec.list_map (Primrec.list_range.comp Primrec.snd)
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
  have hlen : Computable (fun n => intervalEndpoints h (n + 1) - intervalEndpoints h n) :=
    Primrec.nat_sub.to_comp.comp (hc.comp Computable.succ) hc
  have hd : Computable (intervalArray h) :=
    Primrec.encode.to_comp.comp (hr.to_comp.comp (hc.pair hlen))
  refine ⟨⟨hd, ?_⟩, hb, interval_membership h⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hi := (interval_membership h i x).mp hxi
  have hj := (interval_membership h j x).mp hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have := hb.monotone (show i + 1 ≤ j by omega)
    omega
  · have := hb.monotone (show j + 1 ≤ i by omega)
    omega

theorem principal_majorant_interval_hits (X : Set ℕ) (hX : X.Infinite) (h : ℕ → ℕ)
    (hh : Majorizes h (increasingList X hX)) :
    ArrayHits (intervalArray h) X := by
  intro n
  let b := intervalEndpoints h n
  let p := increasingList X hX
  refine ⟨p b, (interval_membership h n _).mpr ?_, ?_⟩
  · have hlo : b ≤ p b := (increasing_list_correct X hX).1.1.le_apply
    have hup := hh b
    have hnext : h b < intervalEndpoints h (n + 1) := by
      change h b < 1 + max b (h b)
      have := le_max_right b (h b)
      omega
    exact ⟨hlo, hup.trans_lt hnext⟩
  · rw [← (increasing_list_correct X hX).1.2]
    exact ⟨b, rfl⟩

theorem array_characterization (X : Set ℕ) (hX : X.Infinite) :
    (∃ h : ℕ → ℕ, Computable h ∧ Majorizes h (increasingList X hX)) ↔
      ∃ d : ℕ → ℕ, StrongArray d ∧ ArrayHits d X := by
  constructor
  · rintro ⟨h, hc, hb⟩
    exact ⟨intervalArray h, (interval_array_spec h hc).1,
      principal_majorant_interval_hits X hX h hb⟩
  · rintro ⟨d, hd, hh⟩
    exact ⟨arrayMaximum d, array_maximum_computable d hd.1,
      array_hits_bounds_principal X hX d hd hh⟩

theorem hyperimmune_iff_no_array (X : Set ℕ) :
    HyperimmuneSet X ↔ X.Infinite ∧ ¬ ∃ d : ℕ → ℕ, StrongArray d ∧ ArrayHits d X := by
  constructor
  · rintro ⟨hX, hh⟩
    refine ⟨hX, ?_⟩
    intro ha
    exact (hyperimmune_iff_no_majorant _).mp hh ((array_characterization X hX).mpr ha)
  · rintro ⟨hX, hh⟩
    refine ⟨hX, (hyperimmune_iff_no_majorant _).mpr ?_⟩
    intro hb
    exact hh ((array_characterization X hX).mp hb)

theorem hyperimmune_implies_immune (X : Set ℕ) (hX : HyperimmuneSet X) :
    SimpleSets.Immune X := by
  classical
  have hno := ((hyperimmune_iff_no_array X).mp hX).2
  obtain ⟨hInf, _⟩ := hX
  refine ⟨hInf, ?_⟩
  intro W hW hWX
  by_contra hfinite
  obtain ⟨B, hBW, hB, hc⟩ := infinite_enumerable_decidable_subset W hW hfinite
  let g := increasingList B hB
  have hg : StrictMono g := (increasing_list_correct B hB).1.1
  have hgc : Computable g := increasing_list_computable B hB hc
  let d := fun n => FiniteSequenceCoding.code [g n]
  have hd : StrongArray d := by
    refine ⟨Primrec.encode.to_comp.comp
      (Primrec.list_cons.to_comp.comp hgc (Computable.const [])), ?_⟩
    intro i j hij
    have hne : g i ≠ g j := fun h => hij (hg.injective h)
    simpa [arraySet, d] using hne
  have hh : ArrayHits d X := by
    intro n
    refine ⟨g n, by simp [arraySet, d], hWX (hBW ?_)⟩
    rw [← (increasing_list_correct B hB).1.2]
    exact ⟨n, rfl⟩
  exact hno ⟨d, hd, hh⟩

end
end Lemmatheca.ComputabilityTheory.HyperimmuneDegrees
