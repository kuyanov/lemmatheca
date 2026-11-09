import Lemmatheca.EffectiveEnumerations.Increasing

/-! Suppress repetitions while retaining the whole range of an infinite stream. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveEnumerations

open UniversalComputation Encodable Denumerable

theorem fresh_exists (q : ℕ → ℕ) (hq : (Set.range q).Infinite) (L : List ℕ) :
    ∃ t, q t ∉ L := by
  classical
  by_contra hn
  push Not at hn
  apply hq
  exact (L.toFinset.finite_toSet).subset (by
    rintro y ⟨t, rfl⟩
    simpa using hn t)

noncomputable def freshIndex (q : ℕ → ℕ) (hq : (Set.range q).Infinite) (L : List ℕ) : ℕ :=
  Nat.find (fresh_exists q hq L)

theorem fresh_index_spec (q : ℕ → ℕ) (hq : (Set.range q).Infinite) (L : List ℕ) :
    q (freshIndex q hq L) ∉ L ∧ ∀ t, q t ∉ L → freshIndex q hq L ≤ t := by
  exact ⟨Nat.find_spec (fresh_exists q hq L), fun t ht => Nat.find_min' _ ht⟩

theorem fresh_index_computable (q : ℕ → ℕ) (hq : (Set.range q).Infinite)
    (hc : Computable q) : Computable (freshIndex q hq) := by
  classical
  have hmem : ComputablePred (fun p : List ℕ × ℕ => q p.2 ∈ p.1) := by
    have hb : Computable (fun p : List ℕ × ℕ => decide (∃ a ∈ p.1, a = p.2)) :=
      (PrimrecRel.exists_mem_list (Primrec.eq : PrimrecRel (fun a b : ℕ => a = b))).decide.to_comp
    apply Computable.computablePred
    exact (hb.comp (Computable.fst.pair (hc.comp Computable.snd))).of_eq (fun p => by simp)
  exact Computable.find hmem.not (fresh_exists q hq)

noncomputable def freshHistory (q : ℕ → ℕ) (hq : (Set.range q).Infinite) : ℕ → List ℕ :=
  Nat.rec [] (fun _ L => L ++ [q (freshIndex q hq L)])

noncomputable def injectiveStream (q : ℕ → ℕ) (hq : (Set.range q).Infinite) (n : ℕ) : ℕ :=
  q (freshIndex q hq (freshHistory q hq n))

theorem fresh_history_computable (q : ℕ → ℕ) (hq : (Set.range q).Infinite)
    (hc : Computable q) : Computable (freshHistory q hq) ∧ Computable (injectiveStream q hq) := by
  have hj := fresh_index_computable q hq hc
  have hh : Computable₂ (fun (_ : ℕ) (z : ℕ × List ℕ) =>
      z.2 ++ [q (freshIndex q hq z.2)]) :=
    Primrec.list_concat.to_comp.comp (Computable.snd.comp Computable.snd)
      (hc.comp (hj.comp (Computable.snd.comp Computable.snd)))
  have hL : Computable (freshHistory q hq) :=
    Computable.nat_rec Computable.id (Computable.const []) hh
  exact ⟨hL, hc.comp (hj.comp hL)⟩

theorem fresh_history_invariant (q : ℕ → ℕ) (hq : (Set.range q).Infinite) (n : ℕ) :
    freshHistory q hq n = (List.range n).map (injectiveStream q hq) ∧
      (freshHistory q hq n).length = n ∧ (freshHistory q hq n).Nodup ∧
      ∀ y ∈ freshHistory q hq n, y ∈ Set.range q := by
  induction n with
  | zero => simp [freshHistory]
  | succ n ih =>
    obtain ⟨heq, hlen, hnodup, hmem⟩ := ih
    have hf : injectiveStream q hq n ∉ freshHistory q hq n :=
      (fresh_index_spec q hq _).1
    change (freshHistory q hq n ++ [injectiveStream q hq n]) =
        (List.range (n + 1)).map (injectiveStream q hq) ∧
      (freshHistory q hq n ++ [injectiveStream q hq n]).length = n + 1 ∧
      (freshHistory q hq n ++ [injectiveStream q hq n]).Nodup ∧
      ∀ y ∈ freshHistory q hq n ++ [injectiveStream q hq n], y ∈ Set.range q
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.range_succ, List.map_append, List.map_singleton, ← heq]
    · simp [hlen]
    · simpa only [List.concat_eq_append] using List.Nodup.concat hf hnodup
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hmem y hy
      · have hy' : y = injectiveStream q hq n := List.mem_singleton.mp hy
        exact hy' ▸ ⟨freshIndex q hq (freshHistory q hq n), rfl⟩

theorem injective_stream_correct (q : ℕ → ℕ) (hq : (Set.range q).Infinite)
    (hc : Computable q) :
    Computable (injectiveStream q hq) ∧ Function.Injective (injectiveStream q hq) ∧
      Set.range (injectiveStream q hq) = Set.range q := by
  have hprior : ∀ i n, i < n → injectiveStream q hq i ∈ freshHistory q hq n := by
    intro i n hin
    rw [(fresh_history_invariant q hq n).1]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hin, rfl⟩
  have hinj : Function.Injective (injectiveStream q hq) := by
    intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim ((fresh_index_spec q hq _).1 (hij ▸ hprior i j h))
    · exact h
    · exact False.elim ((fresh_index_spec q hq _).1 (hij.symm ▸ hprior j i h))
  let j := fun n => freshIndex q hq (freshHistory q hq n)
  have hstep : ∀ n, j n < j (n + 1) := by
    intro n
    by_contra hn
    have hle : j (n + 1) ≤ j n := Nat.le_of_not_gt hn
    have hnxt : q (j (n + 1)) ∉ freshHistory q hq (n + 1) := (fresh_index_spec q hq _).1
    have hold : q (j (n + 1)) ∉ freshHistory q hq n := by
      intro hm
      apply hnxt
      change q (j (n + 1)) ∈ freshHistory q hq n ++ [q (j n)]
      exact List.mem_append_left _ hm
    have hrev : j n ≤ j (n + 1) := (fresh_index_spec q hq _).2 _ hold
    have heq : j (n + 1) = j n := le_antisymm hle hrev
    apply hnxt
    change q (j (n + 1)) ∈ freshHistory q hq n ++ [q (j n)]
    simp [heq]
  have hgrow : ∀ n, n ≤ j n := fun n => (strictMono_nat_of_lt_succ hstep).le_apply
  refine ⟨(fresh_history_computable q hq hc).2, hinj, ?_⟩
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨j n, rfl⟩
  · rintro ⟨t, rfl⟩
    have hm : q t ∈ freshHistory q hq (t + 1) := by
      by_contra hn
      have hle : j (t + 1) ≤ t := (fresh_index_spec q hq _).2 t hn
      have hlo := hgrow (t + 1)
      omega
    rw [(fresh_history_invariant q hq (t + 1)).1] at hm
    obtain ⟨n, _, hn⟩ := List.mem_map.mp hm
    exact ⟨n, hn⟩

theorem infinite_ce_injective_enumeration (A : Set ℕ) (hA : REPred A) (hInf : A.Infinite) :
    ∃ g : ℕ → ℕ, Computable g ∧ Function.Injective g ∧ Set.range g = A := by
  obtain hEmpty | ⟨q, hc, hr⟩ := (enumerable_iff_total_range A).mp hA
  · obtain ⟨a, ha⟩ := hInf.nonempty
    exact False.elim (hEmpty a ha)
  · have heq : Set.range q = A := Set.ext (fun y => (hr y).symm)
    have hq : (Set.range q).Infinite := heq.symm ▸ hInf
    obtain ⟨hg, hinj, hfull⟩ := injective_stream_correct q hq hc
    exact ⟨injectiveStream q hq, hg, hinj, hfull.trans heq⟩

theorem halting_infinite : haltingDiagonal.Infinite := by
  let f : ℕ → ℕ := fun n => encode (Nat.Partrec.Code.const n)
  have hf : Function.Injective f := by
    intro a b hab
    have hc : Nat.Partrec.Code.const a = Nat.Partrec.Code.const b := Encodable.encode_injective hab
    have hv := congrArg (fun c => Nat.Partrec.Code.eval c 0) hc
    simpa using hv
  apply (Set.infinite_range_of_injective hf).mono
  rintro e ⟨n, rfl⟩
  simp [haltingDiagonal, phi, f]

end Lemmatheca.ComputabilityTheory.EffectiveEnumerations
