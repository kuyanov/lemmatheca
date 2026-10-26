import Lemmatheca.OracleComputation.Substitution

/-! Actual two-query programs, incomplete searches, and empty-oracle boundary cases. -/
namespace Lemmatheca.Entry.OracleComputation

open Lemmatheca.ComputabilityTheory.OracleComputation
open Lemmatheca.ComputabilityTheory.UniversalComputation

set_option backward.isDefEq.respectTransparency false

private theorem indicator_bit (A : Set ℕ) (x : ℕ) :
    indicator (fun n => n ∈ A) x = 0 ∨ indicator (fun n => n ∈ A) x = 1 := by
  classical
  by_cases h : x ∈ A <;> simp [indicator,h]

def twoQuery : Code := .pair .query (.comp .query .succ)

theorem twoQuery_eval (A : Set ℕ) (x : ℕ) :
    eval A twoQuery x = Part.some
      (Nat.pair (indicator (fun n => n ∈ A) x) (indicator (fun n => n ∈ A) (x + 1))) := by
  simp [twoQuery,eval]

theorem twoQuery_trace (A : Set ℕ) (x : ℕ) :
    Derives twoQuery x
      [(x, indicator (fun n => n ∈ A) x), (x + 1, indicator (fun n => n ∈ A) (x + 1))]
      (Nat.pair (indicator (fun n => n ∈ A) x) (indicator (fun n => n ∈ A) (x + 1))) ∧
    Consistent A
      [(x, indicator (fun n => n ∈ A) x), (x + 1, indicator (fun n => n ∈ A) (x + 1))] := by
  constructor
  · exact .pair (.query _ _ (indicator_bit A x))
      (.comp (.succ x) (.query _ _ (indicator_bit A (x+1))))
  · simp only [Consistent,List.mem_cons,Prod.mk.injEq]
    aesop

theorem twoQuery_example :
    Derives twoQuery 2 [(2, 1), (3, 0)] (Nat.pair 1 0) ∧
      Consistent ({2} : Set ℕ) [(2, 1), (3, 0)] ∧
      eval ({2} : Set ℕ) twoQuery 2 = Part.some (Nat.pair 1 0) ∧
      eval ({0, 2, 5} : Set ℕ) twoQuery 2 = Part.some (Nat.pair 1 0) ∧
      querySet [(2, 1), (3, 0)] = {2, 3} ∧ useBound [(2, 1), (3, 0)] = 4 := by
  have h := twoQuery_trace ({2} : Set ℕ) 2
  norm_num [indicator] at h
  refine ⟨h.1,h.2,?_,?_,?_,?_⟩
  · simp [twoQuery_eval,indicator]
  · simp [twoQuery_eval,indicator]
  · simp [querySet]
  · norm_num [useBound,querySet,Finset.sup_insert,Finset.sup_singleton]

theorem negative_answers_needed :
    ({2} : Set ℕ) ∩ (↑(querySet [(2, 1), (3, 0)]) : Set ℕ) ⊆ {2, 3} ∧
      eval ({2} : Set ℕ) twoQuery 2 = Part.some (Nat.pair 1 0) ∧
      eval ({2, 3} : Set ℕ) twoQuery 2 = Part.some (Nat.pair 1 1) ∧
      Nat.pair 1 0 ≠ Nat.pair 1 1 := by
  refine ⟨?_,?_,?_,by decide⟩
  · simp [querySet,Set.subset_def]
  · simp [twoQuery_eval,indicator]
  · simp [twoQuery_eval,indicator]

theorem unasked_position_change :
    0 ∉ querySet [(2, 1), (3, 0)] ∧
      eval ({0, 2} : Set ℕ) twoQuery 2 = Part.some (Nat.pair 1 0) ∧
      ¬ (∀ q < 4, indicator (fun n => n ∈ ({0, 2} : Set ℕ)) q =
        indicator (fun n => n ∈ ({2} : Set ℕ)) q) := by
  refine ⟨by simp [querySet],by simp [twoQuery_eval,indicator],?_⟩
  intro h
  have := h 0 (by decide)
  simp [indicator] at this

theorem no_common_query_bound (u : ℕ) :
    (∀ q < u, indicator (fun n => n ∈ (∅ : Set ℕ)) q =
      indicator (fun n => n ∈ ({u} : Set ℕ)) q) ∧
      eval (∅ : Set ℕ) .query u ≠ eval ({u} : Set ℕ) .query u := by
  constructor
  · intro q hq
    have hne : q ≠ u := by omega
    simp [indicator,hne]
  · simp [eval,indicator]

def firstMissing : Code := .find' (.comp .query .right)

def positivePrefix (u : ℕ) : QueryRecord := (List.range u).map (fun q => (q, 1))

theorem firstMissing_full :
    eval (Set.univ : Set ℕ) firstMissing (Nat.pair 0 0) = Part.none := by
  apply Part.eq_none_iff.mpr
  intro y hy
  have hz := ((eval_find Set.univ (.comp .query .right) 0 0 y).mp hy).2.1
  simp [eval,indicator] at hz

theorem firstMissing_truncated (u : ℕ) :
    eval {q : ℕ | q < u} firstMissing (Nat.pair 0 0) = Part.some u := by
  apply Part.eq_some_iff.mpr
  apply (eval_find _ (.comp .query .right) 0 0 u).mpr
  refine ⟨by omega,by simp [eval,indicator],?_⟩
  intro i _ hi
  exact ⟨1,by simp [eval,indicator,hi],by decide⟩

theorem incomplete_prefixes (u : ℕ) :
    (∀ j < u, Derives (.comp .query .right) (Nat.pair 0 j) [(j, 1)] 1) ∧
      Consistent (Set.univ : Set ℕ) (positivePrefix u) ∧
      ¬ ∃ τ y, Derives firstMissing (Nat.pair 0 0) τ y ∧ Consistent (Set.univ : Set ℕ) τ := by
  refine ⟨?_,?_,?_⟩
  · intro j _
    have hr : Derives .right (Nat.pair 0 j) [] j := by simpa using Derives.right (Nat.pair 0 j)
    exact .comp hr (.query j 1 (Or.inr rfl))
  · intro q b hb
    simp only [positivePrefix,List.mem_map,List.mem_range,Prod.mk.injEq] at hb
    obtain ⟨j,_,rfl,rfl⟩ := hb
    simp [indicator]
  · rintro ⟨τ,y,hy,hA⟩
    have hm := trace_sound hy hA
    rw [firstMissing_full] at hm
    simp at hm

theorem divergence_not_finitely_stable (u : ℕ) :
    (∀ q < u, indicator (fun n : ℕ => n < u) q =
      indicator (fun n => n ∈ (Set.univ : Set ℕ)) q) ∧
      eval {q : ℕ | q < u} firstMissing (Nat.pair 0 0) = Part.some u ∧
      eval (Set.univ : Set ℕ) firstMissing (Nat.pair 0 0) = Part.none := by
  exact ⟨fun q hq => by simp [indicator,hq],firstMissing_truncated u,firstMissing_full⟩

def never : Code := .find' (.comp .succ .zero)

theorem partial_replacement_fails (A B : Set ℕ) (x : ℕ) :
    (∀ q, eval B never q = Part.none) ∧
      eval B (subst never .query) x = Part.none ∧ (eval A .query x).Dom := by
  have hnone : ∀ q, eval B never q = Part.none := by
    intro q
    obtain ⟨⟨a,m⟩,rfl⟩ := Nat.pairEquiv.surjective q
    apply Part.eq_none_iff.mpr
    intro y hy
    have hz := ((eval_find B (.comp .succ .zero) a m y).mp hy).2.1
    simp [eval] at hz
  exact ⟨hnone,hnone x,by trivial⟩

theorem empty_records_and_bound (x : ℕ) :
    querySet [] = ∅ ∧ useBound [] = 0 ∧
      querySet [(x, 0)] = {x} ∧ useBound [(x, 0)] = x + 1 := by
  simp [querySet,useBound]

theorem empty_oracle_queries (x : ℕ) :
    eval (∅ : Set ℕ) .zero x = Part.some 0 ∧
      eval (∅ : Set ℕ) .query x = Part.some 0 ∧
      Derives .zero x [] 0 ∧ Derives .query x [(x, 0)] 0 ∧
      Consistent (∅ : Set ℕ) [(x, 0)] := by
  exact ⟨rfl,by simp [eval,indicator],.zero x,.query x 0 (Or.inl rfl),by simp [Consistent,indicator]⟩

theorem query_zero_iff (A : Set ℕ) (x : ℕ) :
    eval A .query x = Part.some 0 ↔ x ∉ A := by
  classical
  by_cases hx : x ∈ A <;> simp [eval,indicator,hx]

theorem erase_empty (c : Code) (x : ℕ) :
    Nat.Partrec.Code.eval (erase .zero c) x = eval (∅ : Set ℕ) c x := by
  apply erase_eval
  intro q
  change Part.some 0 = _
  simp [indicator]

end Lemmatheca.Entry.OracleComputation
