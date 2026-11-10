import Lemmatheca.BoundedChangesAndStrongReductions.Thresholds
import Lemmatheca.TruthTableAndWeakTruthTableReductions.Programs

/-! The specified threshold-query prefix table, including the zero-width case. -/
namespace Lemmatheca.ComputabilityTheory.BoundedChangesStrongReductions

open UniversalComputation LimitComputability DifferenceEnumerable ComputablyBoundedChanges
open StrongReductions PostsTheorem

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem range_sum_computable {α : Type*} [Primcodable α]
    (b : α → ℕ) (hb : Computable b) (f : α → ℕ → ℕ) (hf : Computable₂ f) :
    Computable (fun x => (Finset.range (b x)).sum (f x)) := by
  have hs : Computable₂ (fun x (p : ℕ × ℕ) => p.2 + f x p.1) :=
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))).to₂
  apply (Computable.nat_rec hb (Computable.const 0) hs).of_eq
  intro x
  have he (n : ℕ) : Nat.rec 0 (fun j v => v + f x j) n =
      (Finset.range n).sum (f x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      change Nat.rec 0 (fun j v => v + f x j) n + f x n = _
      rw [Finset.sum_range_succ, ih]
  exact he (b x)

private theorem range_max_computable {α : Type*} [Primcodable α]
    (b : α → ℕ) (hb : Computable b) (f : α → ℕ → ℕ) (hf : Computable₂ f) :
    Computable (fun x => (Finset.range (b x)).sup (f x)) := by
  have hs : Computable₂ (fun x (p : ℕ × ℕ) => max p.2 (f x p.1)) :=
    (Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))).to₂
  apply (Computable.nat_rec hb (Computable.const 0) hs).of_eq
  intro x
  have he (n : ℕ) : Nat.rec 0 (fun j v => max v (f x j)) n =
      (Finset.range n).sup (f x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      change max (Nat.rec 0 (fun j v => max v (f x j)) n) (f x n) = _
      simp only [Finset.range_add_one, Finset.sup_insert, ih]
      exact max_comm _ _
  exact he (b x)

def thresholdWidth (a : Approximation) (hc : Computable₂ a) (b : ℕ → ℕ) (x : ℕ) : ℕ :=
  (Finset.range (b x)).sup (fun k => thresholdQuery a hc x k + 1)

def thresholdTable (a : Approximation) (hc : Computable₂ a) (b : ℕ → ℕ) (x w : ℕ) : ℕ :=
  ((Finset.range (b x)).sum (fun k => beta w (thresholdQuery a hc x k))) % 2

def thresholdData (a : Approximation) (hc : Computable₂ a) (b : ℕ → ℕ) : TableData :=
  ⟨thresholdWidth a hc b, thresholdTable a hc b⟩

theorem threshold_scheme (a : Approximation) (hc : Computable₂ a) (b : ℕ → ℕ)
    (hb : Computable b) : IsScheme (thresholdData a hc b) := by
  have hq := (threshold_query_primitive a hc).to_comp
  have hw : Computable (thresholdWidth a hc b) :=
    range_max_computable b hb (fun x k => thresholdQuery a hc x k + 1)
      (Computable.succ.comp hq).to₂
  have hterm : Computable₂ (fun p : ℕ × ℕ => fun k =>
      beta p.2 (thresholdQuery a hc p.1 k)) :=
    (beta_primitive.to_comp.comp (Computable.snd.comp Computable.fst)
      (hq.comp (Computable.fst.comp Computable.fst) Computable.snd)).to₂
  have hsum := range_sum_computable (fun p : ℕ × ℕ => b p.1)
    (hb.comp Computable.fst) _ hterm
  have ht : Computable (fun p : ℕ × ℕ => thresholdTable a hc b p.1 p.2) :=
    Primrec.nat_mod.to_comp.comp hsum (Computable.const 2)
  exact ⟨hw, ht, fun _ _ => Nat.mod_two_eq_zero_or_one _⟩

theorem threshold_query_below_width (a : Approximation) (hc : Computable₂ a) (b : ℕ → ℕ)
    (x k : ℕ) (hk : k < b x) : thresholdQuery a hc x k < thresholdWidth a hc b x := by
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (Finset.le_sup (f :=
    fun k => thresholdQuery a hc x k + 1) (Finset.mem_range.mpr hk))

theorem threshold_presents (a : Approximation) (hc : Computable₂ a) (b : ℕ → ℕ)
    (A : Set ℕ) (hb : Binary a) (hz : StartsZero a) (hl : Converges a A)
    (hn : ComputableBound a b) : Presents (thresholdData a hc b) A haltingDiagonal := by
  refine ⟨threshold_scheme a hc b hn.1, fun x => ?_⟩
  change thresholdTable a hc b x (prefixCode haltingDiagonal (thresholdWidth a hc b x)) = indicator A x
  rw [final_parity a hc A b hb hz hl hn.2 x]
  apply congrArg (fun n : ℕ => n % 2)
  apply Finset.sum_congr rfl
  intro k hk
  exact (prefixCode_spec haltingDiagonal _).2 _
    (threshold_query_below_width a hc b x k (Finset.mem_range.mp hk))

theorem threshold_zero_width (a : Approximation) (hc : Computable₂ a) (b : ℕ → ℕ)
    (x : ℕ) (hb : b x = 0) :
    thresholdWidth a hc b x = 0 ∧ ∀ w, thresholdTable a hc b x w = 0 := by
  constructor
  · simp [thresholdWidth, hb]
  · intro w
    simp [thresholdTable, hb]

theorem omega_imp_tt (A : Set ℕ) (hA : OmegaCE A) :
    TruthTableReducible A haltingDiagonal := by
  obtain ⟨a, b, hc, hb, hl, hz, hn⟩ := hA
  exact ⟨thresholdData a hc b, threshold_presents a hc b A hb hz hl hn⟩

end
end Lemmatheca.ComputabilityTheory.BoundedChangesStrongReductions
