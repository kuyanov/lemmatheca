import Lemmatheca.FiniteDescriptionsAndDecisionProblems.Decisions
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite-arity primitive recursion, bounded tests, and bounded search.

The human class is Nat.Primrec'. Its existing prim_iff theorem connects every
finite arity to the encoded Primrec interface used for the closure lemmas.
The lastRec construction puts the recursion coordinate after the parameters.
-/

namespace Lemmatheca.ComputabilityTheory.PrimitiveRecursion

open List.Vector
open scoped BigOperators

abbrev Args (n : ℕ) := List.Vector ℕ n

def recValue {α : Type*} (g : α → ℕ) (h : α → ℕ → ℕ → ℕ)
    (x : α) (n : ℕ) : ℕ :=
  Nat.rec (g x) (fun i u => h x i u) n

def initialPart {n : ℕ} (v : Args (n + 1)) : Args n :=
  List.Vector.ofFn fun i => v.get i.castSucc

def lastRec {n : ℕ} (g : Args n → ℕ) (h : Args (n + 2) → ℕ)
    (v : Args (n + 1)) : ℕ :=
  recValue g (fun x i u => h (x ++ (i ::ᵥ u ::ᵥ nil)))
    (initialPart v) (v.get (Fin.last n))

theorem recValue_unique {α : Type*} (g : α → ℕ) (h : α → ℕ → ℕ → ℕ) :
    ∃! F : α → ℕ → ℕ,
      (∀ x, F x 0 = g x) ∧ (∀ x n, F x (n + 1) = h x n (F x n)) := by
  refine ⟨recValue g h, ⟨fun _ => rfl, fun _ _ => rfl⟩, ?_⟩
  rintro F ⟨hz, hs⟩
  funext x n
  induction n with
  | zero => exact hz x
  | succ n ih => simpa [recValue, ih] using hs x n

private theorem prefix_snoc {n : ℕ} (x : Args n) (a : ℕ) :
    initialPart (x ++ a ::ᵥ nil) = x := by
  apply List.Vector.ext
  intro i
  change (List.Vector.ofFn (fun j : Fin n => (x ++ a ::ᵥ nil).get j.castSucc)).get i = _
  rw [List.Vector.get_ofFn]
  change (x.toList ++ [a])[i.val]'_ = x.toList[i.val]'_
  exact List.getElem_append_left (by simp)

private theorem last_snoc {n : ℕ} (x : Args n) (a : ℕ) :
    (x ++ a ::ᵥ nil).get (Fin.last n) = a := by
  rcases x with ⟨l, rfl⟩
  change (l ++ [a])[l.length]'_ = a
  simp


theorem lastRec_equations {n : ℕ} (g : Args n → ℕ) (h : Args (n + 2) → ℕ)
    (x : Args n) (i : ℕ) :
    lastRec g h (x ++ (0 ::ᵥ nil)) = g x ∧
      lastRec g h (x ++ ((i + 1) ::ᵥ nil)) =
        h (x ++ (i ::ᵥ lastRec g h (x ++ (i ::ᵥ nil)) ::ᵥ nil)) := by
  simp [lastRec, prefix_snoc, last_snoc, recValue]

theorem recValue_primrec {α : Type*} [Primcodable α]
    {g : α → ℕ} {h : α → ℕ → ℕ → ℕ}
    (hg : Primrec g) (hh : Primrec₂ fun x (p : ℕ × ℕ) => h x p.1 p.2) :
    Primrec₂ (recValue g h) := by
  exact (Primrec.nat_rec hg hh).of_eq fun _ _ => rfl

theorem lastRec_primrec {n : ℕ} {g : Args n → ℕ} {h : Args (n + 2) → ℕ}
    (hg : Nat.Primrec' g) (hh : Nat.Primrec' h) : Nat.Primrec' (lastRec g h) := by
  apply Nat.Primrec'.prim_iff.mpr
  have hg' := Nat.Primrec'.prim_iff.mp hg
  have hh' := Nat.Primrec'.prim_iff.mp hh
  have hbuild : Primrec (fun p : Args n × (ℕ × ℕ) => p.1 ++ p.2.1 ::ᵥ p.2.2 ::ᵥ nil) := by
    apply Primrec.vector_toList_iff.mp
    simpa only [List.Vector.toList_append, List.Vector.toList_cons, List.Vector.toList_nil] using
      Primrec.list_append.comp (Primrec.vector_toList.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])))
  have hstep : Primrec₂ (fun x (p : ℕ × ℕ) => h (x ++ p.1 ::ᵥ p.2 ::ᵥ nil)) :=
    hh'.comp hbuild
  have hp : Primrec (@initialPart n) :=
    Primrec.vector_ofFn fun i => Primrec.vector_get.comp Primrec.id (Primrec.const i.castSucc)
  have hl : Primrec (fun v : Args (n + 1) => v.get (Fin.last n)) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const (Fin.last n))
  exact (recValue_primrec hg' hstep).comp hp hl

theorem pow_primrec : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := by
  exact Primrec₂.unpaired'.mp Nat.Primrec.pow

theorem factorial_primrec : Primrec Nat.factorial := by
  have h : Primrec (Nat.rec 1 (fun n u => (n + 1) * u)) :=
    Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp₂ (Primrec.succ.comp₂ Primrec₂.left) Primrec₂.right)
  exact h.of_eq fun n => by induction n <;> simp_all [Nat.factorial_succ]

def distance (x y : ℕ) : ℕ := (x - y) + (y - x)

theorem distance_primrec : Primrec₂ distance := by
  exact Primrec.nat_add.comp₂ Primrec.nat_sub Primrec.nat_sub.swap

theorem distance_zero_iff (x y : ℕ) : distance x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hh := Nat.add_eq_zero_iff.mp h
    have hxy := Nat.sub_eq_zero_iff_le.mp hh.1
    have hyx := Nat.sub_eq_zero_iff_le.mp hh.2
    exact le_antisymm hxy hyx
  · rintro rfl
    simp [distance]

def boundedSum {α : Type*} (f : α → ℕ → ℕ) (x : α) (b : ℕ) : ℕ :=
  ∑ i ∈ Finset.range b, f x i

def boundedProduct {α : Type*} (f : α → ℕ → ℕ) (x : α) (b : ℕ) : ℕ :=
  ∏ i ∈ Finset.range b, f x i

theorem boundedSum_primrec {α : Type*} [Primcodable α] {f : α → ℕ → ℕ}
    (hf : Primrec₂ f) : Primrec₂ (boundedSum f) := by
  have h : Primrec₂ (recValue (fun _ : α => 0) (fun x i u => u + f x i)) :=
    recValue_primrec (Primrec.const 0)
      (Primrec.nat_add.comp₂ (Primrec.snd.comp₂ Primrec₂.right)
        (hf.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right)))
  apply h.of_eq
  intro x b
  induction b with
  | zero => simp [recValue, boundedSum]
  | succ b ih =>
    simpa only [recValue, boundedSum, Finset.sum_range_succ] using congrArg (fun u => u + f x b) ih

theorem boundedProduct_primrec {α : Type*} [Primcodable α] {f : α → ℕ → ℕ}
    (hf : Primrec₂ f) : Primrec₂ (boundedProduct f) := by
  have h : Primrec₂ (recValue (fun _ : α => 1) (fun x i u => u * f x i)) :=
    recValue_primrec (Primrec.const 1)
      (Primrec.nat_mul.comp₂ (Primrec.snd.comp₂ Primrec₂.right)
        (hf.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right)))
  apply h.of_eq
  intro x b
  induction b with
  | zero => simp [recValue, boundedProduct]
  | succ b ih =>
    simpa only [recValue, boundedProduct, Finset.prod_range_succ] using congrArg (fun u => u * f x b) ih

theorem boundedSum_equations {α : Type*} (f : α → ℕ → ℕ) (x : α) (b : ℕ) :
    boundedSum f x 0 = 0 ∧ boundedSum f x (b + 1) = boundedSum f x b + f x b := by
  simp [boundedSum, Finset.sum_range_succ]

theorem boundedProduct_equations {α : Type*} (f : α → ℕ → ℕ) (x : α) (b : ℕ) :
    boundedProduct f x 0 = 1 ∧
      boundedProduct f x (b + 1) = boundedProduct f x b * f x b := by
  simp [boundedProduct, Finset.prod_range_succ]

def PRRelation {α : Type*} [Primcodable α] (R : α → Prop) : Prop :=
  Primrec (characteristic R)

theorem PRRelation_iff {α : Type*} [Primcodable α] (R : α → Prop) :
    PRRelation R ↔ PrimrecPred R := by
  classical
  constructor
  · intro h
    have he := (Primrec.eq.comp h (Primrec.const 1))
    exact he.of_eq fun x => (characteristic_spec R x).1
  · intro h
    exact Primrec.ite h (Primrec.const 1) (Primrec.const 0)

def zeroTest (n : ℕ) : ℕ := if n = 0 then 1 else 0

theorem zeroTest_primrec : Primrec zeroTest := by
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const 1) (Primrec.const 0)

theorem zeroTest_equations (n : ℕ) :
    zeroTest 0 = 1 ∧ zeroTest (n + 1) = 0 := by
  simp [zeroTest]

theorem boolean_formulas (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) :
    (1 - a = 1 ↔ a = 0) ∧
      (a * b = 1 ↔ a = 1 ∧ b = 1) ∧
      (1 - (1 - a) * (1 - b) = 1 ↔ a = 1 ∨ b = 1) := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> norm_num

theorem implication_primrec {α : Type*} [Primcodable α] {R S : α → Prop}
    (hR : PrimrecPred R) (hS : PrimrecPred S) :
    PrimrecPred fun x => R x → S x := by
  classical
  exact (hR.not.or hS).of_eq fun _ => by simpa using (or_iff_not_imp_left : (¬ _ ∨ _) ↔ (¬¬ _ → _))

theorem graph_primrec {α : Type*} [Primcodable α] {f : α → ℕ}
    (hf : Primrec f) : PrimrecRel fun x y => f x = y := by
  exact Primrec.eq.comp (hf.comp Primrec.fst) Primrec.snd

theorem characteristic_cases {α : Type*} (R : α → Prop) (f g : α → ℕ) (x : α) :
    characteristic R x * f x + (1 - characteristic R x) * g x =
      (by classical exact if R x then f x else g x) := by
  classical
  by_cases h : R x <;> simp [characteristic, h]

theorem bounded_forall_primrec {α : Type*} [Primcodable α]
    {R : α → ℕ → Prop} (hR : PrimrecRel R) :
    PrimrecRel fun x b => ∀ i < b, R x i := by
  classical
  have h := hR.swap.forall_mem_list
  exact (h.comp (Primrec.list_range.comp Primrec.snd) Primrec.fst).of_eq
    fun p => by simp [Function.swap]

theorem bounded_exists_primrec {α : Type*} [Primcodable α]
    {R : α → ℕ → Prop} (hR : PrimrecRel R) :
    PrimrecRel fun x b => ∃ i < b, R x i := by
  classical
  have h := hR.swap.exists_mem_list
  exact (h.comp (Primrec.list_range.comp Primrec.snd) Primrec.fst).of_eq
    fun p => by simp [Function.swap]

theorem bounded_quantifier_characteristics {α : Type*} (R : α → ℕ → Prop)
    (x : α) (b : ℕ) :
    characteristic (fun x => ∀ i < b, R x i) x =
        boundedProduct (fun x i => characteristic (R x) i) x b ∧
      characteristic (fun x => ∃ i < b, R x i) x =
        1 - zeroTest (boundedSum (fun x i => characteristic (R x) i) x b) := by
  classical
  have hall : boundedProduct (fun x i => characteristic (R x) i) x b = 1 ↔ ∀ i < b, R x i := by
    simp [boundedProduct, Finset.prod_eq_one_iff, characteristic]
  have hzero : boundedSum (fun x i => characteristic (R x) i) x b = 0 ↔ ∀ i < b, ¬ R x i := by
    simp [boundedSum, characteristic]
  have hb : boundedProduct (fun x i => characteristic (R x) i) x b ≤ 1 := by
    clear hall hzero
    induction b with
    | zero => simp [boundedProduct]
    | succ b ih =>
      rw [(boundedProduct_equations _ x b).2]
      by_cases hr : R x b
      · simpa [characteristic, hr] using ih
      · simp [characteristic, hr]
  constructor
  · by_cases h : ∀ i < b, R x i
    · rw [(characteristic_spec (fun x => ∀ i < b, R x i) x).1.mpr h, hall.mpr h]
    · rw [(characteristic_spec (fun x => ∀ i < b, R x i) x).2.mpr h]
      have hn : boundedProduct (fun x i => characteristic (R x) i) x b ≠ 1 := mt hall.mp h
      omega
  · by_cases h : ∃ i < b, R x i
    · have hz : boundedSum (fun x i => characteristic (R x) i) x b ≠ 0 := by
        intro hz
        obtain ⟨i, hi, hr⟩ := h
        exact hzero.mp hz i hi hr
      rw [(characteristic_spec (fun x => ∃ i < b, R x i) x).1.mpr h]
      simp [zeroTest, hz]
    · have hz : boundedSum (fun x i => characteristic (R x) i) x b = 0 :=
        hzero.mpr (fun i hi hr => h ⟨i, hi, hr⟩)
      rw [(characteristic_spec (fun x => ∃ i < b, R x i) x).2.mpr h]
      simp [zeroTest, hz]

noncomputable def boundedSearch {α : Type*} (R : α → ℕ → Prop)
    (x : α) (b : ℕ) : ℕ := by
  classical
  exact Nat.rec 0 (fun n u => if u < n then u else if R x n then n else n + 1) b

theorem boundedSearch_primrec {α : Type*} [Primcodable α]
    {R : α → ℕ → Prop} (hR : PrimrecRel R) : Primrec₂ (boundedSearch R) := by
  classical
  have step : Primrec₂ fun x (p : ℕ × ℕ) =>
      if p.2 < p.1 then p.2 else if R x p.1 then p.1 else p.1 + 1 := by
    apply Primrec.ite
      (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
    exact Primrec.ite (hR.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd) (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
  exact (Primrec.nat_rec (Primrec.const 0) step).of_eq fun _ _ => rfl

theorem boundedSearch_spec {α : Type*} (R : α → ℕ → Prop) (x : α) (b : ℕ) :
    boundedSearch R x b ≤ b ∧
      (boundedSearch R x b < b →
        R x (boundedSearch R x b) ∧ ∀ i < boundedSearch R x b, ¬ R x i) ∧
      (boundedSearch R x b = b ↔ ∀ i < b, ¬ R x i) := by
  classical
  induction b with
  | zero => simp [boundedSearch]
  | succ b ih =>
    have heq : boundedSearch R x (b + 1) =
        if boundedSearch R x b < b then boundedSearch R x b
        else if R x b then b else b + 1 := rfl
    rw [heq]
    by_cases hfound : boundedSearch R x b < b
    · simp only [ite_eq_left hfound]
      have hm := ih.2.1 hfound
      refine ⟨by omega, fun _ => hm, ?_⟩
      constructor
      · intro he
        omega
      · intro hn
        exact False.elim (hn _ (by omega) hm.1)
    · have hu : boundedSearch R x b = b := by omega
      have hn := ih.2.2.mp hu
      simp only [ite_eq_right hfound]
      by_cases hr : R x b
      · simp only [ite_eq_left hr]
        refine ⟨by omega, fun _ => ⟨hr, hn⟩, ?_⟩
        constructor
        · intro he
          omega
        · intro hnone
          exact False.elim (hnone b (by omega) hr)
      · simp only [ite_eq_right hr]
        refine ⟨le_rfl, fun hlt => False.elim (Nat.lt_irrefl _ hlt), ?_⟩
        refine ⟨fun _ i hi => ?_, fun _ => True.intro⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hn i hi
        · exact hr

theorem boundedSearch_eq_iff {α : Type*} (R : α → ℕ → Prop)
    (x : α) (b i : ℕ) (hi : i < b) :
    boundedSearch R x b = i ↔ R x i ∧ ∀ j < i, ¬ R x j := by
  have hs := boundedSearch_spec R x b
  constructor
  · intro heq
    exact heq ▸ hs.2.1 (heq.symm ▸ hi)
  · rintro ⟨hr, hmin⟩
    have hlt : boundedSearch R x b < b := by
      by_contra h
      have heq : boundedSearch R x b = b := by omega
      exact hs.2.2.mp heq i hi hr
    have hm := hs.2.1 hlt
    apply le_antisymm
    · by_contra h
      exact hm.2 i (by omega) hr
    · by_contra h
      exact hmin _ (by omega) hm.1

noncomputable def quotient (x d : ℕ) : ℕ :=
  if d = 0 then 0 else boundedSearch (fun p j => p.1 < (j + 1) * p.2) (x, d) (x + 1)

noncomputable def remainder (x d : ℕ) : ℕ := x - d * quotient x d

theorem quotient_primrec : Primrec₂ quotient := by
  classical
  have ht : PrimrecRel (fun p : ℕ × ℕ => fun j : ℕ => p.1 < (j + 1) * p.2) :=
    Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
  have hs := (boundedSearch_primrec ht).comp Primrec.id (Primrec.succ.comp (Primrec.fst))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0) hs

theorem remainder_primrec : Primrec₂ remainder := by
  exact Primrec.nat_sub.comp₂ Primrec₂.left
    (Primrec.nat_mul.comp₂ Primrec₂.right quotient_primrec)

theorem quotient_eq_div (x d : ℕ) : quotient x d = x / d := by
  classical
  by_cases hd : d = 0
  · simp [quotient, hd]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let R : (ℕ × ℕ) → ℕ → Prop := fun p j => p.1 < (j + 1) * p.2
    let q := boundedSearch R (x, d) (x + 1)
    have hs := boundedSearch_spec R (x, d) (x + 1)
    have hw : R (x, d) x := by dsimp [R]; nlinarith
    have hqb : q < x + 1 := by
      by_contra hn
      have he : q = x + 1 := by dsimp [q]; omega
      exact hs.2.2.mp he x (by omega) hw
    have hm := hs.2.1 hqb
    have hhi : x < (q + 1) * d := hm.1
    have hlo : q * d ≤ x := by
      by_cases hq : q = 0
      · simp [hq]
      · have hp := hm.2 (q - 1) (by omega)
        have htest : ¬ x < q * d := by
          simpa only [R, Nat.sub_add_cancel (by omega : 1 ≤ q)] using hp
        omega
    simpa only [quotient, ite_eq_right hd, R, q] using (Nat.div_eq_of_lt_le hlo hhi).symm

theorem remainder_eq_mod (x d : ℕ) : remainder x d = x % d := by
  rw [remainder, quotient_eq_div, Nat.mod_eq_sub_mul_div]

theorem division_spec (x d : ℕ) (hd : 0 < d) :
    x = d * quotient x d + remainder x d ∧ remainder x d < d := by
  rw [quotient_eq_div, remainder_eq_mod]
  exact ⟨(Nat.div_add_mod x d).symm, Nat.mod_lt x hd⟩

theorem division_unique (x d q r : ℕ) (hd : 0 < d)
    (heq : x = d * q + r) (hr : r < d) :
    q = quotient x d ∧ r = remainder x d := by
  have h := (Nat.div_mod_unique hd).mpr
    (show r + d * q = x ∧ r < d from ⟨by omega, hr⟩)
  rw [quotient_eq_div, remainder_eq_mod]
  exact ⟨h.1.symm, h.2.symm⟩

theorem division_zero (x : ℕ) : quotient x 0 = 0 ∧ remainder x 0 = x := by
  simp [quotient, remainder]

noncomputable def squareRootSearch (x : ℕ) : ℕ :=
  boundedSearch (fun x i => i * i = x) x (x + 1)

theorem squareRootSearch_primrec : Primrec squareRootSearch := by
  have ht : PrimrecRel (fun x i : ℕ => i * i = x) :=
    Primrec.eq.comp (Primrec.nat_mul.comp Primrec.snd Primrec.snd) Primrec.fst
  exact (boundedSearch_primrec ht).comp Primrec.id Primrec.succ

theorem square_test_primrec : PrimrecPred fun x : ℕ => ∃ i, i * i = x := by
  have ht : PrimrecRel (fun x i : ℕ => i * i = x) :=
    Primrec.eq.comp (Primrec.nat_mul.comp Primrec.snd Primrec.snd) Primrec.fst
  exact ((bounded_exists_primrec ht).comp Primrec.id Primrec.succ).of_eq fun x => by
    constructor
    · rintro ⟨i, _, hi⟩
      exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_, hi⟩
      by_cases hz : i = 0
      · omega
      · have hp : 1 ≤ i := by omega
        nlinarith

theorem squareRootSearch_spec (x : ℕ) :
    (squareRootSearch x ≤ x ↔ ∃ i, i * i = x) ∧
      (∀ i, i * i = x → squareRootSearch x = i) ∧
      (squareRootSearch x = x + 1 ↔ ¬ ∃ i, i * i = x) := by
  have hs := boundedSearch_spec (fun x i : ℕ => i * i = x) x (x + 1)
  have hbound : ∀ i, i * i = x → i < x + 1 := by
    intro i hi
    by_cases hz : i = 0
    · omega
    · have hp : 1 ≤ i := by omega
      nlinarith
  have hroot : ∀ i, i * i = x → squareRootSearch x = i := by
    intro i hi
    apply (boundedSearch_eq_iff _ x (x + 1) i (hbound i hi)).mpr
    refine ⟨hi, ?_⟩
    intro j hj hjeq
    have heq : j = i := Nat.mul_self_inj.mp (hjeq.trans hi.symm)
    omega
  refine ⟨?_, hroot, ?_⟩
  · constructor
    · intro h
      exact ⟨_, (hs.2.1 (by change squareRootSearch x < x + 1; omega)).1⟩
    · rintro ⟨i, hi⟩
      rw [hroot i hi]
      exact Nat.lt_succ_iff.mp (hbound i hi)
  · constructor
    · intro he ⟨i, hi⟩
      have h := hroot i hi
      have hb := hbound i hi
      omega
    · intro hn
      exact hs.2.2.mpr (fun i _ hi => hn ⟨i, hi⟩)

theorem squareRootSearch_zero : squareRootSearch 0 = 0 := by
  simp [squareRootSearch, boundedSearch]

theorem empty_bound_search {α : Type*} (R : α → ℕ → Prop) (x : α)
    (hR : R x 0) : boundedSearch R x 0 = 0 ∧ boundedSearch R x 1 = 0 := by
  classical
  simp [boundedSearch, hR]

end Lemmatheca.ComputabilityTheory.PrimitiveRecursion
