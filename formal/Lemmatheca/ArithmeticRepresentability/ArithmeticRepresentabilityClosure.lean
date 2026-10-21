import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentabilityBeta

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory

/-! Strong numeralwise Q representation is closed under terms, composition,
and minimization of a total function with a zero at every parameter tuple. -/
namespace Lemmatheca.ProofTheory.ArithmeticRepresentability
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.ArithmeticTheories
noncomputable section
universe u

theorem realize_graphAt {n : ℕ} {α : Type*} {M : Type u} [language.Structure M]
    (φ : language.Formula (Fin n ⊕ Unit)) (xs : Fin n → language.Term α)
    (y : language.Term α) (v : α → M) :
    (graphAt φ xs y).Realize v ↔
      φ.Realize (extend (fun i => (xs i).realize v) (y.realize v)) := by
  simp only [graphAt, Formula.Realize, BoundedFormula.realize_subst]
  have heq : (fun a => (Sum.elim xs (fun _ => y) a).realize v) =
      extend (fun i => (xs i).realize v) (y.realize v) := by
    funext i
    cases i <;> rfl
  rw [heq]

theorem realize_strictAll {α : Type*} {M : Type u} [language.Structure M]
    (v : α → M) (t : language.Term α) (φ : language.Formula (α ⊕ Unit)) :
    (strictAll t φ).Realize v ↔
      ∀ a : M, leValue M (succValue M a) (t.realize v) → φ.Realize (extend v a) := by
  simp only [strictAll, Formula.realize_iAlls, Formula.realize_imp, ltFormula,
    realize_leFormula, realize_succTerm, Term.realize_var, Term.realize_relabel,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h a ha
    exact h (fun _ => a) ha
  · intro h a ha
    have heq : Sum.elim v a = extend v (a ()) := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => cases i; rfl
    rw [heq]
    exact h (a ()) ha

/-- A term represents its value by equality with the distinguished output. -/
def termGraph {n : ℕ} (t : language.Term (Fin n)) :
    language.Formula (Fin n ⊕ Unit) :=
  (Term.var (.inr ())).equal (t.relabel Sum.inl)

theorem term_stronglyRepresents {n : ℕ} (t : language.Term (Fin n)) :
    StronglyRepresents (fun x => t.realize x) (termGraph t) := by
  apply stronglyRepresents_of_modelwise
  intro M x y
  simp only [termGraph, Formula.realize_equal, Term.realize_var, Term.realize_relabel,
    Function.comp_def, extend, Sum.elim_inl, Sum.elim_inr]
  rw [term_numeral_value]

/-- Witness the intermediate values and apply the outer graph to that tuple. -/
def compositionGraph {m n : ℕ}
    (φ : language.Formula (Fin m ⊕ Unit))
    (ψ : Fin m → language.Formula (Fin n ⊕ Unit)) :
    language.Formula (Fin n ⊕ Unit) :=
  ((Formula.iInf (fun i => graphAt (ψ i)
      (fun j => .var (.inl (.inl j))) (.var (.inr i)))) ⊓
    graphAt φ (fun i => .var (.inr i)) (.var (.inl (.inr ())))).iExs (Fin m)

theorem realize_compositionGraph {m n : ℕ} {M : Type u} [language.Structure M]
    (φ : language.Formula (Fin m ⊕ Unit))
    (ψ : Fin m → language.Formula (Fin n ⊕ Unit)) (x : Fin n → M) (y : M) :
    (compositionGraph φ ψ).Realize (extend x y) ↔
      ∃ a : Fin m → M, (∀ i, (ψ i).Realize (extend x (a i))) ∧
        φ.Realize (extend a y) := by
  simp only [compositionGraph, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iInf, realize_graphAt, Term.realize_var, extend,
    Sum.elim_inl, Sum.elim_inr]

theorem composition_stronglyRepresents {m n : ℕ}
    (f : (Fin m → ℕ) → ℕ) (g : Fin m → (Fin n → ℕ) → ℕ)
    (φ : language.Formula (Fin m ⊕ Unit))
    (ψ : Fin m → language.Formula (Fin n ⊕ Unit))
    (hf : StronglyRepresents f φ) (hg : ∀ i, StronglyRepresents (g i) (ψ i)) :
    StronglyRepresents (fun x => f (fun i => g i x)) (compositionGraph φ ψ) := by
  apply stronglyRepresents_of_modelwise
  intro M x y
  rw [realize_compositionGraph]
  constructor
  · rintro ⟨a, ha, hφ⟩
    have heq : a = fun i => numeralValue M (g i x) := by
      funext i
      exact (stronglyRepresents_modelwise (hg i) x (a i)).mp (ha i)
    subst a
    exact (stronglyRepresents_modelwise hf (fun i => g i x) y).mp hφ
  · intro hy
    refine ⟨fun i => numeralValue M (g i x), ?_, ?_⟩
    · intro i
      exact (stronglyRepresents_modelwise (hg i) x _).mpr rfl
    · exact (stronglyRepresents_modelwise hf (fun i => g i x) y).mpr hy

/-- Search is used here only when a zero exists for every parameter tuple. -/
def regularSearch {n : ℕ} (f : (Fin (n + 1) → ℕ) → ℕ)
    (hdom : ∀ x : Fin n → ℕ, ∃ k, f (Fin.snoc x k) = 0) (x : Fin n → ℕ) : ℕ :=
  Nat.find (hdom x)

/-- The candidate is a zero and every smaller candidate fails the zero test. -/
def graphSearch {n : ℕ} (φ : language.Formula (Fin (n + 1) ⊕ Unit)) :
    language.Formula (Fin n ⊕ Unit) :=
  graphAt φ (Fin.snoc (fun i => .var (.inl i)) (.var (.inr ()))) zeroTerm ⊓
    strictAll (.var (.inr ()))
      (graphAt φ (Fin.snoc (fun i => .var (.inl (.inl i))) (.var (.inr ())))
        zeroTerm).not

theorem realize_snoc {n : ℕ} {α : Type*} {M : Type u} [language.Structure M]
    (ts : Fin n → language.Term α) (t : language.Term α) (v : α → M) :
    (fun i : Fin (n + 1) => ((Fin.snoc ts t : Fin (n + 1) → language.Term α) i).realize v) =
      Fin.snoc (fun i => (ts i).realize v) (t.realize v) :=
  Fin.comp_snoc (fun t : language.Term α => t.realize v) ts t

theorem numeral_snoc {n : ℕ} {M : Type u} [language.Structure M]
    (x : Fin n → ℕ) (a : ℕ) :
    (Fin.snoc (fun i => numeralValue M (x i)) (numeralValue M a) : Fin (n + 1) → M) =
      fun i => numeralValue M ((Fin.snoc x a : Fin (n + 1) → ℕ) i) :=
  (Fin.comp_snoc (numeralValue M) x a).symm

theorem realize_graphSearch {n : ℕ} {M : Type u} [language.Structure M]
    (φ : language.Formula (Fin (n + 1) ⊕ Unit)) (x : Fin n → M) (y : M) :
    (graphSearch φ).Realize (extend x y) ↔
      φ.Realize (extend (Fin.snoc x y) (zeroValue M)) ∧
        ∀ a : M, leValue M (succValue M a) y →
          ¬ φ.Realize (extend (Fin.snoc x a) (zeroValue M)) := by
  simp only [graphSearch, Formula.realize_inf, realize_graphAt, realize_strictAll,
    Formula.realize_not, realize_snoc, Term.realize_var, realize_zeroTerm,
    extend, Sum.elim_inl, Sum.elim_inr]

theorem regularSearch_stronglyRepresents {n : ℕ}
    (f : (Fin (n + 1) → ℕ) → ℕ)
    (hdom : ∀ x : Fin n → ℕ, ∃ k, f (Fin.snoc x k) = 0)
    (φ : language.Formula (Fin (n + 1) ⊕ Unit)) (hf : StronglyRepresents f φ) :
    StronglyRepresents (regularSearch f hdom) (graphSearch φ) := by
  apply stronglyRepresents_of_modelwise
  intro M x y
  rw [realize_graphSearch]
  let k := regularSearch f hdom x
  have hk : f (Fin.snoc x k) = 0 := Nat.find_spec (hdom x)
  have hsmall : ∀ j < k, f (Fin.snoc x j) ≠ 0 := fun j hj =>
    Nat.find_min (hdom x) hj
  have hzero (j : ℕ) :
      φ.Realize (extend (Fin.snoc (fun i => numeralValue M (x i)) (numeralValue M j))
        (zeroValue M)) ↔ f (Fin.snoc x j) = 0 := by
    rw [numeral_snoc]
    have h := stronglyRepresents_modelwise hf (Fin.snoc x j) (zeroValue M)
    refine h.trans ?_
    rw [← numeral_value_zero M, (numeral_injective M).eq_iff]
    exact eq_comm
  constructor
  · rintro ⟨hy, hbefore⟩
    have hbound : ∃ j ≤ k, y = numeralValue M j := by
      rcases numeral_cut y k with h | h
      · exact h
      · exact False.elim (hbefore (numeralValue M k)
          (by simpa only [← numeral_value_succ] using h) ((hzero k).mpr hk))
    obtain ⟨j, hj, rfl⟩ := hbound
    have hjzero := (hzero j).mp hy
    have hkj : k ≤ j := Nat.find_min' (hdom x) hjzero
    exact congrArg (numeralValue M) (Nat.le_antisymm hj hkj)
  · intro hy
    change y = numeralValue M k at hy
    subst y
    refine ⟨(hzero k).mpr hk, ?_⟩
    intro a ha
    obtain ⟨j, hj, rfl⟩ := (strict_finite_bound a k).mp ha
    exact fun h => hsmall j hj ((hzero j).mp h)

end
end Lemmatheca.ProofTheory.ArithmeticRepresentability
