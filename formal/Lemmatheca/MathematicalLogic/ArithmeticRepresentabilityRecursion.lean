import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityClosure
import Lemmatheca.MathematicalLogic.PrimitiveRecursionConventions

/-! Representation of finite primitive recursion using a total finite-sequence
decoder. Universal compatibility clauses avoid assuming that a decoder is
functional on nonstandard codes in arbitrary models of Robinson arithmetic. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticRepresentability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories
noncomputable section

private theorem realize_term_vec3 {α : Type*} {M : Type*} [language.Structure M]
    (v : α → M) (a b c : language.Term α) :
    (fun i : Fin 3 => (![a, b, c] i).realize v) =
      ![a.realize v, b.realize v, c.realize v] := by
  funext i
  fin_cases i <;> rfl

private theorem realize_term_snoc {n : ℕ} {α : Type*} {M : Type*}
    [language.Structure M] (v : α → M) (ts : Fin n → language.Term α)
    (a : language.Term α) :
    (fun i : Fin (n + 1) => ((Fin.snoc ts a : Fin (n + 1) → language.Term α) i).realize v) =
      Fin.snoc (fun i => (ts i).realize v) (a.realize v) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

private theorem forall_unit_function {M : Type*} (P : (Unit → M) → Prop) :
    (∀ a, P a) ↔ ∀ a, P (fun _ => a) := by
  constructor
  · intro h a
    exact h (fun _ => a)
  · intro h a
    have he : (fun _ => a ()) = a := by funext u; cases u; rfl
    exact he ▸ h (a ())

private theorem exists_unit_function {M : Type*} (P : (Unit → M) → Prop) :
    (∃ a, P a) ↔ ∃ a, P (fun _ => a) := by
  constructor
  · rintro ⟨a, ha⟩
    have he : a = fun _ => a () := by funext u; cases u; rfl
    exact ⟨a (), he ▸ ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, ha⟩

private theorem numeral_vec3 {M : Type*} [language.Structure M] (a b c : ℕ) :
    (fun i : Fin 3 => numeralValue M (![a, b, c] i)) =
      ![numeralValue M a, numeralValue M b, numeralValue M c] := by
  funext i
  fin_cases i <;> rfl

def primitiveRec {n : ℕ} (f : (Fin n → ℕ) → ℕ) (g : (Fin (n + 2) → ℕ) → ℕ)
    (x : Fin n → ℕ) : ℕ → ℕ
  | 0 => f x
  | k + 1 => g (Fin.snoc (Fin.snoc x k) (primitiveRec f g x k))

def primitiveRecFunction {n : ℕ} (f : (Fin n → ℕ) → ℕ)
    (g : (Fin (n + 2) → ℕ) → ℕ) (x : Fin (n + 1) → ℕ) : ℕ :=
  primitiveRec f g (fun i => x i.castSucc) (x (Fin.last n))

/-- Values exist at all required places, and all decoded values obey the base
and transition clauses. These are distinct conditions for nonstandard codes. -/
def recursionGraph {n : ℕ}
    (decoder : language.Formula (Fin 3 ⊕ Unit))
    (base : language.Formula (Fin n ⊕ Unit))
    (step : language.Formula (Fin (n + 2) ⊕ Unit)) :
    language.Formula (Fin (n + 1) ⊕ Unit) :=
  let c : language.Term ((Fin (n + 1) ⊕ Unit) ⊕ Fin 2) := .var (.inr 0)
  let d : language.Term ((Fin (n + 1) ⊕ Unit) ⊕ Fin 2) := .var (.inr 1)
  let xs : Fin n → language.Term ((Fin (n + 1) ⊕ Unit) ⊕ Fin 2) :=
    fun i => .var (.inl (.inl i.castSucc))
  let k : language.Term ((Fin (n + 1) ⊕ Unit) ⊕ Fin 2) :=
    .var (.inl (.inl (Fin.last n)))
  let y : language.Term ((Fin (n + 1) ⊕ Unit) ⊕ Fin 2) := .var (.inl (.inr ()))
  let initial :=
    ((graphAt decoder ![c.relabel Sum.inl, d.relabel Sum.inl, zeroTerm]
      (.var (.inr ()))).imp
        (graphAt base (fun i => (xs i).relabel Sum.inl) (.var (.inr ())))).iAlls Unit
  let i : language.Term (((Fin (n + 1) ⊕ Unit) ⊕ Fin 2) ⊕ Unit) := .var (.inr ())
  let total := boundedAll k
    ((graphAt decoder ![(c.relabel Sum.inl).relabel Sum.inl,
      (d.relabel Sum.inl).relabel Sum.inl, i.relabel Sum.inl]
        (.var (.inr ()))).iExs Unit)
  let stepBody :=
    ((graphAt decoder ![(c.relabel Sum.inl).relabel Sum.inl,
        (d.relabel Sum.inl).relabel Sum.inl, i.relabel Sum.inl] (.var (.inr (0 : Fin 2)))) ⊓
      (graphAt decoder ![(c.relabel Sum.inl).relabel Sum.inl,
        (d.relabel Sum.inl).relabel Sum.inl, succTerm (i.relabel Sum.inl)]
          (.var (.inr (1 : Fin 2))))).imp
      (graphAt step
        (Fin.snoc (Fin.snoc (fun j => ((xs j).relabel Sum.inl).relabel Sum.inl)
          (i.relabel Sum.inl)) (.var (.inr (0 : Fin 2))))
        (.var (.inr (1 : Fin 2))))
  let next := strictAll k (stepBody.iAlls (Fin 2))
  (initial ⊓ (total ⊓ (next ⊓ graphAt decoder ![c, d, k] y))).iExs (Fin 2)

def decodeRealizes {M : Type*} [language.Structure M]
    (decoder : language.Formula (Fin 3 ⊕ Unit)) (c d i y : M) : Prop :=
  decoder.Realize (extend ![c, d, i] y)

theorem realize_recursionGraph {n : ℕ} {M : Type*} [language.Structure M]
    (decoder : language.Formula (Fin 3 ⊕ Unit))
    (base : language.Formula (Fin n ⊕ Unit))
    (step : language.Formula (Fin (n + 2) ⊕ Unit))
    (x : Fin n → M) (k y : M) :
    (recursionGraph decoder base step).Realize (extend (Fin.snoc x k) y) ↔
      ∃ cd : Fin 2 → M,
        (∀ u, decodeRealizes decoder (cd 0) (cd 1) (zeroValue M) u →
          base.Realize (extend x u)) ∧
        (∀ i, leValue M i k → ∃ u, decodeRealizes decoder (cd 0) (cd 1) i u) ∧
        (∀ i, leValue M (succValue M i) k → ∀ u v,
          decodeRealizes decoder (cd 0) (cd 1) i u →
          decodeRealizes decoder (cd 0) (cd 1) (succValue M i) v →
          step.Realize (extend (Fin.snoc (Fin.snoc x i) u) v)) ∧
        decodeRealizes decoder (cd 0) (cd 1) k y := by
  simp only [recursionGraph, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_imp, realize_graphAt, realize_boundedAll,
    realize_strictAll, Term.realize_var, Term.realize_relabel, realize_zeroTerm,
    realize_succTerm, Function.comp_def, extend, Sum.elim_inl, Sum.elim_inr,
    Fin.snoc_castSucc, Fin.snoc_last, realize_term_vec3,
    realize_term_snoc, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi,
    Fin.cons_zero, Fin.cons_one, decodeRealizes, forall_unit_function,
    exists_unit_function, and_imp]

theorem represents_primitiveRec {n : ℕ}
    (B : (Fin 3 → ℕ) → ℕ) (decoder : language.Formula (Fin 3 ⊕ Unit))
    (hB : StronglyRepresents B decoder)
    (hcodes : ∀ k (a : Fin k → ℕ), ∃ c d, ∀ i, B ![c, d, i.val] = a i)
    (f : (Fin n → ℕ) → ℕ) (g : (Fin (n + 2) → ℕ) → ℕ)
    (base : language.Formula (Fin n ⊕ Unit))
    (step : language.Formula (Fin (n + 2) ⊕ Unit))
    (hf : StronglyRepresents f base) (hg : StronglyRepresents g step) :
    StronglyRepresents (primitiveRecFunction f g) (recursionGraph decoder base step) := by
  apply stronglyRepresents_of_modelwise
  intro M inputs y
  let x : Fin n → ℕ := fun i => inputs i.castSucc
  let k := inputs (Fin.last n)
  let xs : Fin n → M := fun i => numeralValue M (x i)
  have hin : (fun i => numeralValue M (inputs i)) = Fin.snoc xs (numeralValue M k) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; rfl
    · simp only [Fin.snoc_castSucc]; rfl
  rw [hin, realize_recursionGraph]
  change (∃ cd, _) ↔ y = numeralValue M (primitiveRec f g x k)
  constructor
  · rintro ⟨cd, hinit, htotal, hstep, hend⟩
    have hvalues : ∀ j, j ≤ k → ∀ u,
        decodeRealizes decoder (cd 0) (cd 1) (numeralValue M j) u →
          u = numeralValue M (primitiveRec f g x j) := by
      intro j
      induction j with
      | zero =>
        intro _ u hu
        rw [numeral_value_zero] at hu
        exact (stronglyRepresents_modelwise hf x u).mp (hinit u hu)
      | succ j ih =>
        intro hj v hv
        have hjk : j ≤ k := by omega
        obtain ⟨u, hu⟩ := htotal (numeralValue M j)
          ((finite_bound _ _).mpr ⟨j, hjk, rfl⟩)
        have he := ih hjk u hu
        subst u
        have hlt : leValue M (succValue M (numeralValue M j)) (numeralValue M k) :=
          (strict_finite_bound _ _).mpr ⟨j, by omega, rfl⟩
        have hp := hstep (numeralValue M j) hlt _ v hu
          (by simpa only [numeral_value_succ] using hv)
        have h := stronglyRepresents_modelwise hg
          (Fin.snoc (Fin.snoc x j) (primitiveRec f g x j)) v
        simp only [← numeral_snoc] at h
        exact h.mp hp
    exact hvalues k le_rfl y hend
  · intro hy
    obtain ⟨c, d, hc⟩ := hcodes (k + 1) (fun i => primitiveRec f g x i.val)
    have hdec (j : ℕ) (hj : j ≤ k) (z : M) :
        decodeRealizes decoder (numeralValue M c) (numeralValue M d)
          (numeralValue M j) z ↔ z = numeralValue M (primitiveRec f g x j) := by
      have h := stronglyRepresents_modelwise hB (![c, d, j]) z
      rw [numeral_vec3, hc ⟨j, by omega⟩] at h
      exact h
    refine ⟨![numeralValue M c, numeralValue M d], ?_, ?_, ?_, ?_⟩
    · intro u hu
      have he := (hdec 0 (Nat.zero_le _) u).mp
        (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, numeral_value_zero] using hu)
      exact (stronglyRepresents_modelwise hf x u).mpr he
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := (finite_bound i k).mp hi
      exact ⟨numeralValue M (primitiveRec f g x j), (hdec j hj _).mpr rfl⟩
    · intro i hi u v hu hv
      obtain ⟨j, hj, rfl⟩ := (strict_finite_bound i k).mp hi
      have heu := (hdec j (Nat.le_of_lt hj) u).mp hu
      have hev := (hdec (j + 1) (by omega) v).mp
        (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, numeral_value_succ] using hv)
      subst u
      have h := stronglyRepresents_modelwise hg
        (Fin.snoc (Fin.snoc x j) (primitiveRec f g x j)) v
      simp only [← numeral_snoc] at h
      exact h.mpr hev
    · exact (hdec k le_rfl y).mpr hy

end
end Lemmatheca.MathematicalLogic.ArithmeticRepresentability
