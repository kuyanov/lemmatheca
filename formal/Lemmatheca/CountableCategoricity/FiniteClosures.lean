import Lemmatheca.CountableCategoricity.FormulaClasses
import Lemmatheca.DefinableAndAlgebraicClosure.Closures
import Mathlib.SetTheory.Cardinal.Finite

/-! Finite formula classes bound fixed-parameter definitions and generated carriers. -/
namespace Lemmatheca.ModelTheory.CountableCategoricity

open FirstOrder FirstOrder.Language

universe u v w
variable {L : Language.{u, v}} {T : L.Theory}
variable {M : Type w} [L.Structure M] [Nonempty M] [M ⊨ T] {m : ℕ}

/-- Evaluate the one object variable while retaining this particular parameter tuple. -/
def unarySet (a : Fin m → M) (φ : L.Formula (Fin 1 ⊕ Fin m)) : Set M :=
  {b | φ.Realize (Sum.elim (fun _ => b) a)}

/-- The equivalence is taken over T and is applied at the same fixed parameter values. -/
theorem unarySet_equiv (a : Fin m → M) (φ ψ : L.Formula (Fin 1 ⊕ Fin m))
    (h : T.Iff φ ψ) : unarySet a φ = unarySet a ψ := by
  ext b
  exact h.realize_iff

/-- The actual evaluation map from formula classes to subsets at the fixed tuple. -/
def unaryClassSet (a : Fin m → M) : FormulaClass T (Fin 1 ⊕ Fin m) → Set M :=
  Quotient.lift (unarySet a) (fun φ ψ h => unarySet_equiv a φ ψ h)

/-- Replacing the parameter constants by free coordinates gives exactly these definitions. -/
theorem unaryClassSet_range (a : Fin m → M) :
    Set.range (unaryClassSet (T := T) a) =
      {s : Set M | (Set.range a).Definable₁ L s} := by
  classical
  let k : Set.range a → Fin m := fun b => Classical.choose b.property
  have hk (b : Set.range a) : a (k b) = b.val := Classical.choose_spec b.property
  ext s
  constructor
  · rintro ⟨c, rfl⟩
    induction c using Quotient.inductionOn with | h φ =>
      apply Set.definable_iff_exists_formula_sum.mpr
      let g : Fin 1 ⊕ Fin m → Set.range a ⊕ Fin 1 :=
        Sum.elim Sum.inr (fun j => Sum.inl ⟨a j, Set.mem_range_self j⟩)
      refine ⟨Formula.relabel g φ, ?_⟩
      ext x
      change Formula.Realize φ (Sum.elim (fun _ => x 0) a) ↔ (Formula.relabel g φ).Realize _
      rw [Formula.realize_relabel]
      have h : Sum.elim (Subtype.val : Set.range a → M) x ∘ g =
          Sum.elim (fun _ => x 0) a := by
        funext i
        cases i with
        | inl j => exact congrArg x (Subsingleton.elim j 0)
        | inr j => rfl
      rw [h]
  · intro hs
    obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hs
    let g : Set.range a ⊕ Fin 1 → Fin 1 ⊕ Fin m := Sum.elim (Sum.inr ∘ k) Sum.inl
    refine ⟨classOf T (Formula.relabel g φ), ?_⟩
    ext b
    have hb := Set.ext_iff.mp hφ (fun _ : Fin 1 => b)
    change b ∈ s ↔ Formula.Realize φ (Sum.elim (Subtype.val : Set.range a → M) (fun _ => b)) at hb
    change (Formula.relabel g φ).Realize (Sum.elim (fun _ => b) a) ↔ b ∈ s
    rw [Formula.realize_relabel, hb]
    have h : Sum.elim (fun _ : Fin 1 => b) a ∘ g =
        Sum.elim (Subtype.val : Set.range a → M) (fun _ => b) := by
      funext i
      cases i with
      | inl j => exact hk j
      | inr j => rfl
    rw [h]

/-- Only finitely many unary sets are definable over any specified finite parameter set. -/
theorem finite_unary_definable_sets (hF : ∀ n, Finite (FormulaClass T (Fin n)))
    (A : Set M) (hA : A.Finite) : {s : Set M | A.Definable₁ L s}.Finite := by
  classical
  let := hA.fintype
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let a : Fin (Fintype.card A) → M := Subtype.val ∘ e.symm
  have hr : Set.range a = A := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).prop
    · intro hx
      exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply _)⟩
  let := finite_classes_context (α := Fin 1 ⊕ Fin (Fintype.card A)) hF
  rw [← hr, ← unaryClassSet_range (T := T) a]
  exact Set.finite_range _

/-- Algebraic closure is a union of only finitely many finite definable sets. -/
theorem finite_acl (hF : ∀ n, Finite (FormulaClass T (Fin n)))
    (A : Set M) (hA : A.Finite) : (Closures.acl L A).Finite := by
  have hf : {s : Set M | A.Definable₁ L s ∧ s.Finite}.Finite :=
    (finite_unary_definable_sets hF A hA).subset fun _ hs => hs.1
  have hu := hf.biUnion (fun s hs => hs.2)
  apply hu.subset
  rintro b ⟨s, hs, hfin, hb⟩
  exact Set.mem_iUnion₂.mpr ⟨s, ⟨hs, hfin⟩, hb⟩

/-- Definable closure lies inside the finite algebraic closure. -/
theorem finite_dcl (hF : ∀ n, Finite (FormulaClass T (Fin n)))
    (A : Set M) (hA : A.Finite) : (Closures.dcl L A).Finite := by
  exact (finite_acl hF A hA).subset (Closures.dcl_subset_acl A)

/-- The generated carrier lies inside definable closure, including constants and the empty case. -/
theorem finite_generated (hF : ∀ n, Finite (FormulaClass T (Fin n)))
    (A : Set M) (hA : A.Finite) : (Substructure.closure L A : Set M).Finite := by
  exact (finite_dcl hF A hA).subset
    ((Substructure.closure_le (S := Closures.dclSubstructure A)).mpr (Closures.subset_dcl A))

/-- The graph formula uses coordinate zero for the value and successors for the parameters. -/
def termGraph (t : L.Term (Fin m)) : L.Formula (Fin (m + 1)) :=
  (Term.var 0 : L.Term (Fin (m + 1))).equal (t.relabel Fin.succ)

omit [Nonempty M] in
/-- The concrete graph formula evaluates the specified term at the specified parameter tuple. -/
theorem termGraph_realize (t : L.Term (Fin m)) (a : Fin m → M) (b : M) :
    (termGraph t).Realize (Fin.cons b a) ↔ b = t.realize a := by
  simp only [termGraph, Formula.realize_equal, Term.realize_var, Fin.cons_zero,
    Term.realize_relabel]
  rfl

/-- Equal graph classes force equal values in every model at every fixed parameter tuple. -/
theorem equivalent_graph_values (t s : L.Term (Fin m))
    (h : T.Iff (termGraph t) (termGraph s)) (a : Fin m → M) :
    t.realize a = s.realize a := by
  have h := (h.realize_iff (v := Fin.cons (t.realize a) a)).mp
    ((termGraph_realize t a _).mpr rfl)
  exact (termGraph_realize s a _).mp h

/-- Choosing representative terms embeds the generated carrier into actual graph-formula classes. -/
theorem generated_graph_injection (a : Fin m → M) :
    ∃ f : Substructure.closure L (Set.range a) ↪ FormulaClass T (Fin (m + 1)),
      ∀ b, ∃ t : L.Term (Fin m),
        t.realize a = b.val ∧ f b = classOf T (termGraph t) := by
  classical
  let k : Set.range a → Fin m := fun b => Classical.choose b.property
  have hk : a ∘ k = (Subtype.val : Set.range a → M) :=
    funext fun b => Classical.choose_spec b.property
  have ht : ∀ b : Substructure.closure L (Set.range a),
      ∃ t : L.Term (Fin m), t.realize a = b.val := by
    intro b
    obtain ⟨t, ht⟩ := Substructure.mem_closure_iff_exists_term.mp b.property
    exact ⟨t.relabel k, by rw [Term.realize_relabel, hk, ht]⟩
  choose t ht using ht
  let f : Substructure.closure L (Set.range a) → FormulaClass T (Fin (m + 1)) :=
    fun b => classOf T (termGraph (t b))
  have hf : Function.Injective f := by
    intro b c h
    have he : T.Iff (termGraph (t b)) (termGraph (t c)) := Quotient.exact h
    apply Subtype.ext
    rw [← ht b, ← ht c]
    exact equivalent_graph_values _ _ he a
  exact ⟨⟨f, hf⟩, fun b => ⟨t b, ht b, rfl⟩⟩

/-- The number of formula classes gives one bound for every tuple of this length in every model. -/
theorem generated_uniform_bound (hF : ∀ n, Finite (FormulaClass T (Fin n)))
    (a : Fin m → M) :
    Nat.card (Substructure.closure L (Set.range a)) ≤
      Nat.card (FormulaClass T (Fin (m + 1))) := by
  let := hF (m + 1)
  obtain ⟨f, _⟩ := generated_graph_injection (T := T) a
  exact Nat.card_le_card_of_injective f f.injective

/-- A uniform finite bound for each tuple length throughout the class of models. -/
def UniformLocallyFinite (T : L.Theory) : Prop :=
  ∀ m, ∃ K : ℕ, ∀ N : Theory.ModelType.{u, v, max u v} T, ∀ a : Fin m → N,
    (Substructure.closure L (Set.range a) : Set N).Finite ∧
      Nat.card (Substructure.closure L (Set.range a)) ≤ K

/-- The bound is the number of formula classes in the context with one additional value variable. -/
theorem uniform_locally_finite (hF : ∀ n, Finite (FormulaClass T (Fin n))) :
    UniformLocallyFinite T := by
  intro m
  refine ⟨Nat.card (FormulaClass T (Fin (m + 1))), fun N a => ?_⟩
  exact ⟨finite_generated hF _ (Set.finite_range a), generated_uniform_bound hF a⟩

end Lemmatheca.ModelTheory.CountableCategoricity
