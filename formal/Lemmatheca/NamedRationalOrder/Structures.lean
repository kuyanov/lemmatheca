import Lemmatheca.AtomicAndPrimeModels.AtomicModels
import Lemmatheca.CountableCategoricity.Categoricity
import Lemmatheca.CountableSaturatedModels.Constructions
import Lemmatheca.CountableModels.NamedQuantifierElimination
import Mathlib.Analysis.Real.Cardinality

/-! The actual strict-order language with one constant for each rational. -/
namespace Lemmatheca.ModelTheory.NamedRationalOrder

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open QuantifierElimination.Shared Types IsolatedTypes AtomicAndPrimeModels

abbrev rationalLanguage : Language := binaryRelLanguage[[ℚ]]

@[instance_reducible] def rationalStructure : rationalLanguage.Structure ℚ := by
  let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (· < ·)
  exact Diagrams.namedExpansion (L := binaryRelLanguage) (id : ℚ → ℚ)

def theory : rationalLanguage.Theory :=
  @Language.completeTheory rationalLanguage ℚ rationalStructure

@[reducible] def rationalModel : theory.ModelType.{0, 0, 0} := by
  let : rationalLanguage.Structure ℚ := rationalStructure
  let : ℚ ⊨ theory := by
    change ℚ ⊨ rationalLanguage.completeTheory ℚ
    infer_instance
  exact Theory.ModelType.of theory ℚ

instance : Countable rationalModel := inferInstanceAs (Countable ℚ)

instance : Countable rationalLanguage.Symbols := by
  have : Subsingleton binaryRelLanguage.Symbols := by
    constructor
    rintro (⟨n, f⟩ | ⟨n, r⟩) (⟨m, g⟩ | ⟨m, t⟩)
    · exact f.elim
    · exact f.elim
    · exact g.elim
    · cases r
      cases t
      rfl
  let : Countable binaryRelLanguage.Symbols := inferInstance
  change Countable (binaryRelLanguage[[ℚ]]).Symbols
  infer_instance

theorem theory_complete : theory.IsComplete := by
  let : rationalLanguage.Structure ℚ := rationalStructure
  exact completeTheory.isComplete rationalLanguage ℚ

theorem reduct_axioms :
    (binaryRelLanguage.lhomWithConstants ℚ).onTheory strictDloTheory ⊆ theory := by
  let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (· < ·)
  let : rationalLanguage.Structure ℚ := rationalStructure
  let : (binaryRelLanguage.lhomWithConstants ℚ).IsExpansionOn ℚ :=
    Diagrams.namedExpansion_isExpansion (L := binaryRelLanguage) (id : ℚ → ℚ)
  let : ℚ ⊨ strictDloTheory := model_strictDloTheory
  exact Theory.model_iff_subset_completeTheory.mp
    (((binaryRelLanguage.lhomWithConstants ℚ).onTheory_model strictDloTheory).mpr
      (inferInstance : ℚ ⊨ strictDloTheory))

theorem named_order (M : theory.ModelType.{0, 0, 0}) (p q : ℚ) :
    Structure.RelMap (L := rationalLanguage) (Sum.inl BinaryRelationSymbol.rel)
      ![(binaryRelLanguage.con p : M), (binaryRelLanguage.con q : M)] ↔ p < q := by
  let σ : rationalLanguage.Sentence := Relations.formula₂ (L := rationalLanguage)
    (Sum.inl BinaryRelationSymbol.rel)
    (Constants.term (binaryRelLanguage.con p)) (Constants.term (binaryRelLanguage.con q))
  let : M ⊨ rationalLanguage.completeTheory rationalModel := M.is_model
  have h := realize_iff_of_model_completeTheory rationalModel M σ
  simp only [σ, Sentence.Realize, FirstOrder.Language.Formula.Realize,
    Relations.formula₂, Relations.formula, Relations.boundedFormula, BoundedFormula.Realize,
    Term.realize_relabel] at h
  have hv (N : Type) [rationalLanguage.Structure N] (v : Empty → N) :
      (fun i : Fin 2 => Term.realize v
        (![(binaryRelLanguage.con p).term, (binaryRelLanguage.con q).term] i)) =
      ![(binaryRelLanguage.con p : N), (binaryRelLanguage.con q : N)] := by
    funext i
    fin_cases i
    · change Term.realize v (Constants.term (binaryRelLanguage.con p)) =
        (binaryRelLanguage.con p : N)
      exact Term.realize_constants
    · change Term.realize v (Constants.term (binaryRelLanguage.con q)) =
        (binaryRelLanguage.con q : N)
      exact Term.realize_constants
  simp only [hv] at h
  exact h

noncomputable def tupleIsolator {n : ℕ} (a : Fin n → ℚ) :
    rationalLanguage.Formula (Fin n) :=
  Formula.iInf fun i => (Term.var i).equal (Constants.term ((binaryRelLanguage.con (a i : ℚ) : rationalLanguage.Constants)))

theorem tupleIsolator_realize {n : ℕ} (a : Fin n → ℚ)
    (M : theory.ModelType.{0, 0, 0}) (b : Fin n → M) :
    (tupleIsolator a).Realize b ↔ ∀ i, b i = ((binaryRelLanguage.con (a i : ℚ) : rationalLanguage.Constants) : M) := by
  simp only [tupleIsolator, Formula.realize_iInf, Formula.realize_equal,
    Term.realize_var, Term.realize_constants]

theorem tupleIsolator_isolates {n : ℕ} (a : Fin n → rationalModel) :
    Isolates theory (theory.typeOf a) (tupleIsolator a) := by
  have truth (M : theory.ModelType.{0, 0, 0}) (φ : rationalLanguage.Formula (Fin n)) :
      M ⊨ φ.subst (fun i => (Constants.term ((binaryRelLanguage.con (a i : ℚ) : rationalLanguage.Constants)) :
        rationalLanguage.Term Empty)) ↔
      φ.Realize (fun i => ((binaryRelLanguage.con (a i : ℚ) : rationalLanguage.Constants) : M)) := by
    simp only [Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_subst, Term.realize_constants]
  refine ⟨Theory.CompleteType.formula_mem_typeOf.mpr ?_, fun φ hφ => ?_⟩
  · exact (tupleIsolator_realize a rationalModel a).mpr (fun _ => rfl)
  · apply Theory.models_formula_iff.mpr
    intro M b
    change (tupleIsolator a).Realize b → φ.Realize b
    intro hb
    have he : b = fun i => ((binaryRelLanguage.con (a i : ℚ) : rationalLanguage.Constants) : M) :=
      funext ((tupleIsolator_realize a M b).mp hb)
    rw [he]
    apply (truth M φ).mp
    apply Theory.realize_sentence_of_mem theory
    change rationalModel ⊨ φ.subst (fun i => (Constants.term ((binaryRelLanguage.con (a i : ℚ) : rationalLanguage.Constants)) :
      rationalLanguage.Term Empty))
    apply (truth rationalModel φ).mpr
    exact Theory.CompleteType.formula_mem_typeOf.mp hφ

theorem rational_atomic : IsAtomic theory rationalModel := by
  intro n a
  exact ⟨tupleIsolator a, tupleIsolator_isolates a⟩

theorem rational_prime : IsPrime theory rationalModel := by
  exact countable_atomic_prime theory_complete rational_atomic

/-- The underlying function is exactly the interpretation of the rational names. -/
noncomputable def canonicalEmbedding (M : theory.ModelType.{0, 0, 0}) :
    rationalModel ↪ₑ[rationalLanguage] M where
  toFun := fun q : rationalModel =>
    ((binaryRelLanguage.con (q : ℚ) : rationalLanguage.Constants) : M)
  map_formula' := by
    intro n φ a
    obtain ⟨e⟩ := rational_prime M
    have he (q : rationalModel) : e q =
        ((binaryRelLanguage.con (q : ℚ) : rationalLanguage.Constants) : M) :=
      e.map_constants (binaryRelLanguage.con (q : ℚ))
    simpa only [funext he] using e.map_formula φ a

theorem canonicalEmbedding_unique (M : theory.ModelType.{0, 0, 0})
    (f : rationalModel ↪ₑ[rationalLanguage] M) : f = canonicalEmbedding M := by
  apply ElementaryEmbedding.ext
  intro q
  exact f.map_constants (binaryRelLanguage.con (q : ℚ))

def pointType (q : ℚ) : theory.CompleteType (Fin 1) :=
  theory.typeOf (M := rationalModel) (fun _ : Fin 1 => (q : rationalModel))

theorem pointType_injective : Function.Injective pointType := by
  intro p q h
  let φ : rationalLanguage.Formula (Fin 1) :=
    (Term.var 0).equal (Constants.term (binaryRelLanguage.con p))
  have hp : φ ∈ formulas (pointType p) :=
    Theory.CompleteType.formula_mem_typeOf.mpr (by change p = p; rfl)
  have hq := Theory.CompleteType.formula_mem_typeOf.mp (h ▸ hp)
  change q = p at hq
  exact hq.symm

theorem isolated_iff_named (p : theory.CompleteType (Fin 1)) :
    Isolated theory p ↔ ∃ q : ℚ, p = pointType q := by
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := isolated_realized (M := rationalModel) theory_complete p hp
    refine ⟨a 0, ?_⟩
    have he : a = fun _ : Fin 1 => a 0 := funext (fun i => congrArg a (Subsingleton.elim _ _))
    exact ((realizes_complete_iff p a).mp ha).trans
      (congrArg (fun b : Fin 1 → rationalModel => theory.typeOf b) he)
  · rintro ⟨q, rfl⟩
    exact rational_atomic 1 (fun _ : Fin 1 => (q : rationalModel))

def aboveFormula (q : ℚ) : rationalLanguage.Formula (Fin 1) :=
  Relations.formula (Sum.inl BinaryRelationSymbol.rel)
    ![Constants.term (binaryRelLanguage.con q), Term.var 0]

def aboveAll : Set (rationalLanguage.Formula (Fin 1)) := Set.range aboveFormula

theorem aboveFormula_realize (q : ℚ) (a : Fin 1 → rationalModel) :
    (aboveFormula q).Realize a ↔ q < a 0 := by
  rfl

theorem aboveAll_finitely_realized : FinitelyRealized rationalModel aboveAll := by
  classical
  intro s hs
  let q : ↑s → ℚ := fun φ => Classical.choose (hs φ.property)
  have hq (φ : ↑s) : aboveFormula (q φ) = φ.val := Classical.choose_spec (hs φ.property)
  obtain ⟨b, hb⟩ := (Set.finite_range q).bddAbove
  let c : rationalModel := by exact (b + 1 : ℚ)
  have hc : b < (c : ℚ) := by change b < b + 1; exact lt_add_one b
  refine ⟨(fun _ : Fin 1 => c), fun φ hφ => ?_⟩
  have he : aboveFormula (q ⟨φ, hφ⟩) = φ := hq ⟨φ, hφ⟩
  rw [← he]
  exact (aboveFormula_realize _ _).mpr
    (lt_of_le_of_lt (hb (Set.mem_range_self (f := q) (⟨φ, hφ⟩ : ↑s))) hc)

theorem aboveAll_partial : IsPartial theory aboveAll := by
  exact (partial_iff_finitelyRealized_completeTheory (M := rationalModel) aboveAll).mpr aboveAll_finitely_realized

theorem aboveAll_omitted : Omits rationalModel aboveAll := by
  rintro ⟨a, ha⟩
  exact lt_irrefl (α := ℚ) (a 0) ((aboveFormula_realize (a 0) a).mp
    (ha _ (Set.mem_range_self (a 0))))

theorem rational_not_saturated : ¬ Saturation.OmegaSaturated rationalLanguage rationalModel := by
  intro hs
  obtain ⟨p, hp⟩ := exists_complete_extension aboveAll aboveAll_partial
  obtain ⟨a, ha⟩ := CountableSaturatedModels.saturated_realizes_types theory_complete hs 1 p
  exact aboveAll_omitted ⟨a, fun φ hφ => ha φ (hp hφ)⟩

@[instance_reducible] def realStructure : rationalLanguage.Structure ℝ := by
  let : binaryRelLanguage.Structure ℝ := binaryRelStructure ℝ (· < ·)
  exact Diagrams.namedExpansion (L := binaryRelLanguage) (Rat.cast : ℚ → ℝ)

theorem real_models : letI := realStructure; ℝ ⊨ theory := by
  let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (· < ·)
  let : binaryRelLanguage.Structure ℝ := binaryRelStructure ℝ (· < ·)
  let : ℚ ⊨ strictDloTheory := model_strictDloTheory
  let : ℝ ⊨ strictDloTheory := model_strictDloTheory
  let f : ℚ ↪[binaryRelLanguage] ℝ :=
    { toFun := Rat.cast
      inj' := Rat.cast_injective
      map_fun' := by intro n g; exact g.elim
      map_rel' := by
        intro n r a
        cases r
        change ((a 0 : ℝ) < (a 1 : ℝ)) ↔ a 0 < a 1
        exact Rat.cast_lt }
  let e := strictDlo_elementaryEmbedding f
  exact Diagrams.elementary_namedExpansion_models_diagram e

@[reducible] noncomputable def realModel : theory.ModelType.{0, 0, 0} := by
  let : rationalLanguage.Structure ℝ := realStructure
  let : ℝ ⊨ theory := real_models
  exact Theory.ModelType.of theory ℝ

/-- The original rational inclusion, retaining every named rational. -/
noncomputable def realInclusion : rationalModel ↪ₑ[rationalLanguage] realModel where
  toFun := fun q : rationalModel => (Rat.cast : ℚ → ℝ) q
  map_formula' := by
    intro n φ a
    exact (canonicalEmbedding realModel).map_formula φ a

theorem real_has_unnamed : ∃ r : realModel, ∀ q : ℚ, (q : ℝ) ≠ r := by
  by_contra hn
  have hs : Function.Surjective (Rat.cast : ℚ → ℝ) := by
    intro r
    by_contra hr
    exact hn ⟨r, fun q hq => hr ⟨q, hq⟩⟩
  exact not_countable (α := ℝ) hs.countable

end Lemmatheca.ModelTheory.NamedRationalOrder
