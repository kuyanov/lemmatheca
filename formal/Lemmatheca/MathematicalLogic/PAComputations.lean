import Lemmatheca.MathematicalLogic.ArithmeticRepresentability
import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityConsequences
import Lemmatheca.MathematicalLogic.DiagonalCoding
import Lemmatheca.MathematicalLogic.PAFormulaDefinability
import Lemmatheca.MathematicalLogic.PAChineseRemainder
import Lemmatheca.MathematicalLogic.ArithmeticBoundedTuples
import Lemmatheca.MathematicalLogic.PABetaCoding

/-! Canonical arithmetic graphs of finite primitive-recursive presentations.

The formulas below use the corpus's shared arithmetic language and its actual
PA theory. The raw graphs retain the earlier numeralwise construction. Their
uniform PA properties and existential bounded normalization are additional
theorems; the old numeralwise result is not used as a substitute for them.
-/
namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open FirstOrderProofs
noncomputable section
universe u

/-- Universal closure, independent of a particular finite-variable enumeration. -/
def allClose {α : Type} [Fintype α] (φ : language.Formula α) : language.Sentence :=
  (φ.relabel (Sum.inr : α → Empty ⊕ α)).iAlls α

theorem realize_allClose {α : Type} [Fintype α] {M : Type u}
    [language.Structure M] (φ : language.Formula α) :
    M ⊨ allClose φ ↔ ∀ x : α → M, φ.Realize x := by
  simp only [allClose, Sentence.Realize, Formula.realize_iAlls,
    Formula.realize_relabel, Function.comp_def, Sum.elim_inr]

/-- The actual sentence asserting totality and uniqueness at all internal inputs. -/
def totalUnique {n : ℕ} (φ : language.Formula (Fin n ⊕ Unit)) : language.Sentence :=
  let compare : language.Formula ((Fin n ⊕ Unit) ⊕ Unit) :=
    (graphAt φ (fun i => .var (.inl (.inl i))) (.var (.inr ()))).imp
      ((Term.var (.inr ())).equal (.var (.inl (.inr ()))))
  allClose ((φ ⊓ compare.iAlls Unit).iExs Unit)

theorem realize_totalUnique {n : ℕ} {M : Type u} [language.Structure M]
    (φ : language.Formula (Fin n ⊕ Unit)) :
    M ⊨ totalUnique φ ↔ ∀ x : Fin n → M, ∃! y, φ.Realize (extend x y) := by
  simp only [totalUnique, realize_allClose, Formula.realize_iExs,
    Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_graphAt, Term.realize_var, Formula.realize_equal,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h x
    obtain ⟨y, hy, huniq⟩ := h x
    refine ⟨y (), ?_, ?_⟩
    · convert hy using 1
      congr 1
    · intro z hz
      exact huniq (fun _ => z) hz
  · intro h x
    obtain ⟨y, hy, huniq⟩ := h x
    exact ⟨fun _ => y, hy, fun z hz => huniq (z ()) hz⟩

/-- A graph agrees at the ordinary natural numbers and is uniformly functional
in PA. Defining-equation theorems are recorded separately for the canonical graph. -/
def UniformlyRepresents {n : ℕ} (f : (Fin n → ℕ) → ℕ)
    (φ : language.Formula (Fin n ⊕ Unit)) : Prop :=
  (∀ x y, φ.Realize (extend x y) ↔ y = f x) ∧ Derives PA (totalUnique φ)

/-- Literal existential-prefix bounded syntax, not merely standard equivalence. -/
def SigmaOne {α : Type} (φ : language.Formula α) : Prop :=
  ∃ k : ℕ, ∃ δ : language.Formula (α ⊕ Fin k), DeltaZero δ ∧ φ = δ.iExs (Fin k)

/-- Explicit data for an existential-prefix bounded formula. -/
structure SigmaOneForm (α : Type) where
  witnesses : ℕ
  matrix : language.Formula (α ⊕ Fin witnesses)
  bounded : DeltaZero matrix

def SigmaOneForm.formula {α : Type} (s : SigmaOneForm α) : language.Formula α :=
  s.matrix.iExs (Fin s.witnesses)

theorem SigmaOneForm.isSigmaOne {α : Type} (s : SigmaOneForm α) :
    SigmaOne s.formula := ⟨s.witnesses, s.matrix, s.bounded, rfl⟩

def PAEquivalent {α : Type} [Fintype α] (φ ψ : language.Formula α) : Prop :=
  Derives PA (allClose (φ.iff ψ))

def SigmaOneEquivalent {α : Type} [Fintype α] (φ : language.Formula α) : Prop :=
  ∃ s : SigmaOneForm α, PAEquivalent φ s.formula

private theorem equivalent_model {α : Type} [Fintype α]
    {φ ψ : language.Formula α} (h : PAEquivalent φ ψ)
    (M : Theory.ModelType.{0,0,0} PA) (v : α → M) : φ.Realize v ↔ ψ.Realize v := by
  have hh : M ⊨ allClose (φ.iff ψ) :=
    derives_sound h default (fun B hB => Theory.realize_sentence_of_mem PA hB)
  exact Formula.realize_iff.mp ((realize_allClose _).mp hh v)

private theorem deltaZero_inf {α : Type} {φ ψ : language.Formula α}
    (hφ : DeltaZero φ) (hψ : DeltaZero ψ) : DeltaZero (φ ⊓ ψ) :=
  .imp (.imp hφ (.imp hψ .falsum)) .falsum

private theorem deltaZero_sup {α : Type} {φ ψ : language.Formula α}
    (hφ : DeltaZero φ) (hψ : DeltaZero ψ) : DeltaZero (φ ⊔ ψ) :=
  .imp (.imp hφ .falsum) hψ

/-- Finite witness types can be enumerated without changing the interpreted
existential statement. The result still has a literal `Fin` prefix. -/
private theorem normalized_of_model {α β : Type} [Fintype α] [Fintype β]
    (φ : language.Formula α) (δ : language.Formula (α ⊕ β)) (hδ : DeltaZero δ)
    (h : ∀ (M : Theory.ModelType.{0,0,0} PA) (v : α → M),
      φ.Realize v ↔ ∃ w : β → M, δ.Realize (Sum.elim v w)) : SigmaOneEquivalent φ := by
  let e : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
  let s : SigmaOneForm α := ⟨Fintype.card β, δ.relabel (Sum.map id e), hδ.relabel _⟩
  refine ⟨s, HenkinCompleteness.deductive_completeness ?_⟩
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_allClose]
  intro v
  rw [Formula.realize_iff, h M v]
  simp only [s, SigmaOneForm.formula, Formula.realize_iExs, Formula.realize_relabel]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun j => w (e.symm j), ?_⟩
    convert hw using 1
    funext x
    cases x <;> simp
  · rintro ⟨w, hw⟩
    refine ⟨fun j => w (e j), ?_⟩
    convert hw using 1
    funext x
    cases x <;> rfl

private theorem normalized_bounded {α : Type} [Fintype α]
    (φ : language.Formula α) (hφ : DeltaZero φ) : SigmaOneEquivalent φ := by
  apply normalized_of_model (β := Empty) φ (φ.relabel Sum.inl) (hφ.relabel _)
  intro M v
  simp only [Formula.realize_relabel]
  exact ⟨fun h => ⟨Empty.elim, h⟩, fun ⟨_, h⟩ => h⟩

private theorem normalized_transfer {α : Type} [Fintype α]
    (φ ψ : language.Formula α) (hψ : SigmaOneEquivalent ψ)
    (h : ∀ (M : Theory.ModelType.{0,0,0} PA) (v : α → M), φ.Realize v ↔ ψ.Realize v) :
    SigmaOneEquivalent φ := by
  obtain ⟨s, hs⟩ := hψ
  refine ⟨s, HenkinCompleteness.deductive_completeness ?_⟩
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_allClose]
  intro v
  rw [Formula.realize_iff]
  exact (h M v).trans (equivalent_model hs M v)

private theorem normalized_inf {α : Type} [Fintype α]
    (φ ψ : language.Formula α) (hφ : SigmaOneEquivalent φ) (hψ : SigmaOneEquivalent ψ) :
    SigmaOneEquivalent (φ ⊓ ψ) := by
  obtain ⟨s, hs⟩ := hφ
  obtain ⟨t, ht⟩ := hψ
  let δ : language.Formula (α ⊕ (Fin s.witnesses ⊕ Fin t.witnesses)) :=
    s.matrix.relabel (Sum.map id Sum.inl) ⊓ t.matrix.relabel (Sum.map id Sum.inr)
  apply normalized_of_model (φ ⊓ ψ) δ
    (deltaZero_inf (s.bounded.relabel _) (t.bounded.relabel _))
  intro M v
  rw [Formula.realize_inf, equivalent_model hs M v, equivalent_model ht M v]
  simp only [SigmaOneForm.formula, Formula.realize_iExs, δ,
    Formula.realize_inf, Formula.realize_relabel]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨Sum.elim a b, ?_, ?_⟩
    · convert ha using 1; funext x; cases x <;> rfl
    · convert hb using 1; funext x; cases x <;> rfl
  · rintro ⟨w, ha, hb⟩
    constructor
    · refine ⟨fun j => w (.inl j), ?_⟩
      convert ha using 1; funext x; cases x <;> rfl
    · refine ⟨fun j => w (.inr j), ?_⟩
      convert hb using 1; funext x; cases x <;> rfl

private theorem normalized_sup {α : Type} [Fintype α]
    (φ ψ : language.Formula α) (hφ : SigmaOneEquivalent φ) (hψ : SigmaOneEquivalent ψ) :
    SigmaOneEquivalent (φ ⊔ ψ) := by
  obtain ⟨s, hs⟩ := hφ
  obtain ⟨t, ht⟩ := hψ
  let δ : language.Formula (α ⊕ (Fin s.witnesses ⊕ Fin t.witnesses)) :=
    s.matrix.relabel (Sum.map id Sum.inl) ⊔ t.matrix.relabel (Sum.map id Sum.inr)
  apply normalized_of_model (φ ⊔ ψ) δ
    (deltaZero_sup (s.bounded.relabel _) (t.bounded.relabel _))
  intro M v
  rw [Formula.realize_sup, equivalent_model hs M v, equivalent_model ht M v]
  simp only [SigmaOneForm.formula, Formula.realize_iExs, δ,
    Formula.realize_sup, Formula.realize_relabel]
  constructor
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · refine ⟨Sum.elim a (fun _ => zeroValue M), Or.inl ?_⟩
      convert ha using 1; funext x; cases x <;> rfl
    · refine ⟨Sum.elim (fun _ => zeroValue M) b, Or.inr ?_⟩
      convert hb using 1; funext x; cases x <;> rfl
  · rintro ⟨w, h | h⟩
    · apply Or.inl
      refine ⟨fun j => w (.inl j), ?_⟩
      convert h using 1; funext x; cases x <;> rfl
    · apply Or.inr
      refine ⟨fun j => w (.inr j), ?_⟩
      convert h using 1; funext x; cases x <;> rfl

private theorem normalized_iExs {α β : Type} [Fintype α] [Fintype β]
    (φ : language.Formula (α ⊕ β)) (hφ : SigmaOneEquivalent φ) :
    SigmaOneEquivalent (φ.iExs β) := by
  obtain ⟨s, hs⟩ := hφ
  let f : (α ⊕ β) ⊕ Fin s.witnesses → α ⊕ (β ⊕ Fin s.witnesses) :=
    Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
  apply normalized_of_model (φ.iExs β) (s.matrix.relabel f) (s.bounded.relabel _)
  intro M v
  simp only [Formula.realize_iExs]
  have he (a : β → M) := equivalent_model hs M (Sum.elim v a)
  simp only [SigmaOneForm.formula, Formula.realize_iExs] at he
  simp_rw [he]
  simp only [Formula.realize_relabel]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨Sum.elim a b, ?_⟩
    convert hab using 1
    funext x
    cases x with
    | inl x => cases x <;> rfl
    | inr j => rfl
  · rintro ⟨w, hw⟩
    refine ⟨fun u => w (.inl u), fun j => w (.inr j), ?_⟩
    convert hw using 1
    funext x
    cases x with
    | inl x => cases x <;> rfl
    | inr j => rfl

private theorem normalized_subst {α β : Type} [Fintype α] [Fintype β]
    (φ : language.Formula α) (hφ : SigmaOneEquivalent φ) (σ : α → language.Term β) :
    SigmaOneEquivalent (φ.subst σ) := by
  obtain ⟨s, hs⟩ := hφ
  apply normalized_of_model (φ.subst σ)
    (s.matrix.subst (underSubst σ)) (s.bounded.subst _)
  intro M v
  have he := equivalent_model hs M (fun i => (σ i).realize v)
  have hp : Formula.Realize (φ.subst σ) v ↔ φ.Realize (fun i => (σ i).realize v) := by
    simp only [Formula.Realize, BoundedFormula.realize_subst]
  rw [hp, he]
  simp only [SigmaOneForm.formula, Formula.realize_iExs]
  apply exists_congr
  intro w
  simp only [Formula.Realize, BoundedFormula.realize_subst]
  have hv : Sum.elim (fun i => (σ i).realize v) w =
      (fun a => (underSubst σ a).realize (Sum.elim v w)) := by
    funext x
    cases x with
    | inl x => simp [underSubst, Term.realize_relabel]
    | inr j => rfl
  rw [hv]

private theorem normalized_relabel {α β : Type} [Fintype α] [Fintype β]
    (φ : language.Formula α) (hφ : SigmaOneEquivalent φ) (f : α → β) :
    SigmaOneEquivalent (φ.relabel f) := by
  rw [← formula_subst_vars]
  exact normalized_subst φ hφ (fun x => .var (f x))

private theorem normalized_iInf {α β : Type} [Fintype α] [Finite β]
    (φ : β → language.Formula α) (hφ : ∀ i, SigmaOneEquivalent (φ i)) :
    SigmaOneEquivalent (Formula.iInf φ) := by
  have hl (l : List β) : SigmaOneEquivalent ((l.map φ).foldr (· ⊓ ·) ⊤) := by
    induction l with
    | nil => exact normalized_bounded _ (.imp .falsum .falsum)
    | cons i l ih => exact normalized_inf _ _ (hφ i) ih
  exact hl _

theorem sigmaOne_conjunction {k : ℕ} (φ ψ : language.Formula (Fin k))
    (hφ : SigmaOneEquivalent φ) (hψ : SigmaOneEquivalent ψ) :
    SigmaOneEquivalent (φ ⊓ ψ) := by
  exact normalized_inf φ ψ hφ hψ

theorem sigmaOne_disjunction {k : ℕ} (φ ψ : language.Formula (Fin k))
    (hφ : SigmaOneEquivalent φ) (hψ : SigmaOneEquivalent ψ) :
    SigmaOneEquivalent (φ ⊔ ψ) := by
  exact normalized_sup φ ψ hφ hψ

theorem sigmaOne_existential {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit))
    (hφ : SigmaOneEquivalent φ) : SigmaOneEquivalent (φ.iExs Unit) := by
  exact normalized_iExs φ hφ

theorem sigmaOne_bounded_existential {k : ℕ}
    (φ : language.Formula (Fin k ⊕ Unit)) (t : language.Term (Fin k))
    (hφ : SigmaOneEquivalent φ) : SigmaOneEquivalent (boundedEx t φ) := by
  apply normalized_iExs
  apply normalized_inf _ _ _ hφ
  exact normalized_bounded _ (.le _ _)

/-- The input-recursion coordinate is last, as in the entry's human convention. -/
inductive Program : ℕ → Type
  | zero : Program 0
  | succ : Program 1
  | proj {n : ℕ} (i : Fin n) : Program n
  | comp {m n : ℕ} (f : Program m) (g : Fin m → Program n) : Program n
  | prec {n : ℕ} (base : Program n) (step : Program (n + 2)) : Program (n + 1)

def Program.eval : {n : ℕ} → Program n → (Fin n → ℕ) → ℕ
  | _, .zero, _ => 0
  | _, .succ, x => x 0 + 1
  | _, .proj i, x => x i
  | _, .comp f g, x => f.eval (fun i => (g i).eval x)
  | _, .prec f g, x => primitiveRecFunction f.eval g.eval x

/-- Raw canonical graph in the shared arithmetic syntax. The recursion graph's
universal compatibility clauses normalize using PA's internal decoder theorem. -/
def Program.graph : {n : ℕ} → Program n → language.Formula (Fin n ⊕ Unit)
  | _, .zero => termGraph zeroTerm
  | _, .succ => termGraph (succTerm (.var 0))
  | _, .proj i => termGraph (.var i)
  | _, .comp f g => compositionGraph f.graph (fun i => (g i).graph)
  | _, .prec f g => recursionGraph betaGraph f.graph g.graph

/-- Every presentation has the old, genuinely weaker numeralwise Q property. -/
theorem Program.graph_numeralwise {n : ℕ} (p : Program n) :
    StronglyRepresents p.eval p.graph := by
  induction p with
  | zero => exact term_stronglyRepresents zeroTerm
  | succ => exact term_stronglyRepresents (succTerm (.var (0 : Fin 1)))
  | proj i => exact term_stronglyRepresents (.var i)
  | comp f g ihf ihg =>
    exact composition_stronglyRepresents f.eval (fun i => (g i).eval)
      f.graph (fun i => (g i).graph) ihf ihg
  | prec f g ihf ihg =>
    apply represents_primitiveRec (fun x => beta (x 0) (x 1) (x 2))
      betaGraph beta_stronglyRepresents ?_ f.eval g.eval f.graph g.graph ihf ihg
    intro k a
    obtain ⟨c, d, _, h⟩ := beta_codes_finite_tuple k a
    exact ⟨c, d, by simpa using h⟩

private theorem vector_ofFn_snoc {n : ℕ} (x : Fin n → ℕ) (a : ℕ) :
    List.Vector.ofFn (Fin.snoc x a) =
      List.Vector.ofFn x ++ a ::ᵥ List.Vector.nil := by
  apply List.Vector.toList_injective
  simp only [List.Vector.toList_ofFn, List.Vector.toList_append,
    List.Vector.toList_cons, List.Vector.toList_nil]
  rw [List.ofFn_succ']
  simp

theorem primitiveRec_lastRec {n : ℕ}
    (f : PrimitiveRecursion.Args n → ℕ) (g : PrimitiveRecursion.Args (n + 2) → ℕ)
    (x : Fin n → ℕ) (k : ℕ) :
    primitiveRec (fun v => f (List.Vector.ofFn v)) (fun v => g (List.Vector.ofFn v)) x k =
      PrimitiveRecursion.recValue f (fun v i a => g (v ++ i ::ᵥ a ::ᵥ List.Vector.nil))
        (List.Vector.ofFn x) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [primitiveRec, PrimitiveRecursion.recValue, ih, vector_ofFn_snoc]
    congr 1
    apply List.Vector.toList_injective
    simp

/-- Bridge from the corpus's existing finite-arity primitive-recursive class. -/
theorem program_of_primrec {n : ℕ} (f : PrimitiveRecursion.Args n → ℕ)
    (hf : Nat.Primrec' f) :
    ∃ p : Program n, p.eval = fun x => f (List.Vector.ofFn x) := by
  refine PrimitiveRecursion.generated_by_lastRec
    (C := fun {m} g => ∃ p : Program m,
      p.eval = fun x => g (List.Vector.ofFn x)) ?_ ?_ ?_ ?_ ?_ hf
  · exact ⟨.zero, rfl⟩
  · refine ⟨.succ, ?_⟩
    funext x
    simp [Program.eval, List.Vector.head_ofFn]
  · intro m i
    refine ⟨.proj i, ?_⟩
    funext x
    simp [Program.eval, List.Vector.get_ofFn]
  · intro m k f g hf hg
    obtain ⟨p, hp⟩ := hf
    choose q hq using hg
    refine ⟨.comp p q, ?_⟩
    funext x
    simp only [Program.eval, hp, hq]
  · intro m f g hf hg
    obtain ⟨p, hp⟩ := hf
    obtain ⟨q, hq⟩ := hg
    refine ⟨.prec p q, ?_⟩
    funext x
    simp only [Program.eval, hp, hq, primitiveRecFunction, PrimitiveRecursion.lastRec,
      PrimitiveRecursion.initialPart, List.Vector.get_ofFn, primitiveRec_lastRec]

/-- Uniform PA totality of the actual bounded beta graph. -/
theorem beta_total_unique : Derives PA (totalUnique betaGraph) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_totalUnique]
  intro x
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  let m : M := succValue M (mulValue M (succValue M (x 2)) (x 1))
  have hm : m ≠ zeroValue M := successor_ne_zero _
  obtain ⟨qr, hqr, huniq⟩ := division_model m hm (x 0)
  have hz (a : M) : (0 : M) ≤ a := zero_le_value a
  have hmone : (1 : M) ≤ m := by
    exact ⟨mulValue M (succValue M (x 2)) (x 1), add_one_value _⟩
  have hqbound : leValue M qr.1 (x 0) := by
    change qr.1 ≤ x 0
    calc
      qr.1 = 1 * qr.1 := (one_mul _).symm
      _ ≤ m * qr.1 := mul_le_mul_of_nonneg_right hmone (hz _)
      _ ≤ m * qr.1 + qr.2 := le_add_of_nonneg_right (hz _)
      _ = x 0 := hqr.1.symm
  have hgraph (y : M) : betaGraph.Realize (extend x y) ↔
      leValue M (succValue M y) m ∧ ∃ q, leValue M q (x 0) ∧
        x 0 = addValue M (mulValue M m q) y := by
    simp only [betaGraph, realize_betaFormula, Term.realize_var, extend,
      Sum.elim_inl, Sum.elim_inr, betaModulusTerm, realize_succTerm, realize_mulTerm]
    rfl
  refine ⟨qr.2, (hgraph _).mpr ⟨hqr.2, qr.1, hqbound, hqr.1⟩, ?_⟩
  intro y hy
  obtain ⟨hr, q, _, he⟩ := (hgraph y).mp hy
  exact congrArg Prod.snd (huniq (q, y) ⟨he, hr⟩)

/-- Internal append: the preserved segment ranges over all model indices below n. -/
theorem beta_extension_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (c d n a : M) :
    ∃ c' d', decodeRealizes betaGraph c' d' n a ∧
      ∀ i, leValue M (succValue M i) n → ∀ z,
        decodeRealizes betaGraph c' d' i z ↔ decodeRealizes betaGraph c d i z := by
  obtain ⟨c', d', hn, hi⟩ := beta_extension_value c d n a
  refine ⟨c', d', ?_, ?_⟩
  · change betaGraph.Realize (extend ![c', d', n] a)
    rw [betaValue_iff]
    exact hn.symm
  · intro i hin z
    change betaGraph.Realize (extend ![c', d', i] z) ↔ betaGraph.Realize (extend ![c, d, i] z)
    rw [betaValue_iff, betaValue_iff, hi i hin]

/-- Bounded witness collection for the actual formula, not an arbitrary predicate. -/
theorem bounded_witness_collection {k : ℕ} {M : Type u} [language.Structure M] [M ⊨ PA]
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit)) (x : Fin k → M) (n : M)
    (h : ∀ i, leValue M (succValue M i) n → ∃ y,
      φ.Realize (extend (extend x i) y)) :
    ∃ c d, ∀ i, leValue M (succValue M i) n → ∀ y,
      decodeRealizes betaGraph c d i y → φ.Realize (extend (extend x i) y) := by
  let : Nonempty M := ⟨zeroValue M⟩
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  have hs (a : M) : succValue M a = a + 1 := (add_one_value a).symm
  have hbeta := (realize_totalUnique (M := M) betaGraph).mp
    (derives_sound beta_total_unique default
      (fun B hB => Theory.realize_sentence_of_mem PA hB))
  let P (t : M) := leValue M t n → ∃ c d, ∀ i,
    leValue M (succValue M i) t → ∀ y,
      decodeRealizes betaGraph c d i y → φ.Realize (extend (extend x i) y)
  have hP : (Set.univ : Set M).Definable₁ language {t | P t} := by
    change DPred (fun w : Fin 1 → M => leValue M (w 0) n → ∃ c d, ∀ i,
      leValue M (succValue M i) (w 0) → ∀ y,
        decodeRealizes betaGraph c d i y → φ.Realize (extend (extend x i) y))
    apply dp_imp
    · apply dp_le <;> fun_prop
    · apply dp_exists
      apply dp_exists
      apply dp_forall
      apply dp_imp
      · apply dp_le <;> fun_prop
      · apply dp_forall
        apply dp_imp
        · apply dp_decode <;> fun_prop
        · apply dp_formula φ
          intro j
          cases j with
          | inl j =>
            cases j <;>
              simp only [extend, Sum.elim_inl, Sum.elim_inr, Function.comp_def] <;> fun_prop
          | inr j =>
            simp only [extend, Sum.elim_inr]
            fun_prop
  have hz : P (zeroValue M) := by
    intro _
    refine ⟨zeroValue M, zeroValue M, ?_⟩
    intro i hi
    exact False.elim (successor_ne_zero i
      (le_antisymm hi (zero_le_value (succValue M i))))
  have hstep : ∀ t, P t → P (succValue M t) := by
    intro t ih ht
    obtain ⟨c, d, hcd⟩ := ih (le_trans_value (le_successor_value t) ht)
    obtain ⟨a, ha⟩ := h t ht
    obtain ⟨c', d', hnew, hpres⟩ := beta_extension_model c d t a
    refine ⟨c', d', ?_⟩
    intro i hi y hy
    have hit : i ≤ t := by
      change succValue M i ≤ succValue M t at hi
      simpa only [hs, add_le_add_iff_right] using hi
    rcases lt_or_eq_of_le hit with hlt | heq
    · have hstrict := (successor_le_iff_lt i t).mpr hlt
      exact hcd i hstrict y ((hpres i hstrict y).mp hy)
    · subst i
      have he : y = a := (hbeta ![c', d', t]).unique hy hnew
      simpa only [he] using ha
  exact definable_induction P hP hz hstep n (le_refl n)

private theorem collection_finite_parameters {α : Type} [Fintype α]
    (M : Theory.ModelType.{0,0,0} PA) (A : language.Formula ((α ⊕ Unit) ⊕ Unit))
    (v : α → M) (n : M)
    (h : ∀ i, leValue M (succValue M i) n → ∃ u,
      A.Realize (extend (extend v i) u)) :
    ∃ c d, ∀ i, leValue M (succValue M i) n → ∀ u,
      decodeRealizes betaGraph c d i u → A.Realize (extend (extend v i) u) := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let f : (α ⊕ Unit) ⊕ Unit → (Fin (Fintype.card α) ⊕ Unit) ⊕ Unit :=
    Sum.map (Sum.map e id) id
  let x : Fin (Fintype.card α) → M := fun j => v (e.symm j)
  have hr (i u : M) : (A.relabel f).Realize (extend (extend x i) u) ↔
      A.Realize (extend (extend v i) u) := by
    rw [Formula.realize_relabel]
    have hv : extend (extend x i) u ∘ f = extend (extend v i) u := by
      funext z
      cases z with
      | inl z => cases z <;> simp [f, x, extend]
      | inr z => rfl
    rw [hv]
  obtain ⟨c, d, hcd⟩ := bounded_witness_collection (A.relabel f) x n (by
    intro i hi
    obtain ⟨u, hu⟩ := h i hi
    exact ⟨u, (hr i u).mpr hu⟩)
  exact ⟨c, d, fun i hi u hu => (hr i u).mp (hcd i hi u hu)⟩

private theorem successor_le_successor {M : Type u} [language.Structure M] [M ⊨ PA]
    (a b : M) : leValue M (succValue M a) (succValue M b) ↔ leValue M a b := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, successor_injective (by simpa only [add_successor_value] using hd)⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, by rw [add_successor_value, hd]⟩

private theorem normalized_bounded_all {α : Type} [Fintype α]
    (φ : language.Formula (α ⊕ Unit)) (t : language.Term α)
    (hφ : SigmaOneEquivalent φ) : SigmaOneEquivalent (boundedAll t φ) := by
  obtain ⟨s, hs⟩ := hφ
  let A : language.Formula ((α ⊕ Unit) ⊕ Unit) :=
    boundedTupleEx (.var (.inr ())) s.witnesses (s.matrix.relabel (Sum.map Sum.inl id))
  have hA : DeltaZero A := boundedTupleEx_bounded _ _ (s.bounded.relabel _)
  let swap : (α ⊕ Unit) ⊕ Unit → (α ⊕ Unit) ⊕ Unit :=
    Sum.elim (Sum.elim (fun x => .inl (.inl x)) Sum.inr) (fun u => .inl (.inr u))
  let δ : language.Formula (α ⊕ Unit) :=
    boundedAll (t.relabel Sum.inl) (A.relabel swap)
  apply normalized_of_model (boundedAll t φ) δ (.all _ (hA.relabel _))
  intro M v
  let := modelLinearOrder M
  have ha (i u : M) : A.Realize (extend (extend v i) u) ↔
      ∃ w : Fin s.witnesses → M, (∀ j, leValue M (w j) u) ∧
        s.matrix.Realize (Sum.elim (extend v i) w) := by
    dsimp only [A]
    rw [realize_boundedTupleEx]
    simp only [Term.realize_var, extend, Sum.elim_inr, Formula.realize_relabel]
    apply exists_congr
    intro w
    apply and_congr_right
    intro _
    have hv : Sum.elim (extend (extend v i) u) w ∘
        Sum.map (Sum.inl : α ⊕ Unit → (α ⊕ Unit) ⊕ Unit) id =
        Sum.elim (extend v i) w := by
      funext z
      cases z <;> rfl
    simp only [extend] at hv
    rw [hv]
  have hδ (u : Unit → M) : δ.Realize (Sum.elim v u) ↔
      ∀ i, leValue M i (t.realize v) →
        ∃ w : Fin s.witnesses → M, (∀ j, leValue M (w j) (u ())) ∧
          s.matrix.Realize (Sum.elim (extend v i) w) := by
    dsimp only [δ]
    rw [realize_boundedAll]
    simp only [Term.realize_relabel, Function.comp_def, Sum.elim_inl]
    apply forall_congr'
    intro i
    apply imp_congr_right
    intro _
    rw [Formula.realize_relabel]
    have hv : extend (Sum.elim v u) i ∘ swap = extend (extend v i) (u ()) := by
      funext z
      cases z with
      | inl z => cases z with
        | inl x => rfl
        | inr z => cases z; rfl
      | inr z => cases z; rfl
    rw [hv, ha]
  rw [realize_boundedAll]
  constructor
  · intro h
    have hw (i : M) (hi : leValue M i (t.realize v)) :
        ∃ w : Fin s.witnesses → M, s.matrix.Realize (Sum.elim (extend v i) w) := by
      have he := (equivalent_model hs M (extend v i)).mp (h i hi)
      exact Formula.realize_iExs.mp he
    obtain ⟨c, d, hcd⟩ := collection_finite_parameters M A v
      (succValue M (t.realize v)) (by
        intro i hi
        obtain ⟨w, hw'⟩ := hw i ((successor_le_successor i _).mp hi)
        obtain ⟨u, hu⟩ := (Set.finite_range w).bddAbove
        refine ⟨u, (ha i u).mpr ⟨w, ?_, hw'⟩⟩
        intro j
        exact hu (Set.mem_range_self j))
    refine ⟨fun _ => c, (hδ _).mpr ?_⟩
    intro i hi
    have hb := hcd i ((successor_le_successor i _).mpr hi)
      (betaValue ![c, d, i]) (betaValue_graph ![c, d, i])
    obtain ⟨w, hw', hmatrix⟩ := (ha i _).mp hb
    exact ⟨w, fun j => le_trans_value (hw' j) (betaValue_le c d i), hmatrix⟩
  · rintro ⟨u, hu⟩ i hi
    obtain ⟨w, _, hw⟩ := (hδ u).mp hu i hi
    apply (equivalent_model hs M (extend v i)).mpr
    exact Formula.realize_iExs.mpr ⟨w, hw⟩

theorem sigmaOne_bounded_universal {k : ℕ}
    (φ : language.Formula (Fin k ⊕ Unit)) (t : language.Term (Fin k))
    (hφ : SigmaOneEquivalent φ) : SigmaOneEquivalent (boundedAll t φ) := by
  exact normalized_bounded_all φ t hφ

private theorem normalized_tuple_all {α : Type} [Fintype α] (t : language.Term α)
    (k : ℕ) (φ : language.Formula (α ⊕ Fin k)) (hφ : SigmaOneEquivalent φ) :
    SigmaOneEquivalent (boundedTupleAll t k φ) := by
  induction k generalizing α with
  | zero =>
    let f : α ⊕ Fin 0 → α := Sum.elim id Fin.elim0
    apply normalized_transfer _ (φ.relabel f) (normalized_relabel φ hφ f)
    intro M v
    rw [realize_boundedTupleAll, Formula.realize_relabel]
    constructor
    · intro h
      convert h Fin.elim0 (fun j => j.elim0) using 1
      funext z
      cases z with
      | inl z => rfl
      | inr j => exact j.elim0
    · intro h w _
      convert h using 1
      funext z
      cases z with
      | inl z => rfl
      | inr j => exact j.elim0
  | succ k ih =>
    let f : α ⊕ Fin (k + 1) → (α ⊕ Unit) ⊕ Fin k :=
      Sum.elim (fun a => .inl (.inl a))
        (Fin.cases (.inl (.inr ())) (fun j => .inr j))
    let ψ := boundedTupleAll (t.relabel Sum.inl) k (φ.relabel f)
    have hψ := ih (t.relabel Sum.inl) (φ.relabel f) (normalized_relabel φ hφ f)
    apply normalized_transfer _ (boundedAll t ψ) (normalized_bounded_all ψ t hψ)
    intro M v
    rw [realize_boundedTupleAll, realize_boundedAll]
    simp only [ψ, realize_boundedTupleAll, Formula.realize_relabel,
      Term.realize_relabel, Function.comp_def, extend, Sum.elim_inl]
    constructor
    · intro h a ha w hw
      convert h (Fin.cons a w) (fun j => Fin.cases ha (fun j => hw j) j) using 1
      funext z
      cases z with
      | inl z => rfl
      | inr j => refine Fin.cases rfl (fun j => rfl) j
    · intro h w hw
      convert h (w 0) (hw 0) (fun j => w j.succ) (fun j => hw j.succ) using 1
      funext z
      cases z with
      | inl z => rfl
      | inr j => refine Fin.cases rfl (fun j => rfl) j

private theorem normalized_forall_bounded {α β : Type} [Fintype α] [Fintype β]
    (φ : language.Formula (α ⊕ β)) (t : language.Term α) (hφ : SigmaOneEquivalent φ)
    (hout : ∀ (M : Theory.ModelType.{0,0,0} PA) (v : α → M) (w : β → M),
      (¬ ∀ j, leValue M (w j) (t.realize v)) → φ.Realize (Sum.elim v w)) :
    SigmaOneEquivalent (φ.iAlls β) := by
  let e : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
  let f : α ⊕ β → α ⊕ Fin (Fintype.card β) := Sum.map id e
  let ψ := boundedTupleAll t (Fintype.card β) (φ.relabel f)
  have hψ := normalized_tuple_all t _ _ (normalized_relabel φ hφ f)
  apply normalized_transfer _ ψ hψ
  intro M v
  rw [Formula.realize_iAlls]
  simp only [ψ, realize_boundedTupleAll, Formula.realize_relabel]
  constructor
  · intro h w _
    convert h (fun j => w (e j)) using 1
    funext z
    cases z <;> rfl
  · intro h w
    by_cases hw : ∀ j, leValue M (w j) (t.realize v)
    · convert h (fun j => w (e.symm j)) (fun j => hw (e.symm j)) using 1
      funext z
      cases z <;> simp [f]
    · exact hout M v w hw

private theorem normalized_imp_bounded {α : Type} [Fintype α]
    (δ φ : language.Formula α) (hδ : DeltaZero δ) (hφ : SigmaOneEquivalent φ) :
    SigmaOneEquivalent (δ.imp φ) := by
  apply normalized_transfer _ (δ.not ⊔ φ)
    (normalized_sup _ _ (normalized_bounded _ (.imp hδ .falsum)) hφ)
  intro M v
  simp only [Formula.realize_imp, Formula.realize_sup, Formula.realize_not]
  tauto

private theorem normalized_strictAll {α : Type} [Fintype α]
    (φ : language.Formula (α ⊕ Unit)) (t : language.Term α)
    (hφ : SigmaOneEquivalent φ) : SigmaOneEquivalent (strictAll t φ) := by
  let δ := ltFormula (.var (.inr ())) (t.relabel Sum.inl)
  have hδ : DeltaZero δ := .le _ _
  have hχ := normalized_bounded_all (δ.imp φ) t (normalized_imp_bounded δ φ hδ hφ)
  apply normalized_transfer _ (boundedAll t (δ.imp φ)) hχ
  intro M v
  simp only [strictAll, Formula.realize_iAlls, Formula.realize_imp,
    realize_boundedAll, δ, ltFormula, realize_leFormula, realize_succTerm,
    Term.realize_var, Term.realize_relabel, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr]
  constructor
  · intro h i _ hi
    exact h (fun _ => i) hi
  · intro h w hw
    have hi := h (w ()) (le_trans_value (le_successor_value _) hw) hw
    convert hi using 1
    funext z
    cases z with
    | inl z => rfl
    | inr z => cases z; rfl

private theorem beta_graph_bound {M : Type u} [language.Structure M] [M ⊨ PA]
    (x : Fin 3 → M) (y : M) (hy : betaGraph.Realize (extend x y)) : leValue M y (x 0) := by
  have hx : x = ![x 0, x 1, x 2] := by
    funext j
    fin_cases j <;> rfl
  rw [hx] at hy
  rw [(betaValue_iff _ _).mp hy]
  exact betaValue_le _ _ _

theorem recursion_total_unique {n : ℕ}
    (base : language.Formula (Fin n ⊕ Unit))
    (step : language.Formula (Fin (n + 2) ⊕ Unit))
    (hbase : Derives PA (totalUnique base)) (hstep : Derives PA (totalUnique step)) :
    Derives PA (totalUnique (recursionGraph betaGraph base step)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_totalUnique]
  intro x
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have hs (a : M) : succValue M a = a + 1 := (add_one_value a).symm
  have hmono {a b : M} (h : leValue M a b) :
      leValue M (succValue M a) (succValue M b) := by
    change succValue M a ≤ succValue M b
    rw [hs, hs]
    change a ≤ b at h
    simpa only [add_comm] using (_root_.add_le_add_right h (1 : M))
  have hbaseM := (realize_totalUnique (M := M) base).mp
    (derives_sound hbase default (fun B hB => Theory.realize_sentence_of_mem PA hB))
  have hstepM := (realize_totalUnique (M := M) step).mp
    (derives_sound hstep default (fun B hB => Theory.realize_sentence_of_mem PA hB))
  have hbeta := (realize_totalUnique (M := M) betaGraph).mp
    (derives_sound beta_total_unique default
      (fun B hB => Theory.realize_sentence_of_mem PA hB))
  have hb (c d i : M) : ∃! z, decodeRealizes betaGraph c d i z := hbeta ![c, d, i]
  let xs : Fin n → M := fun i => x i.castSucc
  let k : M := x (Fin.last n)
  have hx : Fin.snoc xs k = x := Fin.snoc_init_self x
  rw [← hx]
  let R := recursionGraph betaGraph base step
  let P (t : M) := ∃ y, R.Realize (extend (Fin.snoc xs t) y)
  have hP : (Set.univ : Set M).Definable₁ language {t | P t} := by
    change DPred (fun w : Fin 1 → M => ∃ y,
      R.Realize (extend (Fin.snoc xs (w 0)) y))
    apply dp_exists
    apply dp_formula R
      (fun w : Fin 1 ⊕ Unit → M => extend (Fin.snoc xs (w (.inl 0))) (w (.inr ())))
    intro j
    cases j with
    | inl j =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [extend, Sum.elim_inl, Fin.snoc_last] using
          (df_proj (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Unit) : Set.univ.DefinableFun language
            (fun w : Fin 1 ⊕ Unit → M => w (.inl 0)))
      · simpa only [extend, Sum.elim_inl, Fin.snoc_castSucc] using
          (df_const (xs i) : Set.univ.DefinableFun language
            (fun _ : Fin 1 ⊕ Unit → M => xs i))
    | inr j => exact df_proj (Sum.inr () : Fin 1 ⊕ Unit)
  have hz : P (zeroValue M) := by
    obtain ⟨a, ha, _⟩ := hbaseM xs
    obtain ⟨c, d, hnew, _⟩ := beta_extension_model
      (zeroValue M) (zeroValue M) (zeroValue M) a
    refine ⟨a, (realize_recursionGraph _ _ _ _ _ _).mpr ⟨![c, d], ?_, ?_, ?_, hnew⟩⟩
    · intro u hu
      have he : u = a := (hb c d (zeroValue M)).unique hu hnew
      simpa only [he] using ha
    · intro i hi
      have he : i = zeroValue M := le_antisymm hi (zero_le_value i)
      subst i
      exact ⟨a, hnew⟩
    · intro i hi
      exact False.elim (successor_ne_zero i
        (le_antisymm hi (zero_le_value (succValue M i))))
  have hsucc : ∀ t, P t → P (succValue M t) := by
    intro t ht
    obtain ⟨y, hy⟩ := ht
    obtain ⟨cd, h0, _, hnext, hend⟩ := (realize_recursionGraph _ _ _ _ _ _).mp hy
    obtain ⟨z, hz, _⟩ := hstepM (Fin.snoc (Fin.snoc xs t) y)
    obtain ⟨c, d, hnew, hpres⟩ := beta_extension_model (cd 0) (cd 1) (succValue M t) z
    refine ⟨z, (realize_recursionGraph _ _ _ _ _ _).mpr ⟨![c, d], ?_, ?_, ?_, hnew⟩⟩
    · intro u hu
      exact h0 u ((hpres (zeroValue M) (hmono (zero_le_value t)) u).mp hu)
    · intro i _
      exact (hb c d i).exists
    · intro i hi u v hu hv
      have hit : i ≤ t := by
        change succValue M i ≤ succValue M t at hi
        simpa only [hs, add_le_add_iff_right] using hi
      rcases lt_or_eq_of_le hit with hlt | heq
      · have hstrict := (successor_le_iff_lt i t).mpr hlt
        exact hnext i hstrict u v
          ((hpres i (hmono hit) u).mp hu)
          ((hpres (succValue M i) (hmono hstrict) v).mp hv)
      · subst i
        have he : u = y := (hb (cd 0) (cd 1) t).unique
          ((hpres t (hmono (le_refl t)) u).mp hu) hend
        have hf : v = z := (hb c d (succValue M t)).unique hv hnew
        simpa only [he, hf] using hz
  obtain ⟨y, hy⟩ := definable_induction P hP hz hsucc k
  refine ⟨y, hy, ?_⟩
  intro y' hy'
  obtain ⟨cd, h0, _, hn, he⟩ := (realize_recursionGraph _ _ _ _ _ _).mp hy'
  obtain ⟨cd', h0', _, hn', he'⟩ := (realize_recursionGraph _ _ _ _ _ _).mp hy
  let C (i : M) := leValue M i k → ∀ u v,
    decodeRealizes betaGraph (cd 0) (cd 1) i u →
    decodeRealizes betaGraph (cd' 0) (cd' 1) i v → u = v
  have hC : (Set.univ : Set M).Definable₁ language {i | C i} := by
    change DPred (fun w : Fin 1 → M => leValue M (w 0) k → ∀ u v,
      decodeRealizes betaGraph (cd 0) (cd 1) (w 0) u →
      decodeRealizes betaGraph (cd' 0) (cd' 1) (w 0) v → u = v)
    apply dp_imp
    · apply dp_le <;> fun_prop
    · apply dp_forall
      apply dp_forall
      apply dp_imp
      · apply dp_decode <;> fun_prop
      · apply dp_imp
        · apply dp_decode <;> fun_prop
        · apply dp_eq <;> fun_prop
  have hc0 : C (zeroValue M) := by
    intro _ u v hu hv
    exact (hbaseM xs).unique (h0 u hu) (h0' v hv)
  have hcs : ∀ i, C i → C (succValue M i) := by
    intro i ih hi u v hu hv
    obtain ⟨a, ha, _⟩ := hb (cd 0) (cd 1) i
    obtain ⟨b, hb', _⟩ := hb (cd' 0) (cd' 1) i
    have hab : a = b := ih (le_trans_value (le_successor_value i) hi) a b ha hb'
    have hu' := hn i hi a u ha hu
    have hv' := hn' i hi b v hb' hv
    exact (hstepM (Fin.snoc (Fin.snoc xs i) a)).unique hu' (by simpa only [hab] using hv')
  exact definable_induction C hC hc0 hcs k (le_refl k) y' y he he'

theorem recursion_sigmaOne {n : ℕ}
    (base : language.Formula (Fin n ⊕ Unit))
    (step : language.Formula (Fin (n + 2) ⊕ Unit))
    (hbase : SigmaOneEquivalent base) (hstep : SigmaOneEquivalent step) :
    SigmaOneEquivalent (recursionGraph betaGraph base step) := by
  have hβ : DeltaZero betaGraph := deltaZero_betaFormula _ _ _ _
  unfold recursionGraph
  apply normalized_iExs
  apply normalized_inf
  · apply normalized_forall_bounded _ (.var (.inr 0))
    · apply normalized_imp_bounded
      · exact hβ.subst _
      · exact normalized_subst _ hbase _
    · intro M v w hw hb
      apply False.elim (hw ?_)
      intro j
      cases j
      have hbound := beta_graph_bound _ _ ((realize_graphAt _ _ _ _).mp hb)
      simpa only [Term.realize_var, Term.realize_relabel, Function.comp_def,
        Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero] using hbound
  · apply normalized_inf
    · apply normalized_bounded_all
      apply normalized_iExs
      exact normalized_bounded _ (hβ.subst _)
    · apply normalized_inf
      · apply normalized_strictAll
        apply normalized_forall_bounded _ (.var (.inl (.inr 0)))
        · apply normalized_imp_bounded
          · exact deltaZero_inf (hβ.subst _) (hβ.subst _)
          · exact normalized_subst _ hstep _
        · intro M v w hw hb
          apply False.elim (hw ?_)
          have hb' := Formula.realize_inf.mp hb
          have h0 := beta_graph_bound _ _ ((realize_graphAt _ _ _ _).mp hb'.1)
          have h1 := beta_graph_bound _ _ ((realize_graphAt _ _ _ _).mp hb'.2)
          intro j
          fin_cases j
          · convert h0 using 2 <;>
              simp [Term.realize_var]
          · convert h1 using 2 <;>
              simp [Term.realize_var]
      · exact normalized_bounded _ (hβ.subst _)

/-- Uniform totality for the specified canonical graph. -/
theorem Program.graph_total_unique {n : ℕ} (p : Program n) :
    Derives PA (totalUnique p.graph) := by
  have ht {m : ℕ} (t : language.Term (Fin m)) :
      Derives PA (totalUnique (termGraph t)) := by
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    rw [realize_totalUnique]
    intro x
    simp only [termGraph, Formula.realize_equal, Term.realize_var,
      Term.realize_relabel, Function.comp_def, extend, Sum.elim_inl, Sum.elim_inr]
    exact ⟨t.realize x, rfl, fun _ h => h⟩
  induction p with
  | zero => exact ht zeroTerm
  | succ => exact ht (succTerm (.var 0))
  | proj i => exact ht (.var i)
  | comp f g ihf ihg =>
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    rw [realize_totalUnique]
    intro x
    have hf := (realize_totalUnique (M := M) f.graph).mp
      (derives_sound ihf default (fun B hB => Theory.realize_sentence_of_mem PA hB))
    have hg i := (realize_totalUnique (M := M) (g i).graph).mp
      (derives_sound (ihg i) default (fun B hB => Theory.realize_sentence_of_mem PA hB)) x
    choose z hz hu using hg
    obtain ⟨y, hy, hyu⟩ := hf z
    refine ⟨y, (realize_compositionGraph _ _ _ _).mpr ⟨z, hz, hy⟩, ?_⟩
    intro y' hy'
    obtain ⟨z', hz', hh⟩ := (realize_compositionGraph _ _ _ _).mp hy'
    have he : z' = z := funext (fun i => hu i (z' i) (hz' i))
    subst z'
    exact hyu y' hh
  | prec f g ihf ihg => exact recursion_total_unique f.graph g.graph ihf ihg

/-- PA-equivalent normalization to a literal existential prefix and bounded matrix. -/
theorem Program.graph_sigmaOne {n : ℕ} (p : Program n) :
    SigmaOneEquivalent (α := Fin n ⊕ Unit) p.graph := by
  induction p with
  | zero => exact normalized_bounded _ (.equal _ _)
  | succ => exact normalized_bounded _ (.equal _ _)
  | proj i => exact normalized_bounded _ (.equal _ _)
  | comp f g ihf ihg =>
    change SigmaOneEquivalent (compositionGraph f.graph (fun i => (g i).graph))
    unfold compositionGraph
    apply normalized_iExs
    apply normalized_inf
    · apply normalized_iInf
      intro i
      exact normalized_subst _ (ihg i) _
    · exact normalized_subst _ ihf _
  | prec f g ihf ihg => exact recursion_sigmaOne f.graph g.graph ihf ihg

/-- The normalized graph is chosen together with a PA proof identifying it with
the specific raw canonical graph. It is not an arbitrary numeralwise choice. -/
def Program.sigmaForm {n : ℕ} (p : Program n) : SigmaOneForm (Fin n ⊕ Unit) :=
  Classical.choose p.graph_sigmaOne

def Program.sigmaGraph {n : ℕ} (p : Program n) : language.Formula (Fin n ⊕ Unit) :=
  p.sigmaForm.formula

theorem Program.sigmaGraph_equivalent {n : ℕ} (p : Program n) :
    PAEquivalent (α := Fin n ⊕ Unit) p.graph p.sigmaGraph := Classical.choose_spec p.graph_sigmaOne

theorem Program.sigmaGraph_isSigmaOne {n : ℕ} (p : Program n) :
    SigmaOne p.sigmaGraph := p.sigmaForm.isSigmaOne

/-- Defining equations for the finite-history graph of arbitrary ingredient
formulas, including nonstandard recursion indices. -/
theorem recursion_equations_model {n : ℕ}
    (base : language.Formula (Fin n ⊕ Unit))
    (step : language.Formula (Fin (n + 2) ⊕ Unit))
    {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin n → M) (k y : M) :
    ((recursionGraph betaGraph base step).Realize (extend (Fin.snoc x (zeroValue M)) y) ↔
      base.Realize (extend x y)) ∧
    ((recursionGraph betaGraph base step).Realize (extend (Fin.snoc x (succValue M k)) y) ↔
      ∃ a : M, (recursionGraph betaGraph base step).Realize (extend (Fin.snoc x k) a) ∧
        step.Realize (extend (Fin.snoc (Fin.snoc x k) a) y)) := by
  let : Nonempty M := ⟨zeroValue M⟩
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  have hs (a : M) : succValue M a = a + 1 := (add_one_value a).symm
  have hmono {a b : M} (h : leValue M a b) :
      leValue M (succValue M a) (succValue M b) := by
    change a ≤ b at h
    change succValue M a ≤ succValue M b
    rw [hs, hs]
    simpa only [add_comm] using (_root_.add_le_add_right h (1 : M))
  have hbeta := (realize_totalUnique (M := M) betaGraph).mp
    (derives_sound beta_total_unique default
      (fun B hB => Theory.realize_sentence_of_mem PA hB))
  have hb (c d i : M) : ∃! z, decodeRealizes betaGraph c d i z := hbeta ![c, d, i]
  constructor
  · rw [realize_recursionGraph]
    constructor
    · rintro ⟨cd, h0, _, _, he⟩
      exact h0 y he
    · intro hy
      obtain ⟨c, d, hnew, _⟩ := beta_extension_model
        (zeroValue M) (zeroValue M) (zeroValue M) y
      refine ⟨![c, d], ?_, ?_, ?_, hnew⟩
      · intro u hu
        have he : u = y := (hb c d (zeroValue M)).unique hu hnew
        simpa only [he] using hy
      · intro i _
        exact (hb c d i).exists
      · intro i hi
        exact False.elim (successor_ne_zero i
          (le_antisymm hi (zero_le_value (succValue M i))))
  · constructor
    · intro hy
      obtain ⟨cd, h0, _, hn, he⟩ := (realize_recursionGraph _ _ _ _ _ _).mp hy
      obtain ⟨a, ha, _⟩ := hb (cd 0) (cd 1) k
      refine ⟨a, (realize_recursionGraph _ _ _ _ _ _).mpr
        ⟨cd, h0, (fun i _ => (hb (cd 0) (cd 1) i).exists), ?_, ha⟩, ?_⟩
      · intro i hi
        exact hn i (le_trans_value hi (le_successor_value k))
      · exact hn k (le_refl_value _) a y ha he
    · rintro ⟨a, ha, hg⟩
      obtain ⟨cd, h0, _, hn, he⟩ := (realize_recursionGraph _ _ _ _ _ _).mp ha
      obtain ⟨c, d, hnew, hpres⟩ := beta_extension_model (cd 0) (cd 1) (succValue M k) y
      apply (realize_recursionGraph _ _ _ _ _ _).mpr
      refine ⟨![c, d], ?_, (fun i _ => (hb c d i).exists), ?_, hnew⟩
      · intro u hu
        exact h0 u ((hpres (zeroValue M) (hmono (zero_le_value k)) u).mp hu)
      · intro i hi u v hu hv
        have hik : i ≤ k := by
          change succValue M i ≤ succValue M k at hi
          simpa only [hs, add_le_add_iff_right] using hi
        rcases lt_or_eq_of_le hik with hlt | heq
        · have hstrict := (successor_le_iff_lt i k).mpr hlt
          exact hn i hstrict u v
            ((hpres i (hmono hik) u).mp hu)
            ((hpres (succValue M i) (hmono hstrict) v).mp hv)
        · subst i
          have hu' : u = a := (hb (cd 0) (cd 1) k).unique
            ((hpres k (hmono (le_refl k)) u).mp hu) he
          have hv' : v = y := (hb c d (succValue M k)).unique hv hnew
          simpa only [hu', hv'] using hg

/-- Specialization to ingredient graphs of primitive-recursive programs. -/
theorem Program.recursion_equations {n : ℕ} (f : Program n) (g : Program (n + 2))
    {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin n → M) (k y : M) :
    ((Program.prec f g).graph.Realize (extend (Fin.snoc x (zeroValue M)) y) ↔
      f.graph.Realize (extend x y)) ∧
    ((Program.prec f g).graph.Realize (extend (Fin.snoc x (succValue M k)) y) ↔
      ∃ a : M, (Program.prec f g).graph.Realize (extend (Fin.snoc x k) a) ∧
        g.graph.Realize (extend (Fin.snoc (Fin.snoc x k) a) y)) :=
  recursion_equations_model f.graph g.graph x k y

/-- The main theorem concerns a literal Sigma-one graph for every actual program. -/
theorem Program.uniform_sigmaOne {n : ℕ} (p : Program n) :
    SigmaOne p.sigmaGraph ∧ UniformlyRepresents p.eval p.sigmaGraph := by
  refine ⟨p.sigmaGraph_isSigmaOne, ?_, ?_⟩
  · intro x y
    let : ℕ ⊨ Q := nat_models_Q
    have hr : p.graph.Realize (extend x y) ↔ y = p.eval x := by
      simpa only [numeral_value_nat] using
        (stronglyRepresents_modelwise p.graph_numeralwise (M := ℕ) x y)
    let : ℕ ⊨ PA := nat_models_PA
    have he' := equivalent_model p.sigmaGraph_equivalent
      (Theory.ModelType.of PA ℕ) (extend x y)
    exact he'.symm.trans hr
  · apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    rw [realize_totalUnique]
    have ht := (realize_totalUnique (M := M) p.graph).mp
      (derives_sound p.graph_total_unique default
        (fun B hB => Theory.realize_sentence_of_mem PA hB))
    intro x
    obtain ⟨y, hy, hu⟩ := ht x
    refine ⟨y, (equivalent_model p.sigmaGraph_equivalent M _).mp hy, ?_⟩
    intro y' hy'
    exact hu y' ((equivalent_model p.sigmaGraph_equivalent M _).mpr hy')

/-- Arity-independent bridge for all existing primitive-recursive numerical operations. -/
theorem primitive_recursive_uniform {n : ℕ} (f : PrimitiveRecursion.Args n → ℕ)
    (hf : Nat.Primrec' f) :
    ∃ p : Program n, p.eval = (fun x => f (List.Vector.ofFn x)) ∧
      SigmaOne p.sigmaGraph ∧ UniformlyRepresents p.eval p.sigmaGraph := by
  obtain ⟨p, hp⟩ := program_of_primrec f hf
  exact ⟨p, hp, p.uniform_sigmaOne⟩

/-- Congruence of the raw recursion-graph constructor under equivalence of its
ingredient graphs. The arbitrary-graph induction theorem is stated separately
in `PARecursionComparison`. -/
theorem recursion_graphs_comparison {n : ℕ}
    {M : Type u} [language.Structure M] [M ⊨ PA]
    (f₁ f₂ : Program n) (g₁ g₂ : Program (n + 2))
    (hf : ∀ (x : Fin n → M) (y : M), f₁.graph.Realize (extend x y) ↔ f₂.graph.Realize (extend x y))
    (hg : ∀ (x : Fin (n + 2) → M) (y : M), g₁.graph.Realize (extend x y) ↔ g₂.graph.Realize (extend x y)) :
    ∀ (x : Fin (n + 1) → M) (y : M), (Program.prec f₁ g₁).graph.Realize (extend x y) ↔
      (Program.prec f₂ g₂).graph.Realize (extend x y) := by
  intro x y
  have hx : Fin.snoc (fun i => x i.castSucc) (x (Fin.last n)) = x := Fin.snoc_init_self x
  rw [← hx]
  simp only [Program.graph, realize_recursionGraph, hf, hg]

end
end Lemmatheca.MathematicalLogic.PAComputations
