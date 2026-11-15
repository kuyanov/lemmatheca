import Lemmatheca.FiniteDimensionalFirstOrderInterpretations.Core
import Lemmatheca.EqualityAxioms.EqualityAxioms

namespace Lemmatheca.MathematicalLogic.QuotientInterpretations
open FirstOrder FirstOrder.Language
universe u v u' v' w z
noncomputable section
variable {L : Language.{u,v}} {K : Language.{u',v'}} {d : ℕ} {α : Type z}

/-- Syntactic tuple data over the actual equality-expanded source language. -/
structure InterpretationData (L : Language.{u,v}) (K : Language.{u',v'}) (d : ℕ) where
  tuple : FiniteDimensionalInterpretations.InterpretationData (EqualityAxioms.Extended L) K d

namespace InterpretationData
variable (I : InterpretationData L K d)

def equalityFormula : K.Formula (Fin 2 × Fin d) := I.tuple.relationFormula (.inr .equality)

abbrev Domain (M : Type w) [K.Structure M] := I.tuple.Domain M
abbrev coordinates (M : Type w) [K.Structure M] (v : α → I.Domain M) :=
  I.tuple.coordinates M v

variable (M : Type w) [K.Structure M]

def E (a b : I.Domain M) : Prop :=
  I.equalityFormula.Realize (I.coordinates M ![a,b])

def Graph {n : ℕ} (f : L.Functions n) (a : Fin n → I.Domain M) (y : I.Domain M) : Prop :=
  (I.tuple.functionGraph f).Realize (Sum.elim (I.coordinates M a) y.val)

def Relation {n : ℕ} (R : L.Relations n) (a : Fin n → I.Domain M) : Prop :=
  (I.tuple.relationFormula (.inl R)).Realize (I.coordinates M a)

/-- All conditions concern actual selected tuples; graph outputs are unique only modulo E. -/
structure Good : Prop where
  nonempty : Nonempty (I.Domain M)
  reflexive : ∀ a, I.E M a a
  symmetric : ∀ {a b}, I.E M a b → I.E M b a
  transitive : ∀ {a b c}, I.E M a b → I.E M b c → I.E M a c
  total : ∀ n (f : L.Functions n) (a : Fin n → I.Domain M), ∃ y, I.Graph M f a y
  unique : ∀ n (f : L.Functions n) (a : Fin n → I.Domain M) (y z : I.Domain M),
    I.Graph M f a y → I.Graph M f a z → I.E M y z
  graphs : ∀ n (f : L.Functions n) (a b : Fin n → I.Domain M) (y z : I.Domain M),
    (∀ i, I.E M (a i) (b i)) → I.E M y z →
      (I.Graph M f a y ↔ I.Graph M f b z)
  relations : ∀ n (R : L.Relations n) (a b : Fin n → I.Domain M),
    (∀ i, I.E M (a i) (b i)) → (I.Relation M R a ↔ I.Relation M R b)

variable {M}

theorem graph_iff_guarded {n : ℕ} (f : L.Functions n)
    (a : Fin n → I.Domain M) (y : I.Domain M) :
    I.Graph M f a y ↔
      (I.tuple.guardedGraph f).Realize (Sum.elim (I.coordinates M a) y.val) := by
  simp only [FiniteDimensionalInterpretations.InterpretationData.guardedGraph,
    Formula.realize_inf, Formula.realize_relabel, Sum.elim_comp_inr]
  exact ⟨fun h => ⟨y.property, h⟩, fun h => h.2⟩

theorem equivalence_congr (h : I.Good M) {a a' b b' : I.Domain M}
    (ha : I.E M a a') (hb : I.E M b b') : I.E M a b ↔ I.E M a' b' := by
  constructor
  · intro hab
    exact h.transitive (h.symmetric ha) (h.transitive hab hb)
  · intro hab
    exact h.transitive ha (h.transitive hab (h.symmetric hb))

theorem graph_output_congr (h : I.Good M) {n : ℕ} (f : L.Functions n)
    (a b : Fin n → I.Domain M) (y z : I.Domain M)
    (hab : ∀ i, I.E M (a i) (b i)) (hy : I.Graph M f a y) (hz : I.Graph M f b z) :
    I.E M y z := by
  exact h.unique n f b y z ((h.graphs n f a b y y hab (h.reflexive y)).mp hy) hz

/-- Only the auxiliary representative operation chooses actual output tuples. -/
@[instance_reducible] def representativeStructure (h : I.Good M) :
    (EqualityAxioms.Extended L).Structure (I.Domain M) where
  funMap {n} f a := Classical.choose (h.total n f a)
  RelMap R a := match R with
    | .inl R => I.Relation M R a
    | .inr .equality => I.E M (a 0) (a 1)

theorem representative_fun_graph (h : I.Good M) {n : ℕ} (f : L.Functions n)
    (a : Fin n → I.Domain M) :
    I.Graph M f a (@Structure.funMap (EqualityAxioms.Extended L) (I.Domain M)
      (I.representativeStructure h) n f a) := by
  exact Classical.choose_spec (h.total n f a)

theorem representative_axioms (h : I.Good M) :
    letI := I.representativeStructure h
    EqualityAxioms.Axioms L (I.Domain M) := by
  let := I.representativeStructure h
  exact {
    reflexive := h.reflexive
    symmetric := h.symmetric
    transitive := h.transitive
    functions := fun f a b hab => I.graph_output_congr h f a b _ _ hab
      (I.representative_fun_graph h f a) (I.representative_fun_graph h f b)
    relations := fun R a b hab => h.relations _ R a b hab }

abbrev QuotientDomain (h : I.Good M) :=
  @EqualityAxioms.QuotientModel L (I.Domain M) (I.representativeStructure h) (I.representative_axioms h)

instance quotientStructure (h : I.Good M) : L.Structure (I.QuotientDomain h) :=
  @EqualityAxioms.quotientStructure L (I.Domain M) (I.representativeStructure h) (I.representative_axioms h)

def projection (h : I.Good M) : I.Domain M → I.QuotientDomain h :=
  @EqualityAxioms.projection L (I.Domain M) (I.representativeStructure h) (I.representative_axioms h)

instance quotientNonempty (h : I.Good M) : Nonempty (I.QuotientDomain h) :=
  ⟨I.projection h (Classical.choice h.nonempty)⟩

theorem projection_eq (h : I.Good M) (a b : I.Domain M) :
    I.projection h a = I.projection h b ↔ I.E M a b := by
  exact Quotient.eq

theorem projection_surjective (h : I.Good M) : Function.Surjective (I.projection h) := by
  exact Quotient.mk_surjective

theorem quotient_function (h : I.Good M) {n : ℕ} (f : L.Functions n)
    (a : Fin n → I.Domain M) (y : I.Domain M) (hy : I.Graph M f a y) :
    Structure.funMap f (I.projection h ∘ a) = I.projection h y := by
  let := I.representativeStructure h
  exact (EqualityAxioms.quotient_function (I.representative_axioms h) f a).trans
    ((I.projection_eq h _ y).mpr
      (h.unique n f a _ y (I.representative_fun_graph h f a) hy))

theorem quotient_relation (h : I.Good M) {n : ℕ} (R : L.Relations n)
    (a : Fin n → I.Domain M) :
    Structure.RelMap R (I.projection h ∘ a) ↔ I.Relation M R a := by
  let := I.representativeStructure h
  exact EqualityAxioms.quotient_relation (I.representative_axioms h) R a

/-- Logical equality is first replaced by the fresh relation, then coordinate-expanded. -/
def translateAux {n : ℕ} (A : L.BoundedFormula α n) : K.Formula ((α ⊕ Fin n) × Fin d) :=
  I.tuple.translateAux (EqualityAxioms.translate A)

def translate (A : L.Formula α) : K.Formula (α × Fin d) :=
  I.tuple.translate (EqualityAxioms.translate A)

def translateSentence (A : L.Sentence) : K.Sentence :=
  I.tuple.translateSentence (EqualityAxioms.translate A)

private theorem child_values {β : Type*} {N : Type*} {n : ℕ}
    (v : β × Fin d → N) (y : Fin d → N) (x : Fin n × Fin d → N) (i : Fin n) :
    Sum.elim (Sum.elim v y) x ∘
      Sum.elim (fun a => Sum.inl (Sum.inl a)) (fun j => Sum.inr (i,j)) =
        Sum.elim v (fun j => x (i,j)) := by
  funext a
  cases a <;> rfl

private theorem graph_values {β : Type*} {N : Type*} {n : ℕ}
    (v : β × Fin d → N) (y : Fin d → N) (x : Fin n × Fin d → N) :
    Sum.elim (Sum.elim v y) x ∘
      Sum.elim Sum.inr (fun j => Sum.inl (Sum.inr j)) =
        Sum.elim x y := by
  funext a
  cases a <;> rfl

theorem termGraph_exists (h : I.Good M) (t : (EqualityAxioms.Extended L).Term α)
    (v : α → I.Domain M) :
    ∃ y : I.Domain M, (I.tuple.termGraph t).Realize
      (Sum.elim (I.coordinates M v) y.val) := by
  induction t with
  | var a =>
    refine ⟨v a, ?_⟩
    simp only [FiniteDimensionalInterpretations.InterpretationData.termGraph,
      Formula.realize_inf, Formula.realize_relabel, Sum.elim_comp_inr,
      Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
      Sum.elim_inl, Sum.elim_inr]
    exact ⟨(v a).property, fun _ => rfl⟩
  | @func n f ts ih =>
    choose x hx using ih
    obtain ⟨y, hy⟩ := h.total n f x
    refine ⟨y, ?_⟩
    simp only [FiniteDimensionalInterpretations.InterpretationData.termGraph,
      Formula.realize_iExs, Formula.realize_inf, Formula.realize_iInf,
      Formula.realize_relabel, child_values, graph_values]
    exact ⟨I.coordinates M x, hx, (I.graph_iff_guarded f x y).mp hy⟩

theorem termGraph_sound (h : I.Good M) (t : (EqualityAxioms.Extended L).Term α)
    (v : α → I.Domain M) (y : Fin d → M)
    (hy : (I.tuple.termGraph t).Realize (Sum.elim (I.coordinates M v) y)) :
    letI := I.representativeStructure h
    ∃ hδ : I.tuple.domain.Realize y, I.E M ⟨y,hδ⟩ (t.realize v) := by
  let := I.representativeStructure h
  induction t generalizing y with
  | var a =>
    simp only [FiniteDimensionalInterpretations.InterpretationData.termGraph,
      Formula.realize_inf, Formula.realize_relabel, Sum.elim_comp_inr,
      Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
      Sum.elim_inl, Sum.elim_inr] at hy
    obtain ⟨hδ, he⟩ := hy
    refine ⟨hδ, ?_⟩
    have he' : (⟨y,hδ⟩ : I.Domain M) = v a := Subtype.ext (funext he)
    simpa only [he', Term.realize_var] using h.reflexive (v a)
  | @func n f ts ih =>
    simp only [FiniteDimensionalInterpretations.InterpretationData.termGraph,
      Formula.realize_iExs, Formula.realize_inf, Formula.realize_iInf,
      Formula.realize_relabel, child_values, graph_values] at hy
    obtain ⟨x, hx, hy⟩ := hy
    choose hδ he using fun i => ih i (fun j => x (i,j)) (hx i)
    let a : Fin n → I.Domain M := fun i => ⟨fun j => x (i,j), hδ i⟩
    have hy' := hy
    simp only [FiniteDimensionalInterpretations.InterpretationData.guardedGraph,
      Formula.realize_inf, Formula.realize_relabel, Sum.elim_comp_inr] at hy'
    obtain ⟨hδy, hgy⟩ := hy'
    refine ⟨hδy, ?_⟩
    exact I.graph_output_congr h f a (fun i => (ts i).realize v) ⟨y,hδy⟩ _ he
      hgy (I.representative_fun_graph h f (fun i => (ts i).realize v))

theorem termGraph_class (h : I.Good M) (t : L.Term α)
    (v : α → I.Domain M) (y : Fin d → M)
    (hy : (I.tuple.termGraph (EqualityAxioms.termTranslate t)).Realize (Sum.elim (I.coordinates M v) y)) :
    ∃ hδ : I.tuple.domain.Realize y,
      I.projection h ⟨y,hδ⟩ = t.realize (I.projection h ∘ v) := by
  let := I.representativeStructure h
  obtain ⟨hδ, he⟩ := I.termGraph_sound h (EqualityAxioms.termTranslate t) v y hy
  refine ⟨hδ, ((I.projection_eq h _ _).mpr he).trans ?_⟩
  exact (EqualityAxioms.term_projection (I.representative_axioms h) t v).symm

private theorem tuple_child_values {β : Type*} {N : Type*} {n : ℕ}
    (v : β × Fin d → N) (x : Fin n × Fin d → N) (i : Fin n) :
    Sum.elim v x ∘ Sum.elim Sum.inl (fun j => Sum.inr (i,j)) =
      Sum.elim v (fun j => x (i,j)) := by
  funext a
  cases a <;> rfl

private theorem coordinates_sum {β γ : Type*}
    (v : β → I.Domain M) (xs : γ → I.Domain M) :
    I.coordinates M (Sum.elim v xs) =
      (fun p => Sum.elim (fun a => (v a).val) (fun i => (xs i).val) p.1 p.2) := by
  funext p
  rcases p with ⟨a,j⟩
  cases a <;> rfl

private theorem snoc_values {n : ℕ} (xs : Fin n → I.Domain M) (y : I.Domain M) :
    (fun i : Fin (n+1) => (Fin.snoc (α := fun _ => I.Domain M) xs y i).val) =
      Fin.snoc (fun i => (xs i).val) y.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

private theorem representative_relation (h : I.Good M) {n : ℕ}
    (R : (EqualityAxioms.Extended L).Relations n) (a : Fin n → I.Domain M) :
    letI := I.representativeStructure h
    (I.tuple.relationFormula R).Realize (I.coordinates M a) ↔ Structure.RelMap R a := by
  cases R with
  | inl R => rfl
  | inr R =>
    cases R
    have he : a = ![a 0, a 1] := by
      funext i
      refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i <;> rfl
    change I.equalityFormula.Realize (I.coordinates M a) ↔ I.E M (a 0) (a 1)
    exact iff_of_eq (congrArg (fun b => I.equalityFormula.Realize (I.coordinates M b)) he)

private theorem expanded_relation_congr (h : I.Good M) {n : ℕ}
    (R : (EqualityAxioms.Extended L).Relations n) (a b : Fin n → I.Domain M)
    (hab : ∀ i, I.E M (a i) (b i)) :
    letI := I.representativeStructure h
    Structure.RelMap R a ↔ Structure.RelMap R b := by
  cases R with
  | inl R => exact h.relations n R a b hab
  | inr R =>
    cases R
    exact I.equivalence_congr h (hab 0) (hab 1)

private theorem invariant_relation_translation (h : I.Good M) {n : ℕ}
    (R : (EqualityAxioms.Extended L).Relations n)
    (ts : Fin n → (EqualityAxioms.Extended L).Term α) (v : α → I.Domain M) :
    letI := I.representativeStructure h
    (I.tuple.relationTranslation R ts).Realize (I.coordinates M v) ↔
      Structure.RelMap R (fun i => (ts i).realize v) := by
  let := I.representativeStructure h
  simp only [FiniteDimensionalInterpretations.InterpretationData.relationTranslation,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_iInf,
    Formula.realize_relabel, tuple_child_values, Sum.elim_comp_inr]
  constructor
  · rintro ⟨x, hx, hR⟩
    choose hδ he using fun i => I.termGraph_sound h (ts i) v (fun j => x (i,j)) (hx i)
    let a : Fin n → I.Domain M := fun i => ⟨fun j => x (i,j), hδ i⟩
    exact (I.expanded_relation_congr h R a (fun i => (ts i).realize v) he).mp
      ((I.representative_relation h R a).mp hR)
  · intro hR
    choose a ha using fun i => I.termGraph_exists h (ts i) v
    choose hδ he using fun i => I.termGraph_sound h (ts i) v (a i).val (ha i)
    refine ⟨I.coordinates M a, ha, ?_⟩
    apply (I.representative_relation h R a).mpr
    exact (I.expanded_relation_congr h R a (fun i => (ts i).realize v) he).mpr hR

/-- This intermediate truth theorem deliberately excludes logical equality atoms. -/
theorem invariant_expanded_truth (h : I.Good M) {n : ℕ}
    (B : (EqualityAxioms.Extended L).BoundedFormula α n) (hB : EqualityAxioms.EqualityFree B)
    (v : α → I.Domain M) (xs : Fin n → I.Domain M) :
    letI := I.representativeStructure h
    (I.tuple.translateAux B).Realize (I.coordinates M (Sum.elim v xs)) ↔
      B.Realize v xs := by
  let := I.representativeStructure h
  induction B with
  | falsum => rfl
  | equal s t => exact hB.elim
  | rel R ts =>
    simpa only [FiniteDimensionalInterpretations.InterpretationData.translateAux,
      BoundedFormula.Realize] using I.invariant_relation_translation h R ts (Sum.elim v xs)
  | imp A B ihA ihB =>
    exact imp_congr (ihA hB.1 xs) (ihB hB.2 xs)
  | @all n A ih =>
    simp only [FiniteDimensionalInterpretations.InterpretationData.translateAux,
      Formula.realize_iAlls, Formula.realize_imp, Formula.realize_relabel,
      Sum.elim_comp_inr, coordinates_sum,
      FiniteDimensionalInterpretations.InterpretationData.bindLastBlock_values]
    change (∀ y : Fin d → M, I.tuple.domain.Realize y →
      (I.tuple.translateAux A).Realize
        (fun p => Sum.elim (fun a => (v a).val)
          (Fin.snoc (fun i => (xs i).val) y) p.1 p.2)) ↔
      ∀ y : I.Domain M, A.Realize v (Fin.snoc xs y)
    constructor
    · intro hall y
      have hb := hall y.val y.property
      apply (ih hB (Fin.snoc xs y)).mp
      simpa only [coordinates_sum, snoc_values] using hb
    · intro hall y hy
      let b : I.Domain M := ⟨y, hy⟩
      have hb := (ih hB (Fin.snoc xs b)).mpr (hall b)
      simpa only [coordinates_sum, snoc_values] using hb

theorem quotient_truth (h : I.Good M) {n : ℕ} (A : L.BoundedFormula α n)
    (v : α → I.Domain M) (xs : Fin n → I.Domain M) :
    (I.translateAux A).Realize (I.coordinates M (Sum.elim v xs)) ↔
      A.Realize (I.projection h ∘ v) (I.projection h ∘ xs) := by
  let := I.representativeStructure h
  exact (I.invariant_expanded_truth h (EqualityAxioms.translate A)
    (EqualityAxioms.translate_equalityFree A) v xs).trans
      (EqualityAxioms.quotient_truth (I.representative_axioms h) A v xs).symm

theorem quotient_formula_truth (h : I.Good M) (A : L.Formula α) (v : α → I.Domain M) :
    (I.translate A).Realize (I.coordinates M v) ↔
      A.Realize (I.projection h ∘ v) := by
  rw [translate, FiniteDimensionalInterpretations.InterpretationData.translate,
    Formula.realize_relabel]
  have hv : I.coordinates M v ∘ (fun p => (Sum.elim id Fin.elim0 p.1,p.2)) =
      I.coordinates M (Sum.elim v (Fin.elim0 : Fin 0 → I.Domain M)) := by
    funext p
    rcases p with ⟨a,j⟩
    cases a with
    | inl a => rfl
    | inr i => exact i.elim0
  rw [hv]
  have hx : I.projection h ∘ (Fin.elim0 : Fin 0 → I.Domain M) = default := Subsingleton.elim _ _
  simpa only [translateAux, Formula.Realize, hx] using I.quotient_truth h A v Fin.elim0

theorem quotient_sentence_truth (h : I.Good M) (A : L.Sentence) :
    M ⊨ I.translateSentence A ↔ I.QuotientDomain h ⊨ A := by
  change Formula.Realize (I.translateSentence A) (default : Empty → M) ↔
    Formula.Realize A (default : Empty → I.QuotientDomain h)
  rw [translateSentence, FiniteDimensionalInterpretations.InterpretationData.translateSentence,
    Formula.realize_relabel]
  have he : (default : Empty → M) ∘ (fun p : Empty × Fin d => p.1.elim) =
      I.coordinates M (default : Empty → I.Domain M) := by
    funext p
    exact p.1.elim
  rw [he]
  have hv : I.projection h ∘ (default : Empty → I.Domain M) = default := Subsingleton.elim _ _
  simpa only [translate, hv] using I.quotient_formula_truth h A (default : Empty → I.Domain M)

theorem representative_assignments (h : I.Good M) {n : ℕ}
    (v : α → I.QuotientDomain h) (xs : Fin n → I.QuotientDomain h) :
    ∃ v' : α → I.Domain M, ∃ xs' : Fin n → I.Domain M,
      I.projection h ∘ v' = v ∧ I.projection h ∘ xs' = xs := by
  choose v' hv using fun a => I.projection_surjective h (v a)
  choose xs' hx using fun i => I.projection_surjective h (xs i)
  exact ⟨v', xs', funext hv, funext hx⟩

theorem representative_independence (h : I.Good M) {n : ℕ} (A : L.BoundedFormula α n)
    (v v' : α → I.Domain M) (xs xs' : Fin n → I.Domain M)
    (hv : I.projection h ∘ v = I.projection h ∘ v')
    (hx : I.projection h ∘ xs = I.projection h ∘ xs') :
    (I.translateAux A).Realize (I.coordinates M (Sum.elim v xs)) ↔
      (I.translateAux A).Realize (I.coordinates M (Sum.elim v' xs')) := by
  rw [I.quotient_truth h, I.quotient_truth h, hv, hx]

end InterpretationData
end
end Lemmatheca.MathematicalLogic.QuotientInterpretations
