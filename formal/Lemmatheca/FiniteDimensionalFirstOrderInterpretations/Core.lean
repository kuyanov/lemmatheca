import Lemmatheca.InterpretingTheories.InterpretingTheories

/-! Finite coordinate blocks in the actual shared first-order syntax. -/
namespace Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.MathematicalLogic.DefinitionalExtensions (close)
universe u v u' v' w z
noncomputable section
variable {L : Language.{u,v}} {K : Language.{u',v'}} {d : ℕ} {α : Type z}

/-- A positive finite block for each represented element; equality is actual tuple equality. -/
structure InterpretationData (L : Language.{u,v}) (K : Language.{u',v'}) (d : ℕ) where
  positive : 0 < d
  domain : K.Formula (Fin d)
  functionGraph : ∀ {n}, L.Functions n → K.Formula ((Fin n × Fin d) ⊕ Fin d)
  relationFormula : ∀ {n}, L.Relations n → K.Formula (Fin n × Fin d)

namespace InterpretationData
variable (I : InterpretationData L K d)

def guardedGraph {n : ℕ} (f : L.Functions n) : K.Formula ((Fin n × Fin d) ⊕ Fin d) :=
  I.domain.relabel Sum.inr ⊓ I.functionGraph f

def nonemptySentence : K.Sentence :=
  (I.domain.relabel (Sum.inr : Fin d → Empty ⊕ Fin d)).iExs (Fin d)

def graphSentence {n : ℕ} (f : L.Functions n) : K.Sentence :=
  close ((Formula.iInf (fun i : Fin n => I.domain.relabel (fun j => (i,j)))).imp
    ((I.guardedGraph f).iExsUnique (Fin d)))

def Admissible (S : K.Theory) : Prop :=
  Derives S I.nonemptySentence ∧ ∀ n (f : L.Functions n), Derives S (I.graphSentence f)

variable (M : Type w) [K.Structure M]

def Domain := {a : Fin d → M // I.domain.Realize a}

def coordinates (v : α → I.Domain M) : α × Fin d → M := fun p => (v p.1).val p.2

def GoodGraphs : Prop :=
  ∀ n (f : L.Functions n) (x : Fin n → I.Domain M),
    ∃! y : Fin d → M,
      (I.guardedGraph f).Realize (Sum.elim (I.coordinates M x) y)

def Good : Prop := Nonempty (I.Domain M) ∧ I.GoodGraphs M

variable {M}

@[instance_reducible] def inducedStructure (h : I.GoodGraphs M) : L.Structure (I.Domain M) where
  funMap {n} f x :=
    ⟨Classical.choose (h n f x), by
      simpa only [Formula.realize_relabel, Sum.elim_comp_inr] using
        (Formula.realize_inf.mp (Classical.choose_spec (h n f x)).1).1⟩
  RelMap R x := (I.relationFormula R).Realize (I.coordinates M x)

theorem realize_nonemptySentence : M ⊨ I.nonemptySentence ↔ Nonempty (I.Domain M) := by
  simp only [nonemptySentence, Sentence.Realize, Formula.realize_iExs,
    Formula.realize_relabel, Sum.elim_comp_inr]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨y, hy⟩⟩
  · rintro ⟨y⟩
    exact ⟨y.val, y.property⟩

theorem realize_graphSentence {n : ℕ} (f : L.Functions n) :
    M ⊨ I.graphSentence f ↔
      ∀ x : Fin n × Fin d → M, (∀ i, I.domain.Realize (fun j => x (i,j))) →
        ∃! y : Fin d → M, (I.guardedGraph f).Realize (Sum.elim x y) := by
  rw [graphSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close]
  simp only [Formula.realize_imp, Formula.realize_iInf, Formula.realize_relabel,
    Function.comp_def, Formula.realize_iExsUnique]

theorem good_of_admissible {S : K.Theory} (h : I.Admissible S)
    [Nonempty M] [M ⊨ S] : I.Good M := by
  constructor
  · apply I.realize_nonemptySentence.mp
    exact derives_sound h.1 default (fun A hA => Theory.realize_sentence_of_mem S hA)
  · intro n f x
    apply (I.realize_graphSentence f).mp
      (derives_sound (h.2 n f) default (fun A hA => Theory.realize_sentence_of_mem S hA))
    exact fun i => (x i).property

theorem induced_fun_graph (h : I.GoodGraphs M) {n : ℕ} (f : L.Functions n)
    (x : Fin n → I.Domain M) (y : Fin d → M) :
    (I.guardedGraph f).Realize (Sum.elim (I.coordinates M x) y) ↔
      y = (@Structure.funMap L (I.Domain M) (I.inducedStructure h) n f x).val := by
  change _ ↔ y = Classical.choose (h n f x)
  exact ⟨fun hy => (Classical.choose_spec (h n f x)).2 y hy,
    fun hy => hy ▸ (Classical.choose_spec (h n f x)).1⟩

/-- Rebind just the last source placeholder to its fresh coordinate block. -/
def bindLastBlock {α : Type*} (n : ℕ) :
    (α ⊕ Fin (n+1)) × Fin d → ((α ⊕ Fin n) × Fin d) ⊕ Fin d :=
  fun p => Sum.elim (fun a => Sum.inl (.inl a,p.2))
    (Fin.lastCases (Sum.inr p.2) (fun i => Sum.inl (.inr i,p.2))) p.1

/-- The output block is disjoint from all input blocks at every recursive call. -/
def termGraph (I : InterpretationData L K d) : L.Term α → K.Formula ((α × Fin d) ⊕ Fin d)
  | .var a => I.domain.relabel Sum.inr ⊓ Formula.iInf (fun j : Fin d =>
      (Term.var (.inr j)).equal (.var (.inl (a,j))))
  | @Term.func _ _ n f ts =>
      ((Formula.iInf (fun i : Fin n =>
        (I.termGraph (ts i)).relabel (Sum.elim
          (fun a => Sum.inl (Sum.inl a)) (fun j => Sum.inr (i,j))))) ⊓
        (I.guardedGraph f).relabel
          (Sum.elim Sum.inr (fun j => Sum.inl (Sum.inr j)))).iExs (Fin n × Fin d)

def relationTranslation {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term α) :
    K.Formula (α × Fin d) :=
  ((Formula.iInf (fun i : Fin n =>
    (I.termGraph (ts i)).relabel (Sum.elim Sum.inl (fun j => Sum.inr (i,j))))) ⊓
    (I.relationFormula R).relabel Sum.inr).iExs (Fin n × Fin d)

def translateAux (I : InterpretationData L K d) :
    {n : ℕ} → L.BoundedFormula α n → K.Formula ((α ⊕ Fin n) × Fin d)
  | _, .falsum => ⊥
  | _, .equal s t => (I.termGraph s ⊓ I.termGraph t).iExs (Fin d)
  | _, .rel R ts => I.relationTranslation R ts
  | _, .imp A B => (I.translateAux A).imp (I.translateAux B)
  | n, .all A => ((I.domain.relabel Sum.inr).imp
      ((I.translateAux A).relabel (bindLastBlock n))).iAlls (Fin d)

def translate (A : L.Formula α) : K.Formula (α × Fin d) :=
  (I.translateAux A).relabel (fun p => (Sum.elim id Fin.elim0 p.1,p.2))

def translateSentence (A : L.Sentence) : K.Sentence :=
  (I.translate A).relabel (fun p => p.1.elim)

theorem bindLastBlock_values {β : Type*} (n : ℕ) (v : β → Fin d → M)
    (xs : Fin n → Fin d → M) (y : Fin d → M) :
    Sum.elim (fun p => Sum.elim v xs p.1 p.2) y ∘ bindLastBlock n =
      (fun p => Sum.elim v (Fin.snoc xs y) p.1 p.2) := by
  funext p
  rcases p with ⟨a,j⟩
  cases a with
  | inl a => rfl
  | inr i =>
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [bindLastBlock]

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

theorem realize_termGraph (h : I.GoodGraphs M) (t : L.Term α)
    (v : α → I.Domain M) (y : Fin d → M) :
    letI := I.inducedStructure h
    (I.termGraph t).Realize (Sum.elim (I.coordinates M v) y) ↔
      y = (t.realize v).val := by
  let := I.inducedStructure h
  induction t generalizing y with
  | var a =>
    simp only [termGraph, Formula.realize_inf, Formula.realize_relabel,
      Sum.elim_comp_inr, Formula.realize_iInf, Formula.realize_equal,
      Term.realize_var, Sum.elim_inl, Sum.elim_inr, coordinates]
    constructor
    · rintro ⟨_, he⟩
      exact funext he
    · intro he
      exact ⟨he ▸ (v a).property, fun j => congrFun he j⟩
  | @func n f ts ih =>
    simp only [termGraph, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_iInf, Formula.realize_relabel, child_values, graph_values]
    change (∃ x : Fin n × Fin d → M,
      (∀ i, (I.termGraph (ts i)).Realize
        (Sum.elim (I.coordinates M v) (fun j => x (i,j)))) ∧
      (I.guardedGraph f).Realize (Sum.elim x y)) ↔
        y = (@Structure.funMap L (I.Domain M) _ n f (fun i => (ts i).realize v)).val
    simp_rw [ih]
    constructor
    · rintro ⟨x, hx, hy⟩
      have he : x = I.coordinates M (fun i => (ts i).realize v) := by
        funext p
        exact congrFun (hx p.1) p.2
      rw [he] at hy
      exact (I.induced_fun_graph h f (fun i => (ts i).realize v) y).mp hy
    · intro hy
      exact ⟨I.coordinates M (fun i => (ts i).realize v), fun _ => rfl,
        (I.induced_fun_graph h f (fun i => (ts i).realize v) y).mpr hy⟩

theorem termGraph_total_unique (h : I.GoodGraphs M) (t : L.Term α)
    (v : α → I.Domain M) :
    ∃! y : Fin d → M, (I.termGraph t).Realize (Sum.elim (I.coordinates M v) y) := by
  let := I.inducedStructure h
  simpa only [I.realize_termGraph h] using
    (show ∃! y : Fin d → M, y = (t.realize v).val from existsUnique_eq)

theorem termGraph_output_domain (h : I.GoodGraphs M) (t : L.Term α)
    (v : α → I.Domain M) (y : Fin d → M)
    (hy : (I.termGraph t).Realize (Sum.elim (I.coordinates M v) y)) :
    I.domain.Realize y := by
  let := I.inducedStructure h
  have he := (I.realize_termGraph h t v y).mp hy
  simpa only [he] using (t.realize v).property

private theorem tuple_child_values {β : Type*} {N : Type*} {n : ℕ}
    (v : β × Fin d → N) (x : Fin n × Fin d → N) (i : Fin n) :
    Sum.elim v x ∘ Sum.elim Sum.inl (fun j => Sum.inr (i,j)) =
      Sum.elim v (fun j => x (i,j)) := by
  funext a
  cases a <;> rfl

private theorem realize_relationTranslation (h : I.GoodGraphs M) {n : ℕ}
    (R : L.Relations n) (ts : Fin n → L.Term α) (v : α → I.Domain M) :
    letI := I.inducedStructure h
    (I.relationTranslation R ts).Realize (I.coordinates M v) ↔
      Structure.RelMap R (fun i => (ts i).realize v) := by
  let := I.inducedStructure h
  change (I.relationTranslation R ts).Realize (I.coordinates M v) ↔
    (I.relationFormula R).Realize (I.coordinates M (fun i => (ts i).realize v))
  simp only [relationTranslation, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_relabel, tuple_child_values, Sum.elim_comp_inr]
  simp_rw [I.realize_termGraph h]
  constructor
  · rintro ⟨x, hx, hy⟩
    have he : x = I.coordinates M (fun i => (ts i).realize v) := by
      funext p
      exact congrFun (hx p.1) p.2
    simpa only [he] using hy
  · intro hy
    exact ⟨I.coordinates M (fun i => (ts i).realize v), fun _ => rfl, hy⟩

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

theorem realize_translateAux (h : I.GoodGraphs M) {n : ℕ} (A : L.BoundedFormula α n)
    (v : α → I.Domain M) (xs : Fin n → I.Domain M) :
    letI := I.inducedStructure h
    (I.translateAux A).Realize (I.coordinates M (Sum.elim v xs)) ↔
      A.Realize v xs := by
  let := I.inducedStructure h
  induction A with
  | falsum => rfl
  | equal s t =>
    simp only [translateAux, Formula.realize_iExs, Formula.realize_inf]
    simp_rw [I.realize_termGraph h]
    change (∃ y : Fin d → M,
      y = (s.realize (Sum.elim v xs)).val ∧ y = (t.realize (Sum.elim v xs)).val) ↔
        s.realize (Sum.elim v xs) = t.realize (Sum.elim v xs)
    constructor
    · rintro ⟨y, hs, ht⟩
      exact Subtype.ext (hs.symm.trans ht)
    · intro he
      exact ⟨(s.realize (Sum.elim v xs)).val, rfl, congrArg Subtype.val he⟩
  | rel R ts =>
    simpa only [translateAux, BoundedFormula.Realize] using
      realize_relationTranslation I h R ts (Sum.elim v xs)
  | imp A B ihA ihB =>
    simp only [translateAux, Formula.realize_imp, BoundedFormula.Realize, ihA, ihB]
  | @all n A ih =>
    simp only [translateAux, Formula.realize_iAlls, Formula.realize_imp,
      Formula.realize_relabel, Sum.elim_comp_inr, coordinates_sum, bindLastBlock_values]
    change (∀ y : Fin d → M, I.domain.Realize y →
      (I.translateAux A).Realize
        (fun p => Sum.elim (fun a => (v a).val)
          (Fin.snoc (fun i => (xs i).val) y) p.1 p.2)) ↔
      ∀ y : I.Domain M, A.Realize v (Fin.snoc xs y)
    constructor
    · intro hall y
      have hb := hall y.val y.property
      apply (ih (Fin.snoc xs y)).mp
      simpa only [coordinates_sum, snoc_values] using hb
    · intro hall y hy
      let b : I.Domain M := ⟨y, hy⟩
      have hb := (ih (Fin.snoc xs b)).mpr (hall b)
      simpa only [coordinates_sum, snoc_values] using hb

theorem realize_translate (h : I.GoodGraphs M) (A : L.Formula α) (v : α → I.Domain M) :
    letI := I.inducedStructure h
    (I.translate A).Realize (I.coordinates M v) ↔ A.Realize v := by
  rw [translate, Formula.realize_relabel]
  have hv : I.coordinates M v ∘ (fun p => (Sum.elim id Fin.elim0 p.1,p.2)) =
      I.coordinates M (Sum.elim v (Fin.elim0 : Fin 0 → I.Domain M)) := by
    funext p
    rcases p with ⟨a,j⟩
    cases a with
    | inl a => rfl
    | inr i => exact i.elim0
  rw [hv]
  exact I.realize_translateAux h A v Fin.elim0

theorem existential_guard (h : I.GoodGraphs M) (A : L.Formula (α ⊕ Unit))
    (v : α → I.Domain M) :
    (I.translate (A.iExs Unit)).Realize (I.coordinates M v) ↔
      ∃ y : Fin d → M, I.domain.Realize y ∧
        (I.translate A).Realize (fun p => Sum.elim (fun a => (v a).val) (fun _ => y) p.1 p.2) := by
  let := I.inducedStructure h
  rw [I.realize_translate h, Formula.realize_iExs]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(y ()).val, (y ()).property, ?_⟩
    have ht := (I.realize_translate h A (Sum.elim v y)).mpr hy
    have he : (fun i => (y i).val) = (fun _ : Unit => (y ()).val) := by
      funext i
      cases i
      rfl
    simpa only [coordinates_sum, he] using ht
  · rintro ⟨y, hy, ht⟩
    let b : I.Domain M := ⟨y, hy⟩
    refine ⟨fun _ => b, ?_⟩
    apply (I.realize_translate h A (Sum.elim v (fun _ => b))).mp
    rw [coordinates_sum]
    exact ht

theorem realize_translateSentence (h : I.GoodGraphs M) (A : L.Sentence) :
    letI := I.inducedStructure h
    M ⊨ I.translateSentence A ↔ I.Domain M ⊨ A := by
  unfold Sentence.Realize translateSentence
  rw [Formula.realize_relabel]
  have he : (default : Empty → M) ∘ (fun p : Empty × Fin d => p.1.elim) =
      I.coordinates M (default : Empty → I.Domain M) := by
    funext p
    exact p.1.elim
  rw [he]
  exact I.realize_translate h A (default : Empty → I.Domain M)

def Interprets (I : InterpretationData L K d) (T : L.Theory) (S : K.Theory) : Prop :=
  I.Admissible S ∧ ∀ A ∈ T, Derives S (I.translateSentence A)

theorem models_induced {T : L.Theory} {S : K.Theory} (h : I.Interprets T S)
    [Nonempty M] [M ⊨ S] :
    letI := I.inducedStructure (I.good_of_admissible (M := M) h.1).2
    I.Domain M ⊨ T := by
  let := I.inducedStructure (I.good_of_admissible (M := M) h.1).2
  constructor
  intro A hA
  apply (I.realize_translateSentence (I.good_of_admissible (M := M) h.1).2 A).mp
  exact derives_sound (h.2 A hA) default (fun B hB => Theory.realize_sentence_of_mem S hB)

theorem derives_translate {T : L.Theory} {S : K.Theory} (h : I.Interprets T S)
    {A : L.Sentence} (hp : Derives T A) : Derives S (I.translateSentence A) := by
  apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
  rw [Theory.models_sentence_iff]
  intro M
  have hg := I.good_of_admissible (M := M) h.1
  let := I.inducedStructure hg.2
  let : Nonempty (I.Domain M) := hg.1
  let : I.Domain M ⊨ T := I.models_induced h
  apply (I.realize_translateSentence hg.2 A).mpr
  exact derives_sound hp default (fun B hB => Theory.realize_sentence_of_mem T hB)

theorem consistent_transfer {T : L.Theory} {S : K.Theory} (h : I.Interprets T S)
    (hS : Consistent S) : Consistent T := by
  intro hp
  apply hS
  exact I.derives_translate h hp

end InterpretationData
end
end Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations
