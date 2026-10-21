import Lemmatheca.DefinitionalExtensions.DefinitionalExtensions

/-! One-dimensional equality-preserving interpretations in the shared syntax. -/
namespace Lemmatheca.MathematicalLogic.InterpretingTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.MathematicalLogic.DefinitionalExtensions (close)
universe u v u' v' w z
noncomputable section
variable {L : Language.{u,v}} {K : Language.{u',v'}} {α : Type z}

structure InterpretationData (L : Language.{u,v}) (K : Language.{u',v'}) where
  domain : K.Formula Unit
  functionGraph : ∀ {n}, L.Functions n → K.Formula (Fin n ⊕ Unit)
  relationFormula : ∀ {n}, L.Relations n → K.Formula (Fin n)

namespace InterpretationData
variable (I : InterpretationData L K)

def guardedGraph {n : ℕ} (f : L.Functions n) : K.Formula (Fin n ⊕ Unit) :=
  I.domain.relabel Sum.inr ⊓ I.functionGraph f

def nonemptySentence : K.Sentence :=
  (I.domain.relabel (Sum.inr : Unit → Empty ⊕ Unit)).iExs Unit

def graphSentence {n : ℕ} (f : L.Functions n) : K.Sentence :=
  close ((Formula.iInf (fun i : Fin n => I.domain.relabel (fun _ => i))).imp
    ((I.guardedGraph f).iExsUnique Unit))

def Admissible (S : K.Theory) : Prop :=
  Derives S I.nonemptySentence ∧ ∀ n (f : L.Functions n), Derives S (I.graphSentence f)

variable (M : Type w) [K.Structure M]

def Domain := {a : M // I.domain.Realize (fun _ => a)}

def GoodGraphs : Prop :=
  ∀ n (f : L.Functions n) (x : Fin n → I.Domain M),
    ∃! y : M, (I.guardedGraph f).Realize (Sum.elim (fun i => (x i).val) (fun _ => y))

def Good : Prop := Nonempty (I.Domain M) ∧ I.GoodGraphs M

variable {M}

@[instance_reducible] def inducedStructure (h : I.GoodGraphs M) : L.Structure (I.Domain M) where
  funMap {n} f x :=
    ⟨Classical.choose (h n f x),
      by
      simpa only [Formula.realize_relabel, Sum.elim_comp_inr] using
        (Formula.realize_inf.mp (Classical.choose_spec (h n f x)).1).1⟩
  RelMap R x := (I.relationFormula R).Realize (fun i => (x i).val)

theorem realize_nonemptySentence : M ⊨ I.nonemptySentence ↔ Nonempty (I.Domain M) := by
  simp only [nonemptySentence, Sentence.Realize, Formula.realize_iExs,
    Formula.realize_relabel, Sum.elim_comp_inr]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨y (), hy⟩⟩
  · rintro ⟨y⟩
    exact ⟨fun _ => y.val, y.property⟩

theorem realize_graphSentence {n : ℕ} (f : L.Functions n) :
    M ⊨ I.graphSentence f ↔
      ∀ x : Fin n → M, (∀ i, I.domain.Realize (fun _ => x i)) →
        ∃! y : M, (I.guardedGraph f).Realize (Sum.elim x (fun _ => y)) := by
  rw [graphSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close]
  simp only [Formula.realize_imp, Formula.realize_iInf, Formula.realize_relabel,
    Function.comp_def, Formula.realize_iExsUnique]
  constructor
  · intro h x hx
    obtain ⟨y, hy, hu⟩ := h x hx
    refine ⟨y (), ?_, ?_⟩
    · convert hy using 1
    · intro z hz
      exact congrFun (hu (fun _ => z) hz) ()
  · intro h x hx
    obtain ⟨y, hy, hu⟩ := h x hx
    refine ⟨fun _ => y, hy, ?_⟩
    intro z hz
    funext i
    cases i
    apply hu (z ())
    convert hz using 1

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
    (x : Fin n → I.Domain M) (y : M) :
    (I.guardedGraph f).Realize (Sum.elim (fun i => (x i).val) (fun _ => y)) ↔
      y = (@Structure.funMap L (I.Domain M) (I.inducedStructure h) n f x).val := by
  change _ ↔ y = Classical.choose (h n f x)
  exact ⟨fun hy => (Classical.choose_spec (h n f x)).2 y hy,
    fun hy => hy ▸ (Classical.choose_spec (h n f x)).1⟩

/-- Every output slot is fresh and every intermediate value is guarded. -/
def termGraph (I : InterpretationData L K) : L.Term α → K.Formula (α ⊕ Unit)
  | .var a => I.domain.relabel Sum.inr ⊓ (Term.var (.inr ())).equal (.var (.inl a))
  | @Term.func _ _ n f ts =>
      ((Formula.iInf (fun i : Fin n =>
        (I.termGraph (ts i)).relabel (Sum.elim
          (fun a => Sum.inl (Sum.inl a)) (fun _ => Sum.inr i)))) ⊓
        (I.guardedGraph f).relabel
          (Sum.elim Sum.inr (fun _ => Sum.inl (Sum.inr ())))).iExs (Fin n)

def relationTranslation {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term α) : K.Formula α :=
  ((Formula.iInf (fun i : Fin n =>
    (I.termGraph (ts i)).relabel (Sum.elim Sum.inl (fun _ => Sum.inr i)))) ⊓
    (I.relationFormula R).relabel Sum.inr).iExs (Fin n)

def translateAux (I : InterpretationData L K) : {n : ℕ} → L.BoundedFormula α n → K.Formula (α ⊕ Fin n)
  | _, .falsum => ⊥
  | _, .equal s t => (I.termGraph s ⊓ I.termGraph t).iExs Unit
  | _, .rel R ts => I.relationTranslation R ts
  | _, .imp A B => (I.translateAux A).imp (I.translateAux B)
  | n, .all A => ((I.domain.relabel Sum.inr).imp
      ((I.translateAux A).relabel (Lemmatheca.MathematicalLogic.DefinitionalExtensions.DefinitionPackage.bindLast n))).iAlls Unit

def translate (A : L.Formula α) : K.Formula α :=
  (I.translateAux A).relabel (Sum.elim id Fin.elim0)

def translateSentence (A : L.Sentence) : K.Sentence := I.translate A

/-- Direct relational atoms, with no graph witnesses. -/
def relationalTerm [L.IsRelational] : L.Term α → K.Term α
  | .var a => .var a
  | .func f _ => isEmptyElim f

def relationalAux (I : InterpretationData L K) [L.IsRelational] :
    {n : ℕ} → L.BoundedFormula α n → K.Formula (α ⊕ Fin n)
  | _, .falsum => ⊥
  | _, .equal s t => (relationalTerm s).equal (relationalTerm t)
  | _, .rel R ts => (I.relationFormula R).subst (fun i => relationalTerm (ts i))
  | _, .imp A B => (I.relationalAux A).imp (I.relationalAux B)
  | n, .all A => ((I.domain.relabel Sum.inr).imp
      ((I.relationalAux A).relabel (Lemmatheca.MathematicalLogic.DefinitionalExtensions.DefinitionPackage.bindLast n))).iAlls Unit

def relational [L.IsRelational] (A : L.Formula α) : K.Formula α :=
  (I.relationalAux A).relabel (Sum.elim id Fin.elim0)

variable {I}


private theorem child_values {β : Type*} {N : Type*} {n : ℕ}
    (v : β → N) (y : N) (x : Fin n → N) (i : Fin n) :
    Sum.elim (Sum.elim v (fun _ : Unit => y)) x ∘
      Sum.elim (fun a => Sum.inl (Sum.inl a)) (fun _ : Unit => Sum.inr i) =
        Sum.elim v (fun _ : Unit => x i) := by
  funext a
  cases a <;> rfl

private theorem graph_values {β : Type*} {N : Type*} {n : ℕ}
    (v : β → N) (y : N) (x : Fin n → N) :
    Sum.elim (Sum.elim v (fun _ : Unit => y)) x ∘
      Sum.elim Sum.inr (fun _ : Unit => Sum.inl (Sum.inr ())) =
        Sum.elim x (fun _ : Unit => y) := by
  funext a
  cases a with
  | inl i => rfl
  | inr i => cases i; rfl

theorem realize_termGraph (h : I.GoodGraphs M) (t : L.Term α)
    (v : α → I.Domain M) (y : M) :
    letI := I.inducedStructure h
    (I.termGraph t).Realize (Sum.elim (fun a => (v a).val) (fun _ => y)) ↔
      y = (t.realize v).val := by
  let := I.inducedStructure h
  induction t generalizing y with
  | var a =>
    simp only [termGraph, Formula.realize_inf, Formula.realize_relabel,
      Sum.elim_comp_inr, Formula.realize_equal, Term.realize_var,
      Sum.elim_inl, Sum.elim_inr, Term.realize_var]
    exact ⟨And.right, fun hy => ⟨hy ▸ (v a).property, hy⟩⟩
  | @func n f ts ih =>
    simp only [termGraph, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_iInf, Formula.realize_relabel, child_values, graph_values]
    change (∃ x : Fin n → M,
      (∀ i, (I.termGraph (ts i)).Realize
        (Sum.elim (fun a => (v a).val) (fun _ => x i))) ∧
      (I.guardedGraph f).Realize (Sum.elim x (fun _ => y))) ↔
        y = (@Structure.funMap L (I.Domain M) _ n f (fun i => (ts i).realize v)).val
    simp_rw [ih]
    constructor
    · rintro ⟨x, hx, hy⟩
      have he : x = fun i => ((ts i).realize v).val := funext hx
      rw [he] at hy
      exact (I.induced_fun_graph h f (fun i => (ts i).realize v) y).mp hy
    · intro hy
      exact ⟨fun i => ((ts i).realize v).val, fun _ => rfl,
        (I.induced_fun_graph h f (fun i => (ts i).realize v) y).mpr hy⟩

theorem termGraph_total_unique (h : I.GoodGraphs M) (t : L.Term α)
    (v : α → I.Domain M) :
    ∃! y : M, (I.termGraph t).Realize (Sum.elim (fun a => (v a).val) (fun _ => y)) := by
  let := I.inducedStructure h
  simpa only [realize_termGraph h] using
    (show ∃! y : M, y = (t.realize v).val from existsUnique_eq)

theorem termGraph_output_domain (h : I.GoodGraphs M) (t : L.Term α)
    (v : α → I.Domain M) (y : M)
    (hy : (I.termGraph t).Realize (Sum.elim (fun a => (v a).val) (fun _ => y))) :
    I.domain.Realize (fun _ => y) := by
  let := I.inducedStructure h
  have he := (realize_termGraph h t v y).mp hy
  simpa only [he] using (t.realize v).property


private theorem graph_at (h : I.GoodGraphs M) (t : L.Term α)
    (v : α → I.Domain M) (y : Unit → M) :
    letI := I.inducedStructure h
    (I.termGraph t).Realize (Sum.elim (fun a => (v a).val) y) ↔
      y () = (t.realize v).val := by
  have he : (fun _ : Unit => y ()) = y := by funext i; cases i; rfl
  simpa only [he] using realize_termGraph h t v (y ())

private theorem tuple_child_values {β : Type*} {N : Type*} {n : ℕ}
    (v : β → N) (x : Fin n → N) (i : Fin n) :
    Sum.elim v x ∘ Sum.elim Sum.inl (fun _ : Unit => Sum.inr i) =
      Sum.elim v (fun _ : Unit => x i) := by
  funext a
  cases a <;> rfl

private theorem realize_relationTranslation (h : I.GoodGraphs M) {n : ℕ}
    (R : L.Relations n) (ts : Fin n → L.Term α) (v : α → I.Domain M) :
    letI := I.inducedStructure h
    (I.relationTranslation R ts).Realize (fun a => (v a).val) ↔
      Structure.RelMap R (fun i => (ts i).realize v) := by
  let := I.inducedStructure h
  change (I.relationTranslation R ts).Realize (fun a => (v a).val) ↔
    (I.relationFormula R).Realize (fun i => ((ts i).realize v).val)
  simp only [relationTranslation, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_relabel, tuple_child_values, Sum.elim_comp_inr]
  simp_rw [realize_termGraph h]
  constructor
  · rintro ⟨x, hx, hy⟩
    have he : x = fun i => ((ts i).realize v).val := funext hx
    simpa only [he] using hy
  · intro hy
    exact ⟨fun i => ((ts i).realize v).val, fun _ => rfl, hy⟩

private theorem bindLast_values {β : Type*} {N : Type*} (n : ℕ)
    (v : β → N) (xs : Fin n → N) (y : Unit → N) :
    Sum.elim (Sum.elim v xs) y ∘
      Lemmatheca.MathematicalLogic.DefinitionalExtensions.DefinitionPackage.bindLast n =
        Sum.elim v (Fin.snoc xs (y ())) := by
  funext a
  cases a with
  | inl i => rfl
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [Lemmatheca.MathematicalLogic.DefinitionalExtensions.DefinitionPackage.bindLast]

private theorem sum_values {β γ : Type*} (v : β → I.Domain M) (xs : γ → I.Domain M) :
    (fun a => (Sum.elim v xs a).val) =
      Sum.elim (fun a => (v a).val) (fun i => (xs i).val) := by
  funext a
  cases a <;> rfl

private theorem snoc_values {n : ℕ} (xs : Fin n → I.Domain M) (y : I.Domain M) :
    (fun i : Fin (n+1) => (Fin.snoc (α := fun _ => I.Domain M) xs y i).val) = Fin.snoc (fun i => (xs i).val) y.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem realize_translateAux (h : I.GoodGraphs M) {n : ℕ} (A : L.BoundedFormula α n)
    (v : α → I.Domain M) (xs : Fin n → I.Domain M) :
    letI := I.inducedStructure h
    (I.translateAux A).Realize (Sum.elim (fun a => (v a).val) (fun i => (xs i).val)) ↔
      A.Realize v xs := by
  let := I.inducedStructure h
  induction A with
  | falsum => rfl
  | equal s t =>
    simp only [translateAux, Formula.realize_iExs, Formula.realize_inf]
    rw [← sum_values v xs]
    simp_rw [graph_at h]
    change (∃ u : Unit → M, u () = (s.realize (Sum.elim v xs)).val ∧
      u () = (t.realize (Sum.elim v xs)).val) ↔
      s.realize (Sum.elim v xs) = t.realize (Sum.elim v xs)
    constructor
    · rintro ⟨u, hs, ht⟩
      exact Subtype.ext (hs.symm.trans ht)
    · intro he
      exact ⟨fun _ => (s.realize (Sum.elim v xs)).val, rfl, congrArg Subtype.val he⟩
  | rel R ts =>
    simpa only [translateAux, BoundedFormula.Realize, sum_values (I := I) v xs] using
      realize_relationTranslation h R ts (Sum.elim v xs)
  | imp A B ihA ihB =>
    simp only [translateAux, Formula.realize_imp, BoundedFormula.Realize, ihA, ihB]
  | @all n A ih =>
    simp only [translateAux, Formula.realize_iAlls, Formula.realize_imp,
      Formula.realize_relabel, Sum.elim_comp_inr, bindLast_values]
    change (∀ y : Unit → M, I.domain.Realize y →
      (I.translateAux A).Realize
        (Sum.elim (fun a => (v a).val) (Fin.snoc (fun i => (xs i).val) (y ())))) ↔
      ∀ y : I.Domain M, A.Realize v (Fin.snoc xs y)
    constructor
    · intro hall y
      have hb := hall (fun _ => y.val) y.property
      apply (ih (Fin.snoc xs y)).mp
      simpa only [snoc_values] using hb
    · intro hall y hy
      let b : I.Domain M := ⟨y (), by
        have he : (fun _ : Unit => y ()) = y := by funext i; cases i; rfl
        simpa only [he] using hy⟩
      have hb := (ih (Fin.snoc xs b)).mpr (hall b)
      simpa only [snoc_values] using hb

theorem realize_translate (h : I.GoodGraphs M) (A : L.Formula α) (v : α → I.Domain M) :
    letI := I.inducedStructure h
    (I.translate A).Realize (fun a => (v a).val) ↔ A.Realize v := by
  rw [translate, Formula.realize_relabel]
  have hv : (fun a => (v a).val) ∘ Sum.elim id (Fin.elim0 : Fin 0 → α) =
      Sum.elim (fun a => (v a).val) (fun i => (Fin.elim0 i : I.Domain M).val) := by
    funext a
    cases a with
    | inl i => rfl
    | inr i => exact i.elim0
  rw [hv]
  exact realize_translateAux h A v Fin.elim0

theorem existential_guard (h : I.GoodGraphs M) (A : L.Formula (α ⊕ Unit))
    (v : α → I.Domain M) :
    (I.translate (A.iExs Unit)).Realize (fun a => (v a).val) ↔
      ∃ y : M, I.domain.Realize (fun _ => y) ∧
        (I.translate A).Realize (Sum.elim (fun a => (v a).val) (fun _ => y)) := by
  let := I.inducedStructure h
  rw [realize_translate h]
  rw [Formula.realize_iExs]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(y ()).val, (y ()).property, ?_⟩
    have ht := (realize_translate h A (Sum.elim v y)).mpr hy
    rw [sum_values (I := I) v y] at ht
    have he : (fun i => (y i).val) = (fun _ : Unit => (y ()).val) := by
      funext i; cases i; rfl
    rwa [he] at ht
  · rintro ⟨y, hy, ht⟩
    refine ⟨fun _ => ⟨y, hy⟩, ?_⟩
    apply (realize_translate h A (Sum.elim v (fun _ => ⟨y, hy⟩))).mp
    rw [sum_values (I := I) v (fun _ : Unit => (⟨y, hy⟩ : I.Domain M))]
    exact ht

theorem realize_translateSentence (h : I.GoodGraphs M) (A : L.Sentence) :
    letI := I.inducedStructure h
    M ⊨ I.translateSentence A ↔ I.Domain M ⊨ A := by
  unfold Sentence.Realize translateSentence
  have he : (fun a : Empty => ((default : Empty → I.Domain M) a).val) = (default : Empty → M) := by
    funext a
    exact a.elim
  simpa only [he] using realize_translate h A (default : Empty → I.Domain M)

theorem relational_graphs [L.IsRelational] : I.GoodGraphs M := by
  intro n f
  exact isEmptyElim f


private theorem relationalTerm_realize [L.IsRelational] (h : I.GoodGraphs M)
    (t : L.Term α) (v : α → I.Domain M) :
    letI := I.inducedStructure h
    (relationalTerm (K := K) t).realize (fun a => (v a).val) = (t.realize v).val := by
  induction t with
  | var a => rfl
  | func f _ _ => exact isEmptyElim f

private theorem realize_relationalAux [L.IsRelational] (h : I.GoodGraphs M)
    {n : ℕ} (A : L.BoundedFormula α n) (v : α → I.Domain M) (xs : Fin n → I.Domain M) :
    letI := I.inducedStructure h
    (I.relationalAux A).Realize (Sum.elim (fun a => (v a).val) (fun i => (xs i).val)) ↔
      A.Realize v xs := by
  let := I.inducedStructure h
  induction A with
  | falsum => rfl
  | equal s t =>
    simp only [relationalAux, Formula.realize_equal, ← sum_values (I := I) v xs,
      relationalTerm_realize h, BoundedFormula.Realize]
    exact ⟨Subtype.ext, congrArg Subtype.val⟩
  | rel R ts =>
    rw [relationalAux, Formula.Realize, BoundedFormula.realize_subst]
    change (I.relationFormula R).Realize
      (fun i => (relationalTerm (ts i)).realize (Sum.elim (fun a => (v a).val)
        (fun j => (xs j).val))) ↔ _
    simp only [← sum_values (I := I) v xs, relationalTerm_realize h]
    rfl
  | imp A B ihA ihB =>
    simp only [relationalAux, Formula.realize_imp, BoundedFormula.Realize, ihA, ihB]
  | @all n A ih =>
    simp only [relationalAux, Formula.realize_iAlls, Formula.realize_imp,
      Formula.realize_relabel, Sum.elim_comp_inr, bindLast_values]
    change (∀ y : Unit → M, I.domain.Realize y →
      (I.relationalAux A).Realize
        (Sum.elim (fun a => (v a).val) (Fin.snoc (fun i => (xs i).val) (y ())))) ↔
      ∀ y : I.Domain M, A.Realize v (Fin.snoc xs y)
    constructor
    · intro hall y
      have hb := hall (fun _ => y.val) y.property
      apply (ih (Fin.snoc xs y)).mp
      simpa only [snoc_values] using hb
    · intro hall y hy
      let b : I.Domain M := ⟨y (), by
        have he : (fun _ : Unit => y ()) = y := by funext i; cases i; rfl
        simpa only [he] using hy⟩
      have hb := (ih (Fin.snoc xs b)).mpr (hall b)
      simpa only [snoc_values] using hb

theorem realize_relational [L.IsRelational] (h : I.GoodGraphs M)
    (A : L.Formula α) (v : α → I.Domain M) :
    letI := I.inducedStructure h
    (I.relational A).Realize (fun a => (v a).val) ↔ A.Realize v := by
  rw [relational, Formula.realize_relabel]
  have hv : (fun a => (v a).val) ∘ Sum.elim id (Fin.elim0 : Fin 0 → α) =
      Sum.elim (fun a => (v a).val) (fun i => (Fin.elim0 i : I.Domain M).val) := by
    funext a
    cases a with
    | inl i => rfl
    | inr i => exact i.elim0
  rw [hv]
  exact realize_relationalAux h A v Fin.elim0

theorem relational_graph_equivalent [L.IsRelational] (h : I.GoodGraphs M)
    (A : L.Formula α) (v : α → I.Domain M) :
    (I.relational A).Realize (fun a => (v a).val) ↔
      (I.translate A).Realize (fun a => (v a).val) := by
  exact (realize_relational h A v).trans (realize_translate h A v).symm

def Interprets (I : InterpretationData L K) (T : L.Theory) (S : K.Theory) : Prop :=
  I.Admissible S ∧ ∀ A ∈ T, Derives S (I.translateSentence A)

theorem models_induced {T : L.Theory} {S : K.Theory} (h : I.Interprets T S)
    [Nonempty M] [M ⊨ S] :
    letI := I.inducedStructure (I.good_of_admissible (M := M) h.1).2
    I.Domain M ⊨ T := by
  let := I.inducedStructure (I.good_of_admissible (M := M) h.1).2
  constructor
  intro A hA
  apply (realize_translateSentence (I.good_of_admissible (M := M) h.1).2 A).mp
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
  apply (realize_translateSentence hg.2 A).mpr
  exact derives_sound hp default (fun B hB => Theory.realize_sentence_of_mem T hB)

theorem consistent_transfer {T : L.Theory} {S : K.Theory} (h : I.Interprets T S)
    (hS : Consistent S) : Consistent T := by
  intro hp
  apply hS
  exact I.derives_translate h hp

theorem satisfiable_transfer {T : L.Theory} {S : K.Theory} (h : I.Interprets T S)
    (hS : S.IsSatisfiable) : T.IsSatisfiable := by
  let M := hS.some
  have hg := I.good_of_admissible (M := M) h.1
  let := I.inducedStructure hg.2
  let : Nonempty (I.Domain M) := hg.1
  let : I.Domain M ⊨ T := I.models_induced h
  exact Theory.Model.isSatisfiable (I.Domain M)

end InterpretationData
end
end Lemmatheca.MathematicalLogic.InterpretingTheories
