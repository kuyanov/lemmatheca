import Lemmatheca.QuotientFirstOrderInterpretations.Core

namespace Lemmatheca.MathematicalLogic.QuotientInterpretations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.MathematicalLogic.DefinitionalExtensions (close)
universe u v u' v' w z
noncomputable section
variable {L : Language.{u,v}} {K : Language.{u',v'}} {d : ℕ}

/-- One native sentence for each equivalence or symbol-compatibility requirement. -/
inductive SideCondition (L : Language.{u,v}) : Type (max u v) where
  | nonempty | reflexive | symmetric | transitive
  | total {n : ℕ} (f : L.Functions n)
  | unique {n : ℕ} (f : L.Functions n)
  | graphs {n : ℕ} (f : L.Functions n)
  | relations {n : ℕ} (R : L.Relations n)

namespace InterpretationData
variable (I : InterpretationData L K d)

def domainAt {β : Type z} (x : Fin d → β) : K.Formula β := I.tuple.domain.relabel x

def equalityAt {β : Type z} (x y : Fin d → β) : K.Formula β :=
  I.equalityFormula.relabel (fun p =>
    Fin.cases (x p.2) (Fin.cases (y p.2) (fun k => Fin.elim0 k)) p.1)

def graphAt {β : Type z} {n : ℕ} (f : L.Functions n)
    (x : Fin n → Fin d → β) (y : Fin d → β) : K.Formula β :=
  (I.tuple.functionGraph f).relabel (Sum.elim (fun p => x p.1 p.2) y)

def guardedAt {β : Type z} {n : ℕ} (f : L.Functions n)
    (x : Fin n → Fin d → β) (y : Fin d → β) : K.Formula β :=
  I.domainAt y ⊓ I.graphAt f x y

def relationAt {β : Type z} {n : ℕ} (R : L.Relations n)
    (x : Fin n → Fin d → β) : K.Formula β :=
  (I.tuple.relationFormula (.inl R)).relabel (fun p => x p.1 p.2)

def inputDomains {β : Type z} {n : ℕ} (x : Fin n → Fin d → β) : K.Formula β :=
  Formula.iInf (fun i => I.domainAt (x i))

def inputEqualities {β : Type z} {n : ℕ} (x y : Fin n → Fin d → β) : K.Formula β :=
  Formula.iInf (fun i => I.equalityAt (x i) (y i))

/-- Actual finite native constructors, with domain guards on every tested block. -/
def sideSentence : SideCondition L → K.Sentence
  | .nonempty => I.tuple.nonemptySentence
  | .reflexive =>
      let b : Fin 1 → Fin d → Fin 1 × Fin d := fun i j => (i,j)
      close ((I.domainAt (b 0)).imp (I.equalityAt (b 0) (b 0)))
  | .symmetric =>
      let b : Fin 2 → Fin d → Fin 2 × Fin d := fun i j => (i,j)
      close ((I.inputDomains b).imp
        ((I.equalityAt (b 0) (b 1)).imp (I.equalityAt (b 1) (b 0))))
  | .transitive =>
      let b : Fin 3 → Fin d → Fin 3 × Fin d := fun i j => (i,j)
      close ((I.inputDomains b).imp ((I.equalityAt (b 0) (b 1)).imp
        ((I.equalityAt (b 1) (b 2)).imp (I.equalityAt (b 0) (b 2)))))
  | @SideCondition.total _ _n f =>
      close ((I.inputDomains (fun i j => (i,j))).imp
        ((I.tuple.guardedGraph f).iExs (Fin d)))
  | @SideCondition.unique _ n f =>
      let x : Fin n → Fin d → (Fin n ⊕ Fin 2) × Fin d := fun i j => (.inl i,j)
      let y : Fin d → (Fin n ⊕ Fin 2) × Fin d := fun j => (.inr 0,j)
      let z : Fin d → (Fin n ⊕ Fin 2) × Fin d := fun j => (.inr 1,j)
      close (((I.inputDomains x ⊓ I.guardedAt f x y) ⊓ I.guardedAt f x z).imp
        (I.equalityAt y z))
  | @SideCondition.graphs _ n f =>
      let x : Fin n → Fin d → ((Fin n ⊕ Fin n) ⊕ Fin 2) × Fin d :=
        fun i j => (.inl (.inl i),j)
      let x' : Fin n → Fin d → ((Fin n ⊕ Fin n) ⊕ Fin 2) × Fin d :=
        fun i j => (.inl (.inr i),j)
      let y : Fin d → ((Fin n ⊕ Fin n) ⊕ Fin 2) × Fin d := fun j => (.inr 0,j)
      let z : Fin d → ((Fin n ⊕ Fin n) ⊕ Fin 2) × Fin d := fun j => (.inr 1,j)
      close (((((I.inputDomains x ⊓ I.inputDomains x') ⊓ I.domainAt y) ⊓ I.domainAt z) ⊓
        (I.inputEqualities x x' ⊓ I.equalityAt y z)).imp
        ((I.graphAt f x y).iff (I.graphAt f x' z)))
  | @SideCondition.relations _ n R =>
      let x : Fin n → Fin d → (Fin n ⊕ Fin n) × Fin d := fun i j => (.inl i,j)
      let y : Fin n → Fin d → (Fin n ⊕ Fin n) × Fin d := fun i j => (.inr i,j)
      close (((I.inputDomains x ⊓ I.inputDomains y) ⊓ I.inputEqualities x y).imp
        ((I.relationAt R x).iff (I.relationAt R y)))

def Admissible (S : K.Theory) : Prop := ∀ c, Derives S (I.sideSentence c)

variable {M : Type w} [K.Structure M]

private theorem coordinate_domainAt {β : Type*} (a : β → I.Domain M) (x : β) :
    (I.domainAt (fun j => (x,j))).Realize (I.coordinates M a) ↔
      I.tuple.domain.Realize (a x).val := by
  rw [domainAt, Formula.realize_relabel]
  rfl

private theorem coordinate_equalityAt {β : Type*} (a : β → I.Domain M) (x y : β) :
    (I.equalityAt (fun j => (x,j)) (fun j => (y,j))).Realize (I.coordinates M a) ↔
      I.E M (a x) (a y) := by
  rw [equalityAt, Formula.realize_relabel]
  have he : I.coordinates M a ∘ (fun p : Fin 2 × Fin d =>
      Fin.cases (x,p.2) (Fin.cases (y,p.2) (fun k => Fin.elim0 k)) p.1) =
      I.coordinates M ![a x,a y] := by
    funext p
    rcases p with ⟨i,j⟩
    refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i <;> rfl
  rw [he]
  rfl

private theorem coordinate_graphAt {β : Type*} {n : ℕ} (a : β → I.Domain M)
    (f : L.Functions n) (x : Fin n → β) (y : β) :
    (I.graphAt f (fun i j => (x i,j)) (fun j => (y,j))).Realize (I.coordinates M a) ↔
      I.Graph M f (a ∘ x) (a y) := by
  rw [graphAt, Formula.realize_relabel]
  have he : I.coordinates M a ∘ Sum.elim (fun p : Fin n × Fin d => (x p.1,p.2))
      (fun j => (y,j)) = Sum.elim (I.coordinates M (a ∘ x)) (a y).val := by
    funext p
    cases p <;> rfl
  rw [he]
  rfl

private theorem coordinate_relationAt {β : Type*} {n : ℕ} (a : β → I.Domain M)
    (R : L.Relations n) (x : Fin n → β) :
    (I.relationAt R (fun i j => (x i,j))).Realize (I.coordinates M a) ↔
      I.Relation M R (a ∘ x) := by
  rw [relationAt, Formula.realize_relabel]
  rfl

private theorem coordinate_inputDomains {β : Type*} {n : ℕ} (a : β → I.Domain M)
    (x : Fin n → β) :
    (I.inputDomains (fun i j => (x i,j))).Realize (I.coordinates M a) := by
  simp only [inputDomains, Formula.realize_iInf, coordinate_domainAt]
  exact fun i => (a (x i)).property

private theorem coordinate_inputEqualities {β : Type*} {n : ℕ} (a : β → I.Domain M)
    (x y : Fin n → β) :
    (I.inputEqualities (fun i j => (x i,j)) (fun i j => (y i,j))).Realize
      (I.coordinates M a) ↔ ∀ i, I.E M (a (x i)) (a (y i)) := by
  simp only [inputEqualities, Formula.realize_iInf, coordinate_equalityAt]

private theorem raw_equalityAt {β : Type*} (v : β → M) (x y : Fin d → β)
    (hx : I.tuple.domain.Realize (v ∘ x)) (hy : I.tuple.domain.Realize (v ∘ y)) :
    (I.equalityAt x y).Realize v ↔ I.E M ⟨v ∘ x,hx⟩ ⟨v ∘ y,hy⟩ := by
  rw [equalityAt, Formula.realize_relabel]
  have he : v ∘ (fun p : Fin 2 × Fin d =>
      Fin.cases (x p.2) (Fin.cases (y p.2) (fun k => Fin.elim0 k)) p.1) =
      I.coordinates M ![(⟨v ∘ x,hx⟩ : I.Domain M), ⟨v ∘ y,hy⟩] := by
    funext p
    rcases p with ⟨i,j⟩
    refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i <;> rfl
  rw [he]
  rfl

private theorem raw_graphAt {β : Type*} {n : ℕ} (v : β → M)
    (f : L.Functions n) (x : Fin n → Fin d → β) (y : Fin d → β)
    (hx : ∀ i, I.tuple.domain.Realize (v ∘ x i)) (hy : I.tuple.domain.Realize (v ∘ y)) :
    (I.graphAt f x y).Realize v ↔
      I.Graph M f (fun i => ⟨v ∘ x i,hx i⟩) ⟨v ∘ y,hy⟩ := by
  rw [graphAt, Formula.realize_relabel]
  have he : v ∘ Sum.elim (fun p : Fin n × Fin d => x p.1 p.2) y =
      Sum.elim (I.coordinates M (fun i => (⟨v ∘ x i,hx i⟩ : I.Domain M))) (v ∘ y) := by
    funext p
    cases p <;> rfl
  rw [he]
  rfl

private theorem raw_relationAt {β : Type*} {n : ℕ} (v : β → M)
    (R : L.Relations n) (x : Fin n → Fin d → β)
    (hx : ∀ i, I.tuple.domain.Realize (v ∘ x i)) :
    (I.relationAt R x).Realize v ↔
      I.Relation M R (fun i => ⟨v ∘ x i,hx i⟩) := by
  rw [relationAt, Formula.realize_relabel]
  rfl

theorem side_sentences_iff_good : (∀ c, M ⊨ I.sideSentence c) ↔ I.Good M := by
  constructor
  · intro hc
    refine {
      nonempty := I.tuple.realize_nonemptySentence.mp (hc .nonempty)
      reflexive := ?_
      symmetric := ?_
      transitive := ?_
      total := ?_
      unique := ?_
      graphs := ?_
      relations := ?_ }
    · intro a
      have hr := hc .reflexive
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close] at hr
      have hh := hr (I.coordinates M (fun _ : Fin 1 => a))
      simp only [Formula.realize_imp, coordinate_domainAt, coordinate_equalityAt] at hh
      exact hh a.property
    · intro a b hab
      have hs := hc .symmetric
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close] at hs
      have hh := hs (I.coordinates M ![a,b])
      simp only [Formula.realize_imp, coordinate_equalityAt,
        Matrix.cons_val_zero, Matrix.cons_val_one] at hh
      exact hh (I.coordinate_inputDomains ![a,b] id) hab
    · intro a b c hab hbc
      have ht := hc .transitive
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close] at ht
      have hh := ht (I.coordinates M ![a,b,c])
      simp only [Formula.realize_imp, coordinate_equalityAt,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hh
      exact hh (I.coordinate_inputDomains ![a,b,c] id) hab hbc
    · intro n f a
      have ht := hc (.total f)
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close] at ht
      have hh := ht (I.coordinates M a)
      simp only [Formula.realize_imp, Formula.realize_iExs] at hh
      obtain ⟨y, hy⟩ := hh (I.coordinate_inputDomains a id)
      have hδ := (Formula.realize_inf.mp hy).1
      simp only [Formula.realize_relabel, Sum.elim_comp_inr] at hδ
      exact ⟨⟨y,hδ⟩, (I.graph_iff_guarded f a ⟨y,hδ⟩).mpr hy⟩
    · intro n f a y z hy hz
      have hu := hc (.unique f)
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close] at hu
      have hh := hu (I.coordinates M (Sum.elim a ![y,z]))
      simp only [Formula.realize_imp, Formula.realize_inf, guardedAt,
        coordinate_inputDomains, coordinate_domainAt, coordinate_graphAt,
        coordinate_equalityAt, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Function.comp_def] at hh
      exact hh ⟨⟨trivial, y.property, hy⟩, z.property, hz⟩
    · intro n f a b y z hab hyz
      have hg := hc (.graphs f)
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close] at hg
      have hh := hg (I.coordinates M (Sum.elim (Sum.elim a b) ![y,z]))
      simp only [Formula.realize_imp, Formula.realize_inf, Formula.realize_iff,
        coordinate_inputDomains, coordinate_domainAt, coordinate_graphAt,
        coordinate_inputEqualities, coordinate_equalityAt,
        Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, Function.comp_def] at hh
      exact hh ⟨⟨⟨⟨trivial,trivial⟩, y.property⟩, z.property⟩, hab, hyz⟩
    · intro n R a b hab
      have hR := hc (.relations R)
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close] at hR
      have hh := hR (I.coordinates M (Sum.elim a b))
      simp only [Formula.realize_imp, Formula.realize_inf, Formula.realize_iff,
        coordinate_inputDomains, coordinate_relationAt, coordinate_inputEqualities,
        Sum.elim_inl, Sum.elim_inr, Function.comp_def] at hh
      exact hh ⟨⟨trivial,trivial⟩, hab⟩
  · intro h c
    cases c with
    | nonempty => exact I.tuple.realize_nonemptySentence.mpr h.nonempty
    | reflexive =>
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close]
      intro v
      rw [Formula.realize_imp, domainAt, Formula.realize_relabel]
      intro hx
      exact (I.raw_equalityAt v _ _ hx hx).mpr (h.reflexive ⟨_,hx⟩)
    | symmetric =>
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close]
      intro v
      simp only [Formula.realize_imp, inputDomains, Formula.realize_iInf,
        domainAt, Formula.realize_relabel]
      intro hd he
      apply (I.raw_equalityAt v _ _ (hd 1) (hd 0)).mpr
      exact h.symmetric ((I.raw_equalityAt v _ _ (hd 0) (hd 1)).mp he)
    | transitive =>
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close]
      intro v
      simp only [Formula.realize_imp, inputDomains, Formula.realize_iInf,
        domainAt, Formula.realize_relabel]
      intro hd he he'
      apply (I.raw_equalityAt v _ _ (hd 0) (hd 2)).mpr
      exact h.transitive ((I.raw_equalityAt v _ _ (hd 0) (hd 1)).mp he)
        ((I.raw_equalityAt v _ _ (hd 1) (hd 2)).mp he')
    | @total n f =>
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close]
      intro v
      simp only [Formula.realize_imp, inputDomains, Formula.realize_iInf,
        domainAt, Formula.realize_relabel, Formula.realize_iExs]
      intro hd
      let a : Fin n → I.Domain M := fun i => ⟨fun j => v (i,j), hd i⟩
      obtain ⟨y,hy⟩ := h.total n f a
      exact ⟨y.val, (I.graph_iff_guarded f a y).mp hy⟩
    | @unique n f =>
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close]
      intro v
      simp only [Formula.realize_imp, Formula.realize_inf, inputDomains,
        Formula.realize_iInf, guardedAt, domainAt, Formula.realize_relabel]
      rintro ⟨⟨hd,hyδ,hy⟩,hzδ,hz⟩
      apply (I.raw_equalityAt v _ _ hyδ hzδ).mpr
      exact h.unique n f _ _ _ ((I.raw_graphAt v f _ _ hd hyδ).mp hy)
        ((I.raw_graphAt v f _ _ hd hzδ).mp hz)
    | @graphs n f =>
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close]
      intro v
      simp only [Formula.realize_imp, Formula.realize_inf, Formula.realize_iff,
        inputDomains, Formula.realize_iInf, inputEqualities,
        domainAt, Formula.realize_relabel]
      rintro ⟨⟨⟨⟨ha,hb⟩,hyδ⟩,hzδ⟩,hab,hyz⟩
      rw [I.raw_graphAt v f _ _ ha hyδ, I.raw_graphAt v f _ _ hb hzδ]
      apply h.graphs n f
      · intro i
        exact (I.raw_equalityAt v _ _ (ha i) (hb i)).mp (hab i)
      · exact (I.raw_equalityAt v _ _ hyδ hzδ).mp hyz
    | @relations n R =>
      rw [sideSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close]
      intro v
      simp only [Formula.realize_imp, Formula.realize_inf, Formula.realize_iff,
        inputDomains, Formula.realize_iInf, inputEqualities,
        domainAt, Formula.realize_relabel]
      rintro ⟨⟨ha,hb⟩,hab⟩
      rw [I.raw_relationAt v R _ ha, I.raw_relationAt v R _ hb]
      apply h.relations n R
      intro i
      exact (I.raw_equalityAt v _ _ (ha i) (hb i)).mp (hab i)
theorem good_of_admissible {S : K.Theory} (h : I.Admissible S)
    [Nonempty M] [M ⊨ S] : I.Good M := by
  apply I.side_sentences_iff_good.mp
  intro c
  exact derives_sound (h c) default (fun A hA => Theory.realize_sentence_of_mem S hA)

def Interprets (T : L.Theory) (S : K.Theory) : Prop :=
  I.Admissible S ∧ ∀ A ∈ T, Derives S (I.translateSentence A)

theorem models_induced {T : L.Theory} {S : K.Theory} (h : I.Interprets T S)
    [Nonempty M] [M ⊨ S] :
    I.QuotientDomain (I.good_of_admissible (M := M) h.1) ⊨ T := by
  constructor
  intro A hA
  apply (I.quotient_sentence_truth (I.good_of_admissible (M := M) h.1) A).mp
  exact derives_sound (h.2 A hA) default (fun B hB => Theory.realize_sentence_of_mem S hB)

theorem derives_translate {T : L.Theory} {S : K.Theory} (h : I.Interprets T S)
    {A : L.Sentence} (hp : Derives T A) : Derives S (I.translateSentence A) := by
  apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
  rw [Theory.models_sentence_iff]
  intro M
  have hg := I.good_of_admissible (M := M) h.1
  let : I.QuotientDomain hg ⊨ T := I.models_induced h
  apply (I.quotient_sentence_truth hg A).mpr
  exact derives_sound hp default (fun B hB => Theory.realize_sentence_of_mem T hB)

theorem consistent_transfer {T : L.Theory} {S : K.Theory} (h : I.Interprets T S)
    (hS : Consistent S) : Consistent T := by
  intro hp
  apply hS
  exact I.derives_translate h hp

end InterpretationData
end
end Lemmatheca.MathematicalLogic.QuotientInterpretations
