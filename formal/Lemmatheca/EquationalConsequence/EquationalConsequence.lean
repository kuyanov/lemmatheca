import Mathlib.ModelTheory.Quotients
import Lemmatheca.TermUnification.TermUnification

/-! Equational proofs and their actual quotient term algebra. -/

namespace Lemmatheca.MathematicalLogic.EquationalConsequence

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}}

abbrev Identity (L : Language.{u, v}) := L.Term ℕ × L.Term ℕ

def Holds (A : Type w) [L.Structure A] (e : Identity L) : Prop :=
  ∀ a : ℕ → A, e.1.realize a = e.2.realize a

def Models (S : Set (Identity L)) (A : Type w) [L.Structure A] : Prop :=
  ∀ e ∈ S, Holds A e

def Consequence (S : Set (Identity L)) (s t : L.Term ℕ) : Prop :=
  ∀ (A : Type (max u w)) [L.Structure A] [Nonempty A], Models S A → Holds A (s, t)

inductive Derivable (S : Set (Identity L)) : L.Term ℕ → L.Term ℕ → Prop
  | hyp {s t} : (s, t) ∈ S → Derivable S s t
  | refl (t) : Derivable S t t
  | symm {s t} : Derivable S s t → Derivable S t s
  | trans {r s t} : Derivable S r s → Derivable S s t → Derivable S r t
  | congr {n} (f : L.Functions n) (s t : Fin n → L.Term ℕ) :
      (∀ i, Derivable S (s i) (t i)) → Derivable S (.func f s) (.func f t)
  | subst {s t} : Derivable S s t → (σ : ℕ → L.Term ℕ) →
      Derivable S (s.subst σ) (t.subst σ)

theorem soundness {S : Set (Identity L)} {s t : L.Term ℕ} (h : Derivable S s t)
    (A : Type w) [L.Structure A] (hA : Models S A) : Holds A (s, t) := by
  induction h with
  | hyp he => exact hA _ he
  | refl t => intro a; rfl
  | symm _ ih => intro a; exact (ih a).symm
  | trans _ _ ih₁ ih₂ => intro a; exact (ih₁ a).trans (ih₂ a)
  | congr f s t _ ih =>
      intro a
      change Structure.funMap f (fun i => (s i).realize a) =
        Structure.funMap f (fun i => (t i).realize a)
      exact congrArg (Structure.funMap f) (funext fun i => ih i a)
  | subst _ σ ih =>
      intro a
      simpa only [Term.realize_subst] using ih (fun x => (σ x).realize a)

structure InvariantCongruence (R : L.Term ℕ → L.Term ℕ → Prop) : Prop where
  equivalence : Equivalence R
  functions : ∀ {n} (f : L.Functions n) (s t : Fin n → L.Term ℕ),
    (∀ i, R (s i) (t i)) → R (.func f s) (.func f t)
  substitution : ∀ {s t}, R s t → ∀ σ : ℕ → L.Term ℕ, R (s.subst σ) (t.subst σ)

theorem derivability_congruence (S : Set (Identity L)) :
    InvariantCongruence (Derivable S) := by
  exact ⟨⟨Derivable.refl, Derivable.symm, Derivable.trans⟩,
    fun f s t h => Derivable.congr f s t h, fun h σ => Derivable.subst h σ⟩

theorem derivability_least (S : Set (Identity L))
    (R : L.Term ℕ → L.Term ℕ → Prop) (hR : InvariantCongruence R)
    (hS : ∀ e ∈ S, R e.1 e.2) {s t} (h : Derivable S s t) : R s t := by
  induction h with
  | hyp he => exact hS _ he
  | refl t => exact hR.equivalence.refl t
  | symm _ ih => exact hR.equivalence.symm ih
  | trans _ _ ih₁ ih₂ => exact hR.equivalence.trans ih₁ ih₂
  | congr f s t _ ih => exact hR.functions f s t ih
  | subst _ σ ih => exact hR.substitution ih σ

def termSetoid (S : Set (Identity L)) : Setoid (L.Term ℕ) where
  r := Derivable S
  iseqv := ⟨Derivable.refl, Derivable.symm, Derivable.trans⟩

abbrev TermQuotient (S : Set (Identity L)) := Quotient (termSetoid S)

def classOf (S : Set (Identity L)) (t : L.Term ℕ) : TermQuotient S :=
  Quotient.mk (termSetoid S) t

@[instance_reducible] def termStructure : L.Structure (L.Term ℕ) where
  funMap := Term.func
  RelMap := fun _ _ => False

@[instance_reducible] def termPrestructure (S : Set (Identity L)) :
    L.Prestructure (termSetoid S) where
  toStructure := termStructure
  fun_equiv s t h := Derivable.congr _ s t h
  rel_equiv _ _ _ := rfl

noncomputable instance equationalQuotientStructure (S : Set (Identity L)) :
    L.Structure (TermQuotient S) :=
  @FirstOrder.Language.quotientStructure L (L.Term ℕ) (termSetoid S) (termPrestructure S)

theorem quotient_nonempty (S : Set (Identity L)) : Nonempty (TermQuotient S) := by
  exact ⟨classOf S (.var 0)⟩

theorem quotient_function (S : Set (Identity L)) {n} (f : L.Functions n)
    (t : Fin n → L.Term ℕ) :
    Structure.funMap (L := L) f (fun i => classOf S (t i)) =
      classOf S (.func f t) := by
  exact @FirstOrder.Language.funMap_quotient_mk' L (L.Term ℕ) (termSetoid S)
    (termPrestructure S) n f t

theorem quotient_evaluation (S : Set (Identity L)) (t : L.Term ℕ)
    (σ : ℕ → L.Term ℕ) :
    t.realize (fun x => classOf S (σ x)) = classOf S (t.subst σ) := by
  induction t with
  | var => rfl
  | func f ts ih =>
      change Structure.funMap (L := L) f
        (fun i => (ts i).realize (fun x => classOf S (σ x))) = _
      simp_rw [ih]
      exact quotient_function S f (fun i => (ts i).subst σ)

def canonicalValuation (S : Set (Identity L)) : ℕ → TermQuotient S :=
  fun x => classOf S (.var x)

theorem canonical_evaluation (S : Set (Identity L)) (t : L.Term ℕ) :
    t.realize (canonicalValuation S) = classOf S t := by
  change t.realize (fun x => classOf S (.var x)) = classOf S t
  simpa only [FirstOrderProofs.term_subst_var] using quotient_evaluation S t Term.var

theorem quotient_model (S : Set (Identity L)) : Models S (TermQuotient S) := by
  intro e he a
  let σ : ℕ → L.Term ℕ := fun x => (a x).out
  have ha : (fun x => classOf S (σ x)) = a := by
    funext x
    exact Quotient.out_eq (a x)
  rw [← ha, quotient_evaluation, quotient_evaluation]
  exact Quotient.sound (Derivable.subst (Derivable.hyp he) σ)

theorem quotient_countermodel {S : Set (Identity L)} {s t : L.Term ℕ}
    (h : ¬ Derivable S s t) :
    Models S (TermQuotient S) ∧ Nonempty (TermQuotient S) ∧
      s.realize (canonicalValuation S) ≠ t.realize (canonicalValuation S) := by
  refine ⟨quotient_model S, quotient_nonempty S, ?_⟩
  rw [canonical_evaluation, canonical_evaluation]
  exact fun he => h (Quotient.exact he)

theorem completeness (S : Set (Identity L)) (s t : L.Term ℕ) :
    Derivable S s t ↔ Consequence.{u, v, w} S s t := by
  constructor
  · intro h A _ _ hA
    exact soundness h A hA
  · intro h
    by_contra hn
    let Q := TermQuotient S
    let : L.Structure (ULift.{w} Q) :=
      { funMap := fun f a => ULift.up (Structure.funMap f (fun i => (a i).down))
        RelMap := fun _ _ => False }
    let : Nonempty Q := quotient_nonempty S
    have heval (r : L.Term ℕ) (a : ℕ → ULift.{w} Q) :
        (r.realize a).down = r.realize (fun x => (a x).down) := by
      induction r with
      | var => rfl
      | func f ts ih =>
          change Structure.funMap (L := L) f (fun i => ((ts i).realize a).down) =
            Structure.funMap (L := L) f (fun i => (ts i).realize (fun x => (a x).down))
          exact congrArg (Structure.funMap f) (funext ih)
    have hmod : Models S (ULift.{w} Q) := by
      intro e he a
      apply ULift.ext
      rw [heval, heval]
      exact quotient_model S e he (fun x => (a x).down)
    have hs := h (ULift.{w} Q) hmod
      (fun x => ULift.up (canonicalValuation S x))
    have hd := congrArg ULift.down hs
    rw [heval, heval] at hd
    change s.realize (canonicalValuation S) = t.realize (canonicalValuation S) at hd
    rw [canonical_evaluation, canonical_evaluation] at hd
    exact hn (Quotient.exact hd)

theorem monotone {S Γ : Set (Identity L)} (hS : S ⊆ Γ) {s t}
    (h : Derivable S s t) : Derivable Γ s t := by
  induction h with
  | hyp he => exact Derivable.hyp (hS he)
  | refl t => exact Derivable.refl t
  | symm _ ih => exact Derivable.symm ih
  | trans _ _ ih₁ ih₂ => exact Derivable.trans ih₁ ih₂
  | congr f s t _ ih => exact Derivable.congr f s t ih
  | subst _ σ ih => exact Derivable.subst ih σ

theorem finite_premises {S : Set (Identity L)} {s t : L.Term ℕ}
    (h : Derivable S s t) :
    ∃ Γ : Set (Identity L), Γ.Finite ∧ Γ ⊆ S ∧ Derivable Γ s t := by
  classical
  induction h with
  | @hyp s t he =>
      exact ⟨{(s, t)}, Set.finite_singleton _, Set.singleton_subset_iff.mpr he,
        Derivable.hyp (Set.mem_singleton _)⟩
  | refl t => exact ⟨∅, Set.finite_empty, Set.empty_subset _, Derivable.refl t⟩
  | symm _ ih =>
      obtain ⟨Γ, hfin, hsub, hd⟩ := ih
      exact ⟨Γ, hfin, hsub, Derivable.symm hd⟩
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨Γ₁, hfin₁, hsub₁, hd₁⟩ := ih₁
      obtain ⟨Γ₂, hfin₂, hsub₂, hd₂⟩ := ih₂
      exact ⟨Γ₁ ∪ Γ₂, hfin₁.union hfin₂, Set.union_subset hsub₁ hsub₂,
        Derivable.trans (monotone Set.subset_union_left hd₁)
          (monotone Set.subset_union_right hd₂)⟩
  | @congr n f s t _ ih =>
      choose Γ hfin hsub hd using ih
      refine ⟨⋃ i, Γ i, Set.finite_iUnion hfin, ?_, Derivable.congr f s t ?_⟩
      · intro e he
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        exact hsub i hi
      · intro i
        exact monotone (Set.subset_iUnion Γ i) (hd i)
  | subst _ σ ih =>
      obtain ⟨Γ, hfin, hsub, hd⟩ := ih
      exact ⟨Γ, hfin, hsub, Derivable.subst hd σ⟩

theorem finite_consequence (S : Set (Identity L)) (s t : L.Term ℕ) :
    Consequence.{u, v, w} S s t ↔
      ∃ Γ : Set (Identity L), Γ.Finite ∧ Γ ⊆ S ∧ Consequence.{u, v, w} Γ s t := by
  constructor
  · intro h
    obtain ⟨Γ, hfin, hsub, hd⟩ := finite_premises ((completeness S s t).mpr h)
    exact ⟨Γ, hfin, hsub, (completeness Γ s t).mp hd⟩
  · rintro ⟨Γ, _, hsub, hΓ⟩
    exact (completeness S s t).mp (monotone hsub ((completeness Γ s t).mpr hΓ))

inductive ProjectionFunction : ℕ → Type
  | binary : ProjectionFunction 2

def projectionLanguage : Language := ⟨ProjectionFunction, fun _ => Empty⟩

def binary (s t : projectionLanguage.Term ℕ) : projectionLanguage.Term ℕ :=
  .func ProjectionFunction.binary ![s, t]

def projectionAxioms : Set (Identity projectionLanguage) :=
  {(binary (.var 0) (.var 1), .var 0)}

theorem nested_projection :
    Derivable projectionAxioms (binary (binary (.var 0) (.var 1)) (.var 2)) (.var 0) := by
  have ha : Derivable projectionAxioms (binary (.var 0) (.var 1)) (.var 0) :=
    Derivable.hyp (Set.mem_singleton _)
  let σ : ℕ → projectionLanguage.Term ℕ :=
    fun j => if j = 0 then binary (.var 0) (.var 1)
      else if j = 1 then .var 2 else .var j
  have hi : Derivable projectionAxioms
      (binary (binary (.var 0) (.var 1)) (.var 2)) (binary (.var 0) (.var 1)) := by
    have hs : (binary (.var 0) (.var 1)).subst σ =
        binary (binary (.var 0) (.var 1)) (.var 2) := by
      simp only [binary, Term.subst]
      congr 1
      funext i
      fin_cases i <;> rfl
    have hi := Derivable.subst ha σ
    rw [hs] at hi
    exact hi
  exact Derivable.trans hi ha

instance projectionBoolStructure : projectionLanguage.Structure Bool where
  funMap f a := by cases f; exact a 0
  RelMap r _ := Empty.elim r

theorem projection_satisfies : Models projectionAxioms Bool := by
  intro e he a
  obtain rfl := Set.mem_singleton_iff.mp he
  rfl

theorem projection_nonconsequence :
    ¬ Holds Bool (binary (.var 0) (.var 1), .var 1) ∧
    ¬ Holds Bool (Term.var 0, (Term.var 1 : projectionLanguage.Term ℕ)) ∧
    ¬ Derivable projectionAxioms (binary (.var 0) (.var 1)) (.var 1) ∧
    ¬ Derivable projectionAxioms (.var 0) (.var 1) := by
  have h₁ : ¬ Holds Bool (binary (.var 0) (.var 1), .var 1) := by
    intro h
    have hf := h (fun j => if j = 1 then true else false)
    change false = true at hf
    exact Bool.false_ne_true hf
  have h₂ : ¬ Holds Bool (Term.var 0, (Term.var 1 : projectionLanguage.Term ℕ)) := by
    intro h
    have hf := h (fun j => if j = 1 then true else false)
    change false = true at hf
    exact Bool.false_ne_true hf
  exact ⟨h₁, h₂, fun hd => h₁ (soundness hd Bool projection_satisfies),
    fun hd => h₂ (soundness hd Bool projection_satisfies)⟩

instance equationalEmptyBoolStructure : Language.empty.Structure Bool := Language.emptyStructure

theorem projection_separation :
    let v : ℕ → Bool := fun j => if j = 1 then true else false
    (binary (.var 0) (.var 1)).realize v = false ∧
      (Term.var 0 : projectionLanguage.Term ℕ).realize v = false ∧
      (Term.var 1 : projectionLanguage.Term ℕ).realize v = true := by
  exact ⟨rfl, rfl, rfl⟩

theorem single_valuation_counterexample :
    let v : ℕ → Bool := fun j => if j = 2 then true else false
    let σ : ℕ → Language.empty.Term ℕ := fun j => if j = 0 then .var 2 else .var j
    (Term.var 0 : Language.empty.Term ℕ).realize v = (Term.var 1 : Language.empty.Term ℕ).realize v ∧
      ((Term.var 0 : Language.empty.Term ℕ).subst σ).realize v ≠
        ((Term.var 1 : Language.empty.Term ℕ).subst σ).realize v := by
  exact ⟨rfl, Bool.false_ne_true.symm⟩

end Lemmatheca.MathematicalLogic.EquationalConsequence
