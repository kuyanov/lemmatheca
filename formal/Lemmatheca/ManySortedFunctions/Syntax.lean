import Lemmatheca.ManySortedLogic.ManySortedLogic

/-! Functional sorted syntax, simultaneous substitution and its semantics. -/
namespace Lemmatheca.MathematicalLogic.ManySortedFunctions
open FirstOrder FirstOrder.Language
universe u v w
structure Signature extends ManySortedLogic.Signature.{u,v} where
  Functions : ℕ → Type v
  input : ∀ {k}, Functions k → Fin k → Sorts
  output : ∀ {k}, Functions k → Sorts

variable (L : Signature.{u,v})
abbrev Context (n : ℕ) := Fin n → L.Sorts

inductive Term {n : ℕ} (γ : Context L n) : L.Sorts → Type (max u v)
  | var (i : Fin n) {s} (typed : γ i = s) : Term γ s
  | app {k} (f : L.Functions k) (ts : ∀ i, Term γ (L.input f i)) :
      Term γ (L.output f)

inductive Formula : {n : ℕ} → Context L n → Type (max u v)
  | falsum {n γ} : @Formula n γ
  | equal {n γ s} (t r : Term L γ s) : @Formula n γ
  | rel {n γ k} (r : L.Relations k) (ts : ∀ i, Term L γ (L.profile r i)) :
      @Formula n γ
  | imp {n γ} (p q : @Formula n γ) : @Formula n γ
  | all {n γ} (s : L.Sorts) (p : @Formula (n+1) (Fin.snoc γ s)) : @Formula n γ

namespace Term
variable {L} {n m : ℕ} {γ : Context L n} {δ : Context L m}
def cast {s t : L.Sorts} (h : s = t) (e : Term L γ s) : Term L γ t := h ▸ e

def rename (r : Fin n → Fin m) (h : ∀ i, δ (r i) = γ i) :
    {s : L.Sorts} → Term L γ s → Term L δ s
  | _, .var i ht => .var (r i) ((h i).trans ht)
  | _, .app f ts => .app f (fun i => rename r h (ts i))

def weaken {s : L.Sorts} {t : L.Sorts} (e : Term L γ t) :
    Term L (Fin.snoc γ s) t :=
  e.rename Fin.castSucc (by intro i; simp)

abbrev Substitution (γ : Context L n) (δ : Context L m) :=
  ∀ i, Term L δ (γ i)

def subst (σ : Substitution γ δ) : {s : L.Sorts} → Term L γ s → Term L δ s
  | _, .var i ht => cast ht (σ i)
  | _, .app f ts => .app f (fun i => subst σ (ts i))

def lift (σ : Substitution γ δ) (s : L.Sorts) :
    Substitution (Fin.snoc γ s) (Fin.snoc δ s) :=
  fun i => Fin.lastCases
    (.var (Fin.last m) (by simp))
    (fun j => cast (by simp) (σ j).weaken) i
end Term

namespace Formula
variable {L}
def subst {n m : ℕ} {γ : Context L n} {δ : Context L m}
    (σ : Term.Substitution γ δ) : Formula L γ → Formula L δ
  | .falsum => .falsum
  | .equal t r => .equal (t.subst σ) (r.subst σ)
  | .rel r ts => .rel r (fun i => (ts i).subst σ)
  | .imp p q => .imp (subst σ p) (subst σ q)
  | .all s p => .all s (subst (Term.lift σ s) p)
end Formula

structure Model where
  Carrier : L.Sorts → Type w
  nonempty : ∀ s, Nonempty (Carrier s)
  func : ∀ {k} (f : L.Functions k), (∀ i, Carrier (L.input f i)) → Carrier (L.output f)
  rel : ∀ {k} (r : L.Relations k), (∀ i, Carrier (L.profile r i)) → Prop

namespace Model
variable {L} (D : Model.{u,v,w} L)
abbrev Assignment {n} (γ : Context L n) := ∀ i, D.Carrier (γ i)
def assignSnoc {n} {γ : Context L n} (a : D.Assignment γ) {s} (x : D.Carrier s) :
    D.Assignment (Fin.snoc γ s) :=
  fun i => Fin.lastCases (by simpa using x) (fun j => by simpa using a j) i

def eval {n} {γ : Context L n} (a : D.Assignment γ) :
    {s : L.Sorts} → Term L γ s → D.Carrier s
  | _, .var i ht => ht ▸ a i
  | _, .app f ts => D.func f (fun i => eval a (ts i))

def Realize : {n : ℕ} → {γ : Context L n} → Formula L γ → D.Assignment γ → Prop
  | _, _, .falsum, _ => False
  | _, _, .equal t r, a => D.eval a t = D.eval a r
  | _, _, .rel r ts, a => D.rel r (fun i => D.eval a (ts i))
  | _, _, .imp p q, a => Realize p a → Realize q a
  | _, _, .all _ p, a => ∀ x, Realize p (D.assignSnoc a x)

def pull {n m} {γ : Context L n} {δ : Context L m}
    (σ : Term.Substitution γ δ) (a : D.Assignment δ) : D.Assignment γ :=
  fun i => D.eval a (σ i)

private theorem eval_cast_heq {n} {γ : Context L n} (a : D.Assignment γ)
    {s t : L.Sorts} (h : s = t) (e : Term L γ s) :
    HEq (D.eval a (h ▸ e)) (D.eval a e) := by
  cases h
  rfl

theorem eval_subst {n m} {γ : Context L n} {δ : Context L m}
    (σ : Term.Substitution γ δ) {s} (t : Term L γ s) (a : D.Assignment δ) :
    D.eval a (t.subst σ) = D.eval (D.pull σ a) t := by
  induction t with
  | var i h => cases h; rfl
  | app f ts ih =>
    simp only [Term.subst, eval]
    congr 1
    funext i
    exact ih i

theorem eval_weaken {n} {γ : Context L n} {s t} (e : Term L γ t)
    (a : D.Assignment γ) (x : D.Carrier s) :
    D.eval (D.assignSnoc a x) e.weaken = D.eval a e := by
  induction e with
  | var i h =>
    cases h
    simp only [Term.weaken, Term.rename, eval]
    apply eq_of_heq
    refine (eqRec_heq _ _).trans ?_
    simp only [assignSnoc, Fin.lastCases_castSucc]
    exact cast_heq _ _
  | app f ts ih =>
    simp only [Term.weaken, Term.rename, eval]
    congr 1
    funext i
    exact ih i

theorem pull_lift {n m} {γ : Context L n} {δ : Context L m}
    (σ : Term.Substitution γ δ) (a : D.Assignment δ) {s} (x : D.Carrier s) :
    D.pull (Term.lift σ s) (D.assignSnoc a x) = D.assignSnoc (D.pull σ a) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [pull, Term.lift, Fin.lastCases_last, eval, assignSnoc]
    apply eq_of_heq
    exact (eqRec_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm)
  · simp only [pull, Term.lift, Fin.lastCases_castSucc, Term.cast, assignSnoc]
    apply eq_of_heq
    exact ((eval_cast_heq D _ _ _).trans (heq_of_eq (D.eval_weaken (σ j) a x))).trans
      (cast_heq _ _).symm

theorem realize_subst {n m} {γ : Context L n} {δ : Context L m}
    (p : Formula L γ) (σ : Term.Substitution γ δ) (a : D.Assignment δ) :
    D.Realize (p.subst σ) a ↔ D.Realize p (D.pull σ a) := by
  induction p generalizing m with
  | falsum => rfl
  | equal t r => simp only [Formula.subst, Realize, eval_subst]
  | rel r ts => simp only [Formula.subst, Realize, eval_subst]
  | imp p q ihp ihq => exact imp_congr (ihp σ a) (ihq σ a)
  | all s p ih =>
    simp only [Formula.subst, Realize]
    apply forall_congr'
    intro x
    simpa only [pull_lift] using ih (Term.lift σ s) (D.assignSnoc a x)

def relationalReduct : ManySortedLogic.FamilyModel L.toSignature where
  Carrier := D.Carrier
  rel := D.rel
end Model

def includeRelational : {n : ℕ} → {γ : Context L n} →
    ManySortedLogic.Formula L.toSignature γ → Formula L γ
  | _, _, .falsum => .falsum
  | _, _, .equal i j h => .equal (.var i rfl) (.var j h.symm)
  | _, _, .rel r args h => .rel r (fun i => .var (args i) (h i))
  | _, _, .imp p q => .imp (includeRelational p) (includeRelational q)
  | _, _, .all s p => .all s (includeRelational p)

theorem realize_includeRelational (D : Model.{u,v,w} L) {n} {γ : Context L n}
    (p : ManySortedLogic.Formula L.toSignature γ) (a : D.Assignment γ) :
    D.Realize (includeRelational L p) a ↔ D.relationalReduct.Realize p a := by
  induction p with
  | falsum => rfl
  | equal i j h =>
    change (a i = (h.symm ▸ a j)) ↔ HEq (a i) (a j)
    constructor
    · intro heq
      exact (heq_of_eq heq).trans (eqRec_heq _ _)
    · intro heq
      exact eq_of_heq (heq.trans (eqRec_heq _ _).symm)
  | rel r args h => rfl
  | imp p q ihp ihq => exact imp_congr (ihp a) (ihq a)
  | all s p ih =>
    exact forall_congr' (fun x => ih (D.assignSnoc a x))

abbrev Sentence := Formula L (Fin.elim0 : Context L 0)
abbrev Theory := Set (Sentence L)
variable {L}
def Model.Models (D : Model.{u,v,w} L) (T : Theory L) : Prop :=
  ∀ p ∈ T, D.Realize p (fun i => Fin.elim0 i)
def IsSatisfiable (L : Signature.{u,v}) (T : Theory L) : Prop :=
  ∃ D : Model.{u,v,max u v} L, D.Models T

end Lemmatheca.MathematicalLogic.ManySortedFunctions
