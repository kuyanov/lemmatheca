import Mathlib.Computability.Primrec.List
import Mathlib.Tactic.FunProp

/-! Compositional automation for primitive-recursive numerical programs.
These closure lemmas let `fun_prop` follow arithmetic and finite-list code. -/
namespace Lemmatheca.MathematicalLogic.PrimitiveRecursiveAutomation
attribute [fun_prop] Primrec
attribute [fun_prop] Primrec.const Primrec.id Primrec.comp Primrec.fst Primrec.snd Primrec.pair
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
@[fun_prop] theorem add {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x + g x) := Primrec.nat_add.comp hf hg
@[fun_prop] theorem sub {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x - g x) := Primrec.nat_sub.comp hf hg
@[fun_prop] theorem mul {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x * g x) := Primrec.nat_mul.comp hf hg
@[fun_prop] theorem max {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => Max.max (f x) (g x)) := Primrec.nat_max.comp hf hg
@[fun_prop] theorem pairNat {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => Nat.pair (f x) (g x)) := Primrec₂.natPair.comp hf hg
@[fun_prop] theorem unpair {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun x => Nat.unpair (f x)) := Primrec.unpair.comp hf
@[fun_prop] theorem eq {f g : α → β} [DecidableEq β] (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => decide (f x = g x)) := Primrec.eq.decide.comp hf hg
@[fun_prop] theorem le {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => decide (f x ≤ g x)) := Primrec.nat_le.decide.comp hf hg
@[fun_prop] theorem lt {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => decide (f x < g x)) := Primrec.nat_lt.decide.comp hf hg
@[fun_prop] theorem and {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x && g x) := (Primrec.dom_bool₂ Bool.and).comp hf hg
@[fun_prop] theorem or {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x || g x) := (Primrec.dom_bool₂ Bool.or).comp hf hg
@[fun_prop] theorem not {f : α → Bool} (hf : Primrec f) :
    Primrec (fun x => !(f x)) := (Primrec.dom_bool Bool.not).comp hf
@[fun_prop] theorem encode {f : α → β} (hf : Primrec f) :
    Primrec (fun x => Encodable.encode (f x)) := Primrec.encode.comp hf
@[fun_prop] theorem ofNat {δ : Type*} [Denumerable δ]
    {f : α → ℕ} (hf : Primrec f) : Primrec (fun x => Denumerable.ofNat δ (f x)) :=
  (Primrec.ofNat δ).comp hf
@[fun_prop] theorem listLength {f : α → List β} (hf : Primrec f) :
    Primrec (fun x => (f x).length) := Primrec.list_length.comp hf
@[fun_prop] theorem listTail {f : α → List β} (hf : Primrec f) :
    Primrec (fun x => (f x).tail) := Primrec.list_tail.comp hf
@[fun_prop] theorem listAppend {f g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x ++ g x) := Primrec.list_append.comp hf hg
@[fun_prop] theorem listRange {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun x => List.range (f x)) := Primrec.list_range.comp hf
@[fun_prop] theorem listCons {f : α → β} {g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x :: g x) := Primrec.list_cons.comp hf hg
@[fun_prop] theorem listGet {f : α → List β} {i : α → ℕ} (hf : Primrec f) (hi : Primrec i) :
    Primrec (fun x => (f x)[i x]?) := Primrec.list_getElem?.comp hf hi
@[fun_prop] theorem optionGet {f : α → Option β} {g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => (f x).getD (g x)) := Primrec.option_getD.comp hf hg
@[fun_prop] theorem listMap {f : α → List β} {g : α → β → γ}
    (hf : Primrec f) (hg : Primrec fun p : α × β => g p.1 p.2) :
    Primrec (fun x => (f x).map (g x)) := Primrec.list_map hf hg
@[fun_prop] theorem listFold {f : α → List β} {g : α → γ} {h : α → γ → β → γ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec fun p : α × (γ × β) => h p.1 p.2.1 p.2.2) :
    Primrec (fun x => (f x).foldl (h x) (g x)) := Primrec.list_foldl hf hg hh.to₂

@[fun_prop] theorem ite {c : α → Prop} [DecidablePred c] {f g : α → β}
    (hc : Primrec (fun x => decide (c x))) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => if c x then f x else g x) := Primrec.ite hc.primrecPred hf hg

@[fun_prop] theorem cond {c : α → Bool} {f g : α → β}
    (hc : Primrec c) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => _root_.cond (c x) (f x) (g x)) := Primrec.cond hc hf hg

@[fun_prop] theorem listAll {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec fun q : α × β => p q.1 q.2) :
    Primrec (fun x => (f x).all (p x)) := by
  have hh : Primrec fun q : α × (β × Bool) => p q.1 q.2.1 && q.2.2 := by fun_prop
  apply (Primrec.list_foldr hf (Primrec.const true) hh.to₂).of_eq
  intro x
  induction f x <;> simp_all

@[fun_prop] theorem listAny {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec fun q : α × β => p q.1 q.2) :
    Primrec (fun x => (f x).any (p x)) := by
  have hh : Primrec fun q : α × (β × Bool) => p q.1 q.2.1 || q.2.2 := by fun_prop
  apply (Primrec.list_foldr hf (Primrec.const false) hh.to₂).of_eq
  intro x
  induction f x <;> simp_all

@[fun_prop] theorem listIsEmpty {f : α → List β} (hf : Primrec f) :
    Primrec (fun x => (f x).isEmpty) := by
  exact ((Primrec.eq.comp (Primrec.list_length.comp hf) (Primrec.const 0)).decide).of_eq
    fun x => by cases f x <;> rfl

@[fun_prop] theorem listMem {f : α → β} {g : α → List β} [DecidableEq β]
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => decide (f x ∈ g x)) := by
  have hp : Primrec fun q : α × β => decide (q.2 = f q.1) := by fun_prop
  apply (listAny (p := fun x y => decide (y = f x)) hg hp).of_eq
  intro x
  apply Bool.eq_iff_iff.mpr
  simp
@[fun_prop] theorem natCases {f : α → ℕ} {g : α → β} {h : α → ℕ → β}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec fun p : α × ℕ => h p.1 p.2) :
    Primrec (fun x => (Nat.casesOn (f x) (g x) (h x) : β)) :=
  Primrec.nat_casesOn hf hg hh.to₂

theorem andPred {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : Primrec fun x => decide (p x)) (hq : Primrec fun x => decide (q x)) :
    Primrec (fun x => decide (p x ∧ q x)) := by
  simpa only [Bool.decide_and] using PrimitiveRecursiveAutomation.and hp hq

theorem orPred {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : Primrec fun x => decide (p x)) (hq : Primrec fun x => decide (q x)) :
    Primrec (fun x => decide (p x ∨ q x)) := by
  simpa only [Bool.decide_or] using PrimitiveRecursiveAutomation.or hp hq

@[fun_prop] theorem listZip [Inhabited β] [Inhabited γ]
    {f : α → List β} {g : α → List γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => (f x).zip (g x)) := by
  have hm : Primrec (fun x => min (f x).length (g x).length) :=
    Primrec.nat_min.comp (Primrec.list_length.comp hf) (Primrec.list_length.comp hg)
  have hi : Primrec (fun p : α × ℕ =>
      ((f p.1)[p.2]?.getD default, (g p.1)[p.2]?.getD default)) := by fun_prop
  apply (Primrec.list_map (Primrec.list_range.comp hm) hi.to₂).of_eq
  intro x
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hil : i < (f x).length := lt_of_lt_of_le (by simpa using hi) (min_le_left _ _)
    have hir : i < (g x).length := lt_of_lt_of_le (by simpa using hi) (min_le_right _ _)
    simp [hil, hir]

end Lemmatheca.MathematicalLogic.PrimitiveRecursiveAutomation
