import Lemmatheca.RankReflection.Syntax
import Lemmatheca.Absoluteness.Absoluteness
import Mathlib.SetTheory.Ordinal.Family

/-! These are external semantic constructions in the universe-relative ZFSet
model. They do not encode definability in first-order ZF, its Replacement schema,
or a single internal truth predicate for a proper class. The corresponding
foundation-strength assertions are recorded separately as unbound nodes. -/
namespace Lemmatheca.SetTheory.RankReflection
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
universe u
noncomputable section

structure Hierarchy where
  level : Ordinal.{u} → ZFSet.{u}
  transitive : ∀ a, (level a).IsTransitive
  monotone : ∀ {a b}, a ≤ b → level a ⊆ level b
  continuous : ∀ l, Order.IsSuccLimit l → ∀ x,
    x ∈ level l ↔ ∃ a < l, x ∈ level a

def InUnion (H : Hierarchy.{u}) (x : ZFSet.{u}) : Prop := ∃ a, x ∈ H.level a
abbrev UnionDomain (H : Hierarchy.{u}) := {x : ZFSet.{u} // InUnion H x}
def NonemptyUnion (H : Hierarchy.{u}) : Prop := ∃ a, (H.level a).Nonempty
def intoUnion (H : Hierarchy.{u}) (a : Ordinal.{u}) (x : H.level a) : UnionDomain H :=
  ⟨x.val,a,x.property⟩

theorem union_transitive (H : Hierarchy.{u}) {x y : ZFSet.{u}}
    (hx : x ∈ y) (hy : InUnion H y) : InUnion H x := by
  obtain ⟨a,ha⟩ := hy
  exact ⟨a,H.transitive a y ha hx⟩

def unionSatisfies (H : Hierarchy.{u}) {n}
    (p : membershipLanguage.BoundedFormula Empty n) (a : Fin n → UnionDomain H) : Prop :=
  nativeSatisfies (fun x y : UnionDomain H => x.val ∈ y.val) p a

def Reflects (H : Hierarchy.{u}) (F : Finset PackedFormula) (a : Ordinal.{u}) : Prop :=
  (H.level a).Nonempty ∧ ∀ p ∈ F, ∀ xs : Fin p.1 → H.level a,
    setSatisfies (H.level a) p.2.toShared xs ↔
      unionSatisfies H p.2.toShared (fun i => intoUnion H a (xs i))

def ReflectsNative (H : Hierarchy.{u}) (F : Finset NativePackedFormula)
    (a : Ordinal.{u}) : Prop :=
  (H.level a).Nonempty ∧ ∀ p ∈ F, ∀ xs : Fin p.1 → H.level a,
    setSatisfies (H.level a) p.2 xs ↔
      unionSatisfies H p.2 (fun i => intoUnion H a (xs i))

def HasWitness (H : Hierarchy.{u}) {a : Ordinal.{u}} {n} (p : Formula (n+1))
    (xs : Fin n → H.level a) : Prop :=
  ∃ b : UnionDomain H,
    unionSatisfies H p.toShared (Fin.snoc (fun i => intoUnion H a (xs i)) b)

def WitnessAt (H : Hierarchy.{u}) {a : Ordinal.{u}} {n} (p : Formula (n+1))
    (xs : Fin n → H.level a) (b : Ordinal.{u}) : Prop :=
  ∃ z : UnionDomain H, z.val ∈ H.level b ∧
    unionSatisfies H p.toShared (Fin.snoc (fun i => intoUnion H a (xs i)) z)

def leastWitnessLevel (H : Hierarchy.{u}) {a : Ordinal.{u}} {n}
    (p : Formula (n+1)) (xs : Fin n → H.level a) : Ordinal.{u} := by
  classical
  exact if HasWitness H p xs then sInf {b | WitnessAt H p xs b} else 0

theorem leastWitnessLevel_spec (H : Hierarchy.{u}) {a : Ordinal.{u}} {n}
    (p : Formula (n+1)) (xs : Fin n → H.level a) (hw : HasWitness H p xs) :
    IsLeast {b | WitnessAt H p xs b} (leastWitnessLevel H p xs) := by
  classical
  have hn : ({b | WitnessAt H p xs b} : Set Ordinal.{u}).Nonempty := by
    obtain ⟨z,hz⟩ := hw
    obtain ⟨b,hb⟩ := z.property
    exact ⟨b,z,hb,hz⟩
  simp only [leastWitnessLevel,ite_eq_left hw]
  exact ⟨csInf_mem hn,fun b hb => csInf_le ⟨0,fun _ _ => bot_le⟩ hb⟩

theorem leastWitnessLevel_no_witness (H : Hierarchy.{u}) {a : Ordinal.{u}} {n}
    (p : Formula (n+1)) (xs : Fin n → H.level a) (hw : ¬HasWitness H p xs) :
    leastWitnessLevel H p xs = 0 := by
  simp only [leastWitnessLevel,ite_eq_right hw]

abbrev Requests (H : Hierarchy.{u}) (F : Finset PackedFormula) (a : Ordinal.{u}) :=
  Σ p : {p // p ∈ closure F}, Fin p.val.1 → H.level a

def requestLevel (H : Hierarchy.{u}) (F : Finset PackedFormula) (a : Ordinal.{u})
    (r : Requests H F a) : Ordinal.{u} :=
  match r.1.val.2, r.2 with
  | .ex p, xs => leastWitnessLevel H p xs
  | _, _ => 0

/-- Nonexistential requests contribute only 1, already bounded by a+1; this
therefore equals the displayed supremum over existential witness bounds. -/
def witnessBound (H : Hierarchy.{u}) (F : Finset PackedFormula) (a : Ordinal.{u}) :
    Ordinal.{u} := max (a+1) (⨆ r : Requests H F a, requestLevel H F a r + 1)

def existentialBounds (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (a : Ordinal.{u}) : Set Ordinal.{u} :=
  {b | ∃ (n : ℕ) (p : Formula (n+1)), (⟨n,Formula.ex p⟩ : PackedFormula) ∈ closure F ∧
    ∃ xs : Fin n → H.level a, b = leastWitnessLevel H p xs}

theorem witnessBound_exact_sup (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (a : Ordinal.{u}) : witnessBound H F a =
      sSup ({a+1} ∪ (fun b => b+1) '' existentialBounds H F a) := by
  classical
  let S : Set Ordinal.{u} := {a+1} ∪ (fun b => b+1) '' existentialBounds H F a
  have hreq (r : Requests H F a) : requestLevel H F a r + 1 ≤ witnessBound H F a :=
    (Ordinal.le_iSup (fun r : Requests H F a => requestLevel H F a r + 1) r).trans
      (le_max_right _ _)
  have hex (b : Ordinal.{u}) (hb : b ∈ existentialBounds H F a) : b+1 ≤ witnessBound H F a := by
    obtain ⟨n,p,hp,xs,rfl⟩ := hb
    exact hreq ⟨⟨⟨n,Formula.ex p⟩,hp⟩,xs⟩
  have hbdd : BddAbove S := by
    refine ⟨witnessBound H F a,?_⟩
    intro x hx
    rcases hx with hx | hx
    · obtain rfl := hx
      exact le_max_left _ _
    · obtain ⟨b,hb,rfl⟩ := hx
      exact hex b hb
  have hstart : a+1 ≤ sSup S := le_csSup hbdd (Or.inl rfl)
  have hone : 1 ≤ sSup S := by
    have hh : (0 : Ordinal.{u})+1 ≤ a+1 := add_le_add_left (show (0 : Ordinal.{u}) ≤ a from bot_le) 1
    rw [zero_add] at hh
    exact hh.trans hstart
  change witnessBound H F a = sSup S
  apply le_antisymm
  · apply max_le hstart
    apply Ordinal.iSup_le
    rintro ⟨⟨⟨n,p⟩,hp⟩,xs⟩
    cases p with
    | ex p =>
      exact le_csSup hbdd (Or.inr ⟨leastWitnessLevel H p xs,⟨n,p,hp,xs,rfl⟩,rfl⟩)
    | falsum => simpa only [requestLevel,zero_add] using hone
    | equal _ _ => simpa only [requestLevel,zero_add] using hone
    | mem _ _ => simpa only [requestLevel,zero_add] using hone
    | neg _ => simpa only [requestLevel,zero_add] using hone
    | conj _ _ => simpa only [requestLevel,zero_add] using hone
  · apply csSup_le ⟨a+1,Or.inl rfl⟩
    intro x hx
    rcases hx with hx | hx
    · obtain rfl := hx
      exact le_max_left _ _
    · obtain ⟨b,hb,rfl⟩ := hx
      exact hex b hb

theorem witnessBound_grows (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (a : Ordinal.{u}) : a < witnessBound H F a := by
  exact lt_of_lt_of_le (lt_add_one a) (le_max_left _ _)

theorem witnessBound_spec (H : Hierarchy.{u}) (F : Finset PackedFormula)
    {a : Ordinal.{u}} {n} (p : Formula (n+1))
    (hp : (⟨n,Formula.ex p⟩ : PackedFormula) ∈ closure F)
    (xs : Fin n → H.level a) (hw : HasWitness H p xs) :
    WitnessAt H p xs (witnessBound H F a) := by
  classical
  obtain ⟨z,hz,ht⟩ := (leastWitnessLevel_spec H p xs hw).1
  let r : Requests H F a := ⟨⟨⟨n,Formula.ex p⟩,hp⟩,xs⟩
  have hb : leastWitnessLevel H p xs ≤ witnessBound H F a := by
    apply le_trans (le_add_right (le_refl _) : leastWitnessLevel H p xs ≤ leastWitnessLevel H p xs + 1)
    exact (Ordinal.le_iSup (fun r : Requests H F a => requestLevel H F a r + 1) r).trans
      (le_max_right _ _)
  exact ⟨z,H.monotone hb hz,ht⟩

def closureSequence (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (start : Ordinal.{u}) (n : ℕ) : Ordinal.{u} := (witnessBound H F)^[n] start
def closureHeight (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (start : Ordinal.{u}) : Ordinal.{u} := ⨆ n : ℕ, closureSequence H F start n

theorem closureSequence_spec (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (start : Ordinal.{u}) :
    closureSequence H F start 0 = start ∧
    (∀ n, closureSequence H F start (n+1) = witnessBound H F (closureSequence H F start n)) ∧
    StrictMono (closureSequence H F start) ∧
    (∀ n, closureSequence H F start n < closureHeight H F start) ∧
    Order.IsSuccLimit (closureHeight H F start) ∧ start < closureHeight H F start := by
  have hs (n : ℕ) : closureSequence H F start (n+1) =
      witnessBound H F (closureSequence H F start n) :=
    Function.iterate_succ_apply' _ _ _
  have hmono : StrictMono (closureSequence H F start) :=
    strictMono_nat_of_lt_succ (fun n => by rw [hs]; exact witnessBound_grows H F _)
  have hlt (n : ℕ) : closureSequence H F start n < closureHeight H F start :=
    (hmono (Nat.lt_succ_self n)).trans_le (Ordinal.le_iSup (closureSequence H F start) (n+1))
  have hzero : (0 : Ordinal.{u}) < closureHeight H F start :=
    (show (0 : Ordinal.{u}) ≤ start from bot_le).trans_lt (hlt 0)
  have hlim : Order.IsSuccLimit (closureHeight H F start) := by
    rw [Ordinal.isSuccLimit_iff,Order.isSuccPrelimit_iff_succ_lt]
    exact ⟨hzero.ne',fun _ ha => Ordinal.succ_lt_iSup_of_ne_iSup (fun n => (hlt n).ne) ha⟩
  exact ⟨rfl,hs,hmono,hlt,hlim,hlt 0⟩

theorem closureHeight_members (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (start : Ordinal.{u}) (x : ZFSet.{u}) :
    x ∈ H.level (closureHeight H F start) ↔
      ∃ n, x ∈ H.level (closureSequence H F start n) := by
  rw [H.continuous _ (closureSequence_spec H F start).2.2.2.2.1]
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨n,hn⟩ := Ordinal.lt_iSup_iff.mp ha
    exact ⟨n,H.monotone hn.le hx⟩
  · rintro ⟨n,hx⟩
    exact ⟨closureSequence H F start n,(closureSequence_spec H F start).2.2.2.1 n,hx⟩

theorem finite_tuple_stage (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (start : Ordinal.{u}) {n} (xs : Fin n → H.level (closureHeight H F start)) :
    ∃ k : ℕ, ∀ i, (xs i).val ∈ H.level (closureSequence H F start k) := by
  classical
  have he (i : Fin n) := (closureHeight_members H F start (xs i).val).mp (xs i).property
  let idx (i : Fin n) : ℕ := (he i).choose
  refine ⟨Finset.univ.sup idx,?_⟩
  intro i
  exact H.monotone ((closureSequence_spec H F start).2.2.1.monotone
    (Finset.le_sup (Finset.mem_univ i))) (he i).choose_spec

def WitnessClosed (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (a : Ordinal.{u}) : Prop :=
  ∀ n (p : Formula (n+1)), (⟨n,Formula.ex p⟩ : PackedFormula) ∈ closure F →
    ∀ xs : Fin n → H.level a, HasWitness H p xs → WitnessAt H p xs a

theorem closureHeight_witnessClosed (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (start : Ordinal.{u}) : WitnessClosed H F (closureHeight H F start) := by
  intro n p hp xs hw
  obtain ⟨k,hk⟩ := finite_tuple_stage H F start xs
  let ys : Fin n → H.level (closureSequence H F start k) := fun i => ⟨(xs i).val,hk i⟩
  have hw' : HasWitness H p ys := hw
  obtain ⟨z,hz,ht⟩ := witnessBound_spec H F p hp ys hw'
  have hs := (closureSequence_spec H F start).2.1 k
  rw [← hs] at hz
  exact ⟨z,H.monotone ((closureSequence_spec H F start).2.2.2.1 (k+1)).le hz,ht⟩

private theorem self_subformulas {n} (p : Formula n) :
    (⟨n,p⟩ : PackedFormula) ∈ subformulas p := by
  cases p <;> simp [subformulas]
private theorem scope_not {M : Type*} (E : M → M → Prop) {n}
    (p : membershipLanguage.BoundedFormula Empty n) (a : Fin n → M) :
    nativeSatisfies E p.not a ↔ ¬nativeSatisfies E p a := Iff.rfl
private theorem scope_inf {M : Type*} (E : M → M → Prop) {n}
    (p q : membershipLanguage.BoundedFormula Empty n) (a : Fin n → M) :
    nativeSatisfies E (p ⊓ q) a ↔ nativeSatisfies E p a ∧ nativeSatisfies E q a := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  exact BoundedFormula.realize_inf
private theorem scope_ex {M : Type*} (E : M → M → Prop) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+1)) (a : Fin n → M) :
    nativeSatisfies E p.ex a ↔ ∃ x, nativeSatisfies E p (Fin.snoc a x) := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  exact BoundedFormula.realize_ex

theorem reflection_of_witnessClosed (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (a : Ordinal.{u}) (hne : (H.level a).Nonempty) (hc : WitnessClosed H F a) :
    Reflects H (closure F) a := by
  classical
  refine ⟨hne,?_⟩
  suffices he : ∀ {n} (p : Formula n), (⟨n,p⟩ : PackedFormula) ∈ closure F →
      ∀ xs : Fin n → H.level a, setSatisfies (H.level a) p.toShared xs ↔
        unionSatisfies H p.toShared (fun i => intoUnion H a (xs i)) by
    exact fun p hp xs => he p.2 hp xs
  intro n p
  induction p with
  | falsum => intro _ _; rfl
  | equal i j =>
    intro _ xs
    change xs i = xs j ↔ intoUnion H a (xs i) = intoUnion H a (xs j)
    simp only [Subtype.ext_iff]
    rfl
  | mem i j => intro _ _; rfl
  | @neg n p ih =>
    intro hp xs
    have hb : (⟨n,p⟩ : PackedFormula) ∈ closure F :=
      closure_subformulas F ⟨n,Formula.neg p⟩ hp (Finset.mem_insert_of_mem (self_subformulas p))
    exact not_congr (ih hb xs)
  | @conj n p q ihp ihq =>
    intro hp xs
    have hb := closure_subformulas F ⟨n,Formula.conj p q⟩ hp
    have hp' : (⟨n,p⟩ : PackedFormula) ∈ closure F := hb
      (Finset.mem_insert_of_mem (Finset.mem_union_left _ (self_subformulas p)))
    have hq' : (⟨n,q⟩ : PackedFormula) ∈ closure F := hb
      (Finset.mem_insert_of_mem (Finset.mem_union_right _ (self_subformulas q)))
    simp only [Formula.toShared,setSatisfies,unionSatisfies,scope_inf]
    exact and_congr (ihp hp' xs) (ihq hq' xs)
  | @ex n p ih =>
    intro hp xs
    have hb : (⟨n+1,p⟩ : PackedFormula) ∈ closure F :=
      closure_subformulas F ⟨n,Formula.ex p⟩ hp (Finset.mem_insert_of_mem (self_subformulas p))
    change nativeSatisfies (fun x y : H.level a => x.val ∈ y.val) p.toShared.ex xs ↔
      nativeSatisfies (fun x y : UnionDomain H => x.val ∈ y.val) p.toShared.ex
        (fun i => intoUnion H a (xs i))
    rw [scope_ex,scope_ex]
    have hm (x : H.level a) :
        (fun i => intoUnion H a ((Fin.snoc (α := fun _ : Fin (n+1) => H.level a) xs x) i)) =
          Fin.snoc (fun i => intoUnion H a (xs i)) (intoUnion H a x) :=
      Fin.comp_snoc (intoUnion H a) xs x
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨intoUnion H a x,?_⟩
      simpa only [unionSatisfies,hm] using (ih hb (Fin.snoc xs x)).mp hx
    · rintro ⟨z,hz⟩
      obtain ⟨w,hw,ht⟩ := hc n p hp xs ⟨z,hz⟩
      let x : H.level a := ⟨w.val,hw⟩
      refine ⟨x,(ih hb (Fin.snoc xs x)).mpr ?_⟩
      have hxw : intoUnion H a x = w := Subtype.ext rfl
      rw [hm,hxw]
      exact ht

def initialLevel (H : Hierarchy.{u}) (theta : Ordinal.{u}) : Ordinal.{u} :=
  sInf {a | theta < a ∧ (H.level a).Nonempty}
def reflectingHeight (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (theta : Ordinal.{u}) : Ordinal.{u} := closureHeight H F (initialLevel H theta)

theorem initialLevel_spec (H : Hierarchy.{u}) (hne : NonemptyUnion H)
    (theta : Ordinal.{u}) : theta < initialLevel H theta ∧
      (H.level (initialLevel H theta)).Nonempty := by
  obtain ⟨a,x,hx⟩ := hne
  have hn : ({b | theta < b ∧ (H.level b).Nonempty} : Set Ordinal.{u}).Nonempty := by
    refine ⟨max a (theta+1),?_,x,H.monotone (le_max_left _ _) hx⟩
    exact lt_of_lt_of_le (lt_add_one theta) (le_max_right _ _)
  exact csInf_mem hn

theorem reflectingHeight_spec (H : Hierarchy.{u}) (hne : NonemptyUnion H)
    (F : Finset PackedFormula) (theta : Ordinal.{u}) :
    theta < reflectingHeight H F theta ∧ Order.IsSuccLimit (reflectingHeight H F theta) ∧
      Reflects H (closure F) (reflectingHeight H F theta) := by
  have hinit := initialLevel_spec H hne theta
  have hs := closureSequence_spec H F (initialLevel H theta)
  refine ⟨hinit.1.trans hs.2.2.2.2.2,hs.2.2.2.2.1,?_⟩
  apply reflection_of_witnessClosed H F _
  · obtain ⟨x,hx⟩ := hinit.2
    exact ⟨x,H.monotone hs.2.2.2.2.2.le hx⟩
  · exact closureHeight_witnessClosed H F _

theorem native_reflectingHeight_spec (H : Hierarchy.{u}) (hne : NonemptyUnion H)
    (F : Finset NativePackedFormula) (theta : Ordinal.{u}) :
    theta < reflectingHeight H (expandFamily F) theta ∧
    Order.IsSuccLimit (reflectingHeight H (expandFamily F) theta) ∧
    ReflectsNative H F (reflectingHeight H (expandFamily F) theta) := by
  obtain ⟨ht,hl,hn,hr⟩ := reflectingHeight_spec H hne (expandFamily F) theta
  refine ⟨ht,hl,hn,?_⟩
  intro p hp xs
  let q : PackedFormula := ⟨p.1,Formula.ofShared p.2⟩
  have hq : q ∈ closure (expandFamily F) :=
    closure_contains _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  exact (Formula.ofShared_realize (fun x y : H.level _ => x.val ∈ y.val) p.2 xs).symm.trans
    ((hr q hq xs).trans (Formula.ofShared_realize
      (fun x y : UnionDomain H => x.val ∈ y.val) p.2 (fun i => intoUnion H _ (xs i))))

theorem closed_reflecting_levels (H : Hierarchy.{u}) (F : Finset PackedFormula)
    (l : Ordinal.{u}) (hl : Order.IsSuccLimit l)
    (hc : ∀ a < l, ∃ b, a ≤ b ∧ b < l ∧ Reflects H (closure F) b) :
    Reflects H (closure F) l := by
  classical
  have hne : (H.level l).Nonempty := by
    obtain ⟨b,_,hb,hn,_⟩ := hc 0 hl.bot_lt
    obtain ⟨x,hx⟩ := hn
    exact ⟨x,H.monotone hb.le hx⟩
  apply reflection_of_witnessClosed H F l hne
  intro n p hp xs hw
  have he (i : Fin n) := (H.continuous l hl (xs i).val).mp (xs i).property
  let idx (i : Fin n) : Ordinal.{u} := (he i).choose
  let t := Finset.univ.sup idx
  have ht : t < l := by
    exact (Finset.sup_lt_iff hl.bot_lt).mpr (fun i _ => (he i).choose_spec.1)
  obtain ⟨b,htb,hbl,hn,hr⟩ := hc t ht
  have hxs (i : Fin n) : (xs i).val ∈ H.level b :=
    H.monotone ((Finset.le_sup (Finset.mem_univ i)).trans htb) (he i).choose_spec.2
  let ys : Fin n → H.level b := fun i => ⟨(xs i).val,hxs i⟩
  have hclass : unionSatisfies H (Formula.ex p).toShared
      (fun i => intoUnion H b (ys i)) := by
    change nativeSatisfies _ p.toShared.ex _
    exact (scope_ex _ _ _).mpr hw
  have hlevel := (hr ⟨n,Formula.ex p⟩ hp ys).mpr hclass
  obtain ⟨x,hx⟩ := (scope_ex _ _ _).mp hlevel
  have hbody : (⟨n+1,p⟩ : PackedFormula) ∈ closure F :=
    closure_subformulas F ⟨n,Formula.ex p⟩ hp (Finset.mem_insert_of_mem (self_subformulas p))
  have htruth := (hr ⟨n+1,p⟩ hbody (Fin.snoc ys x)).mp hx
  refine ⟨intoUnion H b x,H.monotone hbl.le x.property,?_⟩
  have hm : (fun i => intoUnion H b ((Fin.snoc (α := fun _ : Fin (n+1) => H.level b) ys x) i)) =
      Fin.snoc (fun i => intoUnion H b (ys i)) (intoUnion H b x) := Fin.comp_snoc (intoUnion H b) ys x
  have hys : (fun i => intoUnion H b (ys i)) = (fun i => intoUnion H l (xs i)) := by
    funext i
    exact Subtype.ext rfl
  simpa only [hm,hys] using htruth

end
end Lemmatheca.SetTheory.RankReflection
