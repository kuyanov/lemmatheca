import Lemmatheca.Absoluteness.Syntax

/-! A scoped classical expansion for the reflection induction. Its translation
is into the existing ordinary membership language, not a replacement semantics. -/
namespace Lemmatheca.SetTheory.RankReflection
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
universe u

inductive Formula : ℕ → Type
  | falsum {n} : Formula n
  | equal {n} (i j : Fin n) : Formula n
  | mem {n} (i j : Fin n) : Formula n
  | neg {n} (p : Formula n) : Formula n
  | conj {n} (p q : Formula n) : Formula n
  | ex {n} (p : Formula (n+1)) : Formula n
  deriving DecidableEq

namespace Formula
def all {n} (p : Formula (n+1)) : Formula n := .neg (.ex (.neg p))
def imp {n} (p q : Formula n) : Formula n := .neg (.conj p (.neg q))
def disj {n} (p q : Formula n) : Formula n := .neg (.conj (.neg p) (.neg q))
def iff {n} (p q : Formula n) : Formula n :=
  .conj (.neg (.conj p (.neg q))) (.neg (.conj q (.neg p)))

def toShared : {n : ℕ} → Formula n → membershipLanguage.BoundedFormula Empty n
  | _, .falsum => .falsum
  | _, .equal i j => .equal (.var (.inr i)) (.var (.inr j))
  | _, .mem i j => memScoped i j
  | _, .neg p => p.toShared.not
  | _, .conj p q => p.toShared ⊓ q.toShared
  | _, .ex p => p.toShared.ex

def termIndex {n} : membershipLanguage.Term (Empty ⊕ Fin n) → Fin n
  | .var (.inl e) => Empty.elim e
  | .var (.inr i) => i
  | .func f _ => Empty.elim f

def ofShared : {n : ℕ} → membershipLanguage.BoundedFormula Empty n → Formula n
  | _, .falsum => .falsum
  | _, .equal t s => .equal (termIndex t) (termIndex s)
  | _, .rel r ts => by
      cases r
      exact .mem (termIndex (ts 0)) (termIndex (ts 1))
  | _, .imp p q => .neg (.conj (ofShared p) (.neg (ofShared q)))
  | _, .all p => .all (ofShared p)

private theorem termIndex_value {M : Type u} (E : M → M → Prop) {n}
    (t : membershipLanguage.Term (Empty ⊕ Fin n)) (a : Fin n → M) :
    let _ := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
    a (termIndex t) = t.realize (Sum.elim Empty.elim a) := by
  cases t with
  | var v => cases v with
    | inl e => exact Empty.elim e
    | inr i => rfl
  | func f _ => exact Empty.elim f

private theorem shared_not {M : Type u} (E : M → M → Prop) {n}
    (p : membershipLanguage.BoundedFormula Empty n) (a : Fin n → M) :
    nativeSatisfies E p.not a ↔ ¬nativeSatisfies E p a := Iff.rfl
private theorem shared_inf {M : Type u} (E : M → M → Prop) {n}
    (p q : membershipLanguage.BoundedFormula Empty n) (a : Fin n → M) :
    nativeSatisfies E (p ⊓ q) a ↔ nativeSatisfies E p a ∧ nativeSatisfies E q a := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  exact BoundedFormula.realize_inf
private theorem shared_ex {M : Type u} (E : M → M → Prop) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+1)) (a : Fin n → M) :
    nativeSatisfies E p.ex a ↔ ∃ x, nativeSatisfies E p (Fin.snoc a x) := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  exact BoundedFormula.realize_ex

theorem ofShared_realize {M : Type u} (E : M → M → Prop) {n}
    (p : membershipLanguage.BoundedFormula Empty n) (a : Fin n → M) :
    nativeSatisfies E (ofShared p).toShared a ↔ nativeSatisfies E p a  := by
  classical
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  induction p with
  | falsum => rfl
  | equal t s =>
    change a (termIndex t) = a (termIndex s) ↔ _
    rw [termIndex_value E t a,termIndex_value E s a]
    rfl
  | rel r ts =>
    cases r
    change E (a (termIndex (ts 0))) (a (termIndex (ts 1))) ↔ _
    rw [termIndex_value E (ts 0) a,termIndex_value E (ts 1) a]
    rfl
  | imp p q ihp ihq =>
    simp only [ofShared,toShared,shared_not,shared_inf,ihp,ihq,not_and,not_not]
    rfl
  | all p ih =>
    simp only [ofShared,Formula.all,toShared,shared_not,shared_ex,ih,not_exists,not_not]
    rfl

end Formula

abbrev PackedFormula := Σ n, Formula n

def subformulas : {n : ℕ} → Formula n → Finset PackedFormula
  | n, p@(.falsum) => {⟨n,p⟩}
  | n, p@(.equal _ _) => {⟨n,p⟩}
  | n, p@(.mem _ _) => {⟨n,p⟩}
  | n, p@(.neg q) => insert ⟨n,p⟩ (subformulas q)
  | n, p@(.conj q r) => insert ⟨n,p⟩ (subformulas q ∪ subformulas r)
  | n, p@(.ex q) => insert ⟨n,p⟩ (subformulas q)

def closure (F : Finset PackedFormula) : Finset PackedFormula :=
  F.biUnion (fun p => subformulas p.2)

private theorem subformulas_self {n} (p : Formula n) :
    (⟨n,p⟩ : PackedFormula) ∈ subformulas p := by
  cases p <;> simp [subformulas]

private theorem subformulas_closed {n} (p : Formula n) :
    ∀ q ∈ subformulas p, subformulas q.2 ⊆ subformulas p := by
  induction p with
  | falsum =>
    intro q h
    simp only [subformulas,Finset.mem_singleton] at h
    subst q
    exact Finset.Subset.refl _
  | equal i j =>
    intro q h
    simp only [subformulas,Finset.mem_singleton] at h
    subst q
    exact Finset.Subset.refl _
  | mem i j =>
    intro q h
    simp only [subformulas,Finset.mem_singleton] at h
    subst q
    exact Finset.Subset.refl _
  | neg p ih =>
    intro q h
    simp only [subformulas,Finset.mem_insert] at h
    rcases h with rfl | h
    · exact Finset.Subset.refl _
    · exact (ih q h).trans (Finset.subset_insert _ _)
  | conj p r ihp ihr =>
    intro q h
    simp only [subformulas,Finset.mem_insert,Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact Finset.Subset.refl _
    · exact (ihp q h).trans (Finset.subset_union_left.trans (Finset.subset_insert _ _))
    · exact (ihr q h).trans (Finset.subset_union_right.trans (Finset.subset_insert _ _))
  | ex p ih =>
    intro q h
    simp only [subformulas,Finset.mem_insert] at h
    rcases h with rfl | h
    · exact Finset.Subset.refl _
    · exact (ih q h).trans (Finset.subset_insert _ _)

theorem closure_contains (F : Finset PackedFormula) : F ⊆ closure F := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨p,hp,subformulas_self p.2⟩

theorem closure_subformulas (F : Finset PackedFormula) (p : PackedFormula)
    (hp : p ∈ closure F) : subformulas p.2 ⊆ closure F := by
  obtain ⟨q,hq,hp⟩ := Finset.mem_biUnion.mp hp
  intro r hr
  exact Finset.mem_biUnion.mpr ⟨q,hq,subformulas_closed q.2 p hp hr⟩

abbrev NativePackedFormula := Σ n, membershipLanguage.BoundedFormula Empty n

noncomputable def expandFamily (F : Finset NativePackedFormula) : Finset PackedFormula := by
  classical
  exact F.image (fun p => ⟨p.1,Formula.ofShared p.2⟩)

end Lemmatheca.SetTheory.RankReflection
