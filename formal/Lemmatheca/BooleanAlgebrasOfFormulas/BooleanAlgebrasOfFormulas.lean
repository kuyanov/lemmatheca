import Lemmatheca.PropositionalCompactness.PropositionalCompactness
import Lemmatheca.PropositionalNormalForms.PropositionalNormalForms
import Lemmatheca.BooleanAlgebras.BooleanAlgebras

/-! The Boolean algebra of the shared finite propositional formulas.
No replacement syntax or replacement proof calculus is introduced. -/

namespace Lemmatheca.MathematicalLogic.BooleanAlgebrasOfFormulas

open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.PropositionalCompactness
open Lemmatheca.SetTheory.BooleanAlgebras
open Order

universe u
variable {α : Type u}

def formulaSetoid (α : Type u) : Setoid (PropFormula α) where
  r := SemEquivalent
  iseqv := ⟨fun _ _ => rfl, fun h v => (h v).symm, fun h k v => (h v).trans (k v)⟩

abbrev FormulaAlgebra (α : Type u) := Quotient (formulaSetoid α)

def classOf (A : PropFormula α) : FormulaAlgebra α := Quotient.mk _ A

theorem class_eq_iff (A B : PropFormula α) :
    classOf A = classOf B ↔ SemEquivalent A B := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (s := formulaSetoid α) h

theorem equivalent_iff_proofs [DecidableEq α] (A B : PropFormula α) :
    SemEquivalent A B ↔ Derives {A} B ∧ Derives {B} A := by
  constructor
  · intro h
    constructor
    · apply derives_complete
      intro v hv
      have ha : eval v A = true := hv A (by simp)
      change eval v B = true
      rw [← h v]
      exact ha
    · apply derives_complete
      intro v hv
      have hb : eval v B = true := hv B (by simp)
      change eval v A = true
      rw [h v]
      exact hb
  · rintro ⟨hAB, hBA⟩ v
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      exact derives_sound hAB v (by
        intro C hC
        have he := Finset.mem_singleton.mp hC
        change eval v C = true
        simpa only [he] using h)
    · intro h
      exact derives_sound hBA v (by
        intro C hC
        have he := Finset.mem_singleton.mp hC
        change eval v C = true
        simpa only [he] using h)

def truthSet : FormulaAlgebra α → Set (Valuation α) :=
  Quotient.lift (fun A => {v | eval v A = true}) (by
    intro A B h
    ext v
    change eval v A = true ↔ eval v B = true
    rw [h v])

@[simp] theorem mem_truthSet_class (A : PropFormula α) (v : Valuation α) :
    v ∈ truthSet (classOf A) ↔ eval v A = true := Iff.rfl

theorem truthSet_injective : Function.Injective (truthSet : FormulaAlgebra α → _) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h A =>
    induction y using Quotient.inductionOn with
    | h B =>
      apply Quotient.sound
      intro v
      apply Bool.eq_iff_iff.mpr
      exact Set.ext_iff.mp h v

theorem equivalent_neg {A B : PropFormula α} (h : SemEquivalent A B) :
    SemEquivalent (.neg A) (.neg B) := by
  intro v
  simp only [eval, h v]

theorem equivalent_conj {A A' B B' : PropFormula α}
    (hA : SemEquivalent A A') (hB : SemEquivalent B B') :
    SemEquivalent (.conj A B) (.conj A' B') := by
  intro v
  simp only [eval, hA v, hB v]

theorem equivalent_disj {A A' B B' : PropFormula α}
    (hA : SemEquivalent A A') (hB : SemEquivalent B B') :
    SemEquivalent (.disj A B) (.disj A' B') := by
  intro v
  simp only [eval, hA v, hB v]

instance formulaAlgebraMin : Min (FormulaAlgebra α) :=
  ⟨Quotient.map₂ PropFormula.conj (fun {_ _} hA {_ _} hB => equivalent_conj hA hB)⟩

instance formulaAlgebraMax : Max (FormulaAlgebra α) :=
  ⟨Quotient.map₂ PropFormula.disj (fun {_ _} hA {_ _} hB => equivalent_disj hA hB)⟩

instance formulaAlgebraCompl : Compl (FormulaAlgebra α) :=
  ⟨Quotient.map PropFormula.neg (fun {_ _} h => equivalent_neg h)⟩

instance formulaAlgebraBot : Bot (FormulaAlgebra α) := ⟨classOf .falsum⟩
instance formulaAlgebraTop : Top (FormulaAlgebra α) := ⟨classOf verum⟩
instance formulaAlgebraLE : LE (FormulaAlgebra α) := ⟨fun x y => truthSet x ⊆ truthSet y⟩
instance formulaAlgebraLT : LT (FormulaAlgebra α) := ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩
instance formulaAlgebraSDiff : SDiff (FormulaAlgebra α) := ⟨fun x y => min x (yᶜ)⟩
instance formulaAlgebraHImp : HImp (FormulaAlgebra α) := ⟨fun x y => max y (xᶜ)⟩

@[simp] theorem truthSet_inf (x y : FormulaAlgebra α) :
    truthSet (min x y) = truthSet x ∩ truthSet y := by
  induction x using Quotient.inductionOn with
  | h A =>
    induction y using Quotient.inductionOn with
    | h B =>
      ext v
      change (eval v A && eval v B) = true ↔ eval v A = true ∧ eval v B = true
      exact Bool.and_eq_true_iff

@[simp] theorem truthSet_sup (x y : FormulaAlgebra α) :
    truthSet (max x y) = truthSet x ∪ truthSet y := by
  induction x using Quotient.inductionOn with
  | h A =>
    induction y using Quotient.inductionOn with
    | h B =>
      ext v
      change (eval v A || eval v B) = true ↔ eval v A = true ∨ eval v B = true
      exact Bool.or_eq_true_iff

@[simp] theorem truthSet_compl (x : FormulaAlgebra α) :
    truthSet (xᶜ) = (truthSet x)ᶜ := by
  induction x using Quotient.inductionOn with
  | h A =>
    ext v
    change (!(eval v A)) = true ↔ ¬ eval v A = true
    cases eval v A <;> simp

@[simp] theorem truthSet_bot : truthSet (⊥ : FormulaAlgebra α) = ∅ := by
  ext v
  change (false = true) ↔ False
  simp

@[simp] theorem truthSet_top : truthSet (⊤ : FormulaAlgebra α) = Set.univ := by
  ext v
  change (true = true) ↔ True
  simp

instance formulaAlgebraBoolean : BooleanAlgebra (FormulaAlgebra α) :=
  truthSet_injective.booleanAlgebra truthSet Iff.rfl Iff.rfl
    truthSet_sup truthSet_inf truthSet_top truthSet_bot truthSet_compl
    (fun x y => by change truthSet (min x (yᶜ)) = _; simp only [truthSet_inf, truthSet_compl, sdiff_eq]; rfl)
    (fun x y => by change truthSet (max y (xᶜ)) = _; simp only [truthSet_sup, truthSet_compl, himp_eq]; rfl)

@[simp] theorem class_inf (A B : PropFormula α) :
    classOf A ⊓ classOf B = classOf (.conj A B) := rfl
@[simp] theorem class_sup (A B : PropFormula α) :
    classOf A ⊔ classOf B = classOf (.disj A B) := rfl
@[simp] theorem class_compl (A : PropFormula α) :
    (classOf A)ᶜ = classOf (.neg A) := rfl
@[simp] theorem class_falsum : classOf (.falsum : PropFormula α) = ⊥ := rfl
@[simp] theorem class_verum : classOf (verum : PropFormula α) = ⊤ := rfl

theorem class_operations (A B : PropFormula α) :
    classOf A ⊓ classOf B = classOf (.conj A B) ∧
    classOf A ⊔ classOf B = classOf (.disj A B) ∧
    (classOf A)ᶜ = classOf (.neg A) ∧
    classOf (.falsum : PropFormula α) = ⊥ ∧ classOf (verum : PropFormula α) = ⊤ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem class_le_iff (A B : PropFormula α) :
    classOf A ≤ classOf B ↔ ∀ v, eval v A = true → eval v B = true := Iff.rfl

theorem class_le_iff_proof [DecidableEq α] (A B : PropFormula α) :
    classOf A ≤ classOf B ↔ Derives {A} B := by
  constructor
  · intro h
    apply derives_complete
    intro v hv
    exact h (hv A (by simp))
  · intro h v hv
    exact derives_sound h v (by
      intro C hC
      have hCA : C = A := Finset.mem_singleton.mp hC
      change eval v C = true
      simpa [hCA] using hv)

theorem class_implication (A B : PropFormula α) :
    classOf (.impl A B) = (classOf A)ᶜ ⊔ classOf B := by
  apply Quotient.sound
  intro v
  rfl

theorem finite_truthSet_surjective [Fintype α] :
    Function.Surjective (truthSet : FormulaAlgebra α → Set (Valuation α)) := by
  classical
  intro S
  let e := Fintype.equivFin α
  let f : TruthFunction (Fintype.card α) := fun r => decide ((r ∘ e) ∈ S)
  refine ⟨classOf (dnfFormula (canonicalDnf e.symm f)), ?_⟩
  ext v
  change eval v (dnfFormula (canonicalDnf e.symm f)) = true ↔ v ∈ S
  rw [(canonicalDnf_represents e.symm f).2 v]
  simp [f, Function.comp_def]

theorem finite_algebra_card [Fintype α] :
    Nat.card (FormulaAlgebra α) = 2 ^ (2 ^ Fintype.card α) := by
  classical
  calc
    Nat.card (FormulaAlgebra α) = Nat.card (Set (Valuation α)) :=
      Nat.card_congr (Equiv.ofBijective truthSet ⟨truthSet_injective, finite_truthSet_surjective⟩)
    _ = 2 ^ (2 ^ Fintype.card α) := by simp [Nat.card_eq_fintype_card, Valuation]

variable [DecidableEq α]

def IsClosed (T : Theory α) : Prop := ∀ A, TheoryDerives T A → A ∈ T

def consequenceClosure (T : Theory α) : Theory α := {A | TheoryDerives T A}

theorem mem_of_derives_iff (T : Theory α) (hT : IsClosed T) (A : PropFormula α) :
    A ∈ T ↔ TheoryDerives T A := by
  constructor
  · intro hA
    exact ⟨{A}, by simpa, Derives.assumption (by simp)⟩
  · exact hT A

theorem consequenceClosure_closed (T : Theory α) : IsClosed (consequenceClosure T) := by
  intro A hA
  apply (strong_completeness T A).mp
  intro v hv
  apply (strong_completeness (consequenceClosure T) A).mpr hA v
  intro B hB
  exact (strong_completeness T B).mpr hB v hv

theorem consistent_closed_iff (T : Theory α) (hT : IsClosed T) :
    TheoryConsistent T ↔ .falsum ∉ T := by
  unfold TheoryConsistent
  exact not_congr (mem_of_derives_iff T hT .falsum).symm

theorem closed_equivalent (T : Theory α) (hT : IsClosed T) {A B : PropFormula α}
    (h : SemEquivalent A B) : A ∈ T ↔ B ∈ T := by
  constructor
  · intro hA
    apply hT B
    apply (strong_completeness T B).mp
    intro v hv
    change eval v B = true
    rw [← h v]
    exact hv A hA
  · intro hB
    apply hT A
    apply (strong_completeness T A).mp
    intro v hv
    change eval v A = true
    rw [h v]
    exact hv B hB

theorem closed_image_filter (T : Theory α) (hT : IsClosed T) :
    Order.IsPFilter (classOf '' T) := by
  apply Order.IsPFilter.of_def
  · refine ⟨⊤, verum, ?_, rfl⟩
    apply hT
    apply (strong_completeness T verum).mp
    intro v _
    rfl
  · rintro x ⟨A, hA, rfl⟩ y ⟨B, hB, rfl⟩
    refine ⟨classOf (.conj A B), ⟨.conj A B, ?_, rfl⟩, ?_, ?_⟩
    · apply hT
      apply (strong_completeness T (.conj A B)).mp
      intro v hv
      exact Bool.and_eq_true_iff.mpr ⟨hv A hA, hv B hB⟩
    · change classOf A ⊓ classOf B ≤ classOf A
      exact inf_le_left
    · change classOf A ⊓ classOf B ≤ classOf B
      exact inf_le_right
  · rintro x y hxy ⟨A, hA, rfl⟩
    obtain ⟨B, rfl⟩ := Quotient.exists_rep y
    refine ⟨B, ?_, rfl⟩
    apply hT
    apply (strong_completeness T B).mp
    intro v hv
    exact hxy (hv A hA)

def filterOfTheory (T : Theory α) (hT : IsClosed T) : PFilter (FormulaAlgebra α) :=
  (closed_image_filter T hT).toPFilter

def theoryOfFilter (F : PFilter (FormulaAlgebra α)) : Theory α := {A | classOf A ∈ F}

@[simp] theorem mem_filterOfTheory (T : Theory α) (hT : IsClosed T) (A : PropFormula α) :
    classOf A ∈ filterOfTheory T hT ↔ A ∈ T := by
  change (∃ B ∈ T, classOf B = classOf A) ↔ A ∈ T
  constructor
  · rintro ⟨B, hB, he⟩
    exact (closed_equivalent T hT ((class_eq_iff B A).mp he)).mp hB
  · intro hA
    exact ⟨A, hA, rfl⟩

theorem theoryOfFilter_closed (F : PFilter (FormulaAlgebra α)) :
    IsClosed (theoryOfFilter F) := by
  intro C ⟨Δ, hΔ, hd⟩
  have hmeet : ∀ l : List (PropFormula α),
      (∀ A ∈ l, classOf A ∈ F) → classOf (finiteConj l) ∈ F := by
    intro l
    induction l with
    | nil =>
      intro _
      exact PFilter.top_mem
    | cons A rest ih =>
      intro hl
      cases rest with
      | nil => exact hl A (by simp)
      | cons B tail =>
        change classOf A ⊓ classOf (finiteConj (B :: tail)) ∈ F
        exact PFilter.inf_mem (hl A (by simp))
          (ih (fun D hD => hl D (List.mem_cons_of_mem A hD)))
  apply PFilter.mem_of_le (y := classOf C) _ (hmeet Δ.toList (fun A hA => hΔ (Finset.mem_toList.mp hA)))
  intro v hv
  apply derives_sound hd v
  intro A hA
  exact (eval_finiteConj v Δ.toList).mp hv A (Finset.mem_toList.mpr hA)

theorem theory_filter_inverse (T : Theory α) (hT : IsClosed T) :
    theoryOfFilter (filterOfTheory T hT) = T := by
  ext A
  exact mem_filterOfTheory T hT A

theorem filter_theory_inverse (F : PFilter (FormulaAlgebra α)) :
    filterOfTheory (theoryOfFilter F) (theoryOfFilter_closed F) = F := by
  apply SetLike.ext
  intro x
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  exact mem_filterOfTheory (theoryOfFilter F) (theoryOfFilter_closed F) A

theorem filterOfTheory_inclusion (T S : Theory α) (hT : IsClosed T) (hS : IsClosed S) :
    filterOfTheory T hT ≤ filterOfTheory S hS ↔ T ⊆ S := by
  constructor
  · intro h A hA
    exact (mem_filterOfTheory S hS A).mp (h ((mem_filterOfTheory T hT A).mpr hA))
  · intro h x hx
    obtain ⟨A, rfl⟩ := Quotient.exists_rep x
    exact (mem_filterOfTheory S hS A).mpr (h ((mem_filterOfTheory T hT A).mp hx))

omit [DecidableEq α] in
theorem theoryOfFilter_inclusion (F G : PFilter (FormulaAlgebra α)) :
    theoryOfFilter F ⊆ theoryOfFilter G ↔ F ≤ G := by
  constructor
  · intro h x hx
    obtain ⟨A, rfl⟩ := Quotient.exists_rep x
    exact h hx
  · intro h A hA
    exact h hA

theorem filterOfTheory_proper (T : Theory α) (hT : IsClosed T) :
    IsProperFilter (filterOfTheory T hT) ↔ TheoryConsistent T := by
  rw [consistent_closed_iff T hT]
  unfold IsProperFilter
  exact not_congr (mem_filterOfTheory T hT .falsum)

def IsComplete (T : Theory α) : Prop :=
  TheoryConsistent T ∧ ∀ A, A ∈ T ∨ PropFormula.neg A ∈ T

def IsMaximalConsistent (T : Theory α) : Prop :=
  TheoryConsistent T ∧ ∀ S, IsClosed S → T ⊆ S → TheoryConsistent S → S = T

theorem all_formulas_not_complete : ¬ IsComplete (Set.univ : Theory α) := by
  intro h
  apply h.1
  exact ⟨{.falsum}, by simp, Derives.assumption (by simp)⟩

def valuationTheory (v : Valuation α) : Theory α := {A | eval v A = true}

theorem valuationTheory_closed (v : Valuation α) : IsClosed (valuationTheory v) := by
  intro A hA
  exact (strong_completeness (valuationTheory v) A).mpr hA v (fun _ h => h)

theorem valuationTheory_complete (v : Valuation α) : IsComplete (valuationTheory v) := by
  constructor
  · exact (consistency_iff_satisfiable (valuationTheory v)).mpr ⟨v, fun _ h => h⟩
  · intro A
    cases h : eval v A with
    | false => exact Or.inr (by simp [valuationTheory, eval, h])
    | true => exact Or.inl h

noncomputable def theoryValuation (T : Theory α) : Valuation α :=
  by
  classical
  exact fun a => if PropFormula.atom a ∈ T then true else false

private theorem complete_has_valuation (T : Theory α) (hC : IsComplete T) :
    ∃ v : Valuation α, valuationTheory v = T := by
  obtain ⟨v, hv⟩ := (consistency_iff_satisfiable T).mp hC.1
  refine ⟨v, Set.ext fun A => ?_⟩
  constructor
  · intro hA
    by_contra hn
    have hnA := (hC.2 A).resolve_left hn
    have hf := hv (.neg A) hnA
    change eval v A = true at hA
    simp [Satisfies, eval, hA] at hf
  · exact hv A

theorem complete_membership (T : Theory α) (_hT : IsClosed T) (hC : IsComplete T)
    (A : PropFormula α) : eval (theoryValuation T) A = true ↔ A ∈ T := by
  classical
  obtain ⟨v, hv⟩ := complete_has_valuation T hC
  have hval : theoryValuation T = v := by
    funext a
    have hm : PropFormula.atom a ∈ T ↔ v a = true := by
      rw [← hv]
      rfl
    cases he : v a <;> simp_all [theoryValuation]
  rw [hval, ← hv]
  rfl

theorem complete_unique_valuation (T : Theory α) (hT : IsClosed T) (hC : IsComplete T) :
    ∃! v : Valuation α, valuationTheory v = T := by
  refine ⟨theoryValuation T, ?_, ?_⟩
  · ext A
    exact complete_membership T hT hC A
  · intro v hv
    funext a
    apply Bool.eq_iff_iff.mpr
    change eval v (.atom a) = true ↔ eval (theoryValuation T) (.atom a) = true
    rw [complete_membership T hT hC, ← hv]
    rfl

theorem complete_iff_maximal (T : Theory α) (_hT : IsClosed T) :
    IsComplete T ↔ IsMaximalConsistent T := by
  constructor
  · intro hC
    refine ⟨hC.1, ?_⟩
    intro S _hS hTS hS
    obtain ⟨v, hv⟩ := (consistency_iff_satisfiable S).mp hS
    apply Set.Subset.antisymm _ hTS
    intro A hA
    by_contra hn
    have hnA := (hC.2 A).resolve_left hn
    have ht : eval v A = true := hv A hA
    have hf := hv (.neg A) (hTS hnA)
    simp [Satisfies, eval, ht] at hf
  · intro hM
    obtain ⟨v, hv⟩ := (consistency_iff_satisfiable T).mp hM.1
    have he := hM.2 (valuationTheory v) (valuationTheory_closed v) hv (valuationTheory_complete v).1
    simpa only [he] using valuationTheory_complete v

theorem complete_iff_ultrafilter (T : Theory α) (hT : IsClosed T) :
    IsComplete T ↔ IsUltrafilter (filterOfTheory T hT) := by
  constructor
  · intro hC
    have hproper := (filterOfTheory_proper T hT).mpr hC.1
    apply (ultrafilter_characterizations (filterOfTheory T hT) hproper).1.mpr
    intro x
    obtain ⟨A, rfl⟩ := Quotient.exists_rep x
    change classOf A ∈ filterOfTheory T hT ↔ (classOf A)ᶜ ∉ filterOfTheory T hT
    rw [class_compl, mem_filterOfTheory, mem_filterOfTheory]
    obtain ⟨v, hv⟩ := complete_has_valuation T hC
    rw [← hv]
    change eval v A = true ↔ ¬ eval v (.neg A) = true
    cases h : eval v A <;> simp [eval, h]
  · intro hU
    refine ⟨(filterOfTheory_proper T hT).mp hU.1, ?_⟩
    intro A
    by_cases hA : A ∈ T
    · exact Or.inl hA
    · apply Or.inr
      have hdec := (ultrafilter_characterizations (filterOfTheory T hT) hU.1).1.mp hU
      have hn : (classOf A)ᶜ ∈ filterOfTheory T hT := by
        apply (hdec ((classOf A)ᶜ)).mpr
        simpa only [compl_compl, mem_filterOfTheory] using hA
      simpa only [class_compl, mem_filterOfTheory] using hn

def valuationFilter (v : Valuation α) : PFilter (FormulaAlgebra α) :=
  filterOfTheory (valuationTheory v) (valuationTheory_closed v)

theorem valuationFilter_bijection :
    (∀ v : Valuation α, IsUltrafilter (valuationFilter v)) ∧
    ∀ F : PFilter (FormulaAlgebra α), IsUltrafilter F →
      ∃! v : Valuation α, valuationFilter v = F := by
  constructor
  · intro v
    exact (complete_iff_ultrafilter (valuationTheory v) (valuationTheory_closed v)).mp
      (valuationTheory_complete v)
  · intro F hF
    let T := theoryOfFilter F
    have hT := theoryOfFilter_closed F
    have hC : IsComplete T := (complete_iff_ultrafilter T hT).mpr (by
      rw [filter_theory_inverse]
      exact hF)
    obtain ⟨v, hv, hu⟩ := complete_unique_valuation T hT hC
    refine ⟨v, ?_, ?_⟩
    · apply SetLike.ext
      intro x
      obtain ⟨A, rfl⟩ := Quotient.exists_rep x
      change classOf A ∈ filterOfTheory (valuationTheory v) (valuationTheory_closed v) ↔ classOf A ∈ F
      rw [mem_filterOfTheory, hv]
      rfl
    · intro w hw
      apply hu
      ext A
      have he := congrArg (fun G : PFilter (FormulaAlgebra α) => classOf A ∈ G) hw
      change A ∈ valuationTheory w ↔ classOf A ∈ F
      simpa only [valuationFilter, mem_filterOfTheory] using Iff.of_eq he

theorem consistent_extension (Γ : Theory α) (hΓ : TheoryConsistent Γ) :
    ∃ T : Theory α, Γ ⊆ T ∧ IsClosed T ∧ IsComplete T := by
  obtain ⟨v, hv⟩ := (consistency_iff_satisfiable Γ).mp hΓ
  exact ⟨valuationTheory v, hv, valuationTheory_closed v, valuationTheory_complete v⟩

theorem consequence_separation (Γ : Theory α) (A : PropFormula α)
    (h : ¬ TheoryDerives Γ A) :
    ∃ T : Theory α, Γ ⊆ T ∧ IsClosed T ∧ IsComplete T ∧ A ∉ T := by
  have hn : ¬ TheoryEntails Γ A := fun he => h ((strong_completeness Γ A).mp he)
  unfold TheoryEntails at hn
  push Not at hn
  obtain ⟨v, hv, hnA⟩ := hn
  exact ⟨valuationTheory v, hv, valuationTheory_closed v, valuationTheory_complete v, hnA⟩

end Lemmatheca.MathematicalLogic.BooleanAlgebrasOfFormulas
