import Lemmatheca.FirstOrderStructures.FirstOrderSemantics
import Lemmatheca.MostowskiCollapse.MostowskiCollapse
import Lemmatheca.HenkinCompleteness.HenkinCompleteness

/-! Membership structures in the shared first-order language.  ZF and ZFC as
whole first-order theories are not encoded here. -/
namespace Lemmatheca.SetTheory.MembershipModels
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.SetTheory.MostowskiCollapse
universe u v w
noncomputable section

abbrev membershipLanguage := binaryRelLanguage

theorem countable_membership_symbols : Countable membershipLanguage.Symbols := by
  let : Subsingleton membershipLanguage.Symbols := ⟨by
    intro a b
    rcases a with ⟨n,f⟩ | ⟨n,r⟩
    · exact Empty.elim f
    · cases r
      rcases b with ⟨n,f⟩ | ⟨n,r⟩
      · exact Empty.elim f
      · cases r; rfl⟩
  infer_instance

def extension {M : Type u} (E : M → M → Prop) (a : M) : Set M := {b | E b a}

def Represented {M : Type u} (E : M → M → Prop) (B : Set M) : Prop :=
  ∃ a, extension E a = B

theorem exists_unrepresented {M : Type u} (E : M → M → Prop) :
    ∃ B : Set M, ¬ Represented E B := by
  simpa [Represented, Function.Surjective] using Function.cantor_surjective (extension E)

@[instance_reducible] def actualMembershipStructure (D : ZFSet.{u}) :
    membershipLanguage.Structure D :=
  binaryRelStructure D (fun a b => a.val ∈ b.val)

@[instance_reducible] def universeMembershipStructure :
    membershipLanguage.Structure ZFSet.{u} :=
  binaryRelStructure ZFSet (fun a b => a ∈ b)

def TransitiveSetModel (D : ZFSet.{u}) (T : membershipLanguage.Theory) : Prop :=
  D ≠ ∅ ∧ D.IsTransitive ∧ (letI := actualMembershipStructure D; D ⊨ T)

/-- An atom between scoped slots; the scope size is unrelated to set-theoretic Δ0. -/
def memScoped {α : Type v} {n : ℕ} (i j : Fin n) :
    membershipLanguage.BoundedFormula α n :=
  .rel BinaryRelationSymbol.rel ![.var (.inr i), .var (.inr j)]

def extensionalitySentence : membershipLanguage.Sentence :=
  ((((memScoped (α := Empty) (n := 3) 2 0).iff (memScoped 2 1)).all).imp
    (.equal (.var (.inr 0)) (.var (.inr 1)))).all.all

def InternalFoundation {M : Type u} (E : M → M → Prop) : Prop :=
  ∀ a, (∃ b, E b a) → ∃ b, E b a ∧ ∀ c, E c a → ¬ E c b

def foundationSentence : membershipLanguage.Sentence :=
  ((memScoped (α := Empty) (n := 2) 1 0).ex.imp
    ((memScoped (n := 2) 1 0) ⊓
      (((memScoped (n := 3) 2 0) ⊓ (memScoped 2 1)).ex.not)).ex).all

private theorem memScoped_realize {M : Type u} (E : M → M → Prop)
    {α : Type v} {n : ℕ} (i j : Fin n) (a : α → M) (xs : Fin n → M) :
    let := binaryRelStructure M E
    (memScoped i j).Realize a xs ↔ E (xs i) (xs j) := by rfl

theorem extensionality_realize {M : Type u} (E : M → M → Prop) :
    let := binaryRelStructure M E
    M ⊨ extensionalitySentence ↔ Extensional E := by
  simp [extensionalitySentence, Sentence.Realize, Formula.Realize,
    memScoped_realize, BoundedFormula.Realize, Term.realize, Fin.snoc, Extensional]

theorem extension_injective_iff {M : Type u} (E : M → M → Prop) :
    Function.Injective (extension E) ↔ Extensional E := by
  constructor
  · intro h a b hab
    exact h (Set.ext hab)
  · intro h a b hab
    exact h a b (fun c => Set.ext_iff.mp hab c)

theorem foundation_realize {M : Type u} (E : M → M → Prop) :
    let := binaryRelStructure M E
    M ⊨ foundationSentence ↔ InternalFoundation E := by
  simp [foundationSentence, Sentence.Realize, Formula.Realize,
    memScoped_realize, BoundedFormula.Realize, InternalFoundation, Fin.snoc]

theorem wellFounded_internalFoundation {M : Type u} {E : M → M → Prop}
    (h : WellFounded E) : InternalFoundation E := by
  intro a ha
  obtain ⟨b,hb,hm⟩ := h.has_min {x | E x a} ha
  exact ⟨b,hb,hm⟩

theorem descending_range_not_represented {M : Type u} {E : M → M → Prop}
    (hf : InternalFoundation E) (b : ℕ → M) (hb : ∀ n, E (b (n+1)) (b n)) :
    ¬ Represented E (Set.range b) := by
  rintro ⟨a,ha⟩
  have h0 : E (b 0) a := by change b 0 ∈ extension E a; rw [ha]; exact ⟨0,rfl⟩
  obtain ⟨m,hm,hmin⟩ := hf a ⟨b 0,h0⟩
  have hmB : m ∈ Set.range b := by rw [← ha]; exact hm
  obtain ⟨n,rfl⟩ := hmB
  apply hmin (b (n+1)) _ (hb n)
  change b (n+1) ∈ extension E a
  rw [ha]
  exact ⟨n+1,rfl⟩

theorem countable_extension {M : Type u} [Countable M] (E : M → M → Prop) (a : M) :
    (extension E a).Countable := Set.to_countable _

/-- The external injection in the Skolem-paradox discussion, with its exact map. -/
def externalInjection {M : Type u} (E : M → M → Prop) (a w : M)
    (e : M ↪ ℕ) (num : ℕ ↪ M) (hn : ∀ n, E (num n) w) :
    extension E a ↪ extension E w where
  toFun x := ⟨num (e x.val), hn _⟩
  inj' _ _ h := Subtype.ext (e.injective (num.injective (congrArg Subtype.val h)))

theorem actual_extension (D : ZFSet.{u}) (a : D) :
    {b : ZFSet.{u} | ∃ h : b ∈ D, (⟨b,h⟩ : D) ∈ extension
      (fun x y : D => x.val ∈ y.val) a} = {b | b ∈ a.val ∧ b ∈ D} := by
  ext b
  simp only [Set.mem_ofPred_eq, extension]
  aesop

theorem transitive_extension (D : ZFSet.{u}) (hD : D.IsTransitive) (a : D) :
    {b : ZFSet.{u} | ∃ h : b ∈ D, (⟨b,h⟩ : D) ∈ extension
      (fun x y : D => x.val ∈ y.val) a} = {b | b ∈ a.val} := by
  ext b
  simp only [Set.mem_ofPred_eq, extension]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨hD.mem_trans h a.property, h⟩

/-- The target set and map are the previously specified collapse, not new witnesses. -/
abbrev collapsedSet {M : Type v} [Small.{u} M] {E : M → M → Prop}
    (h : WellFounded E) : ZFSet.{u} := ZFSet.range (collapse.{u} h)

def collapseIso {M : Type v} [Small.{u} M] {E : M → M → Prop}
    (h : WellFounded E) (he : Extensional E) :
    letI := binaryRelStructure M E
    letI := actualMembershipStructure (collapsedSet.{u} h)
    M ≃[membershipLanguage] collapsedSet.{u} h := by
  letI := binaryRelStructure M E
  letI := actualMembershipStructure (collapsedSet.{u} h)
  let f : M → collapsedSet.{u} h := fun a => ⟨collapse.{u} h a, ZFSet.mem_range_self a⟩
  have hinj : Function.Injective f := fun a b hab =>
    (collapse_injective h he).1 (congrArg Subtype.val hab)
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a, ha⟩ := ZFSet.mem_range.mp b.property
    exact ⟨a, Subtype.ext ha⟩
  refine { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
           map_fun' := ?_, map_rel' := ?_ }
  · intro n f
    exact Empty.elim f
  · intro n r xs
    cases r
    exact ((collapse_injective h he).2 (xs 0) (xs 1)).symm

theorem collapseIso_value {M : Type v} [Small.{u} M] {E : M → M → Prop}
    (h : WellFounded E) (he : Extensional E) (a : M) :
    (collapseIso.{u} h he a).val = collapse.{u} h a := by rfl

theorem collapse_satisfaction {M : Type v} [Small.{u} M] {E : M → M → Prop}
    (h : WellFounded E) (he : Extensional E) {α : Type w} {n : ℕ}
    (φ : membershipLanguage.BoundedFormula α n) (a : α → M) (xs : Fin n → M) :
    let := binaryRelStructure M E
    let := actualMembershipStructure (collapsedSet.{u} h)
    φ.Realize (fun i => collapseIso.{u} h he (a i))
      (fun i => collapseIso.{u} h he (xs i)) ↔ φ.Realize a xs := by
  let := binaryRelStructure M E
  let := actualMembershipStructure (collapsedSet.{u} h)
  exact StrongHomClass.realize_boundedFormula (collapseIso h he) φ

theorem collapse_theory {M : Type v} [Small.{u} M] {E : M → M → Prop}
    (h : WellFounded E) (he : Extensional E) (T : membershipLanguage.Theory) :
    let := binaryRelStructure M E
    let := actualMembershipStructure (collapsedSet.{u} h)
    (collapsedSet.{u} h ⊨ T) ↔ M ⊨ T := by
  let := binaryRelStructure M E
  let := actualMembershipStructure (collapsedSet.{u} h)
  exact (StrongHomClass.elementarilyEquivalent (collapseIso h he)).theory_model_iff.symm

end
end Lemmatheca.SetTheory.MembershipModels
