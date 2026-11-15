import Lemmatheca.ConstructibleCondensation.Heights
import Lemmatheca.ElementarySubmodels.ElementarySubmodels

namespace Lemmatheca.SetTheory.ConstructibleCondensation
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
open Lemmatheca.SetTheory.MostowskiCollapse
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open scoped ZFSet Ordinal Cardinal
universe u w
noncomputable section

/-- Elementary substructures of the actual membership structure, not a replacement syntax. -/
abbrev ElementarySubmodel (D : ZFSet.{u}) :=
  @Language.ElementarySubstructure membershipLanguage D (actualMembershipStructure D)

variable {D : ZFSet.{u}}
local instance condensationAmbientStructure : membershipLanguage.Structure D :=
  actualMembershipStructure D

def submodelRelation (X : ElementarySubmodel D) (a b : X) : Prop :=
  a.val.val ∈ b.val.val

theorem submodelWellFounded (X : ElementarySubmodel D) : WellFounded (submodelRelation X) := by
  exact InvImage.wf (fun a : X => a.val.val) ZFSet.mem_wf


theorem submodel_extensional (hD : D.IsTransitive) (X : ElementarySubmodel D) :
    Extensional (submodelRelation X) := by
  have hDext : D ⊨ extensionalitySentence :=
    (extensionality_realize (fun a b : D => a.val ∈ b.val)).mpr
      (transitive_membership_hypotheses D hD).2
  have hX := (X.subtype.map_sentence extensionalitySentence).mpr hDext
  have hmem {n : ℕ} (i j : Fin n) (a : Empty → X) (xs : Fin n → X) :
      (memScoped i j).Realize a xs ↔ submodelRelation X (xs i) (xs j) := by rfl
  simpa [extensionalitySentence, Sentence.Realize, Formula.Realize,
    hmem, BoundedFormula.Realize, Term.realize, Fin.snoc, Extensional] using hX


/-- These abbreviations select the already specified Mostowski recursion. -/
abbrev submodelCollapse (X : ElementarySubmodel D) : X → ZFSet.{u} :=
  collapse.{u} (submodelWellFounded X)

abbrev submodelImage (X : ElementarySubmodel D) : ZFSet.{u} :=
  collapsedSet.{u} (submodelWellFounded X)

/-- The specified recursion is regarded as a function into its actual range. -/
def submodelMap (X : ElementarySubmodel D) : X → submodelImage X :=
  fun a => ⟨submodelCollapse X a, ZFSet.mem_range_self a⟩

theorem submodelMap_bijective (hD : D.IsTransitive) (X : ElementarySubmodel D) :
    Function.Bijective (submodelMap X) := by
  constructor
  · intro a b hab
    exact (collapse_injective (submodelWellFounded X) (submodel_extensional hD X)).1
      (congrArg Subtype.val hab)
  · intro b
    obtain ⟨a,ha⟩ := ZFSet.mem_range.mp b.property
    exact ⟨a,Subtype.ext ha⟩


/-- The actual native membership structure on X has the same specified collapse map. -/
def submodelIso (hD : D.IsTransitive) (X : ElementarySubmodel D) :
    letI := actualMembershipStructure (submodelImage X)
    X ≃[membershipLanguage] submodelImage X := by
  letI := actualMembershipStructure (submodelImage X)
  exact
    { toEquiv := Equiv.ofBijective (submodelMap X) (submodelMap_bijective hD X)
      map_fun' := by intro n f; exact Empty.elim f
      map_rel' := by
        intro n r xs
        cases r
        exact ((collapse_injective (submodelWellFounded X)
          (submodel_extensional hD X)).2 (xs 0) (xs 1)).symm }

theorem submodelIso_value (hD : D.IsTransitive) (X : ElementarySubmodel D) (a : X) :
    (submodelIso hD X a).val = submodelCollapse X a := by
  rfl


theorem native_collapse_satisfaction (hD : D.IsTransitive) (X : ElementarySubmodel D)
    {α : Type w} {n : ℕ} (φ : membershipLanguage.BoundedFormula α n)
    (a : α → X) (xs : Fin n → X) :
    letI := actualMembershipStructure (submodelImage X)
    φ.Realize (submodelIso hD X ∘ a) (submodelIso hD X ∘ xs) ↔ φ.Realize a xs := by
  let := actualMembershipStructure (submodelImage X)
  exact StrongHomClass.realize_boundedFormula (submodelIso hD X) φ


theorem native_collapse_theory (hD : D.IsTransitive) (X : ElementarySubmodel D)
    (T : membershipLanguage.Theory) :
    letI := actualMembershipStructure (submodelImage X)
    (submodelImage X ⊨ T) ↔ D ⊨ T := by
  let := actualMembershipStructure (submodelImage X)
  exact (StrongHomClass.elementarilyEquivalent (submodelIso hD X)).theory_model_iff.symm.trans
    (X.theory_model_iff T)


theorem image_cardinality (hD : D.IsTransitive) (X : ElementarySubmodel D) :
    Cardinal.mk (submodelImage X) = Cardinal.mk X := by
  let := actualMembershipStructure (submodelImage X)
  exact Cardinal.mk_congr (submodelIso hD X).toEquiv.symm


/-- Every actual ordinal point below kappa is represented in the submodel. -/
def ContainsOrdinalPoints (X : ElementarySubmodel D) (k : Ordinal.{u}) : Prop :=
  ∀ z ∈ k.toZFSet, ∃ a : X, a.val.val = z

theorem collapse_fixes_ordinals (X : ElementarySubmodel D) (k : Ordinal.{u})
    (hpoints : ContainsOrdinalPoints X k) (a : X) (ha : a.val.val ∈ k.toZFSet) :
    submodelCollapse X a = a.val.val := by
  have hfix : ∀ b : X, b.val.val ∈ k.toZFSet → submodelCollapse X b = b.val.val := by
    intro b
    induction b using (submodelWellFounded X).induction with
    | h b ih =>
      intro hb
      change collapse (submodelWellFounded X) b = b.val.val
      rw [collapse_equation]
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_range]
      constructor
      · rintro ⟨c,rfl⟩
        have hck : c.val.val.val ∈ k.toZFSet :=
          (ZFSet.isOrdinal_toZFSet k).isTransitive.mem_trans c.property hb
        change submodelCollapse X c.val ∈ b.val.val
        rw [ih c.val c.property hck]
        exact c.property
      · intro hz
        have hzk : z ∈ k.toZFSet :=
          (ZFSet.isOrdinal_toZFSet k).isTransitive.mem_trans hz hb
        obtain ⟨c,hc⟩ := hpoints z hzk
        have hcb : submodelRelation X c b := by
          change c.val.val ∈ b.val.val
          rw [hc]
          exact hz
        refine ⟨⟨c,hcb⟩, ?_⟩
        exact (ih c hcb (hc.symm ▸ hzk)).trans hc
  exact hfix a ha


theorem collapse_fixes_subset (X : ElementarySubmodel D) (k : Ordinal.{u})
    (hpoints : ContainsOrdinalPoints X k) (a : X) (ha : a.val.val ⊆ k.toZFSet) :
    submodelCollapse X a = a.val.val ∧ a.val.val ∈ submodelImage X := by
  have he : submodelCollapse X a = a.val.val := by
    change collapse (submodelWellFounded X) a = a.val.val
    rw [collapse_equation]
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨b,rfl⟩
      change submodelCollapse X b.val ∈ a.val.val
      rw [collapse_fixes_ordinals X k hpoints b.val (ha b.property)]
      exact b.property
    · intro hz
      obtain ⟨b,hb⟩ := hpoints z (ha hz)
      have hba : submodelRelation X b a := by
        change b.val.val ∈ a.val.val
        rw [hb]
        exact hz
      refine ⟨⟨b,hba⟩, ?_⟩
      exact (collapse_fixes_ordinals X k hpoints b (hb.symm ▸ ha hz)).trans hb
  refine ⟨he, ?_⟩
  exact he ▸ ZFSet.mem_range_self a


theorem collapse_fixes_index (X : ElementarySubmodel D) (k : Ordinal.{u})
    (hpoints : ContainsOrdinalPoints X k) (a : X) (ha : a.val.val = k.toZFSet) :
    submodelCollapse X a = k.toZFSet := by
  exact (collapse_fixes_subset X k hpoints a (by rw [ha])).1.trans ha


end
end Lemmatheca.SetTheory.ConstructibleCondensation
