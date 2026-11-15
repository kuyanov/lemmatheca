import Lemmatheca.ConstructibleHierarchy.Absoluteness
import Lemmatheca.RankReflection.RankModels

/-! Concrete height and two-inclusion components. Full internal finite-ZF
modelhood and constructibility-history availability are deliberately not encoded
by the supplied-level hypotheses below. -/
namespace Lemmatheca.SetTheory.ConstructibleCondensation
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
open Lemmatheca.SetTheory.ConstructibleHierarchy
open scoped ZFSet Ordinal Cardinal
universe u
noncomputable section

/-- The actual ordinal members selected from the actual set. -/
def ordinalPart (M : ZFSet.{u}) : ZFSet.{u} := ZFSet.sep ZFSet.IsOrdinal M

/-- For a transitive set, the ordinal part is this ordinal's von Neumann set. -/
def ordinalHeight (M : ZFSet.{u}) : Ordinal.{u} := (ordinalPart M).rank

def OrdinalSuccessorClosed (M : ZFSet.{u}) : Prop :=
  ∀ a : Ordinal.{u}, a.toZFSet ∈ M → (a+1).toZFSet ∈ M

theorem ordinalPart_isOrdinal (M : ZFSet.{u}) (hM : M.IsTransitive) :
    (ordinalPart M).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    obtain ⟨haM, hao⟩ := ZFSet.mem_sep.mp ha
    exact ZFSet.mem_sep.mpr ⟨hM.mem_trans hb haM, hao.mem hb⟩
  · intro a ha
    exact (ZFSet.mem_sep.mp ha).2


theorem height_set (M : ZFSet.{u}) (hM : M.IsTransitive) :
    (ordinalHeight M).toZFSet = ordinalPart M := by
  exact (ordinalPart_isOrdinal M hM).toZFSet_rank_eq


theorem ordinal_mem_iff_height (M : ZFSet.{u}) (hM : M.IsTransitive)
    (a : Ordinal.{u}) : a.toZFSet ∈ M ↔ a < ordinalHeight M := by
  rw [← Ordinal.toZFSet_mem_toZFSet_iff, height_set M hM]
  simp only [ordinalPart, ZFSet.mem_sep, ZFSet.isOrdinal_toZFSet, and_true]


theorem height_not_mem (M : ZFSet.{u}) (hM : M.IsTransitive) :
    (ordinalHeight M).toZFSet ∉ M := by
  exact (ordinal_mem_iff_height M hM (ordinalHeight M)).not.mpr (lt_irrefl _)


/-- The three stated native axiom sentences give the exact closure used in the proof. -/
theorem axioms_give_successor_closure (M : ZFSet.{u}) (hM : M.IsTransitive)
    (h0 : setSatisfies M Lemmatheca.SetTheory.RankReflection.emptyAxiom Fin.elim0)
    (hpair : setSatisfies M Lemmatheca.SetTheory.RankReflection.pairingAxiom Fin.elim0)
    (hunion : setSatisfies M Lemmatheca.SetTheory.RankReflection.unionAxiom Fin.elim0) :
    (∅ : ZFSet.{u}) ∈ M ∧ OrdinalSuccessorClosed M := by
  classical
  obtain ⟨a, ha⟩ := (Lemmatheca.SetTheory.RankReflection.emptyAxiom_realize M).mp h0
  have hae : a.val = ∅ := (ZFSet.eq_empty a.val).mpr (by
    intro z hz
    exact ha ⟨z, hM.mem_trans hz a.property⟩ hz)
  have hempty : (∅ : ZFSet.{u}) ∈ M := hae ▸ a.property
  have hpairs : ∀ x ∈ M, ∀ y ∈ M, ({x,y} : ZFSet.{u}) ∈ M := by
    intro x hx y hy
    obtain ⟨p, hp⟩ :=
      (Lemmatheca.SetTheory.RankReflection.pairingAxiom_realize M).mp hpair ⟨x,hx⟩ ⟨y,hy⟩
    have he : p.val = {x,y} := by
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
      constructor
      · intro hz
        simpa only [Subtype.ext_iff] using (hp ⟨z,hM.mem_trans hz p.property⟩).mp hz
      · rintro (hzx | hzy)
        · exact (hp ⟨z,hzx.symm ▸ hx⟩).mpr (Or.inl (Subtype.ext hzx))
        · exact (hp ⟨z,hzy.symm ▸ hy⟩).mpr (Or.inr (Subtype.ext hzy))
    exact he ▸ p.property
  have hunions : ∀ a ∈ M, (⋃₀ a : ZFSet.{u}) ∈ M := by
    intro a haM
    obtain ⟨b,hb⟩ := (Lemmatheca.SetTheory.RankReflection.unionAxiom_realize M).mp hunion ⟨a,haM⟩
    have he : b.val = ⋃₀ a := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_sUnion]
      constructor
      · intro hz
        obtain ⟨y, hy, hzy⟩ := (hb ⟨z,hM.mem_trans hz b.property⟩).mp hz
        exact ⟨y.val, hy, hzy⟩
      · rintro ⟨y, hy, hzy⟩
        have hyM := hM.mem_trans hy haM
        have hzM := hM.mem_trans hzy hyM
        exact (hb ⟨z,hzM⟩).mpr ⟨⟨y,hyM⟩,hy,hzy⟩
    exact he ▸ b.property
  refine ⟨hempty, ?_⟩
  intro a haM
  have hsingle : ({a.toZFSet} : ZFSet.{u}) ∈ M := by
    have he : ({a.toZFSet,a.toZFSet} : ZFSet.{u}) = {a.toZFSet} := by
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton, or_self]
    exact he ▸ hpairs a.toZFSet haM a.toZFSet haM
  have hu := hunions _ (hpairs a.toZFSet haM {a.toZFSet} hsingle)
  have he : (⋃₀ ({a.toZFSet,{a.toZFSet}} : ZFSet.{u})) = (a+1).toZFSet := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.sUnion_pair, ZFSet.mem_union, ZFSet.mem_singleton,
      Ordinal.toZFSet_add_one, ZFSet.mem_insert_iff]
    exact or_comm
  exact he ▸ hu


theorem height_limit (M : ZFSet.{u}) (hM : M.IsTransitive)
    (h0 : (∅ : ZFSet.{u}) ∈ M) (hs : OrdinalSuccessorClosed M) :
    Order.IsSuccLimit (ordinalHeight M) := by
  rw [Ordinal.isSuccLimit_iff, Order.isSuccPrelimit_iff_succ_lt]
  have hz : (0 : Ordinal.{u}) < ordinalHeight M :=
    (ordinal_mem_iff_height M hM 0).mp (by simpa using h0)
  refine ⟨ne_of_gt hz, ?_⟩
  intro a ha
  simpa only [Order.succ_eq_add_one] using
    (ordinal_mem_iff_height M hM (a+1)).mp (hs a ((ordinal_mem_iff_height M hM a).mpr ha))


/-- This is the separately stated set lemma, not the finite-fragment condensation theorem. -/
theorem classification_from_levels (M : ZFSet.{u}) (hM : M.IsTransitive)
    (l : Ordinal.{u}) (hl : Order.IsSuccLimit l)
    (hlevels : ∀ a < l, level a ∈ M)
    (hexhaust : ∀ x ∈ M, ∃ a < l, x ∈ level a) : M = level l := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨a,ha,hx⟩ := hexhaust x hx
    exact (level_limit_members l hl x).mpr ⟨a,ha,hx⟩
  · intro hx
    obtain ⟨a,ha,hx⟩ := (level_limit_members l hl x).mp hx
    exact hM.mem_trans hx (hlevels a ha)


theorem height_level (a : Ordinal.{u}) : ordinalHeight (level a) = a := by
  simp only [ordinalHeight, ordinalPart, level_ordinals, Ordinal.rank_toZFSet]


theorem height_ordinal (a : Ordinal.{u}) : ordinalHeight a.toZFSet = a := by
  have he : ordinalPart a.toZFSet = a.toZFSet := by
    apply ZFSet.ext
    intro x
    simp only [ordinalPart, ZFSet.mem_sep]
    exact ⟨And.left, fun hx => ⟨hx,(ZFSet.isOrdinal_toZFSet a).mem hx⟩⟩
  rw [ordinalHeight, he, Ordinal.rank_toZFSet]


end
end Lemmatheca.SetTheory.ConstructibleCondensation
