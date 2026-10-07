import Mathlib.Order.PrimeSeparator
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Basic

/-! Boolean filters, element-complement duality, and algebraic Stone representation.
The range is a Boolean subalgebra of a power set, not necessarily the full power set.
Classical Lean supplies choice; these declarations do not encode axiom strength over ZF.
-/

namespace Lemmatheca.SetTheory.BooleanAlgebras

open Set Order
universe u v
variable {B : Type u} [BooleanAlgebra B]

/-- Properness of a Boolean filter. -/
def IsProperFilter (F : PFilter B) : Prop := (⊥ : B) ∉ F

theorem principal_filter_proper_iff (a : B) :
    IsProperFilter (PFilter.principal a) ↔ a ≠ ⊥ := by
  simp [IsProperFilter, PFilter.mem_principal]

/-- Maximality among proper filters, using inclusion of carriers. -/
def IsUltrafilter (F : PFilter B) : Prop :=
  IsProperFilter F ∧ ∀ G : PFilter B, F ≤ G → IsProperFilter G → G = F

/-- Element complementation, distinct from complementing the carrier set. -/
def dualIdeal (F : PFilter B) : Set B := {a | aᶜ ∈ F}

def dualFilter (I : Ideal B) : Set B := {a | aᶜ ∈ I}

theorem complement_duality (F : PFilter B) (I : Ideal B) :
    Order.IsIdeal (dualIdeal F) ∧ Order.IsPFilter (dualFilter I) ∧
    (∀ a : B, aᶜ ∈ dualIdeal F ↔ a ∈ F) ∧
    (∀ a : B, aᶜ ∈ dualFilter I ↔ a ∈ I) ∧
    ((⊤ : B) ∉ dualIdeal F ↔ IsProperFilter F) ∧
    ((⊥ : B) ∉ dualFilter I ↔ I.IsProper) := by
  have hFI : Order.IsIdeal (dualIdeal F) :=
    ⟨fun _ _ h hmem => PFilter.mem_of_le (compl_le_compl h) hmem,
      ⟨⊥, by simp [dualIdeal]⟩,
      fun a ha b hb => ⟨a ⊔ b, by
        change (a ⊔ b)ᶜ ∈ F
        rw [compl_sup]
        exact PFilter.inf_mem ha hb,
        le_sup_left, le_sup_right⟩⟩
  have hIF : Order.IsPFilter (dualFilter I) := Order.IsPFilter.of_def
    ⟨⊤, by simp [dualFilter]⟩
    (fun a ha b hb => ⟨a ⊓ b, by
      change (a ⊓ b)ᶜ ∈ I
      rw [compl_inf]
      exact Ideal.sup_mem ha hb,
      inf_le_left, inf_le_right⟩)
    (fun h hmem => I.lower (compl_le_compl h) hmem)
  refine ⟨hFI, hIF, ?_, ?_, ?_, ?_⟩
  · intro a; simp [dualIdeal]
  · intro a; simp [dualFilter]
  · simp [dualIdeal, IsProperFilter]
  · simp [dualFilter, Ideal.isProper_iff_top_notMem]

theorem duality_preserves_inclusion (F G : PFilter B) (I J : Ideal B) :
    (dualIdeal F ⊆ dualIdeal G ↔ F ≤ G) ∧
    (dualFilter I ⊆ dualFilter J ↔ I ≤ J) := by
  constructor
  · constructor
    · intro h a ha
      have := h (show aᶜ ∈ dualIdeal F by simpa [dualIdeal] using ha)
      simpa [dualIdeal] using this
    · intro h a ha; exact h ha
  · constructor
    · intro h a ha
      have := h (show aᶜ ∈ dualFilter I by simpa [dualFilter] using ha)
      simpa [dualFilter] using this
    · intro h a ha; exact h ha

/-- The carrier of the filter obtained by adjoining one element. -/
def adjoin (F : PFilter B) (a : B) : Set B :=
  {b | ∃ f ∈ F, f ⊓ a ≤ b}

theorem adjoin_spec (F : PFilter B) (a : B) :
    Order.IsPFilter (adjoin F a) ∧ (F : Set B) ⊆ adjoin F a ∧ a ∈ adjoin F a ∧
    (∀ G : PFilter B, F ≤ G → a ∈ G → adjoin F a ⊆ G) ∧
    ((⊥ : B) ∉ adjoin F a ↔ ∀ f ∈ F, f ⊓ a ≠ ⊥) ∧
    ((⊥ : B) ∉ adjoin F a ↔ aᶜ ∉ F) := by
  have hmem : a ∈ adjoin F a := ⟨⊤, PFilter.top_mem, by simp⟩
  have hproper : (⊥ : B) ∉ adjoin F a ↔ aᶜ ∉ F := by
    constructor
    · intro h hc
      exact h ⟨aᶜ, hc, by simp⟩
    · rintro h ⟨f, hf, hfa⟩
      exact h (PFilter.mem_of_le
        (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr (le_bot_iff.mp hfa))) hf)
  refine ⟨Order.IsPFilter.of_def ⟨a, hmem⟩ ?_ ?_, ?_, hmem, ?_, ?_, hproper⟩
  · rintro b ⟨f, hf, hfb⟩ c ⟨g, hg, hgc⟩
    refine ⟨b ⊓ c, ⟨f ⊓ g, PFilter.inf_mem hf hg, ?_⟩, inf_le_left, inf_le_right⟩
    exact le_inf ((inf_le_inf_right a inf_le_left).trans hfb)
      ((inf_le_inf_right a inf_le_right).trans hgc)
  · rintro b c hbc ⟨f, hf, hfb⟩
    exact ⟨f, hf, hfb.trans hbc⟩
  · intro b hb; exact ⟨b, hb, inf_le_left⟩
  · rintro G hFG ha b ⟨f, hf, hfb⟩
    exact PFilter.mem_of_le hfb (PFilter.inf_mem (hFG hf) ha)
  · simp only [adjoin, mem_ofPred_eq, le_bot_iff, not_exists, not_and]

theorem ultrafilter_characterizations (F : PFilter B) (hF : IsProperFilter F) :
    (IsUltrafilter F ↔ ∀ a : B, (a ∈ F ↔ aᶜ ∉ F)) ∧
    (IsUltrafilter F ↔ ∀ a b : B, a ⊔ b ∈ F → a ∈ F ∨ b ∈ F) := by
  classical
  have hn (a : B) (ha : a ∈ F) : aᶜ ∉ F := by
    intro hc
    exact hF (by simpa using PFilter.inf_mem ha hc)
  have hchar : IsUltrafilter F ↔ ∀ a : B, (a ∈ F ↔ aᶜ ∉ F) := by
    constructor
    · intro hU a
      refine ⟨hn a, fun hc => ?_⟩
      let G := (adjoin_spec F a).1.toPFilter
      have hG : IsProperFilter G := (adjoin_spec F a).2.2.2.2.2.mpr hc
      have he : G = F := hU.2 G (adjoin_spec F a).2.1 hG
      exact he ▸ (adjoin_spec F a).2.2.1
    · intro hd
      refine ⟨hF, fun G hFG hG => le_antisymm ?_ hFG⟩
      intro a ha
      by_contra hnF
      have hc : aᶜ ∈ F := by
        by_contra hc
        exact hnF ((hd a).mpr hc)
      exact hG (by simpa using PFilter.inf_mem ha (hFG hc))
  refine ⟨hchar, hchar.trans ?_⟩
  constructor
  · intro hd a b hab
    by_contra h
    have ha : aᶜ ∈ F := by
      by_contra hc; exact h (Or.inl ((hd a).mpr hc))
    have hb : bᶜ ∈ F := by
      by_contra hc; exact h (Or.inr ((hd b).mpr hc))
    exact (hn (a ⊔ b) hab) (by simpa using PFilter.inf_mem ha hb)
  · intro hp a
    refine ⟨hn a, fun hc => ?_⟩
    exact (hp a aᶜ (by simp)).resolve_right hc

theorem ultrafilter_dual_maximal (F : PFilter B) (I : Ideal B)
    (hI : (I : Set B) = dualIdeal F) :
    IsUltrafilter F ↔ I.IsMaximal := by
  have hmem (a : B) : a ∈ I ↔ aᶜ ∈ F := by rw [← SetLike.mem_coe, hI]; rfl
  constructor
  · intro hF
    have hp : I.IsProper := Ideal.isProper_iff_top_notMem.mpr (by
      simpa [hmem, IsProperFilter] using hF.1)
    let _ := hp
    have hd := (ultrafilter_characterizations F hF.1).1.mp hF
    have hprime : I.IsPrime := Ideal.isPrime_of_mem_or_compl_mem (fun {a} => by
      by_cases ha : a ∈ F
      · exact Or.inr ((hmem aᶜ).mpr (by simpa using ha))
      · have hc : aᶜ ∈ F := by
          by_contra hc; exact ha ((hd a).mpr hc)
        exact Or.inl ((hmem a).mpr hc))
    let _ := hprime
    infer_instance
  · intro hmax
    let _ := hmax
    have hp : IsProperFilter F := by
      intro h
      exact hmax.top_notMem ((hmem ⊤).mpr (by simpa using h))
    apply (ultrafilter_characterizations F hp).1.mpr
    intro a
    constructor
    · intro ha hc
      exact hp (by simpa using PFilter.inf_mem ha hc)
    · intro hc
      have hor := (inferInstance : I.IsPrime).mem_or_compl_mem (x := a)
      rcases hor with ha | ha
      · exact (hc ((hmem a).mp ha)).elim
      · simpa using (hmem aᶜ).mp ha

theorem ultrafilter_dual_carrier (F : PFilter B) (hF : IsUltrafilter F) :
    dualIdeal F = (F : Set B)ᶜ := by
  ext a
  exact ((ultrafilter_characterizations F hF.1).1.mp hF aᶜ).trans (by simp)

theorem exists_ultrafilter_extension (F : PFilter B) (hF : IsProperFilter F) :
    ∃ U : PFilter B, IsUltrafilter U ∧ F ≤ U := by
  let I := (complement_duality F (Ideal.principal (⊥ : B))).1.toIdeal
  have hp : I.IsProper := Ideal.isProper_iff_top_notMem.mpr
    ((complement_duality F (Ideal.principal (⊥ : B))).2.2.2.2.1.mpr hF)
  obtain ⟨J, hIJ, hJ⟩ := hp.exists_le_maximal
  let U := (complement_duality F J).2.1.toPFilter
  have he : (J : Set B) = dualIdeal U := by
    ext a
    change a ∈ J ↔ aᶜᶜ ∈ J
    simp
  refine ⟨U, (ultrafilter_dual_maximal U J he).mpr hJ, ?_⟩
  intro a ha
  have hi : aᶜ ∈ I := by simpa [I, dualIdeal] using ha
  show aᶜ ∈ J
  exact hIJ hi

theorem exists_ultrafilter_of_ne_bot (c : B) (hc : c ≠ ⊥) :
    ∃ U : PFilter B, IsUltrafilter U ∧ c ∈ U := by
  have hp : IsProperFilter (PFilter.principal c) := by
    simpa [IsProperFilter, PFilter.mem_principal] using hc
  obtain ⟨U, hU, hle⟩ := exists_ultrafilter_extension (PFilter.principal c) hp
  exact ⟨U, hU, hle (by simp)⟩

theorem exists_ultrafilter [Nontrivial B] :
    ∃ U : PFilter B, IsUltrafilter U := by
  obtain ⟨U, hU, _⟩ := exists_ultrafilter_of_ne_bot (⊤ : B) top_ne_bot
  exact ⟨U, hU⟩

theorem separates_not_le (a b : B) (h : ¬ a ≤ b) :
    ∃ U : PFilter B, IsUltrafilter U ∧ a ∈ U ∧ b ∉ U := by
  have hc : a ⊓ bᶜ ≠ ⊥ := by
    intro hc; exact h (disjoint_compl_right_iff.mp (disjoint_iff.mpr hc))
  obtain ⟨U, hU, hcU⟩ := exists_ultrafilter_of_ne_bot (a ⊓ bᶜ) hc
  refine ⟨U, hU, PFilter.mem_of_le inf_le_left hcU, ?_⟩
  intro hb
  exact hU.1 (by simpa using PFilter.inf_mem hb (PFilter.mem_of_le inf_le_right hcU))

theorem separates_ne (a b : B) (h : a ≠ b) :
    ∃ U : PFilter B, IsUltrafilter U ∧ ¬ (a ∈ U ↔ b ∈ U) := by
  classical
  by_cases hab : a ≤ b
  · obtain ⟨U, hU, hb, ha⟩ := separates_not_le b a (fun hba => h (le_antisymm hab hba))
    exact ⟨U, hU, fun he => ha (he.mpr hb)⟩
  · obtain ⟨U, hU, ha, hb⟩ := separates_not_le a b hab
    exact ⟨U, hU, fun he => hb (he.mp ha)⟩

/-- All ultrafilters on the Boolean algebra, including the empty space for a trivial algebra. -/
def StoneSpace (B : Type u) [BooleanAlgebra B] := {U : PFilter B // IsUltrafilter U}

def stoneMap (a : B) : Set (StoneSpace B) := {U | a ∈ U.val}

theorem stoneMap_laws :
    stoneMap (⊥ : B) = ∅ ∧ stoneMap (⊤ : B) = univ ∧
    (∀ a b : B, stoneMap (a ⊓ b) = stoneMap a ∩ stoneMap b) ∧
    (∀ a b : B, stoneMap (a ⊔ b) = stoneMap a ∪ stoneMap b) ∧
    (∀ a : B, stoneMap aᶜ = (stoneMap a)ᶜ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext U
    exact ⟨U.prop.1, False.elim⟩
  · ext U; simp [stoneMap]
  · intro a b; ext U; exact PFilter.inf_mem_iff
  · intro a b; ext U
    refine ⟨(ultrafilter_characterizations U.val U.prop.1).2.mp U.prop a b, ?_⟩
    rintro (ha | hb)
    · exact PFilter.mem_of_le le_sup_left ha
    · exact PFilter.mem_of_le le_sup_right hb
  · intro a; ext U
    simpa [stoneMap] using (ultrafilter_characterizations U.val U.prop.1).1.mp U.prop aᶜ

def stoneHom : BoundedLatticeHom B (Set (StoneSpace B)) where
  toFun := stoneMap
  map_bot' := stoneMap_laws.1
  map_top' := stoneMap_laws.2.1
  map_sup' := stoneMap_laws.2.2.2.1
  map_inf' := stoneMap_laws.2.2.1

theorem stoneMap_order (a b : B) : a ≤ b ↔ stoneMap a ⊆ stoneMap b := by
  constructor
  · intro h U ha; exact PFilter.mem_of_le h ha
  · intro h
    by_contra hab
    obtain ⟨U, hU, ha, hb⟩ := separates_not_le a b hab
    exact hb (h (show (⟨U, hU⟩ : StoneSpace B) ∈ stoneMap a from ha))

theorem stoneMap_injective : Function.Injective (stoneMap : B → Set (StoneSpace B)) := by
  intro a b h
  exact le_antisymm ((stoneMap_order a b).mpr h.le) ((stoneMap_order b a).mpr h.ge)

/-- The Boolean subalgebra that is the image of the Stone homomorphism. -/
def stoneRange (B : Type u) [BooleanAlgebra B] : BooleanSubalgebra (Set (StoneSpace B)) :=
  (⊤ : BooleanSubalgebra B).map stoneHom

theorem stoneRange_carrier : (stoneRange B : Set (Set (StoneSpace B))) = range stoneMap := by
  simp [stoneRange, BooleanSubalgebra.coe_map, stoneHom]

theorem stone_representation :
    ∃ e : B ≃o stoneRange B, ∀ a : B, (e a : Set (StoneSpace B)) = stoneMap a := by
  let f : B ↪o stoneRange B :=
    { toFun := fun a => ⟨stoneMap a, by
        change stoneMap a ∈ (stoneRange B : Set (Set (StoneSpace B)))
        rw [stoneRange_carrier]; exact mem_range_self a⟩
      inj' := fun a b h => stoneMap_injective (congrArg Subtype.val h)
      map_rel_iff' := fun {a b} => (stoneMap_order a b).symm }
  have hf : Function.Surjective f := by
    intro S
    have hS : S.val ∈ range (stoneMap : B → Set (StoneSpace B)) := by
      rw [← stoneRange_carrier]; exact S.prop
    obtain ⟨a, ha⟩ := hS
    exact ⟨a, Subtype.ext ha⟩
  exact ⟨OrderIso.ofSurjective f hf, fun _ => rfl⟩

theorem trivial_representation (h : (⊥ : B) = ⊤) :
    Subsingleton B ∧ IsEmpty (StoneSpace B) ∧
    Function.Bijective (stoneMap : B → Set (StoneSpace B)) := by
  have hB : Subsingleton B := subsingleton_of_bot_eq_top h
  have hX : IsEmpty (StoneSpace B) := ⟨fun U => U.prop.1 (h.symm ▸ PFilter.top_mem)⟩
  let _ := hB
  let _ := hX
  refine ⟨hB, hX, fun a b _ => Subsingleton.elim a b, ?_⟩
  intro S
  refine ⟨⊥, ?_⟩
  ext U
  exact isEmptyElim U

/-- The usual finite/cofinite family on the naturals. -/
def finiteCofinite : Set (Set ℕ) := {s | s.Finite ∨ sᶜ.Finite}

theorem finiteCofinite_algebra :
    ∃ A : BooleanSubalgebra (Set ℕ), (A : Set (Set ℕ)) = finiteCofinite := by
  refine ⟨{
    carrier := finiteCofinite
    supClosed' := ?_
    infClosed' := ?_
    compl_mem' := ?_
    bot_mem' := Or.inl finite_empty
  }, rfl⟩
  · intro a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (ha.union hb)
    · exact Or.inr (hb.subset (compl_subset_compl.mpr subset_union_right))
    · exact Or.inr (ha.subset (compl_subset_compl.mpr subset_union_left))
    · exact Or.inr (ha.subset (compl_subset_compl.mpr subset_union_left))
  · intro a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (ha.subset inter_subset_left)
    · exact Or.inl (ha.subset inter_subset_left)
    · exact Or.inl (hb.subset inter_subset_right)
    · apply Or.inr
      change (a ∩ b)ᶜ.Finite
      rw [Set.compl_inter]
      exact ha.union hb
  · intro a ha
    rcases ha with ha | ha
    · exact Or.inr (by simpa using ha)
    · exact Or.inl ha

theorem finiteCofinite_size : finiteCofinite.Countable ∧ finiteCofinite.Infinite := by
  have hf : {s : Set ℕ | s.Finite}.Countable := Set.Countable.ofPred_finite
  constructor
  · apply (hf.union (hf.image (fun s : Set ℕ => sᶜ))).mono
    rintro s (hs | hs)
    · exact Or.inl hs
    · exact Or.inr ⟨sᶜ, hs, by simp⟩
  · apply Set.infinite_of_injective_forall_mem Set.singleton_injective
    intro n
    exact Or.inl (finite_singleton n)

theorem finiteCofinite_not_powerSet (α : Type v) :
    ¬ Nonempty (finiteCofinite ≃ Set α) := by
  classical
  rintro ⟨e⟩
  cases finite_or_infinite α with
  | inl h =>
    let _ := h
    have : Finite finiteCofinite := Finite.of_injective e e.injective
    exact finiteCofinite_size.2 (Set.toFinite finiteCofinite)
  | inr h =>
    let _ := h
    let _ := finiteCofinite_size.1.to_subtype
    obtain ⟨c, hc⟩ := Countable.exists_injective_nat finiteCofinite
    let f := Infinite.natEmbedding α
    exact Function.cantor_injective (fun s : Set ℕ => c (e.symm (f '' s)))
      (hc.comp (e.symm.injective.comp (Set.image_injective.mpr f.injective)))

end Lemmatheca.SetTheory.BooleanAlgebras
