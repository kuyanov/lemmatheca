import Lemmatheca.RiceShapiroTheorem.Fragments
import Lemmatheca.UniformSelfReference.Uniform
import Mathlib.Order.Interval.Set.Nat

/-! Actual tagged searches, switch selectors and input-bound cutoff selectors. -/
namespace Lemmatheca.ComputabilityTheory.RiceShapiroTheorem

open UniversalComputation UniformSelfReference
open RicesTheorem (Extensional)

noncomputable section
open Classical

/-- Code w decodes to (tag, stage, bounded-evaluation resource). -/
def switchOffer (r j e d x w : ℕ) : Option ℕ :=
  let a := w.unpair.1
  let t := w.unpair.2.unpair.1
  let k := w.unpair.2.unpair.2
  if a = 0 ∧ 0 < boundedValue k e x then some (boundedValue k e x - 1)
  else if a = 1 ∧ H r j t ∧ 0 < boundedValue k d x then
    some (boundedValue k d x - 1)
  else none

def switch (r j e d x : ℕ) : Part ℕ := Nat.rfindOpt (switchOffer r j e d x)

def switchFamily (j a x : ℕ) : Part ℕ :=
  switch a.unpair.1 j a.unpair.2.unpair.1 a.unpair.2.unpair.2 x

theorem switch_offer_primitive :
    Primrec (fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) =>
      switchOffer p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2.1 p.2.2) := by
  let R := fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => p.1.1.1
  let J := fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => p.1.1.2
  let E := fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => p.1.2.1
  let D := fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => p.1.2.2
  let X := fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => p.2.1
  let A := fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => p.2.2.unpair.1
  let T := fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => p.2.2.unpair.2.unpair.1
  let K := fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => p.2.2.unpair.2.unpair.2
  have hr : Primrec R := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hj : Primrec J := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec E := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hd : Primrec D := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec X := Primrec.fst.comp Primrec.snd
  have hu : Primrec (fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => p.2.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec A := Primrec.fst.comp hu
  have hv := Primrec.unpair.comp (Primrec.snd.comp hu)
  have ht : Primrec T := Primrec.fst.comp hv
  have hk : Primrec K := Primrec.snd.comp hv
  have hbE := boundedValue_primitive.comp ((hk.pair he).pair hx)
  have hbD := boundedValue_primitive.comp ((hk.pair hd).pair hx)
  have h0 := (Primrec.eq.comp ha (Primrec.const 0)).and
    (Primrec.nat_lt.comp (Primrec.const 0) hbE)
  have h1 := (Primrec.eq.comp ha (Primrec.const 1)).and
    ((EffectiveEnumerations.stage_predicate_primitive.comp ((hr.pair ht).pair hj)).and
      (Primrec.nat_lt.comp (Primrec.const 0) hbD))
  exact Primrec.ite h0 (Primrec.option_some.comp (Primrec.nat_sub.comp hbE (Primrec.const 1)))
    (Primrec.ite h1 (Primrec.option_some.comp (Primrec.nat_sub.comp hbD (Primrec.const 1)))
      (Primrec.const none))

set_option backward.isDefEq.respectTransparency false in
theorem switch_family_partial :
    Partrec (fun p : ℕ × (ℕ × ℕ) => switchFamily p.1 p.2.1 p.2.2) := by
  have ho : Computable₂ (fun (p : ℕ × (ℕ × ℕ)) w =>
      switchOffer p.2.1.unpair.1 p.1 p.2.1.unpair.2.unpair.1
        p.2.1.unpair.2.unpair.2 p.2.2 w) := by
    have u : Computable (fun p : (ℕ × (ℕ × ℕ)) × ℕ => p.1.2.1.unpair) :=
      Computable.unpair.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    let v := Computable.unpair.comp (Computable.snd.comp u)
    have hp : Computable (fun p : (ℕ × (ℕ × ℕ)) × ℕ =>
        (((p.1.2.1.unpair.1, p.1.1),
          (p.1.2.1.unpair.2.unpair.1, p.1.2.1.unpair.2.unpair.2)), (p.1.2.2, p.2))) :=
      (((Computable.fst.comp u).pair (Computable.fst.comp Computable.fst)).pair
        ((Computable.fst.comp v).pair (Computable.snd.comp v))).pair
          ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
    have hm := switch_offer_primitive.to_comp.comp hp
    exact hm.of_eq (fun _ => rfl)
  exact Partrec.rfindOpt ho

def switchFamilyProgram : ℕ := Classical.choose (partial_family_index switch_family_partial)

theorem switchFamilyProgram_spec : ∀ j a x,
    phi switchFamilyProgram (Nat.pair j (Nat.pair a x)) = switchFamily j a x := by
  exact Classical.choose_spec (partial_family_index switch_family_partial)

def switchAuxiliary : ℕ := Classical.choose
  (specified_partial_family_selector switchFamilyProgram switchFamilyProgram_spec)

def switchSeed : ℕ := RecursionTheorem.selfSpecialize switchAuxiliary

def switchIndex (r e d : ℕ) : ℕ :=
  specialize switchSeed (Nat.pair r (Nat.pair e d))

theorem switchIndex_primitive :
    Primrec (fun p : ℕ × (ℕ × ℕ) => switchIndex p.1 p.2.1 p.2.2) := by
  exact specialize_primitive.comp (Primrec.const _)
    (Primrec₂.natPair.comp Primrec.fst
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem switchIndex_eval (r e d x : ℕ) :
    phi (switchIndex r e d) x = switch r (switchIndex r e d) e d x := by
  have hs := (Classical.choose_spec
    (specified_partial_family_selector switchFamilyProgram switchFamilyProgram_spec)).2.2
  simpa only [switchIndex, switchSeed, switchAuxiliary, UniformSelfReference.selector, switchFamily,
    Nat.unpair_pair] using hs (Nat.pair r (Nat.pair e d)) x

theorem switchIndex_cases (r e d : ℕ) (h : GraphInclusion (phi e) (phi d)) :
    (switchIndex r e d ∉ W r → phi (switchIndex r e d) = phi e) ∧
    (switchIndex r e d ∈ W r → phi (switchIndex r e d) = phi d) := by
  have hm (j x y : ℕ) : y ∈ switch r j e d x ↔
      y ∈ phi e x ∨ (j ∈ W r ∧ y ∈ phi d x) := by
    have offer (w z : ℕ) : z ∈ switchOffer r j e d x w ↔
        (w.unpair.1 = 0 ∧ boundedValue w.unpair.2.unpair.2 e x = z + 1) ∨
        (w.unpair.1 = 1 ∧ H r j w.unpair.2.unpair.1 ∧
          boundedValue w.unpair.2.unpair.2 d x = z + 1) := by
      unfold switchOffer
      dsimp only
      split_ifs <;> simp_all [Option.mem_def] <;> omega
    have sound (w z : ℕ) (hz : z ∈ switchOffer r j e d x w) :
        z ∈ phi e x ∨ (j ∈ W r ∧ z ∈ phi d x) := by
      rcases (offer w z).mp hz with ⟨_, hk⟩ | ⟨_, ht, hk⟩
      · exact Or.inl ((phi_output e x z).mpr ⟨_, hk⟩)
      · exact Or.inr ⟨(EffectiveEnumerations.stage_union r j).mpr ⟨_, ht⟩,
          (phi_output d x z).mpr ⟨_, hk⟩⟩
    constructor
    · intro hy
      obtain ⟨w, hw⟩ := Nat.rfindOpt_spec hy
      exact sound w y hw
    · intro hy
      have hex : ∃ w, y ∈ switchOffer r j e d x w := by
        rcases hy with hy | ⟨hj, hy⟩
        · obtain ⟨k, hk⟩ := (phi_output e x y).mp hy
          exact ⟨Nat.pair 0 (Nat.pair 0 k), (offer _ _).mpr (Or.inl (by simp [hk]))⟩
        · obtain ⟨t, ht⟩ := (EffectiveEnumerations.stage_union r j).mp hj
          obtain ⟨k, hk⟩ := (phi_output d x y).mp hy
          exact ⟨Nat.pair 1 (Nat.pair t k), (offer _ _).mpr (Or.inr (by simp [H, ht, hk]))⟩
      have hh : (switch r j e d x).Dom := Nat.rfindOpt_dom.mpr (by
        obtain ⟨w, hw⟩ := hex; exact ⟨w, y, hw⟩)
      obtain ⟨w, hw⟩ := Nat.rfindOpt_spec (Part.get_mem hh)
      have hyD : y ∈ phi d x := hy.elim (h x y) And.right
      have hzD : (switch r j e d x).get hh ∈ phi d x :=
        (sound w _ hw).elim (h x _) And.right
      have heq := Part.mem_unique hzD hyD
      simpa only [heq] using Part.get_mem hh
  constructor
  · intro hj
    funext x
    apply Part.ext
    intro y
    rw [switchIndex_eval, hm]
    simp only [hj, false_and, or_false]
  · intro hj
    funext x
    apply Part.ext
    intro y
    rw [switchIndex_eval, hm]
    exact ⟨fun hy => hy.elim (h x y) And.right, fun hy => Or.inr ⟨hj, hy⟩⟩

theorem upward_closure (r e d : ℕ) (hA : Extensional (W r))
    (he : e ∈ W r) (hed : GraphInclusion (phi e) (phi d)) : d ∈ W r := by
  let j := switchIndex r e d
  have hj : j ∈ W r := by
    by_contra hn
    exact hn ((hA j e ((switchIndex_cases r e d hed).1 hn)).mpr he)
  exact (hA j d ((switchIndex_cases r e d hed).2 hj)).mp hj

def cutoff (r j e x : ℕ) : Part ℕ :=
  if H r j x then Part.none else phi e x

def cutoffFamily (j a x : ℕ) : Part ℕ := cutoff a.unpair.1 j a.unpair.2 x

theorem cutoff_family_partial :
    Partrec (fun p : ℕ × (ℕ × ℕ) => cutoffFamily p.1 p.2.1 p.2.2) := by
  have hp : PrimrecPred (fun p : ℕ × (ℕ × ℕ) =>
      H p.2.1.unpair.1 p.1 p.2.2) :=
    EffectiveEnumerations.stage_predicate_primitive.comp
      (((Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))).pair
        (Primrec.snd.comp Primrec.snd)).pair Primrec.fst)
  have he : Partrec (fun p : ℕ × (ℕ × ℕ) => phi p.2.1.unpair.2 p.2.2) :=
    phi_recursive.comp
      (Computable.snd.comp (Computable.unpair.comp (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)
  simpa only [Bool.cond_decide, cutoffFamily, cutoff] using
    Partrec.cond hp.decide.to_comp Partrec.none he

def cutoffFamilyProgram : ℕ := Classical.choose (partial_family_index cutoff_family_partial)

theorem cutoffFamilyProgram_spec : ∀ j a x,
    phi cutoffFamilyProgram (Nat.pair j (Nat.pair a x)) = cutoffFamily j a x := by
  exact Classical.choose_spec (partial_family_index cutoff_family_partial)

def cutoffAuxiliary : ℕ := Classical.choose
  (specified_partial_family_selector cutoffFamilyProgram cutoffFamilyProgram_spec)

def cutoffSeed : ℕ := RecursionTheorem.selfSpecialize cutoffAuxiliary

def cutoffIndex (r e : ℕ) : ℕ := specialize cutoffSeed (Nat.pair r e)

theorem cutoffIndex_primitive : Primrec₂ cutoffIndex := by
  exact specialize_primitive.comp (Primrec.const _) Primrec₂.natPair

theorem cutoffIndex_eval (r e x : ℕ) :
    phi (cutoffIndex r e) x = cutoff r (cutoffIndex r e) e x := by
  have hs := (Classical.choose_spec
    (specified_partial_family_selector cutoffFamilyProgram cutoffFamilyProgram_spec)).2.2
  simpa only [cutoffIndex, cutoffSeed, cutoffAuxiliary, UniformSelfReference.selector, cutoffFamily,
    Nat.unpair_pair] using hs (Nat.pair r e) x

theorem cutoffIndex_cases (r e : ℕ) :
    (cutoffIndex r e ∉ W r → phi (cutoffIndex r e) = phi e) ∧
    (∀ t, H r (cutoffIndex r e) t →
      (∀ s < t, ¬ H r (cutoffIndex r e) s) →
      ∀ x, phi (cutoffIndex r e) x = if x < t then phi e x else Part.none) := by
  constructor
  · intro hj
    funext x
    rw [cutoffIndex_eval, cutoff, ite_eq_right]
    exact fun hh => hj ((EffectiveEnumerations.stage_union r _).mpr ⟨x, hh⟩)
  · intro t ht hmin x
    rw [cutoffIndex_eval, cutoff]
    by_cases hx : x < t
    · rw [ite_eq_right (hmin x hx), ite_eq_left hx]
    · have hh : H r (cutoffIndex r e) x :=
        EffectiveEnumerations.stage_monotone r (Nat.le_of_not_gt hx) ht
      rw [ite_eq_left hh, ite_eq_right hx]

theorem finite_accepted_subfunction (r e : ℕ) (hA : Extensional (W r))
    (he : e ∈ W r) :
    cutoffIndex r e ∈ W r ∧ GraphInclusion (phi (cutoffIndex r e)) (phi e) ∧
      ∃ t, (∀ x, phi (cutoffIndex r e) x = if x < t then phi e x else Part.none) ∧
        FiniteGraph (phi (cutoffIndex r e)) ∧ (graph (phi (cutoffIndex r e))).ncard ≤ t := by
  let j := cutoffIndex r e
  have hj : j ∈ W r := by
    by_contra hn
    exact hn ((hA j e ((cutoffIndex_cases r e).1 hn)).mpr he)
  obtain ⟨t, ht, hmin⟩ : ∃ t, H r j t ∧ ∀ s < t, ¬ H r j s := by
    have hex := (EffectiveEnumerations.stage_union r j).mp hj
    exact ⟨Nat.find hex, Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩
  have hres := (cutoffIndex_cases r e).2 t ht hmin
  have hb : ∀ p ∈ graph (phi j), p.1 < t := by
    intro p hp
    by_contra hn
    have hnone : phi j p.1 = Part.none := by rw [hres, ite_eq_right hn]
    rw [graph, Set.mem_ofPred_eq, hnone] at hp
    exact Part.notMem_none _ hp
  have hinj : Set.InjOn Prod.fst (graph (phi j)) := by
    intro a ha b hb heq
    apply Prod.ext heq
    change a.2 ∈ phi j a.1 at ha
    change b.2 ∈ phi j b.1 at hb
    rw [heq] at ha
    exact Part.mem_unique ha hb
  have hfinite : FiniteGraph (phi j) :=
    Set.Finite.of_injOn (f := Prod.fst) (t := Set.Iio t) hb hinj (Set.finite_Iio t)
  refine ⟨hj, ?_, t, hres, hfinite, ?_⟩
  · intro x y hy
    rw [hres] at hy
    split_ifs at hy with hx
    · exact hy
    · exact (Part.notMem_none _ hy).elim
  · simpa only [Set.ncard_Iio_nat] using
      Set.ncard_le_ncard_of_injOn Prod.fst hb hinj (Set.finite_Iio t)

end
end Lemmatheca.ComputabilityTheory.RiceShapiroTheorem
