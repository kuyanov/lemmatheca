import Lemmatheca.EffectiveOperators.Rules

/-! One ordinary dovetailed search and its actual two-parameter compiler. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveOperators

open UniversalComputation RiceShapiroTheorem
open RicesTheorem (PartialFunction)

noncomputable section
open Classical

/-- The candidate unpairs as (d,(y,(s,t))). -/
def ruleOffer (r e x w : ℕ) : Option ℕ :=
  let d := w.unpair.1
  let y := w.unpair.2.unpair.1
  let s := w.unpair.2.unpair.2.unpair.1
  let t := w.unpair.2.unpair.2.unpair.2
  if Valid d ∧ ruleCode d x y ∈ EffectiveEnumerations.stage r s ∧ Match e d t
  then some y else none

def ruleSearch (r e x : ℕ) : Part ℕ := Nat.rfindOpt (ruleOffer r e x)

theorem rule_offer_primitive :
    Primrec (fun p : (ℕ × (ℕ × ℕ)) × ℕ =>
      ruleOffer p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hr : Primrec (fun p : (ℕ × (ℕ × ℕ)) × ℕ => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have he : Primrec (fun p : (ℕ × (ℕ × ℕ)) × ℕ => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec (fun p : (ℕ × (ℕ × ℕ)) × ℕ => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hu : Primrec (fun p : (ℕ × (ℕ × ℕ)) × ℕ => p.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  have hd := Primrec.fst.comp hu
  have hv := Primrec.unpair.comp (Primrec.snd.comp hu)
  have hy := Primrec.fst.comp hv
  have hv' := Primrec.unpair.comp (Primrec.snd.comp hv)
  have hs := Primrec.fst.comp hv'
  have ht := Primrec.snd.comp hv'
  have hcode := Primrec₂.natPair.comp hd (Primrec₂.natPair.comp hx hy)
  exact (Primrec.ite ((valid_primitive.comp hd).and
    ((EffectiveEnumerations.stage_predicate_primitive.comp ((hr.pair hs).pair hcode)).and
      (match_primitive.comp ((he.pair hd).pair ht))))
    (Primrec.option_some.comp hy) (Primrec.const none)).of_eq (fun _ => rfl)

theorem rule_search_partial :
    Partrec (fun p : ℕ × (ℕ × ℕ) => ruleSearch p.1 p.2.1 p.2.2) := by
  exact Partrec.rfindOpt rule_offer_primitive.to_comp.to₂

def ruleSearchProgram : ℕ :=
  Classical.choose (UniformSelfReference.partial_family_index rule_search_partial)

theorem ruleSearchProgram_spec (r e x : ℕ) :
    phi ruleSearchProgram (Nat.pair r (Nat.pair e x)) = ruleSearch r e x := by
  exact Classical.choose_spec
    (UniformSelfReference.partial_family_index rule_search_partial) r e x

def compiler (r e : ℕ) : ℕ :=
  UniformSelfReference.partialFamilyCompiler ruleSearchProgram r e

theorem compiler_eval (r e x : ℕ) :
    phi (compiler r e) x = ruleSearch r e x := by
  rw [compiler, UniformSelfReference.partial_family_compiler_eval, ruleSearchProgram_spec]

private theorem successful_offer (R : RuleRelation) (r : ℕ) (hr : EnumeratesRules r R)
    (e x w y : ℕ) (hy : y ∈ ruleOffer r e x w) : RuleOutput R (phi e) x y := by
  dsimp only [ruleOffer] at hy
  split_ifs at hy with h
  · have hv := Option.mem_some_iff.mp hy
    subst y
    refine ⟨w.unpair.1, (match_iff e _ h.1).mpr ⟨_, h.2.2⟩, ?_⟩
    exact (hr _ _ _).mp ((EffectiveEnumerations.stage_union r _).mpr ⟨_, h.2.1⟩)
  · simp at hy

private theorem successful_search (R : RuleRelation) (r : ℕ) (hr : EnumeratesRules r R)
    (e x y : ℕ) (hy : y ∈ ruleSearch r e x) : RuleOutput R (phi e) x y := by
  obtain ⟨w, hw⟩ := Nat.rfindOpt_spec hy
  exact successful_offer R r hr e x w y hw

theorem compiler_correct (R : RuleRelation) (r : ℕ) (hr : EnumeratesRules r R)
    (hpos : Positive R) (hcoh : Coherent R) (e x : ℕ) :
    phi (compiler r e) x = operator R (phi e) x := by
  rw [compiler_eval]
  apply Part.ext
  intro y
  rw [operator_mem R hpos hcoh]
  constructor
  · exact successful_search R r hr e x y
  · intro hy
    obtain ⟨d, hdf, hdR⟩ := hy
    have hd := hpos d x y hdR
    obtain ⟨s, hs⟩ := (EffectiveEnumerations.stage_union r _).mp ((hr d x y).mpr hdR)
    obtain ⟨t, ht⟩ := (match_iff e d hd).mp hdf
    have hdom : (ruleSearch r e x).Dom := Nat.rfindOpt_dom.mpr
      ⟨Nat.pair d (Nat.pair y (Nat.pair s t)), y,
        by simp [ruleOffer, hd, hs, ht]⟩
    have hz := Part.get_mem hdom
    have heq := rule_output_unique R hpos hcoh (phi e) x _ y
      (successful_search R r hr e x _ hz) ⟨d, hdf, hdR⟩
    simpa only [heq] using hz

def IndexExtensional (H : ℕ → ℕ) : Prop :=
  ∀ e b, phi e = phi b → phi (H e) = phi (H b)

def IsExtensionalTransformation (H : ℕ → ℕ) : Prop := Computable H ∧ IndexExtensional H

theorem compiler_extensional (R : RuleRelation) (r : ℕ) (hr : EnumeratesRules r R)
    (hpos : Positive R) (hcoh : Coherent R) : IndexExtensional (compiler r) := by
  intro e b hab
  funext x
  rw [compiler_correct R r hr hpos hcoh, compiler_correct R r hr hpos hcoh, hab]

end
end Lemmatheca.ComputabilityTheory.EffectiveOperators
