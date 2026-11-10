import Lemmatheca.EffectiveOperators.Compiler

/-! The actual joint canonical-rule recognizer associated to an extensional map. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveOperators

open UniversalComputation RiceShapiroTheorem
open RicesTheorem (PartialFunction)

noncomputable section
open Classical

private def checkedOutput {α : Type*} (f : α → Part ℕ) (g : α → ℕ) (a : α) : Part ℕ :=
  (f a).bind fun v => if v = g a then Part.some 0 else Part.none

private theorem checked_output_partial {α : Type*} [Primcodable α]
    (f : α → Part ℕ) (g : α → ℕ) (hf : Partrec f) (hg : Computable g) :
    Partrec (checkedOutput f g) := by
  have hc : Computable (fun p : α × ℕ => decide (p.2 = g p.1)) :=
    Primrec.eq.decide.to_comp.comp Computable.snd (hg.comp Computable.fst)
  have hfilter : Partrec (fun p : α × ℕ =>
      if p.2 = g p.1 then Part.some 0 else Part.none) :=
    (Partrec.cond hc (Computable.const 0).partrec Partrec.none).of_eq
      (fun p => by simp only [Bool.cond_decide]; split_ifs <;> rfl)
  exact hf.bind hfilter.to₂

private theorem checked_output_domain {α : Type*} (f : α → Part ℕ) (g : α → ℕ) (a : α) :
    (checkedOutput f g a).Dom ↔ g a ∈ f a := by
  rw [Part.dom_iff_mem]
  simp only [checkedOutput, Part.mem_bind_iff]
  constructor
  · rintro ⟨out, v, hv, hout⟩
    split_ifs at hout with h
    · exact h ▸ hv
    · exact (Part.notMem_none _ hout).elim
  · intro h
    exact ⟨0, g a, h, by simp⟩

private theorem value_enumerable {α : Type*} [Primcodable α]
    (f : α → Part ℕ) (g : α → ℕ) (hf : Partrec f) (hg : Computable g) :
    REPred (fun a => g a ∈ f a) :=
  (checked_output_partial f g hf hg).dom_re.of_eq (checked_output_domain f g)

def outputProperty (H : ℕ → ℕ) (x y : ℕ) : Set ℕ := {e | y ∈ phi (H e) x}

theorem output_property_enumerable (H : ℕ → ℕ) (hH : Computable H) (x y : ℕ) :
    REPred (fun e => e ∈ outputProperty H x y) := by
  exact value_enumerable (fun e => phi (H e) x) (fun _ => y)
    (phi_recursive.comp hH (Computable.const x)) (Computable.const y)

theorem output_property_extensional (H : ℕ → ℕ) (hext : IndexExtensional H) (x y : ℕ) :
    RicesTheorem.Extensional (outputProperty H x y) := by
  intro e b h
  change (y ∈ phi (H e) x) ↔ (y ∈ phi (H b) x)
  rw [hext e b h]

theorem output_jointly_enumerable (H : ℕ → ℕ) (hH : Computable H) :
    REPred (fun z : ℕ =>
      z.unpair.2.unpair.2 ∈ phi (H z.unpair.1) z.unpair.2.unpair.1) := by
  have hu : Computable (fun z : ℕ => z.unpair) := Computable.unpair
  have hv := Computable.unpair.comp (Computable.snd.comp hu)
  exact value_enumerable _ _
    (phi_recursive.comp (hH.comp (Computable.fst.comp hu)) (Computable.fst.comp hv))
    (Computable.snd.comp hv)

def canonicalRules (H : ℕ → ℕ) : RuleRelation :=
  fun d x y => Valid d ∧ y ∈ phi (H (fragmentIndex d)) x

/-- Input z unpairs to (d,(x,y)); invalid codes and wrong outputs diverge. -/
def canonicalRecognizer (a z : ℕ) : Part ℕ :=
  let d := z.unpair.1
  let x := z.unpair.2.unpair.1
  let y := z.unpair.2.unpair.2
  if Valid d then
    (phi a (fragmentIndex d)).bind fun j =>
      (phi j x).bind fun v => if v = y then Part.some 0 else Part.none
  else Part.none

theorem canonical_recognizer_partial : Partrec₂ canonicalRecognizer := by
  have hu : Computable (fun p : ℕ × ℕ => p.2.unpair) :=
    Computable.unpair.comp Computable.snd
  have hd := Computable.fst.comp hu
  have hv := Computable.unpair.comp (Computable.snd.comp hu)
  have hx := Computable.fst.comp hv
  have hy := Computable.snd.comp hv
  have hfirst : Partrec (fun p : ℕ × ℕ => phi p.1 (fragmentIndex p.2.unpair.1)) :=
    phi_recursive.comp Computable.fst (fragmentIndex_primitive.to_comp.comp hd)
  have hrun : Partrec (fun p : ℕ × ℕ =>
      (phi p.1 (fragmentIndex p.2.unpair.1)).bind fun j => phi j p.2.unpair.2.unpair.1) :=
    hfirst.bind (phi_recursive.comp Computable.snd (hx.comp Computable.fst)).to₂
  have hcheck := checked_output_partial _ _ hrun hy
  have hvld : Computable (fun p : ℕ × ℕ => decide (Valid p.2.unpair.1)) :=
    valid_primitive.decide.to_comp.comp hd
  have hc : Partrec (fun p : ℕ × ℕ => canonicalRecognizer p.1 p.2) :=
    (Partrec.cond hvld hcheck Partrec.none).of_eq (fun p => by
      simp only [Bool.cond_decide, canonicalRecognizer, checkedOutput, Part.bind_assoc])
  exact hc.to₂

theorem canonical_recognizer_output (a d x y v : ℕ) :
    v ∈ canonicalRecognizer a (ruleCode d x y) ↔
      v = 0 ∧ Valid d ∧ ∃ j, j ∈ phi a (fragmentIndex d) ∧ y ∈ phi j x := by
  simp only [canonicalRecognizer, ruleCode, Nat.unpair_pair]
  split_ifs with hd
  · simp only [Part.mem_bind_iff]
    constructor
    · rintro ⟨j, hj, out, hout, hv⟩
      split_ifs at hv with heq
      · exact ⟨Part.mem_some_iff.mp hv, hd, j, hj, heq ▸ hout⟩
      · exact (Part.notMem_none _ hv).elim
    · rintro ⟨rfl, _, j, hj, hy⟩
      exact ⟨j, hj, y, hy, by simp⟩
  · simp [hd]

def canonicalRecognizerProgram : ℕ :=
  Classical.choose (phi_complete (Partrec₂.unpaired'.mpr canonical_recognizer_partial))

theorem canonicalRecognizerProgram_spec (a z : ℕ) :
    phi canonicalRecognizerProgram (Nat.pair a z) = canonicalRecognizer a z := by
  have h := Classical.choose_spec
    (phi_complete (Partrec₂.unpaired'.mpr canonical_recognizer_partial))
  simpa only [canonicalRecognizerProgram, Nat.unpaired, Nat.unpair_pair] using
    congrFun h (Nat.pair a z)

def canonicalRuleIndex (a : ℕ) : ℕ := specialize canonicalRecognizerProgram a

theorem canonical_rule_index_eval (a z : ℕ) :
    phi (canonicalRuleIndex a) z = canonicalRecognizer a z := by
  rw [canonicalRuleIndex, specialize_eval, canonicalRecognizerProgram_spec]

theorem canonical_rule_index_correct (H : ℕ → ℕ) (a : ℕ)
    (ha : ∀ n, phi a n = Part.some (H n)) :
    EnumeratesRules (canonicalRuleIndex a) (canonicalRules H) := by
  intro d x y
  change (phi (canonicalRuleIndex a) (ruleCode d x y)).Dom ↔ _
  rw [canonical_rule_index_eval, Part.dom_iff_mem]
  simp only [canonical_recognizer_output, ha, Part.mem_some_iff]
  constructor
  · rintro ⟨_, _, hd, j, hj, hy⟩
    subst j
    exact ⟨hd, hy⟩
  · rintro ⟨hd, hy⟩
    exact ⟨0, rfl, hd, H (fragmentIndex d), rfl, hy⟩

theorem canonical_rules_positive (H : ℕ → ℕ) : Positive (canonicalRules H) := by
  intro d x y h
  exact h.1

theorem canonical_rules_enumerable (H : ℕ → ℕ) (hH : Computable H) :
    JointlyEnumerable (canonicalRules H) := by
  obtain ⟨a, ha⟩ := phi_complete (Partrec.nat_iff.mp hH.partrec)
  apply (jointly_enumerable_iff_index _).mpr
  exact ⟨canonicalRuleIndex a, canonical_rule_index_correct H a (fun n => congrFun ha n)⟩

theorem canonical_rules_output (H : ℕ → ℕ) (hH : Computable H)
    (hext : IndexExtensional H) (e x y : ℕ) :
    y ∈ phi (H e) x ↔
      ∃ d, GraphInclusion (fragment d) (phi e) ∧ canonicalRules H d x y := by
  have hb := canonicalBasis_correct (outputProperty H x y)
    (output_property_enumerable H hH x y) (output_property_extensional H hext x y)
  constructor
  · intro h
    obtain ⟨d, hd, hde⟩ := (hb.2.2 e).mp h
    exact ⟨d, hde, hd⟩
  · rintro ⟨d, hde, hd⟩
    exact (hb.2.2 e).mpr ⟨d, hd, hde⟩

theorem canonical_rules_coherent (H : ℕ → ℕ) (hH : Computable H)
    (hext : IndexExtensional H) : Coherent (canonicalRules H) := by
  intro d c x y z hd hc hcompat
  let b := pairListCode (pairList d ++ pairList c)
  obtain ⟨_, hdb, hcb⟩ := compatible_common_fragment d c hcompat
  have hb : phi (fragmentIndex b) = fragment b := funext (fragmentIndex_eval b)
  have hy : y ∈ phi (H (fragmentIndex b)) x :=
    (canonical_rules_output H hH hext (fragmentIndex b) x y).mpr
      ⟨d, by simpa only [hb] using hdb, hd⟩
  have hz : z ∈ phi (H (fragmentIndex b)) x :=
    (canonical_rules_output H hH hext (fragmentIndex b) x z).mpr
      ⟨c, by simpa only [hb] using hcb, hc⟩
  exact Part.mem_unique hy hz

theorem canonical_operator_effective (H : ℕ → ℕ) (hH : Computable H)
    (hext : IndexExtensional H) : IsEffective (operator (canonicalRules H)) := by
  exact ⟨canonicalRules H, canonical_rules_positive H, canonical_rules_coherent H hH hext,
    canonical_rules_enumerable H hH, rfl⟩

theorem canonical_operator_correct (H : ℕ → ℕ) (hH : Computable H)
    (hext : IndexExtensional H) (e : ℕ) :
    operator (canonicalRules H) (phi e) = phi (H e) := by
  funext x
  apply Part.ext
  intro y
  rw [operator_mem _ (canonical_rules_positive H) (canonical_rules_coherent H hH hext)]
  exact (canonical_rules_output H hH hext e x y).symm

def canonicalCompiler (a e : ℕ) : ℕ := compiler (canonicalRuleIndex a) e

theorem canonical_compiler_primitive : Primrec₂ canonicalCompiler := by
  have hr : Primrec canonicalRuleIndex :=
    specialize_primitive.comp (Primrec.const canonicalRecognizerProgram) Primrec.id
  exact (UniformSelfReference.partial_family_compiler_primitive ruleSearchProgram).comp
    (hr.comp Primrec.fst) Primrec.snd

theorem canonical_compiler_correct (H : ℕ → ℕ) (hH : Computable H)
    (hext : IndexExtensional H) (a : ℕ) (ha : ∀ n, phi a n = Part.some (H n))
    (e x : ℕ) : phi (canonicalCompiler a e) x = phi (H e) x := by
  rw [canonicalCompiler,
    compiler_correct (canonicalRules H) (canonicalRuleIndex a)
      (canonical_rule_index_correct H a ha) (canonical_rules_positive H)
      (canonical_rules_coherent H hH hext), canonical_operator_correct H hH hext]

end
end Lemmatheca.ComputabilityTheory.EffectiveOperators
