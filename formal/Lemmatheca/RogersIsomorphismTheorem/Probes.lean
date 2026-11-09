import Lemmatheca.UniformSelfReference.Numberings
import Lemmatheca.CodingFiniteSequences.FiniteSequenceCoding

/-! Uniform self-referential probes, tested after the supplied reverse compiler.
The only choices select two fixed program indices before numerical parameters vary. -/
namespace Lemmatheca.ComputabilityTheory.Rogers

open UniversalComputation UniformSelfReference
open scoped Classical

noncomputable section

def forbidden (b : ℕ → ℕ) (hcode : ℕ) : List ℕ :=
  (FiniteSequenceCoding.decode hcode).map b

def firstRule (b : ℕ → ℕ) (j a z : ℕ) : Part ℕ :=
  if b j ∈ forbidden b a.unpair.2 then Part.none else phi a.unpair.1 z

def rescueRule (b : ℕ → ℕ) (j hcode _z : ℕ) : Part ℕ :=
  if b j ∈ forbidden b hcode then Part.some 1 else Part.none

private def IsProbeCodes (b : ℕ → ℕ) (q : ℕ × ℕ) : Prop :=
  (∀ a z, phi (specialize q.1 a) z = firstRule b (specialize q.1 a) a z) ∧
    ∀ hcode z, phi (specialize q.2 hcode) z =
      rescueRule b (specialize q.2 hcode) hcode z

private theorem computable_map (b : ℕ → ℕ) (hb : Computable b) :
    Computable (fun l : List ℕ => l.map b) := by
  let build (l : List ℕ) : ℕ → List ℕ :=
    Nat.rec [] (fun k old => old ++ [b (l[k]?.getD 0)])
  have hstep : Computable₂ (fun l : List ℕ => fun p : ℕ × List ℕ =>
      p.2 ++ [b (l[p.1]?.getD 0)]) := by
    exact (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hb.comp (Primrec.option_getD.to_comp.comp
        (Computable.list_getElem?.comp Computable.fst (Computable.fst.comp Computable.snd))
        (Computable.const 0)))).to₂
  have hc : Computable (fun l : List ℕ => build l l.length) :=
    Computable.nat_rec Computable.list_length (Computable.const []) hstep
  apply hc.of_eq
  intro l
  have he (k : ℕ) : build l k = (List.range k).map (fun i => b (l[i]?.getD 0)) := by
    induction k with
    | zero => rfl
    | succ k ih => simp [build, List.range_succ, ih]
  rw [he]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simp [List.getElem?_eq_getElem hi]

private theorem membership_computable :
    Computable₂ (fun (l : List ℕ) j => decide (j ∈ l)) := by
  exact ((PrimrecRel.exists_mem_list Primrec.eq).decide.to_comp).of_eq
    (fun p => by simp)

private theorem forbidden_computable (b : ℕ → ℕ) (hb : Computable b) :
    Computable (forbidden b) :=
  (computable_map b hb).comp (Primrec.ofNat (List ℕ)).to_comp

private theorem probe_codes_exist (b : ℕ → ℕ) (hb : Computable b) :
    ∃ q : ℕ × ℕ, IsProbeCodes b q := by
  have htestN : Computable (fun t : ℕ × (ℕ × ℕ) =>
      decide (b t.1 ∈ forbidden b t.2.1.unpair.2)) :=
    membership_computable.comp
      ((forbidden_computable b hb).comp
        (Computable.snd.comp (Computable.unpair.comp (Computable.fst.comp Computable.snd))))
      (hb.comp Computable.fst)
  have htestM : Computable (fun t : ℕ × (ℕ × ℕ) =>
      decide (b t.1 ∈ forbidden b t.2.1)) :=
    membership_computable.comp
      ((forbidden_computable b hb).comp (Computable.fst.comp Computable.snd))
      (hb.comp Computable.fst)
  have hN : Partrec (fun t : ℕ × (ℕ × ℕ) => firstRule b t.1 t.2.1 t.2.2) := by
    exact (Partrec.cond htestN Partrec.none
      (phi_recursive.comp
        (Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp Computable.snd)))
        (Computable.snd.comp Computable.snd))).of_eq (fun t => by simp [firstRule])
  have hM : Partrec (fun t : ℕ × (ℕ × ℕ) => rescueRule b t.1 t.2.1 t.2.2) := by
    exact (Partrec.cond htestM (Partrec.const' (Part.some 1)) Partrec.none).of_eq
      (fun t => by simp [rescueRule])
  obtain ⟨pN, hpN⟩ := partial_family_index hN
  obtain ⟨rN, _, _, hrN⟩ := specified_partial_family_selector pN hpN
  obtain ⟨pM, hpM⟩ := partial_family_index hM
  obtain ⟨rM, _, _, hrM⟩ := specified_partial_family_selector pM hpM
  exact ⟨(RecursionTheorem.selfSpecialize rN, RecursionTheorem.selfSpecialize rM), hrN, hrM⟩

private def selectedProbeCodes (b : ℕ → ℕ) (hb : Computable b) : ℕ × ℕ :=
  Classical.choose (probe_codes_exist b hb)

def firstProbe {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e hcode : ℕ) : ℕ :=
  specialize (selectedProbeCodes C.backward C.backward_computable).1 (Nat.pair e hcode)

def rescueProbe {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (hcode : ℕ) : ℕ :=
  specialize (selectedProbeCodes C.backward C.backward_computable).2 hcode

/-- The same two fixed specialization indices work simultaneously for all inputs. -/
theorem probe_selection {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    (∃ qN qM : ℕ,
      (∀ e hcode, firstProbe C e hcode = specialize qN (Nat.pair e hcode)) ∧
      ∀ hcode, rescueProbe C hcode = specialize qM hcode) ∧
    Primrec₂ (firstProbe C) ∧ Primrec (rescueProbe C) ∧
    (∀ e hcode z, phi (firstProbe C e hcode) z =
      if C.backward (firstProbe C e hcode) ∈ forbidden C.backward hcode
      then Part.none else phi e z) ∧
    ∀ hcode z, phi (rescueProbe C hcode) z =
      if C.backward (rescueProbe C hcode) ∈ forbidden C.backward hcode
      then Part.some 1 else Part.none := by
  let q := selectedProbeCodes C.backward C.backward_computable
  have hq : IsProbeCodes C.backward q :=
    Classical.choose_spec (probe_codes_exist C.backward C.backward_computable)
  refine ⟨⟨q.1, q.2, fun _ _ => rfl, fun _ => rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact specialize_primitive.comp (Primrec.const q.1) Primrec₂.natPair
  · exact selector_primitive q.2
  · intro e hcode z
    have hn := hq.1 (Nat.pair e hcode) z
    simp only [firstRule, Nat.unpair_pair] at hn
    exact hn
  · intro hcode z
    exact hq.2 hcode z

theorem first_probe_escapes {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e hcode : ℕ)
    (h : C.backward (firstProbe C e hcode) ∉ forbidden C.backward hcode) :
    (∀ z, phi (firstProbe C e hcode) z = phi e z) ∧
      C.backward (firstProbe C e hcode) ∉ forbidden C.backward hcode := by
  exact ⟨fun z => by rw [(probe_selection C).2.2.2.1, ite_eq_right h], h⟩

theorem collision_forces_bottom {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e hcode : ℕ)
    (hne : FiniteSequenceCoding.decode hcode ≠ [])
    (hsame : ∀ i ∈ FiniteSequenceCoding.decode hcode, ∀ z, phi i z = phi e z)
    (hhit : C.backward (firstProbe C e hcode) ∈ forbidden C.backward hcode) :
    (∀ z, phi e z = Part.none) ∧
      ∀ j ∈ forbidden C.backward hcode, ∀ z, ψ j z = Part.none := by
  by_cases hempty : FiniteSequenceCoding.decode hcode = []
  · exact (hne hempty).elim
  ·
    obtain ⟨i, hi, hbi⟩ := List.mem_map.mp hhit
    have he : ∀ z, phi e z = Part.none := by
      intro z
      calc
        phi e z = phi i z := (hsame i hi z).symm
        _ = ψ (C.backward i) z := (C.backward_eval i z).symm
        _ = ψ (C.backward (firstProbe C e hcode)) z := by rw [hbi]
        _ = phi (firstProbe C e hcode) z := C.backward_eval _ z
        _ = Part.none := by rw [(probe_selection C).2.2.2.1, ite_eq_left hhit]
    refine ⟨he, ?_⟩
    intro j hj z
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    exact (C.backward_eval i z).trans ((hsame i hi z).trans (he z))

theorem rescue_probe_escapes {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e hcode : ℕ)
    (hne : FiniteSequenceCoding.decode hcode ≠ [])
    (hsame : ∀ i ∈ FiniteSequenceCoding.decode hcode, ∀ z, phi i z = phi e z)
    (hhit : C.backward (firstProbe C e hcode) ∈ forbidden C.backward hcode) :
    C.backward (rescueProbe C hcode) ∉ forbidden C.backward hcode ∧
      ∀ z, phi (rescueProbe C hcode) z = phi e z := by
  have hbot := collision_forces_bottom C e hcode hne hsame hhit
  have hnot : C.backward (rescueProbe C hcode) ∉ forbidden C.backward hcode := by
    intro hm
    have hyes : phi (rescueProbe C hcode) 0 = Part.some 1 := by
      rw [(probe_selection C).2.2.2.2, ite_eq_left hm]
    have hno : phi (rescueProbe C hcode) 0 = Part.none :=
      (C.backward_eval _ 0).symm.trans (hbot.2 _ hm 0)
    have := hyes.symm.trans hno
    exact Part.some_ne_none _ this
  refine ⟨hnot, fun z => ?_⟩
  rw [(probe_selection C).2.2.2.2, ite_eq_right hnot, hbot.1 z]

def nextEquivalent {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e hcode : ℕ) : ℕ :=
  if C.backward (firstProbe C e hcode) ∈ forbidden C.backward hcode
  then rescueProbe C hcode else firstProbe C e hcode

theorem next_equivalent_computable {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    Computable₂ (nextEquivalent C) := by
  have ht : Computable (fun t : ℕ × ℕ =>
      decide (C.backward (firstProbe C t.1 t.2) ∈ forbidden C.backward t.2)) :=
    membership_computable.comp
      ((forbidden_computable C.backward C.backward_computable).comp Computable.snd)
      (C.backward_computable.comp (probe_selection C).2.1.to_comp)
  exact (Computable.cond ht
    ((probe_selection C).2.2.1.to_comp.comp Computable.snd)
    (probe_selection C).2.1.to_comp).of_eq (fun t => by simp [nextEquivalent])

theorem next_equivalent_spec {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (e hcode : ℕ)
    (hne : FiniteSequenceCoding.decode hcode ≠ [])
    (hsame : ∀ i ∈ FiniteSequenceCoding.decode hcode, ∀ z, phi i z = phi e z) :
    (∀ z, phi (nextEquivalent C e hcode) z = phi e z) ∧
      C.backward (nextEquivalent C e hcode) ∉ forbidden C.backward hcode := by
  by_cases hhit : C.backward (firstProbe C e hcode) ∈ forbidden C.backward hcode
  · rw [nextEquivalent, ite_eq_left hhit]
    have hr := rescue_probe_escapes C e hcode hne hsame hhit
    exact ⟨hr.2, hr.1⟩
  · rw [nextEquivalent, ite_eq_right hhit]
    exact first_probe_escapes C e hcode hhit

end
end Lemmatheca.ComputabilityTheory.Rogers
