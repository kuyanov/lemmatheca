import Lemmatheca.UniformSelfReference.Numberings
import Lemmatheca.UniformSelfReference.Halting

/-! Exact output selectors, repeated names, and the nonacceptable zero-input flag. -/
namespace Lemmatheca.ComputabilityTheory.UniformSelfReference.Examples

open UniversalComputation

theorem indexed_output_family :
    ∃ h : ℕ → ℕ, Primrec h ∧
      (∀ a x, phi (h a) x = Part.some (h a + a + x)) ∧ Function.Injective h := by
  have hg : Partrec (fun p : ℕ × (ℕ × ℕ) => Part.some (p.1 + p.2.1 + p.2.2)) :=
    (Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).partrec
  obtain ⟨h, hh, he⟩ := parameterized_partial_recursion (g := fun e a x => Part.some (e + a + x)) hg
  refine ⟨h, hh, he, fun a b hab => ?_⟩
  have ha := he a 0
  have hb := he b 0
  rw [hab, hb] at ha
  have hv := Part.some_injective ha
  omega

theorem successor_selector :
    ∃ h : ℕ → ℕ, Primrec h ∧ IsUniformSelector (fun e _ => e + 1) h ∧
      ∀ a, h a ≠ h a + 1 := by
  have hF : Computable₂ (fun e _ : ℕ => e + 1) :=
    Computable.succ.comp Computable.fst
  obtain ⟨r, _, hh, _, he⟩ := parameterized_recursion hF
  exact ⟨selector (RecursionTheorem.selfSpecialize r), hh, he, fun a => by omega⟩

def repeated (n x : ℕ) : Part ℕ := phi n.unpair.2 x

def repeatedCompilers : Compilers repeated where
  forward := fun n => n.unpair.2
  backward := Nat.pair 0
  forward_computable := (Primrec.snd.comp Primrec.unpair).to_comp
  backward_computable := (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id).to_comp
  forward_eval := fun _ _ => rfl
  backward_eval := fun e x => by simp only [repeated, Nat.unpair_pair]

theorem repeated_compiler_facts :
    Primrec repeatedCompilers.forward ∧ Primrec repeatedCompilers.backward ∧
      Acceptable repeated ∧
      (∀ e, repeatedCompilers.forward (repeatedCompilers.backward e) = e) ∧
      (∀ u v, repeatedCompilers.backward (repeatedCompilers.forward (Nat.pair u v)) = Nat.pair 0 v) ∧
      ∀ u v, u ≠ 0 →
        repeatedCompilers.backward (repeatedCompilers.forward (Nat.pair u v)) ≠ Nat.pair u v := by
  refine ⟨Primrec.snd.comp Primrec.unpair,
    Primrec₂.natPair.comp (Primrec.const 0) Primrec.id,
    ⟨compilers_numbering repeatedCompilers, ⟨repeatedCompilers⟩⟩, ?_, ?_, ?_⟩
  · intro e
    simp [repeatedCompilers]
  · intro u v
    simp [repeatedCompilers]
  · intro u v hu he
    have hh := congrArg (fun n => n.unpair.1) he
    apply hu
    simpa only [repeatedCompilers, Nat.unpair_pair] using hh.symm

def flagged (n x : ℕ) : Part ℕ :=
  if x = 0 then
    if n.unpair.1 = 0 then Part.none else Part.some (n.unpair.1 - 1)
  else phi n.unpair.2 x

theorem flagged_recursive : Partrec₂ flagged := by
  have hx : Computable (fun p : ℕ × ℕ => decide (p.2 = 0)) :=
    Primrec.eq.decide.to_comp.comp Computable.snd (Computable.const 0)
  have hn : Computable (fun p : ℕ × ℕ => decide (p.1.unpair.1 = 0)) :=
    Primrec.eq.decide.to_comp.comp
      (Computable.fst.comp (Computable.unpair.comp Computable.fst)) (Computable.const 0)
  have hv : Computable (fun p : ℕ × ℕ => p.1.unpair.1 - 1) :=
    Primrec.nat_sub.to_comp.comp
      (Computable.fst.comp (Computable.unpair.comp Computable.fst)) (Computable.const 1)
  exact (Partrec.cond hx (Partrec.cond hn Partrec.none hv.partrec)
    (phi_recursive.comp (Computable.snd.comp (Computable.unpair.comp Computable.fst))
      Computable.snd)).of_eq (fun p => by simp [flagged])

theorem flagged_zero_domain (n : ℕ) : (flagged n 0).Dom ↔ 0 < n.unpair.1 := by
  simp only [flagged, ite_true]
  split_ifs with h
  · simp_all
  · simpa using Nat.pos_of_ne_zero h

theorem flagged_zero_decidable : ComputablePred (fun n => (flagged n 0).Dom) := by
  have hp : ComputablePred (fun n : ℕ => 0 < n.unpair.1) :=
    (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.fst.comp Primrec.unpair)).computablePred
  exact hp.of_eq fun n => (flagged_zero_domain n).symm

/-- The standard index and the actual zero-input choice determine the theta-index. -/
theorem flagged_represents {f : ℕ → Part ℕ} (v : ℕ) (hv : phi v = f) :
    (¬ (f 0).Dom → flagged (Nat.pair 0 v) = f) ∧
      ∀ y, y ∈ f 0 → flagged (Nat.pair (y + 1) v) = f := by
  constructor
  · intro hn
    funext x
    by_cases hx : x = 0
    · subst x
      simpa [flagged] using (Part.eq_none_iff'.mpr hn).symm
    · simpa [flagged, hx] using congrFun hv x
  · intro y hy
    funext x
    by_cases hx : x = 0
    · subst x
      simpa [flagged] using (Part.eq_some_iff.mpr hy).symm
    · simpa [flagged, hx] using congrFun hv x

theorem flagged_numbering : IsComputableNumbering flagged := by
  refine ⟨⟨fun n => ?_, fun f hf => ?_⟩, flagged_recursive⟩
  · exact Partrec.nat_iff.mp (flagged_recursive.comp (Computable.const n) Computable.id)
  · obtain ⟨v, hv⟩ := phi_complete hf
    by_cases h : (f 0).Dom
    · obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp h
      exact ⟨Nat.pair (y + 1) v, (flagged_represents v hv).2 y hy⟩
    · exact ⟨Nat.pair 0 v, (flagged_represents v hv).1 h⟩

theorem flagged_nonacceptability :
    (¬ ∃ b : ℕ → ℕ, Computable b ∧ ∀ e x, flagged (b e) x = phi e x) ∧
      ¬ Acceptable flagged := by
  classical
  have hn : ¬ ∃ b : ℕ → ℕ, Computable b ∧ ∀ e x, flagged (b e) x = phi e x := by
    rintro ⟨b, hb, he⟩
    have hd : ComputablePred (fun e => (flagged (b e) 0).Dom) :=
      Computable.computablePred (flagged_zero_decidable.decide.comp hb)
    apply RicesTheorem.haltsZero_facts.2.1
    exact hd.of_eq (fun e => by change (flagged (b e) 0).Dom ↔ (phi e 0).Dom; rw [he])
  refine ⟨hn, ?_⟩
  rintro ⟨_, ⟨C⟩⟩
  exact hn ⟨C.backward, C.backward_computable, C.backward_eval⟩

theorem flagged_zero_nontrivial :
    ¬ (flagged (Nat.pair 0 0) 0).Dom ∧ flagged (Nat.pair 1 0) 0 = Part.some 0 := by
  simp [flagged]

end Lemmatheca.ComputabilityTheory.UniformSelfReference.Examples
