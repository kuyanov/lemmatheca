import Lemmatheca.HighDegreesAndDomination.Definitions

/-! A single ordinary search and the finite successful allowances of total indices. -/
namespace Lemmatheca.ComputabilityTheory.HighDegreesAndDomination

open UniversalComputation

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false
local notation "TOT" => Lemmatheca.Entry.ArithmeticalHierarchy.Totality

def deadlineTest (w : ℕ) : Bool :=
  decide (∀ x ≤ w.unpair.1.unpair.2,
    0 < boundedValue w.unpair.2 w.unpair.1.unpair.1 x)

theorem deadline_test_computable : Computable deadlineTest := by
  have hu := Primrec.unpair.comp (Primrec.snd : Primrec (@Prod.snd ℕ ℕ))
  have hv := Primrec.unpair.comp (Primrec.fst.comp hu)
  have hb := boundedValue_primitive.comp
    (((Primrec.snd.comp hu).pair (Primrec.fst.comp hv)).pair Primrec.fst)
  have hr : PrimrecRel (fun x w : ℕ => 0 < boundedValue w.unpair.2 w.unpair.1.unpair.1 x) :=
    (Primrec.nat_lt.comp (Primrec.const 0) hb).primrecRel
  have hbound := Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
  have hp : PrimrecPred (fun w : ℕ => ∀ x ≤ w.unpair.1.unpair.2,
      0 < boundedValue w.unpair.2 w.unpair.1.unpair.1 x) :=
    (hr.forall_lt.comp hbound Primrec.id).of_eq
      (fun w => by simp only [Nat.lt_succ_iff, id_eq])
  exact hp.decide.to_comp

def deadlineSearch (w : ℕ) : Part ℕ :=
  Nat.rfind (fun k => Part.some (deadlineTest (Nat.pair w k)))

theorem deadline_search_partial : Partrec deadlineSearch := by
  exact Partrec.rfind
    (deadline_test_computable.comp Primrec₂.natPair.to_comp).to₂.partrec₂

def deadlineCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp deadline_search_partial)

def deadlineCompiler (e : ℕ) : ℕ :=
  specialize (Encodable.encode deadlineCode) e

theorem deadline_compiler_primitive : Primrec deadlineCompiler := by
  exact specialize_primitive.comp (Primrec.const _) Primrec.id

theorem deadline_compiler_eval (e n : ℕ) :
    phi (deadlineCompiler e) n = deadlineSearch (Nat.pair e n) := by
  rw [deadlineCompiler, specialize_eval]
  have h := congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp deadline_search_partial))
    (Nat.pair e n)
  simpa [phi, deadlineCode, Part.map_id' Encodable.encode_nat] using h

private theorem success_later {k l e x : ℕ} (hkl : k ≤ l)
    (hk : 0 < boundedValue k e x) : 0 < boundedValue l e x := by
  have hv : boundedValue k e x = (boundedValue k e x - 1) + 1 := by omega
  have hm := Nat.Partrec.Code.evaln_mono hkl ((boundedValue_output k e x _).mp hv)
  have hl := (boundedValue_output l e x _).mpr hm
  omega

theorem deadline_exists (e : ℕ) (he : e ∈ TOT) (n : ℕ) :
    ∃ k, ∀ x ≤ n, 0 < boundedValue k e x := by
  have hw (x : ℕ) : ∃ k, 0 < boundedValue k e x := by
    simpa only [certificate] using (phi_domain e x).mp (he x)
  choose h hh using hw
  refine ⟨(Finset.range (n + 1)).sup h, ?_⟩
  intro x hx
  exact success_later (Finset.le_sup (f := h) (Finset.mem_range.mpr (by omega))) (hh x)

def deadline (e : ℕ) (he : e ∈ TOT) (n : ℕ) : ℕ :=
  Nat.find (deadline_exists e he n)

theorem deadline_spec (e : ℕ) (he : e ∈ TOT) (n : ℕ) :
    (∀ x ≤ n, 0 < boundedValue (deadline e he n) e x) ∧
      (∀ k < deadline e he n, ∃ x ≤ n, boundedValue k e x = 0) ∧
      ∀ k, deadline e he n ≤ k → ∀ x ≤ n, 0 < boundedValue k e x := by
  have hs := Nat.find_spec (deadline_exists e he n)
  refine ⟨hs, ?_, ?_⟩
  · intro k hk
    have hn := Nat.find_min (deadline_exists e he n) hk
    push Not at hn
    obtain ⟨x, hx, hfail⟩ := hn
    exact ⟨x, hx, by omega⟩
  · intro k hk x hx
    exact success_later hk (hs x hx)

theorem deadline_search_value (e : ℕ) (he : e ∈ TOT) (n : ℕ) :
    deadlineSearch (Nat.pair e n) = Part.some (deadline e he n) := by
  apply Part.eq_some_iff.mpr
  rw [deadlineSearch, Nat.mem_rfind]
  refine ⟨?_, ?_⟩
  · simpa [deadlineTest, Nat.unpair_pair] using (deadline_spec e he n).1
  · intro k hk
    obtain ⟨x, hx, hzero⟩ := (deadline_spec e he n).2.1 k hk
    have hn : ¬ ∀ x ≤ n, 0 < boundedValue k e x := fun h => (Nat.ne_of_gt (h x hx)) hzero
    simp [deadlineTest, Nat.unpair_pair, hn]

theorem deadline_computable (e : ℕ) (he : e ∈ TOT) : Computable (deadline e he) := by
  exact (deadline_search_partial.comp ((Computable.const e).pair Computable.id)).of_eq_tot
    (fun n => by rw [deadline_search_value e he n]; exact Part.mem_some _)

end
end Lemmatheca.ComputabilityTheory.HighDegreesAndDomination
