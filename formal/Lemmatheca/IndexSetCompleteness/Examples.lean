import Lemmatheca.IndexSetCompleteness.Classification

/-! The explicit infinite even-domain, constant-output example. -/
namespace Lemmatheca.Entry.IndexSetCompleteness

open Lemmatheca.ComputabilityTheory
open IndexSetCompleteness UniversalComputation

set_option backward.isDefEq.respectTransparency false

def evenMatrix : Matrix := fun _ y _ => decide (y % 2 = 0)

theorem evenMatrix_computable : MatrixComputable evenMatrix := by
  exact ((Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.fst)
    (Primrec.const 2)) (Primrec.const 0)).decide).to_comp

noncomputable def evenIndex : ℕ := totalMap evenMatrix evenMatrix_computable 0

theorem evenIndex_domain (n : ℕ) :
    n ∈ EffectiveEnumerations.indexSet evenIndex ↔ n % 2 = 0 := by
  change (phi (totalMap evenMatrix evenMatrix_computable 0) n).Dom ↔ _
  rw [totalMap_eval, totalSearch_domain]
  simp [evenMatrix]

theorem evenIndex_output (n y : ℕ) :
    y ∈ phi evenIndex n ↔ y = 0 ∧ n % 2 = 0 := by
  change y ∈ phi (totalMap evenMatrix evenMatrix_computable 0) n ↔ _
  rw [totalMap_eval]
  constructor
  · intro hy
    have hh := (totalSearch_least evenMatrix 0 n y).mp hy
    have hn : n % 2 = 0 := by simpa [evenMatrix] using hh.1
    have hy0 : y = 0 := by
      by_contra hne
      have hz := hh.2 0 (by omega)
      simp [evenMatrix,hn] at hz
    exact ⟨hy0,hn⟩
  · rintro ⟨rfl,hn⟩
    apply (totalSearch_least evenMatrix 0 n 0).mpr
    exact ⟨by simp [evenMatrix,hn],fun u hu => by omega⟩

theorem evenIndex_facts :
    evenIndex ∈ IndexSetCompleteness.Infinitude ∧
      evenIndex ∉ Lemmatheca.Entry.ArithmeticalHierarchy.Totality ∧
      evenIndex ∉ Lemmatheca.Entry.ArithmeticalHierarchy.Finiteness ∧
      {y | ∃ n, y ∈ phi evenIndex n} = {0} := by
  have hi : (EffectiveEnumerations.indexSet evenIndex).Infinite := by
    intro hf
    obtain ⟨a,ha⟩ := hf.bddAbove
    have hm : 2*(a+1) ∈ EffectiveEnumerations.indexSet evenIndex :=
      (evenIndex_domain _).mpr (by omega)
    have hb := ha hm
    omega
  have ht : evenIndex ∉ Lemmatheca.Entry.ArithmeticalHierarchy.Totality := by
    intro h
    have h1 : 1 ∈ EffectiveEnumerations.indexSet evenIndex := h 1
    have he := (evenIndex_domain 1).mp h1
    norm_num at he
  refine ⟨hi,ht,hi,?_⟩
  ext y
  constructor
  · rintro ⟨n,hn⟩
    exact (evenIndex_output n y).mp hn |>.1
  · intro hy
    have hy0 : y = 0 := hy
    subst y
    exact ⟨0,(evenIndex_output 0 0).mpr ⟨rfl,rfl⟩⟩

theorem totality_ne_infinitude :
    Lemmatheca.Entry.ArithmeticalHierarchy.Totality ≠ IndexSetCompleteness.Infinitude := by
  intro h
  exact evenIndex_facts.2.1 (h.symm ▸ evenIndex_facts.1)

end Lemmatheca.Entry.IndexSetCompleteness
