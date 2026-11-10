import Lemmatheca.ArslanovCompletenessCriterion.Theorems
import Lemmatheca.EffectivelyClosedClassesAndDnc.Diagonal

namespace Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion

open UniversalComputation OracleComputation
open BusyBeaverFunctions (ordinaryProgram)

noncomputable section

-- The ordinary input is (i,(z,y)); the numerical parameter z is ignored.
def relationInput (w : ℕ) : Part ℕ :=
  (phi w.unpair.1 w.unpair.2.unpair.2).map (fun _ => 0)

theorem relation_input_partial : Nat.Partrec relationInput := by
  apply Partrec.nat_iff.mp
  exact (phi_recursive.comp (Computable.fst.comp Computable.unpair)
    (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair)))).map
      (Computable.const 0).to₂

def relationMaster : ℕ := Classical.choose (phi_complete relation_input_partial)

def relationIndex (i : ℕ) : ℕ := specialize relationMaster i

theorem relation_index_primitive : Primrec relationIndex := by
  exact specialize_primitive.comp (Primrec.const _) Primrec.id

theorem relation_index_eval (i z y : ℕ) :
    phi (relationIndex i) (Nat.pair z y) = (phi i y).map (fun _ => 0) := by
  rw [relationIndex, specialize_eval]
  have h := congrFun (Classical.choose_spec (phi_complete relation_input_partial))
    (Nat.pair i (Nat.pair z y))
  simpa only [relationMaster, relationInput, Nat.unpair_pair] using h

def pickIndex (i : ℕ) : ℕ := ArithmeticDefinability.selectorIndex (relationIndex i)

theorem pick_index_primitive : Primrec pickIndex := by
  exact ArithmeticDefinability.selector_index_primitive.comp relation_index_primitive

theorem pick_index_spec (i x : ℕ) :
    ((phi (pickIndex i) x).Dom ↔ ∃ y, y ∈ EffectiveEnumerations.indexSet i) ∧
      ∀ y, y ∈ phi (pickIndex i) x → y ∈ EffectiveEnumerations.indexSet i := by
  have hs := ArithmeticDefinability.selector_index_spec (relationIndex i) x
  have hm (y : ℕ) : (phi (relationIndex i) (Nat.pair x y)).Dom ↔
      y ∈ EffectiveEnumerations.indexSet i := by
    rw [relation_index_eval]
    rfl
  refine ⟨hs.1.trans (exists_congr hm), ?_⟩
  intro y hy
  exact (hm y).mp (hs.2 y hy)

theorem pick_singleton_diagonal (i v : ℕ)
    (hi : EffectiveEnumerations.indexSet i = {v}) :
    phi (pickIndex i) (pickIndex i) = Part.some v := by
  have hs := pick_index_spec i (pickIndex i)
  have hd : (phi (pickIndex i) (pickIndex i)).Dom := hs.1.mpr ⟨v, by rw [hi]; simp⟩
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
  have hv := hs.2 y hy
  rw [hi] at hv
  have hyv : y = v := Set.mem_singleton_iff.mp hv
  exact Part.eq_some_iff.mpr (hyv ▸ hy)

def dncFPF (g : ℕ → ℕ) (i : ℕ) : ℕ := singletonIndex (g (pickIndex i))

theorem dnc_fpf (g : ℕ → ℕ) (hg : EffectivelyClosedClassesAndDnc.DNC g) :
    FPF (dncFPF g) := by
  intro i heq
  have hs : EffectiveEnumerations.indexSet i = {g (pickIndex i)} :=
    heq.symm.trans (singleton_index_domain _)
  have hv := pick_singleton_diagonal i (g (pickIndex i)) hs
  have hm : g (pickIndex i) ∈ phi (pickIndex i) (pickIndex i) := by
    rw [hv]
    exact Part.mem_some _
  exact hg _ _ hm rfl

def dncFPFCode (c : Code) : Code :=
  .comp (embed (ordinaryProgram singletonIndex singleton_index_primitive.to_comp))
    (.comp c (embed (ordinaryProgram pickIndex pick_index_primitive.to_comp)))

theorem dnc_fpf_code_eval (B : Set ℕ) (g : ℕ → ℕ) (c : Code)
    (hc : ∀ n, eval B c n = Part.some (g n)) (i : ℕ) :
    eval B (dncFPFCode c) i = Part.some (dncFPF g i) := by
  simp only [dncFPFCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
    Part.bind_some, hc, dncFPF]

theorem computes_fpf_of_dnc (B : Set ℕ) (g : ℕ → ℕ)
    (hg : EffectivelyClosedClassesAndDnc.DNC g)
    (hc : PartialComputable B (fun n => Part.some (g n))) : ComputesFPF B := by
  obtain ⟨c, hc⟩ := hc
  refine ⟨dncFPF g, ⟨dncFPFCode c, ?_⟩, dnc_fpf g hg⟩
  funext i
  exact dnc_fpf_code_eval B g c (fun n => congrFun hc n) i

end
end Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion
