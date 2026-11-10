import Lemmatheca.ArithmeticDefinability.ArithmeticDefinability

/-! Effective selection by the first certified pair, with its actual uniform compiler. -/
namespace Lemmatheca.ComputabilityTheory.ArithmeticDefinability

open UniversalComputation

noncomputable section

def certificateSelection (P : ℕ → ℕ → ℕ → Prop) (x : ℕ) : Part ℕ := by
  classical
  exact (Nat.rfind fun w => Part.some (decide (P x w.unpair.1 w.unpair.2))).map
    (fun w => w.unpair.1)

theorem certificateSelection_partial (P : ℕ → ℕ → ℕ → Prop)
    (hP : PrimrecPred (fun p : ℕ × ℕ => P p.1 p.2.unpair.1 p.2.unpair.2)) :
    Nat.Partrec (certificateSelection P) := by
  classical
  have hs : Partrec (fun x => Nat.rfind fun w =>
      Part.some (decide (P x w.unpair.1 w.unpair.2))) :=
    Partrec.rfind (show Computable₂ (fun (x w : ℕ) => decide (P x w.unpair.1 w.unpair.2)) from hP.decide.to_comp).partrec₂
  exact Partrec.nat_iff.mp (hs.map
    (Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp Computable.snd)).to₂)

theorem certificateSelection_spec (P : ℕ → ℕ → ℕ → Prop) (x : ℕ) :
    ((certificateSelection P x).Dom ↔ ∃ y t, P x y t) ∧
      (∀ y, y ∈ certificateSelection P x → ∃ t, P x y t) := by
  classical
  have hd : (certificateSelection P x).Dom ↔ ∃ y t, P x y t := by
    simp only [certificateSelection, Part.map_Dom]
    constructor
    · intro h
      obtain ⟨w, hw, _⟩ := Nat.rfind_dom.mp h
      exact ⟨w.unpair.1, w.unpair.2, by simpa using hw⟩
    · rintro ⟨y, t, ht⟩
      apply Nat.rfind_dom.mpr
      exact ⟨Nat.pair y t, by simpa using ht, fun _ => trivial⟩
  refine ⟨hd, ?_⟩
  intro y hy
  obtain ⟨w, hw, he⟩ := (Part.mem_map_iff _).mp hy
  have hp : P x w.unpair.1 w.unpair.2 := by simpa using Nat.rfind_spec hw
  exact ⟨w.unpair.2, he ▸ hp⟩

/-- Selection is a single-valued enumerable subrelation with exactly the same projection. -/
theorem effective_selection (R : ℕ → ℕ → Prop)
    (hR : REPred (fun p : ℕ × ℕ => R p.1 p.2)) :
    ∃ f : ℕ → Part ℕ, Nat.Partrec f ∧ REPred (Graph f) ∧
      (∀ x, (f x).Dom ↔ ∃ y, R x y) ∧
      (∀ x y, y ∈ f x → R x y) ∧
      ((∀ x, ∃ y, R x y) → ∃ g : ℕ → ℕ, Computable g ∧
        ∀ x, f x = Part.some (g x)) := by
  classical
  have hN : REPred (fun n : ℕ => R n.unpair.1 n.unpair.2) :=
    hR.comp Primrec.unpair.to_comp
  obtain ⟨C, hC, hc⟩ := (enumerable_iff_primitive_certificate _).mp hN
  let P : ℕ → ℕ → ℕ → Prop := fun x y t => C (Nat.pair x y) t
  have hP : PrimrecPred (fun p : ℕ × ℕ => P p.1 p.2.unpair.1 p.2.unpair.2) :=
    hC.comp ((Primrec₂.natPair.comp Primrec.fst
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).pair
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  let f := certificateSelection P
  have hf : Nat.Partrec f := certificateSelection_partial P hP
  have he (x y : ℕ) : R x y ↔ ∃ t, P x y t := by
    simpa [P] using hc (Nat.pair x y)
  have hd (x : ℕ) : (f x).Dom ↔ ∃ y, R x y := by
    rw [(certificateSelection_spec P x).1]
    exact exists_congr (fun y => (he x y).symm)
  refine ⟨f, hf, (partial_recursive_iff_graph_enumerable f).mp hf, hd, ?_, ?_⟩
  · intro x y hy
    exact (he x y).mpr ((certificateSelection_spec P x).2 y hy)
  · intro ht
    let g : ℕ → ℕ := fun x => (f x).get ((hd x).mpr (ht x))
    have hm (x : ℕ) : g x ∈ f x := Part.get_mem _
    refine ⟨g, (Partrec.nat_iff.mpr hf).of_eq_tot hm, ?_⟩
    intro x
    exact Part.eq_some_iff.mpr (hm x)

/-- The one joint procedure searches bounded halting certificates for a relation index. -/
def indexedSelection (e x : ℕ) : Part ℕ :=
  certificateSelection (fun x y t => certificate e (Nat.pair x y) t) x

theorem indexedSelection_joint_partial :
    Nat.Partrec (fun n => indexedSelection n.unpair.1 n.unpair.2) := by
  classical
  have hP : PrimrecPred (fun p : ℕ × ℕ =>
      certificate p.1.unpair.1 (Nat.pair p.1.unpair.2 p.2.unpair.1) p.2.unpair.2) :=
    certificate_primitive.comp
      (((Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)).pair
        (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))).pair
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hc : Computable₂ (fun (n w : ℕ) => decide
      (certificate n.unpair.1 (Nat.pair n.unpair.2 w.unpair.1) w.unpair.2)) := hP.decide.to_comp
  have hs := Partrec.rfind hc.partrec₂
  exact Partrec.nat_iff.mp (hs.map
    (Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp Computable.snd)).to₂)

def selectorMaster : ℕ := (phi_complete indexedSelection_joint_partial).choose

def selectorIndex (e : ℕ) : ℕ := specialize selectorMaster e

theorem selector_master_eval (e x : ℕ) :
    phi selectorMaster (Nat.pair e x) = indexedSelection e x := by
  simpa [selectorMaster] using congrFun
    (Exists.choose_spec (phi_complete indexedSelection_joint_partial)) (Nat.pair e x)

theorem selector_index_primitive : Primrec selectorIndex := by
  exact specialize_primitive.comp (Primrec.const selectorMaster) Primrec.id

theorem selector_index_eval (e x : ℕ) :
    phi (selectorIndex e) x = indexedSelection e x := by
  rw [selectorIndex, specialize_eval, selector_master_eval]

theorem selector_index_spec (e x : ℕ) :
    ((phi (selectorIndex e) x).Dom ↔ ∃ y, (phi e (Nat.pair x y)).Dom) ∧
      (∀ y, y ∈ phi (selectorIndex e) x → (phi e (Nat.pair x y)).Dom) := by
  rw [selector_index_eval]
  have hs := certificateSelection_spec (fun x y t => certificate e (Nat.pair x y) t) x
  constructor
  · exact hs.1.trans (exists_congr fun y => (phi_domain e (Nat.pair x y)).symm)
  · intro y hy
    exact (phi_domain e (Nat.pair x y)).mpr (hs.2 y hy)

end
end Lemmatheca.ComputabilityTheory.ArithmeticDefinability
