import Lemmatheca.RiceShapiroTheorem.Basis

/-! Explicit positive-output bases, nonextraction and negative-information obstructions. -/
namespace Lemmatheca.ComputabilityTheory.RiceShapiroTheorem

open UniversalComputation

noncomputable section
open Classical

/-- The waiting family's fixed second stage has graph {(0,0)}. -/
def zeroAtZero : RicesTheorem.PartialFunction := tableFunction [(0, 0)]

theorem zeroAtZero_partial : Nat.Partrec zeroAtZero := by
  have hp : Partrec zeroAtZero :=
    (fragment_partial.comp (Computable.const (pairListCode [(0, 0)])) Computable.id).of_eq
      (fun _ => by simp only [fragment, pairList_code, zeroAtZero, id_eq])
  exact Partrec.nat_iff.mp hp

def finiteWaitingIndex (e : ℕ) : ℕ := RicesTheorem.waitingMap zeroAtZero zeroAtZero_partial e

theorem finiteWaitingIndex_spec :
    Primrec finiteWaitingIndex ∧ ∀ e,
      FiniteGraph (phi (finiteWaitingIndex e)) ∧
      ((phi e e).Dom → phi (finiteWaitingIndex e) = zeroAtZero) ∧
      (¬ (phi e e).Dom → phi (finiteWaitingIndex e) = RicesTheorem.bottom) ∧
      ((0, 0) ∈ graph (phi (finiteWaitingIndex e)) ↔ e ∈ haltingDiagonal) := by
  have hz : FiniteGraph zeroAtZero := by
    simpa only [fragment, pairList_code, zeroAtZero] using fragment_finite (pairListCode [(0, 0)])
  have hb : FiniteGraph RicesTheorem.bottom := by
    simpa only [empty_fragment.2] using fragment_finite (pairListCode [])
  refine ⟨RicesTheorem.waitingMap_primitive zeroAtZero zeroAtZero_partial, ?_⟩
  intro e
  have hc := RicesTheorem.waitingMap_cases zeroAtZero zeroAtZero_partial e
  change ((phi e e).Dom → phi (finiteWaitingIndex e) = zeroAtZero) ∧
    (¬ (phi e e).Dom → phi (finiteWaitingIndex e) = RicesTheorem.bottom) at hc
  have hf : FiniteGraph (phi (finiteWaitingIndex e)) := by
    by_cases he : (phi e e).Dom
    · rw [hc.1 he]; exact hz
    · rw [hc.2 he]; exact hb
  refine ⟨hf, hc.1, hc.2, ?_⟩
  by_cases he : (phi e e).Dom
  · rw [hc.1 he]
    simp [graph, zeroAtZero, tableFunction, haltingDiagonal, he]
  · rw [hc.2 he]
    simp [graph, RicesTheorem.bottom, haltingDiagonal, he]

/-- The extracting procedure is partial outside the finite-function promise. -/
def IsFiniteGraphExtractor (F : ℕ → Part ℕ) : Prop :=
  Partrec F ∧ ∀ e, FiniteGraph (phi e) →
    ∃ d, d ∈ F e ∧ Valid d ∧ fragment d = phi e

theorem no_finite_graph_extractor : ¬ ∃ F, IsFiniteGraphExtractor F := by
  rintro ⟨F, hF⟩
  have hout (e : ℕ) := hF.2 (finiteWaitingIndex e) ((finiteWaitingIndex_spec.2 e).1)
  let g : ℕ → ℕ := fun e => Classical.choose (hout e)
  have hg (e : ℕ) : g e ∈ F (finiteWaitingIndex e) ∧
      Valid (g e) ∧ fragment (g e) = phi (finiteWaitingIndex e) := Classical.choose_spec (hout e)
  have hc : Computable g :=
    (hF.1.comp finiteWaitingIndex_spec.1.to_comp).of_eq_tot (fun e => (hg e).1)
  have hp : Primrec pairList := Primrec.list_map (Primrec.ofNat (List ℕ))
    (Primrec.unpair.comp Primrec.snd).to₂
  have heq : PrimrecPred (fun q : ℕ × ℕ => q = (0, 0)) :=
    Primrec.eq.comp Primrec.id (Primrec.const (0, 0))
  have hm : PrimrecPred (fun d => (0, 0) ∈ pairList d) :=
    (heq.exists_mem_list.comp hp).of_eq (fun _ => by simp)
  have hd : ComputablePred (fun e => (0, 0) ∈ pairList (g e)) :=
    Computable.computablePred (hm.decide.to_comp.comp hc)
  apply haltingDiagonal_undecidable
  apply hd.of_eq
  intro e
  rw [← tableFunction_mem (pairList (g e)) (hg e).2.1 0 0]
  change 0 ∈ fragment (g e) 0 ↔ e ∈ haltingDiagonal
  rw [(hg e).2.2]
  exact (finiteWaitingIndex_spec.2 e).2.2.2

def haltsZeroBasis : Set ℕ :=
  {d | ∃ y, d = pairListCode [(0, y)]}

def everOutputsBasis (m : ℕ) : Set ℕ :=
  {d | ∃ x, d = pairListCode [(x, m)]}

private theorem singleton_code_primitive :
    Primrec₂ (fun x y : ℕ => pairListCode [(x, y)]) := by
  change Primrec (fun p : ℕ × ℕ => FiniteSequenceCoding.code [Nat.pair p.1 p.2])
  exact Primrec.encode.comp (Primrec.list_cons.comp Primrec₂.natPair (Primrec.const []))

private theorem singleton_inclusion_iff (e x y : ℕ) :
    GraphInclusion (fragment (pairListCode [(x, y)])) (phi e) ↔ y ∈ phi e x := by
  have hc : Consistent [(x, y)] := by simp [Consistent]
  constructor
  · intro h
    apply h x y
    change y ∈ tableFunction (pairList (pairListCode [(x, y)])) x
    rw [pairList_code]
    exact (tableFunction_mem _ hc x y).mpr (by simp)
  · intro hy z v hv
    have hp : (z, v) ∈ [(x, y)] := (tableFunction_mem _ hc z v).mp
      (by simpa only [fragment, pairList_code] using hv)
    have heq := List.mem_singleton.mp hp
    have hz : z = x := congrArg Prod.fst heq
    have hv' : v = y := congrArg Prod.snd heq
    simpa only [hz, hv'] using hy

theorem haltsZero_basis : IsEffectiveBasis RicesTheorem.haltsZero haltsZeroBasis := by
  refine ⟨?_, ?_, ?_⟩
  · apply (enumerable_iff_primitive_certificate _).mpr
    refine ⟨fun d y => d = pairListCode [(0, y)], ?_, fun _ => Iff.rfl⟩
    exact Primrec.eq.comp Primrec.fst
      (singleton_code_primitive.comp (Primrec.const 0) Primrec.snd)
  · rintro d ⟨y, rfl⟩
    simp [Valid, pairList_code, Consistent]
  · intro e
    constructor
    · intro he
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp he
      exact ⟨pairListCode [(0, y)], ⟨y, rfl⟩, (singleton_inclusion_iff e 0 y).mpr hy⟩
    · rintro ⟨d, ⟨y, rfl⟩, hd⟩
      exact Part.dom_iff_mem.mpr ⟨y, (singleton_inclusion_iff e 0 y).mp hd⟩

theorem everOutputs_basis (m : ℕ) :
    IsEffectiveBasis (RicesTheorem.everOutputs m) (everOutputsBasis m) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (enumerable_iff_primitive_certificate _).mpr
    refine ⟨fun d x => d = pairListCode [(x, m)], ?_, fun _ => Iff.rfl⟩
    exact Primrec.eq.comp Primrec.fst
      (singleton_code_primitive.comp Primrec.snd (Primrec.const m))
  · rintro d ⟨x, rfl⟩
    simp [Valid, pairList_code, Consistent]
  · intro e
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨pairListCode [(x, m)], ⟨x, rfl⟩, (singleton_inclusion_iff e x m).mpr hx⟩
    · rintro ⟨d, ⟨x, rfl⟩, hd⟩
      exact ⟨x, (singleton_inclusion_iff e x m).mp hd⟩

def fragmentExtensionSet (d : ℕ) : Set ℕ :=
  {e | GraphInclusion (fragment d) (phi e)}

theorem fixed_fragment_basis (d : ℕ) (hd : Valid d) :
    IsEffectiveBasis (fragmentExtensionSet d) {d} := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Primrec.eq.comp Primrec.id (Primrec.const d)).computablePred.to_re
  · intro c hc
    simpa only [Set.mem_singleton_iff.mp hc] using hd
  · intro e
    simp [fragmentExtensionSet]

def exactSingletonDomain : Set ℕ :=
  {e | ∃ x, ∀ z, (phi e z).Dom ↔ z = x}

theorem singleton_domain_extension :
    Valid (pairListCode [(0, 0)]) ∧ Valid (pairListCode [(0, 0), (1, 0)]) ∧
    fragmentIndex (pairListCode [(0, 0)]) ∈ exactSingletonDomain ∧
    fragmentIndex (pairListCode [(0, 0), (1, 0)]) ∉ exactSingletonDomain ∧
    (∀ x, (phi (fragmentIndex (pairListCode [(0, 0)])) x).Dom ↔ x = 0) ∧
    (∀ x, (phi (fragmentIndex (pairListCode [(0, 0), (1, 0)])) x).Dom ↔ x = 0 ∨ x = 1) ∧
    GraphInclusion (phi (fragmentIndex (pairListCode [(0, 0)])))
      (phi (fragmentIndex (pairListCode [(0, 0), (1, 0)]))) := by
  have h₁ : Valid (pairListCode [(0, 0)]) := by simp [Valid, pairList_code, Consistent]
  have h₂ : Valid (pairListCode [(0, 0), (1, 0)]) := by simp [Valid, pairList_code, Consistent]
  have hs : ∀ x, (phi (fragmentIndex (pairListCode [(0, 0)])) x).Dom ↔ x = 0 := by
    intro x
    simp only [fragmentIndex_eval, fragment, pairList_code, Part.dom_iff_mem]
    simp_rw [tableFunction_mem [(0, 0)] (by simp [Consistent])]
    simp
  have ht : ∀ x, (phi (fragmentIndex (pairListCode [(0, 0), (1, 0)])) x).Dom ↔ x = 0 ∨ x = 1 := by
    intro x
    simp only [fragmentIndex_eval, fragment, pairList_code, Part.dom_iff_mem]
    simp_rw [tableFunction_mem [(0, 0), (1, 0)] (by simp [Consistent])]
    simp [exists_or]
  refine ⟨h₁, h₂, ⟨0, hs⟩, ?_, hs, ht, ?_⟩
  · rintro ⟨x, hx⟩
    have he0 := (hx 0).mp ((ht 0).mpr (by simp))
    have he1 := (hx 1).mp ((ht 1).mpr (by simp))
    omega
  · intro x y hy
    rw [fragmentIndex_eval] at hy ⊢
    have hm : (x, y) ∈ [(0, 0)] :=
      (tableFunction_mem _ (by simp [Consistent]) x y).mp
        (by simpa only [fragment, pairList_code] using hy)
    have hp := List.mem_singleton.mp hm
    have hx : x = 0 := congrArg Prod.fst hp
    have hyv : y = 0 := congrArg Prod.snd hp
    simp [fragment, pairList_code, tableFunction, hx, hyv]

theorem totality_no_finite_subfunction :
    RicesTheorem.Extensional RicesTheorem.totality ∧
    (∃ e, phi e = (fun _ => Part.some 0) ∧ e ∈ RicesTheorem.totality) ∧
    (∀ e d, e ∈ RicesTheorem.totality → GraphInclusion (phi e) (phi d) →
      d ∈ RicesTheorem.totality) ∧
    (∀ f : RicesTheorem.PartialFunction, FiniteGraph f → ¬ ∀ x, (f x).Dom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e d heq
    change (∀ x, (phi e x).Dom) ↔ ∀ x, (phi d x).Dom
    rw [heq]
  · obtain ⟨e, he⟩ := phi_complete (f := fun _ => Part.some 0) Nat.Partrec.zero
    exact ⟨e, he, by simp [RicesTheorem.totality, he]⟩
  · intro e d he h x
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp (he x)
    exact Part.dom_iff_mem.mpr ⟨y, h x y hy⟩
  · intro f hf ht
    have himage : Prod.fst '' graph f = Set.univ := by
      ext x
      constructor
      · intro _; exact Set.mem_univ _
      · intro _
        obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp (ht x)
        exact ⟨(x, y), hy, rfl⟩
    have hfinite : (Set.univ : Set ℕ).Finite := by
      rw [← himage]
      exact hf.image Prod.fst
    exact Set.infinite_univ hfinite

theorem singleton_domain_not_enumerable :
    RicesTheorem.Extensional exactSingletonDomain ∧
      ¬ REPred (fun e => e ∈ exactSingletonDomain) := by
  have hext : RicesTheorem.Extensional exactSingletonDomain := by
    intro e d heq
    change (∃ x, ∀ z, (phi e z).Dom ↔ z = x) ↔ ∃ x, ∀ z, (phi d z).Dom ↔ z = x
    rw [heq]
  refine ⟨hext, ?_⟩
  intro hRE
  obtain ⟨r, hr⟩ := (enumerable_iff_index (fun e => e ∈ exactSingletonDomain)).mp hRE
  have hAr : exactSingletonDomain = W r := Set.ext hr
  have hextW : RicesTheorem.Extensional (W r) := hAr ▸ hext
  obtain ⟨_, _, he, hd, _, _, hgraph⟩ := singleton_domain_extension
  rw [hAr] at he hd
  exact hd (upward_closure r _ _ hextW he hgraph)

end
end Lemmatheca.ComputabilityTheory.RiceShapiroTheorem
