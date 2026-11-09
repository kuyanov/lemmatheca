import Lemmatheca.PaDegrees.Basic
import Lemmatheca.ComputableTreesAndPaths.HaltingPath
import Lemmatheca.EffectiveInseparability.Race

set_option autoImplicit false

namespace Lemmatheca.ComputabilityTheory.PaDegrees

open UniversalComputation TuringDegrees OracleComputation EffectivelyClosedClassesAndDnc
open ComputableSeparation ComputableTreesAndPaths IncomparableTuringDegrees
open EffectiveEnumerations EffectiveInseparability BusyBeaverFunctions

noncomputable section
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def TreeDeciderIndex (t : ℕ) (T : Set ℕ) : Prop :=
  ∀ u, phi t u = Part.some (indicator (fun v => v ∈ T) u)

/-- Test a finite level using the supplied actual ordinary program, without an oracle. -/
def indexedEmpty (t u m : ℕ) : Part Bool :=
  ((binaryLevel (wordLength u + m)).mapM (fun v => phi t v)).map fun values =>
    ((binaryLevel (wordLength u + m)).zip values).all
      (fun vb => !decide (Prefix u vb.1) || decide (vb.2 = 0))

def indexedTreeRace (t u : ℕ) : Part ℕ :=
  if ValidCode u then do
    let m ← Nat.rfind fun m => do
      let left ← indexedEmpty t (appendBit u 0) m
      let right ← indexedEmpty t (appendBit u 1) m
      pure (left || right)
    let left ← indexedEmpty t (appendBit u 0) m
    pure (if left then 0 else 1)
  else Part.none

def treeRace (T : Set ℕ) (u : ℕ) : Part ℕ :=
  if ValidCode u then
    negativeRace (fun u m => EmptyExtension T (appendBit u 0) m)
      (fun u m => EmptyExtension T (appendBit u 1) m) u
  else Part.none

def leftDead (T : Set ℕ) : Set ℕ := {u | 0 ∈ treeRace T u}
def rightDead (T : Set ℕ) : Set ℕ := {u | 1 ∈ treeRace T u}

private def phiListAux (t : ℕ) (L : List ℕ) : ℕ → Part (List ℕ)
  | 0 => Part.some []
  | n + 1 => (phiListAux t L n).bind fun ys =>
      (phi t (L[n]?.getD 0)).map fun y => ys ++ [y]

set_option backward.isDefEq.respectTransparency false in
private theorem phi_list_aux_partial :
    Partrec (fun p : (ℕ × List ℕ) × ℕ => phiListAux p.1.1 p.1.2 p.2) := by
  have hf : Computable (fun p : (ℕ × List ℕ) × ℕ => p.2) := Computable.snd
  have hg : Partrec (fun _ : (ℕ × List ℕ) × ℕ => Part.some ([] : List ℕ)) := Computable.const []
  have hget : Computable (fun p : ((ℕ × List ℕ) × ℕ) × (ℕ × List ℕ) =>
      p.1.1.2[p.2.1]?.getD 0) :=
    (Primrec.list_getD 0).to_comp.comp
      (Computable.snd.comp (Computable.fst.comp Computable.fst))
      (Computable.fst.comp Computable.snd)
  have hphi : Partrec (fun p : ((ℕ × List ℕ) × ℕ) × (ℕ × List ℕ) =>
      phi p.1.1.1 (p.1.1.2[p.2.1]?.getD 0)) :=
    phi_recursive.comp
      (Computable.fst.comp (Computable.fst.comp Computable.fst)) hget
  have happ : Computable₂ (fun (p : ((ℕ × List ℕ) × ℕ) × (ℕ × List ℕ)) (y : ℕ) =>
      p.2.2 ++ [y]) := by
    exact (Primrec.list_append.to_comp.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst))
      (Primrec.list_cons.to_comp.comp Computable.snd (Computable.const []))).to₂
  have hh : Partrec₂ (fun (p : (ℕ × List ℕ) × ℕ) (q : ℕ × List ℕ) =>
      (phi p.1.1 (p.1.2[q.1]?.getD 0)).map fun y => q.2 ++ [y]) :=
    (hphi.map happ).to₂
  have hr := Partrec.nat_rec hf hg hh
  apply hr.of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => simp only [phiListAux]; rw [ih]


set_option backward.isDefEq.respectTransparency false in
private theorem phi_list_aux_take (t : ℕ) (L : List ℕ) (n : ℕ) (hn : n ≤ L.length) :
    phiListAux t L n = (L.take n).mapM (phi t) := by
  induction n with
  | zero => simp [phiListAux]
  | succ n ih =>
    have hlt : n < L.length := by omega
    rw [phiListAux, ih (by omega), List.take_succ_eq_append_getElem hlt, List.mapM_append]
    simp [List.getElem?_eq_getElem hlt, Part.bind_some_eq_map, Part.map_map, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
theorem phi_list_partial :
    Partrec (fun p : ℕ × List ℕ => p.2.mapM (phi p.1)) := by
  have hc : Computable (fun p : ℕ × List ℕ => (p, p.2.length)) :=
    Computable.id.pair (Primrec.list_length.to_comp.comp Computable.snd)
  apply (phi_list_aux_partial.comp hc).of_eq
  intro p
  simp only [phi_list_aux_take p.1 p.2 p.2.length le_rfl, List.take_length]


set_option backward.isDefEq.respectTransparency false in
theorem phi_list_comp {α : Type*} [Primcodable α]
    (t : α → ℕ) (L : α → List ℕ) (ht : Computable t) (hL : Computable L) :
    Partrec (fun x => (L x).mapM (phi (t x))) :=
  Partrec.comp (f := fun p : ℕ × List ℕ => p.2.mapM (phi p.1))
    (g := fun x => (t x, L x)) phi_list_partial (ht.pair hL)

attribute [local irreducible] binaryLevel

theorem indexed_empty_partial :
    Partrec (fun z : ℕ × (ℕ × ℕ) => indexedEmpty z.1 z.2.1 z.2.2) := by
  have hu : Primrec (fun z : ℕ × (ℕ × ℕ) => z.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun z : ℕ × (ℕ × ℕ) => z.2.2) := Primrec.snd.comp Primrec.snd
  have hnodes : Primrec (fun z : ℕ × (ℕ × ℕ) => binaryLevel (wordLength z.2.1 + z.2.2)) :=
    binary_level_primitive.comp (Primrec.nat_add.comp
      (FiniteSequenceCoding.primrec_length.comp hu) hm)
  have hi : Computable (fun z : ℕ × (ℕ × ℕ) =>
      (z.1, binaryLevel (wordLength z.2.1 + z.2.2))) := Computable.fst.pair hnodes.to_comp
  have hvalues : Partrec (fun z : ℕ × (ℕ × ℕ) =>
      (binaryLevel (wordLength z.2.1 + z.2.2)).mapM (phi z.1)) :=
    phi_list_comp (fun z : ℕ × (ℕ × ℕ) => z.1)
      (fun z => binaryLevel (wordLength z.2.1 + z.2.2)) Computable.fst hnodes.to_comp
  have hzip : Primrec (fun z : (ℕ × (ℕ × ℕ)) × List ℕ =>
      (binaryLevel (wordLength z.1.2.1 + z.1.2.2)).zip z.2) :=
    PrimitiveRecursiveAutomation.listZip (hnodes.comp Primrec.fst) Primrec.snd
  have hword : Primrec (fun z : (((ℕ × (ℕ × ℕ)) × List ℕ) × (ℕ × ℕ)) => z.1.1.2.1) :=
    hu.comp (Primrec.fst.comp Primrec.fst)
  have hv : Primrec (fun z : (((ℕ × (ℕ × ℕ)) × List ℕ) × (ℕ × ℕ)) => z.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun z : (((ℕ × (ℕ × ℕ)) × List ℕ) × (ℕ × ℕ)) => z.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hcell : Primrec (fun z : (((ℕ × (ℕ × ℕ)) × List ℕ) × (ℕ × ℕ)) =>
      !decide (Prefix z.1.1.2.1 z.2.1) || decide (z.2.2 = 0)) :=
    (Primrec.dom_bool₂ Bool.or).comp
      (Primrec.not.comp (prefix_primitive.comp (hword.pair hv)).decide)
      (Primrec.eq.comp hb (Primrec.const 0)).decide
  have hc : Primrec (fun z : (ℕ × (ℕ × ℕ)) × List ℕ =>
      ((binaryLevel (wordLength z.1.2.1 + z.1.2.2)).zip z.2).all
        (fun vb => !decide (Prefix z.1.2.1 vb.1) || decide (vb.2 = 0))) :=
    PrimitiveRecursiveAutomation.listAll hzip hcell
  unfold indexedEmpty
  exact hvalues.map hc.to_comp.to₂

private theorem list_decider_test (T : Set ℕ) (u : ℕ) (L : List ℕ) :
    (L.zip (L.map (indicator (fun v => v ∈ T)))).all
        (fun vb => !decide (Prefix u vb.1) || decide (vb.2 = 0)) =
      decide (∀ v ∈ L, v ∈ T → ¬ Prefix u v) := by
  classical
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases ha : a ∈ T <;> by_cases hp : Prefix u a <;>
      simp [indicator, ha, hp, ih]

theorem indexed_empty_eval (t : ℕ) (T : Set ℕ) (ht : TreeDeciderIndex t T) (u m : ℕ) :
    indexedEmpty t u m = Part.some (emptyTest T u m) := by
  unfold indexedEmpty
  change ∀ v, phi t v = Part.some (indicator (fun q => q ∈ T) v) at ht
  simp_rw [ht]
  have hm := (List.mapM_pure (m := Part)
    (l := binaryLevel (wordLength u + m)) (f := indicator (fun q => q ∈ T)))
  simp only [Part.pure_eq_some] at hm
  rw [hm, Part.map_some]
  apply congrArg Part.some
  rw [list_decider_test]
  apply Bool.eq_iff_iff.mpr
  simp only [emptyTest, decide_eq_true_eq]
  rfl

attribute [local irreducible] indexedEmpty

theorem indexed_tree_race_partial :
    Nat.Partrec (fun w => indexedTreeRace w.unpair.1 w.unpair.2) := by
  have happ : Computable₂ appendBit := appendBit_primitive.to_comp
  have hl : Partrec (fun z : (ℕ × ℕ) × ℕ => indexedEmpty z.1.1 (appendBit z.1.2 0) z.2) :=
    indexed_empty_partial.comp ((Computable.fst.comp Computable.fst).pair
      ((happ.comp (Computable.snd.comp Computable.fst) (Computable.const 0)).pair Computable.snd))
  have hr : Partrec (fun z : (ℕ × ℕ) × ℕ => indexedEmpty z.1.1 (appendBit z.1.2 1) z.2) :=
    indexed_empty_partial.comp ((Computable.fst.comp Computable.fst).pair
      ((happ.comp (Computable.snd.comp Computable.fst) (Computable.const 1)).pair Computable.snd))
  have hor : Computable₂ (fun (z : ((ℕ × ℕ) × ℕ) × Bool) (r : Bool) => z.2 || r) :=
    ((Primrec.dom_bool₂ Bool.or).to_comp.comp
      (Computable.snd.comp Computable.fst) Computable.snd).to₂
  have hright : Partrec (fun z : ((ℕ × ℕ) × ℕ) × Bool =>
      (indexedEmpty z.1.1.1 (appendBit z.1.1.2 1) z.1.2).map (fun r => z.2 || r)) :=
    (hr.comp Computable.fst).map hor
  have htest := hl.bind hright.to₂
  have hmin := Partrec.rfind htest.to₂
  have hout : Computable₂ (fun (_z : (ℕ × ℕ) × ℕ) (left : Bool) => if left then (0 : ℕ) else 1) :=
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const true))
      (Primrec.const 0) (Primrec.const 1)).to_comp.to₂
  have hbody := hmin.bind (hl.map hout).to₂
  have hvalid : Computable (fun w : ℕ × ℕ => decide (ValidCode w.2)) :=
    valid_code_primitive.decide.to_comp.comp Computable.snd
  have hfull := Partrec.cond hvalid hbody Partrec.none
  apply Partrec.nat_iff.mp
  apply (hfull.comp Computable.unpair).of_eq
  intro w
  simp only [indexedTreeRace, Bool.cond_decide, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map]

theorem indexed_tree_race_eval (t : ℕ) (T : Set ℕ) (ht : TreeDeciderIndex t T) (u : ℕ) :
    indexedTreeRace t u = treeRace T u := by
  unfold indexedTreeRace treeRace
  by_cases hu : ValidCode u
  · simp only [hu, ↓reduceIte]
    simp_rw [indexed_empty_eval t T ht]
    simp [Part.bind_eq_bind, negativeRace, raceStage, emptyTest, Bool.decide_or,
      Part.bind_some_eq_map]
  · simp only [hu, ↓reduceIte]

theorem tree_race_at_stage (T : Set ℕ) (u m : ℕ) (hu : ValidCode u)
    (hm : m ∈ raceStage (fun u m => EmptyExtension T (appendBit u 0) m)
      (fun u m => EmptyExtension T (appendBit u 1) m) u) :
    treeRace T u = Part.some (if EmptyExtension T (appendBit u 0) m then 0 else 1) := by
  simpa only [treeRace, hu, ↓reduceIte] using
    negativeRace_at_stage (fun u m => EmptyExtension T (appendBit u 0) m)
      (fun u m => EmptyExtension T (appendBit u 1) m) u m hm

/-- The two recognizers share one program, parameterized by side and tree-decider index. -/
def treeSideSearch (w : ℕ) : Part ℕ :=
  (indexedTreeRace w.unpair.1.unpair.2 w.unpair.2).bind fun side =>
    if side = w.unpair.1.unpair.1 then Part.some 0 else Part.none

attribute [local irreducible] indexedTreeRace

theorem tree_side_search_partial : Nat.Partrec treeSideSearch := by
  have hinput : Computable (fun w : ℕ => Nat.pair w.unpair.1.unpair.2 w.unpair.2) :=
    (Primrec₂.natPair.comp
      ((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair)).to_comp
  have hr : Partrec (fun w : ℕ => indexedTreeRace w.unpair.1.unpair.2 w.unpair.2) :=
    ((Partrec.nat_iff.mpr indexed_tree_race_partial).comp hinput).of_eq
      (fun w => by simp only [Nat.unpair_pair])
  have htest : Computable (fun z : ℕ × ℕ => decide (z.2 = z.1.unpair.1.unpair.1)) :=
    (Primrec.eq.comp Primrec.snd
      ((Primrec.fst.comp Primrec.unpair).comp
        ((Primrec.fst.comp Primrec.unpair).comp Primrec.fst))).decide.to_comp
  have hbranch : Partrec (fun z : ℕ × ℕ =>
      if z.2 = z.1.unpair.1.unpair.1 then Part.some 0 else Part.none) :=
    (Partrec.cond htest (Computable.const 0) Partrec.none).of_eq
      (fun z => by simp only [Bool.cond_decide, PFun.coe_val])
  exact Partrec.nat_iff.mp (hr.bind hbranch.to₂)

def TreeSideProgramIndex (v : ℕ) : Prop := ∀ w, phi v w = treeSideSearch w

theorem tree_side_program_index_exists : ∃ v, TreeSideProgramIndex v := by
  obtain ⟨v, hv⟩ := phi_complete tree_side_search_partial
  exact ⟨v, fun w => congrFun hv w⟩

def treeSideProgramIndex : ℕ := Classical.choose tree_side_program_index_exists

def treeSideIndex (side t : ℕ) : ℕ := specialize treeSideProgramIndex (Nat.pair side t)

theorem tree_side_index_primitive : Primrec₂ treeSideIndex := by
  exact specialize_primitive.comp (Primrec.const treeSideProgramIndex)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

theorem tree_side_index_eval (side t u : ℕ) :
    phi (treeSideIndex side t) u = (indexedTreeRace t u).bind
      (fun result => if result = side then Part.some 0 else Part.none) := by
  rw [treeSideIndex, specialize_eval]
  simpa only [treeSideSearch, treeSideProgramIndex, Nat.unpair_pair] using
    Classical.choose_spec tree_side_program_index_exists (Nat.pair (Nat.pair side t) u)

attribute [local irreducible] treeSideIndex

private theorem selected_side_domain (p : Part ℕ) (side : ℕ) :
    (p.bind (fun result => if result = side then Part.some 0 else Part.none)).Dom ↔ side ∈ p := by
  classical
  simp only [Part.dom_iff_mem, Part.mem_bind_iff]
  constructor
  · rintro ⟨a, b, hb, ha⟩
    by_cases h : b = side
    · exact h ▸ hb
    · simp only [h, ↓reduceIte, Part.notMem_none] at ha
  · intro h
    exact ⟨0, side, h, by simp⟩

theorem dead_pair_indices (t : ℕ) (T : Set ℕ) (ht : TreeDeciderIndex t T) :
    indexSet (treeSideIndex 0 t) = leftDead T ∧
      indexSet (treeSideIndex 1 t) = rightDead T := by
  constructor <;> ext u
  · change (phi (treeSideIndex 0 t) u).Dom ↔ 0 ∈ treeRace T u
    rw [tree_side_index_eval, indexed_tree_race_eval t T ht]
    exact selected_side_domain _ _
  · change (phi (treeSideIndex 1 t) u).Dom ↔ 1 ∈ treeRace T u
    rw [tree_side_index_eval, indexed_tree_race_eval t T ht]
    exact selected_side_domain _ _

theorem dead_pair_enumerable_disjoint (t : ℕ) (T : Set ℕ) (ht : TreeDeciderIndex t T) :
    REPred (fun u => u ∈ leftDead T) ∧ REPred (fun u => u ∈ rightDead T) ∧
      Disjoint (leftDead T) (rightDead T) := by
  have hi := dead_pair_indices t T ht
  refine ⟨(enumerable_iff_index _).mpr ⟨treeSideIndex 0 t, ?_⟩,
    (enumerable_iff_index _).mpr ⟨treeSideIndex 1 t, ?_⟩, ?_⟩
  · intro u
    change u ∈ leftDead T ↔ u ∈ indexSet (treeSideIndex 0 t)
    rw [hi.1]
  · intro u
    change u ∈ rightDead T ↔ u ∈ indexSet (treeSideIndex 1 t)
    rw [hi.2]
  · exact Set.disjoint_left.mpr fun _ h0 h1 => Nat.zero_ne_one (Part.mem_unique h0 h1)

private theorem left_dead_witness (T : Set ℕ) (u : ℕ) (hu : ValidCode u)
    (h : u ∈ leftDead T) : ∃ m, EmptyExtension T (appendBit u 0) m := by
  change 0 ∈ treeRace T u at h
  have hm : 0 ∈ negativeRace (fun u m => EmptyExtension T (appendBit u 0) m)
      (fun u m => EmptyExtension T (appendBit u 1) m) u := by
    simpa only [leftDead, treeRace, hu, ↓reduceIte] using h
  rw [negativeRace] at hm
  obtain ⟨m, _, hv⟩ := (Part.mem_map_iff _).mp hm
  by_cases he : EmptyExtension T (appendBit u 0) m
  · exact ⟨m, he⟩
  · simp only [he, ↓reduceIte] at hv
    contradiction

private theorem right_dead_witness (T : Set ℕ) (u : ℕ) (hu : ValidCode u)
    (h : u ∈ rightDead T) : ∃ m, EmptyExtension T (appendBit u 1) m := by
  change 1 ∈ treeRace T u at h
  have hm : 1 ∈ negativeRace (fun u m => EmptyExtension T (appendBit u 0) m)
      (fun u m => EmptyExtension T (appendBit u 1) m) u := by
    simpa only [rightDead, treeRace, hu, ↓reduceIte] using h
  rw [negativeRace] at hm
  obtain ⟨m, hstage, hv⟩ := (Part.mem_map_iff _).mp hm
  have hn : ¬ EmptyExtension T (appendBit u 0) m := by
    intro he
    simp only [he, ↓reduceIte] at hv
    contradiction
  exact ⟨m, ((raceStage_spec _ _ _ _).mp hstage).1.resolve_left hn⟩

theorem extendible_dead_children (T : Set ℕ) (hT : IsBinaryTree T)
    (u : ℕ) (hu : ValidCode u) (he : Extendible T u) :
    (u ∈ leftDead T ↔ ¬ Extendible T (appendBit u 0)) ∧
      (u ∈ rightDead T ↔ ¬ Extendible T (appendBit u 1)) := by
  constructor
  · constructor
    · intro h hn
      obtain ⟨m, hm⟩ := left_dead_witness T u hu h
      exact hn m hm
    · intro hn
      have hr := (one_child_survives T hT u hu he).resolve_left hn
      have hex : ∃ m, EmptyExtension T (appendBit u 0) m := by
        simpa only [Extendible, not_forall, not_not] using hn
      let m := Nat.find hex
      have hleft : EmptyExtension T (appendBit u 0) m := Nat.find_spec hex
      have hm : m ∈ raceStage (fun u m => EmptyExtension T (appendBit u 0) m)
          (fun u m => EmptyExtension T (appendBit u 1) m) u :=
        (raceStage_spec _ _ _ _).mpr ⟨Or.inl hleft,
          fun i hi => ⟨Nat.find_min hex hi, hr i⟩⟩
      change 0 ∈ treeRace T u
      apply Part.eq_some_iff.mp
      simpa only [hleft, ↓reduceIte] using tree_race_at_stage T u m hu hm
  · constructor
    · intro h hn
      obtain ⟨m, hm⟩ := right_dead_witness T u hu h
      exact hn m hm
    · intro hn
      have hl := (one_child_survives T hT u hu he).resolve_right hn
      have hex : ∃ m, EmptyExtension T (appendBit u 1) m := by
        simpa only [Extendible, not_forall, not_not] using hn
      let m := Nat.find hex
      have hright : EmptyExtension T (appendBit u 1) m := Nat.find_spec hex
      have hm : m ∈ raceStage (fun u m => EmptyExtension T (appendBit u 0) m)
          (fun u m => EmptyExtension T (appendBit u 1) m) u :=
        (raceStage_spec _ _ _ _).mpr ⟨Or.inr hright,
          fun i hi => ⟨hl i, Nat.find_min hex hi⟩⟩
      change 1 ∈ treeRace T u
      apply Part.eq_some_iff.mp
      simpa only [hl m, ↓reduceIte] using tree_race_at_stage T u m hu hm

def pairRaceIndex : ℕ := Classical.choose canonical_program_index_exists

/-- The same numerical map works before the DNC oracle varies. -/
def treePairMap (t u : ℕ) : ℕ :=
  canonicalIndex pairRaceIndex (treeSideIndex 0 t) (treeSideIndex 1 t) u

theorem tree_pair_map_primitive : Primrec₂ treePairMap := by
  have hl : Primrec (fun z : ℕ × ℕ => treeSideIndex 0 z.1) :=
    tree_side_index_primitive.comp (Primrec.const 0) Primrec.fst
  have hr : Primrec (fun z : ℕ × ℕ => treeSideIndex 1 z.1) :=
    tree_side_index_primitive.comp (Primrec.const 1) Primrec.fst
  unfold Primrec₂ treePairMap canonicalIndex
  exact specialize_primitive.comp (Primrec.const pairRaceIndex)
    (Primrec₂.natPair.comp hl (Primrec₂.natPair.comp hr Primrec.snd))

theorem tree_pair_map_reduction (t : ℕ) (T : Set ℕ) (ht : TreeDeciderIndex t T) :
    PairReduction (leftDead T) (rightDead T) (diagonalOutput 0) (diagonalOutput 1)
      (treePairMap t) := by
  have hi := dead_pair_indices t T ht
  have hd : Disjoint (indexSet (treeSideIndex 0 t)) (indexSet (treeSideIndex 1 t)) := by
    rw [hi.1, hi.2]
    exact (dead_pair_enumerable_disjoint t T ht).2.2
  have hp := canonical_pair_reduction pairRaceIndex
    (Classical.choose_spec canonical_program_index_exists) _ _ hd
  rw [hi.1, hi.2] at hp
  exact hp

def branchSelector (t : ℕ) (D : Set ℕ) (u : ℕ) : ℕ :=
  indicator (fun e => e ∈ D) (treePairMap t u)

theorem branch_selector_correct (t : ℕ) (T : Set ℕ) (ht : TreeDeciderIndex t T)
    (hT : IsBinaryTree T) (D : Set ℕ) (hD : D ∈ binaryDNCClass)
    (u : ℕ) (hu : ValidCode u) (he : Extendible T u) :
    Extendible T (appendBit u (branchSelector t D u)) := by
  have hp := tree_pair_map_reduction t T ht
  have hd := (dnc_iff_separator D).mp hD
  have hc := extendible_dead_children T hT u hu he
  by_cases hq : treePairMap t u ∈ D
  · simp only [branchSelector, indicator, hq, ↓reduceIte]
    by_contra hn
    have hr : treePairMap t u ∈ diagonalOutput 1 := (hp.2.2 u).mp (hc.2.mpr hn)
    exact Set.disjoint_left.mp hd.2 hq hr
  · simp only [branchSelector, indicator, hq, ↓reduceIte]
    by_contra hn
    exact hq (hd.1 ((hp.2.1 u).mp (hc.1.mpr hn)))

end
end Lemmatheca.ComputabilityTheory.PaDegrees
