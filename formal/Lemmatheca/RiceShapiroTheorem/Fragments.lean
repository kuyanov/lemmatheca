import Lemmatheca.RicesTheorem.RicesTheorem
import Lemmatheca.EffectiveEnumerations.Stages
import Mathlib.Data.Set.Card

/-! Finite positive graph observations in the existing numerical program numbering. -/
namespace Lemmatheca.ComputabilityTheory.RiceShapiroTheorem

open UniversalComputation
open RicesTheorem (PartialFunction Extensional)

abbrev PairList := List (ℕ × ℕ)

def Consistent (D : PairList) : Prop :=
  ∀ p ∈ D, ∀ q ∈ D, p.1 = q.1 → p.2 = q.2

def pairList (d : ℕ) : PairList :=
  (FiniteSequenceCoding.decode d).map Nat.unpair

def pairListCode (D : PairList) : ℕ :=
  FiniteSequenceCoding.code (D.map fun p => Nat.pair p.1 p.2)

def Valid (d : ℕ) : Prop := Consistent (pairList d)

def tableFunction (D : PairList) (x : ℕ) : Part ℕ :=
  Part.ofOption (D.lookup x)

def fragment (d : ℕ) : PartialFunction := tableFunction (pairList d)

def GraphInclusion (f g : PartialFunction) : Prop :=
  ∀ x y, y ∈ f x → y ∈ g x

def graph (f : PartialFunction) : Set (ℕ × ℕ) := {p | p.2 ∈ f p.1}

def FiniteGraph (f : PartialFunction) : Prop := (graph f).Finite

theorem pairList_code (D : PairList) : pairList (pairListCode D) = D := by
  unfold pairList pairListCode
  rw [FiniteSequenceCoding.decode_code]
  induction D with
  | nil => rfl
  | cons p D ih =>
    rcases p with ⟨x, y⟩
    simp only [List.map_cons, Nat.unpair_pair, ih]

private theorem pairList_primitive : Primrec pairList := by
  exact Primrec.list_map (Primrec.ofNat (List ℕ))
    (Primrec.unpair.comp Primrec.snd).to₂

theorem valid_primitive : PrimrecPred Valid := by
  have h : PrimrecRel (fun (q p : ℕ × ℕ) => p.1 = q.1 → p.2 = q.2) :=
    ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)).not.or
      (Primrec.eq.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst))).of_eq (fun z => by simp only [imp_iff_not_or])
  have h' : PrimrecRel (fun (p : ℕ × ℕ) (D : PairList) =>
      ∀ q ∈ D, p.1 = q.1 → p.2 = q.2) :=
    h.forall_mem_list.comp Primrec.snd Primrec.fst
  exact h'.forall_mem_list.comp pairList_primitive pairList_primitive

private theorem tableFunction_mem_list {D : PairList} {x y : ℕ}
    (h : y ∈ tableFunction D x) : (x, y) ∈ D := by
  have he : D.lookup x = some y := by simpa only [tableFunction, Part.mem_ofOption,
    Option.mem_def] using h
  obtain ⟨l₁, l₂, rfl, _⟩ := List.lookup_eq_some_iff.mp he
  simp

theorem tableFunction_mem (D : PairList) (hD : Consistent D) (x y : ℕ) :
    y ∈ tableFunction D x ↔ (x, y) ∈ D := by
  constructor
  · exact tableFunction_mem_list
  · intro h
    have hs : (D.lookup x).isSome := List.lookup_isSome_iff.mpr ⟨(x, y), h, by simp⟩
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hs
    have hm : z ∈ tableFunction D x := by
      simpa only [tableFunction, Part.mem_ofOption, Option.mem_def] using hz
    have he : z = y := hD (x, z) (tableFunction_mem_list hm) (x, y) h rfl
    simpa only [he] using hm

theorem fragment_finite (d : ℕ) : FiniteGraph (fragment d) := by
  refine (pairList d).toFinset.finite_toSet.subset ?_
  intro p hp
  simpa only [Finset.mem_coe, List.mem_toFinset] using tableFunction_mem_list hp

theorem finite_graph_has_code (f : PartialFunction) (hf : FiniteGraph f) :
    ∃ d, Valid d ∧ fragment d = f := by
  classical
  let D : PairList := hf.toFinset.toList
  have hD (p : ℕ × ℕ) : p ∈ D ↔ p.2 ∈ f p.1 := by
    simp [D, graph]
  have hc : Consistent D := by
    intro p hp q hq he
    have hp' := (hD p).mp hp
    have hq' := (hD q).mp hq
    rw [he] at hp'
    exact Part.mem_unique hp' hq'
  refine ⟨pairListCode D, ?_, ?_⟩
  · simpa only [Valid, pairList_code] using hc
  · change tableFunction (pairList (pairListCode D)) = f
    rw [pairList_code]
    funext x
    exact Part.ext fun y => (tableFunction_mem D hc x y).trans (hD (x, y))

theorem fragment_partial : Partrec₂ fragment := by
  change Partrec (fun p : ℕ × ℕ => Part.ofOption ((pairList p.1).lookup p.2))
  exact (Primrec.listLookup.comp Primrec.snd
    (pairList_primitive.comp Primrec.fst)).to_comp.ofOption

noncomputable def fragmentProgram : ℕ :=
  Classical.choose (phi_complete (Partrec₂.unpaired'.mpr fragment_partial))

noncomputable def fragmentIndex (d : ℕ) : ℕ := specialize fragmentProgram d

theorem fragmentProgram_spec (d x : ℕ) :
    phi fragmentProgram (Nat.pair d x) = fragment d x := by
  have h := Classical.choose_spec (phi_complete (Partrec₂.unpaired'.mpr fragment_partial))
  simpa only [fragmentProgram, Nat.unpaired, Nat.unpair_pair] using congrFun h (Nat.pair d x)

theorem fragmentIndex_primitive : Primrec fragmentIndex := by
  exact specialize_primitive.comp (Primrec.const _) Primrec.id

theorem fragmentIndex_eval (d x : ℕ) : phi (fragmentIndex d) x = fragment d x := by
  rw [fragmentIndex, specialize_eval, fragmentProgram_spec]

theorem empty_fragment : Valid (pairListCode []) ∧
    fragment (pairListCode []) = RicesTheorem.bottom := by
  constructor
  · simp [Valid, pairList_code, Consistent]
  · funext x
    simp [fragment, pairList_code, tableFunction, Part.ofOption, RicesTheorem.bottom]

theorem unlisted_input_answer :
    Consistent [(2, 7)] ∧ Consistent [(2, 7), (0, 17)] ∧
    GraphInclusion (tableFunction [(2, 7)]) (tableFunction [(2, 7), (0, 17)]) ∧
    tableFunction [(2, 7)] 0 = Part.none ∧
    tableFunction [(2, 7), (0, 17)] 0 = Part.some 17 := by
  have h₁ : Consistent [(2, 7)] := by simp [Consistent]
  have h₂ : Consistent [(2, 7), (0, 17)] := by simp [Consistent]
  refine ⟨h₁, h₂, ?_, rfl, rfl⟩
  intro x y h
  apply (tableFunction_mem _ h₂ x y).mpr
  exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp
    ((tableFunction_mem _ h₁ x y).mp h)))

def Match (e d t : ℕ) : Prop :=
  ∀ p ∈ pairList d, ∃ k < t, boundedValue k e p.1 = p.2 + 1

theorem match_primitive :
    PrimrecPred (fun p : (ℕ × ℕ) × ℕ => Match p.1.1 p.1.2 p.2) := by
  have hs : PrimrecRel (fun (k : ℕ) (p : (ℕ × ℕ) × ℕ) =>
      boundedValue k p.1.1 p.1.2 = p.2 + 1) := by
    exact Primrec.eq.comp
      (boundedValue_primitive.comp
        ((Primrec.fst.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
  have hr : PrimrecRel (fun (q : ℕ × ℕ) (p : (ℕ × ℕ) × ℕ) =>
      ∃ k < p.2, boundedValue k p.1.1 q.1 = q.2 + 1) := by
    change PrimrecPred (fun a : (ℕ × ℕ) × ((ℕ × ℕ) × ℕ) =>
      ∃ k < a.2.2, boundedValue k a.2.1.1 a.1.1 = a.1.2 + 1)
    simpa only [List.mem_range] using hs.exists_mem_list.comp
      (Primrec.list_range.comp (Primrec.snd.comp Primrec.snd))
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst))
  exact hr.forall_mem_list.comp
    (pairList_primitive.comp (Primrec.snd.comp Primrec.fst)) Primrec.id

theorem match_iff (e d : ℕ) (hd : Valid d) :
    GraphInclusion (fragment d) (phi e) ↔ ∃ t, Match e d t := by
  have bound : ∀ D : PairList,
      (∀ p ∈ D, ∃ k, boundedValue k e p.1 = p.2 + 1) →
      ∃ t, ∀ p ∈ D, ∃ k < t, boundedValue k e p.1 = p.2 + 1 := by
    intro D
    induction D with
    | nil => intro _; exact ⟨0, by simp⟩
    | cons p D ih =>
      intro h
      obtain ⟨k, hk⟩ := h p (by simp)
      obtain ⟨t, ht⟩ := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
      refine ⟨max (k + 1) t, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _), hk⟩
      · obtain ⟨j, hj, he⟩ := ht q hq
        exact ⟨j, Nat.lt_of_lt_of_le hj (le_max_right _ _), he⟩
  constructor
  · intro h
    apply bound (pairList d)
    intro p hp
    exact (phi_output e p.1 p.2).mp
      (h p.1 p.2 ((tableFunction_mem (pairList d) hd p.1 p.2).mpr hp))
  · rintro ⟨t, ht⟩ x y hxy
    obtain ⟨k, _, hk⟩ := ht (x, y) ((tableFunction_mem (pairList d) hd x y).mp hxy)
    exact (phi_output e x y).mpr ⟨k, hk⟩

theorem empty_match (e t : ℕ) : Match e (pairListCode []) t := by
  simp [Match, pairList_code]

/-- The entry's W_r is the existing domain numbering, and H is its actual finite stage. -/
abbrev W := EffectiveEnumerations.indexSet

def H (r j t : ℕ) : Prop := j ∈ EffectiveEnumerations.stage r t

end Lemmatheca.ComputabilityTheory.RiceShapiroTheorem
