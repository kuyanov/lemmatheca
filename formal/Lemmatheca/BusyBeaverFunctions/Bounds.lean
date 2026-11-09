import Lemmatheca.BusyBeaverFunctions.ProgramSize

/-! The finite output/resource extrema and their computable approximations. -/
namespace Lemmatheca.ComputabilityTheory.BusyBeaverFunctions

open Encodable Denumerable
open Nat.Partrec (Code)
open UniversalComputation

set_option backward.isDefEq.respectTransparency false

/-- Search for a least successful allowance; divergence remains a partial value. -/
def leastResource (e x : ℕ) : Part ℕ :=
  Nat.rfind (fun k => Part.some (decide (0 < boundedValue k e x)))

theorem leastResource_spec (e x k : ℕ) :
    k ∈ leastResource e x ↔ certificate e x k ∧ ∀ j < k, ¬ certificate e x j := by
  simp [leastResource, Nat.mem_rfind, certificate]

theorem leastResource_domain (e x : ℕ) : (leastResource e x).Dom ↔ (phi e x).Dom := by
  rw [phi_domain]
  simp [leastResource, Nat.rfind_dom, certificate]

theorem leastResource_partrec :
    Nat.Partrec (fun z => leastResource z.unpair.1 z.unpair.2) := by
  have hv : Primrec (fun p : ℕ × ℕ =>
      boundedValue p.2 p.1.unpair.1 p.1.unpair.2) :=
    boundedValue_primitive.comp
      ((Primrec.snd.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))).pair
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
  have hp : Computable (fun p : ℕ × ℕ =>
      decide (0 < boundedValue p.2 p.1.unpair.1 p.1.unpair.2)) :=
    (Primrec.nat_lt.comp (Primrec.const 0) hv).decide.to_comp
  exact Partrec.nat_iff.mp (Partrec.rfind hp.to₂.partrec₂)

/-- Undefined contestants contribute the already included value zero to maxima. -/
noncomputable def zeroDefault (p : Part ℕ) : ℕ := by
  classical
  exact if h : p.Dom then p.get h else 0

noncomputable def outputMaximum (n : ℕ) : ℕ :=
  ((contestants n).map (fun c => zeroDefault (Code.eval c 0))).foldl max 0

noncomputable def resourceMaximum (n : ℕ) : ℕ :=
  ((contestants n).map (fun c => zeroDefault (leastResource (encode c) 0))).foldl max 0

theorem zeroDefault_value {p : Part ℕ} {y : ℕ} (hy : y ∈ p) : zeroDefault p = y := by
  classical
  rw [zeroDefault, dite_eq_left hy.1]
  exact Part.mem_unique (Part.get_mem hy.1) hy

private theorem zeroDefault_le_iff (p : Part ℕ) (b : ℕ) :
    zeroDefault p ≤ b ↔ ∀ y ∈ p, y ≤ b := by
  classical
  by_cases h : p.Dom
  · rw [zeroDefault, dite_eq_left h]
    constructor
    · intro hb y hy
      rw [← Part.mem_unique (Part.get_mem h) hy]
      exact hb
    · intro hb
      exact hb _ (Part.get_mem h)
  · constructor
    · intro _ y hy
      exact (h hy.1).elim
    · intro _
      simp [zeroDefault, h]

private theorem fold_max_le (xs : List ℕ) (a b : ℕ) :
    xs.foldl max a ≤ b ↔ a ≤ b ∧ ∀ x ∈ xs, x ≤ b := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, and_assoc]

theorem outputMaximum_le_iff (n b : ℕ) :
    outputMaximum n ≤ b ↔ ∀ c, nodeSize c ≤ n → ∀ y ∈ Code.eval c 0, y ≤ b := by
  simp [outputMaximum, fold_max_le, zeroDefault_le_iff, contestants_spec]

theorem resourceMaximum_le_iff (n b : ℕ) :
    resourceMaximum n ≤ b ↔
      ∀ c, nodeSize c ≤ n → ∀ k ∈ leastResource (encode c) 0, k ≤ b := by
  simp [resourceMaximum, fold_max_le, zeroDefault_le_iff, contestants_spec]

theorem maxima_monotone : Monotone outputMaximum ∧ Monotone resourceMaximum := by
  constructor
  · intro m n h
    apply (outputMaximum_le_iff m (outputMaximum n)).mpr
    intro c hc y hy
    exact (outputMaximum_le_iff n (outputMaximum n)).mp le_rfl c (hc.trans h) y hy
  · intro m n h
    apply (resourceMaximum_le_iff m (resourceMaximum n)).mpr
    intro c hc k hk
    exact (resourceMaximum_le_iff n (resourceMaximum n)).mp le_rfl c (hc.trans h) k hk

theorem maxima_zero : outputMaximum 0 = 0 ∧ resourceMaximum 0 = 0 := by
  exact ⟨rfl, rfl⟩

theorem bounded_value_persists {k l e x y : ℕ} (hkl : k ≤ l)
    (h : boundedValue k e x = y + 1) : boundedValue l e x = y + 1 := by
  exact (boundedValue_output l e x y).mpr
    (Code.evaln_mono hkl ((boundedValue_output k e x y).mp h))

theorem certificate_value {e x k y : ℕ} (h : certificate e x k) (hy : y ∈ phi e x) :
    boundedValue k e x = y + 1 := by
  have hp : 0 < boundedValue k e x := h
  have hm : boundedValue k e x - 1 ∈ phi e x :=
    (phi_output e x _).mpr ⟨k, by omega⟩
  have := Part.mem_unique hm hy
  omega

theorem contestant_bounds (c : Code) (n y : ℕ) (hs : nodeSize c ≤ n)
    (hy : y ∈ Code.eval c 0) :
    y ≤ outputMaximum n ∧
      ∃ k ∈ leastResource (encode c) 0,
        k ≤ resourceMaximum n ∧ boundedValue (resourceMaximum n) (encode c) 0 = y + 1 := by
  have hyp : y ∈ phi (encode c) 0 := by simpa [phi] using hy
  have hd := (leastResource_domain (encode c) 0).mpr hyp.1
  obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp hd
  have hks := (resourceMaximum_le_iff n (resourceMaximum n)).mp le_rfl c hs k hk
  refine ⟨(outputMaximum_le_iff n (outputMaximum n)).mp le_rfl c hs y hy, k, hk, hks, ?_⟩
  exact bounded_value_persists hks (certificate_value ((leastResource_spec _ _ _).mp hk).1 hyp)

/-- When success is visible, the bounded scan returns its first successful index. -/
def firstSeen (s e x : ℕ) : ℕ :=
  if 0 < boundedValue s e x then
    (List.range (s + 1)).findIdx (fun k => decide (0 < boundedValue k e x))
  else 0

def outputStage (s n : ℕ) : ℕ :=
  ((contestants n).map (fun c => boundedValue s (encode c) 0 - 1)).foldl max 0

def resourceStage (s n : ℕ) : ℕ :=
  ((contestants n).map (fun c => firstSeen s (encode c) 0)).foldl max 0

theorem firstSeen_spec (s e x : ℕ) (h : certificate e x s) :
    firstSeen s e x ∈ leastResource e x ∧ firstSeen s e x ≤ s := by
  dsimp [certificate] at h
  obtain ⟨k, hk, hks⟩ := Nat.rfind_min'
    (p := fun j => decide (0 < boundedValue j e x))
    (m := s) (by simpa only [decide_eq_true_eq] using h)
  change k ∈ leastResource e x at hk
  have hm := (leastResource_spec e x k).mp hk
  dsimp [certificate] at hm
  have heq : (List.range (s + 1)).findIdx (fun j => decide (0 < boundedValue j e x)) = k := by
    apply (List.findIdx_eq (by simpa using Nat.lt_succ_of_le hks)).mpr
    constructor
    · simpa only [List.getElem_range, decide_eq_true_eq] using hm.1
    · intro j hj
      simpa only [List.getElem_range, decide_eq_false_iff_not] using hm.2 j hj
  rw [firstSeen, ite_eq_left h, heq]
  exact ⟨hk, hks⟩

private theorem bounded_primitive {α : Type*} [Primcodable α]
    {k e x : α → ℕ} (hk : Primrec k) (he : Primrec e) (hx : Primrec x) :
    Primrec (fun a => boundedValue (k a) (e a) (x a)) :=
  boundedValue_primitive.comp ((hk.pair he).pair hx)

private theorem firstSeen_primitive : Primrec (fun p : (ℕ × ℕ) × ℕ => firstSeen p.1.1 p.1.2 p.2) := by
  have hs : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have he : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hx : Primrec (fun p : (ℕ × ℕ) × ℕ => p.2) := Primrec.snd
  have hp := Primrec.nat_lt.comp (Primrec.const 0) (bounded_primitive hs he hx)
  have hi := Primrec.list_findIdx (Primrec.list_range.comp (Primrec.succ.comp hs))
    ((Primrec.nat_lt.comp (Primrec.const 0)
      (bounded_primitive Primrec.snd (he.comp Primrec.fst) (hx.comp Primrec.fst))).decide).to₂
  exact Primrec.ite hp hi (Primrec.const 0)

theorem stages_computable : Computable₂ outputStage ∧ Computable₂ resourceStage := by
  have hc : Primrec (fun p : ℕ × ℕ => contestants p.2) := contestants_primitive.comp Primrec.snd
  have hv : Primrec (fun p : (ℕ × ℕ) × Code => boundedValue p.1.1 (encode p.2) 0 - 1) :=
    Primrec.nat_sub.comp
      (bounded_primitive (Primrec.fst.comp Primrec.fst)
        (Primrec.encode.comp Primrec.snd) (Primrec.const 0)) (Primrec.const 1)
  have hr : Primrec (fun p : (ℕ × ℕ) × Code => firstSeen p.1.1 (encode p.2) 0) :=
    firstSeen_primitive.comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.encode.comp Primrec.snd)).pair (Primrec.const 0))
  have hb := Primrec.list_foldl (Primrec.list_map hc hv.to₂) (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  have hs := Primrec.list_foldl (Primrec.list_map hc hr.to₂) (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact ⟨hb.to_comp, hs.to_comp⟩

private theorem fold_map_max_mono {α : Type*} (xs : List α) (f g : α → ℕ)
    (h : ∀ c, f c ≤ g c) :
    (xs.map f).foldl max 0 ≤ (xs.map g).foldl max 0 := by
  apply (fold_max_le _ 0 _).mpr
  refine ⟨Nat.zero_le _, ?_⟩
  intro y hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
  exact (h c).trans (((fold_max_le (xs.map g) 0 _).mp le_rfl).2
    (g c) (List.mem_map.mpr ⟨c, hc, rfl⟩))

private theorem output_value_monotone (e x : ℕ) :
    Monotone (fun s => boundedValue s e x - 1) := by
  intro s t hst
  change boundedValue s e x - 1 ≤ boundedValue t e x - 1
  by_cases hs : boundedValue s e x = 0
  · simp [hs]
  · have ht := bounded_value_persists (e := e) (x := x) (y := boundedValue s e x - 1) hst (by omega)
    rw [ht]
    omega

private theorem firstSeen_monotone (e x : ℕ) : Monotone (fun s => firstSeen s e x) := by
  intro s t hst
  by_cases hs : 0 < boundedValue s e x
  · have ht := bounded_value_persists (e := e) (x := x) (y := boundedValue s e x - 1) hst (by omega)
    have htp : 0 < boundedValue t e x := by omega
    have hk := firstSeen_spec s e x (by simpa only [certificate] using hs)
    have hl := firstSeen_spec t e x (by simpa only [certificate] using htp)
    exact Nat.le_of_eq (Part.mem_unique hk.1 hl.1)
  · simp [firstSeen, hs]

theorem stages_monotone (n : ℕ) :
    Monotone (fun s => outputStage s n) ∧ Monotone (fun s => resourceStage s n) := by
  constructor
  · intro s t hst
    exact fold_map_max_mono (contestants n) _ _ (fun c => output_value_monotone (encode c) 0 hst)
  · intro s t hst
    exact fold_map_max_mono (contestants n) _ _ (fun c => firstSeen_monotone (encode c) 0 hst)

theorem stages_bounded (s n : ℕ) :
    outputStage s n ≤ outputMaximum n ∧ resourceStage s n ≤ resourceMaximum n := by
  constructor
  · apply (fold_max_le _ 0 _).mpr
    refine ⟨Nat.zero_le _, ?_⟩
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    by_cases hs : 0 < boundedValue s (encode c) 0
    · have hm : boundedValue s (encode c) 0 - 1 ∈ phi (encode c) 0 :=
        (phi_output _ _ _).mpr ⟨s, by omega⟩
      have hmc : boundedValue s (encode c) 0 - 1 ∈ Code.eval c 0 := by simpa [phi] using hm
      exact (outputMaximum_le_iff n (outputMaximum n)).mp le_rfl c
        ((contestants_spec n c).mp hc) _ hmc
    · have hz : boundedValue s (encode c) 0 = 0 := by omega
      simp [hz]
  · apply (fold_max_le _ 0 _).mpr
    refine ⟨Nat.zero_le _, ?_⟩
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    by_cases hs : 0 < boundedValue s (encode c) 0
    · exact (resourceMaximum_le_iff n (resourceMaximum n)).mp le_rfl c
        ((contestants_spec n c).mp hc) _
        (firstSeen_spec s (encode c) 0 (by simpa only [certificate] using hs)).1
    · simp [firstSeen, hs]

private theorem exact_contributions (n s : ℕ) (c : Code)
    (hc : c ∈ contestants n) (hs : resourceMaximum n ≤ s) :
    boundedValue s (encode c) 0 - 1 = zeroDefault (Code.eval c 0) ∧
      firstSeen s (encode c) 0 = zeroDefault (leastResource (encode c) 0) := by
  classical
  by_cases hd : (Code.eval c 0).Dom
  · have hy := Part.get_mem hd
    obtain ⟨_, k, hk, _, hbk⟩ := contestant_bounds c n _ ((contestants_spec n c).mp hc) hy
    have hbs := bounded_value_persists hs hbk
    have hcert : certificate (encode c) 0 s := by dsimp [certificate]; omega
    have hfs := (firstSeen_spec s (encode c) 0 hcert).1
    constructor
    · rw [hbs, zeroDefault_value hy]
      omega
    · rw [zeroDefault_value hk]
      exact Part.mem_unique hfs hk
  · have hphi : ¬ (phi (encode c) 0).Dom := by simpa [phi] using hd
    have hl : ¬ (leastResource (encode c) 0).Dom :=
      fun h => hphi ((leastResource_domain _ _).mp h)
    have hcert : ¬ certificate (encode c) 0 s := fun h => hphi ((phi_domain _ _).mpr ⟨s, h⟩)
    have hz : boundedValue s (encode c) 0 = 0 := by dsimp [certificate] at hcert; omega
    simp [hz, zeroDefault, hd, hl, firstSeen]

theorem stages_exact_after (n : ℕ) :
    ∀ s, resourceMaximum n ≤ s →
      outputStage s n = outputMaximum n ∧ resourceStage s n = resourceMaximum n := by
  intro s hs
  constructor
  · exact congrArg (fun xs : List ℕ => xs.foldl max 0)
      (List.map_congr_left (fun c hc => (exact_contributions n s c hc hs).1))
  · exact congrArg (fun xs : List ℕ => xs.foldl max 0)
      (List.map_congr_left (fun c hc => (exact_contributions n s c hc hs).2))

theorem outputMaximum_one : outputMaximum 1 = 1 := by
  apply Nat.le_antisymm
  · apply (outputMaximum_le_iff 1 1).mpr
    intro c hc y hy
    cases c with
    | zero =>
      rw [show Code.eval Code.zero 0 = Part.some 0 from Code.eval_const 0 0] at hy
      have := Part.mem_some_iff.mp hy
      omega
    | succ | left | right => simp_all [Code.eval]
    | pair c d | comp c d | prec c d =>
      have := nodeSize_positive c
      have := nodeSize_positive d
      simp only [nodeSize] at hc
      omega
    | rfind' c =>
      have := nodeSize_positive c
      simp only [nodeSize] at hc
      omega
  · exact (outputMaximum_le_iff 1 (outputMaximum 1)).mp le_rfl .succ (by decide) 1 (by simp [Code.eval])

end Lemmatheca.ComputabilityTheory.BusyBeaverFunctions
