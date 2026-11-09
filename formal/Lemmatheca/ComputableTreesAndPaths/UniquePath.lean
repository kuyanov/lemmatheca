import Lemmatheca.ComputableTreesAndPaths.HaltingPath

/-! An ordinary search for the sole surviving short prefix; duplicate prefixes count once. -/
namespace Lemmatheca.ComputabilityTheory.ComputableTreesAndPaths

open IncomparableTuringDegrees PostsTheorem UniversalComputation

set_option backward.isDefEq.respectTransparency false

noncomputable section

def survivors (T : Set ℕ) (n m : ℕ) : List ℕ := by
  classical
  exact (((binaryLevel m).filter (fun u => decide (u ∈ T))).map
    (takeCode (n + 1))).eraseDups

theorem survivors_spec (T : Set ℕ) (n m u : ℕ) (_hnm : n + 1 ≤ m) :
    u ∈ survivors T n m ↔
      ∃ v ∈ T, ValidCode v ∧ wordLength v = m ∧ takeCode (n + 1) v = u := by
  classical
  simp only [survivors, List.mem_eraseDups, List.mem_map, List.mem_filter,
    binary_level_spec, decide_eq_true_eq]
  aesop

theorem survivors_computable (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) :
    Computable₂ (survivors T) := by
  classical
  let f (n v : ℕ) : Option ℕ := if v ∈ T then some (takeCode (n + 1) v) else none
  have hf : Computable₂ f := by
    have hp := Computable.option_some.comp
      (take_code_primitive.to_comp.comp (Computable.succ.comp Computable.fst) Computable.snd)
    have hh := Computable.cond (hc.decide.comp Computable.snd) hp (Computable.const none)
    exact hh.to₂.of_eq (fun _ => by simp only [Bool.cond_decide]; rfl)
  have hm := (computable_list_map f hf).comp Computable.fst
    (binary_level_primitive.to_comp.comp Computable.snd)
  have hr : Primrec (fun l : List (Option ℕ) => l.filterMap id) :=
    Primrec.listFilterMap Primrec.id Primrec.snd
  have hh := erase_dups_primitive.to_comp.comp (hr.to_comp.comp hm)
  apply hh.to₂.of_eq
  intro p
  have he (l : List ℕ) : (l.map (f p.1)).filterMap id =
      (l.filter (fun v => decide (v ∈ T))).map (takeCode (p.1 + 1)) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      have ih' : l.filterMap (fun v => if v ∈ T then some (takeCode (p.1 + 1) v) else none) =
          (l.filter (fun v => decide (v ∈ T))).map (takeCode (p.1 + 1)) := by
        simpa only [f, List.filterMap_map, Function.comp_def, id_eq] using ih
      by_cases ha : a ∈ T <;> simp [f, ha, ih']
  change (((binaryLevel p.2).map (f p.1)).filterMap id).eraseDups = _
  rw [he]
  rfl

theorem survivor_path_prefix (T : Set ℕ) (X : Set ℕ) (hX : Path T X)
    (n m : ℕ) (hnm : n + 1 ≤ m) :
    prefixCode X (n + 1) ∈ survivors T n m := by
  apply (survivors_spec T n m _ hnm).mpr
  refine ⟨prefixCode X m, hX m, prefix_code_valid _ _, (prefixCode_spec _ _).1, ?_⟩
  simp [takeCode, prefixCode, ← List.map_take, List.take_range, min_eq_left hnm]

theorem survivors_decreasing (T : Set ℕ) (hT : IsBinaryTree T)
    (n m k : ℕ) (hnm : n + 1 ≤ m) :
    ∀ u ∈ survivors T n (m + k), u ∈ survivors T n m := by
  intro u hu
  obtain ⟨v, hvT, hv, hvl, he⟩ := (survivors_spec T n (m + k) u (by omega)).mp hu
  apply (survivors_spec T n m u hnm).mpr
  refine ⟨takeCode m v, hT.2 _ _ (take_valid _ _ hv) hvT (take_spec _ _ hv).2,
    take_valid _ _ hv, ?_, ?_⟩
  · rw [(take_spec _ _ hv).1, hvl, min_eq_left (by omega)]
  · simpa only [takeCode, FiniteSequenceCoding.decode_code, List.take_take,
      min_eq_left hnm] using he

private theorem extendible_has_path (T : Set ℕ) (hT : IsBinaryTree T) (u : ℕ)
    (hu : ValidCode u) (he : Extendible T u) : ∃ X, Path T X ∧ Realizes u X := by
  classical
  have huT : u ∈ T := by
    obtain ⟨v, hvT, _, hp⟩ :
        ∃ v ∈ T, wordLength v = wordLength u + 0 ∧ Prefix u v := by
      simpa only [empty_extension_spec T hT, not_not] using he 0
    exact hT.2 _ _ hu hvT hp
  let S : Set ℕ := {v | v ∈ T ∧ (Prefix v u ∨ Prefix u v)}
  have hS : IsBinaryTree S := by
    refine ⟨fun v hv => hT.1 _ hv.1, ?_⟩
    intro w v hw hv hwv
    refine ⟨hT.2 _ _ hw hv.1 hwv, ?_⟩
    rcases hv.2 with hvu | huv
    · exact Or.inl (prefix_trans hwv hvu)
    · by_cases hlen : wordLength w ≤ wordLength u
      · exact Or.inl ⟨hlen, fun q hq =>
          (hwv.2 q hq).trans (huv.2 q (lt_of_lt_of_le hq hlen)).symm⟩
      · have hle : wordLength u ≤ wordLength w := by omega
        exact Or.inr ⟨hle, fun q hq =>
          (huv.2 q hq).trans (hwv.2 q (lt_of_lt_of_le hq hle)).symm⟩
  have hi (n : ℕ) : HasLevel S n := by
    by_cases hn : n ≤ wordLength u
    · have hp := (take_spec n u hu).2
      refine ⟨takeCode n u, ⟨hT.2 _ _ (take_valid _ _ hu) huT hp, Or.inl hp⟩, ?_⟩
      rw [(take_spec _ _ hu).1, min_eq_left hn]
    · obtain ⟨v, hvT, hvl, hp⟩ : ∃ v ∈ T,
          wordLength v = wordLength u + (n - wordLength u) ∧ Prefix u v := by
        simpa only [empty_extension_spec T hT, not_not] using he (n - wordLength u)
      exact ⟨v, ⟨hvT, Or.inr hp⟩, by omega⟩
  obtain ⟨X, hX⟩ := (all_levels_path S hS).mp hi
  refine ⟨X, fun n => (hX n).1, ?_⟩
  have hs := hX (wordLength u + 1)
  have hl : wordLength (prefixCode X (wordLength u + 1)) = wordLength u + 1 :=
    (prefixCode_spec X (wordLength u + 1)).1
  have hp : Prefix u (prefixCode X (wordLength u + 1)) := by
    rcases hs.2 with hleft | hright
    · have hbad := hleft.1
      rw [hl] at hbad
      omega
    · exact hright
  intro q hq
  exact (hp.2 q hq).trans ((prefixCode_spec X (wordLength u + 1)).2 q (by omega))

theorem unique_survivor (T : Set ℕ) (hT : IsBinaryTree T) (X : Set ℕ)
    (hX : Path T X) (hu : ∀ Y, Path T Y → Y = X) (n : ℕ) :
    ∃ m ≥ n + 1, survivors T n m = [prefixCode X (n + 1)] := by
  classical
  let L := binaryLevel (n + 1)
  let good := prefixCode X (n + 1)
  have dies (u : ℕ) (hL : u ∈ L) (hne : u ≠ good) : ∃ k, EmptyExtension T u k := by
    have hv := (binary_level_spec (n + 1) u).mp hL
    by_contra hnot
    have he : Extendible T u := by simpa only [Extendible, not_exists] using hnot
    obtain ⟨Y, hY, hr⟩ := extendible_has_path T hT u hv.1 he
    have hYX := hu Y hY
    rw [hYX] at hr
    have hc := realizes_code u X hv.1 hr
    rw [hv.2] at hc
    exact hne hc
  let kill (u : ℕ) := if h : u ∈ L ∧ u ≠ good then Nat.find (dies u h.1 h.2) else 0
  let M := L.toFinset.sup kill
  have hbound (u : ℕ) (hL : u ∈ L) : kill u ≤ M :=
    Finset.le_sup (by simpa only [List.mem_toFinset] using hL)
  have hkill (u : ℕ) (hL : u ∈ L) (hne : u ≠ good) : EmptyExtension T u (kill u) := by
    dsimp only [kill]
    split
    · exact Nat.find_spec (dies u hL hne)
    · next h => exact False.elim (h ⟨hL, hne⟩)
  let m := n + 1 + M
  have hall (u : ℕ) (hmem : u ∈ survivors T n m) : u = good := by
    obtain ⟨v, hvT, hv, hvl, he⟩ := (survivors_spec T n m u (by dsimp [m]; omega)).mp hmem
    have huvalid : ValidCode u := by rw [← he]; exact take_valid _ _ hv
    have hulen : wordLength u = n + 1 := by
      rw [← he, (take_spec _ _ hv).1, hvl, min_eq_left (by dsimp [m]; omega)]
    have hL : u ∈ L := (binary_level_spec _ _).mpr ⟨huvalid, hulen⟩
    by_contra hne
    have hempty : EmptyExtension T u M := by
      convert empty_extension_persists T hT u (kill u) (M - kill u) (hkill u hL hne) using 1
      exact (Nat.add_sub_of_le (hbound u hL)).symm
    apply (empty_extension_spec T hT u M).mp hempty
    refine ⟨v, hvT, ?_, ?_⟩
    · rw [hulen]
      exact hvl
    · simpa only [he] using (take_spec (n + 1) v hv).2
  have hgood : good ∈ survivors T n m := survivor_path_prefix T X hX n m (by dsimp [m]; omega)
  have hnodup : (survivors T n m).Nodup := erase_dups_nodup _
  refine ⟨m, by dsimp [m]; omega, ?_⟩
  cases hs : survivors T n m with
  | nil => simp only [hs, List.not_mem_nil] at hgood
  | cons a l =>
    have ha : a = good := hall a (by simp only [hs, List.mem_cons, true_or])
    have hn : a ∉ l := (List.nodup_cons.mp (by simpa only [hs] using hnodup)).1
    cases l with
    | nil => exact congrArg (fun v => [v]) ha
    | cons b bs =>
      have hb : b = good := hall b (by simp [hs])
      exact False.elim (hn (by simp only [List.mem_cons]; exact Or.inl (ha.trans hb.symm)))

def uniqueSearch (T : Set ℕ) (n : ℕ) : Part ℕ := by
  classical
  exact (Nat.rfind fun k => Part.some
    (decide ((survivors T n (n + 1 + k)).length = 1))).map
      (fun k => wordBit ((survivors T n (n + 1 + k)).headD 0) n)

theorem unique_search_recursive (T : Set ℕ)
    (hc : ComputablePred (fun u => u ∈ T)) : Nat.Partrec (uniqueSearch T) := by
  classical
  have hl : Computable (fun p : ℕ × ℕ => survivors T p.1 (p.1 + 1 + p.2)) :=
    (survivors_computable T hc).comp Computable.fst
      (Primrec.nat_add.to_comp.comp (Computable.succ.comp Computable.fst) Computable.snd)
  have ht : Computable₂ (fun n k => decide ((survivors T n (n + 1 + k)).length = 1)) :=
    (Primrec.eq.decide.to_comp.comp (Computable.list_length.comp hl) (Computable.const 1)).to₂
  have hhead := Primrec.option_getD.to_comp.comp (Primrec.list_head?.to_comp.comp hl)
    (Computable.const 0)
  have hhd : Computable (fun p : ℕ × ℕ => (survivors T p.1 (p.1 + 1 + p.2)).headD 0) :=
    hhead.of_eq (fun _ => by simp only [List.headD_eq_head?_getD])
  have hv : Computable₂ (fun n k => wordBit ((survivors T n (n + 1 + k)).headD 0) n) :=
    (beta_primitive.to_comp.comp hhd Computable.fst).to₂
  have hh := (Partrec.rfind ht.partrec₂).map hv
  apply Partrec.nat_iff.mp
  apply hh.of_eq
  intro n
  have he : (↑(fun k => decide ((survivors T n (n + 1 + k)).length = 1)) : ℕ →. Bool) =
      (fun k => Part.some (decide ((survivors T n (n + 1 + k)).length = 1))) :=
    funext (PFun.coe_val _)
  simp only [uniqueSearch, he]

theorem unique_search_correct (T : Set ℕ) (hT : IsBinaryTree T) (X : Set ℕ)
    (hX : Path T X) (hu : ∀ Y, Path T Y → Y = X) (n : ℕ) :
    uniqueSearch T n = Part.some (indicator (fun q => q ∈ X) n) := by
  classical
  let Q (k : ℕ) := (survivors T n (n + 1 + k)).length = 1
  obtain ⟨m, hmn, hm⟩ := unique_survivor T hT X hX hu n
  have hex : ∃ k, Q k := by
    refine ⟨m - (n + 1), ?_⟩
    have he : n + 1 + (m - (n + 1)) = m := Nat.add_sub_of_le hmn
    dsimp only [Q]
    rw [he, hm]
    rfl
  let k := Nat.find hex
  have hk : k ∈ Nat.rfind (fun j => Part.some (decide (Q j))) := by
    apply Nat.mem_rfind.mpr
    exact ⟨by simpa using Nat.find_spec hex,
      fun {j} hj => by simpa using Nat.find_min hex hj⟩
  have hlen : (survivors T n (n + 1 + k)).length = 1 := Nat.find_spec hex
  obtain ⟨u, huword⟩ := List.length_eq_one_iff.mp hlen
  have hgood := survivor_path_prefix T X hX n (n + 1 + k) (by omega)
  rw [huword] at hgood
  have heq : u = prefixCode X (n + 1) := (List.mem_singleton.mp hgood).symm
  have hout : wordBit ((survivors T n (n + 1 + k)).headD 0) n =
      indicator (fun q => q ∈ X) n := by
    rw [huword, heq]
    exact (prefixCode_spec X (n + 1)).2 n (by omega)
  apply Part.eq_some_iff.mpr
  exact (Part.mem_map_iff _).mpr ⟨k, hk, hout⟩

theorem unique_path_computable (T : Set ℕ) (hT : IsBinaryTree T)
    (hc : ComputablePred (fun u => u ∈ T)) (X : Set ℕ)
    (hX : Path T X) (hu : ∀ Y, Path T Y → Y = X) :
    Computable (indicator (fun q => q ∈ X)) ∧
      ComputablePred (fun q => q ∈ X) ∧
      ∀ n, uniqueSearch T n = Part.some (indicator (fun q => q ∈ X) n) := by
  have hχ : Computable (indicator (fun q => q ∈ X)) :=
    (Partrec.nat_iff.mpr (unique_search_recursive T hc)).of_eq_tot (fun n => by
      rw [unique_search_correct T hT X hX hu n]
      exact Part.mem_some _)
  exact ⟨hχ, (decidable_iff_characteristic _).mpr ⟨_, hχ, fun _ => rfl⟩,
    unique_search_correct T hT X hX hu⟩

end
end Lemmatheca.ComputabilityTheory.ComputableTreesAndPaths
