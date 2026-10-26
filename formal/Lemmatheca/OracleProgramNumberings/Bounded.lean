import Lemmatheca.OracleProgramNumberings.Coding

/-! Actual bounded query evaluation and its coded finite-table construction. -/
namespace Lemmatheca.ComputabilityTheory.OracleProgramNumberings

open OracleComputation
namespace FSC
export FiniteSequenceCoding (code cons append entry)
end FSC

def boundedQ (q : ℕ → ℕ) : ℕ → Code → ℕ → Option ℕ
  | 0, _, _ => none
  | k + 1, c, x =>
      if x ≤ k then
        match c with
        | .zero => some 0
        | .succ => some (x + 1)
        | .left => some x.unpair.1
        | .right => some x.unpair.2
        | .query => some (q x)
        | .pair c d => do
            let u ← boundedQ q (k + 1) c x
            let v ← boundedQ q (k + 1) d x
            pure (Nat.pair u v)
        | .comp c d => do
            let v ← boundedQ q (k + 1) d x
            boundedQ q (k + 1) c v
        | .prec c d =>
            match x.unpair.2 with
            | 0 => boundedQ q (k + 1) c x.unpair.1
            | n + 1 => do
                let v ← boundedQ q k (.prec c d) (Nat.pair x.unpair.1 n)
                boundedQ q (k + 1) d (Nat.pair x.unpair.1 (Nat.pair n v))
        | .find' c => do
            let v ← boundedQ q (k + 1) c x
            if v = 0 then pure x.unpair.2
            else boundedQ q k (.find' c) (Nat.pair x.unpair.1 (x.unpair.2 + 1))
      else none
termination_by k c _ => (k, sizeOf c)

noncomputable def bounded (A : Set ℕ) :=
  boundedQ (UniversalComputation.indicator (fun x => x ∈ A))

def optionNumber (v : Option ℕ) : ℕ := v.elim 0 Nat.succ

noncomputable def boundedValue (A : Set ℕ) (k e x : ℕ) : ℕ :=
  optionNumber (bounded A k (decodeCode e) x)

def tableLookup (table allowance p x : ℕ) : ℕ :=
  if x < allowance then FSC.entry (FSC.entry table p) x else 0

def tableEntry (q : ℕ → ℕ) (old current k p x : ℕ) : ℕ :=
  match p with
  | 0 => 1
  | 1 => x + 2
  | 2 => x.unpair.1 + 1
  | 3 => x.unpair.2 + 1
  | 4 => q x + 1
  | n + 5 =>
      let m := n / 4
      let a := m.unpair.1
      let b := m.unpair.2
      match n % 4 with
      | 0 =>
          let u := tableLookup current (k + 1) a x
          let v := tableLookup current (k + 1) b x
          if u = 0 ∨ v = 0 then 0 else Nat.pair (u - 1) (v - 1) + 1
      | 1 =>
          match x.unpair.2 with
          | 0 => tableLookup current (k + 1) a x.unpair.1
          | j + 1 =>
              let v := tableLookup old k p (Nat.pair x.unpair.1 j)
              if v = 0 then 0
              else tableLookup current (k + 1) b
                (Nat.pair x.unpair.1 (Nat.pair j (v - 1)))
      | 2 =>
          let v := tableLookup current (k + 1) b x
          if v = 0 then 0 else tableLookup current (k + 1) a (v - 1)
      | _ =>
          let v := tableLookup current (k + 1) m x
          if v = 0 then 0
          else if v = 1 then x.unpair.2 + 1
          else tableLookup old k p (Nat.pair x.unpair.1 (x.unpair.2 + 1))

def buildRow (q : ℕ → ℕ) (old current k p : ℕ) : ℕ → ℕ
  | 0 => 0
  | x + 1 => FSC.append (buildRow q old current k p x)
      (FSC.cons (tableEntry q old current k p x) 0)

def buildRows (q : ℕ → ℕ) (old k : ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 =>
      let current := buildRows q old k p
      FSC.append current (FSC.cons (buildRow q old current k p (k + 1)) 0)

def finiteTable (q : ℕ → ℕ) (e : ℕ) : ℕ → ℕ
  | 0 => FSC.code (List.replicate (e + 1) 0)
  | k + 1 => buildRows q (finiteTable q e k) k (e + 1)

def tableValue (q : ℕ → ℕ) (k e x : ℕ) : ℕ :=
  tableLookup (finiteTable q e k) k e x

theorem bounded_input_bound {q : ℕ → ℕ} {k : ℕ} {c : Code} {x y : ℕ}
    (h : y ∈ boundedQ q k c x) : x < k := by
  cases k with
  | zero => simp [boundedQ] at h
  | succ k =>
      by_cases hx : x ≤ k
      · omega
      · cases c <;> simp [boundedQ, hx] at h



private theorem bounded_mono_le (q : ℕ → ℕ) (k : ℕ) :
    ∀ (l : ℕ) (c : Code) (x y : ℕ), k ≤ l →
      boundedQ q k c x = some y → boundedQ q l c x = some y := by
  induction k with
  | zero => intro l c x y hkl h; simp [boundedQ] at h
  | succ k ih =>
      intro l c x y hkl h
      cases l with
      | zero => omega
      | succ l =>
          have hle : k ≤ l := by omega
          induction c generalizing x y
          all_goals
              have hx : x ≤ k := Nat.le_of_lt_succ (bounded_input_bound h)
              have hlx : x ≤ l := le_trans hx hle
              rw [boundedQ, ite_eq_left hx] at h
              rw [boundedQ, ite_eq_left hlx]
          case zero | succ | left | right | query => exact h
          case pair c d ihc ihd =>
            simp only [bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h ⊢
            obtain ⟨u, hu, v, hv, hvy⟩ := h
            exact ⟨u, ihc x u hu, v, ihd x v hv, hvy⟩
          case comp c d ihc ihd =>
            simp only [bind, Option.bind_eq_some_iff] at h ⊢
            obtain ⟨v, hv, hy⟩ := h
            exact ⟨v, ihd x v hv, ihc v y hy⟩
          case prec c d ihc ihd =>
            cases hn : x.unpair.2 with
            | zero =>
                simp only [hn] at h ⊢
                exact ihc x.unpair.1 y h
            | succ n =>
                simp only [hn, bind, Option.bind_eq_some_iff] at h ⊢
                obtain ⟨v, hv, hy⟩ := h
                exact ⟨v, ih l (.prec c d) _ v hle hv, ihd _ y hy⟩
          case find' c ihc =>
            simp only [bind, Option.bind_eq_some_iff] at h ⊢
            obtain ⟨v, hv, hy⟩ := h
            refine ⟨v, ihc x v hv, ?_⟩
            by_cases hz : v = 0
            · simpa only [hz, ite_eq_left] using hy
            · simp only [ite_eq_right hz] at hy ⊢
              exact ih l (.find' c) _ y hle hy

theorem bounded_sound (A : Set ℕ) (k : ℕ) (c : Code) (x y : ℕ)
    (h : y ∈ bounded A k c x) : y ∈ eval A c x := by
  change boundedQ (UniversalComputation.indicator (fun x => x ∈ A)) k c x = some y at h
  induction k generalizing c x y with
  | zero => simp [boundedQ] at h
  | succ k ih =>
      induction c generalizing x y
      all_goals
        have hx : x ≤ k := Nat.le_of_lt_succ (bounded_input_bound h)
        rw [boundedQ, ite_eq_left hx] at h
      case zero | succ | left | right | query =>
        simpa only [eval, Part.mem_some_iff] using (Option.some.inj h).symm
      case pair c d ihc ihd =>
        simp only [bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
        obtain ⟨u, hu, v, hv, hvy⟩ := h
        rw [eval_pair]
        exact ⟨u, v, ihc x u hu, ihd x v hv, hvy.symm⟩
      case comp c d ihc ihd =>
        simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨v, hv, hy⟩ := h
        exact (eval_comp A c d x y).mpr ⟨v, ihd x v hv, ihc v y hy⟩
      case prec c d ihc ihd =>
        rw [← Nat.pair_unpair x]
        cases hn : x.unpair.2 with
        | zero =>
            simp only [hn] at h
            rw [eval_prec_zero]
            exact ihc _ _ h
        | succ n =>
            simp only [hn, bind, Option.bind_eq_some_iff] at h
            obtain ⟨v, hv, hy⟩ := h
            rw [eval_prec_succ, Part.mem_bind_iff]
            exact ⟨v, ih (.prec c d) _ _ hv, ihd _ _ hy⟩
      case find' c ihc =>
        simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨v, hv, hy⟩ := h
        have hv' := ihc x v hv
        rw [← Nat.pair_unpair x, eval_find]
        by_cases hz : v = 0
        · simp only [hz, ite_eq_left, Option.pure_def, Option.some.injEq] at hy
          subst y
          refine ⟨le_rfl, ?_, fun i hlo hhi => by omega⟩
          simpa only [hz, Nat.pair_unpair] using hv'
        · simp only [ite_eq_right hz] at hy
          have hs := ih (.find' c) _ _ hy
          rw [eval_find] at hs
          refine ⟨by omega, hs.2.1, ?_⟩
          intro i hlo hhi
          by_cases hi : i = x.unpair.2
          · subst i
            exact ⟨v, by simpa only [Nat.pair_unpair] using hv', Nat.pos_of_ne_zero hz⟩
          · exact hs.2.2 i (by omega) hhi


theorem bounded_monotone (q : ℕ → ℕ) (k j : ℕ) (c : Code) (x y : ℕ)
    (h : boundedQ q k c x = some y) : boundedQ q (k + j) c x = some y := by
  exact bounded_mono_le q k (k + j) c x y (Nat.le_add_right k j) h


private theorem bounded_consistent_append {A : Set ℕ} {σ τ : QueryRecord} :
    Consistent A (σ ++ τ) ↔ Consistent A σ ∧ Consistent A τ := by
  simp only [Consistent, List.mem_append]
  aesop

private theorem derives_bounded {c : Code} {x y : ℕ} {τ : QueryRecord}
    (h : Derives c x τ y) : ∀ A, Consistent A τ → ∃ k, bounded A k c x = some y := by
  induction h
  case zero x | succ x | left x | right x =>
    intro A hc
    exact ⟨x + 1, by simp [bounded, boundedQ]⟩
  case query x b hb =>
    intro A hc
    have hh := hc x b (by simp)
    exact ⟨x + 1, by simp [bounded, boundedQ, ← hh]⟩
  case pair c d x u v σ τ hc hd ihc ihd =>
    intro A hτ
    obtain ⟨k₁, hk₁⟩ := ihc A (bounded_consistent_append.mp hτ).1
    obtain ⟨k₂, hk₂⟩ := ihd A (bounded_consistent_append.mp hτ).2
    let K := k₁ + k₂ + x
    have h₁ := bounded_mono_le _ k₁ (K + 1) c x u (by dsimp [K]; omega) hk₁
    have h₂ := bounded_mono_le _ k₂ (K + 1) d x v (by dsimp [K]; omega) hk₂
    refine ⟨K + 1, ?_⟩
    rw [bounded, boundedQ, ite_eq_left (by dsimp [K]; omega)]
    simp only [h₁, h₂, bind, Option.bind_some, Option.pure_def]
  case comp c d x v y σ τ hd hc ihd ihc =>
    intro A hτ
    obtain ⟨k₁, hk₁⟩ := ihd A (bounded_consistent_append.mp hτ).1
    obtain ⟨k₂, hk₂⟩ := ihc A (bounded_consistent_append.mp hτ).2
    let K := k₁ + k₂ + x
    have h₁ := bounded_mono_le _ k₁ (K + 1) d x v (by dsimp [K]; omega) hk₁
    have h₂ := bounded_mono_le _ k₂ (K + 1) c v y (by dsimp [K]; omega) hk₂
    refine ⟨K + 1, ?_⟩
    rw [bounded, boundedQ, ite_eq_left (by dsimp [K]; omega)]
    simp only [h₁, h₂, bind, Option.bind_some]
  case prec_zero c d a y τ hc ihc =>
    intro A hτ
    obtain ⟨k, hk⟩ := ihc A hτ
    let K := k + Nat.pair a 0
    have h₁ := bounded_mono_le _ k (K + 1) c a y (by dsimp [K]; omega) hk
    refine ⟨K + 1, ?_⟩
    rw [bounded, boundedQ, ite_eq_left (by dsimp [K]; omega)]
    simp only [Nat.unpair_pair, h₁]
  case prec_succ c d a n v y σ τ hc hd ihc ihd =>
    intro A hτ
    obtain ⟨k₁, hk₁⟩ := ihc A (bounded_consistent_append.mp hτ).1
    obtain ⟨k₂, hk₂⟩ := ihd A (bounded_consistent_append.mp hτ).2
    let K := k₁ + k₂ + Nat.pair a (n + 1)
    have h₁ := bounded_mono_le _ k₁ K (.prec c d) (Nat.pair a n) v
      (by dsimp [K]; omega) hk₁
    have h₂ := bounded_mono_le _ k₂ (K + 1) d (Nat.pair a (Nat.pair n v)) y
      (by dsimp [K]; omega) hk₂
    refine ⟨K + 1, ?_⟩
    rw [bounded, boundedQ, ite_eq_left (by dsimp [K]; omega)]
    simp only [Nat.unpair_pair, h₁, h₂, bind, Option.bind_some]
  case find_zero c a m τ hc ihc =>
    intro A hτ
    obtain ⟨k, hk⟩ := ihc A hτ
    let K := k + Nat.pair a m
    have h₁ := bounded_mono_le _ k (K + 1) c (Nat.pair a m) 0
      (by dsimp [K]; omega) hk
    refine ⟨K + 1, ?_⟩
    rw [bounded, boundedQ, ite_eq_left (by dsimp [K]; omega)]
    simp only [Nat.unpair_pair, h₁, bind, Option.bind_some, ite_true, Option.pure_def]
  case find_succ c a m v j σ τ hc hv hd ihc ihd =>
    intro A hτ
    obtain ⟨k₁, hk₁⟩ := ihc A (bounded_consistent_append.mp hτ).1
    obtain ⟨k₂, hk₂⟩ := ihd A (bounded_consistent_append.mp hτ).2
    let K := k₁ + k₂ + Nat.pair a m
    have h₁ := bounded_mono_le _ k₁ (K + 1) c (Nat.pair a m) v
      (by dsimp [K]; omega) hk₁
    have h₂ := bounded_mono_le _ k₂ K (.find' c) (Nat.pair a (m + 1)) j
      (by dsimp [K]; omega) hk₂
    refine ⟨K + 1, ?_⟩
    rw [bounded, boundedQ, ite_eq_left (by dsimp [K]; omega)]
    simp only [Nat.unpair_pair, h₁, h₂, bind, Option.bind_some,
      ite_eq_right (Nat.ne_of_gt hv)]

theorem bounded_complete (A : Set ℕ) (c : Code) (x y : ℕ) :
    y ∈ eval A c x ↔ ∃ k, bounded A k c x = some y := by
  constructor
  · intro h
    obtain ⟨τ, hd, hc⟩ := (trace_complete A c x y).mp h
    exact derives_bounded hd A hc
  · rintro ⟨k, hk⟩
    exact bounded_sound A k c x y hk


theorem boundedValue_output (A : Set ℕ) (k e x y : ℕ) :
    boundedValue A k e x = y + 1 ↔ bounded A k (decodeCode e) x = some y := by
  unfold boundedValue
  cases h : bounded A k (decodeCode e) x <;> simp [optionNumber]


private theorem decode_single (v : ℕ) :
    FiniteSequenceCoding.decode (FSC.cons v 0) = [v] := by
  have h0 : FiniteSequenceCoding.code [] = 0 := by simp [FiniteSequenceCoding.code]
  rw [← h0, ← FiniteSequenceCoding.code_cons v [], FiniteSequenceCoding.decode_code]

private theorem buildRow_list (q : ℕ → ℕ) (old current k p n : ℕ) :
    FiniteSequenceCoding.decode (buildRow q old current k p n) =
      (List.range n).map (tableEntry q old current k p) := by
  induction n with
  | zero => simp [buildRow]
  | succ n ih =>
      rw [buildRow, FiniteSequenceCoding.append, FiniteSequenceCoding.decode_code,
        ih, decode_single, List.range_succ, List.map_append]
      rfl

private theorem buildRows_length (q : ℕ → ℕ) (old k p : ℕ) :
    (FiniteSequenceCoding.decode (buildRows q old k p)).length = p := by
  induction p with
  | zero => simp [buildRows]
  | succ p ih =>
      simp only [buildRows, FiniteSequenceCoding.append, FiniteSequenceCoding.decode_code,
        decode_single, List.length_append, List.length_singleton, ih]

private theorem append_entry_before (s v j : ℕ)
    (hj : j < (FiniteSequenceCoding.decode s).length) :
    FSC.entry (FSC.append s (FSC.cons v 0)) j = FSC.entry s j := by
  simp only [FiniteSequenceCoding.entry, FiniteSequenceCoding.append,
    FiniteSequenceCoding.decode_code, decode_single, List.getElem?_append_left hj]

private theorem append_entry_last (s v j : ℕ)
    (hj : (FiniteSequenceCoding.decode s).length = j) :
    FSC.entry (FSC.append s (FSC.cons v 0)) j = v := by
  simp only [FiniteSequenceCoding.entry, FiniteSequenceCoding.append,
    FiniteSequenceCoding.decode_code, decode_single,
    List.getElem?_append_right (Nat.le_of_eq hj), hj, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

private theorem buildRow_entry (q : ℕ → ℕ) (old current k p n x : ℕ) (hx : x < n) :
    FSC.entry (buildRow q old current k p n) x = tableEntry q old current k p x := by
  simp only [FiniteSequenceCoding.entry, buildRow_list, List.getElem?_map,
    List.getElem?_range hx, Option.map_some, Option.getD_some]

private theorem buildRows_lookup_before (q : ℕ → ℕ) (old k p j x : ℕ) (hj : j < p) :
    tableLookup (buildRows q old k (p + 1)) (k + 1) j x =
      tableLookup (buildRows q old k p) (k + 1) j x := by
  unfold tableLookup
  rw [buildRows, append_entry_before _ _ j (by rw [buildRows_length]; exact hj)]

private theorem buildRows_lookup_last (q : ℕ → ℕ) (old k p x : ℕ) (hx : x < k + 1) :
    tableLookup (buildRows q old k (p + 1)) (k + 1) p x =
      tableEntry q old (buildRows q old k p) k p x := by
  rw [tableLookup, ite_eq_left hx, buildRows,
    append_entry_last _ _ p (buildRows_length q old k p), buildRow_entry _ _ _ _ _ _ _ hx]

private theorem bounded_outside (q : ℕ → ℕ) (k : ℕ) (c : Code) (x : ℕ) (hx : k ≤ x) :
    boundedQ q k c x = none := by
  cases h : boundedQ q k c x with
  | none => rfl
  | some y => have hb := bounded_input_bound h; omega

private theorem tableEntry_correct (q : ℕ → ℕ) (old current k p x : ℕ)
    (hold : ∀ u, tableLookup old k p u = optionNumber (boundedQ q k (decodeCode p) u))
    (hcurrent : ∀ r < p, ∀ u,
      tableLookup current (k + 1) r u = optionNumber (boundedQ q (k + 1) (decodeCode r) u))
    (hx : x ≤ k) :
    tableEntry q old current k p x = optionNumber (boundedQ q (k + 1) (decodeCode p) x) := by
  rcases p with _ | p
  · simp [tableEntry, decodeCode, boundedQ, hx, optionNumber]
  rcases p with _ | p
  · simp [tableEntry, decodeCode, boundedQ, hx, optionNumber]
  rcases p with _ | p
  · simp [tableEntry, decodeCode, boundedQ, hx, optionNumber]
  rcases p with _ | p
  · simp [tableEntry, decodeCode, boundedQ, hx, optionNumber]
  rcases p with _ | p
  · simp [tableEntry, decodeCode, boundedQ, hx, optionNumber]

  have hm : p / 4 < p + 5 := lt_of_le_of_lt (Nat.div_le_self p 4) (by omega)
  have h₁ : (p / 4).unpair.1 < p + 5 := lt_of_le_of_lt (p / 4).unpair_left_le hm
  have h₂ : (p / 4).unpair.2 < p + 5 := lt_of_le_of_lt (p / 4).unpair_right_le hm
  have hp := Nat.mod_lt p (by decide : 0 < 4)
  rw [tableEntry, decodeCode]
  interval_cases hh : p % 4
  · simp only
    rw [boundedQ, ite_eq_left hx, hcurrent _ h₁, hcurrent _ h₂]
    cases ha : boundedQ q (k + 1) (decodeCode (p / 4).unpair.1) x <;>
      cases hb : boundedQ q (k + 1) (decodeCode (p / 4).unpair.2) x <;>
      simp_all [optionNumber]
  · simp only
    rw [boundedQ, ite_eq_left hx]
    rw [decodeCode] at hold
    simp only [hh] at hold
    cases hn : x.unpair.2 with
    | zero => simp only [hcurrent _ h₁]
    | succ n =>
        simp only [hold]
        cases hv : boundedQ q k (.prec (decodeCode (p / 4).unpair.1)
          (decodeCode (p / 4).unpair.2)) (Nat.pair x.unpair.1 n) with
        | none => simp [optionNumber]
        | some v => simp [optionNumber, hcurrent _ h₂]
  · simp only
    rw [boundedQ, ite_eq_left hx, hcurrent _ h₂]
    cases hv : boundedQ q (k + 1) (decodeCode (p / 4).unpair.2) x with
    | none => simp [optionNumber]
    | some v => simp [optionNumber, hcurrent _ h₁]
  · simp only
    rw [boundedQ, ite_eq_left hx, hcurrent _ hm]
    rw [decodeCode] at hold
    simp only [hh] at hold
    cases hv : boundedQ q (k + 1) (decodeCode (p / 4)) x with
    | none => simp [optionNumber]
    | some v =>
        cases v with
        | zero => simp [optionNumber]
        | succ v => simp [optionNumber, hold]

theorem table_correct (q : ℕ → ℕ) (k e p x : ℕ) (hp : p ≤ e) :
    tableLookup (finiteTable q e k) k p x =
      optionNumber (boundedQ q k (decodeCode p) x) := by
  induction k generalizing e p x with
  | zero => simp [tableLookup, boundedQ, optionNumber]
  | succ k ih =>
      have hrows : ∀ r, r ≤ e + 1 → ∀ j, j < r → ∀ u,
          tableLookup (buildRows q (finiteTable q e k) k r) (k + 1) j u =
            optionNumber (boundedQ q (k + 1) (decodeCode j) u) := by
        intro r
        induction r with
        | zero => intro hr j hj u; omega
        | succ r ihr =>
            intro hr j hj u
            by_cases hjr : j < r
            · rw [buildRows_lookup_before q (finiteTable q e k) k r j u hjr]
              exact ihr (by omega) j hjr u
            · have heq : j = r := by omega
              subst j
              by_cases hu : u < k + 1
              · rw [buildRows_lookup_last q (finiteTable q e k) k r u hu]
                apply tableEntry_correct q (finiteTable q e k) (buildRows q (finiteTable q e k) k r)
                  k r u
                · intro v
                  exact ih e r v (by omega)
                · intro a ha v
                  exact ihr (by omega) a ha v
                · omega
              · rw [tableLookup, ite_eq_right hu,
                  bounded_outside q (k + 1) (decodeCode r) u (by omega)]
                rfl
      exact hrows (e + 1) le_rfl p (by omega) x


theorem tableValue_correct (A : Set ℕ) (k e x : ℕ) :
    tableValue (UniversalComputation.indicator (fun n => n ∈ A)) k e x =
      boundedValue A k e x := by
  exact table_correct (UniversalComputation.indicator (fun n => n ∈ A)) k e e x le_rfl


end Lemmatheca.ComputabilityTheory.OracleProgramNumberings
