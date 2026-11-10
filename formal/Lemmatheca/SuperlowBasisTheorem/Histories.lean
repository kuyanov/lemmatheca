import Lemmatheca.SuperlowBasisTheorem.Definitions

/-! Arbitrary answer-oracle histories for the unchanged low-basis program. -/
namespace Lemmatheca.ComputabilityTheory.SuperlowBasisTheorem

open UniversalComputation OracleComputation OracleProgramNumberings
open LowBasisTheorem StrongReductions Classical

noncomputable section
set_option backward.isDefEq.respectTransparency false

def answerHistory (δ : ℕ → ℕ) (C : Set ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => if δ (FiniteSequenceCoding.cons e (answerHistory δ C e)) ∈ C
      then answerHistory δ C e else FiniteSequenceCoding.cons e (answerHistory δ C e)

def answerBit (δ : ℕ → ℕ) (C : Set ℕ) (e : ℕ) : ℕ :=
  indicator C (δ (FiniteSequenceCoding.cons e (answerHistory δ C e)))

theorem halting_histories (δ : ℕ → ℕ) :
    answerHistory δ haltingDiagonal = history δ ∧
      answerBit δ haltingDiagonal = recordedBit δ := by
  have hh : answerHistory δ haltingDiagonal = history δ := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih => simp only [answerHistory, history, ih]
  refine ⟨hh, ?_⟩
  funext e
  simp only [answerBit, recordedBit, hh, Membership.mem, Set.Mem]

theorem history_code_all_oracles (δ : ℕ → ℕ) (hδ : Primrec δ) (C : Set ℕ) (e : ℕ) :
    eval C (historyCode δ hδ) e = Part.some (answerHistory δ C e) := by
  have hq (z : ℕ) : eval C (candidateCode δ hδ) z =
      Part.some (indicator C (candidateInput δ z)) := by
    simp only [candidateCode, eval, eval_embed, ordinaryCode_eval, Part.bind_some, Membership.mem, Set.Mem]
  have hs (i l : ℕ) : eval C (stepCode δ hδ) (Nat.pair i l) =
      Part.some (if δ (FiniteSequenceCoding.cons i l) ∈ C then l
        else FiniteSequenceCoding.cons i l) := by
    simp only [stepCode, eval, identity_eval, hq, Part.bind_some, Part.map_some,
      eval_embed, ordinaryCode_eval]
    simp [retainInput, candidateInput, indicator, Nat.unpair_pair, Membership.mem, Set.Mem]
  have hr (k : ℕ) : eval C
      (.prec .zero (.comp (stepCode δ hδ) .right)) (Nat.pair 0 k) =
      Part.some (answerHistory δ C k) := by
    induction k with
    | zero => simp [eval, answerHistory]
    | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_some]
      change (eval C .right (Nat.pair 0 (Nat.pair k (answerHistory δ C k)))).bind
        (eval C (stepCode δ hδ)) = _
      simp only [eval, Nat.unpair_pair, Part.bind_some]
      exact hs k (answerHistory δ C k)
  change (eval C (.pair .zero identityCode) e).bind
    (eval C (.prec .zero (.comp (stepCode δ hδ) .right))) = _
  have hp : eval C (.pair .zero identityCode) e = Part.some (Nat.pair 0 e) := by
    simp only [eval, identity_eval, Part.bind_some, Part.map_some]
  rw [hp, Part.bind_some]
  exact hr e

theorem jump_code_all_oracles (δ : ℕ → ℕ) (hδ : Primrec δ) (C : Set ℕ) (e : ℕ) :
    eval C (jumpCode δ hδ) e = Part.some (answerBit δ C e) := by
  have hp : eval C (.pair identityCode (historyCode δ hδ)) e =
      Part.some (Nat.pair e (answerHistory δ C e)) := by
    simp only [eval, identity_eval, history_code_all_oracles, Part.bind_some, Part.map_some]
  change (eval C (.pair identityCode (historyCode δ hδ)) e).bind
    (eval C (candidateCode δ hδ)) = _
  rw [hp, Part.bind_some]
  simp only [candidateCode, eval, eval_embed, ordinaryCode_eval, Part.bind_some]
  simp only [candidateInput, Nat.unpair_pair, answerBit, Membership.mem, Set.Mem]

theorem jump_code_total (δ : ℕ → ℕ) (hδ : Primrec δ) :
    AllOracleTotal (jumpCode δ hδ) := by
  intro C e
  rw [jump_code_all_oracles]
  trivial

def answerTrace (δ : ℕ → ℕ) (C : Set ℕ) (e : ℕ) : QueryRecord :=
  (List.range (e + 1)).map (fun i =>
    (δ (FiniteSequenceCoding.cons i (answerHistory δ C i)), answerBit δ C i))

private theorem trace_comp_inv {c d : Code} {x y : ℕ} {τ : QueryRecord}
    (h : Derives (.comp c d) x τ y) :
    ∃ v σ ρ, Derives d x σ v ∧ Derives c v ρ y ∧ τ = σ ++ ρ := by
  cases h with
  | comp hd hc => exact ⟨_, _, _, hd, hc, rfl⟩

private theorem trace_pair_inv {c d : Code} {x y : ℕ} {τ : QueryRecord}
    (h : Derives (.pair c d) x τ y) :
    ∃ u v σ ρ, Derives c x σ u ∧ Derives d x ρ v ∧
      y = Nat.pair u v ∧ τ = σ ++ ρ := by
  cases h with
  | pair hc hd => exact ⟨_, _, _, _, hc, hd, rfl, rfl⟩

private theorem trace_consistent_parts (C : Set ℕ) (σ ρ : QueryRecord) :
    Consistent C (σ ++ ρ) ↔ Consistent C σ ∧ Consistent C ρ := by
  simp only [Consistent, List.mem_append]
  aesop

private theorem trace_pure_value (c : Code) (d : Nat.Partrec.Code) (hcd : c = embed d)
    (x v y : ℕ) (τ : QueryRecord) (hv : eval ∅ c x = Part.some v)
    (hd : Derives c x τ y) : τ = [] ∧ y = v := by
  have ht : τ = [] := by rw [hcd] at hd; exact embed_record_empty hd
  have hy := trace_sound hd (show Consistent ∅ τ by rw [ht]; simp [Consistent])
  rw [hv] at hy
  exact ⟨ht, Part.mem_some_iff.mp hy⟩

private theorem trace_identity (x y : ℕ) (τ : QueryRecord)
    (hd : Derives identityCode x τ y) : τ = [] ∧ y = x := by
  exact trace_pure_value identityCode Nat.Partrec.Code.id rfl x x y τ (identity_eval ∅ x) hd

private theorem trace_ordinary (f : ℕ → ℕ) (hf : Nat.Primrec f) (x y : ℕ) (τ : QueryRecord)
    (hd : Derives (embed (ordinaryCode f hf)) x τ y) : τ = [] ∧ y = f x := by
  exact trace_pure_value _ _ rfl x (f x) y τ
    (by rw [eval_embed, ordinaryCode_eval]) hd

private theorem trace_candidate (δ : ℕ → ℕ) (hδ : Primrec δ) (C : Set ℕ)
    (x y : ℕ) (τ : QueryRecord) (hd : Derives (candidateCode δ hδ) x τ y)
    (hc : Consistent C τ) :
    τ = [(candidateInput δ x, indicator C (candidateInput δ x))] ∧
      y = indicator C (candidateInput δ x) := by
  obtain ⟨q, σ, ρ, hσ, hρ, ht⟩ := trace_comp_inv hd
  obtain ⟨hs, hq⟩ := trace_ordinary _ _ _ _ _ hσ
  have hp : ρ = [(q, y)] := by cases hρ; rfl
  have hτ : τ = [(candidateInput δ x, y)] := by rw [ht, hs, hp, hq]; rfl
  have hb : y = indicator C (candidateInput δ x) := by
    have := hc (candidateInput δ x) y (by rw [hτ]; simp)
    simpa only [Membership.mem, Set.Mem] using this
  exact ⟨by rw [hτ, hb], hb⟩

private theorem trace_step (δ : ℕ → ℕ) (hδ : Primrec δ) (C : Set ℕ)
    (i l y : ℕ) (τ : QueryRecord) (hd : Derives (stepCode δ hδ) (Nat.pair i l) τ y)
    (hc : Consistent C τ) :
    τ = [(δ (FiniteSequenceCoding.cons i l), indicator C (δ (FiniteSequenceCoding.cons i l)))] ∧
      y = if δ (FiniteSequenceCoding.cons i l) ∈ C then l else FiniteSequenceCoding.cons i l := by
  obtain ⟨w, σ, ρ, hσ, hρ, ht⟩ := trace_comp_inv hd
  obtain ⟨u, v, η, ζ, hη, hζ, hw, hs⟩ := trace_pair_inv hσ
  have hcs : Consistent C σ := (trace_consistent_parts C σ ρ).mp (by rw [← ht]; exact hc) |>.1
  have hcz : Consistent C ζ := (trace_consistent_parts C η ζ).mp (by rw [← hs]; exact hcs) |>.2
  obtain ⟨he, hu⟩ := trace_identity _ _ _ hη
  obtain ⟨hz, hv⟩ := trace_candidate δ hδ C _ _ _ hζ hcz
  obtain ⟨hr, hy⟩ := trace_ordinary _ _ _ _ _ hρ
  have hτ : τ = [(δ (FiniteSequenceCoding.cons i l), indicator C (δ (FiniteSequenceCoding.cons i l)))] := by
    simp only [ht, hs, he, hz, List.nil_append, hr, List.append_nil, candidateInput, Nat.unpair_pair]
  refine ⟨hτ, ?_⟩
  rw [hw, hu, hv] at hy
  by_cases hq : C (δ (FiniteSequenceCoding.cons i l))
  · simpa [retainInput, candidateInput, Nat.unpair_pair, indicator, Membership.mem, Set.Mem, hq] using hy
  · simpa [retainInput, candidateInput, Nat.unpair_pair, indicator, Membership.mem, Set.Mem, hq] using hy

private theorem trace_prec_zero (c d : Code) (a y : ℕ) (τ : QueryRecord)
    (h : Derives (.prec c d) (Nat.pair a 0) τ y) : Derives c a τ y := by
  generalize hx : Nat.pair a 0 = x at h
  cases h <;> simp only [Nat.pair_eq_pair] at hx
  · obtain ⟨rfl, _⟩ := hx; assumption
  · omega

private theorem trace_prec_succ (c d : Code) (a n y : ℕ) (τ : QueryRecord)
    (h : Derives (.prec c d) (Nat.pair a (n + 1)) τ y) :
    ∃ σ ρ v, Derives (.prec c d) (Nat.pair a n) σ v ∧
      Derives d (Nat.pair a (Nat.pair n v)) ρ y ∧ τ = σ ++ ρ := by
  generalize hx : Nat.pair a (n + 1) = x at h
  cases h <;> simp only [Nat.pair_eq_pair] at hx
  · omega
  · obtain ⟨rfl, hn⟩ := hx
    cases Nat.succ.inj hn
    exact ⟨_, _, _, by assumption, by assumption, rfl⟩

private def prefixTrace (δ : ℕ → ℕ) (C : Set ℕ) (n : ℕ) : QueryRecord :=
  (List.range n).map (fun i =>
    (δ (FiniteSequenceCoding.cons i (answerHistory δ C i)), answerBit δ C i))

private theorem trace_history_rec (δ : ℕ → ℕ) (hδ : Primrec δ) (C : Set ℕ)
    (n : ℕ) (τ : QueryRecord) (y : ℕ)
    (hd : Derives (.prec .zero (.comp (stepCode δ hδ) .right)) (Nat.pair 0 n) τ y)
    (hc : Consistent C τ) : τ = prefixTrace δ C n ∧ y = answerHistory δ C n := by
  induction n generalizing τ y with
  | zero =>
    have hz := trace_prec_zero _ _ _ _ _ hd
    cases hz
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨σ, ρ, v, hσ, hρ, ht⟩ := trace_prec_succ _ _ _ _ _ _ hd
    have hparts := (trace_consistent_parts C σ ρ).mp (by rw [← ht]; exact hc)
    obtain ⟨hs, hv⟩ := ih _ _ hσ hparts.1
    obtain ⟨w, η, ζ, hη, hζ, hr⟩ := trace_comp_inv hρ
    have he : η = [] ∧ w = Nat.pair n v := by cases hη; exact ⟨rfl, by simp⟩
    have hcz : Consistent C ζ := (trace_consistent_parts C η ζ).mp (by rw [← hr]; exact hparts.2) |>.2
    rw [he.2, hv] at hζ
    obtain ⟨hz, hy⟩ := trace_step δ hδ C _ _ _ _ hζ hcz
    refine ⟨?_, ?_⟩
    · simp only [ht, hs, hr, he.1, List.nil_append, hz, prefixTrace, List.range_succ,
        List.map_append, List.map_cons, List.map_nil, answerBit]
    · simpa only [answerHistory] using hy

private theorem trace_history (δ : ℕ → ℕ) (hδ : Primrec δ) (C : Set ℕ)
    (e y : ℕ) (τ : QueryRecord) (hd : Derives (historyCode δ hδ) e τ y)
    (hc : Consistent C τ) : τ = prefixTrace δ C e ∧ y = answerHistory δ C e := by
  obtain ⟨w, σ, ρ, hσ, hρ, ht⟩ := trace_comp_inv hd
  have he : σ = [] ∧ w = Nat.pair 0 e := by
    apply trace_pure_value _ (.pair .zero Nat.Partrec.Code.id) rfl e (Nat.pair 0 e) w σ _ hσ
    change eval ∅ (.pair .zero identityCode) e = Part.some (Nat.pair 0 e)
    simp only [eval, identity_eval, Part.bind_some, Part.map_some]
  have hcr : Consistent C ρ := (trace_consistent_parts C σ ρ).mp (by rw [← ht]; exact hc) |>.2
  rw [he.2] at hρ
  obtain ⟨hr, hy⟩ := trace_history_rec δ hδ C _ _ _ hρ hcr
  exact ⟨by rw [ht, he.1, List.nil_append, hr], hy⟩

private theorem trace_jump (δ : ℕ → ℕ) (hδ : Primrec δ) (C : Set ℕ)
    (e y : ℕ) (τ : QueryRecord) (hd : Derives (jumpCode δ hδ) e τ y)
    (hc : Consistent C τ) : τ = answerTrace δ C e ∧ y = answerBit δ C e := by
  obtain ⟨w, σ, ρ, hσ, hρ, ht⟩ := trace_comp_inv hd
  obtain ⟨u, v, η, ζ, hη, hζ, hw, hs⟩ := trace_pair_inv hσ
  have hparts := (trace_consistent_parts C σ ρ).mp (by rw [← ht]; exact hc)
  have hcz : Consistent C ζ := (trace_consistent_parts C η ζ).mp (by rw [← hs]; exact hparts.1) |>.2
  obtain ⟨he, hu⟩ := trace_identity _ _ _ hη
  obtain ⟨hz, hv⟩ := trace_history δ hδ C _ _ _ hζ hcz
  rw [hw, hu, hv] at hρ
  obtain ⟨hr, hy⟩ := trace_candidate δ hδ C _ _ _ hρ hparts.2
  refine ⟨?_, ?_⟩
  · simp only [ht, hs, he, hz, List.nil_append, hr, candidateInput, Nat.unpair_pair,
      answerTrace, prefixTrace, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, answerBit]
  · simpa only [candidateInput, Nat.unpair_pair, answerBit] using hy

theorem jump_code_trace (δ : ℕ → ℕ) (hδ : Primrec δ) (C : Set ℕ) (e : ℕ) :
    Derives (jumpCode δ hδ) e (answerTrace δ C e) (answerBit δ C e) ∧
      Consistent C (answerTrace δ C e) ∧ (answerTrace δ C e).length = e + 1 := by
  obtain ⟨τ, hd, hc⟩ := (trace_complete C (jumpCode δ hδ) e (answerBit δ C e)).mp
    (by rw [jump_code_all_oracles]; exact Part.mem_some _)
  obtain ⟨ht, _⟩ := trace_jump δ hδ C e _ τ hd hc
  subst τ
  exact ⟨hd, hc, by simp [answerTrace]⟩

theorem jump_trace_unique (δ : ℕ → ℕ) (hδ : Primrec δ) (C : Set ℕ) (e y : ℕ)
    (τ : QueryRecord) (hd : Derives (jumpCode δ hδ) e τ y) (hc : Consistent C τ) :
    τ = answerTrace δ C e ∧ y = answerBit δ C e := by
  exact trace_jump δ hδ C e y τ hd hc

def forcedHistory (η : List ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if η[i]?.getD 0 = 1 then forcedHistory η i
      else FiniteSequenceCoding.cons i (forcedHistory η i)

def answerWord (δ : ℕ → ℕ) (C : Set ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map (answerBit δ C)

theorem answer_word_spec (δ : ℕ → ℕ) (C : Set ℕ) (n : ℕ) :
    answerWord δ C n ∈ binaryRows n ∧
      ∀ i ≤ n, forcedHistory (answerWord δ C n) i = answerHistory δ C i := by
  have hd (i : ℕ) (hi : i < n) :
      (answerWord δ C n)[i]?.getD 0 = answerBit δ C i := by
    simp [answerWord, hi]
  constructor
  · apply (binaryRows_spec n).1 _ |>.mpr
    refine ⟨?_, by simp [answerWord]⟩
    intro b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
    exact indicator_bits C _
  · intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hin : i < n := by omega
      have hh := ih (by omega)
      simp only [forcedHistory, hd i hin, hh, answerBit]
      by_cases hq : δ (FiniteSequenceCoding.cons i (answerHistory δ C i)) ∈ C
      · simp only [Membership.mem, Set.Mem] at hq
        simp [answerHistory, indicator, Membership.mem, Set.Mem, hq]
      · simp only [Membership.mem, Set.Mem] at hq
        simp [answerHistory, indicator, Membership.mem, Set.Mem, hq]

theorem forced_history_primitive :
    Primrec (fun p : List ℕ × ℕ => forcedHistory p.1 p.2) := by
  let g : List ℕ → ℕ × ℕ → ℕ := fun η p =>
    if η[p.1]?.getD 0 = 1 then p.2 else FiniteSequenceCoding.cons p.1 p.2
  have hget : Primrec (fun p : List ℕ × (ℕ × ℕ) => p.1[p.2.1]?.getD 0) :=
    ((Primrec.list_getD 0).comp Primrec.fst (Primrec.fst.comp Primrec.snd)).of_eq
      (fun _ => rfl)
  have hg : Primrec₂ g :=
    Primrec.ite (Primrec.eq.comp hget (Primrec.const 1))
      (Primrec.snd.comp Primrec.snd)
      (FiniteSequenceCoding.primrec_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
  have hr := Primrec.nat_rec (Primrec.const 0) hg
  change Primrec₂ forcedHistory
  refine hr.of_eq ?_
  intro η n
  induction n with
  | zero => rfl
  | succ n ih => simp only [g, forcedHistory, ih]

end
end Lemmatheca.ComputabilityTheory.SuperlowBasisTheorem
