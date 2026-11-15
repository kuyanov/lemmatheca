import Lemmatheca.ExactPairsAndFailureOfMeets.Search

/-! Actual protected-column stages and their two union sets. -/
namespace Lemmatheca.ComputabilityTheory.ExactPairs
open OracleComputation OracleProgramNumberings UniversalComputation IncomparableTuringDegrees
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
local instance exactPairsConstructionDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable

def settle (A : ℕ → Set ℕ) (s e f u v : ℕ) : ℕ × ℕ :=
  if HasDisagreement A s e f u v then
    (pad A s (selected A s e f u v).unpair.2.unpair.1 (s + 1),
      pad A s (selected A s e f u v).unpair.2.unpair.2 (s + 1))
  else (pad A s u (s + 1), pad A s v (s + 1))

def stage (A : ℕ → Set ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | s + 1 => settle A s s.unpair.1 s.unpair.2 (stage A s).1 (stage A s).2

def leftWord (A : ℕ → Set ℕ) (s : ℕ) : ℕ := (stage A s).1

def rightWord (A : ℕ → Set ℕ) (s : ℕ) : ℕ := (stage A s).2

def leftSet (A : ℕ → Set ℕ) : Set ℕ := unionSet (leftWord A)

def rightSet (A : ℕ → Set ℕ) : Set ℕ := unionSet (rightWord A)

theorem settle_growth (A : ℕ → Set ℕ) (s e f u v : ℕ) :
    ProtectedExtension A s u (settle A s e f u v).1 ∧
      ProtectedExtension A s v (settle A s e f u v).2 ∧
      s + 1 ≤ wordLength (settle A s e f u v).1 ∧
      s + 1 ≤ wordLength (settle A s e f u v).2 := by
  by_cases h : HasDisagreement A s e f u v
  · rw [settle, ite_eq_left h]
    obtain ⟨hu,hv,_,_,_⟩ := (selected_spec A s e f u v h).1
    have hp := pad_spec A s (selected A s e f u v).unpair.2.unpair.1 (s + 1)
    have hq := pad_spec A s (selected A s e f u v).unpair.2.unpair.2 (s + 1)
    exact ⟨protected_trans A hu hp.2.1 le_rfl, protected_trans A hv hq.2.1 le_rfl,
      by rw [hp.1]; exact le_max_right _ _, by rw [hq.1]; exact le_max_right _ _⟩
  · rw [settle, ite_eq_right h]
    have hp := pad_spec A s u (s + 1)
    have hq := pad_spec A s v (s + 1)
    exact ⟨hp.2.1, hq.2.1, by rw [hp.1]; exact le_max_right _ _,
      by rw [hq.1]; exact le_max_right _ _⟩

/-- Only protected completions are covered. -/
theorem settle_correct (A : ℕ → Set ℕ) (s e f u v : ℕ) (X Y : Set ℕ)
    (hX : ProtectedCompletion A s (settle A s e f u v).1 X)
    (hY : ProtectedCompletion A s (settle A s e f u v).2 Y)
    (g : ℕ → ℕ) (he : ∀ x, phi X e x = Part.some (g x))
    (hf : ∀ x, phi Y f x = Part.some (g x)) :
    ∀ x, eval (boundedJoin A s) (searchCode s e u) x = Part.some (g x) := by
  by_cases h : HasDisagreement A s e f u v
  · rw [settle, ite_eq_left h] at hX hY
    have hp := (pad_spec A s (selected A s e f u v).unpair.2.unpair.1 (s + 1)).2.1.1
    have hq := (pad_spec A s (selected A s e f u v).unpair.2.unpair.2 (s + 1)).2.1.1
    exact False.elim (disagreement_excludes_common A s e f u v _ X Y
      (selected_spec A s e f u v h).1 (realizes_prefix hp hX.1)
      (realizes_prefix hq hY.1) ⟨g,he,hf⟩)
  · rw [settle, ite_eq_right h] at hX hY
    exact no_disagreement_search A s e f u v X Y g h
      (protected_completion_of_extension A (pad_spec A s u (s + 1)).2.1 hX le_rfl)
      (protected_completion_of_extension A (pad_spec A s v (s + 1)).2.1 hY le_rfl) he hf

theorem stage_prefixes (A : ℕ → Set ℕ) (s : ℕ) :
    Prefix (leftWord A s) (leftWord A (s + 1)) ∧
      Prefix (rightWord A s) (rightWord A (s + 1)) := by
  have hg := settle_growth A s s.unpair.1 s.unpair.2 (stage A s).1 (stage A s).2
  exact ⟨hg.1.1,hg.2.1.1⟩

theorem stage_lengths (A : ℕ → Set ℕ) (s : ℕ) :
    s ≤ wordLength (leftWord A s) ∧ s ≤ wordLength (rightWord A s) := by
  cases s with
  | zero => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | succ s =>
      have hg := settle_growth A s s.unpair.1 s.unpair.2 (stage A s).1 (stage A s).2
      exact hg.2.2

theorem stage_realizes (A : ℕ → Set ℕ) (s : ℕ) :
    Realizes (leftWord A s) (leftSet A) ∧ Realizes (rightWord A s) (rightSet A) := by
  exact ⟨(coherent_union (leftWord A) (fun n => (stage_prefixes A n).1)
      (fun n => (stage_lengths A n).1)).1 s,
    (coherent_union (rightWord A) (fun n => (stage_prefixes A n).2)
      (fun n => (stage_lengths A n).2)).1 s⟩

theorem stage_protected (A : ℕ → Set ℕ) (s t : ℕ) (hst : s ≤ t) :
    ProtectedExtension A s (leftWord A s) (leftWord A t) ∧
      ProtectedExtension A s (rightWord A s) (rightWord A t) := by
  induction t, hst using Nat.le_induction with
  | base => exact ⟨protected_refl A s _,protected_refl A s _⟩
  | succ t hst ih =>
      have hg := settle_growth A t t.unpair.1 t.unpair.2 (stage A t).1 (stage A t).2
      exact ⟨protected_trans A ih.1 hg.1 hst, protected_trans A ih.2 hg.2.1 hst⟩

theorem union_protected (A : ℕ → Set ℕ) (s : ℕ) :
    ProtectedCompletion A s (leftWord A s) (leftSet A) ∧
      ProtectedCompletion A s (rightWord A s) (rightSet A) := by
  refine ⟨⟨(stage_realizes A s).1, ?_⟩, ⟨(stage_realizes A s).2, ?_⟩⟩
  · intro q hqu hqs
    let t := max s (q + 1)
    have hp := (stage_protected A s t (le_max_left _ _)).1
    have hlen := (stage_lengths A t).1
    have hqt : q < wordLength (leftWord A t) := by have := le_max_right s (q + 1); omega
    exact ((stage_realizes A t).1 q hqt).symm.trans (hp.2 q hqu hqt hqs)
  · intro q hqu hqs
    let t := max s (q + 1)
    have hp := (stage_protected A s t (le_max_left _ _)).2
    have hlen := (stage_lengths A t).2
    have hqt : q < wordLength (rightWord A t) := by have := le_max_right s (q + 1); omega
    exact ((stage_realizes A t).2 q hqt).symm.trans (hp.2 q hqu hqt hqs)

theorem column_agreement (A : ℕ → Set ℕ) (n : ℕ) :
    (∀ x, wordLength (leftWord A (n + 1)) ≤ x →
      indicator (fun x => x ∈ column (leftSet A) n) x = indicator (fun x => x ∈ A n) x) ∧
    (∀ x, wordLength (rightWord A (n + 1)) ≤ x →
      indicator (fun x => x ∈ column (rightSet A) n) x = indicator (fun x => x ∈ A n) x) := by
  have hp := union_protected A (n + 1)
  constructor
  · intro x hx
    have he := hp.1.2 (Nat.pair n x) (hx.trans (Nat.right_le_pair _ _)) (by simp)
    simpa [column, indicator, Nat.unpair_pair] using he
  · intro x hx
    have he := hp.2.2 (Nat.pair n x) (hx.trans (Nat.right_le_pair _ _)) (by simp)
    simpa [column, indicator, Nat.unpair_pair] using he

/-- Separate finite correction tables are retained on the two sides. -/
def leftRecoveryCode (A : ℕ → Set ℕ) (n : ℕ) : Code :=
  subst (columnCode n) (correctionCode (errorTable (A n) (wordLength (leftWord A (n + 1)))))

def rightRecoveryCode (A : ℕ → Set ℕ) (n : ℕ) : Code :=
  subst (columnCode n) (correctionCode (errorTable (A n) (wordLength (rightWord A (n + 1)))))

theorem column_recovery (A : ℕ → Set ℕ) (n : ℕ) :
    TuringDegrees.Reduces (leftRecoveryCode A n) (A n) (leftSet A) ∧
      TuringDegrees.Reduces (rightRecoveryCode A n) (A n) (rightSet A) := by
  have hp := column_agreement A n
  constructor
  · exact TuringDegrees.subst_reduces _ _
      (correction_reduces (A n) (column (leftSet A) n) _ (fun x hx => (hp.1 x hx).symm))
      (column_code_eval n (leftSet A))
  · exact TuringDegrees.subst_reduces _ _
      (correction_reduces (A n) (column (rightSet A) n) _ (fun x hx => (hp.2 x hx).symm))
      (column_code_eval n (rightSet A))

theorem constructed_common_output (A : ℕ → Set ℕ) (e f : ℕ) (g : ℕ → ℕ)
    (he : ∀ x, phi (leftSet A) e x = Part.some (g x))
    (hf : ∀ x, phi (rightSet A) f x = Part.some (g x)) :
    ∀ x, eval (boundedJoin A (Nat.pair e f))
      (searchCode (Nat.pair e f) e (leftWord A (Nat.pair e f))) x = Part.some (g x) := by
  let s := Nat.pair e f
  have hp := union_protected A (s + 1)
  have hX := protected_completion_of_extension A (protected_refl A s (leftWord A (s + 1)))
    hp.1 (Nat.le_succ s)
  have hY := protected_completion_of_extension A (protected_refl A s (rightWord A (s + 1)))
    hp.2 (Nat.le_succ s)
  have hX' : ProtectedCompletion A s
      (settle A s e f (leftWord A s) (rightWord A s)).1 (leftSet A) := by
    simpa only [leftWord,rightWord,stage,s,Nat.unpair_pair] using hX
  have hY' : ProtectedCompletion A s
      (settle A s e f (leftWord A s) (rightWord A s)).2 (rightSet A) := by
    simpa only [leftWord,rightWord,stage,s,Nat.unpair_pair] using hY
  exact settle_correct A s e f (leftWord A s) (rightWord A s)
    (leftSet A) (rightSet A) hX' hY' g he hf

theorem constructed_lower_bound (A : ℕ → Set ℕ) (D : Set ℕ)
    (he : TuringDegrees.Reducible D (leftSet A))
    (hf : TuringDegrees.Reducible D (rightSet A)) :
    ∃ e f, (∀ x, phi (leftSet A) e x = Part.some (indicator (fun x => x ∈ D) x)) ∧
      (∀ x, phi (rightSet A) f x = Part.some (indicator (fun x => x ∈ D) x)) ∧
      TuringDegrees.Reducible D (finiteJoin A (Nat.pair e f)) := by
  obtain ⟨c,hc⟩ := he
  obtain ⟨d,hd⟩ := hf
  let e := encodeCode c
  let f := encodeCode d
  have he' : ∀ x, phi (leftSet A) e x = Part.some (indicator (fun x => x ∈ D) x) := by
    simpa only [e,OracleProgramNumberings.phi,decode_encode,TuringDegrees.Reduces] using hc
  have hf' : ∀ x, phi (rightSet A) f x = Part.some (indicator (fun x => x ∈ D) x) := by
    simpa only [f,OracleProgramNumberings.phi,decode_encode,TuringDegrees.Reduces] using hd
  refine ⟨e,f,he',hf',?_⟩
  exact TuringDegrees.reducible_trans
    ⟨searchCode (Nat.pair e f) e (leftWord A (Nat.pair e f)),
      constructed_common_output A e f _ he' hf'⟩
    (finite_join_presentations A (Nat.pair e f)).1

theorem constructed_exact_pair (A : ℕ → Set ℕ)
    (h : ∀ n, TuringDegrees.Reducible (A n) (A (n + 1))) (D : Set ℕ) :
    TuringDegrees.Reducible D (leftSet A) ∧ TuringDegrees.Reducible D (rightSet A) ↔
      ∃ n, TuringDegrees.Reducible D (A n) := by
  constructor
  · rintro ⟨hb,hc⟩
    obtain ⟨e,f,_,_,hD⟩ := constructed_lower_bound A D hb hc
    exact ⟨Nat.pair e f - 1, TuringDegrees.reducible_trans hD
      (finite_join_chain_bound A h (Nat.pair e f)).1⟩
  · rintro ⟨n,hn⟩
    have hr := column_recovery A n
    exact ⟨TuringDegrees.reducible_trans hn ⟨leftRecoveryCode A n,hr.1⟩,
      TuringDegrees.reducible_trans hn ⟨rightRecoveryCode A n,hr.2⟩⟩
end
end Lemmatheca.ComputabilityTheory.ExactPairs
