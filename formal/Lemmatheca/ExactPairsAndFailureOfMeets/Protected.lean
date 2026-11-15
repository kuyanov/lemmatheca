import Lemmatheca.ExactPairsAndFailureOfMeets.Support

/-! Protected finite words anchored separately at their original seeds. -/
namespace Lemmatheca.ComputabilityTheory.ExactPairs

open OracleComputation OracleProgramNumberings UniversalComputation IncomparableTuringDegrees

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section
local instance exactPairsProtectedDecidable : DecidablePred (fun p : Prop => p) :=
  Classical.propDecidable

def ProtectedExtension (A : ℕ → Set ℕ) (s u v : ℕ) : Prop :=
  Prefix u v ∧ ∀ q, wordLength u ≤ q → q < wordLength v → q.unpair.1 < s →
    wordBit v q = indicator (fun x => x ∈ A q.unpair.1) q.unpair.2

def ProtectedCompletion (A : ℕ → Set ℕ) (s u : ℕ) (X : Set ℕ) : Prop :=
  Realizes u X ∧ ∀ q, wordLength u ≤ q → q.unpair.1 < s →
    indicator (fun x => x ∈ X) q = indicator (fun x => x ∈ A q.unpair.1) q.unpair.2

def paddedBit (A : ℕ → Set ℕ) (s u q : ℕ) : ℕ :=
  if q < wordLength u then wordBit u q else
    if q.unpair.1 < s then indicator (fun x => x ∈ A q.unpair.1) q.unpair.2 else 0

def pad (A : ℕ → Set ℕ) (s u m : ℕ) : ℕ :=
  FiniteSequenceCoding.code ((List.range (max (wordLength u) m)).map (paddedBit A s u))

def completionSet (A : ℕ → Set ℕ) (s u : ℕ) : Set ℕ :=
  {q | paddedBit A s u q = 1}

theorem protected_refl (A : ℕ → Set ℕ) (s u : ℕ) : ProtectedExtension A s u u := by
  exact ⟨prefix_refl u, fun q hq hq' _ => by omega⟩

theorem protected_trans (A : ℕ → Set ℕ) {s t u v w : ℕ}
    (huv : ProtectedExtension A s u v) (hvw : ProtectedExtension A t v w) (hst : s ≤ t) :
    ProtectedExtension A s u w := by
  refine ⟨prefix_trans huv.1 hvw.1, ?_⟩
  intro q hqu hqw hqs
  by_cases hqv : q < wordLength v
  · rw [← hvw.1.2 q hqv]
    exact huv.2 q hqu hqv hqs
  · exact hvw.2 q (by omega) hqw (lt_of_lt_of_le hqs hst)

theorem protected_completion_of_extension (A : ℕ → Set ℕ) {s t u v : ℕ} {X : Set ℕ}
    (huv : ProtectedExtension A s u v) (hX : ProtectedCompletion A t v X) (hst : s ≤ t) :
    ProtectedCompletion A s u X := by
  refine ⟨realizes_prefix huv.1 hX.1, ?_⟩
  intro q hqu hqs
  by_cases hqv : q < wordLength v
  · rw [← hX.1 q hqv]
    exact huv.2 q hqu hqv hqs
  · exact hX.2 q (by omega) (lt_of_lt_of_le hqs hst)

theorem protected_prefix (A : ℕ → Set ℕ) (s u w : ℕ) (X : Set ℕ)
    (hX : ProtectedCompletion A s u X) (huw : Prefix u w) (hwX : Realizes w X) :
    ProtectedExtension A s u w := by
  exact ⟨huw, fun q hqu hqw hqs => (hwX q hqw).trans (hX.2 q hqu hqs)⟩

private theorem padded_bit_binary (A : ℕ → Set ℕ) (s u q : ℕ) :
    paddedBit A s u q = 0 ∨ paddedBit A s u q = 1 := by
  by_cases hu : q < wordLength u
  · simpa [paddedBit, hu] using PostsTheorem.beta_bits u q
  · by_cases hi : q.unpair.1 < s
    · by_cases ha : q.unpair.2 ∈ A q.unpair.1 <;> simp [paddedBit, hu, hi, indicator, ha]
    · simp [paddedBit, hu, hi]

private theorem completion_indicator (A : ℕ → Set ℕ) (s u q : ℕ) :
    indicator (fun x => x ∈ completionSet A s u) q = paddedBit A s u q := by
  rcases padded_bit_binary A s u q with h | h <;> simp [indicator, completionSet, h]

theorem pad_spec (A : ℕ → Set ℕ) (s u m : ℕ) :
    wordLength (pad A s u m) = max (wordLength u) m ∧
      ProtectedExtension A s u (pad A s u m) ∧
      ∀ q < wordLength (pad A s u m), wordBit (pad A s u m) q = paddedBit A s u q := by
  have hlen : wordLength (pad A s u m) = max (wordLength u) m := by
    simp [pad, wordLength, FiniteSequenceCoding.length]
  have hb (q : ℕ) (hq : q < max (wordLength u) m) :
      wordBit (pad A s u m) q = paddedBit A s u q := by
    have he : FiniteSequenceCoding.entry (pad A s u m) q = paddedBit A s u q := by
      simp [pad, FiniteSequenceCoding.entry, List.getElem?_range hq]
    change FiniteSequenceCoding.entry (pad A s u m) q % 2 = _
    rw [he]
    rcases padded_bit_binary A s u q with h | h <;> simp [h]
  refine ⟨hlen, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [hlen]; exact le_max_left _ _
  · intro q hq
    rw [hb q (lt_of_lt_of_le hq (le_max_left _ _))]
    simp [paddedBit, hq]
  · intro q hqu hqm hqs
    rw [hb q (hlen ▸ hqm)]
    simp [paddedBit, Nat.not_lt.mpr hqu, hqs]
  · intro q hq
    exact hb q (hlen ▸ hq)

theorem completion_set_spec (A : ℕ → Set ℕ) (s u : ℕ) :
    ProtectedCompletion A s u (completionSet A s u) := by
  constructor
  · intro q hq
    rw [completion_indicator]
    simp [paddedBit, hq]
  · intro q hqu hqs
    rw [completion_indicator]
    simp [paddedBit, Nat.not_lt.mpr hqu, hqs]

def DisagreementCandidate (A : ℕ → Set ℕ) (s e f u v t : ℕ) : Prop :=
  let x := t.unpair.1
  let a := t.unpair.2.unpair.1
  let b := t.unpair.2.unpair.2
  ProtectedExtension A s u a ∧ ProtectedExtension A s v b ∧
    0 < certificateValue a e x ∧ 0 < certificateValue b f x ∧
    certificateValue a e x ≠ certificateValue b f x

def HasDisagreement (A : ℕ → Set ℕ) (s e f u v : ℕ) : Prop :=
  ∃ t, DisagreementCandidate A s e f u v t

def selected (A : ℕ → Set ℕ) (s e f u v : ℕ) : ℕ :=
  if h : HasDisagreement A s e f u v then Nat.find h else 0

theorem selected_spec (A : ℕ → Set ℕ) (s e f u v : ℕ)
    (h : HasDisagreement A s e f u v) :
    DisagreementCandidate A s e f u v (selected A s e f u v) ∧
      ∀ t < selected A s e f u v, ¬ DisagreementCandidate A s e f u v t := by
  simpa only [selected, dite_eq_left h] using
    (show DisagreementCandidate A s e f u v (Nat.find h) ∧
      ∀ t < Nat.find h, ¬ DisagreementCandidate A s e f u v t from
        ⟨Nat.find_spec h, fun _ ht => Nat.find_min h ht⟩)

theorem disagreement_excludes_common (A : ℕ → Set ℕ) (s e f u v t : ℕ) (X Y : Set ℕ)
    (ht : DisagreementCandidate A s e f u v t)
    (hX : Realizes t.unpair.2.unpair.1 X) (hY : Realizes t.unpair.2.unpair.2 Y) :
    ¬ ∃ g : ℕ → ℕ, (∀ x, phi X e x = Part.some (g x)) ∧
      (∀ x, phi Y f x = Part.some (g x)) := by
  rintro ⟨g,he,hf⟩
  obtain ⟨_,_,ha,hb,hn⟩ := ht
  let x := t.unpair.1
  let a := t.unpair.2.unpair.1
  let b := t.unpair.2.unpair.2
  let y := certificateValue a e x - 1
  let z := certificateValue b f x - 1
  have hy : certificateValue a e x = y + 1 := by dsimp [y,a,x]; omega
  have hz : certificateValue b f x = z + 1 := by dsimp [z,b,x]; omega
  have hy' : y = g x := Part.mem_unique (certificate_sound X a e x y hX hy)
    (by rw [he]; exact Part.mem_some _)
  have hz' : z = g x := Part.mem_unique (certificate_sound Y b f x z hY hz)
    (by rw [hf]; exact Part.mem_some _)
  exact hn (by change certificateValue a e x = certificateValue b f x; omega)

end
end Lemmatheca.ComputabilityTheory.ExactPairs
