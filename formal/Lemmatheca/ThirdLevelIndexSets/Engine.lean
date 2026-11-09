import Lemmatheca.ThirdLevelIndexSets.Markers
import Lemmatheca.EffectiveEnumerations.Stages

/-! A finite ascending scan of genuinely fresh, cumulatively discovered events. -/
namespace Lemmatheca.ComputabilityTheory.ThirdLevelIndexSets

structure Schedule where
  event : ℕ → ℕ → ℕ → Bool
  label : ℕ → ℕ
  event_primitive : Primrec (fun p : (ℕ × ℕ) × ℕ => event p.1.1 p.1.2 p.2)
  label_primitive : Primrec label
  bounded : ∀ x s c, event x s c = true → c < s
  increasing : ∀ x s c, event x s c = true → event x (s+1) c = true

def fresh (σ : Schedule) (x s c : ℕ) : Bool :=
  σ.event x (s+1) c && !(σ.event x s c)

/-- Scan codes 0 through c-1, recomputing the current marker after every event. -/
def scan (σ : Schedule) (x s : ℕ) (B : List ℕ) : ℕ → List ℕ
  | 0 => B
  | c+1 => if fresh σ x s c then bump (scan σ x s B c) (σ.label c)
    else scan σ x s B c

def stages (σ : Schedule) (x : ℕ) : ℕ → List ℕ
  | 0 => []
  | s+1 => scan σ x s (stages σ x s) (s+1)

def output (σ : Schedule) (x : ℕ) : Set ℕ := {z | ∃ s, z ∈ stages σ x s}

def events (σ : Schedule) (x : ℕ) : Set ℕ := {c | ∃ s, σ.event x s c = true}

def lowEvents (σ : Schedule) (x n : ℕ) : Set ℕ :=
  {c | c ∈ events σ x ∧ σ.label c ≤ n}

def labelEvents (σ : Schedule) (x y : ℕ) : Set ℕ :=
  {c | c ∈ events σ x ∧ σ.label c = y}

private theorem event_monotone (σ : Schedule) (x c : ℕ) {s t : ℕ} (hst : s ≤ t)
    (h : σ.event x s c = true) : σ.event x t c = true := by
  induction hst with
  | refl => exact h
  | step ht ih => exact σ.increasing x _ c ih

private theorem scan_included_base (σ : Schedule) (x s : ℕ) (B : List ℕ) (c : ℕ) :
    Included B (scan σ x s B c) := by
  induction c with
  | zero => exact fun _ h => h
  | succ c ih =>
    simp only [scan]
    split
    · exact fun z hz => List.mem_cons_of_mem _ (ih z hz)
    · exact ih

private theorem scan_nodup (σ : Schedule) (x s : ℕ) (B : List ℕ) (hB : B.Nodup) (c : ℕ) :
    (scan σ x s B c).Nodup := by
  induction c with
  | zero => exact hB
  | succ c ih =>
    simp only [scan]
    split
    · exact bump_nodup _ ih _
    · exact ih

private theorem scan_prefix (σ : Schedule) (x s : ℕ) (B : List ℕ) (c n : ℕ)
    (h : ∀ d < c, fresh σ x s d = true → n < σ.label d) :
    ∀ i ≤ n, marker (scan σ x s B c) i = marker B i := by
  induction c with
  | zero => exact fun _ _ => rfl
  | succ c ih =>
    intro i hi
    have he := ih (fun d hd => h d (by omega)) i hi
    simp only [scan]
    split
    · rename_i hf
      rw [bump_prefix _ _ _ (by have := h c (by omega) hf; omega), he]
    · exact he

theorem fresh_primitive (σ : Schedule) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => fresh σ p.1.1 p.1.2 p.2) := by
  exact Primrec.and.comp
    (σ.event_primitive.comp (((Primrec.fst.comp Primrec.fst).pair
      (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd))
    (Primrec.not.comp σ.event_primitive)

theorem scan_primitive (σ : Schedule) :
    Primrec (fun p : ((ℕ × ℕ) × List ℕ) × ℕ =>
      scan σ p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  let step := fun (p : (ℕ × ℕ) × List ℕ) (q : ℕ × List ℕ) =>
    if fresh σ p.1.1 p.1.2 q.1 then bump q.2 (σ.label q.1) else q.2
  have hf : Primrec (fun p : ((ℕ × ℕ) × List ℕ) × (ℕ × List ℕ) =>
      fresh σ p.1.1.1 p.1.1.2 p.2.1) :=
    (fresh_primitive σ).comp (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.fst.comp Primrec.snd))
  have hs : Primrec₂ step := Primrec.ite
    (Primrec.eq.comp hf (Primrec.const true))
    (bump_primitive.comp (Primrec.snd.comp Primrec.snd)
      (σ.label_primitive.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd)
  exact (Primrec.nat_rec Primrec.snd hs).of_eq
    (g := fun p c => scan σ p.1.1 p.1.2 p.2 c) (fun p c => by
    induction c with
    | zero => rfl
    | succ c ih => simp only [step, scan, ih])

theorem stages_primitive (σ : Schedule) : Primrec₂ (stages σ) := by
  have hs : Primrec (fun p : ℕ × (ℕ × List ℕ) =>
      scan σ p.1 p.2.1 p.2.2 (p.2.1+1)) :=
    (scan_primitive σ).comp (((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)).pair
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
  exact (Primrec.nat_rec (Primrec.const ([] : List ℕ)) hs.to₂).of_eq (fun x s => by
    induction s with
    | zero => rfl
    | succ s ih => simp only [stages, ih])

/-- This is the precise numerical finite-list code used by the human algorithm. -/
def stageCode (σ : Schedule) (x s : ℕ) : ℕ :=
  FiniteSequenceCoding.code (stages σ x s)

theorem stageCode_primitive (σ : Schedule) : Primrec₂ (stageCode σ) := by
  exact Primrec.encode.comp (stages_primitive σ)

theorem stageCode_decode (σ : Schedule) (x s : ℕ) :
    FiniteSequenceCoding.decode (stageCode σ x s) = stages σ x s := by
  exact FiniteSequenceCoding.decode_code _

theorem stages_nodup (σ : Schedule) (x s : ℕ) : (stages σ x s).Nodup := by
  induction s with
  | zero => exact List.nodup_nil
  | succ s ih => exact scan_nodup σ x s _ ih _

theorem stages_included (σ : Schedule) (x : ℕ) :
    ∀ {s t}, s ≤ t → Included (stages σ x s) (stages σ x t) := by
  intro s t h
  induction h with
  | refl => exact fun _ h => h
  | step ht ih =>
    intro z hz
    exact scan_included_base σ x _ _ _ z (ih z hz)

theorem stage_test_primitive (σ : Schedule) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => (stages σ p.1.1 p.1.2).contains p.2) := by
  have hm : PrimrecRel (fun (B : List ℕ) z => z ∈ B) :=
    Primrec.eq.exists_mem_list.of_eq (by simp)
  have hc : Primrec₂ (fun (B : List ℕ) z => B.contains z) :=
    hm.decide.of_eq (fun B z => by simp)
  exact hc.comp ((stages_primitive σ).comp (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst)) Primrec.snd

theorem event_once (σ : Schedule) (x c : ℕ) :
    c ∈ events σ x ↔ ∃! s, fresh σ x s c = true := by
  have exists_fresh : ∀ t, σ.event x t c = true → ∃ s, fresh σ x s c = true := by
    intro t
    induction t with
    | zero => intro h; have := σ.bounded x 0 c h; omega
    | succ t ih =>
      intro ht
      by_cases ho : σ.event x t c = true
      · exact ih ho
      · exact ⟨t, by simp [fresh, ht, ho]⟩
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨s,hs⟩ := exists_fresh t ht
    refine ⟨s,hs,fun r hr => ?_⟩
    have hs' : σ.event x (s+1) c = true ∧ σ.event x s c = false := by simpa [fresh] using hs
    have hr' : σ.event x (r+1) c = true ∧ σ.event x r c = false := by simpa [fresh] using hr
    have hs1 := hs'.1
    have hs0 := hs'.2
    have hr1 := hr'.1
    have hr0 := hr'.2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hh := event_monotone σ x c (show r+1 ≤ s by omega) hr1
      simp [hh] at hs0
    · have hh := event_monotone σ x c (show s+1 ≤ r by omega) hs1
      simp [hh] at hr0
  · rintro ⟨s,hs,_⟩
    refine ⟨s+1, ?_⟩
    have : σ.event x (s+1) c = true ∧ σ.event x s c = false := by simpa [fresh] using hs
    exact this.1

theorem fresh_bound (σ : Schedule) (x s c : ℕ) (h : fresh σ x s c = true) :
    c ≤ s := by
  have he : σ.event x (s+1) c = true ∧ σ.event x s c = false := by simpa [fresh] using h
  have := σ.bounded x (s+1) c he.1
  omega

theorem stage_marker_monotone (σ : Schedule) (x n : ℕ) :
    Monotone (fun s => marker (stages σ x s) n) := by
  intro s t hst
  exact marker_monotone_of_included _ _ (stages_included σ x hst) n

private theorem finite_events_collected (σ : Schedule) (x : ℕ) (F : Set ℕ)
    (hF : F.Finite) (hsub : F ⊆ events σ x) :
    ∃ S, ∀ c ∈ F, σ.event x S c = true := by
  classical
  induction F, hF using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert c F hc hF ih =>
    obtain ⟨S,hS⟩ := ih (fun z hz => hsub (Set.mem_insert_of_mem _ hz))
    obtain ⟨t,ht⟩ := hsub (Set.mem_insert c F)
    refine ⟨max S t, ?_⟩
    intro z hz
    rcases hz with rfl | hz
    · exact event_monotone σ x z (le_max_right _ _) ht
    · exact event_monotone σ x z (le_max_left _ _) (hS z hz)

private theorem scan_included_steps (σ : Schedule) (x s : ℕ) (B : List ℕ)
    {c d : ℕ} (hcd : c ≤ d) : Included (scan σ x s B c) (scan σ x s B d) := by
  induction hcd with
  | refl => exact fun _ hz => hz
  | step hd ih =>
    intro z hz
    simp only [scan]
    split
    · exact List.mem_cons_of_mem _ (ih z hz)
    · exact ih z hz

theorem fresh_label_strict (σ : Schedule) (x s c : ℕ)
    (hf : fresh σ x s c = true) :
    marker (stages σ x s) (σ.label c) < marker (stages σ x (s+1)) (σ.label c) := by
  have hc := fresh_bound σ x s c hf
  have h0 := marker_monotone_of_included _ _ (scan_included_base σ x s (stages σ x s) c) (σ.label c)
  have h1 := bump_marker_strict (scan σ x s (stages σ x s) c) (σ.label c)
  have he : scan σ x s (stages σ x s) (c+1) =
      bump (scan σ x s (stages σ x s) c) (σ.label c) := by simp [scan,hf]
  have h2 := marker_monotone_of_included _ _
    (scan_included_steps σ x s (stages σ x s) (show c+1 ≤ s+1 by omega)) (σ.label c)
  rw [he] at h2
  exact h0.trans_lt (h1.trans_le h2)

theorem bounded_label_stabilization (σ : Schedule) (x n : ℕ)
    (h : (lowEvents σ x n).Finite) :
    ∃ S, (∀ t ≥ S, ∀ i ≤ n, marker (stages σ x t) i = marker (stages σ x S) i) ∧
      ∀ i ≤ n, marker (stages σ x S) i ∉ output σ x := by
  obtain ⟨S,hS⟩ := finite_events_collected σ x (lowEvents σ x n) h (fun _ hc => hc.1)
  have hno : ∀ t ≥ S, ∀ c, fresh σ x t c = true → n < σ.label c := by
    intro t ht c hf
    by_contra hn
    have he : σ.event x (t+1) c = true ∧ σ.event x t c = false := by simpa [fresh] using hf
    have hlow : c ∈ lowEvents σ x n := ⟨⟨t+1,he.1⟩,by omega⟩
    have hold := event_monotone σ x c ht (hS c hlow)
    rw [hold] at he
    simp at he
  have hstable : ∀ t ≥ S, ∀ i ≤ n,
      marker (stages σ x t) i = marker (stages σ x S) i := by
    intro t ht
    induction ht with
    | refl => exact fun _ _ => rfl
    | @step t ht ih =>
      intro i hi
      exact (scan_prefix σ x t (stages σ x t) (t+1) n
        (fun c _ hf => hno t ht c hf) i hi).trans (ih i hi)
  refine ⟨S,hstable,?_⟩
  intro i hi
  rintro ⟨t,ht⟩
  have hm := stages_included σ x (le_max_right S t) _ ht
  have hmarker := hstable (max S t) (le_max_left _ _) i hi
  rw [← hmarker] at hm
  exact (marker_spec (stages σ x (max S t)) i).1 hm

theorem output_coinfinite_of_finite_low (σ : Schedule) (x : ℕ)
    (h : ∀ n, (lowEvents σ x n).Finite) :
    (output σ x)ᶜ.Infinite := by
  intro hf
  obtain ⟨a,ha⟩ := hf.bddAbove
  obtain ⟨S,_,hS⟩ := bounded_label_stabilization σ x (a+1) (h (a+1))
  have hm := hS (a+1) le_rfl
  have hu := ha hm
  have hl := (marker_strictMono (stages σ x S)).id_le (a+1)
  change a+1 ≤ marker (stages σ x S) (a+1) at hl
  omega

theorem marker_unbounded_of_infinite_label (σ : Schedule) (x y : ℕ)
    (h : (labelEvents σ x y).Infinite) :
    ∀ N, ∃ s, N < marker (stages σ x s) y := by
  intro N
  by_contra hn
  push Not at hn
  obtain ⟨b,S,hS⟩ := converges_of_monotone_of_bounded (stage_marker_monotone σ x y) hn
  apply h
  apply (Set.finite_Iio S).subset
  intro c hc
  obtain ⟨t,ht,_⟩ := (event_once σ x c).mp hc.1
  have hb := fresh_bound σ x t c ht
  by_contra hlt
  change ¬ c < S at hlt
  have htS : S ≤ t := by omega
  have hm := fresh_label_strict σ x t c ht
  rw [hc.2, hS t htS, hS (t+1) (by omega)] at hm
  omega

/-- Any finite collection of final omissions has at most y elements. -/
theorem complement_card_bound (σ : Schedule) (x y : ℕ)
    (h : (labelEvents σ x y).Infinite) (F : Finset ℕ)
    (hF : ∀ z ∈ F, z ∉ output σ x) : F.card ≤ y := by
  obtain ⟨s,hs⟩ := marker_unbounded_of_infinite_label σ x y h (F.sup id)
  have hsub : F ⊆ (missingBelow (stages σ x s) (marker (stages σ x s) y)).toFinset := by
    intro z hz
    have hle : z ≤ F.sup id := Finset.le_sup (f := id) hz
    have hn : z ∉ stages σ x s := fun hm => hF z hz ⟨s,hm⟩
    simp [missingBelow, show z < marker (stages σ x s) y from lt_of_le_of_lt hle hs, hn]
  have hc := Finset.card_le_card hsub
  have hn : (missingBelow (stages σ x s) (marker (stages σ x s) y)).Nodup :=
    (List.nodup_range).filter _
  rw [List.toFinset_card_of_nodup hn, (marker_spec (stages σ x s) y).2] at hc
  exact hc

theorem output_cofinite_of_infinite_label (σ : Schedule) (x y : ℕ)
    (h : (labelEvents σ x y).Infinite) : (output σ x)ᶜ.Finite := by
  by_contra hn
  obtain ⟨F,hF,hcard⟩ := (show ((output σ x)ᶜ).Infinite from hn).exists_subset_card_eq (y+1)
  have hb := complement_card_bound σ x y h F (fun z hz => hF hz)
  omega

/-- A final-set test certifies a whole marker prefix, without an effective settling bound.
This is finite-prefix transport under the already established stage inclusion. -/
theorem certified_prefix_stable (σ : Schedule) (x n S : ℕ)
    (h : ∀ i ≤ n, marker (stages σ x S) i ∉ output σ x) :
    ∀ t ≥ S, ∀ i ≤ n, marker (stages σ x t) i = marker (stages σ x S) i := by
  intro t ht
  apply marker_prefix_of_included _ _ (stages_included σ x ht) n
  intro i hi hm
  exact h i hi ⟨t,hm⟩

end Lemmatheca.ComputabilityTheory.ThirdLevelIndexSets
