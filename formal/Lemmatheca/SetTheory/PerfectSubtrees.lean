import Lemmatheca.SetTheory.AlmostDisjoint
import Mathlib.Data.List.Infix
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Count
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Continuum

/-! Countable sequence trees, binary splitting, and their largest perfect kernel.
Paths are functions on the naturals, represented by all their finite list prefixes.
Empty trees and empty perfect trees are permitted. -/

noncomputable section

namespace Lemmatheca.SetTheory.PerfectSubtrees

open Set Cardinal

/-- The finite prefix of a natural-number sequence of the specified length. -/
def natPrefix (x : ℕ → ℕ) (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => x i)

/-- Prefix closure, with no root or nonemptiness assumption. -/
def IsSequenceTree (T : Set (List ℕ)) : Prop :=
  ∀ ⦃s⦄, s ∈ T → ∀ ⦃t⦄, t <+: s → t ∈ T

/-- The complete set of infinite paths through a family of finite sequences. -/
def body (T : Set (List ℕ)) : Set (ℕ → ℕ) :=
  {x | ∀ n, natPrefix x n ∈ T}

/-- An infinite sequence extends a finite word. -/
def Extends (s : List ℕ) (x : ℕ → ℕ) : Prop := natPrefix x s.length = s

/-- The paths through T extending the given finite word. -/
def cone (T : Set (List ℕ)) (s : List ℕ) : Set (ℕ → ℕ) :=
  {x | x ∈ body T ∧ Extends s x}

def IsSubtree (S T : Set (List ℕ)) : Prop := IsSequenceTree S ∧ S ⊆ T

/-- Incompatibility is incomparability in the finite-prefix order. -/
def Incompatible (s t : List ℕ) : Prop := ¬s <+: t ∧ ¬t <+: s

/-- A perfect tree keeps admitting incompatible extensions above every node. -/
def IsPerfect (P : Set (List ℕ)) : Prop :=
  IsSequenceTree P ∧ ∀ s ∈ P, ∃ u ∈ P, ∃ v ∈ P,
    s <+: u ∧ s <+: v ∧ Incompatible u v

def pathNodes (x : ℕ → ℕ) : Set (List ℕ) := Set.range (natPrefix x)

@[simp] theorem natPrefix_length (x : ℕ → ℕ) (n : ℕ) : (natPrefix x n).length = n := by
  simp [natPrefix]

@[simp] theorem natPrefix_get (x : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    (natPrefix x n)[i]'(by simpa using hi) = x i := by
  simp [natPrefix]

theorem natPrefix_mono (x : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) :
    natPrefix x n <+: natPrefix x m := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by simpa using h, ?_⟩
  intro i hi
  simp [natPrefix]

theorem prefix_of_extends {s : List ℕ} {x : ℕ → ℕ} (h : Extends s x)
    {n : ℕ} (hn : s.length ≤ n) : s <+: natPrefix x n := by
  rw [← h]
  exact natPrefix_mono x hn

theorem extends_of_prefix {s : List ℕ} {x : ℕ → ℕ} {n : ℕ}
    (h : s <+: natPrefix x n) : Extends s x := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa [natPrefix] using (h.getElem hj).symm

theorem extends_trans {s t : List ℕ} {x : ℕ → ℕ} (h : s <+: t)
    (ht : Extends t x) : Extends s x := by
  exact extends_of_prefix (h.trans (prefix_of_extends ht (le_refl _)))

theorem extends_comparable {s t : List ℕ} {x : ℕ → ℕ}
    (hs : Extends s x) (ht : Extends t x) : s <+: t ∨ t <+: s := by
  exact List.prefix_or_prefix_of_prefix
    (prefix_of_extends hs (Nat.le_max_left _ _))
    (prefix_of_extends ht (Nat.le_max_right _ _))

theorem root_mem {T : Set (List ℕ)} (hT : IsSequenceTree T) (hne : T.Nonempty) :
    [] ∈ T := by
  obtain ⟨s, hs⟩ := hne
  exact hT hs (List.nil_prefix)

theorem body_mono {S T : Set (List ℕ)} (h : S ⊆ T) : body S ⊆ body T := by
  intro x hx n
  exact h (hx n)

theorem cone_antitone (T : Set (List ℕ)) {s t : List ℕ} (h : s <+: t) :
    cone T t ⊆ cone T s := by
  intro x hx
  exact ⟨hx.1, extends_trans h hx.2⟩

/-- Prefix nodes form a downward-closed chain, meeting every finite length. -/
theorem pathNodes_spec {T : Set (List ℕ)} {x : ℕ → ℕ} (hx : x ∈ body T) :
    pathNodes x ⊆ T ∧
      (∀ s ∈ pathNodes x, ∀ t ∈ pathNodes x, s <+: t ∨ t <+: s) ∧
      IsSequenceTree (pathNodes x) ∧
      ∀ n, ∃ s ∈ pathNodes x, s.length = n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro s ⟨n, rfl⟩
    exact hx n
  · rintro s ⟨n, rfl⟩ t ⟨m, rfl⟩
    rcases le_total n m with h | h
    · exact Or.inl (natPrefix_mono x h)
    · exact Or.inr (natPrefix_mono x h)
  · rintro s ⟨n, rfl⟩ t ht
    exact ⟨t.length, extends_of_prefix ht⟩
  · intro n
    exact ⟨natPrefix x n, ⟨n, rfl⟩, natPrefix_length x n⟩

theorem incompatible_strict_extensions {s u v : List ℕ}
    (hu : s <+: u) (hv : s <+: v) (h : Incompatible u v) :
    s.length < u.length ∧ s.length < v.length := by
  constructor
  · refine lt_of_le_of_ne hu.length_le ?_
    intro he
    exact h.1 ((hu.eq_of_length he).symm ▸ hv)
  · refine lt_of_le_of_ne hv.length_le ?_
    intro he
    exact h.2 ((hv.eq_of_length he).symm ▸ hu)

/-- A binary splitting system, with children indexed by appending one bit. -/
def BinarySystem (P : Set (List ℕ)) (r : List ℕ)
    (u : List Bool → List ℕ) : Prop :=
  u [] = r ∧ (∀ σ, u σ ∈ P) ∧
    ∀ σ, u σ <+: u (σ ++ [false]) ∧ u σ <+: u (σ ++ [true]) ∧
      (u σ).length < (u (σ ++ [false])).length ∧
      (u σ).length < (u (σ ++ [true])).length ∧
      Incompatible (u (σ ++ [false])) (u (σ ++ [true]))

/-- The selected system nodes together with all of their prefixes. -/
def systemClosure (u : List Bool → List ℕ) : Set (List ℕ) :=
  {t | ∃ σ, t <+: u σ}

/-- The coherent union along a binary path, reading each coordinate late enough. -/
def systemPath (u : List Bool → List ℕ) (z : ℕ → Bool) (n : ℕ) : ℕ :=
  (u (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z (n + 1))).getD n 0

theorem binary_system_exists {P : Set (List ℕ)} (hP : IsPerfect P)
    {r : List ℕ} (hr : r ∈ P) :
    ∃ u : List Bool → List ℕ, BinarySystem P r u := by
  classical
  choose left hleft right hright hl hrightpre hi using hP.2
  let child (s : List ℕ) (b : Bool) : List ℕ :=
    if h : s ∈ P then if b then right s h else left s h else s
  have hc (s : List ℕ) (hs : s ∈ P) (b : Bool) : child s b ∈ P := by
    cases b <;> simp [child, hs, hleft, hright]
  let u (σ : List Bool) := σ.foldl child r
  have hm (σ : List Bool) : u σ ∈ P := by
    induction σ using List.reverseRecOn with
    | nil => simpa [u] using hr
    | append_singleton σ b ih => simpa [u, List.foldl_append] using hc (u σ) ih b
  refine ⟨u, by simp [u], hm, ?_⟩
  intro σ
  have hs := hm σ
  have hlen := incompatible_strict_extensions (hl (u σ) hs) (hrightpre (u σ) hs) (hi (u σ) hs)
  simpa [u, List.foldl_append, child, hs] using
    And.intro (hl (u σ) hs) (And.intro (hrightpre (u σ) hs)
      (And.intro hlen.1 (And.intro hlen.2 (hi (u σ) hs))))

theorem systemClosure_spec {P : Set (List ℕ)} (hP : IsSequenceTree P)
    {r : List ℕ} {u : List Bool → List ℕ} (hu : BinarySystem P r u) :
    IsPerfect (systemClosure u) ∧ IsSubtree (systemClosure u) P ∧
      (systemClosure u).Nonempty := by
  have ht : IsSequenceTree (systemClosure u) := by
    rintro s ⟨σ, hs⟩ t ht
    exact ⟨σ, ht.trans hs⟩
  refine ⟨⟨ht, ?_⟩, ⟨ht, ?_⟩, ?_⟩
  · rintro s ⟨σ, hs⟩
    exact ⟨u (σ ++ [false]), ⟨σ ++ [false], List.prefix_rfl⟩,
      u (σ ++ [true]), ⟨σ ++ [true], List.prefix_rfl⟩,
      hs.trans (hu.2.2 σ).1, hs.trans (hu.2.2 σ).2.1, (hu.2.2 σ).2.2.2.2⟩
  · rintro s ⟨σ, hs⟩
    exact hP (hu.2.1 σ) hs
  · exact ⟨u [], ⟨[], List.prefix_rfl⟩⟩


private theorem binarySystem_step {P : Set (List ℕ)} {r : List ℕ}
    {u : List Bool → List ℕ} (hu : BinarySystem P r u) (σ : List Bool) (b : Bool) :
    u σ <+: u (σ ++ [b]) ∧ (u σ).length < (u (σ ++ [b])).length := by
  cases b
  · exact ⟨(hu.2.2 σ).1, (hu.2.2 σ).2.2.1⟩
  · exact ⟨(hu.2.2 σ).2.1, (hu.2.2 σ).2.2.2.1⟩

private theorem binarySystem_mono {P : Set (List ℕ)} {r : List ℕ}
    {u : List Bool → List ℕ} (hu : BinarySystem P r u)
    {σ τ : List Bool} (h : σ <+: τ) : u σ <+: u τ := by
  obtain ⟨l, rfl⟩ := h
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    simpa [List.append_assoc] using ih.trans (binarySystem_step hu (σ ++ l) b).1

private theorem binarySystem_length {P : Set (List ℕ)} {r : List ℕ}
    {u : List Bool → List ℕ} (hu : BinarySystem P r u) (σ : List Bool) :
    σ.length ≤ (u σ).length := by
  induction σ using List.reverseRecOn with
  | nil => simp
  | append_singleton σ b ih =>
    have hh := (binarySystem_step hu σ b).2
    simp only [List.length_append, List.length_singleton]
    omega

private theorem binaryPrefix_mono (z : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n <+:
      Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z m := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by simpa [Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix] using h, ?_⟩
  intro i hi
  simp [Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix]

private theorem binaryPrefix_succ (z : ℕ → Bool) (n : ℕ) :
    Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z (n + 1) =
      Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n ++ [z n] := by
  simpa [Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix] using
    List.ofFn_succ' (fun i : Fin (n + 1) => z i)

private theorem getD_eq_of_prefix {s t : List ℕ} (h : s <+: t) {i : ℕ}
    (hi : i < s.length) : s.getD i 0 = t.getD i 0 := by
  simp only [List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ (lt_of_lt_of_le hi h.length_le)]
  exact h.getElem hi

theorem systemPath_spec {P : Set (List ℕ)} (hP : IsSequenceTree P)
    {r : List ℕ} {u : List Bool → List ℕ} (hu : BinarySystem P r u) :
    Function.Injective (systemPath u) ∧
      ∀ z : ℕ → Bool, systemPath u z ∈ cone P r ∧
        systemPath u z ∈ body (systemClosure u) ∧
        ∀ n, Extends (u (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n)) (systemPath u z) := by
  classical
  have hext (z : ℕ → Bool) (n : ℕ) :
      Extends (u (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n)) (systemPath u z) := by
    let w (m : ℕ) := u (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z m)
    have hlen (m : ℕ) : m ≤ (w m).length := by
      simpa [w, Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix] using
        binarySystem_length hu (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z m)
    have hmono {a b : ℕ} (hab : a ≤ b) : w a <+: w b :=
      binarySystem_mono hu (binaryPrefix_mono z hab)
    have hcoh (a b i : ℕ) (ha : i < (w a).length) (hb : i < (w b).length) :
        (w a).getD i 0 = (w b).getD i 0 := by
      rcases le_total a b with hab | hba
      · exact getD_eq_of_prefix (hmono hab) ha
      · exact (getD_eq_of_prefix (hmono hba) hb).symm
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [natPrefix, List.getElem_ofFn]
      change systemPath u z i = (w n)[i]
      change (w (i + 1)).getD i 0 = (w n)[i]
      rw [← List.getD_eq_getElem _ _ hj]
      exact hcoh (i + 1) n i (lt_of_lt_of_le (by omega) (hlen (i + 1))) hj
  have hpath (z : ℕ → Bool) :
      systemPath u z ∈ cone P r ∧ systemPath u z ∈ body (systemClosure u) ∧
      ∀ n, Extends (u (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n)) (systemPath u z) := by
    have hpref (n : ℕ) : natPrefix (systemPath u z) n <+:
        u (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n) := by
      have hlen := binarySystem_length hu (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n)
      have hn : n ≤ (u (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n)).length := by
        simpa [Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix] using hlen
      have hh := natPrefix_mono (systemPath u z) hn
      rw [show natPrefix (systemPath u z) (u (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n)).length = u (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n) from hext z n] at hh
      exact hh
    refine ⟨⟨?_, ?_⟩, ?_, hext z⟩
    · intro n
      exact hP (hu.2.1 _) (hpref n)
    · have hh := hext z 0
      simpa [Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix, hu.1] using hh
    · intro n
      exact ⟨Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n, hpref n⟩
  refine ⟨?_, hpath⟩
  intro z y hxy
  have hp (n : ℕ) : Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n =
      Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix y n := by
    induction n with
    | zero => simp [Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix]
    | succ n ih =>
      have hz := hext z (n + 1)
      have hy := hext y (n + 1)
      rw [binaryPrefix_succ] at hz hy
      rw [← ih, ← hxy] at hy
      have hc := extends_comparable hz hy
      have hi := (hu.2.2 (Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix z n)).2.2.2.2
      have hbit : z n = y n := by
        cases hzn : z n <;> cases hyn : y n
        · rfl
        · rw [hzn, hyn] at hc
          exact (hc.elim hi.1 hi.2).elim
        · rw [hzn, hyn] at hc
          exact (hc.elim hi.2 hi.1).elim
        · rfl
      rw [binaryPrefix_succ, binaryPrefix_succ, ih, hbit]
  funext n
  have hh := congrArg (fun l : List Bool => l[n]?) (hp (n + 1))
  simpa only [Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix, List.getElem?_ofFn, dite_eq_left (Nat.lt_succ_self n), Option.some.injEq] using hh

theorem perfect_cone_injection {P : Set (List ℕ)} (hP : IsPerfect P)
    {r : List ℕ} (hr : r ∈ P) :
    ∃ f : (ℕ → Bool) → cone P r, Function.Injective f := by
  obtain ⟨u, hu⟩ := binary_system_exists hP hr
  have hh := systemPath_spec hP.1 hu
  refine ⟨fun z => ⟨systemPath u z, (hh.2 z).1⟩, ?_⟩
  intro z y h
  exact hh.1 (congrArg Subtype.val h)

/-- Nodes whose original-tree branch cone is uncountable. -/
def kernel (T : Set (List ℕ)) : Set (List ℕ) :=
  {s | s ∈ T ∧ ¬(cone T s).Countable}

/-- Branches passing through an original-tree node with a countable cone. -/
def exceptional (T : Set (List ℕ)) : Set (ℕ → ℕ) :=
  {x | ∃ s ∈ T, s ∉ kernel T ∧ x ∈ cone T s}

theorem kernel_subtree {T : Set (List ℕ)} (hT : IsSequenceTree T) :
    IsSubtree (kernel T) T := by
  refine ⟨?_, fun _ hs => hs.1⟩
  intro s hs t ht
  refine ⟨hT hs.1 ht, ?_⟩
  intro hc
  exact hs.2 (hc.mono (cone_antitone T ht))

theorem exceptional_countable (T : Set (List ℕ)) : (exceptional T).Countable := by
  classical
  let C (s : List ℕ) := if s ∈ T ∧ s ∉ kernel T then cone T s else ∅
  have hc (s : List ℕ) : (C s).Countable := by
    dsimp [C]
    split_ifs with h
    · by_contra hn
      exact h.2 ⟨h.1, hn⟩
    · exact countable_empty
  apply (countable_iUnion hc).mono
  rintro x ⟨s, hs, hn, hx⟩
  exact mem_iUnion.mpr ⟨s, by simpa [C, hs, hn] using hx⟩

theorem kernel_remainder (T : Set (List ℕ)) :
    body T \ body (kernel T) = exceptional T := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨n, hn⟩ : ∃ n, natPrefix x n ∉ kernel T := by
      simpa only [body, mem_ofPred_eq, not_forall] using hn
    exact ⟨natPrefix x n, hx n, hn, hx, by simp [Extends]⟩
  · rintro ⟨s, hs, hn, hx⟩
    refine ⟨hx.1, ?_⟩
    intro hk
    exact hn (hx.2 ▸ hk s.length)

theorem kernel_perfect {T : Set (List ℕ)} (hT : IsSequenceTree T) :
    IsPerfect (kernel T) := by
  classical
  refine ⟨(kernel_subtree hT).1, ?_⟩
  intro s hs
  have hun : ¬(cone T s \ exceptional T).Countable := by
    intro hc
    exact hs.2 (hc.of_sdiff (exceptional_countable T))
  have hnt : (cone T s \ exceptional T).Nontrivial :=
    Set.not_subsingleton_iff.mp (fun hh => hun hh.countable)
  obtain ⟨x, hx, y, hy, hxy⟩ := hnt
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ y k := by
    by_contra hn
    push Not at hn
    exact hxy (funext hn)
  let n := max s.length (k + 1)
  have hklt : k < n := lt_of_lt_of_le (by omega) (Nat.le_max_right _ _)
  have hgood (z : ℕ → ℕ) (hz : z ∈ cone T s \ exceptional T) : z ∈ body (kernel T) := by
    intro m
    refine ⟨hz.1.1 m, ?_⟩
    intro hn
    exact hz.2 ⟨natPrefix z m, hz.1.1 m, (fun hk => hk.2 hn), hz.1.1, by simp [Extends]⟩
  have hne : natPrefix x n ≠ natPrefix y n := by
    intro he
    have hh := congrArg (fun l : List ℕ => l[k]?) he
    have hv : x k = y k := by
      simpa only [natPrefix, List.getElem?_ofFn, dite_eq_left hklt, Option.some.injEq] using hh
    exact hk hv
  refine ⟨natPrefix x n, hgood x hx n, natPrefix y n, hgood y hy n,
    prefix_of_extends hx.1.2 (Nat.le_max_left _ _),
    prefix_of_extends hy.1.2 (Nat.le_max_left _ _), ?_⟩
  constructor
  · intro hp
    exact hne (hp.eq_of_length (by simp))
  · intro hp
    exact hne (hp.eq_of_length (by simp)).symm


private theorem perfect_cone_lower {P : Set (List ℕ)} (hP : IsPerfect P)
    {r : List ℕ} (hr : r ∈ P) : Cardinal.continuum ≤ Cardinal.mk (cone P r) := by
  obtain ⟨f, hf⟩ := perfect_cone_injection hP hr
  have hh := Cardinal.mk_le_of_injective hf
  simpa only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat,
    Cardinal.lift_id, Cardinal.lift_aleph0, Cardinal.two_power_aleph0] using hh

private theorem perfect_cone_uncountable {P : Set (List ℕ)} (hP : IsPerfect P)
    {r : List ℕ} (hr : r ∈ P) : ¬(cone P r).Countable := by
  intro hc
  have hh := (perfect_cone_lower hP hr).trans (Cardinal.le_aleph0_iff_set_countable.mpr hc)
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hh

theorem kernel_largest {T Q : Set (List ℕ)} (hQ : IsPerfect Q) (hQT : Q ⊆ T) :
    Q ⊆ kernel T := by
  intro s hs
  refine ⟨hQT hs, ?_⟩
  intro hc
  apply perfect_cone_uncountable hQ hs
  apply hc.mono
  intro x hx
  exact ⟨body_mono hQT hx.1, hx.2⟩

theorem kernel_nonempty_iff {T : Set (List ℕ)} (_hT : IsSequenceTree T) :
    (kernel T).Nonempty ↔ ¬(body T).Countable := by
  constructor
  · rintro ⟨s, hs⟩ hc
    exact hs.2 (hc.mono (fun _ hx => hx.1))
  · intro hn
    by_contra he
    have hempty : kernel T = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    have hbody : body (kernel T) = ∅ := by
      rw [hempty]
      ext x
      simp [body]
    have hr := kernel_remainder T
    rw [hbody, sdiff_empty] at hr
    exact hn (hr ▸ exceptional_countable T)

theorem kernel_empty_iff {T : Set (List ℕ)} (hT : IsSequenceTree T) :
    kernel T = ∅ ↔ (body T).Countable := by
  rw [← Set.not_nonempty_iff_eq_empty, kernel_nonempty_iff hT]
  exact not_not

theorem kernel_self_of_perfect {T : Set (List ℕ)} (hT : IsPerfect T) : kernel T = T := by
  exact Set.Subset.antisymm (kernel_subtree hT.1).2 (kernel_largest hT (Subset.rfl))

theorem body_cardinality_le (T : Set (List ℕ)) : Cardinal.mk (body T) ≤ Cardinal.continuum := by
  have hh := Cardinal.mk_set_le (body T)
  simpa only [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_id,
    Cardinal.lift_aleph0, Cardinal.aleph0_power_aleph0] using hh

theorem body_cardinality_dichotomy {T : Set (List ℕ)} (hT : IsSequenceTree T) :
    (body T).Countable ∨ Cardinal.mk (body T) = Cardinal.continuum := by
  classical
  by_cases hc : (body T).Countable
  · exact Or.inl hc
  · right
    obtain ⟨r, hr⟩ := (kernel_nonempty_iff hT).mpr hc
    have hl := perfect_cone_lower (kernel_perfect hT) hr
    have hm : Cardinal.mk (cone (kernel T) r) ≤ Cardinal.mk (body T) := by
      let f : cone (kernel T) r → body T :=
        fun x => ⟨x.val, body_mono (kernel_subtree hT).2 x.property.1⟩
      apply Cardinal.mk_le_of_injective (f := f)
      intro x y h
      exact Subtype.ext (congrArg (fun z : body T => z.val) h)
    exact (body_cardinality_le T).antisymm (hl.trans hm)

theorem uncountable_iff_perfect_subtree {T : Set (List ℕ)} (hT : IsSequenceTree T) :
    ¬(body T).Countable ↔
      ∃ P : Set (List ℕ), IsSubtree P T ∧ IsPerfect P ∧ P.Nonempty := by
  constructor
  · intro hn
    exact ⟨kernel T, kernel_subtree hT, kernel_perfect hT, (kernel_nonempty_iff hT).mpr hn⟩
  · rintro ⟨P, hPT, hP, r, hr⟩ hc
    apply perfect_cone_uncountable hP hr
    apply hc.mono
    intro x hx
    exact body_mono hPT.2 hx.1

/-- All finite prefixes of a selected family of infinite paths. -/
def prefixTree (A : Set (ℕ → ℕ)) : Set (List ℕ) :=
  {s | ∃ x ∈ A, ∃ n, natPrefix x n = s}

end Lemmatheca.SetTheory.PerfectSubtrees
