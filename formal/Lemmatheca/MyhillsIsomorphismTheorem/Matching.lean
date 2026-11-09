import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Reduce
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.FinRange
import Lemmatheca.CodingFiniteSequences.FiniteSequenceCoding

/-! The finite ordered matching construction in Myhill's theorem. Labels are
proof invariants only: none of the numerical definitions take labels as input. -/
namespace Lemmatheca.ComputabilityTheory.Myhill

abbrev Matching := List (ℕ × ℕ)

def IsMatching (M : Matching) : Prop :=
  (M.map Prod.fst).Nodup ∧ (M.map Prod.snd).Nodup

def domain (M : Matching) : List ℕ := M.map Prod.fst

def range (M : Matching) : List ℕ := M.map Prod.snd

def transpose (M : Matching) : Matching := M.map Prod.swap

def lookup (M : Matching) (x : ℕ) : ℕ := (M.lookup x).getD 0

def inverseLookup (M : Matching) (y : ℕ) : ℕ := lookup (transpose M) y

def Extends (M N : Matching) : Prop := ∀ p ∈ M, p ∈ N

/-- Test successive positions until the first true test; freeze there. If all
tests at positions below the bound are false, return the bound itself. -/
def boundedSearch (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if p (boundedSearch p n) then boundedSearch p n else n + 1

def leastUnused (M : Matching) : ℕ :=
  boundedSearch (fun x => (M.lookup x).isNone) (M.length + 1)

def leastUnusedOutput (M : Matching) : ℕ := leastUnused (transpose M)

def walk (f : ℕ → ℕ) (M : Matching) (x : ℕ) : ℕ → ℕ
  | 0 => x
  | n + 1 => inverseLookup M (f (walk f M x n))

def escapeIndex (f : ℕ → ℕ) (M : Matching) (x : ℕ) : ℕ :=
  boundedSearch (fun n => ((transpose M).lookup (f (walk f M x n))).isNone)
    (M.length + 1)

def endpoint (f : ℕ → ℕ) (M : Matching) (x : ℕ) : ℕ :=
  f (walk f M x (escapeIndex f M x))

def extend (f : ℕ → ℕ) (M : Matching) (x : ℕ) : Matching :=
  M ++ [(x, endpoint f M x)]

def Respects {L : Type*} (left right : ℕ → L) (M : Matching) : Prop :=
  ∀ p ∈ M, left p.1 = right p.2

def leftCompletion (f : ℕ → ℕ) (M : Matching) : Matching :=
  extend f M (leastUnused M)

def rightCompletion (g : ℕ → ℕ) (M : Matching) : Matching :=
  transpose (extend g (transpose M) (leastUnusedOutput M))

def stage (f g : ℕ → ℕ) : ℕ → Matching
  | 0 => []
  | s + 1 => if s % 2 = 0 then leftCompletion f (stage f g s)
    else rightCompletion g (stage f g s)

def forward (f g : ℕ → ℕ) (x : ℕ) : ℕ :=
  lookup (stage f g (2 * (x + 1))) x

def backward (f g : ℕ → ℕ) (y : ℕ) : ℕ :=
  inverseLookup (stage f g (2 * (y + 1))) y

private theorem lookup_none_iff (M : Matching) (x : ℕ) :
    M.lookup x = none ↔ x ∉ domain M := by
  rw [List.lookup_eq_none_iff]
  simp only [bne_iff_ne, domain, List.mem_map, not_exists, not_and]
  constructor
  · intro h p hp he
    exact h p hp he.symm
  · intro h p hp he
    exact h p hp he.symm

private theorem lookup_some_mem (M : Matching) (x y : ℕ)
    (h : M.lookup x = some y) : (x, y) ∈ M := by
  obtain ⟨l, r, he, _⟩ := List.lookup_eq_some_iff.mp h
  simp [he]

private theorem functional_left (M : Matching) (hM : IsMatching M)
    {x y z : ℕ} (hy : (x, y) ∈ M) (hz : (x, z) ∈ M) : y = z := by
  exact congrArg Prod.snd (List.inj_on_of_nodup_map hM.1 hy hz rfl)

private theorem functional_right (M : Matching) (hM : IsMatching M)
    {x y z : ℕ} (hx : (x, z) ∈ M) (hy : (y, z) ∈ M) : x = y := by
  exact congrArg Prod.fst (List.inj_on_of_nodup_map hM.2 hx hy rfl)

private theorem transpose_mem (M : Matching) (x y : ℕ) :
    (y, x) ∈ transpose M ↔ (x, y) ∈ M := by
  simp [transpose]

theorem matching_code (M : Matching) :
    Encodable.encode M = FiniteSequenceCoding.code (M.map (fun p => Nat.pair p.1 p.2)) := by
  induction M with
  | nil => rfl
  | cons p M ih =>
    change Nat.pair (Nat.pair p.1 p.2) (Encodable.encode M) + 1 =
      Nat.pair (Nat.pair p.1 p.2) (Encodable.encode (M.map (fun p => Nat.pair p.1 p.2))) + 1
    exact congrArg (fun n => Nat.pair (Nat.pair p.1 p.2) n + 1) ih

theorem matching_lookup (M : Matching) (hM : IsMatching M) :
    (∀ x y, (x, y) ∈ M ↔ M.lookup x = some y) ∧
      (∀ x ∈ domain M, (x, lookup M x) ∈ M) ∧
      (∀ y ∈ range M, (inverseLookup M y, y) ∈ M) := by
  have hs (x y : ℕ) : (x, y) ∈ M ↔ M.lookup x = some y := by
    constructor
    · intro h
      cases he : M.lookup x with
      | none =>
        exact False.elim ((lookup_none_iff M x).mp he (List.mem_map.mpr ⟨(x, y), h, rfl⟩))
      | some z =>
        have hz := lookup_some_mem M x z he
        have hzy := functional_left M hM hz h
        simp [hzy]
    · exact lookup_some_mem M x y
  refine ⟨hs, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hx
    have he' : M.lookup x = some p.2 := hs x p.2 |>.mp (by simpa [← he] using hp)
    simpa [lookup, he'] using (hs x p.2).mpr he'
  · intro y hy
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hy
    have hm : (y, p.1) ∈ transpose M := (transpose_mem M p.1 y).mpr (by simpa [← he] using hp)
    have hn : ((transpose M).map Prod.fst).Nodup := by
      simpa [transpose, List.map_map, Function.comp_def] using hM.2
    cases ht : (transpose M).lookup y with
    | none => exact False.elim ((lookup_none_iff (transpose M) y).mp ht
        (List.mem_map.mpr ⟨(y, p.1), hm, rfl⟩))
    | some z =>
      have hz := lookup_some_mem (transpose M) y z ht
      have hez : z = p.1 := congrArg Prod.snd (List.inj_on_of_nodup_map hn hz hm rfl)
      change ((transpose M).lookup y |>.getD 0, y) ∈ M
      rw [ht]
      simp only [Option.getD_some, hez]
      exact (transpose_mem M p.1 y).mp hm

theorem transpose_matching (M : Matching) :
    transpose (transpose M) = M ∧
      (IsMatching (transpose M) ↔ IsMatching M) ∧
      domain (transpose M) = range M ∧ range (transpose M) = domain M := by
  have ht : transpose (transpose M) = M := by
    simp [transpose, List.map_map, Function.comp_def]
  have hd : domain (transpose M) = range M := by
    simp [domain, range, transpose, List.map_map, Function.comp_def]
  have hr : range (transpose M) = domain M := by
    simp [domain, range, transpose, List.map_map, Function.comp_def]
  refine ⟨ht, ?_, hd, hr⟩
  change (domain (transpose M)).Nodup ∧ (range (transpose M)).Nodup ↔
    (domain M).Nodup ∧ (range M).Nodup
  rw [hd, hr, and_comm]

private theorem boundedSearch_invariant (p : ℕ → Bool) (n : ℕ) :
    boundedSearch p n ≤ n ∧
      (∀ i < boundedSearch p n, p i = false) ∧
      (boundedSearch p n < n → p (boundedSearch p n) = true) := by
  induction n with
  | zero => simp [boundedSearch]
  | succ n ih =>
    by_cases hp : p (boundedSearch p n) = true
    · rw [boundedSearch, ite_eq_left hp]
      exact ⟨by omega, ih.2.1, fun _ => hp⟩
    · have hp' : p (boundedSearch p n) = false := Bool.eq_false_iff.mpr hp
      have he : boundedSearch p n = n := by
        by_contra hn
        exact hp (ih.2.2 (by omega))
      rw [boundedSearch, ite_eq_right hp]
      refine ⟨le_rfl, ?_, by omega⟩
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · exact ih.2.1 i (by omega)
      · simpa [he] using hp'

private theorem boundedSearch_success (p : ℕ → Bool) {k n : ℕ}
    (hk : k < n) (hp : p k = true) :
    boundedSearch p n ≤ k ∧ p (boundedSearch p n) = true := by
  have hi := boundedSearch_invariant p n
  have hl : boundedSearch p n ≤ k := by
    by_contra h
    have := hi.2.1 k (by omega)
    simp [hp] at this
  exact ⟨hl, hi.2.2 (by omega)⟩

private theorem missing_coordinate (l : List ℕ) : ∃ x ≤ l.length, x ∉ l := by
  by_contra! h
  have hs : Finset.range (l.length + 1) ⊆ l.toFinset := by
    intro x hx
    exact List.mem_toFinset.mpr (h x (by simpa using Finset.mem_range.mp hx))
  have hc := Finset.card_le_card hs
  have hl := List.toFinset_card_le l
  rw [Finset.card_range] at hc
  omega

private theorem fresh_test (M : Matching) (x : ℕ) :
    (M.lookup x).isNone = true ↔ x ∉ domain M := by
  rw [Option.isNone_iff_eq_none, lookup_none_iff]

theorem leastUnused_spec (M : Matching) :
    leastUnused M ≤ M.length ∧ leastUnused M ∉ domain M ∧
      ∀ i < leastUnused M, i ∈ domain M := by
  obtain ⟨k, hk, hkm⟩ := missing_coordinate (domain M)
  have hk' : k ≤ M.length := by simpa [domain] using hk
  have hp := (fresh_test M k).mpr hkm
  have hs := boundedSearch_success (fun x => (M.lookup x).isNone) (by omega : k < M.length + 1) hp
  refine ⟨by exact le_trans hs.1 hk', (fresh_test M _).mp hs.2, ?_⟩
  intro i hi
  by_contra hm
  have hf := (boundedSearch_invariant (fun x => (M.lookup x).isNone) (M.length + 1)).2.1 i hi
  have ht := (fresh_test M i).mpr hm
  simp [ht] at hf

private theorem walk_edge (f : ℕ → ℕ) (M : Matching) (x i : ℕ)
    (hM : IsMatching M) (hi : f (walk f M x i) ∈ range M) :
    (walk f M x (i + 1), f (walk f M x i)) ∈ M := by
  exact (matching_lookup M hM).2.2 _ hi

private theorem walk_no_repeat (f : ℕ → ℕ) (M : Matching) (x n : ℕ)
    (hM : IsMatching M) (hf : Function.Injective f) (hx : x ∉ domain M)
    (hcont : ∀ i < n, f (walk f M x i) ∈ range M) :
    ∀ i j, i < j → j ≤ n → walk f M x i ≠ walk f M x j := by
  intro i
  induction i with
  | zero =>
    intro j hij hj he
    cases j with
    | zero => omega
    | succ j =>
      have hp := walk_edge f M x j hM (hcont j (by omega))
      have hd : walk f M x (j + 1) ∈ domain M :=
        List.mem_map.mpr ⟨_, hp, rfl⟩
      change x = walk f M x (j + 1) at he
      rw [← he] at hd
      exact hx hd
  | succ i ih =>
    intro j hij hj he
    cases j with
    | zero => omega
    | succ j =>
      have hi := walk_edge f M x i hM (hcont i (by omega))
      have hj' := walk_edge f M x j hM (hcont j (by omega))
      rw [← he] at hj'
      exact ih j (by omega) (by omega) (hf (functional_left M hM hi hj'))

theorem walk_escapes (f : ℕ → ℕ) (M : Matching) (x : ℕ)
    (hM : IsMatching M) (hf : Function.Injective f) (hx : x ∉ domain M) :
    escapeIndex f M x ≤ M.length ∧ endpoint f M x ∉ range M ∧
      ∀ i < escapeIndex f M x, f (walk f M x i) ∈ range M := by
  have hex : ∃ i ≤ M.length, f (walk f M x i) ∉ range M := by
    by_contra! hc
    have hcont : ∀ i < M.length + 1, f (walk f M x i) ∈ range M :=
      fun i hi => hc i (by omega)
    have hn := walk_no_repeat f M x (M.length + 1) hM hf hx hcont
    let a : Fin (M.length + 1) → ℕ := fun i => walk f M x (i.val + 1)
    have ha : Function.Injective a := by
      intro i j he
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with hij | heq | hji
      · exact False.elim (hn (i.val + 1) (j.val + 1) (by omega) (by omega) he)
      · exact heq
      · exact False.elim (hn (j.val + 1) (i.val + 1) (by omega) (by omega) he.symm)
    have hs : Finset.univ.image a ⊆ (domain M).toFinset := by
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨_, walk_edge f M x i.val hM (hcont i.val i.isLt), rfl⟩)
    have hl := Finset.card_le_card hs
    have hl' := List.toFinset_card_le (domain M)
    rw [Finset.card_image_of_injective _ ha] at hl
    simp only [Finset.card_univ, Fintype.card_fin, domain, List.length_map] at hl hl'
    omega
  obtain ⟨i, hi, hif⟩ := hex
  have ht := (transpose_matching M).2.2.1
  have hp : ((transpose M).lookup (f (walk f M x i))).isNone = true := by
    apply (fresh_test (transpose M) _).mpr
    simpa only [ht] using hif
  have hs := boundedSearch_success
    (fun i => ((transpose M).lookup (f (walk f M x i))).isNone)
    (by omega : i < M.length + 1) hp
  refine ⟨le_trans hs.1 hi, ?_, ?_⟩
  · have he := (fresh_test (transpose M) _).mp hs.2
    simpa only [ht, endpoint, escapeIndex] using he
  · intro j hj
    by_contra hnot
    have htrue : ((transpose M).lookup (f (walk f M x j))).isNone = true := by
      apply (fresh_test (transpose M) _).mpr
      simpa only [ht] using hnot
    have hfalse := (boundedSearch_invariant
      (fun i => ((transpose M).lookup (f (walk f M x i))).isNone)
      (M.length + 1)).2.1 j hj
    simp [htrue] at hfalse

theorem extension_matching (f : ℕ → ℕ) (M : Matching) (x : ℕ)
    (hM : IsMatching M) (hf : Function.Injective f) (hx : x ∉ domain M) :
    IsMatching (extend f M x) ∧ Extends M (extend f M x) ∧
      (extend f M x).length = M.length + 1 ∧
      domain (extend f M x) = domain M ++ [x] ∧
      range (extend f M x) = range M ++ [endpoint f M x] ∧
      endpoint f M x ∉ range M := by
  have hy := (walk_escapes f M x hM hf hx).2.1
  have hm : IsMatching (extend f M x) := by
    constructor
    · simpa [extend, List.map_append, IsMatching, domain] using hM.1.concat hx
    · simpa [extend, List.map_append, IsMatching, range] using hM.2.concat hy
  refine ⟨hm, ?_, ?_, ?_, ?_, hy⟩
  · intro p hp
    exact List.mem_append_left _ hp
  · simp [extend]
  · simp [domain, extend]
  · simp [range, extend]

theorem extension_respects {L : Type*} (left right : ℕ → L)
    (f : ℕ → ℕ) (M : Matching) (x : ℕ)
    (hM : IsMatching M) (hf : Function.Injective f) (hx : x ∉ domain M)
    (hlabels : Respects left right M) (hforward : ∀ u, left u = right (f u)) :
    Respects left right (extend f M x) := by
  have hc := (walk_escapes f M x hM hf hx).2.2
  have hw : ∀ i ≤ escapeIndex f M x, left (walk f M x i) = left x := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hp := walk_edge f M x i hM (hc i (by omega))
      calc
        left (walk f M x (i + 1)) = right (f (walk f M x i)) := hlabels _ hp
        _ = left (walk f M x i) := (hforward _).symm
        _ = left x := ih (by omega)
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hlabels p hp
  · have he : p = (x, endpoint f M x) := List.mem_singleton.mp hp
    subst p
    exact (hw _ le_rfl).symm.trans (hforward _)

private theorem left_properties (f : ℕ → ℕ) (M : Matching)
    (hM : IsMatching M) (hf : Function.Injective f) :
    IsMatching (leftCompletion f M) ∧ (leftCompletion f M).length = M.length + 1 ∧
      Extends M (leftCompletion f M) ∧ leastUnused M ∈ domain (leftCompletion f M) := by
  have he := extension_matching f M (leastUnused M) hM hf (leastUnused_spec M).2.1
  refine ⟨he.1, he.2.2.1, he.2.1, ?_⟩
  change leastUnused M ∈ domain (extend f M (leastUnused M))
  rw [he.2.2.2.1]
  simp

private theorem right_properties (g : ℕ → ℕ) (M : Matching)
    (hM : IsMatching M) (hg : Function.Injective g) :
    IsMatching (rightCompletion g M) ∧ (rightCompletion g M).length = M.length + 1 ∧
      Extends M (rightCompletion g M) ∧
      leastUnusedOutput M ∈ range (rightCompletion g M) := by
  have ht := (transpose_matching M).2.1.mpr hM
  have he := extension_matching g (transpose M) (leastUnusedOutput M) ht hg
    (leastUnused_spec (transpose M)).2.1
  refine ⟨(transpose_matching _).2.1.mpr he.1, ?_, ?_, ?_⟩
  · simp [rightCompletion, transpose, extend]
  · intro p hp
    apply List.mem_map.mpr
    refine ⟨p.swap, he.2.1 p.swap (List.mem_map.mpr ⟨p, hp, rfl⟩), ?_⟩
    simp
  · have hr : range (rightCompletion g M) = range M ++ [leastUnusedOutput M] := by
      simp [rightCompletion, range, transpose, extend, List.map_map, Function.comp_def]
    rw [hr]
    simp

private theorem stage_step (f g : ℕ → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g) (s : ℕ)
    (hM : IsMatching (stage f g s)) :
    IsMatching (stage f g (s + 1)) ∧
      (stage f g (s + 1)).length = (stage f g s).length + 1 ∧
      Extends (stage f g s) (stage f g (s + 1)) := by
  rw [stage]
  split_ifs
  · have hp := left_properties f _ hM hf
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  · have hp := right_properties g _ hM hg
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

private theorem extends_domain {M N : Matching} (he : Extends M N)
    {x : ℕ} (hx : x ∈ domain M) : x ∈ domain N := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨p, he p hp, rfl⟩

private theorem extends_range {M N : Matching} (he : Extends M N)
    {y : ℕ} (hy : y ∈ range M) : y ∈ range N := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  exact List.mem_map.mpr ⟨p, he p hp, rfl⟩

private theorem leastUnused_eq {M : Matching} {n : ℕ}
    (hn : n ∉ domain M) (hi : ∀ i < n, i ∈ domain M) : leastUnused M = n := by
  have ha := leastUnused_spec M
  apply le_antisymm
  · by_contra h
    exact hn (ha.2.2 n (by omega))
  · by_contra h
    exact ha.2.1 (hi _ (by omega))

theorem stage_matching (f g : ℕ → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (∀ s, IsMatching (stage f g s) ∧ (stage f g s).length = s) ∧
      (∀ s t, s ≤ t → Extends (stage f g s) (stage f g t)) ∧
      ∀ n x, x < n → x ∈ domain (stage f g (2 * n)) ∧
        x ∈ range (stage f g (2 * n)) := by
  have hm : ∀ s, IsMatching (stage f g s) ∧ (stage f g s).length = s := by
    intro s
    induction s with
    | zero => simp [stage, IsMatching]
    | succ s ih =>
      have hs := stage_step f g hf hg s ih.1
      exact ⟨hs.1, hs.2.1.trans (congrArg (· + 1) ih.2)⟩
  have hmono : ∀ s t, s ≤ t → Extends (stage f g s) (stage f g t) := by
    intro s t hst
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
    clear hst
    induction d with
    | zero => exact fun _ hp => hp
    | succ d ih =>
      intro p hp
      exact (stage_step f g hf hg (s + d) (hm _).1).2.2 p (ih p hp)
  refine ⟨hm, hmono, ?_⟩
  intro n
  induction n with
  | zero => intro x hx; omega
  | succ n ih =>
    have heven : stage f g (2 * n + 1) = leftCompletion f (stage f g (2 * n)) := by
      simp [stage]
    have hodd : stage f g (2 * n + 2) = rightCompletion g (stage f g (2 * n + 1)) := by
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, stage]
      simp
    have hd : ∀ x < n + 1, x ∈ domain (stage f g (2 * n + 1)) := by
      intro x hx
      by_cases hxn : x < n
      · exact extends_domain (hmono _ _ (by omega)) (ih x hxn).1
      · have heq : x = n := by omega
        subst x
        by_cases hn : n ∈ domain (stage f g (2 * n))
        · exact extends_domain (hmono _ _ (by omega)) hn
        · have ha := leastUnused_eq hn (fun i hi => (ih i hi).1)
          rw [heven]
          simpa only [ha] using (left_properties f (stage f g (2 * n)) (hm _).1 hf).2.2.2
    have hr : ∀ x < n + 1, x ∈ range (stage f g (2 * n + 2)) := by
      intro x hx
      by_cases hxn : x < n
      · exact extends_range (hmono _ _ (by omega)) (ih x hxn).2
      · have heq : x = n := by omega
        subst x
        by_cases hn : n ∈ range (stage f g (2 * n + 1))
        · exact extends_range (hmono _ _ (by omega)) hn
        · have ha : leastUnusedOutput (stage f g (2 * n + 1)) = n := by
            apply leastUnused_eq
            · simpa only [(transpose_matching _).2.2.1] using hn
            · intro i hi
              rw [(transpose_matching _).2.2.1]
              exact extends_range (hmono _ _ (by omega)) (ih i hi).2
          rw [hodd]
          simpa only [ha] using (right_properties g (stage f g (2 * n + 1)) (hm _).1 hg).2.2.2
    intro x hx
    have hbound : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [hbound]
    exact ⟨extends_domain (hmono _ _ (by omega)) (hd x hx), hr x hx⟩

theorem readings_mem (f g : ℕ → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (∀ x, (x, forward f g x) ∈ stage f g (2 * (x + 1))) ∧
      ∀ y, (backward f g y, y) ∈ stage f g (2 * (y + 1)) := by
  have hm := stage_matching f g hf hg
  constructor
  · intro x
    exact (matching_lookup _ (hm.1 _).1).2.1 x (hm.2.2 (x + 1) x (by omega)).1
  · intro y
    exact (matching_lookup _ (hm.1 _).1).2.2 y (hm.2.2 (y + 1) y (by omega)).2

theorem inverse_identities (f g : ℕ → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.LeftInverse (backward f g) (forward f g) ∧
      Function.RightInverse (backward f g) (forward f g) ∧
      Function.Bijective (forward f g) := by
  have hm := stage_matching f g hf hg
  have hp := readings_mem f g hf hg
  have hl : Function.LeftInverse (backward f g) (forward f g) := by
    intro x
    let t := max (2 * (x + 1)) (2 * (forward f g x + 1))
    exact functional_right (stage f g t) (hm.1 _).1
      (hm.2.1 _ _ (le_max_right _ _) _ (hp.2 (forward f g x)))
      (hm.2.1 _ _ (le_max_left _ _) _ (hp.1 x))
  have hr : Function.RightInverse (backward f g) (forward f g) := by
    intro y
    let t := max (2 * (y + 1)) (2 * (backward f g y + 1))
    exact functional_left (stage f g t) (hm.1 _).1
      (hm.2.1 _ _ (le_max_right _ _) _ (hp.1 (backward f g y)))
      (hm.2.1 _ _ (le_max_left _ _) _ (hp.2 y))
  exact ⟨hl, hr, hl.injective, hr.surjective⟩

private theorem rec_computable_assist {α σ : Type*} [Primcodable α] [Primcodable σ]
    {b : α → σ} {s : α → ℕ × σ → σ}
    (hb : Computable b) (hs : Computable₂ s) :
    Computable₂ (fun a n => Nat.rec (motive := fun _ => σ) (b a) (fun i v => s a (i, v)) n) := by
  exact Computable.nat_rec Computable.snd (hb.comp Computable.fst)
    (hs.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂

private theorem lookupRaw_computable_assist :
    Computable₂ (fun (M : Matching) x => M.lookup x) :=
  (Primrec.listLookup.comp Primrec.snd Primrec.fst).to_comp

private theorem lookup_computable_assist : Computable₂ lookup :=
  Computable.option_getD lookupRaw_computable_assist (Computable.const 0)

private theorem transpose_computable_assist : Computable transpose := by
  exact (Primrec.list_map Primrec.id
    ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd)).to₂).to_comp

private theorem inverseLookup_computable_assist : Computable₂ inverseLookup :=
  lookup_computable_assist.comp (transpose_computable_assist.comp Computable.fst) Computable.snd

private theorem isNone_computable_assist : Computable (@Option.isNone ℕ) := by
  exact ((Primrec.option_casesOn Primrec.id (Primrec.const true)
    (Primrec.const false).to₂).of_eq (fun o => by cases o <;> rfl)).to_comp

private theorem boundedSearch_computable_assist {α : Type*} [Primcodable α]
    {p : α → ℕ → Bool} (hp : Computable₂ p) :
    Computable₂ (fun a n => boundedSearch (p a) n) := by
  have hs : Computable₂ (fun a (q : ℕ × ℕ) =>
      if p a q.2 then q.2 else q.1 + 1) := by
    exact (Computable.cond
      (hp.comp Computable.fst (Computable.snd.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
      (Computable.succ.comp (Computable.fst.comp Computable.snd))).of_eq
        (fun _ => by simp only [Bool.cond_eq_ite])
  apply (rec_computable_assist (Computable.const 0) hs).of_eq
  rintro ⟨a, n⟩
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun u => if p a u then u else n + 1) ih

private theorem leastUnused_computable_assist : Computable leastUnused := by
  have ht : Computable₂ (fun (M : Matching) x => (M.lookup x).isNone) :=
    isNone_computable_assist.comp lookupRaw_computable_assist
  exact (boundedSearch_computable_assist ht).comp Computable.id
    (Computable.succ.comp Computable.list_length)

private theorem walk_computable_assist (f : ℕ → ℕ) (hf : Computable f) :
    Computable₂ (fun (a : Matching × ℕ) n => walk f a.1 a.2 n) := by
  have hs : Computable₂ (fun (a : Matching × ℕ) (q : ℕ × ℕ) =>
      inverseLookup a.1 (f q.2)) :=
    inverseLookup_computable_assist.comp (Computable.fst.comp Computable.fst)
      (hf.comp (Computable.snd.comp Computable.snd))
  apply (rec_computable_assist Computable.snd hs).of_eq
  rintro ⟨⟨M, x⟩, n⟩
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun y => inverseLookup M (f y)) ih

private theorem escapeIndex_computable_assist (f : ℕ → ℕ) (hf : Computable f) :
    Computable₂ (escapeIndex f) := by
  have ht : Computable₂ (fun (a : Matching × ℕ) n =>
      ((transpose a.1).lookup (f (walk f a.1 a.2 n))).isNone) :=
    isNone_computable_assist.comp
      (lookupRaw_computable_assist.comp
        (transpose_computable_assist.comp (Computable.fst.comp Computable.fst))
        (hf.comp (walk_computable_assist f hf)))
  exact (boundedSearch_computable_assist ht).comp Computable.id
    (Computable.succ.comp (Computable.list_length.comp Computable.fst))

private theorem endpoint_computable_assist (f : ℕ → ℕ) (hf : Computable f) :
    Computable₂ (endpoint f) :=
  hf.comp ((walk_computable_assist f hf).comp Computable.id
    (escapeIndex_computable_assist f hf))

private theorem extend_computable_assist (f : ℕ → ℕ) (hf : Computable f) :
    Computable₂ (extend f) :=
  Computable.list_concat.comp Computable.fst
    (Computable.snd.pair (endpoint_computable_assist f hf))

private theorem leftCompletion_computable_assist (f : ℕ → ℕ) (hf : Computable f) :
    Computable (leftCompletion f) :=
  (extend_computable_assist f hf).comp Computable.id leastUnused_computable_assist

private theorem rightCompletion_computable_assist (g : ℕ → ℕ) (hg : Computable g) :
    Computable (rightCompletion g) :=
  transpose_computable_assist.comp ((extend_computable_assist g hg).comp
    transpose_computable_assist (leastUnused_computable_assist.comp transpose_computable_assist))

theorem construction_computable (f g : ℕ → ℕ)
    (hf : Computable f) (hg : Computable g) :
    Computable (stage f g) ∧ Computable (forward f g) ∧ Computable (backward f g) := by
  have hs : Computable₂ (fun (_ : ℕ) (q : ℕ × Matching) =>
      if q.1 % 2 = 0 then leftCompletion f q.2 else rightCompletion g q.2) := by
    have ht : Computable (fun p : ℕ × (ℕ × Matching) => decide (p.2.1 % 2 = 0)) :=
      Primrec.eq.decide.to_comp.comp
        (Primrec.nat_mod.to_comp.comp (Computable.fst.comp Computable.snd)
          (Computable.const 2)) (Computable.const 0)
    exact (Computable.cond ht
      ((leftCompletion_computable_assist f hf).comp (Computable.snd.comp Computable.snd))
      ((rightCompletion_computable_assist g hg).comp (Computable.snd.comp Computable.snd))).of_eq
        (fun _ => by simp only [Bool.cond_eq_ite, decide_eq_true_eq])
  have hstage : Computable (stage f g) := by
    apply (Computable.nat_rec Computable.id (Computable.const []) hs).of_eq
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        exact congrArg (fun M => if n % 2 = 0 then leftCompletion f M else rightCompletion g M) ih
  have hclock : Computable (fun x : ℕ => 2 * (x + 1)) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.succ
  exact ⟨hstage,
    lookup_computable_assist.comp (hstage.comp hclock) Computable.id,
    inverseLookup_computable_assist.comp (hstage.comp hclock) Computable.id⟩

private theorem respects_transpose {L : Type*} (left right : ℕ → L)
    (M : Matching) (hM : Respects left right M) : Respects right left (transpose M) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (hM q hq).symm

theorem stages_respect {L : Type*} (left right : ℕ → L) (f g : ℕ → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hforward : ∀ x, left x = right (f x))
    (hbackward : ∀ y, right y = left (g y)) :
    ∀ s, Respects left right (stage f g s) := by
  intro s
  induction s with
  | zero => intro p hp; simp [stage] at hp
  | succ s ih =>
    have hM := (stage_matching f g hf hg).1 s |>.1
    rw [stage]
    split_ifs
    · exact extension_respects left right f _ _ hM hf
        (leastUnused_spec _).2.1 ih hforward
    · apply respects_transpose right left
      exact extension_respects right left g _ _ ((transpose_matching _).2.1.mpr hM) hg
        (leastUnused_spec _).2.1 (respects_transpose left right _ ih) hbackward

/-- The actual numerical maps above preserve any labels, including labels in
nonencodable types; the same maps work for every such invariant. -/
theorem labelled_bijection {L : Type*} (left right : ℕ → L) (f g : ℕ → ℕ)
    (hf : Computable f) (hg : Computable g)
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hforward : ∀ x, left x = right (f x))
    (hbackward : ∀ y, right y = left (g y)) :
    Computable (forward f g) ∧ Computable (backward f g) ∧
      Function.LeftInverse (backward f g) (forward f g) ∧
      Function.RightInverse (backward f g) (forward f g) ∧
      ∀ x, left x = right (forward f g x) := by
  have hc := construction_computable f g hf hg
  have hi := inverse_identities f g hfi hgi
  refine ⟨hc.2.1, hc.2.2, hi.1, hi.2.1, ?_⟩
  intro x
  exact stages_respect left right f g hfi hgi hforward hbackward _ _
    ((readings_mem f g hfi hgi).1 x)

end Lemmatheca.ComputabilityTheory.Myhill
