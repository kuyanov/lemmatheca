import Lemmatheca.FiniteRoundComparison.CharacteristicFormulas
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.SetTheory.Cardinal.Basic

/-! A failed infinite-language converse and the exact pure-equality game. -/

namespace Lemmatheca.Entry.FiniteRoundComparison

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.FiniteRoundComparison

/-- The displayed example has one existential, one universal and an inner existential. -/
def rankThreeExample {L : Language.{0, 0}} (R : L.Relations 2) : L.Sentence :=
  (((.rel R ![.var (.inr 0), .var (.inr 1)] : L.BoundedFormula Empty 2) ⊔
    (.rel R ![.var (.inr 1), .var (.inr 2)] : L.BoundedFormula Empty 3).ex).all).ex

theorem rankThreeExample_rank {L : Language.{0, 0}} (R : L.Relations 2) :
    quantifierRank (rankThreeExample R) = 3 := by
  simp only [rankThreeExample, quantifierRank_ex, quantifierRank_sup, quantifierRank]
  decide

inductive UnaryPredicate : ℕ → Type
  | pred (index : ℕ) : UnaryPredicate 1

def unaryLanguage : Language := ⟨fun _ => Empty, UnaryPredicate⟩

instance : unaryLanguage.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

def WithAllPredicates := {S : Set ℕ // S.Finite ∨ S = Set.univ}
abbrev FiniteProfiles := Finset ℕ

instance withAllPredicatesStructure : unaryLanguage.Structure WithAllPredicates where
  funMap := fun f _ => f.elim
  RelMap := fun r a => match r with | .pred n => n ∈ (a 0).val

instance finiteProfilesStructure : unaryLanguage.Structure FiniteProfiles where
  funMap := fun f _ => f.elim
  RelMap := fun r a => match r with | .pred n => n ∈ a 0

/-- The specified extra element realizes all predicates simultaneously. -/
def allPredicatesPoint : WithAllPredicates := ⟨Set.univ, Or.inr rfl⟩

theorem allPredicatesPoint_spec (i : ℕ) :
    Structure.RelMap (L := unaryLanguage) (.pred i) (fun _ => allPredicatesPoint) := by
  trivial

instance : Nonempty WithAllPredicates := ⟨allPredicatesPoint⟩
instance : Nonempty FiniteProfiles := ⟨∅⟩

private def predicateSupport : {n : ℕ} → unaryLanguage.BoundedFormula Empty n → Finset ℕ
  | _, .falsum => ∅
  | _, .equal _ _ => ∅
  | _, .rel (.pred i) _ => {i}
  | _, .imp φ ψ => predicateSupport φ ∪ predicateSupport ψ
  | _, .all φ => predicateSupport φ

private theorem unary_term {n : ℕ} (t : unaryLanguage.Term (Empty ⊕ Fin n)) :
    ∃ i : Fin n, t = .var (.inr i) := by
  cases t with
  | var x =>
    cases x with
    | inl x => exact x.elim
    | inr i => exact ⟨i, rfl⟩
  | func f _ => exact f.elim

private theorem supported_agreement {n : ℕ}
    (φ : unaryLanguage.BoundedFormula Empty n) (hr : quantifierRank φ = 0)
    (a : Fin n → WithAllPredicates) (b : Fin n → FiniteProfiles)
    (heq : ∀ i j, a i = a j ↔ b i = b j)
    (hp : ∀ k ∈ predicateSupport φ, ∀ i, k ∈ (a i).val ↔ k ∈ b i) :
    φ.Realize default a ↔ φ.Realize default b := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    obtain ⟨i, rfl⟩ := unary_term t
    obtain ⟨j, rfl⟩ := unary_term u
    exact heq i j
  | rel R ts =>
    cases R with
    | pred k =>
      choose v hv using fun i => unary_term (ts i)
      have ht : ts = fun i => Term.var (.inr (v i)) := funext hv
      rw [ht]
      exact hp k (Finset.mem_singleton_self k) (v 0)
  | imp φ ψ ihφ ihψ =>
    have hm : max (quantifierRank φ) (quantifierRank ψ) ≤ 0 := Nat.le_of_eq hr
    have hφ := ihφ (Nat.eq_zero_of_le_zero (max_le_iff.mp hm).1) a b heq
      (fun k hk => hp k (Finset.mem_union_left _ hk))
    have hψ := ihψ (Nat.eq_zero_of_le_zero (max_le_iff.mp hm).2) a b heq
      (fun k hk => hp k (Finset.mem_union_right _ hk))
    exact imp_congr hφ hψ
  | all φ _ => simp [quantifierRank] at hr

private theorem qf_from_finite (φ : unaryLanguage.BoundedFormula Empty 1)
    (hr : quantifierRank φ = 0) (b : FiniteProfiles) :
    ∃ a : WithAllPredicates,
      φ.Realize default (fun _ => a) ↔ φ.Realize default (fun _ => b) := by
  let a : WithAllPredicates := ⟨b, Or.inl b.finite_toSet⟩
  exact ⟨a, supported_agreement φ hr (fun _ => a) (fun _ => b)
    (fun _ _ => iff_of_true rfl rfl) (fun _ _ _ => Iff.rfl)⟩

private theorem qf_to_finite (φ : unaryLanguage.BoundedFormula Empty 1)
    (hr : quantifierRank φ = 0) (a : WithAllPredicates) :
    ∃ b : FiniteProfiles,
      φ.Realize default (fun _ => a) ↔ φ.Realize default (fun _ => b) := by
  classical
  let b := (predicateSupport φ).filter (fun k => k ∈ a.val)
  refine ⟨b, supported_agreement φ hr (fun _ => a) (fun _ => b)
    (fun _ _ => iff_of_true rfl rfl) ?_⟩
  intro k hk i
  simp only [b, Finset.mem_filter, hk, true_and]

private theorem closed_rank_one (φ : unaryLanguage.BoundedFormula Empty 0)
    (hr : quantifierRank φ ≤ 1) :
    φ.Realize default (Fin.elim0 : Fin 0 → WithAllPredicates) ↔
      φ.Realize default (Fin.elim0 : Fin 0 → FiniteProfiles) := by
  match φ with
  | .falsum => rfl
  | .equal t _ =>
    obtain ⟨i, _⟩ := unary_term t
    exact i.elim0
  | .rel (.pred _) ts =>
    obtain ⟨i, _⟩ := unary_term (ts 0)
    exact i.elim0
  | .imp φ ψ =>
    exact imp_congr (closed_rank_one φ ((le_max_left _ _).trans hr))
      (closed_rank_one ψ ((le_max_right _ _).trans hr))
  | .all φ =>
    have hq : quantifierRank φ = 0 := by change quantifierRank φ + 1 ≤ 1 at hr; omega
    rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
    constructor
    · intro h b
      obtain ⟨a, hab⟩ := qf_from_finite φ hq b
      have ha := h a
      have hb : Fin.snoc (Fin.elim0 : Fin 0 → WithAllPredicates) a = (fun _ => a) :=
        funext fun i => Fin.lastCases rfl (fun j => j.elim0) i
      rw [hb] at ha
      convert hab.mp ha using 1
      exact funext fun i => Fin.lastCases rfl (fun j => j.elim0) i
    · intro h a
      obtain ⟨b, hab⟩ := qf_to_finite φ hq a
      have hb := h b
      have he : Fin.snoc (Fin.elim0 : Fin 0 → FiniteProfiles) b = (fun _ => b) :=
        funext fun i => Fin.lastCases rfl (fun j => j.elim0) i
      rw [he] at hb
      convert hab.mpr hb using 1
      exact funext fun i => Fin.lastCases rfl (fun j => j.elim0) i
termination_by sizeOf φ
decreasing_by all_goals simp_wf <;> omega

theorem infinite_language_rank_one :
    RankAgreement (L := unaryLanguage) 1
      (Fin.elim0 : Fin 0 → WithAllPredicates) (Fin.elim0 : Fin 0 → FiniteProfiles) := by
  intro φ hφ
  have hh := closed_rank_one (tupleBounded φ)
    (by rw [quantifierRank_tupleBounded]; exact hφ)
  simpa only [tupleBounded, Formula.realize_relabel_sumInr] using hh

theorem infinite_language_unanswered :
    ∀ b : FiniteProfiles,
      ¬ AtomicMatch (L := unaryLanguage) (Fin.snoc (Fin.elim0 : Fin 0 → WithAllPredicates)
        allPredicatesPoint) (Fin.snoc (Fin.elim0 : Fin 0 → FiniteProfiles) b) := by
  intro b h
  obtain ⟨i, hi⟩ := b.exists_notMem
  have hh := h (.inr ⟨1, UnaryPredicate.pred i, fun _ => 0⟩)
  change i ∈ (Set.univ : Set ℕ) ↔ i ∈ b at hh
  exact hi (hh.mp (Set.mem_univ _))

theorem infinite_language_no_strategy :
    ¬ Nonempty (WinningStrategy (L := unaryLanguage) 1
      (Fin.elim0 : Fin 0 → WithAllPredicates) (Fin.elim0 : Fin 0 → FiniteProfiles)) := by
  intro h
  have hw := (strategy_iff_wins 1 _ _).mp h
  obtain ⟨b, hb⟩ := hw.2.1 allPredicatesPoint
  exact infinite_language_unanswered b hb

private abbrev Remainder {M : Type} {n : ℕ} (a : Fin n → M) :=
  {x : M // x ∉ Set.range a}

private theorem empty_atomic {M N : Type} [Language.empty.Structure M]
    [Language.empty.Structure N] {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : ∀ i j, a i = a j ↔ b i = b j) : AtomicMatch (L := Language.empty) a b := by
  exact (atomicMatch_iff a b).mpr ⟨h, fun _ R => R.elim⟩

private theorem match_symm {L : Language} {M N : Type} [L.Structure M] [L.Structure N]
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (h : AtomicMatch (L := L) a b) :
    AtomicMatch (L := L) b a := fun i => (h i).symm

private theorem empty_snoc_match {M N : Type} [Language.empty.Structure M]
    [Language.empty.Structure N] {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : AtomicMatch (L := Language.empty) a b) (x : M) (y : N)
    (hxy : ∀ i, x = a i ↔ y = b i) :
    AtomicMatch (L := Language.empty) (Fin.snoc a x) (Fin.snoc b y) := by
  apply empty_atomic
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · exact iff_of_true rfl rfl
    · simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hxy j
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last, eq_comm] using hxy i
    · simpa only [Fin.snoc_castSucc] using ((atomicMatch_iff a b).mp h).1 i j

private theorem remove_embedding {M : Type} {n k : ℕ} (a : Fin n → M) (x : M)
    (e : Fin (k + 1) ↪ Remainder a) : Nonempty (Fin k ↪ Remainder (Fin.snoc a x)) := by
  classical
  obtain ⟨skip, hskip⟩ : ∃ skip : Fin k ↪ Fin (k + 1), ∀ i, (e (skip i)).val ≠ x := by
    by_cases hx : ∃ j, (e j).val = x
    · obtain ⟨j, hj⟩ := hx
      refine ⟨j.succAboveEmb, fun i hi => ?_⟩
      exact Fin.succAbove_ne j i (e.injective (Subtype.ext (hi.trans hj.symm)))
    · refine ⟨Fin.castLEEmb (Nat.le_succ k), fun i hi => hx ⟨_, hi⟩⟩
  refine ⟨⟨fun i => ⟨(e (skip i)).val, ?_⟩, ?_⟩⟩
  · rw [Fin.range_snoc]
    rintro (heq | hold)
    · exact hskip i heq
    · exact (e (skip i)).property hold
  · intro i j hij
    exact skip.injective (e.injective (Subtype.ext
      (congrArg (fun z : Remainder (Fin.snoc a x) => z.val) hij)))

private theorem fresh_response {M N : Type} [Language.empty.Structure M]
    [Language.empty.Structure N] {n k : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : AtomicMatch (L := Language.empty) a b) (e : Fin (k + 1) ↪ Remainder b) (x : M) :
    ∃ y : N, AtomicMatch (L := Language.empty) (Fin.snoc a x) (Fin.snoc b y) := by
  classical
  by_cases hx : x ∈ Set.range a
  · obtain ⟨i, rfl⟩ := hx
    exact ⟨b i, empty_snoc_match h _ _ (fun j => ((atomicMatch_iff a b).mp h).1 i j)⟩
  · refine ⟨(e 0).val, empty_snoc_match h _ _ (fun i => ?_)⟩
    exact iff_of_false (fun hi => hx ⟨i, hi.symm⟩)
      (fun hi => (e 0).property ⟨i, hi.symm⟩)

private theorem wins_big {M N : Type} [Language.empty.Structure M]
    [Language.empty.Structure N] (k : ℕ) {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : AtomicMatch (L := Language.empty) a b)
    (hM : Nonempty (Fin k ↪ Remainder a)) (hN : Nonempty (Fin k ↪ Remainder b)) :
    Wins (L := Language.empty) k a b := by
  induction k generalizing n with
  | zero => exact h
  | succ k ih =>
    obtain ⟨eM⟩ := hM
    obtain ⟨eN⟩ := hN
    refine ⟨h, fun x => ?_, fun y => ?_⟩
    · obtain ⟨y, hxy⟩ := fresh_response h eN x
      exact ⟨y, ih _ _ hxy (remove_embedding a x eM) (remove_embedding b y eN)⟩
    · obtain ⟨x, hyx⟩ := fresh_response (match_symm h) eM y
      exact ⟨x, ih _ _ (match_symm hyx) (remove_embedding a x eM) (remove_embedding b y eN)⟩

private theorem wins_symm {L : Language} {M N : Type} [L.Structure M] [L.Structure N]
    {k n : ℕ} {a : Fin n → M} {b : Fin n → N} (h : Wins (L := L) k a b) :
    Wins (L := L) k b a := by
  induction k generalizing n with
  | zero => exact match_symm h
  | succ k ih =>
    refine ⟨match_symm h.1, fun y => ?_, fun x => ?_⟩
    · obtain ⟨x, hx⟩ := h.2.2 y
      exact ⟨x, ih hx⟩
    · obtain ⟨y, hy⟩ := h.2.1 x
      exact ⟨y, ih hy⟩

private theorem wins_down {L : Language} {M N : Type} [L.Structure M] [L.Structure N]
    {j k n : ℕ} {a : Fin n → M} {b : Fin n → N} (hjk : j ≤ k) :
    Wins (L := L) k a b → Wins (L := L) j a b := by
  induction k, hjk using Nat.le_induction with
  | base => exact id
  | succ k _ ih => exact fun h => ih (wins_mono h)

private theorem wins_embedding {M N : Type} [Language.empty.Structure M]
    [Language.empty.Structure N] {k n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : Wins (L := Language.empty) k a b) (hM : Nonempty (Fin k ↪ Remainder a)) :
    Nonempty (Fin k ↪ Remainder b) := by
  classical
  induction k generalizing n with
  | zero => exact ⟨Function.Embedding.ofIsEmpty⟩
  | succ k ih =>
    obtain ⟨e⟩ := hM
    let x := (e 0).val
    obtain ⟨y, hy⟩ := h.2.1 x
    have hyfresh : y ∉ Set.range b := by
      rintro ⟨i, hi⟩
      have heq := ((atomicMatch_iff _ _).mp (wins_atomic hy)).1 (Fin.last n) i.castSucc
      have heq' : x = a i ↔ y = b i := by
        simpa only [Fin.snoc_last, Fin.snoc_castSucc] using heq
      have hx : x = a i := heq'.mpr hi.symm
      exact (e 0).property ⟨i, hx.symm⟩
    obtain ⟨rest⟩ := ih hy (remove_embedding a x e)
    let lifted : Fin k ↪ Remainder b := {
      toFun := fun i => ⟨(rest i).val, fun hb => (rest i).property
        (by obtain ⟨j, hj⟩ := hb; exact ⟨j.castSucc, by simpa only [Fin.snoc_castSucc] using hj⟩)⟩
      inj' := fun i j hij => rest.injective (Subtype.ext (congrArg (fun z : Remainder b => z.val) hij)) }
    have hnot : (⟨y, hyfresh⟩ : Remainder b) ∉ Set.range lifted := by
      rintro ⟨i, hi⟩
      apply (rest i).property
      have hv : (rest i).val = y := congrArg (fun z : Remainder b => z.val) hi
      exact ⟨Fin.last n, by simpa only [Fin.snoc_last] using hv.symm⟩
    exact ⟨Fin.Embedding.snoc lifted hnot⟩

private theorem fin_embedding_card (X : Type) (k : ℕ) :
    Nonempty (Fin k ↪ X) ↔ (k : Cardinal) ≤ Cardinal.mk X := by
  rw [← Cardinal.mk_fin k, Cardinal.le_def]

private theorem small_remainders {M N : Type} [Language.empty.Structure M]
    [Language.empty.Structure N] {k n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : Wins (L := Language.empty) k a b) (hM : ¬ Nonempty (Fin k ↪ Remainder a)) :
    ∃ r : ℕ, r < k ∧ Nonempty (Remainder a ≃ Fin r) ∧
      Nonempty (Remainder b ≃ Fin r) := by
  have hlt : Cardinal.mk (Remainder a) < (k : Cardinal) :=
    lt_of_not_ge (fun hh => hM ((fin_embedding_card _ k).mpr hh))
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp (hlt.trans Cardinal.natCast_lt_aleph0)
  have hrk : r < k := by rw [hr] at hlt; exact_mod_cast hlt
  have hlow : (r : Cardinal) ≤ Cardinal.mk (Remainder b) := by
    apply (fin_embedding_card _ r).mp
    exact wins_embedding (wins_down hrk.le h) ((fin_embedding_card _ r).mpr hr.ge)
  have hupp : Cardinal.mk (Remainder b) < (r + 1 : ℕ) := by
    apply lt_of_not_ge
    intro he
    have ha := wins_embedding (wins_down (Nat.succ_le_of_lt hrk) (wins_symm h))
      ((fin_embedding_card _ (r + 1)).mpr he)
    have hc := (fin_embedding_card _ (r + 1)).mp ha
    rw [hr] at hc
    exact (by exact_mod_cast Nat.lt_succ_self r : (r : Cardinal) < (r + 1 : ℕ)).not_ge hc
  have hb : Cardinal.mk (Remainder b) = (r : Cardinal) :=
    le_antisymm (Cardinal.lt_natCast_add_one_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using hupp)) hlow
  exact ⟨r, hrk, Cardinal.mk_eq_nat_iff.mp hr, Cardinal.mk_eq_nat_iff.mp hb⟩

private theorem wins_equiv {M N : Type} [Language.empty.Structure M]
    [Language.empty.Structure N] (e : M ≃ N) (k : ℕ) {n : ℕ}
    (a : Fin n → M) (b : Fin n → N) (he : ∀ i, e (a i) = b i) :
    Wins (L := Language.empty) k a b := by
  induction k generalizing n with
  | zero =>
    exact empty_atomic a b
      (fun i j => by rw [← he i, ← he j]; exact e.injective.eq_iff.symm)
  | succ k ih =>
    have ha : AtomicMatch (L := Language.empty) a b := empty_atomic a b
      (fun i j => by rw [← he i, ← he j]; exact e.injective.eq_iff.symm)
    refine ⟨ha, fun x => ⟨e x, ih _ _ (fun i => ?_)⟩,
      fun y => ⟨e.symm y, ih _ _ (fun i => ?_)⟩⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]
      · simpa only [Fin.snoc_castSucc] using he i
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using e.apply_symm_apply y
      · simpa only [Fin.snoc_castSucc] using he i

private theorem wins_remainder_equiv {M N : Type} [Language.empty.Structure M]
    [Language.empty.Structure N] {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : AtomicMatch (L := Language.empty) a b) (er : Remainder a ≃ Remainder b) (k : ℕ) :
    Wins (L := Language.empty) k a b := by
  classical
  obtain ⟨p, hd, hr, hp⟩ := (atomicMatch_iff_partialIso a b).mp h
  let f : Set.range a → Set.range b := fun x =>
    ⟨p.toFun ⟨x.val, hd.symm ▸ x.property⟩, hr ▸ Set.mem_range_self _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have he := p.injective (congrArg (fun z : Set.range b => z.val) hxy)
      exact congrArg (fun z : p.dom => z.val) he
    · intro y
      have hy : y.val ∈ Set.range p.toFun := by rw [hr]; exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨⟨x.val, hd ▸ x.property⟩, Subtype.ext hx⟩
  let e0 : Set.range a ≃ Set.range b := Equiv.ofBijective f hf
  let e := (Equiv.Set.compl e0).symm er
  apply wins_equiv e.val k a b
  intro i
  have he := e.property (⟨a i, Set.mem_range_self i⟩ : Set.range a)
  obtain ⟨hi, hpi⟩ := hp i
  exact he.trans hpi

/-- The precise finite/infinite remainder condition in the pure-equality game. -/
theorem equality_game_iff {M N : Type} [Language.empty.Structure M]
    [Language.empty.Structure N] [Nonempty M] [Nonempty N]
    (k : ℕ) {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : AtomicMatch (L := Language.empty) a b) :
    Wins (L := Language.empty) k a b ↔
      (∃ r : ℕ, r < k ∧
        Nonempty ({x : M // x ∉ Set.range a} ≃ Fin r) ∧
        Nonempty ({y : N // y ∉ Set.range b} ≃ Fin r)) ∨
      (Nonempty (Fin k ↪ {x : M // x ∉ Set.range a}) ∧
        Nonempty (Fin k ↪ {y : N // y ∉ Set.range b})) := by
  constructor
  · intro hw
    by_cases hM : Nonempty (Fin k ↪ Remainder a)
    · by_cases hN : Nonempty (Fin k ↪ Remainder b)
      · exact Or.inr ⟨hM, hN⟩
      · obtain ⟨r, hr, hb, ha⟩ := small_remainders (wins_symm hw) hN
        exact Or.inl ⟨r, hr, ha, hb⟩
    · exact Or.inl (small_remainders hw hM)
  · rintro (⟨r, _, ⟨eM⟩, ⟨eN⟩⟩ | ⟨hM, hN⟩)
    · exact wins_remainder_equiv a b h (eM.trans eN.symm) k
    · exact wins_big k a b h hM hN

theorem equality_large_sets {M N : Type} [Language.empty.Structure M]
    [Language.empty.Structure N] [Nonempty M] [Nonempty N]
    (k : ℕ) (hM : Nonempty (Fin k ↪ M)) (hN : Nonempty (Fin k ↪ N)) :
    RankAgreement (L := Language.empty) k
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  obtain ⟨eM⟩ := hM
  obtain ⟨eN⟩ := hN
  apply wins_preserves_formulas
  apply wins_big k _ _ (empty_atomic _ _ (fun i => i.elim0))
  · exact ⟨⟨fun i => ⟨eM i, by rintro ⟨j, _⟩; exact j.elim0⟩,
      fun i j hij => eM.injective (congrArg Subtype.val hij)⟩⟩
  · exact ⟨⟨fun i => ⟨eN i, by rintro ⟨j, _⟩; exact j.elim0⟩,
      fun i j hij => eN.injective (congrArg Subtype.val hij)⟩⟩

end Lemmatheca.Entry.FiniteRoundComparison
