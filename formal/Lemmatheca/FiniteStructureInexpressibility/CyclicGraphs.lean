import Lemmatheca.FiniteStructureInexpressibility.FiniteOrders
import Lemmatheca.FiniteStructureInexpressibility.GraphTranslation
import Lemmatheca.FiniteStructureInexpressibility.CyclicArithmetic

/-! Finite graph obstructions and the bounded-size exception, using the existing finite walks. -/

namespace Lemmatheca.ModelTheory.FiniteStructureInexpressibility

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.FiniteRoundComparison

def IsGraph {M : Type} (r : M → M → Prop) : Prop := Std.Symm r ∧ Std.Irrefl r

private theorem walk_append {M : Type} {r : M → M → Prop} {m n : ℕ} {a b c : M}
    (h : ExpressiveLimits.Walk r m a b) (h' : ExpressiveLimits.Walk r n b c) :
    ExpressiveLimits.Walk r (m + n) a c := by
  induction m generalizing a with
  | zero => simpa only [Nat.zero_add] using (h ▸ h')
  | succ m ih =>
    obtain ⟨d, had, hdb⟩ := h
    simpa only [Nat.succ_add] using
      (show ExpressiveLimits.Walk r ((m + n) + 1) a c from ⟨d, had, ih hdb⟩)

private theorem walk_reverse {M : Type} {r : M → M → Prop} (hr : Std.Symm r)
    {n : ℕ} {a b : M} (h : ExpressiveLimits.Walk r n a b) :
    ExpressiveLimits.Walk r n b a := by
  induction n generalizing a with
  | zero => exact h.symm
  | succ n ih =>
    obtain ⟨c, hac, hcb⟩ := h
    exact walk_append (ih hcb) (show ExpressiveLimits.Walk r 1 c a from ⟨a, hr.symm a c hac, rfl⟩)

theorem reachability_equivalence {M : Type} (r : M → M → Prop) (hr : Std.Symm r) :
    Equivalence (ExpressiveLimits.Reachable r) := by
  refine ⟨fun a => ⟨0, rfl⟩, ?_, ?_⟩
  · rintro a b ⟨n, hn⟩
    exact ⟨n, walk_reverse hr hn⟩
  · rintro a b c ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, walk_append hm hn⟩

theorem finite_graph_connectedness_not_definable :
    ¬ ∃ σ : ExpressiveLimits.language.Sentence,
      ∀ (M : Type) [Finite M] [Nonempty M] (r : M → M → Prop),
        Std.Symm r → Std.Irrefl r →
        (@Sentence.Realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) σ ↔
          ∀ a b, ExpressiveLimits.Reachable r a b) := by
  rintro ⟨σ, hσ⟩
  let τ : ExpressiveLimits.language.Sentence := graphTranslation σ
  let φ : ExpressiveLimits.language.Formula (Fin 0) := τ.relabel Empty.elim
  let k := quantifierRank φ
  let m := 2 * (2 ^ k + 3)
  let n := m + 1
  have heval (q : ℕ) :
      @Formula.Realize ExpressiveLimits.language (Fin q) (orderStructure q) _ φ Fin.elim0 ↔
      @Sentence.Realize ExpressiveLimits.language (Fin q) (orderStructure q) τ := by
    let := orderStructure q
    dsimp only [φ]
    rw [Formula.realize_relabel]
    have hv : (Fin.elim0 : Fin 0 → Fin q) ∘ (Empty.elim : Empty → Fin 0) = default :=
      Subsingleton.elim _ _
    rw [hv]
    rfl
  have hp (q : ℕ) (hq : 3 ≤ q) :
      @Sentence.Realize ExpressiveLimits.language (Fin q) (orderStructure q) τ ↔ Odd q := by
    let : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
    obtain ⟨hs, hi⟩ := graphEdge_is_graph q hq
    have hh := hσ (Fin q) (GraphEdge (fun x y : Fin q => x < y)) hs hi
    have ht := graphTranslation_realize (fun x y : Fin q => x < y) σ
      (default : Empty → Fin q) (default : Fin 0 → Fin q)
    exact ht.symm.trans (hh.trans (cyclic_graph_connected_iff q hq))
  have hpow : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hm : 3 ≤ m := by dsimp [m]; omega
  have hn : 3 ≤ n := by dsimp [n]; omega
  have hmrank : 2 ^ k - 1 ≤ m := by dsimp [m]; omega
  have hnrank : 2 ^ k - 1 ≤ n := by dsimp [n]; omega
  have ha := large_orders k m n (by omega) (by omega) hmrank hnrank φ le_rfl
  have ho : Odd n := by
    dsimp [n, m]
    exact ⟨2 ^ k + 3, by omega⟩
  have hτn := (hp n hn).mpr ho
  have hτm := (heval m).mp (ha.mpr ((heval n).mpr hτn))
  obtain ⟨d, hd⟩ := (hp m hm).mp hτm
  dsimp [m] at hd
  omega

theorem finite_graph_reachability_not_definable :
    ¬ ∃ ρ : ExpressiveLimits.language.Formula (Fin 2),
      ∀ (M : Type) [Finite M] [Nonempty M] (r : M → M → Prop),
        Std.Symm r → Std.Irrefl r → ∀ a b,
        (@Formula.Realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) (Fin 2) ρ ![a,b] ↔
          ExpressiveLimits.Reachable r a b) := by
  rintro ⟨ρ, hρ⟩
  apply finite_graph_connectedness_not_definable
  let σ : ExpressiveLimits.language.Sentence := (tupleBounded ρ).alls
  refine ⟨σ, ?_⟩
  intro M _ _ r hr hi
  let := ExpressiveLimits.relationStructure r
  change ((tupleBounded ρ).alls).Realize (default : Empty → M) ↔ _
  rw [BoundedFormula.realize_alls]
  simp only [tupleBounded_realize]
  have hp (a : Fin 2 → M) : a = ![a 0, a 1] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h a b
    exact (hρ M r hr hi a b).mp (h ![a, b])
  · intro h a
    rw [hp a]
    exact (hρ M r hr hi (a 0) (a 1)).mpr (h (a 0) (a 1))

/-- A reachable pair in a finite relation has a walk shorter than the number of vertices. -/
theorem short_walk {M : Type} [Finite M] [Nonempty M] (r : M → M → Prop)
    {a b : M} (h : ExpressiveLimits.Reachable r a b) :
    ∃ s : ℕ, s < Nat.card M ∧ ExpressiveLimits.Walk r s a b := by
  classical
  let s := Nat.find h
  have hs : ExpressiveLimits.Walk r s a b := Nat.find_spec h
  obtain ⟨v, hv0, hvn, hv⟩ := (ExpressiveLimits.walk_iff_tuple s a b).mp hs
  let g : ℕ → M := fun i => v ⟨min i s, by omega⟩
  have gval (i : Fin (s + 1)) : g i.val = v i := by
    dsimp [g]
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  have gzero : g 0 = a := (gval 0).trans hv0
  have glast : g s = b := (gval (Fin.last s)).trans hvn
  have edge (i : ℕ) (hi : i < s) : r (g i) (g (i + 1)) := by
    have h₀ := gval ((⟨i, hi⟩ : Fin s).castSucc)
    have h₁ := gval ((⟨i, hi⟩ : Fin s).succ)
    exact h₀.symm ▸ h₁.symm ▸ hv (⟨i, hi⟩ : Fin s)
  have along (f : ℕ → M) (n : ℕ) (hf : ∀ i < n, r (f i) (f (i + 1))) :
      ExpressiveLimits.Walk r n (f 0) (f n) := by
    induction n generalizing f with
    | zero => rfl
    | succ n ih =>
      exact ⟨f 1, hf 0 (by omega), ih (fun i => f (i + 1))
        (fun i hi => hf (i + 1) (by omega))⟩
  have segment (i j : ℕ) (hij : i ≤ j) (hjs : j ≤ s) :
      ExpressiveLimits.Walk r (j - i) (g i) (g j) := by
    have hh := along (fun k => g (i + k)) (j - i) (by
      intro k hk
      have he := edge (i + k) (by omega)
      simpa only [Nat.add_assoc] using he)
    simpa only [Nat.add_zero, Nat.add_sub_of_le hij] using hh
  have bad (i j : Fin (s + 1)) (he : v i = v j) (hlt : i.val < j.val) : False := by
    have hp := segment 0 i.val (Nat.zero_le _) (by omega)
    have hq := segment j.val s (by omega) le_rfl
    have heq : g i.val = g j.val := (gval i).trans (he.trans (gval j).symm)
    have hw := walk_append hp (heq.symm ▸ hq)
    rw [gzero, glast] at hw
    have hm : s ≤ (i.val - 0) + (s - j.val) := Nat.find_min' h hw
    omega
  have hi : Function.Injective v := by
    intro i j he
    by_contra hne
    have hij : i.val ≠ j.val := fun hval => hne (Fin.ext hval)
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact bad i j he hlt
    · exact bad j i he.symm hgt
  have hc := Nat.card_le_card_of_injective v hi
  simp only [Nat.card_fin] at hc
  exact ⟨s, by omega, hs⟩

/-- Universally close the finite disjunction of the previously constructed length formulas. -/
noncomputable def boundedConnectednessSentence (N : ℕ) : ExpressiveLimits.language.Sentence :=
  (BoundedFormula.iSup (fun s : Fin N => tupleBounded (ExpressiveLimits.pathFormula s.val))).alls

theorem boundedConnectednessSentence_realize {M : Type} [Finite M] [Nonempty M]
    (N : ℕ) (_hN : 0 < N) (r : M → M → Prop) (hcard : Nat.card M ≤ N) :
    @Sentence.Realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) (boundedConnectednessSentence N) ↔
      ∀ a b, ExpressiveLimits.Reachable r a b := by
  classical
  let := ExpressiveLimits.relationStructure r
  change ((BoundedFormula.iSup (fun s : Fin N =>
    tupleBounded (ExpressiveLimits.pathFormula s.val))).alls).Realize (default : Empty → M) ↔ _
  rw [BoundedFormula.realize_alls]
  simp only [BoundedFormula.realize_iSup]
  simp only [tupleBounded_realize]
  have ht (s : ℕ) (a b : M) :
      (ExpressiveLimits.pathFormula s).Realize ![a, b] ↔ ExpressiveLimits.Walk r s a b :=
    ExpressiveLimits.pathFormula_realize s a b
  have hp (a : Fin 2 → M) : a = ![a 0, a 1] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h a b
    obtain ⟨s, hs⟩ := h ![a, b]
    exact ⟨s.val, (ht s.val a b).mp hs⟩
  · intro h a
    obtain ⟨s, hs, hw⟩ := short_walk r (h (a 0) (a 1))
    refine ⟨⟨s, hs.trans_le hcard⟩, ?_⟩
    rw [hp a]
    exact (ht s (a 0) (a 1)).mpr hw

end Lemmatheca.ModelTheory.FiniteStructureInexpressibility
