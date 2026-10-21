import Lemmatheca.PropositionalNormalForms.PropositionalNormalForms
import Mathlib.Data.Finset.Powerset

open Lemmatheca.MathematicalLogic.Propositional

/-! Resolution on finite sets of the shared propositional literals. -/
namespace Lemmatheca.ProofTheory.Resolution
universe u
variable {α : Type u} [DecidableEq α]
abbrev Clause (α : Type u) := Finset (PropLiteral α)
abbrev ClauseSet (α : Type u) := Finset (Clause α)
def pos (p : α) : PropLiteral α := ⟨p, true⟩
def neg (p : α) : PropLiteral α := ⟨p, false⟩
def LiteralSat (v : Valuation α) (l : PropLiteral α) : Prop := v l.atom = l.positive
def ClauseSat (v : Valuation α) (C : Clause α) : Prop := ∃ l ∈ C, LiteralSat v l
def Models (v : Valuation α) (Γ : ClauseSet α) : Prop := ∀ C ∈ Γ, ClauseSat v C
def Sat (Γ : ClauseSet α) : Prop := ∃ v, Models v Γ
def ofCnf (L : List (List (PropLiteral α))) : ClauseSet α :=
  (L.map List.toFinset).toFinset
def resolvent (p : α) (C D : Clause α) : Clause α := C.erase (pos p) ∪ D.erase (neg p)
inductive Derives (Γ : ClauseSet α) : Clause α → Prop
  | premise {C} : C ∈ Γ → Derives Γ C
  | resolve {C D} (p : α) : pos p ∈ C → neg p ∈ D →
      Derives Γ C → Derives Γ D → Derives Γ (resolvent p C D)
def Tautological (C : Clause α) : Prop := ∃ p, pos p ∈ C ∧ neg p ∈ C
def neutral (p : α) (Γ : ClauseSet α) : ClauseSet α :=
  Γ.filter (fun C => pos p ∉ C ∧ neg p ∉ C)
def positive (p : α) (Γ : ClauseSet α) : ClauseSet α :=
  Γ.filter (fun C => pos p ∈ C ∧ neg p ∉ C)
def negative (p : α) (Γ : ClauseSet α) : ClauseSet α :=
  Γ.filter (fun C => neg p ∈ C ∧ pos p ∉ C)
def eliminate (p : α) (Γ : ClauseSet α) : ClauseSet α :=
  neutral p Γ ∪ (positive p Γ).biUnion (fun C =>
    (negative p Γ).image (fun D => resolvent p C D))
def Supported (S : Finset α) (Γ : ClauseSet α) : Prop :=
  ∀ C ∈ Γ, ∀ l ∈ C, l.atom ∈ S
def support (Γ : ClauseSet α) : Finset α := Γ.biUnion (fun C => C.image PropLiteral.atom)
def Closed (Γ : ClauseSet α) : Prop :=
  ∀ C ∈ Γ, ∀ D ∈ Γ, ∀ p, pos p ∈ C → neg p ∈ D → resolvent p C D ∈ Γ
def literals (S : Finset α) : Finset (PropLiteral α) := S.biUnion (fun p => {pos p, neg p})
def availableClauses (S : Finset α) : Finset (Clause α) := (literals S).powerset
def Step (Γ Δ : ClauseSet α) : Prop :=
  ∃ C ∈ Γ, ∃ D ∈ Γ, ∃ p, pos p ∈ C ∧ neg p ∈ D ∧
    resolvent p C D ∉ Γ ∧ Δ = insert (resolvent p C D) Γ

omit [DecidableEq α] in
theorem literal_formula (v : Valuation α) (l : PropLiteral α) :
    eval v (literalFormula l) = true ↔ LiteralSat v l := by
  cases l with
  | mk a b =>
    cases b <;> cases hv : v a <;> simp [literalFormula, eval, LiteralSat, hv]
theorem list_clause (v : Valuation α) (L : List (PropLiteral α)) :
    eval v (clauseFormula L) = true ↔ ClauseSat v L.toFinset := by
  have hf := eval_finiteDisj_false v (L.map literalFormula)
  have hn := not_congr hf
  simpa [clauseFormula, ClauseSat, literal_formula] using hn
theorem list_cnf (v : Valuation α) (L : List (List (PropLiteral α))) :
    eval v (cnfFormula L) = true ↔ Models v (ofCnf L) := by
  simp [cnfFormula, eval_finiteConj, Models, ofCnf, list_clause]
omit [DecidableEq α] in
theorem empty_cases (v : Valuation α) :
    ¬ ClauseSat v ∅ ∧ Models v ∅ ∧ ¬ Sat ({∅} : ClauseSet α) := by
  simp [ClauseSat, Models, Sat]
omit [DecidableEq α] in
theorem tautological_true (C : Clause α) (h : Tautological C) (v : Valuation α) :
    ClauseSat v C := by
  obtain ⟨p, hp, hn⟩ := h
  cases hv : v p with
  | false => exact ⟨neg p, hn, by simp [LiteralSat, neg, hv]⟩
  | true => exact ⟨pos p, hp, by simp [LiteralSat, pos, hv]⟩
theorem compose {Γ Δ : ClauseSet α} {C : Clause α}
    (h : ∀ D ∈ Δ, Derives Γ D) (d : Derives Δ C) : Derives Γ C := by
  induction d with
  | premise hD => exact h _ hD
  | resolve p hp hn _ _ ihC ihD => exact Derives.resolve p hp hn ihC ihD
theorem resolve_sound {p : α} {C D : Clause α} (v : Valuation α)
    (hC : ClauseSat v C) (hD : ClauseSat v D) : ClauseSat v (resolvent p C D) := by
  cases hv : v p with
  | false =>
    obtain ⟨l, hl, hs⟩ := hC
    refine ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hl⟩), hs⟩
    intro he
    subst l
    simp [LiteralSat, pos, hv] at hs
  | true =>
    obtain ⟨l, hl, hs⟩ := hD
    refine ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl⟩), hs⟩
    intro he
    subst l
    simp [LiteralSat, neg, hv] at hs
theorem sound {Γ : ClauseSet α} {C : Clause α} (d : Derives Γ C)
    (v : Valuation α) (h : Models v Γ) : ClauseSat v C := by
  induction d with
  | premise hC => exact h _ hC
  | resolve p _ _ _ _ ihC ihD => exact resolve_sound v ihC ihD
theorem refutation_unsat {Γ : ClauseSet α} (d : Derives Γ ∅) : ¬ Sat Γ := by
  rintro ⟨v, hv⟩
  exact (empty_cases v).1 (sound d v hv)
theorem add_resolvent_models {Γ : ClauseSet α} {C D : Clause α} {p : α}
    (hC : C ∈ Γ) (hD : D ∈ Γ) (v : Valuation α) :
    Models v (insert (resolvent p C D) Γ) ↔ Models v Γ := by
  constructor
  · intro h E hE
    exact h E (Finset.mem_insert_of_mem hE)
  · intro h E hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact resolve_sound v (h C hC) (h D hD)
    · exact h E hE
theorem elimination_derivable (p : α) (Γ : ClauseSet α) :
    ∀ C ∈ eliminate p Γ, Derives Γ C := by
  intro E hE
  rcases Finset.mem_union.mp hE with hE | hE
  · exact Derives.premise (Finset.mem_filter.mp hE).1
  · obtain ⟨C, hC, hE⟩ := Finset.mem_biUnion.mp hE
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hE
    have hCp := (Finset.mem_filter.mp hC).2.1
    have hDn := (Finset.mem_filter.mp hD).2.1
    exact Derives.resolve p hCp hDn
      (.premise (Finset.mem_filter.mp hC).1) (.premise (Finset.mem_filter.mp hD).1)
omit [DecidableEq α] in
private theorem atom_ne_of_signs {l : PropLiteral α} {p : α}
    (hp : l ≠ pos p) (hn : l ≠ neg p) : l.atom ≠ p := by
  rcases l with ⟨a, b⟩
  cases b <;> simp_all [pos, neg]

private theorem clause_update (p : α) (v : Valuation α) (b : Bool) (C : Clause α)
    (hp : pos p ∉ C) (hn : neg p ∉ C) :
    ClauseSat (Function.update v p b) C ↔ ClauseSat v C := by
  have he (l : PropLiteral α) (hl : l ∈ C) :
      LiteralSat (Function.update v p b) l ↔ LiteralSat v l := by
    have hne := atom_ne_of_signs (fun h => hp (h ▸ hl)) (fun h => hn (h ▸ hl))
    simp [LiteralSat, Function.update_of_ne hne]
  constructor <;> rintro ⟨l, hl, ht⟩
  · exact ⟨l, hl, (he l hl).mp ht⟩
  · exact ⟨l, hl, (he l hl).mpr ht⟩

omit [DecidableEq α] in
private theorem clause_mono {v : Valuation α} {C D : Clause α}
    (h : C ⊆ D) (hc : ClauseSat v C) : ClauseSat v D := by
  obtain ⟨l, hl, ht⟩ := hc
  exact ⟨l, h hl, ht⟩

theorem elimination_support {S : Finset α} {Γ : ClauseSet α}
    (h : Supported S Γ) (p : α) : Supported (S.erase p) (eliminate p Γ) := by
  intro E hE l hl
  rcases Finset.mem_union.mp hE with hE | hE
  · obtain ⟨hC, hp, hn⟩ := Finset.mem_filter.mp hE
    exact Finset.mem_erase.mpr ⟨
      atom_ne_of_signs (fun he => hp (he ▸ hl)) (fun he => hn (he ▸ hl)), h E hC l hl⟩
  · obtain ⟨C, hC, hE⟩ := Finset.mem_biUnion.mp hE
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hCΓ, _, hCn⟩ := Finset.mem_filter.mp hC
    obtain ⟨hDΓ, _, hDp⟩ := Finset.mem_filter.mp hD
    rcases Finset.mem_union.mp hl with hl | hl
    · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
      exact Finset.mem_erase.mpr ⟨
        atom_ne_of_signs hne (fun he => hCn (he ▸ hl)), h C hCΓ l hl⟩
    · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
      exact Finset.mem_erase.mpr ⟨
        atom_ne_of_signs (fun he => hDp (he ▸ hl)) hne, h D hDΓ l hl⟩

theorem elimination_extend (p : α) (Γ : ClauseSet α) (v : Valuation α)
    (h : Models v (eliminate p Γ)) :
    ∃ w, Models w Γ ∧ ∀ q, q ≠ p → w q = v q := by
  have neutral_sat (C : Clause α) (hc : C ∈ Γ) (hp : pos p ∉ C) (hn : neg p ∉ C) :
      ClauseSat v C := h C (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, hp, hn⟩))
  by_cases hall : ∀ C ∈ positive p Γ, ClauseSat v (C.erase (pos p))
  · refine ⟨Function.update v p false, ?_, ?_⟩
    · intro C hC
      by_cases hn : neg p ∈ C
      · exact ⟨neg p, hn, by simp [LiteralSat, neg]⟩
      · by_cases hp : pos p ∈ C
        · have hr := hall C (Finset.mem_filter.mpr ⟨hC, hp, hn⟩)
          have hstable := clause_update p v false (C.erase (pos p))
            (by simp) (fun hm => hn (Finset.mem_of_mem_erase hm))
          exact clause_mono (Finset.erase_subset _ _) (hstable.mpr hr)
        · exact (clause_update p v false C hp hn).mpr (neutral_sat C hC hp hn)
    · intro q hq
      exact Function.update_of_ne hq _ _
  · push Not at hall
    obtain ⟨C, hC, hfalse⟩ := hall
    have negative_remainder (D : Clause α) (hD : D ∈ negative p Γ) :
        ClauseSat v (D.erase (neg p)) := by
      have hres : resolvent p C D ∈ eliminate p Γ :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨C, hC, Finset.mem_image.mpr ⟨D, hD, rfl⟩⟩)
      obtain ⟨l, hl, ht⟩ := h _ hres
      rcases Finset.mem_union.mp hl with hl | hl
      · exact False.elim (hfalse ⟨l, hl, ht⟩)
      · exact ⟨l, hl, ht⟩
    refine ⟨Function.update v p true, ?_, ?_⟩
    · intro D hD
      by_cases hp : pos p ∈ D
      · exact ⟨pos p, hp, by simp [LiteralSat, pos]⟩
      · by_cases hn : neg p ∈ D
        · have hr := negative_remainder D (Finset.mem_filter.mpr ⟨hD, hn, hp⟩)
          have hstable := clause_update p v true (D.erase (neg p))
            (fun hm => hp (Finset.mem_of_mem_erase hm)) (by simp)
          exact clause_mono (Finset.erase_subset _ _) (hstable.mpr hr)
        · exact (clause_update p v true D hp hn).mpr (neutral_sat D hD hp hn)
    · intro q hq
      exact Function.update_of_ne hq _ _

theorem elimination_equisatisfiable (p : α) (Γ : ClauseSet α) :
    Sat (eliminate p Γ) ↔ Sat Γ := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw, _⟩ := elimination_extend p Γ v hv
    exact ⟨w, hw⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, fun C hC => sound (elimination_derivable p Γ C hC) v hv⟩
private theorem complete_supported (S : Finset α) :
    ∀ Γ : ClauseSet α, Supported S Γ → ¬ Sat Γ → Derives Γ ∅ := by
  induction S using Finset.induction_on with
  | empty =>
    intro Γ hs hn
    have empty_clause (C : Clause α) (hC : C ∈ Γ) : C = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro l hl
      simpa using hs C hC l hl
    by_cases he : ∅ ∈ Γ
    · exact .premise he
    · exfalso
      apply hn
      refine ⟨fun _ => false, ?_⟩
      intro C hC
      exact False.elim (he ((empty_clause C hC) ▸ hC))
  | @insert p S hp ih =>
    intro Γ hs hn
    have hs' : Supported S (eliminate p Γ) := by
      simpa [hp] using elimination_support hs p
    have hn' : ¬ Sat (eliminate p Γ) := fun h => hn ((elimination_equisatisfiable p Γ).mp h)
    exact compose (elimination_derivable p Γ) (ih _ hs' hn')

theorem finite_complete {Γ : ClauseSet α} (h : ¬ Sat Γ) : Derives Γ ∅ := by
  apply complete_supported (support Γ) Γ ?_ h
  intro C hC l hl
  exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩

theorem refutation_iff (Γ : ClauseSet α) : ¬ Sat Γ ↔ Derives Γ ∅ := by
  exact ⟨finite_complete, refutation_unsat⟩
theorem derives_support {S : Finset α} {Γ : ClauseSet α} {C : Clause α}
    (h : Supported S Γ) (d : Derives Γ C) : ∀ l ∈ C, l.atom ∈ S := by
  induction d with
  | premise hC => exact h _ hC
  | resolve p _ _ _ _ ihC ihD =>
    intro l hl
    rcases Finset.mem_union.mp hl with hl | hl
    · exact ihC l (Finset.mem_of_mem_erase hl)
    · exact ihD l (Finset.mem_of_mem_erase hl)
theorem closed_derives {Γ : ClauseSet α} (h : Closed Γ) {C : Clause α}
    (d : Derives Γ C) : C ∈ Γ := by
  induction d with
  | premise hC => exact hC
  | resolve p hp hn _ _ ihC ihD => exact h _ ihC _ ihD p hp hn
theorem closed_satisfiable {Γ : ClauseSet α} (h : Closed Γ) (he : ∅ ∉ Γ) :
    Sat Γ := by
  by_contra hn
  exact he (closed_derives h (finite_complete hn))
private theorem clause_available {S : Finset α} {C : Clause α}
    (h : ∀ l ∈ C, l.atom ∈ S) : C ∈ availableClauses S := by
  apply Finset.mem_powerset.mpr
  intro l hl
  have ha := h l hl
  refine Finset.mem_biUnion.mpr ⟨l.atom, ha, ?_⟩
  rcases l with ⟨a, b⟩
  cases b <;> simp [pos, neg]

theorem saturation_bound (S : Finset α) (states : ℕ → ClauseSet α) (k : ℕ)
    (h0 : Supported S (states 0)) (hs : ∀ i < k, Step (states i) (states (i + 1))) :
    k ≤ (availableClauses S).card := by
  have inv : ∀ i, i ≤ k →
      Supported S (states i) ∧ (states 0).card + i = (states i).card := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨h0, by simp⟩
    | succ i ih =>
      intro hi
      obtain ⟨hsi, hci⟩ := ih (by omega)
      obtain ⟨C, hC, D, hD, p, hp, hn, hnew, he⟩ := hs i (by omega)
      constructor
      · rw [he]
        intro E hE
        rcases Finset.mem_insert.mp hE with rfl | hE
        · exact derives_support hsi
            (Derives.resolve p hp hn (.premise hC) (.premise hD))
        · exact hsi E hE
      · rw [he, Finset.card_insert_of_notMem hnew]
        omega
  obtain ⟨hsk, hck⟩ := inv k le_rfl
  have hb : (states k).card ≤ (availableClauses S).card :=
    Finset.card_le_card (fun C hC => clause_available (hsk C hC))
  omega

/-- A finite saturation run adds one missing resolvent at each transition. -/
inductive SaturationRun : ℕ → ClauseSet α → ClauseSet α → Prop
  | nil (Γ : ClauseSet α) : SaturationRun 0 Γ Γ
  | cons {Γ Δ Θ : ClauseSet α} {k : ℕ} :
      Step Γ Δ → SaturationRun k Δ Θ → SaturationRun (k + 1) Γ Θ

theorem step_models {Γ Δ : ClauseSet α} (h : Step Γ Δ) (v : Valuation α) :
    Models v Δ ↔ Models v Γ := by
  obtain ⟨C, hC, D, hD, p, _, _, _, rfl⟩ := h
  exact add_resolvent_models hC hD v

theorem no_step_iff_closed (Γ : ClauseSet α) :
    (¬ ∃ Δ, Step Γ Δ) ↔ Closed Γ := by
  constructor
  · intro h C hC D hD p hp hn
    by_contra hnew
    exact h ⟨insert (resolvent p C D) Γ, C, hC, D, hD, p, hp, hn, hnew, rfl⟩
  · intro hc ⟨Δ, C, hC, D, hD, p, hp, hn, hnew, _⟩
    exact hnew (hc C hC D hD p hp hn)

theorem saturation_run_models {k : ℕ} {Γ Δ : ClauseSet α}
    (h : SaturationRun k Γ Δ) (v : Valuation α) : Models v Δ ↔ Models v Γ := by
  induction h with
  | nil => rfl
  | cons hs _ ih => exact ih.trans (step_models hs v)

/-- A closed endpoint exists after at most the number of as-yet absent clauses
on the initial support. The run uses the actual missing-resolvent transitions. -/
theorem saturation_exists (S : Finset α) (Γ : ClauseSet α) (hs : Supported S Γ) :
    ∃ k Δ, SaturationRun k Γ Δ ∧ Closed Δ ∧
      k ≤ (availableClauses S).card - Γ.card := by
  classical
  have step_support {Ξ Θ : ClauseSet α} (h : Step Ξ Θ) (hx : Supported S Ξ) :
      Supported S Θ := by
    obtain ⟨C, hC, D, hD, p, hp, hn, _, rfl⟩ := h
    intro E hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact derives_support hx (Derives.resolve p hp hn (.premise hC) (.premise hD))
    · exact hx E hE
  have step_card {Ξ Θ : ClauseSet α} (h : Step Ξ Θ) : Θ.card = Ξ.card + 1 := by
    obtain ⟨_, _, _, _, _, _, _, hnew, rfl⟩ := h
    exact Finset.card_insert_of_notMem hnew
  have card_bound {Ξ : ClauseSet α} (hx : Supported S Ξ) :
      Ξ.card ≤ (availableClauses S).card :=
    Finset.card_le_card (fun C hC => clause_available (hx C hC))
  have with_fuel : ∀ fuel Ξ, Supported S Ξ → Ξ.card + fuel = (availableClauses S).card →
      ∃ k Θ, SaturationRun k Ξ Θ ∧ Closed Θ ∧ k ≤ fuel := by
    intro fuel
    induction fuel with
    | zero =>
      intro Ξ hx hcard
      have hc : Closed Ξ := by
        apply (no_step_iff_closed Ξ).mp
        rintro ⟨Θ, hstep⟩
        have ht := card_bound (step_support hstep hx)
        have hs := step_card hstep
        omega
      exact ⟨0, Ξ, .nil Ξ, hc, le_rfl⟩
    | succ fuel ih =>
      intro Ξ hx hcard
      by_cases hc : Closed Ξ
      · exact ⟨0, Ξ, .nil Ξ, hc, Nat.zero_le _⟩
      · have he : ∃ Θ, Step Ξ Θ := by
          by_contra hn
          exact hc ((no_step_iff_closed Ξ).mp hn)
        obtain ⟨Θ, ht⟩ := he
        obtain ⟨k, Ω, hr, hclosed, hk⟩ := ih Θ (step_support ht hx) (by
          have hstepcard := step_card ht
          omega)
        exact ⟨k + 1, Ω, .cons ht hr, hclosed, by omega⟩
  exact with_fuel ((availableClauses S).card - Γ.card) Γ hs (by
    have hbound := card_bound hs
    omega)

theorem saturation_endpoint_refutation {k : ℕ} {Γ Δ : ClauseSet α}
    (hr : SaturationRun k Γ Δ) (hc : Closed Δ) :
    (∅ ∈ Δ) ↔ ¬ Sat Γ := by
  constructor
  · intro hempty ⟨v, hv⟩
    exact (empty_cases v).1 ((saturation_run_models hr v).mpr hv ∅ hempty)
  · intro hn
    by_contra he
    obtain ⟨v, hv⟩ := closed_satisfiable hc he
    exact hn ⟨v, (saturation_run_models hr v).mp hv⟩

/-- The restriction of each original valuation already satisfies the
eliminated clauses; no change in its truth values is required in this direction. -/
theorem elimination_models (p : α) (Γ : ClauseSet α) (v : Valuation α)
    (h : Models v Γ) : Models v (eliminate p Γ) := by
  intro C hC
  exact sound (elimination_derivable p Γ C hC) v h

def eliminateMany : List α → ClauseSet α → ClauseSet α
  | [], Γ => Γ
  | p :: ps, Γ => eliminateMany ps (eliminate p Γ)

theorem elimination_many_extend (ps : List α) (Γ : ClauseSet α) (v : Valuation α)
    (h : Models v (eliminateMany ps Γ)) :
    ∃ w, Models w Γ ∧ ∀ q, q ∉ ps → w q = v q := by
  induction ps generalizing Γ v with
  | nil => exact ⟨v, h, by simp⟩
  | cons p ps ih =>
    obtain ⟨w, hw, hsame⟩ := ih (eliminate p Γ) v h
    obtain ⟨u, hu, hrestore⟩ := elimination_extend p Γ w hw
    refine ⟨u, hu, ?_⟩
    intro q hq
    have hp : q ≠ p := by intro he; exact hq (List.mem_cons.mpr (Or.inl he))
    have hps : q ∉ ps := fun hm => hq (List.mem_cons.mpr (Or.inr hm))
    exact (hrestore q hp).trans (hsame q hps)

theorem elimination_many_support (ps : List α) {S : Finset α} {Γ : ClauseSet α}
    (h : Supported S Γ) : Supported (S \ ps.toFinset) (eliminateMany ps Γ) := by
  induction ps generalizing S Γ with
  | nil => simpa [eliminateMany] using h
  | cons p ps ih =>
    have hs := ih (elimination_support h p)
    have he : S.erase p \ ps.toFinset = S \ (p :: ps).toFinset := by
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons,
        Finset.mem_insert, List.mem_toFinset, not_or]
      tauto
    simpa only [eliminateMany, he] using hs

theorem elimination_many_equisatisfiable (ps : List α) (Γ : ClauseSet α) :
    Sat (eliminateMany ps Γ) ↔ Sat Γ := by
  induction ps generalizing Γ with
  | nil => rfl
  | cons p ps ih => exact (ih (eliminate p Γ)).trans (elimination_equisatisfiable p Γ)

theorem eliminate_all_decides (S : Finset α) (Γ : ClauseSet α) (h : Supported S Γ) :
    (∅ ∈ eliminateMany S.toList Γ ↔ ¬ Sat Γ) ∧
      (∅ ∉ eliminateMany S.toList Γ → ∃ v, Models v Γ) := by
  have hs : Supported ∅ (eliminateMany S.toList Γ) := by
    simpa using elimination_many_support S.toList h
  have empty_clause (C : Clause α) (hC : C ∈ eliminateMany S.toList Γ) : C = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    simpa using hs C hC l hl
  have model_if_no_empty (hn : ∅ ∉ eliminateMany S.toList Γ) : ∃ v, Models v Γ := by
    apply (elimination_many_equisatisfiable S.toList Γ).mp
    refine ⟨fun _ => false, ?_⟩
    intro C hC
    exact False.elim (hn ((empty_clause C hC) ▸ hC))
  refine ⟨?_, model_if_no_empty⟩
  constructor
  · intro he hsat
    obtain ⟨v, hv⟩ := (elimination_many_equisatisfiable S.toList Γ).mpr hsat
    exact (empty_cases v).1 (hv ∅ he)
  · intro hn
    by_contra he
    exact hn (model_if_no_empty he)

theorem formula_refutation (A : PropFormula α) (L : List (List (PropLiteral α)))
    (h : SemEquivalent (.neg A) (cnfFormula L)) :
    Tautology A ↔ Derives (ofCnf L) ∅ := by
  rw [← refutation_iff]
  constructor
  · intro hA ⟨v, hv⟩
    have hc := (list_cnf v L).mpr hv
    rw [← h v] at hc
    simp [eval, show eval v A = true from hA v] at hc
  · intro hn v
    change eval v A = true
    cases ha : eval v A with
    | false =>
      exfalso
      apply hn
      refine ⟨v, (list_cnf v L).mp ?_⟩
      rw [← h v]
      simp [eval, ha]
    | true => rfl
theorem entailment_refutation (Γ : Finset (PropFormula α)) (B : PropFormula α)
    (L : List (List (PropLiteral α)))
    (h : SemEquivalent (.conj (finiteConj Γ.toList) (.neg B)) (cnfFormula L)) :
    Entails Γ B ↔ Derives (ofCnf L) ∅ := by
  rw [← refutation_iff]
  constructor
  · intro hent ⟨v, hv⟩
    have hc := (list_cnf v L).mpr hv
    rw [← h v] at hc
    have ht : eval v (finiteConj Γ.toList) = true ∧ eval v B = false := by
      simpa [eval] using hc
    have hΓ : SatisfiesContext v Γ := by
      simpa [SatisfiesContext, Satisfies] using (eval_finiteConj v Γ.toList).mp ht.1
    have hb := hent v hΓ
    simp [Satisfies, ht.2] at hb
  · intro hn v hΓ
    change eval v B = true
    cases hb : eval v B with
    | false =>
      exfalso
      apply hn
      refine ⟨v, (list_cnf v L).mp ?_⟩
      rw [← h v]
      have ht : eval v (finiteConj Γ.toList) = true := by
        apply (eval_finiteConj v Γ.toList).mpr
        simpa [SatisfiesContext, Satisfies] using hΓ
      simp [eval, ht, hb]
    | true => rfl
end Lemmatheca.ProofTheory.Resolution
