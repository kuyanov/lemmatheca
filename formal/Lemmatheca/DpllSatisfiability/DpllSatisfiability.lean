import Lemmatheca.TseitinEncoding.TseitinEncoding

/-! Finite list CNFs, partial-assignment residuals, and ordered DPLL. -/
namespace Lemmatheca.MathematicalLogic.DpllSatisfiability
open Lemmatheca.MathematicalLogic.Propositional
universe u
variable {α : Type u} [DecidableEq α]

abbrev Cnf (α : Type u) := List (List (PropLiteral α))
abbrev PartialAssignment (α : Type u) := α → Option Bool

def opposite (l : PropLiteral α) : PropLiteral α := ⟨l.atom, !l.positive⟩
abbrev Models := @TseitinEncoding.ListModels
def Sat (Γ : Cnf α) : Prop := ∃ v, Models v Γ
def Extends (v : Valuation α) (τ : PartialAssignment α) : Prop :=
  ∀ p b, τ p = some b → v p = b
def residual (τ : PartialAssignment α) (Γ : Cnf α) : Cnf α :=
  (Γ.filter (fun C => !(C.any (fun l => τ l.atom == some l.positive)))).map
    (fun C => C.filter (fun l => (τ l.atom).isNone))
def single (p : α) (b : Bool) : PartialAssignment α :=
  fun q => if q = p then some b else none
def setting (p : α) (b : Bool) (Γ : Cnf α) : Cnf α :=
  (Γ.filter (fun C => !(C.contains ⟨p,b⟩))).map
    (fun C => C.filter (fun l => l.atom != p))
def support (Γ : Cnf α) : Finset α := (Γ.flatten.map PropLiteral.atom).toFinset
def Supported (L : List α) (Γ : Cnf α) : Prop :=
  ∀ C ∈ Γ, ∀ l ∈ C, l.atom ∈ L
def occurs (p : α) (b : Bool) (Γ : Cnf α) : Bool :=
  Γ.any (fun C => C.contains ⟨p,b⟩)
def Pure (l : PropLiteral α) (Γ : Cnf α) : Prop :=
  occurs l.atom l.positive Γ = true ∧ occurs l.atom (!l.positive) Γ = false

def UnitChain : Cnf α → List (PropLiteral α) → Prop
  | _, [] => True
  | Γ, l :: ls => [l] ∈ Γ ∧ UnitChain (setting l.atom l.positive Γ) ls

def preferred (p : α) (Γ : Cnf α) : Option Bool :=
  if [⟨p,true⟩] ∈ Γ then some true
  else if [⟨p,false⟩] ∈ Γ then some false
  else if occurs p false Γ = false then some true
  else if occurs p true Γ = false then some false
  else none

def restore (p : α) (b : Bool) (r : Option (Valuation α)) : Option (Valuation α) :=
  r.map (fun v => Function.update v p b)

def solve : List α → Cnf α → Option (Valuation α)
  | [], Γ => if Γ = [] then some (fun _ => false) else none
  | p :: K, Γ =>
      if Γ = [] then some (fun _ => false)
      else if [] ∈ Γ then none
      else match preferred p Γ with
        | some b => restore p b (solve K (setting p b Γ))
        | none => match restore p true (solve K (setting p true Γ)) with
          | some v => some v
          | none => restore p false (solve K (setting p false Γ))

/-- Number of assignments on the longest explored branch; empty CNFs stop early. -/
def searchDepth : List α → Cnf α → ℕ
  | [], _ => 0
  | p :: K, Γ =>
      if Γ = [] ∨ [] ∈ Γ then 0
      else match preferred p Γ with
        | some b => 1 + searchDepth K (setting p b Γ)
        | none => match restore p true (solve K (setting p true Γ)) with
          | some _ => 1 + searchDepth K (setting p true Γ)
          | none => 1 + max (searchDepth K (setting p true Γ))
              (searchDepth K (setting p false Γ))

omit [DecidableEq α] in
theorem empty_cases (v : Valuation α) :
    Models v ([] : Cnf α) ∧ ¬ Sat ([[]] : Cnf α) := by
  simp [Models, TseitinEncoding.ListModels, Sat]


omit [DecidableEq α] in
theorem residual_models (v : Valuation α) (τ : PartialAssignment α) (Γ : Cnf α)
    (h : Extends v τ) : Models v Γ ↔ Models v (residual τ Γ) := by
  constructor
  · intro hv C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    obtain ⟨hD, hnone⟩ := List.mem_filter.mp hD
    obtain ⟨l, hl, ht⟩ := hv D hD
    refine ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, ht⟩
    cases he : τ l.atom with
    | none => simp
    | some b =>
      have hb := h l.atom b he
      have heq : b = l.positive := hb.symm.trans ht
      have htrue : D.any (fun l => τ l.atom == some l.positive) = true :=
        List.any_eq_true.mpr ⟨l, hl, by simp [he, heq]⟩
      simp [htrue] at hnone
  · intro hv D hD
    by_cases htrue : D.any (fun l => τ l.atom == some l.positive) = true
    · obtain ⟨l, hl, ht⟩ := List.any_eq_true.mp htrue
      exact ⟨l, hl, h l.atom l.positive (by simpa using ht)⟩
    · have hm : D.filter (fun l => (τ l.atom).isNone) ∈ residual τ Γ :=
        List.mem_map.mpr ⟨D, List.mem_filter.mpr ⟨hD, by simp [htrue]⟩, rfl⟩
      obtain ⟨l, hl, ht⟩ := hv _ hm
      exact ⟨l, (List.mem_filter.mp hl).1, ht⟩


omit [DecidableEq α] in
theorem partial_extension (τ : PartialAssignment α) : ∃ v, Extends v τ := by
  refine ⟨fun p => (τ p).getD false, ?_⟩
  intro p b hb
  simp [hb]


omit [DecidableEq α] in
theorem residual_terminal (τ : PartialAssignment α) (Γ : Cnf α) :
    (residual τ Γ = [] → ∀ v, Extends v τ → Models v Γ) ∧
    ([] ∈ residual τ Γ → ¬ ∃ v, Extends v τ ∧ Models v Γ) := by
  constructor
  · intro he v hv
    exact (residual_models v τ Γ hv).mpr (by simp [he, Models, TseitinEncoding.ListModels])
  · rintro he ⟨v, hv, hm⟩
    obtain ⟨l, hl, _⟩ := (residual_models v τ Γ hv).mp hm [] he
    simp at hl


theorem setting_residual (p : α) (b : Bool) (Γ : Cnf α) :
    setting p b Γ = residual (single p b) Γ := by
  have test (l : PropLiteral α) :
      (single p b l.atom == some l.positive) = (l == ⟨p,b⟩) := by
    rcases l with ⟨q,c⟩
    by_cases he : q = p
    · subst q; cases b <;> cases c <;> simp [single]
    · simp [single, he, PropLiteral.mk.injEq]
  have unassigned (l : PropLiteral α) : (single p b l.atom).isNone = (l.atom != p) := by
    simp only [single]
    split <;> simp_all
  simp only [residual, test, unassigned, List.any_beq']
  rfl


private theorem mem_support {p : α} {Γ : Cnf α} :
    p ∈ support Γ ↔ ∃ C ∈ Γ, ∃ l ∈ C, l.atom = p := by
  simp [support, List.mem_flatten]

private theorem setting_member {p : α} {b : Bool} {Γ : Cnf α} {C : List (PropLiteral α)} :
    C ∈ setting p b Γ ↔
      ∃ D ∈ Γ, (⟨p,b⟩ : PropLiteral α) ∉ D ∧ C = D.filter (fun l => l.atom != p) := by
  constructor
  · intro h
    obtain ⟨D, hD, he⟩ := List.mem_map.mp h
    obtain ⟨hD, habs⟩ := List.mem_filter.mp hD
    exact ⟨D, hD, by simpa using habs, he.symm⟩
  · rintro ⟨D, hD, habs, rfl⟩
    exact List.mem_map.mpr ⟨D, List.mem_filter.mpr ⟨hD, by simpa using habs⟩, rfl⟩

theorem setting_support (p : α) (b : Bool) (Γ : Cnf α) :
    support (setting p b Γ) ⊆ (support Γ).erase p := by
  intro q hq
  obtain ⟨C, hC, l, hl, rfl⟩ := mem_support.mp hq
  obtain ⟨D, hD, _, rfl⟩ := setting_member.mp hC
  obtain ⟨hl, hne⟩ := List.mem_filter.mp hl
  exact Finset.mem_erase.mpr ⟨by simpa using hne, mem_support.mpr ⟨D, hD, l, hl, rfl⟩⟩


theorem setting_supported {p : α} {K : List α} {Γ : Cnf α}
    (h : Supported (p :: K) Γ) (b : Bool) : Supported K (setting p b Γ) := by
  intro C hC l hl
  obtain ⟨D, hD, _, rfl⟩ := setting_member.mp hC
  obtain ⟨hl, hne⟩ := List.mem_filter.mp hl
  have hm := h D hD l hl
  rcases List.mem_cons.mp hm with he | hm
  · simp [he] at hne
  · exact hm


theorem setting_models (p : α) (b : Bool) (v : Valuation α) (Γ : Cnf α) :
    Models (Function.update v p b) Γ ↔ Models v (setting p b Γ) := by
  constructor
  · intro hv C hC
    obtain ⟨D, hD, habs, rfl⟩ := setting_member.mp hC
    obtain ⟨l, hl, ht⟩ := hv D hD
    have hne : l.atom ≠ p := by
      intro he
      have hs : b = l.positive := by simpa [he] using ht
      have heq : l = ⟨p,b⟩ := by cases l; simp_all
      exact habs (heq ▸ hl)
    exact ⟨l, List.mem_filter.mpr ⟨hl, by simpa using hne⟩,
      by simpa [Function.update_of_ne hne] using ht⟩
  · intro hv D hD
    by_cases hmem : (⟨p,b⟩ : PropLiteral α) ∈ D
    · exact ⟨⟨p,b⟩, hmem, by simp⟩
    · have hm : D.filter (fun l => l.atom != p) ∈ setting p b Γ :=
        setting_member.mpr ⟨D, hD, hmem, rfl⟩
      obtain ⟨l, hl, ht⟩ := hv _ hm
      obtain ⟨hl, hne⟩ := List.mem_filter.mp hl
      have hne : l.atom ≠ p := by simpa using hne
      exact ⟨l, hl, by simpa [Function.update_of_ne hne] using ht⟩


omit [DecidableEq α] in
theorem unit_forced {p : α} {b : Bool} {Γ : Cnf α} (hunit : [⟨p,b⟩] ∈ Γ)
    (v : Valuation α) (hv : Models v Γ) : v p = b := by
  obtain ⟨l, hl, hv⟩ := hv _ hunit
  obtain rfl := List.mem_singleton.mp hl
  exact hv


theorem unit_equisatisfiable {p : α} {b : Bool} {Γ : Cnf α}
    (hunit : [⟨p,b⟩] ∈ Γ) : Sat Γ ↔ Sat (setting p b Γ) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, (setting_models p b v Γ).mp ?_⟩
    simpa only [← unit_forced hunit v hv, Function.update_eq_self] using hv
  · rintro ⟨v, hv⟩
    exact ⟨Function.update v p b, (setting_models p b v Γ).mpr hv⟩


theorem unit_chain_forced {Γ : Cnf α} {ls : List (PropLiteral α)}
    (hrun : UnitChain Γ ls) (v : Valuation α) (hv : Models v Γ) :
    ∀ l ∈ ls, v l.atom = l.positive := by
  induction ls generalizing Γ with
  | nil => simp
  | cons l ls ih =>
    obtain ⟨hunit, htail⟩ := hrun
    have hforce := unit_forced hunit v hv
    have hm : Models v (setting l.atom l.positive Γ) := by
      apply (setting_models _ _ _ _).mp
      simpa only [← hforce, Function.update_eq_self] using hv
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hforce
    · exact ih htail hm k hk


private theorem unit_chain_support {Γ : Cnf α} {ls : List (PropLiteral α)}
    (hrun : UnitChain Γ ls) :
    (ls.map PropLiteral.atom).Nodup ∧ ∀ l ∈ ls, l.atom ∈ support Γ := by
  induction ls generalizing Γ with
  | nil => simp
  | cons l ls ih =>
    obtain ⟨hunit, htail⟩ := hrun
    obtain ⟨hnd, hs⟩ := ih htail
    have hsub := setting_support l.atom l.positive Γ
    constructor
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_,hnd⟩
      rintro hm
      obtain ⟨k,hk,he⟩ := List.mem_map.mp hm
      exact (Finset.mem_erase.mp (hsub (hs k hk))).1 he
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact mem_support.mpr ⟨[k], hunit, k, by simp, rfl⟩
      · exact Finset.mem_of_mem_erase (hsub (hs k hk))

theorem unit_chain_bound {Γ : Cnf α} {ls : List (PropLiteral α)}
    (hrun : UnitChain Γ ls) :
    (ls.map PropLiteral.atom).Nodup ∧ ls.length ≤ (support Γ).card := by
  obtain ⟨hnd,hs⟩ := unit_chain_support hrun
  refine ⟨hnd, ?_⟩
  have hsub : (ls.map PropLiteral.atom).toFinset ⊆ support Γ := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact hs l hl
  have hc := Finset.card_le_card hsub
  simpa only [List.toFinset_card_of_nodup hnd, List.length_map] using hc


private theorem occurs_true {p : α} {b : Bool} {Γ : Cnf α} :
    occurs p b Γ = true ↔ ∃ C ∈ Γ, (⟨p,b⟩ : PropLiteral α) ∈ C := by
  simp [occurs, List.any_eq_true]

theorem pure_update {p : α} {b : Bool} {Γ : Cnf α}
    (habs : occurs p (!b) Γ = false) (v : Valuation α) (hv : Models v Γ) :
    Models (Function.update v p b) Γ := by
  intro C hC
  obtain ⟨l, hl, ht⟩ := hv C hC
  refine ⟨l, hl, ?_⟩
  by_cases he : l.atom = p
  · have hs : l.positive = b := by
      by_contra hn
      have hb : l.positive = !b := Bool.eq_not_iff.mpr hn
      have heq : l = ⟨p,!b⟩ := by cases l; simp_all
      have ho := occurs_true.mpr ⟨C, hC, heq ▸ hl⟩
      simp [habs] at ho
    simp [he, hs]
  · simpa [Function.update_of_ne he] using ht


theorem pure_equisatisfiable {p : α} {b : Bool} {Γ : Cnf α}
    (habs : occurs p (!b) Γ = false) : Sat Γ ↔ Sat (setting p b Γ) := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (setting_models p b v Γ).mp (pure_update habs v hv)⟩
  · rintro ⟨v, hv⟩
    exact ⟨Function.update v p b, (setting_models p b v Γ).mpr hv⟩


theorem branching (p : α) (Γ : Cnf α) :
    Sat Γ ↔ Sat (setting p true Γ) ∨ Sat (setting p false Γ) := by
  constructor
  · rintro ⟨v, hv⟩
    have hh : Sat (setting p (v p) Γ) := by
      refine ⟨v, (setting_models p (v p) v Γ).mp ?_⟩
      simpa only [Function.update_eq_self] using hv
    cases he : v p
    · exact Or.inr (he ▸ hh)
    · exact Or.inl (he ▸ hh)
  · rintro (⟨v,hv⟩ | ⟨v,hv⟩)
    · exact ⟨Function.update v p true, (setting_models p true v Γ).mpr hv⟩
    · exact ⟨Function.update v p false, (setting_models p false v Γ).mpr hv⟩


theorem preferred_safe {p : α} {b : Bool} {Γ : Cnf α}
    (h : preferred p Γ = some b) : Sat Γ ↔ Sat (setting p b Γ) := by
  unfold preferred at h
  split at h
  · cases h; exact unit_equisatisfiable (by assumption)
  · split at h
    · cases h; exact unit_equisatisfiable (by assumption)
    · split at h
      · cases h; exact pure_equisatisfiable (by simpa using ‹occurs p false Γ = false›)
      · split at h
        · cases h; exact pure_equisatisfiable (by simpa using ‹occurs p true Γ = false›)
        · contradiction


private theorem restore_success {p : α} {b : Bool} {r : Option (Valuation α)}
    {v : Valuation α} (h : restore p b r = some v) :
    ∃ w, r = some w ∧ Function.update w p b = v := by
  cases r <;> simp_all [restore]

private theorem restore_exists (p : α) (b : Bool) (r : Option (Valuation α)) :
    (∃ v, restore p b r = some v) ↔ ∃ v, r = some v := by
  cases r <;> simp [restore]

omit [DecidableEq α] in
private theorem empty_clause_unsat {Γ : Cnf α} (he : [] ∈ Γ) : ¬ Sat Γ := by
  rintro ⟨v,hv⟩
  obtain ⟨l,hl,_⟩ := hv [] he
  simp at hl

theorem solve_sound {L : List α} {Γ : Cnf α} {v : Valuation α}
    (h : solve L Γ = some v) : Models v Γ := by
  induction L generalizing Γ v with
  | nil =>
    simp only [solve] at h
    split at h
    · subst Γ; simp [Models, TseitinEncoding.ListModels]
    · contradiction
  | cons p K ih =>
    rw [solve] at h
    split at h
    · subst Γ; simp [Models, TseitinEncoding.ListModels]
    · split at h
      · contradiction
      · split at h
        · obtain ⟨w,hw,rfl⟩ := restore_success h
          exact (setting_models _ _ _ _).mpr (ih hw)
        · split at h
          · cases h
            obtain ⟨w,hw,rfl⟩ := restore_success (by assumption)
            exact (setting_models _ _ _ _).mpr (ih hw)
          · obtain ⟨w,hw,rfl⟩ := restore_success h
            exact (setting_models _ _ _ _).mpr (ih hw)


theorem solve_complete {L : List α} {Γ : Cnf α} (h : Supported L Γ) :
    (∃ v, solve L Γ = some v) ↔ Sat Γ := by
  induction L generalizing Γ with
  | nil =>
    by_cases he : Γ = []
    · subst Γ; simp [solve, Sat, Models, TseitinEncoding.ListModels]
    · have hu : ¬ Sat Γ := by
        rintro ⟨v,hv⟩
        obtain ⟨C,hC⟩ := List.exists_mem_of_ne_nil Γ he
        obtain ⟨l,hl,_⟩ := hv C hC
        exact (List.not_mem_nil (a := l.atom)) (h C hC l hl)
      simp [solve, he, hu]
  | cons p K ih =>
    by_cases he : Γ = []
    · subst Γ; simp [solve, Sat, Models, TseitinEncoding.ListModels]
    · by_cases hempty : [] ∈ Γ
      · simp [solve, he, hempty, empty_clause_unsat hempty]
      · have hi (b : Bool) := ih (setting_supported h b)
        cases hpref : preferred p Γ with
        | some b =>
          simp only [solve, ite_eq_right he, ite_eq_right hempty, hpref]
          exact (restore_exists p b _).trans ((hi b).trans (preferred_safe hpref).symm)
        | none =>
          simp only [solve, ite_eq_right he, ite_eq_right hempty, hpref]
          have hbranches := (branching p Γ).symm
          cases hr : restore p true (solve K (setting p true Γ)) with
          | some v =>
            constructor
            · intro _
              exact (branching p Γ).mpr (Or.inl
                ((hi true).mp ((restore_exists p true _).mp ⟨v,hr⟩)))
            · intro _; exact ⟨v,rfl⟩
          | none =>
            have hfalse : ¬ Sat (setting p true Γ) := by
              intro ht
              obtain ⟨v,hv⟩ := (restore_exists p true _).mpr ((hi true).mpr ht)
              rw [hr] at hv
              contradiction
            simpa [hfalse] using (restore_exists p false _).trans
              ((hi false).trans (by simpa [hfalse] using hbranches))


theorem solve_failure {L : List α} {Γ : Cnf α} (h : Supported L Γ) :
    solve L Γ = none ↔ ¬ Sat Γ := by
  constructor
  · intro he hs
    obtain ⟨v,hv⟩ := (solve_complete h).mpr hs
    rw [he] at hv
    contradiction
  · intro hu
    cases he : solve L Γ with
    | none => rfl
    | some v => exact False.elim (hu ⟨v,solve_sound he⟩)


theorem solve_outside {L : List α} {Γ : Cnf α} {v : Valuation α}
    (h : solve L Γ = some v) {p : α} (hp : p ∉ L) : v p = false := by
  induction L generalizing Γ v with
  | nil =>
    simp only [solve] at h
    split at h
    · cases h; rfl
    · contradiction
  | cons q K ih =>
    have hpq : p ≠ q := fun he => hp (by simp [he])
    have hpK : p ∉ K := fun hm => hp (List.mem_cons_of_mem _ hm)
    rw [solve] at h
    split at h
    · cases h; rfl
    · split at h
      · contradiction
      · split at h
        · obtain ⟨w,hw,rfl⟩ := restore_success h
          simpa [Function.update_of_ne hpq] using ih hw hpK
        · split at h
          · cases h
            obtain ⟨w,hw,rfl⟩ := restore_success (by assumption)
            simpa [Function.update_of_ne hpq] using ih hw hpK
          · obtain ⟨w,hw,rfl⟩ := restore_success h
            simpa [Function.update_of_ne hpq] using ih hw hpK


theorem depth_bound (L : List α) (Γ : Cnf α) : searchDepth L Γ ≤ L.length := by
  induction L generalizing Γ with
  | nil => simp [searchDepth]
  | cons p K ih =>
    rw [searchDepth]
    split
    · simp
    · split
      · simpa only [List.length_cons, Nat.add_comm] using Nat.add_le_add_left (ih _) 1
      · split
        · simpa only [List.length_cons, Nat.add_comm] using Nat.add_le_add_left (ih _) 1
        · simpa only [List.length_cons, Nat.add_comm] using
            Nat.add_le_add_left (max_le (ih _) (ih _)) 1


private theorem eraseDups_nodup (xs : List α) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons p xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp
    · exact eraseDups_nodup _
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem support_input (Γ : Cnf α) :
    Supported (Γ.flatten.map PropLiteral.atom).eraseDups Γ ∧
    (Γ.flatten.map PropLiteral.atom).eraseDups.length = (support Γ).card := by
  constructor
  · intro C hC l hl
    simp only [List.mem_eraseDups, List.mem_map, List.mem_flatten]
    exact ⟨l, ⟨C,hC,hl⟩, rfl⟩
  · have he := List.toFinset_card_of_nodup
      (eraseDups_nodup (Γ.flatten.map PropLiteral.atom))
    have heq : (Γ.flatten.map PropLiteral.atom).eraseDups.toFinset =
        (Γ.flatten.map PropLiteral.atom).toFinset := by ext p; simp
    rw [heq] at he
    exact he.symm


end Lemmatheca.MathematicalLogic.DpllSatisfiability
