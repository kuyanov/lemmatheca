import Lemmatheca.SacksSplitting.Construction

/-! Ordinary computation of the supplied Sacks stages and their limit pieces. -/
namespace Lemmatheca.ComputabilityTheory.SacksSplitting

open PostsTheorem UniversalComputation LimitComputability

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency true

private theorem cIte {α β : Type*} [Primcodable α] [Primcodable β]
    {P : α → Prop} [DecidablePred P] {f g : α → β}
    (hc : Computable (fun x => decide (P x))) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => if P x then f x else g x) := by
  simpa only [Bool.cond_decide] using hc.cond hf hg

private theorem cBoundedSearch {α : Type*} [Primcodable α] {R : α → ℕ → Prop}
    (hR : ComputablePred (fun p : α × ℕ => R p.1 p.2)) :
    Computable₂ (PrimitiveRecursion.boundedSearch R) := by
  have hstep : Computable₂ (fun p : α × ℕ => fun v : ℕ × ℕ =>
      if v.2 < v.1 then v.2 else if R p.1 v.1 then v.1 else v.1 + 1) :=
    cIte (Primrec.nat_lt.decide.to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.snd)) (Computable.snd.comp Computable.snd)
      (cIte (hR.decide.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd))) (Computable.fst.comp Computable.snd)
        (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)))
  exact (Computable.nat_rec Computable.snd (Computable.const 0) hstep).of_eq
    (fun _ => rfl)

private theorem cBoundedForall {α : Type*} [Primcodable α] {R : α → ℕ → Prop}
    (hR : ComputablePred (fun p : α × ℕ => R p.1 p.2)) :
    ComputablePred (fun p : α × ℕ => ∀ j < p.2, R p.1 j) := by
  apply Computable.computablePred
  have hstep : Computable₂ (fun p : α × ℕ => fun v : ℕ × Bool =>
      v.2 && decide (R p.1 v.1)) :=
    (Primrec.dom_bool₂ Bool.and).to_comp.comp (Computable.snd.comp Computable.snd)
      (hR.decide.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd)))
  apply (Computable.nat_rec Computable.snd (Computable.const true) hstep).of_eq
  intro p
  induction p.2 with
  | zero => simp
  | succ n ih =>
      simp only [ih]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hl, hn⟩ j hj
        by_cases he : j = n
        · simpa only [he] using hn
        · exact hl j (by omega)
      · intro hl
        exact ⟨fun j hj => hl j (by omega), hl n (by omega)⟩

private theorem cPredComp {α β : Type*} [Primcodable α] [Primcodable β]
    {P : β → Prop} {f : α → β} (hP : ComputablePred P) (hf : Computable f) :
    ComputablePred (fun a => P (f a)) := by
  obtain ⟨inst, hp⟩ := hP
  exact ⟨fun a => inst (f a), hp.comp hf⟩

private theorem cTabulate {α : Type*} [Primcodable α] {f : α → ℕ → ℕ}
    (hf : Computable₂ f) : Computable₂ (fun a n => FiniteInjury.tabulate n (f a)) := by
  have hstep : Computable₂ (fun p : α × ℕ => fun v : ℕ × List ℕ =>
      v.2 ++ [f p.1 v.1]) :=
    Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
  have hl := Computable.nat_rec Computable.snd (Computable.const ([] : List ℕ)) hstep
  apply (Computable.encode.comp hl).of_eq
  intro p
  have he : Nat.rec ([] : List ℕ) (fun n l => l ++ [f p.1 n]) p.2 =
      (List.range p.2).map (f p.1) := by
    induction p.2 with
    | zero => rfl
    | succ n ih => simp only [ih, List.range_succ, List.map_append,
        List.map_singleton]
  exact congrArg Encodable.encode he

attribute [local fun_prop] Computable Computable.const Computable.id Computable.comp
  Computable.fst Computable.snd Computable.pair

private theorem cAdd {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => f x + g x) :=
  Primrec.nat_add.to_comp.comp hf hg
private theorem cSub {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => f x - g x) :=
  Primrec.nat_sub.to_comp.comp hf hg
private theorem cMax {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => max (f x) (g x)) :=
  Primrec.nat_max.to_comp.comp hf hg
private theorem cMod {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => f x % g x) :=
  Primrec.nat_mod.to_comp.comp hf hg
private theorem cDiv {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => f x / g x) :=
  Primrec.nat_div.to_comp.comp hf hg
private theorem cEq {α β : Type*} [Primcodable α] [Primcodable β] [DecidableEq β]
    {f g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable (fun x => decide (f x = g x)) := Primrec.eq.decide.to_comp.comp hf hg
private theorem cLt {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => decide (f x < g x)) :=
  Primrec.nat_lt.decide.to_comp.comp hf hg
private theorem cLe {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => decide (f x ≤ g x)) :=
  Primrec.nat_le.decide.to_comp.comp hf hg
private theorem cAnd {α : Type*} [Primcodable α] {P Q : α → Prop}
    (hP : Computable (fun x => decide (P x))) (hQ : Computable (fun x => decide (Q x))) :
    Computable (fun x => decide (P x ∧ Q x)) := by
  simpa only [Bool.decide_and] using (Primrec.dom_bool₂ Bool.and).to_comp.comp hP hQ
private theorem cPredAnd {α : Type*} [Primcodable α] {P Q : α → Prop}
    (hp : ComputablePred P) (hq : ComputablePred Q) :
    ComputablePred (fun x => P x ∧ Q x) := (cAnd hp.decide hq.decide).computablePred
private theorem cPair {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => Nat.pair (f x) (g x)) :=
  Primrec₂.natPair.to_comp.comp hf hg
private theorem cEntry {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) :
    Computable (fun x => FiniteSequenceCoding.entry (f x) (g x)) :=
  FiniteSequenceCoding.primrec_entry.to_comp.comp hf hg
private theorem cBeta {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => beta (f x) (g x)) :=
  beta_primitive.to_comp.comp hf hg
private theorem cValue {α : Type*} [Primcodable α] {u k e x : α → ℕ}
    (hu : Computable u) (hk : Computable k) (he : Computable e) (hx : Computable x) :
    Computable (fun p => finiteValue (u p) (k p) (e p) (x p)) := by
  exact (finiteValue_primitive.to_comp.comp (cPair hu (cPair hk (cPair he hx)))).of_eq
    (fun _ => by simp only [finiteValueInput, Nat.unpair_pair])

attribute [local fun_prop] cAdd cSub cMax cMod cDiv cEq cLt cLe cAnd cPair cEntry cBeta cValue cIte

private theorem cSide {α : Type*} [Primcodable α] {z : α → State} {i : α → ℕ}
    (hz : Computable z) (hi : Computable i) : Computable (fun p => sideCode (z p) (i p)) := by
  unfold sideCode
  fun_prop
private theorem cLength {α : Type*} [Primcodable α] {z : α → State} {q : α → ℕ}
    (hz : Computable z) (hq : Computable q) : Computable (fun p => lengthRecord (z p) (q p)) := by
  unfold lengthRecord
  fun_prop
private theorem cRestraint {α : Type*} [Primcodable α] {z : α → State} {q : α → ℕ}
    (hz : Computable z) (hq : Computable q) : Computable (fun p => restraintRecord (z p) (q p)) := by
  unfold restraintRecord
  fun_prop
attribute [local fun_prop] cSide cLength cRestraint

private theorem observation_computable :
    Computable (fun p : ℕ × (State × ℕ) => leastObservation p.1 p.2.1 p.2.2) := by
  have hR : ComputablePred (fun p : (State × ℕ) × ℕ =>
      0 < finiteValue (sideCode p.1.1 (p.1.2 % 2)) p.2 (p.1.2 / 2) (p.1.2 / 2)) := by
    have hq : Computable (fun p : (State × ℕ) × ℕ => p.1.2) :=
      Computable.snd.comp Computable.fst
    have hz : Computable (fun p : (State × ℕ) × ℕ => p.1.1) :=
      Computable.fst.comp Computable.fst
    exact (cLt (Computable.const 0) (cValue
      (cSide hz (cMod hq (Computable.const 2))) Computable.snd
      (cDiv hq (Computable.const 2)) (cDiv hq (Computable.const 2)))).computablePred
  have hs : Computable (fun p : ℕ × (State × ℕ) =>
      PrimitiveRecursion.boundedSearch (fun p : State × ℕ => fun k =>
        0 < finiteValue (sideCode p.1 (p.2 % 2)) k (p.2 / 2) (p.2 / 2))
        p.2 (p.1 + 2)) := (cBoundedSearch hR).comp Computable.snd (by fun_prop)
  unfold leastObservation
  exact cIte (cLt hs (by fun_prop)) hs (Computable.const 0)
private theorem cObservation {α : Type*} [Primcodable α]
    {s q : α → ℕ} {z : α → State}
    (hs : Computable s) (hz : Computable z) (hq : Computable q) :
    Computable (fun p => leastObservation (s p) (z p) (q p)) :=
  Computable.comp (f := fun v : ℕ × (State × ℕ) => leastObservation v.1 v.2.1 v.2.2)
    (g := fun p => (s p, z p, q p)) observation_computable (hs.pair (hz.pair hq))
attribute [local fun_prop] cObservation

private theorem expands_computable (h : Approximation) (hh : Computable₂ h) :
    ComputablePred (fun p : ℕ × (State × ℕ) => Expands h p.1 p.2.1 p.2.2) := by
  let D := ℕ × (State × ℕ)
  have hs : Computable (fun p : D × ℕ => p.1.1) := Computable.fst.comp Computable.fst
  have hz : Computable (fun p : D × ℕ => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hq : Computable (fun p : D × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hR : ComputablePred (fun p : D × ℕ =>
      finiteValue (sideCode p.1.2.1 (p.1.2.2 % 2)) (p.1.1 + 1) (p.1.2.2 / 2) p.2 =
        h p.1.1 p.2 + 1) :=
    (cEq (cValue (cSide hz (cMod hq (Computable.const 2)))
      (cAdd hs (Computable.const 1)) (cDiv hq (Computable.const 2)) Computable.snd)
      (cAdd (hh.comp hs Computable.snd) (Computable.const 1))).computablePred
  have hb : Computable (fun p : D => lengthRecord p.2.1 p.2.2 + 1) :=
    cAdd (cLength (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)) (Computable.const 1)
  exact cPredComp (cBoundedForall (R := fun (p : D) x =>
    finiteValue (sideCode p.2.1 (p.2.2 % 2)) (p.1 + 1) (p.2.2 / 2) x =
      h p.1 x + 1) hR) (Computable.id.pair hb)

private theorem cExpands {α : Type*} [Primcodable α] (h : Approximation)
    (hh : Computable₂ h) {s q : α → ℕ} {z : α → State}
    (hs : Computable s) (hz : Computable z) (hq : Computable q) :
    Computable (fun p => decide (Expands h (s p) (z p) (q p))) :=
  Computable.comp (f := fun v : ℕ × (State × ℕ) => decide (Expands h v.1 v.2.1 v.2.2))
    (g := fun p => (s p, z p, q p)) (expands_computable h hh).decide
    (hs.pair (hz.pair hq))

private theorem cNextLength {α : Type*} [Primcodable α] (h : Approximation)
    (hh : Computable₂ h) {s q : α → ℕ} {z : α → State}
    (hs : Computable s) (hz : Computable z) (hq : Computable q) :
    Computable (fun p => nextLength h (s p) (z p) (q p)) :=
  cIte (cLe hq hs) (cAdd (cLength hz hq)
    (cIte (cExpands h hh hs hz hq) (Computable.const 1) (Computable.const 0)))
    (Computable.const 0)
private theorem cNextRestraint {α : Type*} [Primcodable α] (h : Approximation)
    (hh : Computable₂ h) {s q : α → ℕ} {z : α → State}
    (hs : Computable s) (hz : Computable z) (hq : Computable q) :
    Computable (fun p => nextRestraint h (s p) (z p) (q p)) :=
  cIte (cLe hq hs) (cMax (cRestraint hz hq)
    (cMax (cObservation hs hz hq)
      (cIte (cExpands h hh hs hz hq) (cAdd hs (Computable.const 1)) (Computable.const 0))))
    (Computable.const 0)
private theorem cArrival {α : Type*} [Primcodable α] {a s : α → ℕ}
    (ha : Computable a) (hs : Computable s) :
    Computable (fun p => FriedbergSplitting.arrival (a p) (s p)) :=
  FriedbergSplitting.scheduler_primitive.2.1.to_comp.comp ha hs

private theorem priority_computable (h : Approximation) (hh : Computable₂ h) :
    Computable (fun p : ℕ × (ℕ × State) => priority p.1 h p.2.1 p.2.2) := by
  let D := ℕ × (ℕ × State)
  have ha : Computable (fun p : D × ℕ => p.1.1) := Computable.fst.comp Computable.fst
  have hs : Computable (fun p : D × ℕ => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hz : Computable (fun p : D × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hR : ComputablePred (fun p : D × ℕ =>
      FriedbergSplitting.arrival p.1.1 p.1.2.1 < nextRestraint h p.1.2.1 p.1.2.2 p.2) :=
    (cLt (cArrival ha hs) (cNextRestraint h hh hs hz Computable.snd)).computablePred
  exact (cBoundedSearch hR).comp Computable.id
    (cAdd (Computable.fst.comp Computable.snd) (Computable.const 1))

private theorem cPriority {α : Type*} [Primcodable α] (h : Approximation)
    (hh : Computable₂ h) {a s : α → ℕ} {z : α → State}
    (ha : Computable a) (hs : Computable s) (hz : Computable z) :
    Computable (fun p => priority (a p) h (s p) (z p)) :=
  Computable.comp (f := fun v : ℕ × (ℕ × State) => priority v.1 h v.2.1 v.2.2)
    (g := fun p => (a p, s p, z p)) (priority_computable h hh) (ha.pair (hs.pair hz))
private theorem cChosen {α : Type*} [Primcodable α] (h : Approximation)
    (hh : Computable₂ h) {a s : α → ℕ} {z : α → State}
    (ha : Computable a) (hs : Computable s) (hz : Computable z) :
    Computable (fun p => chosenSide (a p) h (s p) (z p)) :=
  cIte (cLt (cPriority h hh ha hs hz) (cAdd hs (Computable.const 1)))
    (cSub (Computable.const 1) (cMod (cPriority h hh ha hs hz) (Computable.const 2)))
    (Computable.const 0)

set_option maxHeartbeats 800000 in
private theorem next_side_computable (h : Approximation) (hh : Computable₂ h) (i : ℕ) :
    Computable (fun p : ℕ × (ℕ × State) => nextSideCode p.1 h p.2.1 p.2.2 i) := by
  let D := ℕ × (ℕ × State)
  have ha : Computable (fun p : D × ℕ => p.1.1) := Computable.fst.comp Computable.fst
  have hs : Computable (fun p : D × ℕ => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hz : Computable (fun p : D × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hc : Computable (fun p : D => chosenSide p.1 h p.2.1 p.2.2) :=
    cChosen h hh Computable.fst (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)
  have harr : ComputablePred (fun p : D × ℕ => FriedbergSplitting.HasArrival p.1.1 p.1.2.1) :=
    (cLt (cArrival ha hs) (cAdd hs (Computable.const 1))).computablePred
  have hchosen : ComputablePred (fun p : D × ℕ =>
      chosenSide p.1.1 h p.1.2.1 p.1.2.2 = i % 2) :=
    (cEq (hc.comp Computable.fst) (Computable.const (i % 2))).computablePred
  have hx : ComputablePred (fun p : D × ℕ =>
      p.2 = FriedbergSplitting.arrival p.1.1 p.1.2.1) :=
    (cEq Computable.snd (cArrival ha hs)).computablePred
  have hp := cPredAnd harr (cPredAnd hchosen hx)
  have htest : Computable (fun p : D × ℕ => decide
      (FriedbergSplitting.HasArrival p.1.1 p.1.2.1 ∧
        chosenSide p.1.1 h p.1.2.1 p.1.2.2 = i % 2 ∧
        p.2 = FriedbergSplitting.arrival p.1.1 p.1.2.1)) := hp.decide
  have hbody : Computable₂ (fun p : D => fun x =>
      if FriedbergSplitting.HasArrival p.1 p.2.1 ∧
        chosenSide p.1 h p.2.1 p.2.2 = i % 2 ∧
        x = FriedbergSplitting.arrival p.1 p.2.1 then 1 else beta (sideCode p.2.2 i) x) :=
    cIte htest (Computable.const 1) (cBeta (cSide hz (Computable.const i)) Computable.snd)
  change Computable (fun p : D => FiniteInjury.tabulate (p.2.1 + 1)
    (fun x => if FriedbergSplitting.HasArrival p.1 p.2.1 ∧
      chosenSide p.1 h p.2.1 p.2.2 = i % 2 ∧ x = FriedbergSplitting.arrival p.1 p.2.1
      then 1 else beta (sideCode p.2.2 i) x))
  have ht : Computable₂ (fun p : D => fun n => FiniteInjury.tabulate n
      (fun x => if FriedbergSplitting.HasArrival p.1 p.2.1 ∧
        chosenSide p.1 h p.2.1 p.2.2 = i % 2 ∧
        x = FriedbergSplitting.arrival p.1 p.2.1 then 1 else beta (sideCode p.2.2 i) x)) :=
    cTabulate hbody
  exact Computable.comp (f := fun p : D × ℕ => FiniteInjury.tabulate p.2
    (fun x => if FriedbergSplitting.HasArrival p.1.1 p.1.2.1 ∧
      chosenSide p.1.1 h p.1.2.1 p.1.2.2 = i % 2 ∧
      x = FriedbergSplitting.arrival p.1.1 p.1.2.1 then 1 else beta (sideCode p.1.2.2 i) x))
    (g := fun p : D => (p, p.2.1 + 1)) ht
    (Computable.id.pair (cAdd (Computable.fst.comp Computable.snd) (Computable.const 1)))

set_option maxHeartbeats 800000 in
private theorem next_records_computable (h : Approximation) (hh : Computable₂ h) :
    Computable (fun p : ℕ × (ℕ × State) =>
      FiniteInjury.tabulate (p.2.1 + 1) (nextLength h p.2.1 p.2.2)) ∧
    Computable (fun p : ℕ × (ℕ × State) =>
      FiniteInjury.tabulate (p.2.1 + 1) (nextRestraint h p.2.1 p.2.2)) := by
  let D := ℕ × (ℕ × State)
  have hs : Computable (fun p : D × ℕ => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hz : Computable (fun p : D × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hlenBody : Computable₂ (fun p : D => fun q => nextLength h p.2.1 p.2.2 q) :=
    cNextLength h hh hs hz Computable.snd
  have hresBody : Computable₂ (fun p : D => fun q => nextRestraint h p.2.1 p.2.2 q) :=
    cNextRestraint h hh hs hz Computable.snd
  have hlenTab : Computable₂ (fun p : D => fun n =>
      FiniteInjury.tabulate n (nextLength h p.2.1 p.2.2)) := cTabulate hlenBody
  have hresTab : Computable₂ (fun p : D => fun n =>
      FiniteInjury.tabulate n (nextRestraint h p.2.1 p.2.2)) := cTabulate hresBody
  have hlen : Computable (fun p : D =>
      FiniteInjury.tabulate (p.2.1 + 1) (nextLength h p.2.1 p.2.2)) :=
    Computable.comp (f := fun p : D × ℕ => FiniteInjury.tabulate p.2 (nextLength h p.1.2.1 p.1.2.2))
      (g := fun p : D => (p, p.2.1 + 1)) hlenTab
      (Computable.id.pair (cAdd (Computable.fst.comp Computable.snd) (Computable.const 1)))
  have hres : Computable (fun p : D =>
      FiniteInjury.tabulate (p.2.1 + 1) (nextRestraint h p.2.1 p.2.2)) :=
    Computable.comp (f := fun p : D × ℕ => FiniteInjury.tabulate p.2 (nextRestraint h p.1.2.1 p.1.2.2))
      (g := fun p : D => (p, p.2.1 + 1)) hresTab
      (Computable.id.pair (cAdd (Computable.fst.comp Computable.snd) (Computable.const 1)))
  exact ⟨hlen, hres⟩

private theorem next_computable (h : Approximation) (hh : Computable₂ h) :
    Computable (fun p : ℕ × (ℕ × State) => next p.1 h p.2.1 p.2.2) := by
  let D := ℕ × (ℕ × State)
  have h₀ := next_side_computable h hh 0
  have h₁ := next_side_computable h hh 1
  obtain ⟨hlen, hres⟩ := next_records_computable h hh
  change Computable (fun p : D =>
    (nextSideCode p.1 h p.2.1 p.2.2 0, nextSideCode p.1 h p.2.1 p.2.2 1,
      FiniteInjury.tabulate (p.2.1 + 1) (nextLength h p.2.1 p.2.2),
      FiniteInjury.tabulate (p.2.1 + 1) (nextRestraint h p.2.1 p.2.2)))
  exact h₀.pair (h₁.pair (hlen.pair hres))

theorem stage_computable (a : ℕ) (h : Approximation) (hh : Computable₂ h) :
    Computable₂ (fun b s => stage b h s) ∧
      Computable (fun p : (ℕ × ℕ) × ℕ => stageBit a h p.1.1 p.1.2 p.2) ∧
      Computable₂ (lengthAt a h) ∧ Computable₂ (restraintAt a h) ∧
      ComputablePred (fun p : ℕ × ℕ => Expanded a h p.1 p.2) := by
  have hstep : Computable₂ (fun p : ℕ × ℕ => fun v : ℕ × State => next p.1 h v.1 v.2) :=
    Computable.comp (f := fun v : ℕ × (ℕ × State) => next v.1 h v.2.1 v.2.2)
      (g := fun p : (ℕ × ℕ) × (ℕ × State) => (p.1.1, p.2.1, p.2.2))
      (next_computable h hh) ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp Computable.snd).pair (Computable.snd.comp Computable.snd)))
  have hst : Computable (fun p : ℕ × ℕ =>
      Nat.rec (motive := fun _ => State) (0, 0, 0, 0) (fun n z => next p.1 h n z) p.2) :=
    Computable.nat_rec Computable.snd (Computable.const (0, 0, 0, 0)) hstep
  have hs : Computable₂ (fun b s => stage b h s) := hst.of_eq (fun p => by
    induction p.2 with
    | zero => rfl
    | succ n ih => simp only [stage, ← ih])
  have hsa : Computable (stage a h) := hs.comp (Computable.const a) Computable.id
  refine ⟨hs, ?_, ?_, ?_, ?_⟩
  · exact cBeta (cSide (hsa.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst)) Computable.snd
  · exact cLength (hsa.comp Computable.fst) Computable.snd
  · exact cRestraint (hsa.comp Computable.fst) Computable.snd
  · have hleft : ComputablePred (fun p : ℕ × ℕ => p.1 ≤ p.2) :=
      (cLe Computable.fst Computable.snd).computablePred
    have hright : ComputablePred (fun p : ℕ × ℕ => Expands h p.2 (stage a h p.2) p.1) :=
      cPredComp (expands_computable h hh) (Computable.snd.pair
        ((hsa.comp Computable.snd).pair Computable.fst))
    exact cPredAnd hleft hright

theorem effective_partition (a : ℕ) (h : Approximation) (hh : Computable₂ h) :
    REPred (piece a h 0) ∧ REPred (piece a h 1) ∧
      Disjoint (piece a h 0) (piece a h 1) ∧
      piece a h 0 ∪ piece a h 1 = EffectiveEnumerations.indexSet a := by
  have he (i : ℕ) : REPred (piece a h i) := by
    apply EffectiveEnumerations.approximation_enumerable
    have htest : Computable₂ (fun s x => stageBit a h s i x) :=
      Computable.comp (f := fun p : (ℕ × ℕ) × ℕ => stageBit a h p.1.1 p.1.2 p.2)
        (g := fun p : ℕ × ℕ => ((p.1, i), p.2)) (stage_computable a h hh).2.1
        ((Computable.fst.pair (Computable.const i)).pair Computable.snd)
    refine ⟨id, fun s x => stageBit a h s i x, Computable.id, htest,
      fun s x => beta_bits (stageCode a h s i) x, ?_, ?_, fun _ => Iff.rfl⟩
    · intro s x hx
      exact (stage_invariants a h s).2.2.1 i hx
    · intro s x hx
      exact stage_monotone a h i (Nat.le_succ s) hx
  refine ⟨he 0, he 1, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro x ⟨s, hs⟩ ⟨t, ht⟩
    exact Set.disjoint_left.mp (stage_invariants a h (max s t)).1
      (stage_monotone a h 0 (Nat.le_max_left s t) hs)
      (stage_monotone a h 1 (Nat.le_max_right s t) ht)
  · apply Set.ext
    intro x
    constructor
    · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
      · exact (FriedbergSplitting.scheduler_exhaustive a x).mpr
          ⟨s, (stage_invariants a h s).2.1 ▸ Or.inl hs⟩
      · exact (FriedbergSplitting.scheduler_exhaustive a x).mpr
          ⟨s, (stage_invariants a h s).2.1 ▸ Or.inr hs⟩
    · intro hx
      obtain ⟨s, hs⟩ := (FriedbergSplitting.scheduler_exhaustive a x).mp hx
      have hu := (stage_invariants a h s).2.1
      rw [← hu] at hs
      exact hs.elim (fun hm => Or.inl ⟨s, hm⟩) (fun hm => Or.inr ⟨s, hm⟩)

theorem prefix_settles (a : ℕ) (h : Approximation) (i k : ℕ) :
    ∃ T, ∀ s ≥ T, Agreement (stageCode a h s i) k (piece a h i) := by
  have hcover (x : ℕ) : x ∈ piece a h i ↔ ∃ s, x ∈ stageSet a h s i := Iff.rfl
  obtain ⟨T, hT⟩ := EffectiveEnumerations.prefix_settled_exists
    (piece a h i) (fun s => stageSet a h s i) (stage_monotone a h i) hcover k
  refine ⟨T, fun s hs x hx => ?_⟩
  have hm := EffectiveEnumerations.settling_persists (piece a h i)
    (fun s => stageSet a h s i) (stage_monotone a h i) hcover hT hs x hx
  rw [← finiteOracle_indicator (stageCode a h s i) x]
  change (if x ∈ stageSet a h s i then 1 else 0) = if x ∈ piece a h i then 1 else 0
  simp only [← hm]

end
end Lemmatheca.ComputabilityTheory.SacksSplitting
