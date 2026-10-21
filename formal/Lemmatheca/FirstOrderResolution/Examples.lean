import Lemmatheca.FirstOrderResolution.FirstOrderResolution

namespace Lemmatheca.Entry.FirstOrderResolution

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.HerbrandModels
open Lemmatheca.MathematicalLogic.FirstOrderResolution

universe u v w
variable {L : Language.{u, v}} {α : Type w}

noncomputable section

def constant (a : L.Functions 0) : L.Term α := .func a Fin.elim0
def unary (f : L.Functions 1) (t : L.Term α) : L.Term α := .func f (fun _ => t)
def unaryAtom (P : L.Relations 1) (t : L.Term α) : Atom L α := ⟨1, P, fun _ => t⟩
def binaryAtom (B : L.Relations 2) (s t : L.Term α) : Atom L α := ⟨2, B, ![s, t]⟩
def signed (b : Bool) (A : Atom L α) : FOLiteral L α := ⟨A, b⟩

def workedC (P : L.Relations 1) : FOClause L ℕ := {signed true (unaryAtom P (.var 0))}
def workedD (P Q : L.Relations 1) (f : L.Functions 1) : FOClause L ℕ :=
  {signed false (unaryAtom P (unary f (.var 0))), signed true (unaryAtom Q (.var 0))}
def workedF (Q : L.Relations 1) (a : L.Functions 0) : FOClause L ℕ :=
  {signed false (unaryAtom Q (constant a))}
def workedMiddle (Q : L.Relations 1) : FOClause L ℕ := {signed true (unaryAtom Q (.var 1))}
def workedMu (f : L.Functions 1) : ℕ → L.Term ℕ :=
  Lemmatheca.MathematicalLogic.TermUnification.single 0 (unary f (.var 1))
def workedNu (a : L.Functions 0) : ℕ → L.Term ℕ :=
  Lemmatheca.MathematicalLogic.TermUnification.single 2 (constant a)

@[simp] private theorem constant_subst {β : Type*} (a : L.Functions 0)
    (σ : α → L.Term β) : (constant a : L.Term α).subst σ = constant a := by
  unfold constant Term.subst
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] private theorem constant_relabel {β : Type*} (a : L.Functions 0)
    (r : α → β) : (constant a : L.Term α).relabel r = constant a := by
  unfold constant Term.relabel
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] private theorem unary_relabel {β : Type*} (f : L.Functions 1) (t : L.Term α)
    (r : α → β) : (unary f t).relabel r = unary f (t.relabel r) := rfl

@[simp] private theorem constant_realize {M : Type*} [L.Structure M]
    (a : L.Functions 0) (v : α → M) :
    (constant a : L.Term α).realize v = Structure.funMap a Fin.elim0 := by
  unfold constant Term.realize
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] private theorem unary_atom_realize {M : Type*} [L.Structure M]
    (P : L.Relations 1) (t : L.Term α) (v : α → M) :
    (unaryAtom P t).Realize v ↔ Structure.RelMap P (fun _ => t.realize v) := Iff.rfl

@[simp] private theorem constant_ne_var (a : L.Functions 0) (n : ℕ) :
    (constant a : L.Term ℕ) ≠ .var n := by simp [constant]

@[simp] private theorem var_ne_constant (a : L.Functions 0) (n : ℕ) :
    (.var n : L.Term ℕ) ≠ constant a := by simp [constant]

@[simp] private theorem unary_subst {β : Type*} (f : L.Functions 1) (t : L.Term α)
    (σ : α → L.Term β) : (unary f t).subst σ = unary f (t.subst σ) := rfl

@[simp] private theorem unary_atom_subst {β : Type*} (P : L.Relations 1) (t : L.Term α)
    (σ : α → L.Term β) : (unaryAtom P t).subst σ = unaryAtom P (t.subst σ) := rfl

@[simp] private theorem unary_atom_eq (P : L.Relations 1) (s t : L.Term α) :
    unaryAtom P s = unaryAtom P t ↔ s = t := by
  simp [unaryAtom, Atom.mk.injEq, funext_iff]

private theorem single_atom_mgu (P : L.Relations 1) (i : ℕ) (t : L.Term ℕ)
    (ht : t.subst (Lemmatheca.MathematicalLogic.TermUnification.single i t) = t) :
    AtomMGU.{u, v, 0} {unaryAtom P (.var i), unaryAtom P t}
      (Lemmatheca.MathematicalLogic.TermUnification.single i t) := by
  classical
  constructor
  · intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [Term.subst, Lemmatheca.MathematicalLogic.TermUnification.single, ht]
  · intro β σ hσ
    have he : σ i = t.subst σ := by
      apply (unary_atom_eq P _ _).mp
      simpa only [unary_atom_subst, Term.subst] using
        hσ (unaryAtom P (.var i)) (by simp) (unaryAtom P t) (by simp)
    refine ⟨σ, ?_⟩
    intro x
    by_cases hx : x = i
    · subst x
      simpa [Lemmatheca.MathematicalLogic.TermUnification.single] using he.symm
    · simp [Lemmatheca.MathematicalLogic.TermUnification.single, hx, Term.subst]

theorem worked_first_step (P Q : L.Relations 1) (f : L.Functions 1) :
    ∃ d : InferenceData (workedC P) (workedD P Q f),
      d.positiveFamily = {signed true (unaryAtom P (.var 0))} ∧
      d.negativeFamily = {signed false (unaryAtom P (unary f (.var 1)))} ∧
      d.unifier = workedMu f ∧ resolvent d = workedMiddle Q := by
  classical
  let d : InferenceData (workedC P) (workedD P Q f) := {
    positiveFamily := {signed true (unaryAtom P (.var 0))}
    negativeFamily := {signed false (unaryAtom P (unary f (.var 1)))}
    positive_subset := by
      simp [leftCopy, renameClause, clauseSubst, literalSubst, workedC, even,
        signed, Term.subst]
    negative_subset := by
      simp [rightCopy, renameClause, clauseSubst, literalSubst, workedD, odd,
        signed, Term.subst]
    positive_nonempty := Finset.singleton_nonempty _
    negative_nonempty := Finset.singleton_nonempty _
    positive_sign := by simp [signed]
    negative_sign := by simp [signed]
    unifier := workedMu f
    mostGeneral := by
      simpa [signed, workedMu] using single_atom_mgu P 0 (unary f (.var 1)) (by
        simp [Term.subst, Lemmatheca.MathematicalLogic.TermUnification.single]) }
  refine ⟨d, rfl, rfl, rfl, ?_⟩
  simp [Lemmatheca.MathematicalLogic.FirstOrderResolution.resolvent, d,
    leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
    workedC, workedD, workedMiddle, workedMu, even, odd, signed, Term.subst,
    Lemmatheca.MathematicalLogic.TermUnification.single,
    Finset.sdiff_singleton_eq_erase, Finset.erase_insert_eq_erase,
    PropLiteral.mk.injEq]

theorem worked_second_step (Q : L.Relations 1) (a : L.Functions 0) :
    ∃ d : InferenceData (workedMiddle Q) (workedF Q a),
      d.positiveFamily = {signed true (unaryAtom Q (.var 2))} ∧
      d.negativeFamily = {signed false (unaryAtom Q (constant a))} ∧
      d.unifier = workedNu a ∧ resolvent d = ∅ := by
  classical
  let d : InferenceData (workedMiddle Q) (workedF Q a) := {
    positiveFamily := {signed true (unaryAtom Q (.var 2))}
    negativeFamily := {signed false (unaryAtom Q (constant a))}
    positive_subset := by
      simp [leftCopy, renameClause, clauseSubst, literalSubst, workedMiddle, even,
        signed, Term.subst]
    negative_subset := by
      simp [rightCopy, renameClause, clauseSubst, literalSubst, workedF, odd, signed]
    positive_nonempty := Finset.singleton_nonempty _
    negative_nonempty := Finset.singleton_nonempty _
    positive_sign := by simp [signed]
    negative_sign := by simp [signed]
    unifier := workedNu a
    mostGeneral := by
      simpa [signed, workedNu] using single_atom_mgu Q 2 (constant a) (by simp) }
  refine ⟨d, rfl, rfl, rfl, ?_⟩
  simp [Lemmatheca.MathematicalLogic.FirstOrderResolution.resolvent, d,
    leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
    workedMiddle, workedF, even, odd, signed, Term.subst]

theorem worked_refutation (P Q : L.Relations 1) (f : L.Functions 1) (a : L.Functions 0) :
    Derives ({workedC P, workedD P Q f, workedF Q a} : Set (FOClause L ℕ)) ∅ := by
  obtain ⟨d, _, _, _, hd⟩ := worked_first_step P Q f
  obtain ⟨e, _, _, _, he⟩ := worked_second_step Q a
  rw [← he]
  apply Derives.resolve e
  · rw [← hd]
    exact Derives.resolve d (Derives.premise (by simp)) (Derives.premise (by simp))
  · exact Derives.premise (by simp)

def barberC (B : L.Relations 2) (a : L.Functions 0) : FOClause L ℕ :=
  {signed true (binaryAtom B (.var 0) (.var 0)), signed true (binaryAtom B (constant a) (.var 0))}
def barberD (B : L.Relations 2) (a : L.Functions 0) : FOClause L ℕ :=
  {signed false (binaryAtom B (constant a) (.var 0)), signed false (binaryAtom B (.var 0) (.var 0))}
def barberMu (a : L.Functions 0) (n : ℕ) : L.Term ℕ :=
  if n = 0 ∨ n = 1 then constant a else .var n

@[simp] private theorem binary_atom_subst {β : Type*} (B : L.Relations 2) (s t : L.Term α)
    (σ : α → L.Term β) : (binaryAtom B s t).subst σ =
      binaryAtom B (s.subst σ) (t.subst σ) := by
  unfold binaryAtom Atom.subst
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] private theorem binary_atom_eq (B : L.Relations 2) (s t s' t' : L.Term α) :
    binaryAtom B s t = binaryAtom B s' t' ↔ s = s' ∧ t = t' := by
  simp [binaryAtom, Atom.mk.injEq, funext_iff, Fin.forall_fin_two]

@[simp] private theorem binary_atom_realize {M : Type*} [L.Structure M]
    (B : L.Relations 2) (s t : L.Term α) (v : α → M) :
    (binaryAtom B s t).Realize v ↔ Structure.RelMap B ![s.realize v, t.realize v] := by
  unfold binaryAtom Atom.Realize
  have he : (fun i : Fin 2 => (![s, t] i).realize v) = ![s.realize v, t.realize v] := by
    funext i
    fin_cases i <;> rfl
  rw [he]

theorem barber_unsatisfiable (B : L.Relations 2) (a : L.Functions 0) :
    ¬ ClauseSatisfiable ({barberC B a, barberD B a} : Set (FOClause L ℕ)) := by
  rintro ⟨M, hM⟩
  let v : ℕ → M := fun _ => Structure.funMap a Fin.elim0
  have hC := (clause_formula_realize _ v).mp (hM (barberC B a) (by simp) v)
  have hD := (clause_formula_realize _ v).mp (hM (barberD B a) (by simp) v)
  simp [ClauseRealize, barberC, barberD, signed, v] at hC hD
  exact hD hC

theorem barber_step (B : L.Relations 2) (a : L.Functions 0) :
    ∃ d : InferenceData (barberC B a) (barberD B a),
      d.positiveFamily = leftCopy (barberC B a) ∧
      d.negativeFamily = rightCopy (barberD B a) ∧
      d.unifier = barberMu a ∧ resolvent d = ∅ := by
  classical
  have hAtoms : ((leftCopy (barberC B a) ∪ rightCopy (barberD B a)).image
      PropLiteral.atom) = {binaryAtom B (.var 0) (.var 0),
        binaryAtom B (constant a) (.var 0), binaryAtom B (constant a) (.var 1),
        binaryAtom B (.var 1) (.var 1)} := by
    ext A
    simp [leftCopy, rightCopy, renameClause, clauseSubst, literalSubst, barberC,
      barberD, even, odd, signed, Term.subst]
    tauto
  let d : InferenceData (barberC B a) (barberD B a) := {
    positiveFamily := leftCopy (barberC B a)
    negativeFamily := rightCopy (barberD B a)
    positive_subset := Finset.Subset.refl _
    negative_subset := Finset.Subset.refl _
    positive_nonempty := by
      simp [leftCopy, renameClause, clauseSubst, barberC]
    negative_nonempty := by
      simp [rightCopy, renameClause, clauseSubst, barberD]
    positive_sign := by
      simp [leftCopy, renameClause, clauseSubst, barberC, literalSubst, signed]
    negative_sign := by
      simp [rightCopy, renameClause, clauseSubst, barberD, literalSubst, signed]
    unifier := barberMu a
    mostGeneral := by
      rw [hAtoms]
      constructor
      · simp [AtomUnifies, barberMu, Term.subst]
      · intro β σ hσ
        have h0 : σ 0 = constant a := by
          have he := hσ (binaryAtom B (.var 0) (.var 0)) (by simp)
            (binaryAtom B (constant a) (.var 0)) (by simp)
          simpa only [binary_atom_subst, Term.subst, constant_subst,
            binary_atom_eq, eq_self_iff_true, and_true] using he
        have h1 : σ 1 = constant a := by
          have he := hσ (binaryAtom B (.var 1) (.var 1)) (by simp)
            (binaryAtom B (constant a) (.var 1)) (by simp)
          simpa only [binary_atom_subst, constant_subst, Term.subst,
            binary_atom_eq, eq_self_iff_true, and_true] using he
        refine ⟨σ, ?_⟩
        intro n
        by_cases hn0 : n = 0
        · subst n
          simpa [barberMu] using h0.symm
        by_cases hn1 : n = 1
        · subst n
          simpa [barberMu] using h1.symm
        · simp [barberMu, hn0, hn1, Term.subst] }
  exact ⟨d, rfl, rfl, rfl, by
    simp [Lemmatheca.MathematicalLogic.FirstOrderResolution.resolvent, d, clauseSubst]⟩

theorem barber_single_pair_tautological (B : L.Relations 2) (a : L.Functions 0)
    (d : InferenceData (barberC B a) (barberD B a))
    (hS : d.positiveFamily.card = 1) (hT : d.negativeFamily.card = 1) :
    ∃ A : Atom L ℕ, signed true A ∈ resolvent d ∧ signed false A ∈ resolvent d := by
  classical
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hS
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hT
  have hsc := d.positive_subset (show s ∈ d.positiveFamily by simp [hs])
  have htd := d.negative_subset (show t ∈ d.negativeFamily by simp [ht])
  have hu := d.mostGeneral.1 s.atom
    (Finset.mem_image.mpr ⟨s, Finset.mem_union_left _ (by simp [hs]), rfl⟩)
    t.atom (Finset.mem_image.mpr ⟨t, Finset.mem_union_right _ (by simp [ht]), rfl⟩)
  simp [leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
    barberC, barberD, even, odd, signed, Term.subst] at hsc htd
  have hmem (l : FOLiteral L ℕ)
      (hl : l ∈ (leftCopy (barberC B a) \ d.positiveFamily) ∪
        (rightCopy (barberD B a) \ d.negativeFamily)) :
      literalSubst d.unifier l ∈ Lemmatheca.MathematicalLogic.FirstOrderResolution.resolvent d :=
    Finset.mem_image.mpr ⟨l, hl, rfl⟩
  rcases hsc with rfl | rfl <;> rcases htd with rfl | rfl <;>
    simp only [binary_atom_subst, Term.subst, constant_subst] at hu
  · have he : d.unifier 0 = constant a ∧ d.unifier 0 = d.unifier 1 := by
      simpa [signed] using (binary_atom_eq B _ _ _ _).mp hu
    refine ⟨binaryAtom B (constant a) (d.unifier 0), ?_, ?_⟩
    · have hm := hmem (signed true (binaryAtom B (constant a) (.var 0))) (by
        simp [hs, ht, leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
          barberC, barberD, even, odd, signed, Term.subst])
      simpa [literalSubst, signed, Term.subst] using hm
    · have hm := hmem (signed false (binaryAtom B (.var 1) (.var 1))) (by
        simp [hs, ht, leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
          barberC, barberD, even, odd, signed, Term.subst])
      simpa [literalSubst, signed, Term.subst, he.1, ← he.2] using hm
  · have he : d.unifier 0 = d.unifier 1 := by
      simpa [signed] using ((binary_atom_eq B _ _ _ _).mp hu).1
    refine ⟨binaryAtom B (constant a) (d.unifier 0), ?_, ?_⟩
    · have hm := hmem (signed true (binaryAtom B (constant a) (.var 0))) (by
        simp [hs, ht, leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
          barberC, barberD, even, odd, signed, Term.subst])
      simpa [literalSubst, signed, Term.subst] using hm
    · have hm := hmem (signed false (binaryAtom B (constant a) (.var 1))) (by
        simp [hs, ht, leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
          barberC, barberD, even, odd, signed, Term.subst])
      simpa [literalSubst, signed, Term.subst, he] using hm
  · have he : d.unifier 0 = d.unifier 1 := by
      simpa [signed] using ((binary_atom_eq B _ _ _ _).mp hu).2
    refine ⟨binaryAtom B (d.unifier 0) (d.unifier 0), ?_, ?_⟩
    · have hm := hmem (signed true (binaryAtom B (.var 0) (.var 0))) (by
        simp [hs, ht, leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
          barberC, barberD, even, odd, signed, Term.subst])
      simpa [literalSubst, signed, Term.subst] using hm
    · have hm := hmem (signed false (binaryAtom B (.var 1) (.var 1))) (by
        simp [hs, ht, leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
          barberC, barberD, even, odd, signed, Term.subst])
      simpa [literalSubst, signed, Term.subst, he] using hm
  · have he : constant a = d.unifier 1 ∧ d.unifier 0 = d.unifier 1 := by
      simpa [signed] using (binary_atom_eq B _ _ _ _).mp hu
    refine ⟨binaryAtom B (d.unifier 0) (d.unifier 0), ?_, ?_⟩
    · have hm := hmem (signed true (binaryAtom B (.var 0) (.var 0))) (by
        simp [hs, ht, leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
          barberC, barberD, even, odd, signed, Term.subst])
      simpa [literalSubst, signed, Term.subst] using hm
    · have hm := hmem (signed false (binaryAtom B (constant a) (.var 1))) (by
        simp [hs, ht, leftCopy, rightCopy, renameClause, clauseSubst, literalSubst,
          barberC, barberD, even, odd, signed, Term.subst])
      simpa [literalSubst, signed, Term.subst, ← he.1, he.2] using hm

/-- Two literals whose variables remain independent in singleton-MGU steps. -/
def VariablePair (P : L.Relations 1) (C : FOClause L ℕ) : Prop :=
  ∃ i j : ℕ, i ≠ j ∧ ∃ s t : Bool,
    C = {signed s (unaryAtom P (.var i)), signed t (unaryAtom P (.var j))}

def pairPositive (P : L.Relations 1) : FOClause L ℕ :=
  {signed true (unaryAtom P (.var 0)), signed true (unaryAtom P (.var 1))}
def pairNegative (P : L.Relations 1) : FOClause L ℕ :=
  {signed false (unaryAtom P (.var 0)), signed false (unaryAtom P (.var 1))}
def pairTheory (P : L.Relations 1) : Set (FOClause L ℕ) := {pairPositive P, pairNegative P}
def pairMu (n : ℕ) : L.Term ℕ := if n ≤ 3 then .var 0 else .var n

private theorem selected_pair (P : L.Relations 1) {C : FOClause L ℕ}
    (hC : VariablePair P C) (r : ℕ → ℕ) (F : FOClause L ℕ) (b : Bool)
    (hsub : F ⊆ renameClause r C) (hcard : F.card = 1)
    (hsign : ∀ l ∈ F, l.positive = b) :
    ∃ i j : ℕ, i ≠ j ∧ ∃ t : Bool,
      renameClause r C = {signed b (unaryAtom P (.var (r i))),
        signed t (unaryAtom P (.var (r j)))} ∧
      F = {signed b (unaryAtom P (.var (r i)))} := by
  classical
  obtain ⟨i, j, hij, s, t, rfl⟩ := hC
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hcard
  have hm := hsub (by rw [hl]; exact Finset.mem_singleton_self l)
  have hb := hsign l (by rw [hl]; exact Finset.mem_singleton_self l)
  simp only [renameClause, clauseSubst, Finset.image_insert, Finset.image_singleton] at hm ⊢
  have hsimp (c : Bool) (k : ℕ) :
      literalSubst (fun x => Term.var (r x)) (signed c (unaryAtom P (.var k))) =
        signed c (unaryAtom P (.var (r k))) := rfl
  simp only [hsimp, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
  rcases hm with rfl | rfl
  · change s = b at hb
    subst s
    exact ⟨i, j, hij, t, rfl, hl⟩
  · change t = b at hb
    subst t
    exact ⟨j, i, hij.symm, s, Finset.pair_comm _ _, hl⟩

private theorem untouched_mgu_variables (P : L.Relations 1)
    (a b c e : ℕ) (hab : a ≠ b) (hcb : c ≠ b) (hae : a ≠ e) (hce : c ≠ e)
    (hbe : b ≠ e) (μ : ℕ → L.Term ℕ)
    (hmgu : AtomMGU.{u, v, 0} {unaryAtom P (.var a), unaryAtom P (.var c)} μ) :
    ∃ x y : ℕ, x ≠ y ∧ μ b = .var x ∧ μ e = .var y := by
  classical
  let σ : ℕ → L.Term ℕ := fun n => if n = b then .var 1 else if n = e then .var 2 else .var 0
  have hσ : AtomUnifies σ {unaryAtom P (.var a), unaryAtom P (.var c)} := by
    intro A hA B hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;>
      simp [Atom.subst, unaryAtom, Term.subst, σ, hab, hcb, hae, hce]
  obtain ⟨ρ, hρ⟩ := hmgu.2 ℕ σ hσ
  have hb : (μ b).subst ρ = .var 1 := by simpa [σ] using hρ b
  have he : (μ e).subst ρ = .var 2 := by simpa [σ, hbe.symm] using hρ e
  cases hμb : μ b with
  | var x =>
    cases hμe : μ e with
    | var y =>
      refine ⟨x, y, ?_, rfl, rfl⟩
      intro hxy
      have hb' : ρ x = .var 1 := by simpa only [hμb, Term.subst] using hb
      have he' : ρ y = .var 2 := by simpa only [hμe, Term.subst] using he
      rw [hxy, he'] at hb'
      cases hb'
    | func f ts => rw [hμe] at he; cases he
  | func f ts => rw [hμb] at hb; cases hb


theorem variable_pair_step (P : L.Relations 1) {C D : FOClause L ℕ}
    (hC : VariablePair P C) (hD : VariablePair P D) (d : InferenceData C D)
    (hS : d.positiveFamily.card = 1) (hT : d.negativeFamily.card = 1) :
    VariablePair P (resolvent d) := by
  classical
  obtain ⟨i, j, hij, s, hleft, hpos⟩ :=
    selected_pair P hC even d.positiveFamily true d.positive_subset hS d.positive_sign
  obtain ⟨k, l, hkl, t, hright, hneg⟩ :=
    selected_pair P hD odd d.negativeFamily false d.negative_subset hT d.negative_sign
  have hmgu : AtomMGU.{u, v, 0}
      {unaryAtom P (.var (even i)), unaryAtom P (.var (odd k))} d.unifier := by
    simpa [hpos, hneg, signed] using d.mostGeneral
  obtain ⟨x, y, hxy, hx, hy⟩ := untouched_mgu_variables P
    (even i) (even j) (odd k) (odd l)
    (by dsimp [even]; omega) (by dsimp [even, odd]; omega)
    (by dsimp [even, odd]; omega) (by dsimp [odd]; omega)
    (by dsimp [even, odd]; omega) d.unifier hmgu
  refine ⟨x, y, hxy, s, t, ?_⟩
  have hneLeft : signed true (unaryAtom P (.var (even i))) ≠
      signed s (unaryAtom P (.var (even j))) := by
    intro heq
    have hatom := congrArg PropLiteral.atom heq
    have : even i = even j := by
      simpa [signed, unaryAtom, Atom.mk.injEq, funext_iff] using hatom
    dsimp [even] at this
    omega
  have hneRight : signed false (unaryAtom P (.var (odd k))) ≠
      signed t (unaryAtom P (.var (odd l))) := by
    intro heq
    have hatom := congrArg PropLiteral.atom heq
    have : odd k = odd l := by
      simpa [signed, unaryAtom, Atom.mk.injEq, funext_iff] using hatom
    dsimp [odd] at this
    omega
  unfold Lemmatheca.MathematicalLogic.FirstOrderResolution.resolvent
  change clauseSubst d.unifier
    ((renameClause even C \ d.positiveFamily) ∪
     (renameClause odd D \ d.negativeFamily)) = _
  rw [hleft, hright, hpos, hneg]
  simp only [Finset.sdiff_singleton_eq_erase, Finset.erase_insert_eq_erase]
  rw [Finset.erase_eq_of_notMem (by simpa only [Finset.mem_singleton] using hneLeft),
    Finset.erase_eq_of_notMem (by simpa only [Finset.mem_singleton] using hneRight)]
  simp [clauseSubst, literalSubst, signed, Atom.subst, unaryAtom, Term.subst, hx, hy]


theorem variable_pair_invariant (P : L.Relations 1) {Γ : Set (FOClause L ℕ)}
    (hΓ : ∀ C ∈ Γ, VariablePair P C) {C : FOClause L ℕ} (d : BinaryDerives Γ C) :
    VariablePair P C := by
  induction d with
  | premise hC => exact hΓ _ hC
  | resolve data hS hT _ _ ihC ihD =>
      exact variable_pair_step P ihC ihD data hS hT

theorem pair_unsatisfiable (P : L.Relations 1) : ¬ ClauseSatisfiable (pairTheory P) := by
  rintro ⟨M, hM⟩
  let v : ℕ → M := fun _ => Classical.choice inferInstance
  have hC := (clause_formula_realize _ v).mp (hM (pairPositive P) (by simp [pairTheory]) v)
  have hD := (clause_formula_realize _ v).mp (hM (pairNegative P) (by simp [pairTheory]) v)
  simp [ClauseRealize, pairPositive, pairNegative, signed, v] at hC hD
  exact hD hC

theorem pair_binary_no_refutation (P : L.Relations 1) :
    ¬ BinaryDerives (pairTheory P) ∅ := by
  intro h
  have hi := variable_pair_invariant P (Γ := pairTheory P) (by
    intro C hC
    simp only [pairTheory, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · exact ⟨0, 1, by omega, true, true, rfl⟩
    · exact ⟨0, 1, by omega, false, false, rfl⟩) h
  rcases hi with ⟨i, j, _, s, t, he⟩
  have hm : signed s (unaryAtom P (.var i)) ∈ (∅ : FOClause L ℕ) := by
    rw [he]
    simp
  exact Finset.notMem_empty _ hm

theorem pair_generalized_step (P : L.Relations 1) :
    ∃ d : InferenceData (pairPositive P) (pairNegative P),
      d.positiveFamily = leftCopy (pairPositive P) ∧
      d.negativeFamily = rightCopy (pairNegative P) ∧
      d.unifier = pairMu ∧ resolvent d = ∅ := by
  classical
  have hAtoms : ((leftCopy (pairPositive P) ∪ rightCopy (pairNegative P)).image
      PropLiteral.atom) = {unaryAtom P (.var 0), unaryAtom P (.var 2),
        unaryAtom P (.var 1), unaryAtom P (.var 3)} := by
    ext A
    simp [leftCopy, rightCopy, renameClause, clauseSubst, literalSubst, pairPositive,
      pairNegative, even, odd, signed, Term.subst]
    tauto
  let d : InferenceData (pairPositive P) (pairNegative P) := {
    positiveFamily := leftCopy (pairPositive P)
    negativeFamily := rightCopy (pairNegative P)
    positive_subset := Finset.Subset.refl _
    negative_subset := Finset.Subset.refl _
    positive_nonempty := by simp [leftCopy, renameClause, clauseSubst, pairPositive]
    negative_nonempty := by simp [rightCopy, renameClause, clauseSubst, pairNegative]
    positive_sign := by
      simp [leftCopy, renameClause, clauseSubst, pairPositive, literalSubst, signed]
    negative_sign := by
      simp [rightCopy, renameClause, clauseSubst, pairNegative, literalSubst, signed]
    unifier := pairMu
    mostGeneral := by
      rw [hAtoms]
      constructor
      · simp [AtomUnifies, pairMu, Term.subst]
      · intro β σ hσ
        have hi (n : ℕ) (hn : n ≤ 3) : σ n = σ 0 := by
          apply (unary_atom_eq P _ _).mp
          simpa only [unary_atom_subst, Term.subst] using
            hσ (unaryAtom P (.var n)) (by interval_cases n <;> simp)
              (unaryAtom P (.var 0)) (by simp)
        refine ⟨σ, ?_⟩
        intro n
        by_cases hn : n ≤ 3
        · simpa [pairMu, hn, Term.subst] using (hi n hn).symm
        · simp [pairMu, hn, Term.subst] }
  exact ⟨d, rfl, rfl, rfl, by
    simp [Lemmatheca.MathematicalLogic.FirstOrderResolution.resolvent, d, clauseSubst]⟩

theorem pair_generalized_refutation (P : L.Relations 1) :
    Derives (pairTheory P) ∅ := by
  obtain ⟨d, _, _, _, hd⟩ := pair_generalized_step P
  rw [← hd]
  exact Derives.resolve d (Derives.premise (by simp [pairTheory]))
    (Derives.premise (by simp [pairTheory]))

/-- Keeping only one preimage fails for the actual shared clause substitution. -/
theorem duplicate_pivot_fiber (P : L.Relations 1) (a : L.Functions 0) :
    let γ : ℕ → GroundTerm L := fun _ => constant a
    let p : GroundAtom L := unaryAtom P (constant a)
    clauseSubst γ (pairPositive P) = {signed true p} ∧
      clauseSubst γ ((pairPositive P).erase (signed true (unaryAtom P (.var 0)))) = {signed true p} ∧
      clauseSubst γ ((pairPositive P).erase (signed true (unaryAtom P (.var 1)))) = {signed true p} := by
  classical
  simp [clauseSubst, pairPositive, literalSubst, signed, Term.subst,
    Finset.erase_insert_of_ne, PropLiteral.mk.injEq]

end
end Lemmatheca.Entry.FirstOrderResolution
