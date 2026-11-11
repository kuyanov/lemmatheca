import Lemmatheca.FunctionalCompletenessCriterion.Basic

namespace Lemmatheca.MathematicalLogic.FunctionalCompletenessCriterion

open Propositional

def PreservesZero {n : ℕ} (f : TruthFunction n) : Prop := f (fun _ => false) = false

def PreservesOne {n : ℕ} (f : TruthFunction n) : Prop := f (fun _ => true) = true

def SelfDual {n : ℕ} (f : TruthFunction n) : Prop :=
  ∀ row, f (fun i => !(row i)) = !(f row)

def parity : (n : ℕ) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, row => Bool.xor (row 0) (parity n (fun i => row i.succ))

def affineValue {n : ℕ} (c : Bool) (coeff : Fin n → Bool) : TruthFunction n :=
  fun row => Bool.xor c (parity n (fun i => coeff i && row i))

def Affine {n : ℕ} (f : TruthFunction n) : Prop :=
  ∃ c coeff, f = affineValue c coeff

def difference {n : ℕ} (f : TruthFunction n) (i : Fin n) (row : Fin n → Bool) : Bool :=
  Bool.xor (f (Function.update row i false)) (f (Function.update row i true))

def EscapesAll (S : Set Operation) : Prop :=
  (∃ g ∈ S, ¬ PreservesZero g.table) ∧
  (∃ g ∈ S, ¬ PreservesOne g.table) ∧
  (∃ g ∈ S, ¬ Monotone g.table) ∧
  (∃ g ∈ S, ¬ SelfDual g.table) ∧
  (∃ g ∈ S, ¬ Affine g.table)

private theorem parity_zero (n : ℕ) : parity n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [parity] using ih

private theorem parity_xor (n : ℕ) (a b : Fin n → Bool) :
    parity n (fun i => Bool.xor (a i) (b i)) = Bool.xor (parity n a) (parity n b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [parity, ih]
    cases a 0 <;> cases b 0 <;> simp

private theorem parity_single {n : ℕ} (i : Fin n) (b : Bool) :
    parity n (fun j => if j = i then b else false) = b := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [parity, Fin.succ_ne_zero, parity_zero]
    | succ i => simpa [parity, Fin.succ_inj, Ne.symm (Fin.succ_ne_zero i)] using ih i

private theorem affine_constant {n : ℕ} (b : Bool) : Affine (fun _ : Fin n → Bool => b) := by
  refine ⟨b, fun _ => false, ?_⟩
  funext row
  simp [affineValue, parity_zero]

private theorem affine_projection {n : ℕ} (i : Fin n) : Affine (fun row => row i) := by
  refine ⟨false, fun j => j == i, ?_⟩
  funext row
  simp only [affineValue, Bool.false_xor]
  have he : (fun j => (j == i) && row j) = (fun j => if j = i then row i else false) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [he, parity_single]

private theorem affine_xor {n : ℕ} {f g : TruthFunction n} (hf : Affine f) (hg : Affine g) :
    Affine (fun row => Bool.xor (f row) (g row)) := by
  obtain ⟨c, a, rfl⟩ := hf
  obtain ⟨d, b, rfl⟩ := hg
  refine ⟨Bool.xor c d, fun i => Bool.xor (a i) (b i), ?_⟩
  funext row
  have he : (fun i => Bool.xor (a i) (b i) && row i) =
      (fun i => Bool.xor (a i && row i) (b i && row i)) := by
    funext i
    cases a i <;> cases b i <;> cases row i <;> rfl
  simp only [affineValue, he, parity_xor]
  cases c <;> cases d <;> simp

private theorem affine_parity {n m : ℕ} (fs : Fin n → TruthFunction m)
    (hfs : ∀ i, Affine (fs i)) : Affine (fun row => parity n (fun i => fs i row)) := by
  induction n with
  | zero => exact affine_constant false
  | succ n ih => exact affine_xor (hfs 0) (ih (fun i => fs i.succ) (fun i => hfs i.succ))

private theorem affine_compose {n m : ℕ} {f : TruthFunction n} (hf : Affine f)
    (args : Fin n → TruthFunction m) (ha : ∀ i, Affine (args i)) :
    Affine (superpose f args) := by
  obtain ⟨c, coeff, rfl⟩ := hf
  apply affine_xor (affine_constant c)
  apply affine_parity
  intro i
  cases h : coeff i
  · simpa [h] using (affine_constant (n := m) false)
  · simpa [h] using ha i

private theorem update_cons {n : ℕ} (b : Bool) (row : Fin n → Bool) (i : Fin n) (v : Bool) :
    Function.update (Fin.cases b row : Fin (n+1) → Bool) i.succ v = (Fin.cases b (Function.update row i v) : Fin (n+1) → Bool) := by
  funext j
  cases j using Fin.cases <;> simp [Function.update_apply, Fin.succ_inj, Ne.symm (Fin.succ_ne_zero i)]

private theorem update_head {n : ℕ} (b v : Bool) (row : Fin n → Bool) :
    Function.update (Fin.cases b row : Fin (n+1) → Bool) 0 v = (Fin.cases v row : Fin (n+1) → Bool) := by
  funext j
  cases j using Fin.cases <;> simp

private theorem parity_update_xor {n : ℕ} (coeff row : Fin n → Bool) (i : Fin n) :
    Bool.xor (parity n (fun j => coeff j && Function.update row i false j))
      (parity n (fun j => coeff j && Function.update row i true j)) = coeff i := by
  rw [← parity_xor]
  have he : (fun j => Bool.xor (coeff j && Function.update row i false j)
      (coeff j && Function.update row i true j)) = (fun j => if j = i then coeff i else false) := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [h]
  rw [he, parity_single]

theorem nullary_properties (f : TruthFunction 0) :
    Affine f ∧ Monotone f ∧ ¬ SelfDual f ∧
      (PreservesZero f ↔ f (fun i => Fin.elim0 i) = false) ∧
      (PreservesOne f ↔ f (fun i => Fin.elim0 i) = true) := by
  have he : ∀ a b : Fin 0 → Bool, a = b := fun a b => funext fun i => Fin.elim0 i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hf : f = fun _ => f (fun i => Fin.elim0 i) :=
      funext fun row => congrArg f (he row _)
    rw [hf]
    exact affine_constant _
  · intro a b hab
    rw [he a b]
  · intro hd
    have h := hd (fun i => Fin.elim0 i)
    rw [he (fun i => !((fun j => Fin.elim0 j) i)) (fun i => Fin.elim0 i)] at h
    cases hv : f (fun i => Fin.elim0 i) <;> simp_all
  · unfold PreservesZero
    rw [he (fun _ => false) (fun i => Fin.elim0 i)]
  · unfold PreservesOne
    rw [he (fun _ => true) (fun i => Fin.elim0 i)]

theorem generated_preservesZero {S : Set Operation} {n : ℕ} (f : TruthFunction n)
    (hS : ∀ g ∈ S, PreservesZero g.table) (hf : Generates S f) : PreservesZero f := by
  obtain ⟨t, ht⟩ := hf
  rw [PreservesZero, ← ht]
  clear ht
  induction t with
  | atom a => rfl
  | gate g hg args ih =>
    simpa only [PreservesZero, termEval, funext ih] using hS g hg

theorem generated_preservesOne {S : Set Operation} {n : ℕ} (f : TruthFunction n)
    (hS : ∀ g ∈ S, PreservesOne g.table) (hf : Generates S f) : PreservesOne f := by
  obtain ⟨t, ht⟩ := hf
  rw [PreservesOne, ← ht]
  clear ht
  induction t with
  | atom a => rfl
  | gate g hg args ih =>
    simpa only [PreservesOne, termEval, funext ih] using hS g hg

theorem generated_monotone {S : Set Operation} {n : ℕ} (f : TruthFunction n)
    (hS : ∀ g ∈ S, Monotone g.table) (hf : Generates S f) : Monotone f := by
  obtain ⟨t, ht⟩ := hf
  have he : f = fun row => termEval row t := funext fun row => (ht row).symm
  rw [he]
  clear he ht
  induction t with
  | atom a => exact fun a b hab => hab _
  | gate g hg args ih => exact fun a b hab => hS g hg (fun i => ih i hab)

theorem generated_selfDual {S : Set Operation} {n : ℕ} (f : TruthFunction n)
    (hS : ∀ g ∈ S, SelfDual g.table) (hf : Generates S f) : SelfDual f := by
  obtain ⟨t, ht⟩ := hf
  have he : f = fun row => termEval row t := funext fun row => (ht row).symm
  rw [he]
  clear he ht
  induction t with
  | atom a => exact fun _ => rfl
  | gate g hg args ih =>
    intro row
    simp only [termEval]
    rw [show (fun i => termEval (fun j => !row j) (args i)) =
        (fun i => !(termEval row (args i))) from funext (fun i => ih i row)]
    exact hS g hg _

theorem generated_affine {S : Set Operation} {n : ℕ} (f : TruthFunction n)
    (hS : ∀ g ∈ S, Affine g.table) (hf : Generates S f) : Affine f := by
  obtain ⟨t, ht⟩ := hf
  have he : f = fun row => termEval row t := funext fun row => (ht row).symm
  rw [he]
  clear he ht
  induction t with
  | atom a => exact affine_projection a
  | gate g hg args ih => exact affine_compose (hS g hg) _ ih

theorem difference_ignores_coordinate {n : ℕ} (f : TruthFunction n) (i : Fin n)
    (row : Fin n → Bool) (b : Bool) :
    difference f i (Function.update row i b) = difference f i row := by
  simp [difference, Function.update_idem]

theorem difference_affineValue {n : ℕ} (c : Bool) (coeff : Fin n → Bool)
    (i : Fin n) (row : Fin n → Bool) :
    difference (affineValue c coeff) i row = coeff i := by
  unfold difference affineValue
  have h := parity_update_xor coeff row i
  cases c <;> simpa using h

theorem affine_iff_constant_differences {n : ℕ} (f : TruthFunction n) :
    Affine f ↔ ∀ i row row', difference f i row = difference f i row' := by
  constructor
  · rintro ⟨c, coeff, rfl⟩ i row row'
    rw [difference_affineValue, difference_affineValue]
  · intro h
    induction n with
    | zero => exact (nullary_properties f).1
    | succ n ih =>
      let f0 : TruthFunction n := fun row => f (Fin.cases false row)
      have ht : ∀ i row row', difference f0 i row = difference f0 i row' := by
        intro i row row'
        simpa only [difference, update_cons] using
          h i.succ (Fin.cases false row) (Fin.cases false row')
      have ha := affine_compose (ih f0 ht)
        (fun i row => row i.succ) (fun i => affine_projection i.succ)
      let d := difference f 0 (fun _ => false)
      have hb : Affine (fun row : Fin (n+1) → Bool => d && row 0) := by
        cases hd : d
        · simpa [hd] using affine_constant (n := n+1) false
        · simpa [hd] using affine_projection (n := n+1) 0
      have hab := affine_xor hb ha
      have he : f = fun row => Bool.xor (d && row 0) (f0 (fun i => row i.succ)) := by
        funext row
        have hr : (Fin.cases (row 0) (fun i => row i.succ) : Fin (n+1) → Bool) = row := by
          funext j; cases j using Fin.cases <;> rfl
        have hd := h 0 (Fin.cases false (fun i => row i.succ)) (fun _ => false)
        change difference f 0 (Fin.cases false (fun i => row i.succ)) = d at hd
        simp only [difference, update_head] at hd
        rw [← hr]
        cases hv : row 0
        · simp [f0]
        · simp only [Fin.cases_zero, Fin.cases_succ, Bool.and_true, f0]
          change f (Fin.cases true (fun i => row i.succ)) =
            Bool.xor d (f (Fin.cases false (fun i => row i.succ)))
          cases hzero : f (Fin.cases false (fun i => row i.succ)) <;>
            cases hone : f (Fin.cases true (fun i => row i.succ)) <;> simp_all
      rw [he]
      exact hab

private theorem monotone_from_edges {n : ℕ} (f : TruthFunction n)
    (h : ∀ i row, row i = false → f row ≤ f (Function.update row i true)) : Monotone f := by
  induction n with
  | zero =>
    intro a b hab
    have he : a = b := funext fun i => Fin.elim0 i
    rw [he]
  | succ n ih =>
    have hm (b : Bool) : Monotone (fun row : Fin n → Bool => f (Fin.cases b row)) := by
      apply ih
      intro i row hi
      simpa only [update_cons] using h i.succ (Fin.cases b row : Fin (n+1) → Bool) (by simpa using hi)
    intro a b hab
    have ha : (Fin.cases (a 0) (fun i => a i.succ) : Fin (n+1) → Bool) = a := by
      funext j; cases j using Fin.cases <;> rfl
    have hb : (Fin.cases (b 0) (fun i => b i.succ) : Fin (n+1) → Bool) = b := by
      funext j; cases j using Fin.cases <;> rfl
    rw [← ha, ← hb]
    apply le_trans ?_ (hm (b 0) (fun i => hab i.succ))
    have hhead := hab 0
    cases ha0 : a 0 <;> cases hb0 : b 0
    · exact le_rfl
    · simpa only [update_head] using h 0 (Fin.cases false (fun i => a i.succ)) rfl
    · exact False.elim ((by decide : ¬ (true : Bool) ≤ false) (by simpa [ha0, hb0] using hhead))
    · exact le_rfl

theorem nonmonotone_edge {n : ℕ} (f : TruthFunction n) (hf : ¬ Monotone f) :
    ∃ (i : Fin n) (row : Fin n → Bool), row i = false ∧ f row = true ∧
      f (Function.update row i true) = false := by
  by_contra h
  push Not at h
  apply hf
  apply monotone_from_edges
  intro i row hi
  cases h0 : f row
  · exact Bool.false_le _
  · have h1 : f (Function.update row i true) = true := by
      cases hv : f (Function.update row i true)
      · exact False.elim (h i row hi h0 hv)
      · rfl
    simp [h1]

theorem necessary_witnesses {S : Set Operation} (hS : PositiveComplete S) :
    EscapesAll S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    have hh := generated_preservesZero (fun row : Fin 1 → Bool => !(row 0)) h
      (hS 1 (by decide) _)
    simp [PreservesZero] at hh
  · by_contra h
    push Not at h
    have hh := generated_preservesOne (fun row : Fin 1 → Bool => !(row 0)) h
      (hS 1 (by decide) _)
    simp [PreservesOne] at hh
  · by_contra h
    push Not at h
    have hh := generated_monotone (fun row : Fin 1 → Bool => !(row 0)) h
      (hS 1 (by decide) _)
    have bad := hh (a := fun _ => false) (b := fun _ => true) (fun _ => Bool.false_le _)
    exact (by decide : ¬ (true : Bool) ≤ false) bad
  · by_contra h
    push Not at h
    have hh := generated_selfDual (fun _ : Fin 1 → Bool => false) h
      (hS 1 (by decide) _)
    have bad := hh (fun _ => false)
    simp at bad
  · by_contra h
    push Not at h
    have hh := generated_affine (fun row : Fin 2 → Bool => row 0 && row 1) h
      (hS 2 (by decide) _)
    have bad := (affine_iff_constant_differences _).mp hh 0 (fun _ => false) (fun _ => true)
    simp [difference] at bad

end Lemmatheca.MathematicalLogic.FunctionalCompletenessCriterion
