import Lemmatheca.FunctionalCompletenessCriterion.Properties
import Mathlib.Tactic.FinCases

namespace Lemmatheca.MathematicalLogic.FunctionalCompletenessCriterion

open Propositional

def unaryNeg : TruthFunction 1 := fun row => !(row 0)

def unaryConstant (b : Bool) : TruthFunction 1 := fun _ => b

def binaryAnd : TruthFunction 2 := fun row => row 0 && row 1

def row2 (p q : Bool) : Fin 2 → Bool := fun i => if i = 0 then p else q

def diagonal (g : Operation) : TruthFunction 1 :=
  fun row => g.table (fun _ => row 0)

def pinCoordinate {n : ℕ} (f : TruthFunction n) (i : Fin n) (row : Fin n → Bool) :
    TruthFunction 1 := fun input => f (Function.update row i (input 0))

def dualPin (g : Operation) (row : Fin g.arity → Bool) : TruthFunction 1 :=
  fun input => g.table (fun i => if row i then input 0 else !(input 0))

def signedUnary (a b : Bool) : TruthFunction 1 := fun row => if row 0 then b else a

def binarySlice {n : ℕ} (f : TruthFunction n) (i : Fin n)
    (row row' : Fin n → Bool) : TruthFunction 2 :=
  fun input => f (fun j => if j = i then input 1 else if input 0 then row' j else row j)

def OddBinary (f : TruthFunction 2) : Prop :=
  Bool.xor (f (row2 false false)) (Bool.xor (f (row2 false true))
    (Bool.xor (f (row2 true false)) (f (row2 true true)))) = true

def literalInput (a p : Bool) : Bool := if a then p else !p

def normalizedBinary (f : TruthFunction 2) (a b c : Bool) : TruthFunction 2 :=
  fun row => Bool.xor c (f (row2 (literalInput a (row 0)) (literalInput b (row 1))))

private theorem generated_rename {S : Set Operation} {n m : ℕ} {f : TruthFunction n}
    (hf : Generates S f) (σ : Fin n → Fin m) : Generates S (fun row => f (fun i => row (σ i))) := by
  exact generates_superpose f (fun i row => row (σ i)) hf (fun i => generates_projection S (σ i))

private theorem generated_not {S : Set Operation} {n : ℕ} {f : TruthFunction n}
    (hf : Generates S f) (hn : Generates S unaryNeg) : Generates S (fun row => !(f row)) := by
  exact generates_superpose unaryNeg (fun _ => f) hn (fun _ => hf)

private theorem row2_eta (row : Fin 2 → Bool) : row2 (row 0) (row 1) = row := by
  funext i
  fin_cases i <;> rfl

theorem literalInput_eq (a p : Bool) : literalInput a p = a ↔ p = true := by
  cases a <;> cases p <;> decide

theorem diagonal_generated {S : Set Operation} (g : Operation) (hg : g ∈ S) :
    Generates S (diagonal g) := by
  exact generated_rename (generates_member g hg) (fun _ => 0)

theorem pinCoordinate_generated {S : Set Operation} (g : Operation) (hg : g ∈ S)
    (hconst : ∀ b, Generates S (unaryConstant b)) (i : Fin g.arity)
    (row : Fin g.arity → Bool) : Generates S (pinCoordinate g.table i row) := by
  have hh : ∀ j : Fin g.arity, Generates S (if j = i then (fun row => row 0) else unaryConstant (row j)) := by
    intro j
    split_ifs
    · exact generates_projection S 0
    · exact hconst _
  convert generates_superpose g.table _ (generates_member g hg) hh using 1
  funext input
  apply congrArg g.table
  funext j
  by_cases hj : j = i <;> simp [hj, unaryConstant]

theorem pinCoordinate_negation {n : ℕ} (f : TruthFunction n) (i : Fin n)
    (row : Fin n → Bool) (hi : row i = false) (h0 : f row = true)
    (h1 : f (Function.update row i true) = false) :
    pinCoordinate f i row = unaryNeg := by
  funext input
  cases hv : input 0
  · have he : Function.update row i false = row := by
      rw [← hi, Function.update_eq_self]
    simpa [pinCoordinate, unaryNeg, hv, he] using h0
  · simpa [pinCoordinate, unaryNeg, hv] using h1

theorem generates_negation {S : Set Operation}
    (h0 : ∃ g ∈ S, ¬ PreservesZero g.table)
    (h1 : ∃ g ∈ S, ¬ PreservesOne g.table)
    (hm : ∃ g ∈ S, ¬ Monotone g.table) : Generates S unaryNeg := by
  obtain ⟨a, ha, ha0⟩ := h0
  obtain ⟨b, hb, hb1⟩ := h1
  have ha0' : a.table (fun _ => false) = true := by
    simpa [PreservesZero] using ha0
  have hb1' : b.table (fun _ => true) = false := by
    simpa [PreservesOne] using hb1
  by_cases ha1 : a.table (fun _ => true) = false
  · have he : diagonal a = unaryNeg := by
      funext row
      cases hv : row 0 <;> simp [diagonal, unaryNeg, hv, ha0', ha1]
    rw [← he]
    exact diagonal_generated a ha
  by_cases hb0 : b.table (fun _ => false) = true
  · have he : diagonal b = unaryNeg := by
      funext row
      cases hv : row 0 <;> simp [diagonal, unaryNeg, hv, hb0, hb1']
    rw [← he]
    exact diagonal_generated b hb
  have ha1' : a.table (fun _ => true) = true := by simpa using ha1
  have hb0' : b.table (fun _ => false) = false := by simpa using hb0
  have hconst : ∀ c, Generates S (unaryConstant c) := by
    intro c
    cases c
    · have he : diagonal b = unaryConstant false := by
        funext row; cases hv : row 0 <;> simp [diagonal, unaryConstant, hv, hb0', hb1']
      rw [← he]; exact diagonal_generated b hb
    · have he : diagonal a = unaryConstant true := by
        funext row; cases hv : row 0 <;> simp [diagonal, unaryConstant, hv, ha0', ha1']
      rw [← he]; exact diagonal_generated a ha
  obtain ⟨g, hg, hgm⟩ := hm
  obtain ⟨i, row, hi, hr0, hr1⟩ := nonmonotone_edge g.table hgm
  rw [← pinCoordinate_negation g.table i row hi hr0 hr1]
  exact pinCoordinate_generated g hg hconst i row

theorem dualPin_generated {S : Set Operation} (g : Operation) (hg : g ∈ S)
    (hn : Generates S unaryNeg) (row : Fin g.arity → Bool) :
    Generates S (dualPin g row) := by
  have hh : ∀ i : Fin g.arity, Generates S (if row i then (fun input => input 0) else unaryNeg) := by
    intro i
    split_ifs
    · exact generates_projection S 0
    · exact hn
  convert generates_superpose g.table _ (generates_member g hg) hh using 1
  funext input
  apply congrArg g.table
  funext i
  by_cases hi : row i = true <;> simp [hi, unaryNeg]

theorem dualPin_constant (g : Operation) (row : Fin g.arity → Bool)
    (h : g.table row = g.table (fun i => !(row i))) :
    dualPin g row = unaryConstant (g.table row) := by
  funext input
  cases hv : input 0
  · simpa [dualPin, unaryConstant, hv] using h.symm
  · simp [dualPin, unaryConstant, hv]

theorem generates_constants {S : Set Operation} (hn : Generates S unaryNeg)
    (hd : ∃ g ∈ S, ¬ SelfDual g.table) : ∀ b, Generates S (unaryConstant b) := by
  obtain ⟨g, hg, hd⟩ := hd
  unfold SelfDual at hd
  push Not at hd
  obtain ⟨row, hr⟩ := hd
  have he : g.table row = g.table (fun i => !(row i)) := by
    cases h0 : g.table row <;> cases h1 : g.table (fun i => !(row i)) <;> simp_all
  have hc : Generates S (unaryConstant (g.table row)) := by
    rw [← dualPin_constant g row he]
    exact dualPin_generated g hg hn row
  have hc' := generated_not hc hn
  intro b
  cases hv : g.table row <;> cases b
  · simpa [hv] using hc
  · convert hc' using 1
    funext input
    simp [unaryConstant, hv]
  · convert hc' using 1
    funext input
    simp [unaryConstant, hv]
  · simpa [hv] using hc

theorem signedUnary_generated {S : Set Operation} (hn : Generates S unaryNeg)
    (hconst : ∀ b, Generates S (unaryConstant b)) (a b : Bool) :
    Generates S (signedUnary a b) := by
  cases a <;> cases b
  · convert hconst false using 1
    funext input; cases hv : input 0 <;> simp [signedUnary, unaryConstant, hv]
  · convert generates_projection S (n := 1) 0 using 1
    funext input; cases hv : input 0 <;> simp [signedUnary, hv]
  · convert hn using 1
    funext input; cases hv : input 0 <;> simp [signedUnary, unaryNeg, hv]
  · convert hconst true using 1
    funext input; cases hv : input 0 <;> simp [signedUnary, unaryConstant, hv]

theorem binarySlice_generated {S : Set Operation} (g : Operation) (hg : g ∈ S)
    (hn : Generates S unaryNeg) (hconst : ∀ b, Generates S (unaryConstant b))
    (i : Fin g.arity) (row row' : Fin g.arity → Bool) :
    Generates S (binarySlice g.table i row row') := by
  have hh : ∀ j : Fin g.arity, Generates S
      (if j = i then (fun input : Fin 2 → Bool => input 1)
        else (fun input => signedUnary (row j) (row' j) (fun _ => input 0))) := by
    intro j
    split_ifs
    · exact generates_projection S 1
    · exact generated_rename (signedUnary_generated hn hconst (row j) (row' j)) (fun _ => 0)
  convert generates_superpose g.table _ (generates_member g hg) hh using 1
  funext input
  apply congrArg g.table
  funext j
  by_cases hj : j = i <;> simp [hj, signedUnary]

theorem binarySlice_odd {n : ℕ} (f : TruthFunction n) (i : Fin n)
    (row row' : Fin n → Bool) (h0 : difference f i row = false)
    (h1 : difference f i row' = true) : OddBinary (binarySlice f i row row') := by
  have hs (p q : Bool) : binarySlice f i row row' (row2 p q) =
      f (Function.update (if p then row' else row) i q) := by
    apply congrArg f
    funext j
    by_cases hj : j = i <;> cases p <;> simp [row2, hj]
  unfold OddBinary
  rw [hs, hs, hs, hs]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  unfold difference at h0 h1
  cases h00 : f (Function.update row i false) <;>
    cases h01 : f (Function.update row i true) <;>
    cases h10 : f (Function.update row' i false) <;>
    cases h11 : f (Function.update row' i true) <;> simp_all

theorem generates_oddBinary {S : Set Operation} (hn : Generates S unaryNeg)
    (hconst : ∀ b, Generates S (unaryConstant b))
    (ha : ∃ g ∈ S, ¬ Affine g.table) :
    ∃ f : TruthFunction 2, Generates S f ∧ OddBinary f := by
  obtain ⟨g, hg, ha⟩ := ha
  have hd : ¬ ∀ i row row', difference g.table i row = difference g.table i row' := by
    intro h
    exact ha ((affine_iff_constant_differences _).mpr h)
  push Not at hd
  obtain ⟨i, row, row', hr⟩ := hd
  cases h0 : difference g.table i row <;> cases h1 : difference g.table i row'
  · exact False.elim (hr (h0.trans h1.symm))
  · exact ⟨_, binarySlice_generated g hg hn hconst i row row', binarySlice_odd _ _ _ _ h0 h1⟩
  · exact ⟨_, binarySlice_generated g hg hn hconst i row' row, binarySlice_odd _ _ _ _ h1 h0⟩
  · exact False.elim (hr (h0.trans h1.symm))

theorem odd_exception (f : TruthFunction 2) (hf : OddBinary f) :
    ∃ a b c : Bool, ∀ p q : Bool,
      f (row2 p q) = Bool.xor c ((p == a) && (q == b)) := by
  cases h00 : f (row2 false false) <;> cases h01 : f (row2 false true) <;>
    cases h10 : f (row2 true false) <;> cases h11 : f (row2 true true) <;>
    simp [OddBinary, h00, h01, h10, h11] at hf
  · exact ⟨true, true, false, by intro p q; cases p <;> cases q <;> simp_all⟩
  · exact ⟨true, false, false, by intro p q; cases p <;> cases q <;> simp_all⟩
  · exact ⟨false, true, false, by intro p q; cases p <;> cases q <;> simp_all⟩
  · exact ⟨false, false, true, by intro p q; cases p <;> cases q <;> simp_all⟩
  · exact ⟨false, false, false, by intro p q; cases p <;> cases q <;> simp_all⟩
  · exact ⟨false, true, true, by intro p q; cases p <;> cases q <;> simp_all⟩
  · exact ⟨true, false, true, by intro p q; cases p <;> cases q <;> simp_all⟩
  · exact ⟨true, true, true, by intro p q; cases p <;> cases q <;> simp_all⟩

theorem normalizedBinary_and (f : TruthFunction 2) (a b c : Bool)
    (hf : ∀ p q : Bool, f (row2 p q) = Bool.xor c ((p == a) && (q == b))) :
    normalizedBinary f a b c = binaryAnd := by
  funext row
  unfold normalizedBinary binaryAnd
  rw [hf]
  cases a <;> cases b <;> cases c <;> cases hv : row 0 <;> cases hw : row 1 <;>
    simp [literalInput]

theorem normalizedBinary_generated {S : Set Operation} (f : TruthFunction 2)
    (hf : Generates S f) (hn : Generates S unaryNeg) (a b c : Bool) :
    Generates S (normalizedBinary f a b c) := by
  have hl (d : Bool) (i : Fin 2) : Generates S (fun row : Fin 2 → Bool => literalInput d (row i)) := by
    cases d
    · exact generated_not (generates_projection S i) hn
    · exact generates_projection S i
  have hh := generates_superpose f (fun i row => literalInput (if i = 0 then a else b) (row i)) hf
    (fun i => hl _ i)
  have he : superpose f (fun i row => literalInput (if i = 0 then a else b) (row i)) =
      (fun row => f (row2 (literalInput a (row 0)) (literalInput b (row 1)))) := by
    funext row
    apply congrArg f
    funext i
    fin_cases i <;> rfl
  rw [he] at hh
  cases c
  · convert hh using 1
    funext row
    simp [normalizedBinary]
  · convert generated_not hh hn using 1
    funext row
    simp [normalizedBinary]

theorem generates_conjunction {S : Set Operation} (hn : Generates S unaryNeg)
    (ho : ∃ f : TruthFunction 2, Generates S f ∧ OddBinary f) :
    Generates S binaryAnd := by
  obtain ⟨f, hf, ho⟩ := ho
  obtain ⟨a, b, c, he⟩ := odd_exception f ho
  rw [← normalizedBinary_and f a b c he]
  exact normalizedBinary_generated f hf hn a b c

end Lemmatheca.MathematicalLogic.FunctionalCompletenessCriterion
