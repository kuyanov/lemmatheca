import Lemmatheca.UniversalComputation.UniversalComputation
import Mathlib.Data.Nat.Size

/-! The actual finite recursive-program syntax, its node size, an effective finite
contestant list and a binary numeral compiler. -/
namespace Lemmatheca.ComputabilityTheory.BusyBeaverFunctions

open Encodable Denumerable
open Nat.Partrec (Code)
open UniversalComputation

set_option backward.isDefEq.respectTransparency false

/-- Program size counts tree nodes, with repeated subprograms counted repeatedly. -/
def nodeSize : Code → ℕ
  | .zero | .succ | .left | .right => 1
  | .pair c d | .comp c d | .prec c d => 1 + nodeSize c + nodeSize d
  | .rfind' c => 1 + nodeSize c

private theorem nodeSize_primitive : Primrec nodeSize := by
  have hb : Primrec (fun p : Code × Code × Code × ℕ × ℕ =>
      1 + p.2.2.2.1 + p.2.2.2.2) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 1)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hu : Primrec (fun p : Code × Code × ℕ => 1 + p.2.2) :=
    Primrec.nat_add.comp (Primrec.const 1) (Primrec.snd.comp Primrec.snd)
  have hp := Code.primrec_recOn (α := Code) (σ := ℕ) Primrec.id
    (Primrec.const 1) (Primrec.const 1) (Primrec.const 1) (Primrec.const 1)
    (pr := fun _ _ _ a b => 1 + a + b) hb
    (co := fun _ _ _ a b => 1 + a + b) hb
    (pc := fun _ _ _ a b => 1 + a + b) hb
    (rf := fun _ _ a => 1 + a) hu
  apply hp.of_eq
  intro c
  induction c <;> simp_all [nodeSize]

theorem nodeSize_computable : Computable nodeSize := by
  exact nodeSize_primitive.to_comp

theorem nodeSize_positive (c : Code) : 0 < nodeSize c := by
  cases c <;> simp [nodeSize]

/-- The finite list is generated constructor by constructor, then size-filtered. -/
def contestantStep (n : ℕ) (cs : List Code) : List Code :=
  ([Code.zero, Code.succ, Code.left, Code.right] ++ cs.map Code.rfind' ++
    cs.flatMap (fun c => cs.flatMap (fun d => [Code.pair c d, Code.comp c d, Code.prec c d]))).filter
      (fun c => decide (nodeSize c ≤ n + 1))

def contestants : ℕ → List Code
  | 0 => []
  | n + 1 => contestantStep n (contestants n)

theorem contestants_spec (n : ℕ) (c : Code) : c ∈ contestants n ↔ nodeSize c ≤ n := by
  induction n generalizing c with
  | zero => simp [contestants, Nat.not_le.mpr (nodeSize_positive c)]
  | succ n ih =>
    change c ∈ (contestantStep n (contestants n)) ↔ _
    rw [contestantStep, List.mem_filter]
    constructor
    · intro h
      exact of_decide_eq_true h.2
    · intro hs
      refine ⟨?_, decide_eq_true hs⟩
      cases c with
      | zero | succ | left | right => simp
      | rfind' d =>
        have hd : d ∈ contestants n := (ih d).mpr (by simp only [nodeSize] at hs; omega)
        simp [hd]
      | pair c d | comp c d | prec c d =>
        have hc : c ∈ contestants n := (ih c).mpr (by simp only [nodeSize] at hs; omega)
        have hd : d ∈ contestants n := (ih d).mpr (by simp only [nodeSize] at hs; omega)
        simp [hc, hd]

private theorem contestantStep_primitive : Primrec₂ contestantStep := by
  let triple : Code × Code → List Code := fun p =>
    [Code.pair p.1 p.2, Code.comp p.1 p.2, Code.prec p.1 p.2]
  have ht : Primrec triple :=
    Primrec.list_cons.comp (Code.primrec₂_pair.comp Primrec.fst Primrec.snd)
      (Primrec.list_cons.comp (Code.primrec₂_comp.comp Primrec.fst Primrec.snd)
        (Primrec.list_cons.comp (Code.primrec₂_prec.comp Primrec.fst Primrec.snd)
          (Primrec.const [])))
  have hi : Primrec (fun p : (ℕ × List Code) × Code =>
      p.1.2.flatMap (fun d => triple (p.2, d))) :=
    Primrec.list_flatMap (Primrec.snd.comp Primrec.fst)
      (ht.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂
  have hb : Primrec (fun p : ℕ × List Code =>
      p.2.flatMap (fun c => p.2.flatMap (fun d => triple (c, d)))) :=
    Primrec.list_flatMap Primrec.snd hi.to₂
  have hu : Primrec (fun p : ℕ × List Code => p.2.map Code.rfind') :=
    Primrec.list_map Primrec.snd (Code.primrec_rfind'.comp Primrec.snd).to₂
  have hl := Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.const [Code.zero, Code.succ, Code.left, Code.right]) hu) hb
  have hp : PrimrecPred (fun p : (ℕ × List Code) × Code => nodeSize p.2 ≤ p.1.1 + 1) :=
    Primrec.nat_le.comp (nodeSize_primitive.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
  have hf := Primrec.listFilterMap hl
    (Primrec.ite hp (Primrec.option_some_iff.mpr Primrec.snd) (Primrec.const none)).to₂
  apply Primrec₂.mk
  apply hf.of_eq
  intro p
  dsimp [triple, contestantStep]
  rw [← List.filterMap_eq_filter]
  congr 1
  funext c
  by_cases h : nodeSize c ≤ p.1 + 1 <;> simp [Option.guard, h]

theorem contestants_primitive : Primrec contestants := by
  have h := Primrec.nat_rec₁ ([] : List Code) contestantStep_primitive
  exact h.of_eq (fun n => by induction n <;> simp [contestants, *])

theorem contestants_computable : Computable contestants := by
  exact contestants_primitive.to_comp

theorem contestants_monotone {m n : ℕ} (h : m ≤ n) :
    ∀ c ∈ contestants m, c ∈ contestants n := by
  intro c hc
  exact (contestants_spec n c).mpr (((contestants_spec m c).mp hc).trans h)

/-- This fixed addition program computes the sum of its two paired inputs. -/
def addCode : Code := .prec Code.id (.comp .succ (.comp .right .right))

def doubleCode : Code := .comp addCode (.pair Code.id Code.id)

private theorem addCode_eval (a b : ℕ) : Code.eval addCode (Nat.pair a b) = Part.some (a + b) := by
  induction b with
  | zero => rw [addCode, Code.eval_prec_zero, Code.eval_id, Nat.add_zero]
  | succ b ih =>
    change Code.eval (.prec Code.id (.comp .succ (.comp .right .right)))
      (Nat.pair a (b + 1)) = _
    rw [Code.eval_prec_succ]
    change (Code.eval addCode (Nat.pair a b)).bind _ = _
    rw [ih, Part.bind_some]
    simp [Code.eval, Nat.add_assoc]

theorem doubleCode_eval (x : ℕ) : Code.eval doubleCode x = Part.some (2 * x) := by
  have hp : Code.eval (.pair Code.id Code.id) x = Part.some (Nat.pair x x) := by
    change Nat.pair <$> Code.eval Code.id x <*> Code.eval Code.id x = _
    rw [Code.eval_id]
    simp [Seq.seq]
  change (Code.eval (.pair Code.id Code.id) x).bind (Code.eval addCode) = _
  rw [hp, Part.bind_some, addCode_eval]
  congr 1
  omega

/-- A binary compiler in the same syntax; it never inserts a numeral as a new leaf. -/
def binaryConstant : ℕ → Code :=
  Nat.binaryRec (motive := fun _ => Code) .zero
    (fun b _ c => if b then .comp .succ (.comp doubleCode c) else .comp doubleCode c)

def constantOverhead : ℕ := nodeSize doubleCode + 3

theorem binaryConstant_step (b : Bool) (k : ℕ) (h : Nat.bit b k ≠ 0) :
    binaryConstant (Nat.bit b k) =
      if b then .comp .succ (.comp doubleCode (binaryConstant k))
      else .comp doubleCode (binaryConstant k) := by
  exact Nat.binaryRec_eq b k (Or.inr (Nat.bit_ne_zero_iff.mp h))

private def appendBinary (b : Bool) (c : Code) : Code :=
  if b then .comp .succ (.comp doubleCode c) else .comp doubleCode c

private theorem appendBinary_primitive : Primrec₂ appendBinary := by
  apply Primrec₂.mk
  apply (Primrec.cond Primrec.fst
    (Code.primrec₂_comp.comp (Primrec.const Code.succ)
      (Code.primrec₂_comp.comp (Primrec.const doubleCode) Primrec.snd))
    (Code.primrec₂_comp.comp (Primrec.const doubleCode) Primrec.snd)).of_eq
  intro p
  cases p.1 <;> rfl

theorem binaryConstant_computable : Computable binaryConstant := by
  let G : ℕ × List Code → Option Code := fun p =>
    if p.2.length = 0 then some Code.zero
    else (p.2[p.2.length.div2]?).map (appendBinary p.2.length.bodd)
  have hl : Primrec (fun p : ℕ × List Code => p.2.length) := Primrec.list_length.comp Primrec.snd
  have hg : Primrec G :=
    Primrec.ite (Primrec.eq.comp hl (Primrec.const 0)) (Primrec.const (some Code.zero))
      (Primrec.option_map
        (Primrec.list_getElem?.comp Primrec.snd (Primrec.nat_div2.comp hl))
        (appendBinary_primitive.comp
          (Primrec.nat_bodd.comp (hl.comp Primrec.fst)) Primrec.snd).to₂)
  have hrec : Primrec₂ (fun (_ : ℕ) n => binaryConstant n) :=
    Primrec.nat_strong_rec (fun (_ : ℕ) n => binaryConstant n)
      (g := fun a cs => G (a, cs)) hg.to₂ (fun a n => by
      cases n with
      | zero => rfl
      | succ n =>
        have hd : (n + 1).div2 < n + 1 := by
          rw [Nat.div2_val]
          exact Nat.div_lt_self (by omega) (by omega)
        have he := binaryConstant_step (n + 1).bodd (n + 1).div2
          (by simpa only [Nat.bit_bodd_div2] using Nat.succ_ne_zero n)
        rw [Nat.bit_bodd_div2] at he
        simp only [G, List.length_map, List.length_range, Nat.succ_ne_zero, ↓reduceIte,
          List.getElem?_map, List.getElem?_range hd, Option.map_some]
        exact congrArg Option.some he.symm)
  exact (hrec.comp (Primrec.const 0) Primrec.id).to_comp

theorem binaryConstant_eval (n x : ℕ) : Code.eval (binaryConstant n) x = Part.some n := by
  induction n using Nat.binaryRec' with
  | zero => exact Code.eval_const 0 x
  | bit b n h ih =>
    rw [binaryConstant_step b n (Nat.bit_ne_zero_iff.mpr h)]
    cases b <;> simp [Code.eval, ih, doubleCode_eval, Nat.bit_val]

theorem binaryConstant_size (n : ℕ) :
    nodeSize (binaryConstant n) ≤ 1 + constantOverhead * Nat.size n := by
  induction n using Nat.binaryRec' with
  | zero => simp [binaryConstant, nodeSize]
  | bit b n h ih =>
    have hn : Nat.bit b n ≠ 0 := Nat.bit_ne_zero_iff.mpr h
    rw [binaryConstant_step b n hn, Nat.size_bit hn]
    have ha : constantOverhead = 20 := rfl
    rw [ha] at ih ⊢
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, nodeSize]
    all_goals
      have hd : nodeSize doubleCode = 17 := rfl
      rw [hd]
      omega

theorem binaryLength_computable : Computable Nat.size := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hp : Computable (fun p : ℕ × ℕ => decide (p.1 < 2 ^ p.2)) :=
    (Primrec.nat_lt.comp Primrec.fst
      (hpow.comp (Primrec.const 2) Primrec.snd)).decide.to_comp
  have hs := Partrec.rfind hp.to₂.partrec₂
  apply hs.of_eq_tot
  intro n
  rw [Nat.mem_rfind]
  refine ⟨?_, ?_⟩
  · change true ∈ Part.some (decide (n < 2 ^ Nat.size n))
    simpa using Nat.lt_size_self n
  · intro k hk
    change false ∈ Part.some (decide (n < 2 ^ k))
    apply (Part.mem_some_iff).mpr
    exact (decide_eq_false_iff_not.mpr
      (fun h => Nat.not_le_of_gt hk (Nat.size_le.mpr h))).symm

theorem eventual_binary_budget (u v : ℕ) :
    ∃ N, ∀ n, N ≤ n → u + v * Nat.size n ≤ n := by
  have hpow : ∀ j, 4 ≤ j → j ^ 2 ≤ 2 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
      calc
        (j + 1) ^ 2 ≤ 2 * j ^ 2 := by nlinarith
        _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
  let L := max 5 (2 * (u + v + 1))
  refine ⟨2 ^ (L - 1), ?_⟩
  intro n hn
  have hL : L ≤ Nat.size n := by
    have := (Nat.lt_size (m := L - 1) (n := n)).mpr hn
    have : 5 ≤ L := le_max_left _ _
    omega
  have h5 : 5 ≤ Nat.size n := (le_max_left _ _).trans hL
  have huv : u + v + 2 ≤ Nat.size n := by
    have := (le_max_right 5 (2 * (u + v + 1))).trans hL
    omega
  have hu : u ≤ u * Nat.size n := by
    have := Nat.mul_le_mul_left u (show 1 ≤ Nat.size n by omega)
    simpa using this
  have hm := Nat.mul_le_mul_right (Nat.size n) huv
  have hpred : Nat.size n - 1 + 1 = Nat.size n := by omega
  have hquad : u + v * Nat.size n ≤ (Nat.size n - 1) ^ 2 := by nlinarith
  exact hquad.trans ((hpow _ (by omega)).trans ((Nat.lt_size).mp (by omega)))

end Lemmatheca.ComputabilityTheory.BusyBeaverFunctions
