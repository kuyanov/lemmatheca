import Mathlib.Computability.Primrec.List
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-! Explicit square-pair list codes and primitive-recursive operations on their numbers. -/
namespace Lemmatheca.MathematicalLogic.FiniteSequenceCoding
open Encodable Denumerable
open scoped BigOperators
abbrev code (s : List ℕ) : ℕ := Encodable.encode s
abbrev decode (c : ℕ) : List ℕ := Denumerable.ofNat (List ℕ) c

def head (c : ℕ) : ℕ := if c = 0 then 0 else (Nat.unpair (c - 1)).1
def tail (c : ℕ) : ℕ := if c = 0 then 0 else (Nat.unpair (c - 1)).2
def tails (c i : ℕ) : ℕ := tail^[i] c
def length (c : ℕ) : ℕ := (decode c).length
def entry (c i : ℕ) : ℕ := (decode c)[i]?.getD 0
def cons (a c : ℕ) : ℕ := 1 + Nat.pair a c
def reverse (c : ℕ) : ℕ := code (decode c).reverse
def append (c d : ℕ) : ℕ := code (decode c ++ decode d)
def fold (h : ℕ → ℕ → ℕ) (c z : ℕ) : ℕ := (decode c).foldl h z

def bound (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (m + bound m n + 1) ^ 2

def states (a b : ℕ) (F G : ℕ → ℕ → ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (a, b)
  | n + 1 => (F n (states a b F G n).1 (states a b F G n).2,
               G n (states a b F G n).1 (states a b F G n).2)

def historyCode (h : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => append (historyCode h n) (cons (h n (historyCode h n)) 0)

def historyValue (h : ℕ → ℕ → ℕ) (n : ℕ) : ℕ := h n (historyCode h n)

private theorem initial_segment_sum (k n : ℕ) (hk : k ≤ n) :
    (∑ j ∈ Finset.range n, if j < k then 1 else 0) = k := by
  have hf : (Finset.range n).filter (fun j => j < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.card_filter, hf, Finset.card_range]

theorem sqrt_count (n : ℕ) :
    Nat.sqrt n = ∑ j ∈ Finset.range n, if (j + 1) ^ 2 ≤ n then 1 else 0 := by
  have he (j : ℕ) : (j + 1) ^ 2 ≤ n ↔ j < Nat.sqrt n := by
    rw [← Nat.le_sqrt']
    omega
  simp_rw [he]
  exact (initial_segment_sum (Nat.sqrt n) n (Nat.sqrt_le_self n)).symm

theorem code_cons (a : ℕ) (s : List ℕ) : code (a :: s) = cons a (code s) := by
  simp [code, cons, Encodable.encode_list_cons, Nat.add_comm]

theorem decode_zero : decode 0 = [] := by
  exact Denumerable.list_ofNat_zero

theorem decode_succ (c : ℕ) :
    decode (c + 1) = (Nat.unpair c).1 :: decode (Nat.unpair c).2 := by
  simp [decode, Denumerable.list_ofNat_succ]

theorem decode_code (s : List ℕ) : decode (code s) = s := by
  exact Denumerable.ofNat_encode s

theorem code_decode (c : ℕ) : code (decode c) = c := by
  exact Denumerable.encode_ofNat c

theorem code_bijective : Function.Bijective code := by
  exact ⟨Function.LeftInverse.injective decode_code, Function.RightInverse.surjective code_decode⟩

theorem head_code (s : List ℕ) : head (code s) = s.headD 0 := by
  cases s with
  | nil => simp [code, head]
  | cons a s => simp [code, head, Encodable.encode_list_cons]

theorem tail_code (s : List ℕ) : tail (code s) = code s.tail := by
  cases s with
  | nil => simp [code, tail]
  | cons a s => simp [code, tail, Encodable.encode_list_cons]

theorem head_lt_code (a : ℕ) (s : List ℕ) : a < code (a :: s) := by
  have h := Nat.left_le_pair a (code s)
  simpa [code, Encodable.encode_list_cons] using Nat.lt_succ_of_le h

theorem tail_lt_code (a : ℕ) (s : List ℕ) : code s < code (a :: s) := by
  have h := Nat.right_le_pair a (code s)
  simpa [code, Encodable.encode_list_cons] using Nat.lt_succ_of_le h

theorem tail_lt {c : ℕ} (hc : c ≠ 0) : tail c < c := by
  rcases Nat.exists_eq_succ_of_ne_zero hc with ⟨n, rfl⟩
  simpa [tail] using Nat.lt_succ_of_le (Nat.unpair_right_le n)

theorem member_lt_code {a : ℕ} {s : List ℕ} (ha : a ∈ s) : a < code s := by
  induction s with
  | nil => simp at ha
  | cons b s ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact head_lt_code a s
    · exact (ih ha).trans (tail_lt_code b s)

theorem tails_code (s : List ℕ) (i : ℕ) : tails (code s) i = code (s.drop i) := by
  induction i with
  | zero => simp [tails]
  | succ i ih =>
    rw [tails, Function.iterate_succ_apply', ← tails, ih, tail_code]
    exact congrArg code List.tail_drop

theorem tails_stop (c : ℕ) : tails c c = 0 := by
  rw [← code_decode c, tails_code]
  rw [List.drop_eq_nil_of_le (by simpa using Encodable.length_le_encode (decode c))]
  rfl

theorem length_eq_sum (c : ℕ) :
    length c = ∑ j ∈ Finset.range c, if tails c j = 0 then 0 else 1 := by
  have hz (j : ℕ) : tails c j = 0 ↔ length c ≤ j := by
    have hc : tails c j = code ((decode c).drop j) := by
      simpa using tails_code (decode c) j
    rw [hc]
    constructor
    · intro h
      have hd : (decode c).drop j = [] := by simpa using congrArg decode h
      have hh := congrArg List.length hd
      simp only [List.length_drop, List.length_nil] at hh
      exact Nat.le_of_sub_eq_zero hh
    · intro h
      rw [List.drop_eq_nil_of_le h]
      rfl
  have hl : length c ≤ c := by simpa [length] using Encodable.length_le_encode (decode c)
  rw [← initial_segment_sum (length c) c hl]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : length c ≤ j
  · simp [hz j |>.mpr h, Nat.not_lt.mpr h]
  · simp [mt (hz j).mp h, Nat.lt_of_not_ge h]

theorem entry_eq_head (c i : ℕ) : entry c i = head (tails c i) := by
  rw [← code_decode c, tails_code, head_code]
  simp [entry, List.head?_drop]

theorem entry_code (s : List ℕ) (i : ℕ) : entry (code s) i = s[i]?.getD 0 := by
  simp [entry]

theorem entry_out_of_range (c i : ℕ) (hi : length c ≤ i) : entry c i = 0 := by
  simp [entry, List.getElem?_eq_none hi]

theorem primrec_head : Primrec head := by
  have hd : Primrec decode := Primrec.ofNat (List ℕ)
  have hh : Primrec fun c => (decode c).headD 0 :=
    by simpa using Primrec.option_getD.comp (Primrec.list_head?.comp hd) (Primrec.const 0)
  exact hh.of_eq fun c => by simpa using (head_code (decode c)).symm

theorem primrec_tail : Primrec tail := by
  have ht : Primrec fun c => code (decode c).tail :=
    Primrec.encode.comp (Primrec.list_tail.comp (Primrec.ofNat (List ℕ)))
  exact ht.of_eq fun c => by simpa using (tail_code (decode c)).symm

theorem primrec_tails : Primrec₂ tails := by
  exact (Primrec.nat_iterate Primrec.snd Primrec.fst
    (primrec_tail.comp₂ Primrec₂.right)).to₂

theorem primrec_length : Primrec length := by
  exact Primrec.list_length.comp (Primrec.ofNat (List ℕ))

theorem primrec_entry : Primrec₂ entry := by
  exact (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp ((Primrec.ofNat (List ℕ)).comp Primrec.fst) Primrec.snd)
    (Primrec.const 0)).to₂

theorem primrec_cons : Primrec₂ cons := by
  exact (Primrec.succ.comp (Primrec₂.natPair : Primrec fun p : ℕ × ℕ => Nat.pair p.1 p.2)).to₂.of_eq
    fun a c => by simp [cons, Nat.add_comm]

theorem primrec_fold {h : ℕ → ℕ → ℕ} (hh : Primrec₂ h) : Primrec₂ (fold h) := by
  exact (Primrec.list_foldl ((Primrec.ofNat (List ℕ)).comp Primrec.fst)
    Primrec.snd (hh.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right))).to₂

theorem primrec_reverse : Primrec reverse := by
  exact Primrec.encode.comp (Primrec.list_reverse.comp (Primrec.ofNat (List ℕ)))

theorem primrec_append : Primrec₂ append := by
  exact (Primrec.encode.comp
    (Primrec.list_append.comp ((Primrec.ofNat (List ℕ)).comp Primrec.fst)
      ((Primrec.ofNat (List ℕ)).comp Primrec.snd))).to₂

theorem append_code (s t : List ℕ) : append (code s) (code t) = code (s ++ t) := by
  simp [append]

theorem primrec_bound : Primrec₂ bound := by
  have hs : Primrec fun p : ℕ × (ℕ × ℕ) => p.1 + p.2.2 + 1 :=
    Primrec.succ.comp (Primrec.nat_add.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
  have ht : Primrec₂ fun m (p : ℕ × ℕ) => (m + p.2 + 1) ^ 2 :=
    (Primrec.nat_mul.comp hs hs).to₂.of_eq fun m p => by simp [pow_two]
  exact (Primrec.nat_rec (Primrec.const 0) ht).of_eq fun m n => by
    induction n <;> simp [bound, *]

theorem bound_mono (m : ℕ) : Monotone (bound m) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := Nat.le_mul_self (m + bound m n + 1)
  simp only [bound, pow_two]
  omega

theorem code_le_bound {s : List ℕ} {m n : ℕ}
    (hlen : s.length ≤ n) (hmem : ∀ a ∈ s, a ≤ m) : code s ≤ bound m n := by
  have hb : ∀ s : List ℕ, (∀ a ∈ s, a ≤ m) → code s ≤ bound m s.length := by
    intro s
    induction s with
    | nil => simp [code, bound]
    | cons a s ih =>
      intro hs
      have ha := hs a (by simp)
      have ht := ih (fun b h => hs b (by simp [h]))
      have hp := Nat.pair_lt_max_add_one_sq a (code s)
      have hm : max a (code s) ≤ m + bound m s.length := max_le (by omega) (by omega)
      have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 2
      simpa [code, Encodable.encode_list_cons, bound] using (Nat.succ_le_iff.mpr hp).trans hsq
  exact (hb s hmem).trans (bound_mono m hlen)

theorem primrec_states (a b : ℕ) {F G : ℕ → ℕ → ℕ → ℕ}
    (hF : Primrec fun p : ℕ × ℕ × ℕ => F p.1 p.2.1 p.2.2)
    (hG : Primrec fun p : ℕ × ℕ × ℕ => G p.1 p.2.1 p.2.2) :
    Primrec (states a b F G) := by
  have hp := Primrec.nat_rec₁ (a, b) (hF.pair hG).to₂
  exact hp.of_eq fun n => by induction n <;> simp [states, *]

theorem fibonacci_states (n : ℕ) :
    states 0 1 (fun _ _ y => y) (fun _ x y => x + y) n = (Nat.fib n, Nat.fib (n + 1)) := by
  induction n with
  | zero => simp [states]
  | succ n ih => simp [states, ih, Nat.fib_add_two]

theorem primrec_fibonacci : Primrec Nat.fib := by
  have hs := primrec_states (F := fun _ _ y => y) (G := fun _ x y => x + y) 0 1
    (Primrec.snd.comp Primrec.snd)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.fst.comp hs).of_eq fun n => by
    have he := congrArg (fun p : ℕ × ℕ => p.1) (fibonacci_states n)
    exact he

theorem history_identity (h : ℕ → ℕ → ℕ) (n : ℕ) :
    decode (historyCode h n) = (List.range n).map (historyValue h) := by
  induction n with
  | zero => simp [historyCode]
  | succ n ih =>
    have hs : cons (h n (historyCode h n)) 0 = code [h n (historyCode h n)] :=
      (code_cons _ []).symm
    simp only [historyCode, append, decode_code, hs, List.range_succ, List.map_append,
      List.map_singleton]
    simpa [historyValue] using congrArg (fun s => s ++ [h n (historyCode h n)]) ih

theorem history_equation (h : ℕ → ℕ → ℕ) (n : ℕ) :
    historyValue h n = h n (code ((List.range n).map (historyValue h))) := by
  rw [← history_identity, code_decode]
  rfl

theorem history_unique (h : ℕ → ℕ → ℕ) (a : ℕ → ℕ)
    (ha : ∀ n, a n = h n (code ((List.range n).map a))) : a = historyValue h := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [ha n, history_equation h n]
    congr 2
    apply List.map_congr_left
    intro i hi
    exact ih i (List.mem_range.mp hi)

theorem primrec_historyCode {h : ℕ → ℕ → ℕ} (hh : Primrec₂ h) :
    Primrec (historyCode h) := by
  have hs : Primrec₂ fun n c => append c (cons (h n c) 0) :=
    (primrec_append.comp Primrec.snd (primrec_cons.comp hh (Primrec.const 0))).to₂
  exact (Primrec.nat_rec₁ 0 hs).of_eq fun n => by
    induction n <;> simp [historyCode, *]

theorem primrec_historyValue {h : ℕ → ℕ → ℕ} (hh : Primrec₂ h) :
    Primrec (historyValue h) := by
  exact hh.comp Primrec.id (primrec_historyCode hh)


theorem primrec_fold_param {h : ℕ → ℕ → ℕ → ℕ}
    (hh : Primrec fun p : ℕ × ℕ × ℕ => h p.1 p.2.1 p.2.2) :
    Primrec fun p : ℕ × ℕ × ℕ => fold (h p.1) p.2.1 p.2.2 := by
  exact Primrec.list_foldl
    ((Primrec.ofNat (List ℕ)).comp (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)
    (hh.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂

theorem primrec_states_param {a b : ℕ → ℕ} {F G : ℕ → ℕ → ℕ → ℕ → ℕ}
    (ha : Primrec a) (hb : Primrec b)
    (hF : Primrec fun p : ℕ × ℕ × ℕ × ℕ => F p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hG : Primrec fun p : ℕ × ℕ × ℕ × ℕ => G p.1 p.2.1 p.2.2.1 p.2.2.2) :
    Primrec₂ fun x n => states (a x) (b x) (F x) (G x) n := by
  exact (Primrec.nat_rec (ha.pair hb) (hF.pair hG).to₂).of_eq fun x n => by
    induction n <;> simp [states, *]

theorem primrec_historyCode_param {h : ℕ → ℕ → ℕ → ℕ}
    (hh : Primrec fun p : ℕ × ℕ × ℕ => h p.1 p.2.1 p.2.2) :
    Primrec₂ fun x n => historyCode (h x) n := by
  have hs : Primrec₂ fun x (p : ℕ × ℕ) => append p.2 (cons (h x p.1 p.2) 0) :=
    (primrec_append.comp (Primrec.snd.comp Primrec.snd)
      (primrec_cons.comp hh (Primrec.const 0))).to₂
  exact (Primrec.nat_rec (Primrec.const 0) hs).of_eq fun x n => by
    induction n <;> simp [historyCode, *]

theorem primrec_historyValue_param {h : ℕ → ℕ → ℕ → ℕ}
    (hh : Primrec fun p : ℕ × ℕ × ℕ => h p.1 p.2.1 p.2.2) :
    Primrec₂ fun x n => historyValue (h x) n := by
  exact (hh.comp (Primrec.pair Primrec.fst
    (Primrec.pair Primrec.snd (primrec_historyCode_param hh)))).to₂

end Lemmatheca.MathematicalLogic.FiniteSequenceCoding
