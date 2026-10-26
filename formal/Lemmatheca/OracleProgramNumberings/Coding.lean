import Lemmatheca.OracleComputation.Substitution
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursionConventions

/-! The specified nine-constructor oracle numbering. -/
namespace Lemmatheca.ComputabilityTheory.OracleProgramNumberings

open OracleComputation

def encodeCode : Code → ℕ
  | .zero => 0
  | .succ => 1
  | .left => 2
  | .right => 3
  | .query => 4
  | .pair c d => 5 + 4 * Nat.pair (encodeCode c) (encodeCode d)
  | .comp c d => 7 + 4 * Nat.pair (encodeCode c) (encodeCode d)
  | .prec c d => 6 + 4 * Nat.pair (encodeCode c) (encodeCode d)
  | .find' c => 8 + 4 * encodeCode c

def decodeCode : ℕ → Code
  | 0 => .zero
  | 1 => .succ
  | 2 => .left
  | 3 => .right
  | 4 => .query
  | n + 5 =>
      let m := n / 4
      have hm : m < n + 5 := lt_of_le_of_lt (Nat.div_le_self n 4) (by omega)
      have _h₁ : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
      have _h₂ : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
      match n % 4 with
      | 0 => .pair (decodeCode m.unpair.1) (decodeCode m.unpair.2)
      | 1 => .prec (decodeCode m.unpair.1) (decodeCode m.unpair.2)
      | 2 => .comp (decodeCode m.unpair.1) (decodeCode m.unpair.2)
      | _ => .find' (decodeCode m)
termination_by e => e
decreasing_by all_goals omega

theorem decode_encode (c : Code) : decodeCode (encodeCode c) = c := by
  induction c with
  | zero | succ | left | right | query => simp [decodeCode, encodeCode]
  | pair c d hc hd =>
      change decodeCode (5 + 4 * Nat.pair (encodeCode c) (encodeCode d)) = _
      rw [Nat.add_comm 5, decodeCode]
      simpa [Nat.add_div] using congrArg₂ Code.pair hc hd
  | comp c d hc hd =>
      change decodeCode (7 + 4 * Nat.pair (encodeCode c) (encodeCode d)) = _
      rw [show 7 + 4 * Nat.pair (encodeCode c) (encodeCode d) =
        (4 * Nat.pair (encodeCode c) (encodeCode d) + 2) + 5 by omega, decodeCode]
      simpa [Nat.add_div] using congrArg₂ Code.comp hc hd
  | prec c d hc hd =>
      change decodeCode (6 + 4 * Nat.pair (encodeCode c) (encodeCode d)) = _
      rw [show 6 + 4 * Nat.pair (encodeCode c) (encodeCode d) =
        (4 * Nat.pair (encodeCode c) (encodeCode d) + 1) + 5 by omega, decodeCode]
      simpa [Nat.add_div] using congrArg₂ Code.prec hc hd
  | find' c hc =>
      change decodeCode (8 + 4 * encodeCode c) = _
      rw [show 8 + 4 * encodeCode c = (4 * encodeCode c + 3) + 5 by omega, decodeCode]
      simpa [Nat.add_div] using congrArg Code.find' hc

theorem encode_decode (e : ℕ) : encodeCode (decodeCode e) = e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    iterate 5 rcases e with _ | e; · simp [decodeCode, encodeCode]
    have hm : e / 4 < e + 5 := lt_of_le_of_lt (Nat.div_le_self e 4) (by omega)
    have h₁ : (e / 4).unpair.1 < e + 5 := lt_of_le_of_lt (e / 4).unpair_left_le hm
    have h₂ : (e / 4).unpair.2 < e + 5 := lt_of_le_of_lt (e / 4).unpair_right_le hm
    have hn := Nat.mod_lt e (by decide : 0 < 4)
    have he := Nat.mod_add_div e 4
    change encodeCode (decodeCode (e + 5)) = e + 5
    rw [decodeCode]
    interval_cases h : e % 4 <;>
      simp [encodeCode, ih _ hm, ih _ h₁, ih _ h₂, Nat.pair_unpair] <;> omega

instance oracleCodeDenumerable : Denumerable Code :=
  Denumerable.mk' ⟨encodeCode, decodeCode, decode_encode, encode_decode⟩

noncomputable def phi (A : Set ℕ) (e x : ℕ) : Part ℕ := eval A (decodeCode e) x

def pairIndex (c d : ℕ) : ℕ := 5 + 4 * Nat.pair c d
def precIndex (c d : ℕ) : ℕ := 6 + 4 * Nat.pair c d
def compIndex (c d : ℕ) : ℕ := 7 + 4 * Nat.pair c d
def findIndex (c : ℕ) : ℕ := 8 + 4 * c

theorem encoding_equations (c d : Code) :
    encodeCode .zero = 0 ∧ encodeCode .succ = 1 ∧ encodeCode .left = 2 ∧
      encodeCode .right = 3 ∧ encodeCode .query = 4 ∧
      encodeCode (.pair c d) = pairIndex (encodeCode c) (encodeCode d) ∧
      encodeCode (.prec c d) = precIndex (encodeCode c) (encodeCode d) ∧
      encodeCode (.comp c d) = compIndex (encodeCode c) (encodeCode d) ∧
      encodeCode (.find' c) = findIndex (encodeCode c) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem code_bijective : Function.Bijective encodeCode :=
  ⟨Function.LeftInverse.injective decode_encode, Function.RightInverse.surjective encode_decode⟩

theorem pairIndex_primitive : Primrec₂ pairIndex :=
  Primrec.nat_add.comp (Primrec.const 5)
    (Primrec.nat_mul.comp (Primrec.const 4) Primrec₂.natPair)
theorem precIndex_primitive : Primrec₂ precIndex :=
  Primrec.nat_add.comp (Primrec.const 6)
    (Primrec.nat_mul.comp (Primrec.const 4) Primrec₂.natPair)
theorem compIndex_primitive : Primrec₂ compIndex :=
  Primrec.nat_add.comp (Primrec.const 7)
    (Primrec.nat_mul.comp (Primrec.const 4) Primrec₂.natPair)
theorem findIndex_primitive : Primrec findIndex :=
  Primrec.nat_add.comp (Primrec.const 8)
    (Primrec.nat_mul.comp (Primrec.const 4) Primrec.id)

theorem primrec_recOn {α σ : Type*} [Primcodable α] [Primcodable σ]
    {c : α → Code} (hc : Primrec c)
    {z s l r q : α → σ}
    (hz : Primrec z) (hs : Primrec s) (hl : Primrec l) (hr : Primrec r) (hq : Primrec q)
    {pr co pc : α → Code → Code → σ → σ → σ}
    (hpr : Primrec fun a : α × Code × Code × σ × σ =>
      pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    (hco : Primrec fun a : α × Code × Code × σ × σ =>
      co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    (hpc : Primrec fun a : α × Code × Code × σ × σ =>
      pc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {rf : α → Code → σ → σ}
    (hrf : Primrec fun a : α × Code × σ => rf a.1 a.2.1 a.2.2) :
    Primrec (fun a => Code.recOn (motive := fun _ => σ) (c a) (z a) (s a) (l a) (r a) (q a)
      (pr a) (co a) (pc a) (rf a)) := by
  open Primrec in
    have hdecode : Primrec decodeCode := by
      have heq : Denumerable.ofNat Code = decodeCode := rfl
      rw [← heq]
      exact Primrec.ofNat Code
    let F (a : α) (c : Code) : σ :=
      Code.recOn (motive := fun _ => σ) c (z a) (s a) (l a) (r a) (q a)
        (pr a) (co a) (pc a) (rf a)
    let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
      let a := p.1.1
      let values := p.1.2
      let n := p.2.1
      let m := p.2.2
      values[m]?.bind fun v => values[m.unpair.1]?.bind fun u =>
        values[m.unpair.2]?.map fun w =>
          cond (n % 4 == 0) (pr a (decodeCode m.unpair.1) (decodeCode m.unpair.2) u w)
            (cond (n % 4 == 1) (pc a (decodeCode m.unpair.1) (decodeCode m.unpair.2) u w)
              (cond (n % 4 == 2) (co a (decodeCode m.unpair.1) (decodeCode m.unpair.2) u w)
                (rf a (decodeCode m) v)))
    have hG₁ : Primrec G₁ := by
      apply option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd))
      apply Primrec₂.mk
      apply option_bind ((list_getElem?.comp (snd.comp fst)
        (fst.comp (Primrec.unpair.comp (snd.comp snd)))).comp fst)
      apply Primrec₂.mk
      apply option_map ((list_getElem?.comp (snd.comp fst)
        (snd.comp (Primrec.unpair.comp (snd.comp snd)))).comp (fst.comp fst))
      apply Primrec₂.mk
      have a : Primrec (fun p : ((((α × List σ) × ℕ × ℕ) × σ) × σ) × σ => p.1.1.1.1.1) :=
        fst.comp (fst.comp (fst.comp (fst.comp fst)))
      have n : Primrec (fun p : ((((α × List σ) × ℕ × ℕ) × σ) × σ) × σ => p.1.1.1.2.1) :=
        fst.comp (snd.comp (fst.comp (fst.comp fst)))
      have m : Primrec (fun p : ((((α × List σ) × ℕ × ℕ) × σ) × σ) × σ => p.1.1.1.2.2) :=
        snd.comp (snd.comp (fst.comp (fst.comp fst)))
      have m₁ := fst.comp (Primrec.unpair.comp m)
      have m₂ := snd.comp (Primrec.unpair.comp m)
      have v : Primrec (fun p : ((((α × List σ) × ℕ × ℕ) × σ) × σ) × σ => p.1.1.2) :=
        snd.comp (fst.comp fst)
      have u : Primrec (fun p : ((((α × List σ) × ℕ × ℕ) × σ) × σ) × σ => p.1.2) :=
        snd.comp fst
      have w : Primrec (fun p : ((((α × List σ) × ℕ × ℕ) × σ) × σ) × σ => p.2) := snd
      have rest := a.pair ((hdecode.comp m₁).pair
        ((hdecode.comp m₂).pair (u.pair w)))
      have rem := nat_mod.comp n (const 4)
      have hp := hpr.comp rest
      have hpc' := hpc.comp rest
      have hco' := hco.comp rest
      have hr' := hrf.comp (a.pair ((hdecode.comp m).pair v))
      exact (Primrec.beq.comp rem (const 0)).cond hp
        ((Primrec.beq.comp rem (const 1)).cond hpc'
          ((Primrec.beq.comp rem (const 2)).cond hco' hr'))
    let G : α → List σ → Option σ := fun a values =>
      values.length.casesOn (some (z a)) fun n =>
      n.casesOn (some (s a)) fun n =>
      n.casesOn (some (l a)) fun n =>
      n.casesOn (some (r a)) fun n =>
      n.casesOn (some (q a)) fun n => G₁ ((a, values), n, n / 4)
    have hG : Primrec₂ G := by
      apply Primrec₂.mk
      apply nat_casesOn (list_length.comp snd) (option_some_iff.mpr (hz.comp fst))
      apply Primrec₂.mk
      apply nat_casesOn snd (option_some_iff.mpr (hs.comp (fst.comp fst)))
      apply Primrec₂.mk
      apply nat_casesOn snd (option_some_iff.mpr (hl.comp (fst.comp (fst.comp fst))))
      apply Primrec₂.mk
      apply nat_casesOn snd (option_some_iff.mpr (hr.comp (fst.comp (fst.comp (fst.comp fst)))))
      apply Primrec₂.mk
      apply nat_casesOn snd (option_some_iff.mpr (hq.comp (fst.comp (fst.comp (fst.comp (fst.comp fst))))))
      apply Primrec₂.mk
      exact hG₁.comp (((fst.pair snd).comp (fst.comp (fst.comp (fst.comp (fst.comp fst))))).pair
        (snd.pair (nat_div.comp snd (const 4))))
    refine ((nat_strong_rec (fun a n => F a (decodeCode n)) hG fun a n => ?_).comp
      Primrec.id (encode_iff.mpr hc)).of_eq fun a => ?_
    · iterate 5 rcases n with _ | n; · simp [G, decodeCode, F] <;> rfl
      simp only [G, List.length_map, List.length_range]
      change G₁ ((a, (List.range (n + 5)).map fun j => F a (decodeCode j)), n, n / 4) =
        some (F a (decodeCode (n + 5)))
      have hm : n / 4 < n + 5 := lt_of_le_of_lt (Nat.div_le_self n 4) (by omega)
      have h₁ : (n / 4).unpair.1 < n + 5 := lt_of_le_of_lt (n / 4).unpair_left_le hm
      have h₂ : (n / 4).unpair.2 < n + 5 := lt_of_le_of_lt (n / 4).unpair_right_le hm
      simp only [G₁, List.getElem?_map, List.getElem?_range, hm, h₁, h₂,
        Option.map_some, Option.bind_some]
      rw [decodeCode]
      have hn := Nat.mod_lt n (by decide : 0 < 4)
      interval_cases h : n % 4 <;> simp [F]
    · change F a (decodeCode (encodeCode (c a))) = _
      rw [decode_encode]


theorem indexed_complete (A : Set ℕ) (f : ℕ → Part ℕ) :
    PartialComputable A f ↔ ∃ e, phi A e = f := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨encodeCode c, by unfold phi; rw [decode_encode]⟩
  · rintro ⟨e, he⟩
    exact ⟨decodeCode e, he⟩

end Lemmatheca.ComputabilityTheory.OracleProgramNumberings
