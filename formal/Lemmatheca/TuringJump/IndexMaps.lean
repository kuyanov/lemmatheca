import Lemmatheca.TuringJump.Core

/-! Ordinary primitive-recursive compilers for substitution and diagonal freezing. -/
namespace Lemmatheca.ComputabilityTheory.TuringJump

open OracleComputation OracleProgramNumberings

noncomputable section

def translate (d e : ℕ) : ℕ := encodeCode (subst (decodeCode d) (decodeCode e))

theorem translate_decode (d e : ℕ) :
    decodeCode (translate d e) = subst (decodeCode d) (decodeCode e) := by
  exact decode_encode _

private theorem jump_decode_pair (p q : ℕ) :
    decodeCode (pairIndex p q) = .pair (decodeCode p) (decodeCode q) := by
  apply code_bijective.1
  simp only [encode_decode, encodeCode, pairIndex]

private theorem jump_decode_prec (p q : ℕ) :
    decodeCode (precIndex p q) = .prec (decodeCode p) (decodeCode q) := by
  apply code_bijective.1
  simp only [encode_decode, encodeCode, precIndex]

private theorem jump_decode_comp (p q : ℕ) :
    decodeCode (compIndex p q) = .comp (decodeCode p) (decodeCode q) := by
  apply code_bijective.1
  simp only [encode_decode, encodeCode, compIndex]

private theorem jump_decode_find (p : ℕ) :
    decodeCode (findIndex p) = .find' (decodeCode p) := by
  apply code_bijective.1
  simp only [encode_decode, encodeCode, findIndex]

theorem translate_equations (d p q i : ℕ) :
    (i < 4 → translate d i = i) ∧ translate d 4 = d ∧
      translate d (pairIndex p q) = pairIndex (translate d p) (translate d q) ∧
      translate d (precIndex p q) = precIndex (translate d p) (translate d q) ∧
      translate d (compIndex p q) = compIndex (translate d p) (translate d q) ∧
      translate d (findIndex p) = findIndex (translate d p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hi
    interval_cases i <;> simp [translate, decodeCode, subst, encodeCode]
  · simp only [translate, decodeCode, subst, encode_decode]
  · unfold translate
    rw [jump_decode_pair]
    rfl
  · unfold translate
    rw [jump_decode_prec]
    rfl
  · unfold translate
    rw [jump_decode_comp]
    rfl
  · unfold translate
    rw [jump_decode_find]
    rfl

theorem translate_primitive : Primrec₂ translate := by
  let F (p : ℕ × ℕ) (c : Code) : ℕ :=
    Code.recOn (motive := fun _ => ℕ) c 0 1 2 3 p.1
      (fun _ _ u v => pairIndex u v) (fun _ _ u v => compIndex u v)
      (fun _ _ u v => precIndex u v) (fun _ u => findIndex u)
  have h : Primrec (fun p : ℕ × ℕ => F p (decodeCode p.2)) := by
    apply primrec_recOn ((Primrec.ofNat Code).comp Primrec.snd)
      (Primrec.const 0) (Primrec.const 1) (Primrec.const 2) (Primrec.const 3) Primrec.fst
    · exact pairIndex_primitive.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact compIndex_primitive.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact precIndex_primitive.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact findIndex_primitive.comp (Primrec.snd.comp Primrec.snd)
  apply h.of_eq
  intro p
  have he (c : Code) : F p c = encodeCode (subst (decodeCode p.1) c) := by
    induction c <;> simp_all [F, subst, encodeCode, pairIndex, compIndex, precIndex,
      findIndex, encode_decode]
  exact he (decodeCode p.2)

theorem translate_eval (A B : Set ℕ) (d : ℕ)
    (hd : TuringDegrees.Reduces (decodeCode d) A B) (e x : ℕ) :
    phi B (translate d e) x = phi A e x := by
  unfold phi translate
  rw [decode_encode]
  exact subst_eval A B (decodeCode d) hd (decodeCode e) x

def jumpMap (d e : ℕ) : ℕ := freeze (translate d e) e

theorem jump_map_primitive : Primrec₂ jumpMap := by
  exact freeze_primitive.comp translate_primitive Primrec.snd

theorem jump_map_eval (A B : Set ℕ) (d : ℕ)
    (hd : TuringDegrees.Reduces (decodeCode d) A B) (e y : ℕ) :
    phi B (jumpMap d e) y = phi B (translate d e) e ∧
      phi B (translate d e) e = phi A e e := by
  exact ⟨freeze_eval B (translate d e) e y, translate_eval A B d hd e e⟩

theorem jump_map_membership (A B : Set ℕ) (d : ℕ)
    (hd : TuringDegrees.Reduces (decodeCode d) A B) (e : ℕ) :
    e ∈ jump A ↔ jumpMap d e ∈ jump B := by
  change (phi A e e).Dom ↔ (phi B (jumpMap d e) (jumpMap d e)).Dom
  rw [(jump_map_eval A B d hd e (jumpMap d e)).1,
    (jump_map_eval A B d hd e (jumpMap d e)).2]

theorem jump_monotone {A B : Set ℕ} (hAB : TuringDegrees.Reducible A B) :
    ManyOneReducible (fun e => e ∈ jump A) (fun e => e ∈ jump B) := by
  obtain ⟨c, hc⟩ := hAB
  have hd : TuringDegrees.Reduces (decodeCode (encodeCode c)) A B := by
    rwa [decode_encode]
  exact ⟨jumpMap (encodeCode c),
    (jump_map_primitive.comp (Primrec.const (encodeCode c)) Primrec.id).to_comp,
    jump_map_membership A B (encodeCode c) hd⟩

theorem reverse_query_maps (A B : Set ℕ) (g : ℕ → ℕ) (hg : Computable g)
    (hred : ∀ e, e ∈ jump A ↔ g e ∈ jump B) :
    Computable (g ∘ queryMap 1) ∧ Computable (g ∘ queryMap 0) ∧
      ∀ x, (x ∈ A ↔ g (queryMap 1 x) ∈ jump B) ∧
        (x ∉ A ↔ g (queryMap 0 x) ∈ jump B) := by
  exact ⟨hg.comp (query_map_primitive 1).to_comp, hg.comp (query_map_primitive 0).to_comp,
    fun x => ⟨(membership_maps A x).1.trans (hred (queryMap 1 x)),
      (membership_maps A x).2.trans (hred (queryMap 0 x))⟩⟩

theorem jump_characterization (A B : Set ℕ) :
    TuringDegrees.Reducible A B ↔
      ManyOneReducible (fun e => e ∈ jump A) (fun e => e ∈ jump B) := by
  constructor
  · exact jump_monotone
  · rintro ⟨g, hg, hred⟩
    obtain ⟨h1, h0, hm⟩ := reverse_query_maps A B g hg hred
    apply (relative_decidable_iff_reducible B A).mp
    apply (relative_two_sided_recognition B A).mpr
    exact ⟨(relative_ce_iff_jump B A).mpr ⟨g ∘ queryMap 1, h1, fun x => (hm x).1⟩,
      (relative_ce_iff_jump B Aᶜ).mpr ⟨g ∘ queryMap 0, h0, fun x => (hm x).2⟩⟩

end
end Lemmatheca.ComputabilityTheory.TuringJump
