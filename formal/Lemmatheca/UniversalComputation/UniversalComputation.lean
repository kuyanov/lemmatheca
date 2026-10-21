import Mathlib.Computability.Halting
import Lemmatheca.PartialRecursiveFunctions.PartialRecursiveFunctions
import Lemmatheca.CodingFiniteSequences.FiniteSequenceCoding

/-! Numerical program indices, universal evaluation, effective parameters and
computably enumerable sets. The program datatype and encoding are the shared
`Nat.Partrec.Code`; finite-arity correspondence is supplied by the machines unit.
-/

namespace Lemmatheca.ComputabilityTheory.UniversalComputation

open Encodable Denumerable
open Nat.Partrec (Code)

def phi (e x : ℕ) : Part ℕ := Code.eval (ofNat Code e) x

def boundedValue (k e x : ℕ) : ℕ :=
  (Code.evaln k (ofNat Code e) x).elim 0 Nat.succ

def certificate (e x k : ℕ) : Prop := 0 < boundedValue k e x

def specialize (e a : ℕ) : ℕ := encode (Code.curry (ofNat Code e) a)

def haltingDiagonal : Set ℕ := {e | (phi e e).Dom}

def haltingPairs : Set ℕ := {n | (phi n.unpair.1 n.unpair.2).Dom}

def eraseSearch : Code → Code
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .pair c d => .pair (eraseSearch c) (eraseSearch d)
  | .comp c d => .comp (eraseSearch c) (eraseSearch d)
  | .prec c d => .prec (eraseSearch c) (eraseSearch d)
  | .rfind' _ => .zero

def SearchFree : Code → Prop
  | .zero | .succ | .left | .right => True
  | .pair c d | .comp c d | .prec c d => SearchFree c ∧ SearchFree d
  | .rfind' _ => False

theorem encoding_equations (c d : Code) :
    encode Code.zero = 0 ∧ encode Code.succ = 1 ∧ encode Code.left = 2 ∧
    encode Code.right = 3 ∧ encode (Code.pair c d) = 4 * Nat.pair (encode c) (encode d) + 4 ∧
    encode (Code.comp c d) = 4 * Nat.pair (encode c) (encode d) + 6 ∧
    encode (Code.prec c d) = 4 * Nat.pair (encode c) (encode d) + 5 ∧
    encode (Code.rfind' c) = 4 * encode c + 7 := by
  simp only [Code.encodeCode_eq, Code.encodeCode]
  and_intros <;> first | trivial | omega

theorem boundedValue_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => boundedValue p.1.1 p.1.2 p.2) := by
  have hb := Code.primrec_evaln.comp
    (((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.ofNat Code).comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)
  exact (Primrec.encode.comp hb).of_eq fun p => by
    cases he : Code.evaln p.1.1 (ofNat Code p.1.2) p.2 <;> simp [boundedValue, he]

theorem boundedValue_output (k e x y : ℕ) :
    boundedValue k e x = y + 1 ↔ y ∈ Code.evaln k (ofNat Code e) x := by
  unfold boundedValue
  cases Code.evaln k (ofNat Code e) x <;> simp [Option.mem_def]

theorem phi_output (e x y : ℕ) :
    y ∈ phi e x ↔ ∃ k, boundedValue k e x = y + 1 := by
  exact Code.evaln_complete.trans (exists_congr fun k => (boundedValue_output k e x y).symm)

theorem phi_domain (e x : ℕ) : (phi e x).Dom ↔ ∃ k, certificate e x k := by
  rw [Part.dom_iff_mem]
  simp only [phi_output, certificate]
  constructor
  · rintro ⟨y, k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨boundedValue k e x - 1, k, by omega⟩

theorem certificate_primitive :
    PrimrecPred (fun p : (ℕ × ℕ) × ℕ => certificate p.1.1 p.1.2 p.2) := by
  exact Primrec.nat_lt.comp (Primrec.const 0)
    (boundedValue_primitive.comp ((Primrec.snd.pair (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst)))

theorem phi_recursive : Partrec₂ phi := by
  exact Code.eval_part.comp ((Computable.ofNat Code).comp Computable.fst) Computable.snd

theorem phi_complete {f : ℕ → Part ℕ} (hf : Nat.Partrec f) :
    ∃ e, phi e = f := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  refine ⟨encode c, ?_⟩
  funext x
  simpa only [phi, ofNat_encode] using congrFun hc x

theorem specialize_primitive : Primrec₂ specialize := by
  exact Primrec.encode.comp₂
    (Code.primrec₂_curry.comp₂ ((Primrec.ofNat Code).comp₂ Primrec₂.left) Primrec₂.right)

theorem specialize_eval (e a x : ℕ) : phi (specialize e a) x = phi e (Nat.pair a x) := by
  simp only [phi, specialize, ofNat_encode, Code.eval_curry]

theorem tuple_specialization {m n : ℕ} :
    ∃ s : ℕ → List.Vector ℕ m → ℕ,
      Primrec₂ s ∧ ∀ e a (x : List.Vector ℕ n),
        phi (s e a) (encode x.toList) = phi e (encode (a.toList ++ x.toList)) := by
  let F : ℕ → ℕ := Nat.unpaired FiniteSequenceCoding.append
  have hF : Nat.Primrec F := Primrec.nat_iff.mp
    (FiniteSequenceCoding.primrec_append.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair))
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Nat.Partrec.of_primrec hF)
  let s : ℕ → List.Vector ℕ m → ℕ := fun e a =>
    encode (Code.comp (ofNat Code e) (Code.curry c (encode a.toList)))
  refine ⟨s, ?_, ?_⟩
  · exact Primrec.encode.comp₂
      (Code.primrec₂_comp.comp₂ ((Primrec.ofNat Code).comp₂ Primrec₂.left)
        (Code.primrec₂_curry.comp₂ (Primrec₂.const c)
          ((Primrec.encode.comp Primrec.vector_toList).comp₂ Primrec₂.right)))
  · intro e a x
    simp only [s, phi, ofNat_encode, Code.eval, Code.eval_curry]
    rw [congrFun hc (Nat.pair (encode a.toList) (encode x.toList))]
    change (Part.some (F (Nat.pair (encode a.toList) (encode x.toList)))).bind
      (fun z : ℕ => Code.eval (ofNat Code e) z) = _
    rw [Part.bind_some]
    apply congrArg (Code.eval (ofNat Code e))
    simpa [F, Nat.unpaired, FiniteSequenceCoding.code] using
      (FiniteSequenceCoding.append_code a.toList x.toList)

theorem no_total_universal :
    ¬ ∃ V : ℕ → ℕ → ℕ, Computable₂ V ∧
      ∀ f : ℕ → ℕ, Computable f → ∃ e, ∀ x, V e x = f x := by
  rintro ⟨V, hV, h⟩
  have hd : Computable (fun x => V x x + 1) :=
    Primrec.succ.to_comp.comp (hV.comp Computable.id Computable.id)
  obtain ⟨e, he⟩ := h _ hd
  have := he e
  omega

theorem eraseSearch_primitive : Primrec eraseSearch := by
  have hp := Code.primrec_recOn (α := Code) (σ := Code) Primrec.id
    (Primrec.const Code.zero) (Primrec.const Code.succ)
    (Primrec.const Code.left) (Primrec.const Code.right)
    (pr := fun _ _ _ a b => Code.pair a b)
    (Code.primrec₂_pair.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (co := fun _ _ _ a b => Code.comp a b)
    (Code.primrec₂_comp.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (pc := fun _ _ _ a b => Code.prec a b)
    (Code.primrec₂_prec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (rf := fun _ _ _ => Code.zero) (Primrec.const Code.zero)
  apply hp.of_eq
  intro c
  induction c <;> simp_all [eraseSearch]

theorem eraseSearch_searchFree (c : Code) : SearchFree (eraseSearch c) := by
  induction c <;> simp_all [eraseSearch, SearchFree]

theorem searchFree_fixed (c : Code) (h : SearchFree c) : eraseSearch c = c := by
  induction c <;> simp_all [eraseSearch, SearchFree]

theorem searchFree_eval (c : Code) (h : SearchFree c) :
    ∃ f : ℕ → ℕ, Nat.Primrec f ∧ Code.eval c = fun x => Part.some (f x) := by
  induction c with
  | zero => exact ⟨fun _ => 0, Nat.Primrec.zero, rfl⟩
  | succ => exact ⟨Nat.succ, Nat.Primrec.succ, rfl⟩
  | left => exact ⟨fun n => n.unpair.1, Nat.Primrec.left, rfl⟩
  | right => exact ⟨fun n => n.unpair.2, Nat.Primrec.right, rfl⟩
  | pair c d ihc ihd =>
    obtain ⟨f, hf, he⟩ := ihc h.1
    obtain ⟨g, hg, hd⟩ := ihd h.2
    refine ⟨fun n => Nat.pair (f n) (g n), hf.pair hg, ?_⟩
    funext x
    simp [Code.eval, he, hd, Seq.seq]
  | comp c d ihc ihd =>
    obtain ⟨f, hf, he⟩ := ihc h.1
    obtain ⟨g, hg, hd⟩ := ihd h.2
    refine ⟨fun n => f (g n), hf.comp hg, ?_⟩
    funext x
    simp [Code.eval, he, hd]
  | prec c d ihc ihd =>
    obtain ⟨f, hf, he⟩ := ihc h.1
    obtain ⟨g, hg, hd⟩ := ihd h.2
    let F : ℕ → ℕ := Nat.unpaired fun a n => n.rec (f a) fun i v => g (Nat.pair a (Nat.pair i v))
    refine ⟨F, hf.prec hg, ?_⟩
    funext x
    obtain ⟨⟨a, n⟩, rfl⟩ := Nat.pairEquiv.surjective x
    change Code.eval (.prec c d) (Nat.pair a n) = _
    induction n with
    | zero => simp [Code.eval_prec_zero, he, F]
    | succ n ih => simp [Code.eval_prec_succ, ih, hd, F]
  | rfind' c _ => exact False.elim h

theorem searchFree_complete {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ c : Code, SearchFree c ∧ Code.eval c = fun x => Part.some (f x) := by
  induction hf with
  | zero => exact ⟨.zero, trivial, rfl⟩
  | succ => exact ⟨.succ, trivial, rfl⟩
  | left => exact ⟨.left, trivial, rfl⟩
  | right => exact ⟨.right, trivial, rfl⟩
  | pair hf hg ihf ihg =>
    obtain ⟨c, hc, he⟩ := ihf
    obtain ⟨d, hd, hdv⟩ := ihg
    refine ⟨.pair c d, ⟨hc, hd⟩, ?_⟩
    funext x
    simp [Code.eval, he, hdv, Seq.seq]
  | comp hf hg ihf ihg =>
    obtain ⟨c, hc, he⟩ := ihf
    obtain ⟨d, hd, hdv⟩ := ihg
    refine ⟨.comp c d, ⟨hc, hd⟩, ?_⟩
    funext x
    simp [Code.eval, he, hdv]
  | prec hf hg ihf ihg =>
    obtain ⟨c, hc, he⟩ := ihf
    obtain ⟨d, hd, hdv⟩ := ihg
    refine ⟨.prec c d, ⟨hc, hd⟩, ?_⟩
    funext x
    obtain ⟨⟨a, n⟩, rfl⟩ := Nat.pairEquiv.surjective x
    change Code.eval (.prec c d) (Nat.pair a n) = _
    induction n with
    | zero => simp [Code.eval_prec_zero, he]
    | succ n ih => simp [Code.eval_prec_succ, ih, hdv]

theorem eraseSearch_total (c : Code) (x : ℕ) : (Code.eval (eraseSearch c) x).Dom := by
  obtain ⟨f, _, hf⟩ := searchFree_eval (eraseSearch c) (eraseSearch_searchFree c)
  rw [hf]
  trivial

noncomputable def primitiveDiagonal (e : ℕ) : ℕ :=
  (Code.eval (eraseSearch (ofNat Code e)) e).get (eraseSearch_total _ _) + 1

theorem primitiveDiagonal_computable : Computable primitiveDiagonal := by
  have hp : Partrec (fun e => Code.eval (eraseSearch (ofNat Code e)) e) :=
    Code.eval_part.comp (eraseSearch_primitive.to_comp.comp (Computable.ofNat Code)) Computable.id
  have hs := hp.map (Computable.succ.comp Computable.snd).to₂
  apply hs.of_eq_tot
  intro e
  exact Part.mem_map _ (Part.get_mem (eraseSearch_total (ofNat Code e) e))

theorem primitiveDiagonal_not_primitive : ¬ Nat.Primrec primitiveDiagonal := by
  intro hd
  obtain ⟨c, hc, hce⟩ := searchFree_complete hd
  have hp : eraseSearch (ofNat Code (encode c)) = c := by
    simp [searchFree_fixed c hc]
  have he : Code.eval (eraseSearch (ofNat Code (encode c))) (encode c) =
      Part.some (primitiveDiagonal (encode c)) := by rw [hp, hce]
  have hg := Part.get_mem (eraseSearch_total (ofNat Code (encode c)) (encode c))
  have heq := Part.mem_unique hg (Part.eq_some_iff.mp he)
  have hddef : primitiveDiagonal (encode c) =
      (Code.eval (eraseSearch (ofNat Code (encode c))) (encode c)).get
        (eraseSearch_total _ _) + 1 := rfl
  omega

theorem unary_primitive_iff (f : ℕ → ℕ) :
    Nat.Primrec' (fun v : List.Vector ℕ 1 => f (v.get 0)) ↔ Nat.Primrec f := by
  simpa only [List.Vector.get_zero] using
    (Nat.Primrec'.prim_iff₁ (f := f)).trans Primrec.nat_iff

theorem haltingDiagonal_undecidable :
    ¬ ComputablePred (fun e => e ∈ haltingDiagonal) := by
  classical
  intro h
  let g : ℕ → Part ℕ := fun x => if x ∈ haltingDiagonal then Part.none else Part.some 0
  have hg : Partrec g :=
    (Partrec.cond h.decide Partrec.none (Computable.const 0).partrec).of_eq fun x => by
      simp [g]
  obtain ⟨j, hj⟩ := phi_complete (Partrec.nat_iff.mp hg)
  have hh : (phi j j).Dom ↔ j ∉ haltingDiagonal := by
    rw [hj]
    simp only [g]
    split_ifs <;> simp_all
  change ((phi j j).Dom ↔ ¬ (phi j j).Dom) at hh
  tauto

theorem haltingPairs_undecidable :
    ¬ ComputablePred (fun e => e ∈ haltingPairs) := by
  classical
  intro h
  have hh : ComputablePred (fun e => Nat.pair e e ∈ haltingPairs) :=
    Computable.computablePred (h.decide.comp (Primrec₂.natPair.comp Primrec.id Primrec.id).to_comp)
  exact haltingDiagonal_undecidable (hh.of_eq fun e => by simp [haltingPairs, haltingDiagonal])

theorem partial_diagonal_diverges (j : ℕ)
    (h : ∀ x, phi j x = (phi x x).map Nat.succ) : ¬ (phi j j).Dom := by
  intro hd
  obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hd
  have hs : n + 1 ∈ phi j j := by
    rw [h j]
    exact Part.mem_map _ hn
  have := Part.mem_unique hs hn
  omega

noncomputable def indicator (A : ℕ → Prop) (x : ℕ) : ℕ := by
  classical
  exact if A x then 1 else 0

theorem decidable_iff_characteristic (A : ℕ → Prop) :
    ComputablePred A ↔ ∃ f : ℕ → ℕ, Computable f ∧
      ∀ x, f x = indicator A x := by
  classical
  constructor
  · intro h
    have hf : Computable (indicator A) :=
      (Primrec.dom_bool (fun b => if b then 1 else 0)).to_comp.comp h.decide |>.of_eq fun x => by
        simp [indicator]
    exact ⟨indicator A, hf, fun _ => rfl⟩
  · rintro ⟨f, hf, he⟩
    have hp : Computable (fun x => decide (f x = 1)) :=
      (Primrec.eq.decide.to_comp.comp hf (Computable.const 1))
    exact Computable.computablePred (hp.of_eq fun x => by simp [he, indicator])

theorem enumerable_iff_domain (A : ℕ → Prop) :
    REPred A ↔ ∃ f : ℕ → Part ℕ, Nat.Partrec f ∧ ∀ x, A x ↔ (f x).Dom := by
  constructor
  · intro hA
    let f : ℕ → Part ℕ := fun x =>
      (Part.assert (A x) fun _ => Part.some ()).map (fun _ => 0)
    have hf : Nat.Partrec f := Partrec.nat_iff.mp
      (hA.map (Computable.const 0).to₂)
    refine ⟨f, hf, fun x => ?_⟩
    simp only [f, Part.map_Dom]
    change A x ↔ ∃ _ : A x, True
    simp
  · rintro ⟨f, hf, he⟩
    exact (Partrec.nat_iff.mpr hf).dom_re.of_eq fun x => (he x).symm

theorem enumerable_iff_index (A : ℕ → Prop) :
    REPred A ↔ ∃ e, ∀ x, A x ↔ (phi e x).Dom := by
  rw [enumerable_iff_domain]
  constructor
  · rintro ⟨f, hf, he⟩
    obtain ⟨e, rfl⟩ := phi_complete hf
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    exact ⟨phi e, Partrec.nat_iff.mp (phi_recursive.comp (Computable.const e) Computable.id), he⟩

theorem enumerable_iff_primitive_certificate (A : ℕ → Prop) :
    REPred A ↔ ∃ R : ℕ → ℕ → Prop,
      PrimrecPred (fun p : ℕ × ℕ => R p.1 p.2) ∧ ∀ x, A x ↔ ∃ t, R x t := by
  classical
  constructor
  · intro hA
    obtain ⟨e, he⟩ := (enumerable_iff_index A).mp hA
    refine ⟨certificate e, ?_, fun x => (he x).trans (phi_domain e x)⟩
    exact certificate_primitive.comp ((Primrec.const e).pair Primrec.fst |>.pair Primrec.snd)
  · rintro ⟨R, hR, he⟩
    have hc : Computable₂ (fun x t => decide (R x t)) := hR.decide.to_comp
    have hs : Partrec (fun x => Nat.rfind (fun t => Part.some (decide (R x t)))) :=
      Partrec.rfind hc.partrec₂
    apply hs.dom_re.of_eq
    intro x
    constructor
    · intro hd
      obtain ⟨n, hn, _⟩ := Nat.rfind_dom.mp hd
      exact (he x).mpr ⟨n, by simpa using hn⟩
    · intro ha
      obtain ⟨n, hn⟩ := (he x).mp ha
      exact Nat.rfind_dom.mpr ⟨n, by simpa using hn, fun _ => trivial⟩

theorem enumerable_iff_decidable_certificate (A : ℕ → Prop) :
    REPred A ↔ ∃ R : ℕ → ℕ → Prop,
      ComputablePred (fun p : ℕ × ℕ => R p.1 p.2) ∧ ∀ x, A x ↔ ∃ t, R x t := by
  classical
  constructor
  · intro h
    obtain ⟨R, hR, he⟩ := (enumerable_iff_primitive_certificate A).mp h
    exact ⟨R, hR.computablePred, he⟩
  · rintro ⟨R, hR, he⟩
    have hc : Computable₂ (fun x t => decide (R x t)) := hR.decide
    have hs : Partrec (fun x => Nat.rfind (fun t => Part.some (decide (R x t)))) :=
      Partrec.rfind hc.partrec₂
    apply hs.dom_re.of_eq
    intro x
    constructor
    · intro hd
      obtain ⟨n, hn, _⟩ := Nat.rfind_dom.mp hd
      exact (he x).mpr ⟨n, by simpa using hn⟩
    · intro ha
      obtain ⟨n, hn⟩ := (he x).mp ha
      exact Nat.rfind_dom.mpr ⟨n, by simpa using hn, fun _ => trivial⟩

private theorem empty_enumerable : REPred (fun _ : ℕ => False) :=
  (Partrec.none : Partrec (fun _ : ℕ => (Part.none : Part ℕ))).dom_re

theorem enumerable_iff_primitive_range (A : ℕ → Prop) :
    REPred A ↔ (∀ x, ¬ A x) ∨
      ∃ f : ℕ → ℕ, Nat.Primrec f ∧ ∀ y, A y ↔ ∃ x, f x = y := by
  classical
  constructor
  · intro hA
    by_cases h0 : ∀ x, ¬ A x
    · exact Or.inl h0
    · obtain ⟨a, ha⟩ := not_forall_not.mp h0
      obtain ⟨R, hR, he⟩ := (enumerable_iff_primitive_certificate A).mp hA
      let f : ℕ → ℕ := fun z => if R z.unpair.1 z.unpair.2 then z.unpair.1 else a
      have hf : Primrec f := Primrec.ite (hR.comp Primrec.unpair)
        (Primrec.fst.comp Primrec.unpair) (Primrec.const a)
      refine Or.inr ⟨f, Primrec.nat_iff.mp hf, fun y => ?_⟩
      constructor
      · intro hy
        obtain ⟨t, ht⟩ := (he y).mp hy
        exact ⟨Nat.pair y t, by simp [f, ht]⟩
      · rintro ⟨z, rfl⟩
        dsimp only [f]
        split_ifs with hz
        · exact (he _).mpr ⟨_, hz⟩
        · exact ha
  · rintro (h0 | ⟨f, hf, he⟩)
    · exact empty_enumerable.of_eq fun x => by simp [h0 x]
    · apply (enumerable_iff_primitive_certificate A).mpr
      refine ⟨fun y x => f x = y, ?_, he⟩
      exact Primrec.eq.comp ((Primrec.nat_iff.mpr hf).comp Primrec.snd) Primrec.fst

theorem enumerable_iff_partial_range (A : ℕ → Prop) :
    REPred A ↔ ∃ f : ℕ → Part ℕ, Nat.Partrec f ∧ ∀ y, A y ↔ ∃ x, y ∈ f x := by
  classical
  constructor
  · intro hA
    obtain h0 | ⟨f, hf, he⟩ := (enumerable_iff_primitive_range A).mp hA
    · refine ⟨fun _ => Part.none, Nat.Partrec.none, ?_⟩
      intro y
      simp [h0 y]
    · exact ⟨fun x => Part.some (f x), Nat.Partrec.of_primrec hf, fun y => by simpa only [Part.mem_some_iff, eq_comm] using he y⟩
  · rintro ⟨f, hf, he⟩
    obtain ⟨e, rfl⟩ := phi_complete hf
    apply (enumerable_iff_primitive_certificate A).mpr
    refine ⟨fun y w => boundedValue w.unpair.2 e w.unpair.1 = y + 1, ?_, ?_⟩
    · have hu := Primrec.unpair.comp (Primrec.snd : Primrec (@Prod.snd ℕ ℕ))
      exact Primrec.eq.comp
        (boundedValue_primitive.comp (((Primrec.snd.comp hu).pair (Primrec.const e)).pair
          (Primrec.fst.comp hu)))
        (Primrec.succ.comp Primrec.fst)
    · intro y
      rw [he y]
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨k, hk⟩ := (phi_output e x y).mp hx
        exact ⟨Nat.pair x k, by simpa using hk⟩
      · rintro ⟨w, hw⟩
        exact ⟨w.unpair.1, (phi_output e w.unpair.1 y).mpr ⟨w.unpair.2, hw⟩⟩

theorem enumerable_iff_total_range (A : ℕ → Prop) :
    REPred A ↔ (∀ x, ¬ A x) ∨
      ∃ f : ℕ → ℕ, Computable f ∧ ∀ y, A y ↔ ∃ x, f x = y := by
  constructor
  · intro hA
    obtain h0 | ⟨f, hf, he⟩ := (enumerable_iff_primitive_range A).mp hA
    · exact Or.inl h0
    · exact Or.inr ⟨f, (Primrec.nat_iff.mpr hf).to_comp, he⟩
  · rintro (h0 | ⟨f, hf, he⟩)
    · exact empty_enumerable.of_eq fun x => by simp [h0 x]
    · apply (enumerable_iff_partial_range A).mpr
      exact ⟨fun x => Part.some (f x), Partrec.nat_iff.mp hf.partrec,
        fun y => by simpa only [Part.mem_some_iff, eq_comm] using he y⟩

theorem enumerable_union {A B : ℕ → Prop} (hA : REPred A) (hB : REPred B) :
    REPred (fun x => A x ∨ B x) := by
  obtain ⟨R, hR, he⟩ := (enumerable_iff_primitive_certificate A).mp hA
  obtain ⟨S, hS, hs⟩ := (enumerable_iff_primitive_certificate B).mp hB
  apply (enumerable_iff_primitive_certificate _).mpr
  refine ⟨fun x t => R x t ∨ S x t, hR.or hS, ?_⟩
  intro x
  simp only [he, hs, exists_or]

theorem enumerable_inter {A B : ℕ → Prop} (hA : REPred A) (hB : REPred B) :
    REPred (fun x => A x ∧ B x) := by
  obtain ⟨R, hR, he⟩ := (enumerable_iff_primitive_certificate A).mp hA
  obtain ⟨S, hS, hs⟩ := (enumerable_iff_primitive_certificate B).mp hB
  apply (enumerable_iff_primitive_certificate _).mpr
  refine ⟨fun x w => R x w.unpair.1 ∧ S x w.unpair.2, ?_, ?_⟩
  · have hu := Primrec.unpair.comp (Primrec.snd : Primrec (@Prod.snd ℕ ℕ))
    exact (hR.comp (Primrec.fst.pair (Primrec.fst.comp hu))).and
      (hS.comp (Primrec.fst.pair (Primrec.snd.comp hu)))
  · intro x
    rw [he, hs]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      exact ⟨Nat.pair i j, by simpa using And.intro hi hj⟩
    · rintro ⟨w, hi, hj⟩
      exact ⟨⟨w.unpair.1, hi⟩, ⟨w.unpair.2, hj⟩⟩

theorem enumerable_exists {A : ℕ → ℕ → Prop}
    (hA : REPred (fun p : ℕ × ℕ => A p.1 p.2)) : REPred (fun x => ∃ y, A x y) := by
  have hN : REPred (fun q : ℕ => A q.unpair.1 q.unpair.2) :=
    hA.comp Computable.unpair
  obtain ⟨R, hR, he⟩ := (enumerable_iff_primitive_certificate _).mp hN
  apply (enumerable_iff_primitive_certificate _).mpr
  refine ⟨fun x w => R (Nat.pair x w.unpair.1) w.unpair.2, ?_, ?_⟩
  · have hu := Primrec.unpair.comp (Primrec.snd : Primrec (@Prod.snd ℕ ℕ))
    exact hR.comp ((Primrec₂.natPair.comp Primrec.fst (Primrec.fst.comp hu)).pair
      (Primrec.snd.comp hu))
  · intro x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨t, ht⟩ := (he (Nat.pair x y)).mp (by simpa using hy)
      exact ⟨Nat.pair y t, by simpa using ht⟩
    · rintro ⟨w, hw⟩
      exact ⟨w.unpair.1, by simpa using (he (Nat.pair x w.unpair.1)).mpr ⟨w.unpair.2, hw⟩⟩

theorem enumerable_preimage {A : ℕ → Prop} {g : ℕ → ℕ}
    (hA : REPred A) (hg : Computable g) : REPred (fun x => A (g x)) := by
  exact hA.comp hg

theorem enumerable_image {A : ℕ → Prop} {g : ℕ → ℕ}
    (hA : REPred A) (hg : Computable g) :
    REPred (fun y => ∃ x, A x ∧ g x = y) := by
  obtain h0 | ⟨f, hf, he⟩ := (enumerable_iff_total_range A).mp hA
  · exact empty_enumerable.of_eq fun y => by simp [h0]
  · apply (enumerable_iff_total_range _).mpr
    refine Or.inr ⟨fun x => g (f x), hg.comp hf, ?_⟩
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (he x).mp hx
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨f z, (he _).mpr ⟨z, rfl⟩, rfl⟩

theorem countable_dovetail {e : ℕ → ℕ} (he : Computable e) :
    ∃ h : ℕ → Part ℕ, Nat.Partrec h ∧
      ∀ x, (h x).Dom ↔ ∃ i, (phi (e i) x).Dom := by
  have hr : REPred (fun p : ℕ × ℕ => (phi (e p.2) p.1).Dom) :=
    (phi_recursive.comp (he.comp Computable.snd) Computable.fst).dom_re
  have hA := enumerable_exists (A := fun x i => (phi (e i) x).Dom) hr
  obtain ⟨h, hh, heq⟩ := (enumerable_iff_domain _).mp hA
  exact ⟨h, hh, fun x => (heq x).symm⟩

theorem haltingDiagonal_enumerable : REPred (fun e => e ∈ haltingDiagonal) := by
  exact (phi_recursive.comp Computable.id Computable.id).dom_re

theorem haltingPairs_enumerable : REPred (fun e => e ∈ haltingPairs) := by
  exact (phi_recursive.comp
    (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp).dom_re

theorem haltingDiagonal_complement_not_enumerable :
    ¬ REPred (fun e => e ∉ haltingDiagonal) := by
  intro h
  exact haltingDiagonal_undecidable
    (ComputablePred.computable_iff_re_compl_re'.mpr ⟨haltingDiagonal_enumerable, h⟩)

theorem haltingPairs_complement_not_enumerable :
    ¬ REPred (fun e => e ∉ haltingPairs) := by
  intro h
  exact haltingPairs_undecidable
    (ComputablePred.computable_iff_re_compl_re'.mpr ⟨haltingPairs_enumerable, h⟩)

theorem singleton_range_not_injective (f : ℕ → ℕ) (a : ℕ)
    (h : Set.range f = {a}) : ¬ Function.Injective f := by
  intro hi
  have h0 : f 0 = a := by simpa [h] using (Set.mem_range_self 0 : f 0 ∈ Set.range f)
  have h1 : f 1 = a := by simpa [h] using (Set.mem_range_self 1 : f 1 ∈ Set.range f)
  exact Nat.zero_ne_one (hi (h0.trans h1.symm))

end Lemmatheca.ComputabilityTheory.UniversalComputation
