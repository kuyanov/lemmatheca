import Lemmatheca.MathematicalLogic.PAComputations
import Lemmatheca.MathematicalLogic.ArithmeticBoundedFormulas
import Lemmatheca.MathematicalLogic.UniversalComputation

/-! Standard-model arithmetic definability.  The formulas are the shared
arithmetic formulas; computability and enumerability are the existing notions.
No internal PA totality claim is part of these definitions. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticDefinability

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open PAComputations FirstOrderProofs

noncomputable section

-- Select the encoding supplied by the primitive-codable tuple instance.
local instance (priority := high) tupleEncodable (n : ℕ) : Encodable (Fin n → ℕ) :=
  (inferInstance : Primcodable (Fin n → ℕ)).toEncodable

/-- Truth in the specified standard arithmetic structure, at every assignment. -/
def Defines {α : Type} (R : (α → ℕ) → Prop) (A : language.Formula α) : Prop :=
  ∀ x, A.Realize x ↔ R x

def SigmaOneDefinable {α : Type} (R : (α → ℕ) → Prop) : Prop :=
  ∃ A : language.Formula α, BoundedSigmaOne A ∧ Defines R A

def PiOne {α : Type} (A : language.Formula α) : Prop :=
  ∃ k : ℕ, ∃ D : language.Formula (α ⊕ Fin k),
    BoundedArithmetic D ∧ A = D.iAlls (Fin k)

def PiOneDefinable {α : Type} (R : (α → ℕ) → Prop) : Prop :=
  ∃ A : language.Formula α, PiOne A ∧ Defines R A

/-- This is a class of standard relations, not a literal syntactic intersection. -/
def DeltaOneDefinable {α : Type} (R : (α → ℕ) → Prop) : Prop :=
  SigmaOneDefinable R ∧ PiOneDefinable R

/-- Effective change between function tuples and the corpus's vector tuples. -/
theorem tuple_recoding {n : ℕ} (R : (Fin n → ℕ) → Prop) :
    (REPred R ↔ REPred (fun v : List.Vector ℕ n => R v.get)) ∧
    (ComputablePred R ↔ ComputablePred (fun v : List.Vector ℕ n => R v.get)) := by
  classical
  have hx (x : Fin n → ℕ) : (List.Vector.ofFn x).get = x := by
    funext i
    exact List.Vector.get_ofFn x i
  constructor
  · constructor
    · intro h
      exact h.comp Primrec.vector_get'.to_comp
    · intro h
      have h' : REPred (fun x => R (List.Vector.ofFn x).get) :=
        h.comp Primrec.vector_ofFn'.to_comp
      exact h'.of_eq (fun x => by rw [hx])
  · constructor
    · intro h
      exact Computable.computablePred (h.decide.comp Primrec.vector_get'.to_comp)
    · intro h
      exact (Computable.computablePred (h.decide.comp Primrec.vector_ofFn'.to_comp)).of_eq
        (fun x => by rw [hx])

theorem term_realize_primitive {α γ : Type} [Primcodable γ]
    (t : language.Term α) (v : γ → α → ℕ)
    (hv : ∀ i, Primrec (fun x => v x i)) : Primrec (fun x => t.realize (v x)) := by
  induction t with
  | var i => exact hv i
  | @func n f ts ih =>
    cases f with
    | zero => exact Primrec.const 0
    | succ => exact Primrec.succ.comp (ih 0)
    | add => exact Primrec.nat_add.comp (ih 0) (ih 1)
    | mul => exact Primrec.nat_mul.comp (ih 0) (ih 1)

private theorem bounded_forall_primitive {γ : Type} [Primcodable γ]
    (t : γ → ℕ) (ht : Primrec t) (P : γ → ℕ → Prop)
    (hP : PrimrecPred (fun p : γ × ℕ => P p.1 p.2)) :
    PrimrecPred (fun x => ∀ a ≤ t x, P x a) := by
  have hR : PrimrecRel (fun a x => P x a) := hP.comp (Primrec.snd.pair Primrec.fst)
  exact (hR.forall_mem_list.comp
    (Primrec.list_range.comp (Primrec.succ.comp ht)) Primrec.id).of_eq
      (fun x => by simp only [List.mem_range, Nat.lt_succ_iff, id_eq])

private theorem bounded_exists_primitive {γ : Type} [Primcodable γ]
    (t : γ → ℕ) (ht : Primrec t) (P : γ → ℕ → Prop)
    (hP : PrimrecPred (fun p : γ × ℕ => P p.1 p.2)) :
    PrimrecPred (fun x => ∃ a ≤ t x, P x a) := by
  have hR : PrimrecRel (fun a x => P x a) := hP.comp (Primrec.snd.pair Primrec.fst)
  exact (hR.exists_mem_list.comp
    (Primrec.list_range.comp (Primrec.succ.comp ht)) Primrec.id).of_eq
      (fun x => by simp only [List.mem_range, Nat.lt_succ_iff, id_eq])

theorem deltaZero_truth_primitive {α : Type} {A : language.Formula α}
    (hA : DeltaZero A) {γ : Type} [Primcodable γ]
    (v : γ → α → ℕ) (hv : ∀ i, Primrec (fun x => v x i)) :
    PrimrecPred (fun x => A.Realize (v x)) := by
  induction hA generalizing γ with
  | falsum =>
    classical
    exact ⟨inferInstance, by simpa using (Primrec.const false : Primrec (fun _ : γ => false))⟩
  | equal s t =>
    simpa only [Formula.realize_equal] using
      Primrec.eq.comp (term_realize_primitive s v hv) (term_realize_primitive t v hv)
  | le s t =>
    exact (Primrec.nat_le.comp (term_realize_primitive s v hv)
      (term_realize_primitive t v hv)).of_eq (fun _ => by
        simp only [realize_leFormula, leValue_nat])
  | imp _ _ ihA ihB =>
    exact ((ihA v hv).not.or (ihB v hv)).of_eq (fun _ => by simp only [Formula.realize_imp]; tauto)
  | @all α t φ _ ih =>
    have hb := ih (fun p : γ × ℕ => extend (v p.1) p.2) (by
      intro i
      cases i with
      | inl i => exact (hv i).comp Primrec.fst
      | inr i => exact Primrec.snd)
    exact (bounded_forall_primitive _ (term_realize_primitive t v hv) (fun x a => φ.Realize (extend (v x) a)) hb).of_eq
      (fun _ => by simp only [realize_boundedAll, leValue_nat])
  | @ex α t φ _ ih =>
    have hb := ih (fun p : γ × ℕ => extend (v p.1) p.2) (by
      intro i
      cases i with
      | inl i => exact (hv i).comp Primrec.fst
      | inr i => exact Primrec.snd)
    exact (bounded_exists_primitive _ (term_realize_primitive t v hv) (fun x a => φ.Realize (extend (v x) a)) hb).of_eq
      (fun _ => by simp only [realize_boundedEx, leValue_nat])

theorem bounded_truth_primitive {α : Type} {A : language.Formula α}
    (hA : BoundedArithmetic A) {γ : Type} [Primcodable γ]
    (v : γ → α → ℕ) (hv : ∀ i, Primrec (fun x => v x i)) :
    PrimrecPred (fun x => A.Realize (v x)) := by
  induction hA generalizing γ with
  | core h => exact deltaZero_truth_primitive h v hv
  | imp _ _ ihA ihB =>
    exact ((ihA v hv).not.or (ihB v hv)).of_eq (fun _ => by simp only [Formula.realize_imp]; tauto)
  | @all α t φ _ ih =>
    have hb := ih (fun p : γ × ℕ => extend (v p.1) p.2) (by
      intro i
      cases i with
      | inl i => exact (hv i).comp Primrec.fst
      | inr i => exact Primrec.snd)
    exact (bounded_forall_primitive _ (term_realize_primitive t v hv) (fun x a => φ.Realize (extend (v x) a)) hb).of_eq
      (fun _ => by simp only [realize_boundedAll, leValue_nat])
  | @ex α t φ _ ih =>
    have hb := ih (fun p : γ × ℕ => extend (v p.1) p.2) (by
      intro i
      cases i with
      | inl i => exact (hv i).comp Primrec.fst
      | inr i => exact Primrec.snd)
    exact (bounded_exists_primitive _ (term_realize_primitive t v hv) (fun x a => φ.Realize (extend (v x) a)) hb).of_eq
      (fun _ => by simp only [realize_boundedEx, leValue_nat])
  | @strictAll α t φ _ ih =>
    have hb := ih (fun p : γ × ℕ => extend (v p.1) p.2) (by
      intro i
      cases i with
      | inl i => exact (hv i).comp Primrec.fst
      | inr i => exact Primrec.snd)
    have hR : PrimrecRel (fun a x => φ.Realize (extend (v x) a)) :=
      hb.comp (Primrec.snd.pair Primrec.fst)
    exact (hR.forall_mem_list.comp
      (Primrec.list_range.comp (term_realize_primitive t v hv)) Primrec.id).of_eq
      (fun _ => by simp only [List.mem_range, realize_strictAll, leValue_nat, id_eq]; rfl)
  | @strictEx α t φ _ ih =>
    have hb := ih (fun p : γ × ℕ => extend (v p.1) p.2) (by
      intro i
      cases i with
      | inl i => exact (hv i).comp Primrec.fst
      | inr i => exact Primrec.snd)
    have hR : PrimrecRel (fun a x => φ.Realize (extend (v x) a)) :=
      hb.comp (Primrec.snd.pair Primrec.fst)
    exact (hR.exists_mem_list.comp
      (Primrec.list_range.comp (term_realize_primitive t v hv)) Primrec.id).of_eq
      (fun _ => by simp only [List.mem_range, realize_strictEx, leValue_nat, id_eq]; rfl)

theorem sigmaOne_subst {α β : Type} {A : language.Formula α}
    (hA : BoundedSigmaOne A) (σ : α → language.Term β) :
    BoundedSigmaOne (A.subst σ) := by
  obtain ⟨k, D, hD, rfl⟩ := hA
  exact ⟨k, D.subst (underSubst σ), hD.subst _, subst_iExs D σ⟩

/-- A finite witness type is reindexed to the literal natural-number prefix. -/
theorem sigmaOne_of_matrix {α β : Type} [Fintype β]
    (D : language.Formula (α ⊕ β)) (hD : BoundedArithmetic D) :
    SigmaOneDefinable (fun x => ∃ w : β → ℕ, D.Realize (Sum.elim x w)) := by
  let e := Fintype.equivFin β
  let E := D.relabel (Sum.map id e)
  refine ⟨E.iExs (Fin (Fintype.card β)), ⟨_, E, hD.relabel _, rfl⟩, ?_⟩
  intro x
  simp only [Formula.realize_iExs, E, Formula.realize_relabel]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun j => w (e j), ?_⟩
    convert hw using 1
    funext i
    cases i <;> rfl
  · rintro ⟨w, hw⟩
    refine ⟨fun j => w (e.symm j), ?_⟩
    convert hw using 1
    funext i
    cases i <;> simp [e]

theorem sigmaOne_project {α β : Type} [Fintype β]
    {R : ((α ⊕ β) → ℕ) → Prop} (hR : SigmaOneDefinable R) :
    SigmaOneDefinable (fun x => ∃ w : β → ℕ, R (Sum.elim x w)) := by
  obtain ⟨A, ⟨k, D, hD, rfl⟩, hA⟩ := hR
  let e : (α ⊕ β) ⊕ Fin k → α ⊕ (β ⊕ Fin k) :=
    Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
  have he := sigmaOne_of_matrix (D.relabel e) (hD.relabel e)
  obtain ⟨B, hB, hb⟩ := he
  refine ⟨B, hB, fun x => (hb x).trans ?_⟩
  simp only [Formula.realize_relabel]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun j => w (.inl j), (hA _).mp ?_⟩
    apply Formula.realize_iExs.mpr
    refine ⟨fun j => w (.inr j), ?_⟩
    convert hw using 1
    funext i
    cases i with
    | inl i => cases i <;> rfl
    | inr i => rfl
  · rintro ⟨w, hw⟩
    obtain ⟨z, hz⟩ := Formula.realize_iExs.mp ((hA _).mpr hw)
    refine ⟨Sum.elim w z, ?_⟩
    convert hz using 1
    funext i
    cases i with
    | inl i => cases i <;> rfl
    | inr i => rfl

theorem primitive_relation_sigmaOne {n : ℕ} (R : (Fin n → ℕ) → Prop)
    (hR : PrimrecPred R) : SigmaOneDefinable R := by
  classical
  let f : List.Vector ℕ n → ℕ := fun v => if R v.get then 1 else 0
  have hf : Primrec f := by
    have hc := (hR.decide.comp Primrec.vector_get').cond
      (Primrec.const (1 : ℕ)) (Primrec.const 0)
    exact hc.of_eq (fun _ => by simp only [f, Bool.cond_decide])
  obtain ⟨p, hp⟩ := program_of_primrec f (Nat.Primrec'.prim_iff.mpr hf)
  have hs : BoundedSigmaOne p.sigmaGraph := by
    obtain ⟨k, D, hD, he⟩ := p.sigmaGraph_isSigmaOne
    exact ⟨k, D, .core hD, he⟩
  let σ : Fin n ⊕ Unit → language.Term (Fin n) :=
    Sum.elim Term.var (fun _ => numeralTerm 1)
  refine ⟨p.sigmaGraph.subst σ, sigmaOne_subst hs σ, ?_⟩
  intro x
  have hr : Formula.Realize (p.sigmaGraph.subst σ) x ↔
      p.sigmaGraph.Realize (extend x 1) := by
    simp only [Formula.Realize, BoundedFormula.realize_subst]
    have he : (fun i => (σ i).realize x) = extend x 1 := by
      funext i
      cases i <;> rfl
    rw [he]
  rw [hr, p.uniform_sigmaOne.2.1, hp]
  have hxv : (List.Vector.ofFn x).get = x := by
    funext i
    exact List.Vector.get_ofFn x i
  simp only [f, hxv]
  by_cases hx : R x <;> simp [hx]

theorem primitive_function_graph {n : ℕ} (f : (Fin n → ℕ) → ℕ)
    (hf : Primrec f) :
    ∃ G : language.Formula (Fin n ⊕ Unit), BoundedSigmaOne G ∧
      ∀ x y, G.Realize (extend x y) ↔ f x = y := by
  obtain ⟨p, hp⟩ := program_of_primrec
    (fun v : List.Vector ℕ n => f v.get)
    (Nat.Primrec'.prim_iff.mpr (hf.comp Primrec.vector_get'))
  refine ⟨p.sigmaGraph, ?_, ?_⟩
  · obtain ⟨k, D, hD, he⟩ := p.sigmaGraph_isSigmaOne
    exact ⟨k, D, .core hD, he⟩
  · intro x y
    rw [p.uniform_sigmaOne.2.1, hp]
    have hx : (List.Vector.ofFn x).get = x := by
      funext i
      exact List.Vector.get_ofFn x i
    change y = f (List.Vector.ofFn x).get ↔ f x = y
    rw [hx]
    exact eq_comm

theorem sigmaOne_relabel {α β : Type} {R : (α → ℕ) → Prop}
    (hR : SigmaOneDefinable R) (f : α → β) :
    SigmaOneDefinable (fun x => R (x ∘ f)) := by
  obtain ⟨A, hA, ha⟩ := hR
  refine ⟨A.relabel f, ?_, ?_⟩
  · simpa only [formula_subst_vars] using sigmaOne_subst hA (fun i => Term.var (f i))
  · intro x
    rw [Formula.realize_relabel]
    exact ha (x ∘ f)

private def tupleDecode (n t : ℕ) : Fin n → ℕ :=
  (Encodable.decode (α := Fin n → ℕ) t).getD (fun _ => 0)

private theorem tupleDecode_primitive (n : ℕ) : Primrec (tupleDecode n) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (fun _ => 0))

private theorem tupleDecode_encode {n : ℕ} (x : Fin n → ℕ) :
    tupleDecode n (Encodable.encode x) = x := by
  simp [tupleDecode]

private theorem exists_primitive_re {γ : Type} [Primcodable γ]
    {R : γ → ℕ → Prop} (hR : PrimrecPred (fun p : γ × ℕ => R p.1 p.2)) :
    REPred (fun x => ∃ t, R x t) := by
  classical
  have hs : Partrec (fun x => Nat.rfind (fun t => Part.some (decide (R x t)))) :=
    Partrec.rfind (show Computable₂ (fun x t => decide (R x t)) from hR.decide.to_comp).partrec₂
  apply hs.dom_re.of_eq
  intro x
  constructor
  · intro hd
    obtain ⟨n, hn, _⟩ := Nat.rfind_dom.mp hd
    exact ⟨n, by simpa using hn⟩
  · rintro ⟨n, hn⟩
    exact Nat.rfind_dom.mpr ⟨n, by simpa using hn, fun _ => trivial⟩

theorem finite_arity_certificate {n : ℕ} {R : (Fin n → ℕ) → Prop}
    (hR : REPred R) :
    ∃ C : (Fin n → ℕ) → ℕ → Prop,
      PrimrecPred (fun p : (Fin n → ℕ) × ℕ => C p.1 p.2) ∧
      ∀ x, R x ↔ ∃ t, C x t := by
  have hc : REPred (fun t => R (tupleDecode n t)) :=
    hR.comp (tupleDecode_primitive n).to_comp
  obtain ⟨C, hC, hc⟩ :=
    (UniversalComputation.enumerable_iff_primitive_certificate _).mp hc
  refine ⟨fun x t => C (Encodable.encode x) t,
    hC.comp ((Primrec.encode.comp Primrec.fst).pair Primrec.snd), ?_⟩
  intro x
  simpa only [tupleDecode_encode] using hc (Encodable.encode x)

theorem enumerable_iff_sigmaOne {n : ℕ} (R : (Fin n → ℕ) → Prop) :
    REPred R ↔ SigmaOneDefinable R := by
  classical
  constructor
  · intro hR
    have hc : REPred (fun t => R (tupleDecode n t)) :=
      hR.comp (tupleDecode_primitive n).to_comp
    obtain ⟨C, hC, hc⟩ :=
      (UniversalComputation.enumerable_iff_primitive_certificate _).mp hc
    let P : (Fin (n + 1) → ℕ) → Prop := fun z =>
      C (Encodable.encode (Fin.init z)) (z (Fin.last n))
    have hi : Primrec (fun z : Fin (n + 1) → ℕ => Fin.init z) :=
      (Primrec.vector_get'.comp (Primrec.vector_ofFn (fun i : Fin n =>
        Primrec.fin_app.comp Primrec.id (Primrec.const i.castSucc)))).of_eq
        (fun z => by
          funext i
          exact List.Vector.get_ofFn (fun i => z i.castSucc) i)
    have hP : PrimrecPred P := by
      change PrimrecPred (fun z : Fin (n + 1) → ℕ =>
        C (Encodable.encode (Fin.init z)) (z (Fin.last n)))
      exact hC.comp ((Primrec.encode.comp hi).pair
        (Primrec.fin_app.comp Primrec.id (Primrec.const (Fin.last n))))
    obtain ⟨A, hA, ha⟩ := primitive_relation_sigmaOne P hP
    let e : Fin (n + 1) → Fin n ⊕ Unit :=
      Fin.lastCases (.inr ()) (fun i => .inl i)
    let B := A.relabel e
    have hB : BoundedSigmaOne B := by
      simpa only [formula_subst_vars] using sigmaOne_subst hA (fun i => Term.var (e i))
    have hb : SigmaOneDefinable (fun z : (Fin n ⊕ Unit) → ℕ =>
        C (Encodable.encode (fun i => z (.inl i))) (z (.inr ()))) := by
      refine ⟨B, hB, ?_⟩
      intro z
      change (A.relabel e).Realize z ↔ _
      rw [Formula.realize_relabel, ha]
      dsimp [P]
      have he : Fin.init (z ∘ e) = fun i => z (.inl i) := by
        funext i
        simp [e, Fin.init]
      rw [he]
      simp [e]
    obtain ⟨D, hD, hd⟩ := sigmaOne_project hb
    refine ⟨D, hD, fun x => (hd x).trans ?_⟩
    have hh := hc (Encodable.encode x)
    rw [tupleDecode_encode] at hh
    change (∃ w : Unit → ℕ, C (Encodable.encode x) (w ())) ↔ R x
    rw [hh]
    exact ⟨fun ⟨w, hw⟩ => ⟨w (), hw⟩, fun ⟨t, ht⟩ => ⟨fun _ => t, ht⟩⟩
  · rintro ⟨A, ⟨k, D, hD, rfl⟩, ha⟩
    let C (x : Fin n → ℕ) (t : ℕ) : Prop :=
      D.Realize (Sum.elim x (tupleDecode k t))
    have hC : PrimrecPred (fun p : (Fin n → ℕ) × ℕ => C p.1 p.2) := by
      apply bounded_truth_primitive hD
      intro i
      cases i with
      | inl i => exact Primrec.fin_app.comp Primrec.fst (Primrec.const i)
      | inr i =>
        exact Primrec.fin_app.comp
          ((tupleDecode_primitive k).comp Primrec.snd) (Primrec.const i)
    apply (exists_primitive_re hC).of_eq
    intro x
    rw [← ha x, Formula.realize_iExs]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨tupleDecode k t, ht⟩
    · rintro ⟨w, hw⟩
      exact ⟨Encodable.encode w, by simpa [C, tupleDecode_encode] using hw⟩

theorem piOne_iff_complement_sigmaOne {α : Type} (R : (α → ℕ) → Prop) :
    PiOneDefinable R ↔ SigmaOneDefinable (fun x => ¬R x) := by
  classical
  constructor
  · rintro ⟨A, ⟨k, D, hD, rfl⟩, ha⟩
    refine ⟨D.not.iExs (Fin k), ⟨k, D.not, .imp hD (.core .falsum), rfl⟩, ?_⟩
    intro x
    change (D.not.iExs (Fin k)).Realize x ↔ ¬R x
    rw [Formula.realize_iExs, ← ha x, Formula.realize_iAlls]
    simp only [Formula.realize_not, not_forall]
  · rintro ⟨A, ⟨k, D, hD, rfl⟩, ha⟩
    refine ⟨D.not.iAlls (Fin k), ⟨k, D.not, .imp hD (.core .falsum), rfl⟩, ?_⟩
    intro x
    have hh := ha x
    rw [Formula.realize_iExs] at hh
    simp only [Formula.realize_iAlls, Formula.realize_not]
    tauto

theorem coenumerable_iff_piOne {n : ℕ} (R : (Fin n → ℕ) → Prop) :
    REPred (fun x => ¬R x) ↔ PiOneDefinable R := by
  rw [piOne_iff_complement_sigmaOne, ← enumerable_iff_sigmaOne]

theorem decidable_iff_deltaOne {n : ℕ} (R : (Fin n → ℕ) → Prop) :
    ComputablePred R ↔ DeltaOneDefinable R := by
  rw [ComputablePred.computable_iff_re_compl_re', DeltaOneDefinable,
    enumerable_iff_sigmaOne, coenumerable_iff_piOne]

/-- Fixed numerical parameters are removed by actual numeral substitution. -/
theorem numerical_parameters {α β : Type} (A : language.Formula (α ⊕ β))
    (p : β → ℕ) :
    ∃ B : language.Formula α,
      Defines (fun x => A.Realize (Sum.elim x p)) B ∧
      (BoundedSigmaOne A → BoundedSigmaOne B) := by
  let σ : α ⊕ β → language.Term α :=
    Sum.elim Term.var (fun i => numeralTerm (p i))
  refine ⟨A.subst σ, ?_, fun h => sigmaOne_subst h σ⟩
  intro x
  simp only [Formula.Realize, BoundedFormula.realize_subst]
  have he : (fun i => (σ i).realize x) = Sum.elim x p := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (realize_numeralTerm x (p i)).trans (numeral_value_nat (p i))
  rw [he]

private theorem constantTuple_primitive (n : ℕ) :
    Primrec (fun x : ℕ => (fun _ : Fin n => x)) :=
  (Primrec.vector_get'.comp (Primrec.vector_ofFn (fun _ => Primrec.id))).of_eq
    (fun x => by funext i; exact List.Vector.get_ofFn (fun _ => x) i)

theorem unary_enumerable_iff (A : ℕ → Prop) :
    REPred A ↔ SigmaOneDefinable (fun v : Fin 1 → ℕ => A (v 0)) := by
  rw [← enumerable_iff_sigmaOne]
  constructor
  · intro h
    exact h.comp (Primrec.fin_app.comp Primrec.id (Primrec.const 0)).to_comp
  · intro h
    exact h.comp (constantTuple_primitive 1).to_comp

theorem halting_separation :
    let K := fun v : Fin 1 → ℕ => v 0 ∈ UniversalComputation.haltingDiagonal
    SigmaOneDefinable K ∧ ¬PiOneDefinable K ∧
      PiOneDefinable (fun v => ¬K v) ∧ ¬SigmaOneDefinable (fun v => ¬K v) := by
  classical
  dsimp only
  let K := fun v : Fin 1 → ℕ => v 0 ∈ UniversalComputation.haltingDiagonal
  have hs : SigmaOneDefinable K :=
    (unary_enumerable_iff _).mp UniversalComputation.haltingDiagonal_enumerable
  have hn : ¬PiOneDefinable K := by
    intro hp
    have hd := (decidable_iff_deltaOne K).mpr ⟨hs, hp⟩
    have hu : ComputablePred (fun e => e ∈ UniversalComputation.haltingDiagonal) :=
      Computable.computablePred (hd.decide.comp (constantTuple_primitive 1).to_comp)
    exact UniversalComputation.haltingDiagonal_undecidable hu
  refine ⟨hs, hn, ?_, ?_⟩
  · apply (piOne_iff_complement_sigmaOne _).mpr
    obtain ⟨A, hA, ha⟩ := hs
    exact ⟨A, hA, fun x => (ha x).trans (by simp [K])⟩
  · intro h
    exact hn ((piOne_iff_complement_sigmaOne K).mpr h)

/-- The graph contains just the successful input-output pairs. -/
def Graph (f : ℕ → Part ℕ) (v : Fin 2 → ℕ) : Prop := v 1 ∈ f (v 0)

theorem partial_recursive_iff_graph_enumerable (f : ℕ → Part ℕ) :
    Nat.Partrec f ↔ REPred (Graph f) := by
  classical
  constructor
  · intro hf
    obtain ⟨e, he⟩ := UniversalComputation.phi_complete hf
    let C (v : Fin 2 → ℕ) (t : ℕ) : Prop :=
      UniversalComputation.boundedValue t e (v 0) = v 1 + 1
    have hC : PrimrecPred (fun p : (Fin 2 → ℕ) × ℕ => C p.1 p.2) :=
      Primrec.eq.comp
        (UniversalComputation.boundedValue_primitive.comp
          ((Primrec.snd.pair (Primrec.const e)).pair
            (Primrec.fin_app.comp Primrec.fst (Primrec.const 0))))
        (Primrec.succ.comp (Primrec.fin_app.comp Primrec.fst (Primrec.const 1)))
    apply (exists_primitive_re hC).of_eq
    intro v
    exact (UniversalComputation.phi_output e (v 0) (v 1)).symm.trans (by rw [he]; rfl)
  · intro hG
    obtain ⟨C, hC, hc⟩ := finite_arity_certificate hG
    let P (x w : ℕ) : Prop := C ![x, w.unpair.1] w.unpair.2
    have hv : Primrec (fun p : ℕ × ℕ => (![p.1, p.2.unpair.1] : Fin 2 → ℕ)) := by
      apply Primrec.vector_get'.comp
        (Primrec.vector_ofFn (fun i => ?_)) |>.of_eq
          (fun p => by funext i; exact List.Vector.get_ofFn (![p.1, p.2.unpair.1]) i)
      fin_cases i
      · exact Primrec.fst
      · exact Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
    have hP : PrimrecPred (fun p : ℕ × ℕ => P p.1 p.2) :=
      hC.comp (hv.pair (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
    let search (x : ℕ) := Nat.rfind (fun w => Part.some (decide (P x w)))
    have hs : Partrec search :=
      Partrec.rfind (show Computable₂ (fun x w => decide (P x w)) from hP.decide.to_comp).partrec₂
    have hout : Partrec (fun x => (search x).map (fun w => w.unpair.1)) :=
      hs.map (Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp Computable.snd)).to₂
    apply Partrec.nat_iff.mp
    apply hout.of_eq
    intro x
    apply Part.ext
    intro y
    rw [Part.mem_map_iff]
    constructor
    · rintro ⟨w, hw, hy⟩
      have hp : P x w := by simpa [search] using Nat.rfind_spec hw
      have hg := (hc ![x, w.unpair.1]).mpr ⟨w.unpair.2, hp⟩
      simpa only [Graph, Matrix.cons_val_zero, Matrix.cons_val_one, hy] using hg
    · intro hy
      have hg : Graph f ![x, y] := by simpa [Graph] using hy
      obtain ⟨t, ht⟩ := (hc ![x, y]).mp hg
      have hd : (search x).Dom := Nat.rfind_dom.mpr
        ⟨Nat.pair y t, by simpa [P] using ht, fun _ => trivial⟩
      obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp hd
      have hp : P x w := by simpa [search] using Nat.rfind_spec hw
      have hg := (hc ![x, w.unpair.1]).mpr ⟨w.unpair.2, hp⟩
      have hmem : w.unpair.1 ∈ f x := by simpa [Graph] using hg
      exact ⟨w, hw, Part.mem_unique hmem hy⟩

theorem partial_recursive_iff_graph_sigmaOne (f : ℕ → Part ℕ) :
    Nat.Partrec f ↔ SigmaOneDefinable (Graph f) := by
  rw [partial_recursive_iff_graph_enumerable, enumerable_iff_sigmaOne]

theorem partial_recursive_domain_sigmaOne {f : ℕ → Part ℕ} (hf : Nat.Partrec f) :
    SigmaOneDefinable (fun v : Fin 1 → ℕ => (f (v 0)).Dom) := by
  have hg := (partial_recursive_iff_graph_sigmaOne f).mp hf
  let e : Fin 2 → Fin 1 ⊕ Unit := ![.inl 0, .inr ()]
  obtain ⟨A, hA, ha⟩ := sigmaOne_project (sigmaOne_relabel hg e)
  refine ⟨A, hA, fun x => (ha x).trans ?_⟩
  change (∃ w : Unit → ℕ, w () ∈ f (x 0)) ↔ (f (x 0)).Dom
  exact ⟨fun ⟨w, hw⟩ => hw.1, fun h => ⟨fun _ => (f (x 0)).get h, h, rfl⟩⟩

/-- Literal alternating prefixes, with bounded level zero and finite blocks. -/
def Prefix : (r : ℕ) → Bool → {α : Type} → language.Formula α → Prop
  | 0, _, _, A => BoundedArithmetic A
  | r + 1, true, α, A => ∃ k : ℕ, ∃ D : language.Formula (α ⊕ Fin k),
      Prefix r false D ∧ A = D.iExs (Fin k)
  | r + 1, false, α, A => ∃ k : ℕ, ∃ D : language.Formula (α ⊕ Fin k),
      Prefix r true D ∧ A = D.iAlls (Fin k)

def PrefixDefinable {α : Type} (r : ℕ) (existential : Bool)
    (R : (α → ℕ) → Prop) : Prop :=
  ∃ A : language.Formula α, Prefix r existential A ∧ Defines R A

theorem universal_graph_sigmaOne :
    SigmaOneDefinable (fun v : Fin 3 → ℕ => v 2 ∈ UniversalComputation.phi (v 0) (v 1)) := by
  rw [← enumerable_iff_sigmaOne]
  let C (v : Fin 3 → ℕ) (t : ℕ) : Prop :=
    UniversalComputation.boundedValue t (v 0) (v 1) = v 2 + 1
  have hC : PrimrecPred (fun p : (Fin 3 → ℕ) × ℕ => C p.1 p.2) :=
    Primrec.eq.comp
      (UniversalComputation.boundedValue_primitive.comp
        ((Primrec.snd.pair (Primrec.fin_app.comp Primrec.fst (Primrec.const 0))).pair
          (Primrec.fin_app.comp Primrec.fst (Primrec.const 1))))
      (Primrec.succ.comp (Primrec.fin_app.comp Primrec.fst (Primrec.const 2)))
  exact (exists_primitive_re hC).of_eq (fun v =>
    (UniversalComputation.phi_output (v 0) (v 1) (v 2)).symm)

theorem total_programs_piTwo :
    PrefixDefinable 2 false (fun v : Unit → ℕ =>
      ∀ x, (UniversalComputation.phi (v ()) x).Dom) := by
  let e : Fin 3 → (Unit ⊕ Fin 1) ⊕ Unit :=
    ![.inl (.inl ()), .inl (.inr 0), .inr ()]
  obtain ⟨A, hA, ha⟩ := sigmaOne_project (sigmaOne_relabel universal_graph_sigmaOne e)
  refine ⟨A.iAlls (Fin 1), ⟨1, A, ?_, rfl⟩, ?_⟩
  · exact hA
  · intro v
    rw [Formula.realize_iAlls]
    constructor
    · intro h x
      have hh := (ha (Sum.elim v (fun _ => x))).mp (h (fun _ => x))
      obtain ⟨w, hw⟩ := hh
      exact hw.1
    · intro h x
      apply (ha (Sum.elim v x)).mpr
      have hd := h (x 0)
      refine ⟨fun _ => (UniversalComputation.phi (v ()) (x 0)).get hd, ?_⟩
      change (UniversalComputation.phi (v ()) (x 0)).get hd ∈ _
      exact ⟨hd, rfl⟩

end
end Lemmatheca.MathematicalLogic.ArithmeticDefinability
