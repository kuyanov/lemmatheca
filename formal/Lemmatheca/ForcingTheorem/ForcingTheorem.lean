import Lemmatheca.ForcingNames.CohenName

namespace Lemmatheca.SetTheory.ForcingTheorem
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
universe u v

inductive Aux : ℕ → Type
  | mem {n} (i j : Fin n) : Aux n
  | neq {n} (i j : Fin n) : Aux n
  | neg {n} (p : Aux n) : Aux n
  | disj {n} (p q : Aux n) : Aux n
  | ex {n} (p : Aux (n+1)) : Aux n

def Aux.Holds {D : Type u} (E : D → D → Prop) :
    {n : ℕ} → Aux n → (Fin n → D) → Prop
  | _, .mem i j, a => E (a i) (a j)
  | _, .neq i j, a => a i ≠ a j
  | _, .neg p, a => ¬p.Holds E a
  | _, .disj p q, a => p.Holds E a ∨ q.Holds E a
  | _, .ex p, a => ∃ x : D, p.Holds E (Fin.snoc a x)

def termSlot {n} : membershipLanguage.Term (Empty ⊕ Fin n) → Fin n
  | .var (.inl e) => Empty.elim e
  | .var (.inr i) => i
  | .func f _ => Empty.elim f

def translate : {n : ℕ} → membershipLanguage.BoundedFormula Empty n → Aux n
  | n, .falsum => .ex (.neq (Fin.last n) (Fin.last n))
  | _, .equal t s => .neg (.neq (termSlot t) (termSlot s))
  | _, .rel r ts => by
    cases r
    exact .mem (termSlot (ts 0)) (termSlot (ts 1))
  | _, .imp p q => .disj (.neg (translate p)) (translate q)
  | _, .all p => .neg (.ex (.neg (translate p)))

theorem termSlot_realize {D : Type u} [membershipLanguage.Structure D] {n}
    (t : membershipLanguage.Term (Empty ⊕ Fin n)) (a : Fin n → D) :
    t.realize (Sum.elim Empty.elim a) = a (termSlot t) := by
  cases t with
  | var i => cases i with
    | inl i => exact Empty.elim i
    | inr i => rfl
  | func f ts => exact Empty.elim f

theorem translate_realize {D : Type u} (E : D → D → Prop) {n}
    (φ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → D) :
    letI := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure D E
    φ.Realize Empty.elim a ↔ (translate φ).Holds E a := by
  classical
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure D E
  induction φ with
  | falsum =>
    simp [translate,Aux.Holds,BoundedFormula.Realize]
  | equal t s =>
    change t.realize (Sum.elim Empty.elim a) = s.realize (Sum.elim Empty.elim a) ↔
      ¬(a (termSlot t) ≠ a (termSlot s))
    rw [not_ne_iff,termSlot_realize,termSlot_realize]
  | rel r ts =>
    cases r
    change E ((ts 0).realize (Sum.elim Empty.elim a)) ((ts 1).realize (Sum.elim Empty.elim a)) ↔ _
    rw [termSlot_realize,termSlot_realize]
    rfl
  | imp φ ψ ihφ ihψ =>
    simp only [translate,Aux.Holds,BoundedFormula.realize_imp,ihφ,ihψ,imp_iff_not_or]
  | all φ ih =>
    simp only [translate,Aux.Holds,BoundedFormula.realize_all,not_exists,not_not,ih]

theorem translate_setSatisfies (D : ZFSet.{u}) {n}
    (φ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → D) :
    setSatisfies D φ a ↔ (translate φ).Holds (fun x y : D => x.val ∈ y.val) a := by
  exact translate_realize (fun x y : D => x.val ∈ y.val) φ a

open Set Order
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open scoped ZFSet
noncomputable section
attribute [local instance] Classical.propDecidable

structure Context (Q : Type v) [PartialOrder Q] where
  conditions : ZFSet.{u}
  ground : ZFSet.{u}
  relation : ZFSet.{u}
  code : Q ≃ conditions
  transitive : ground.IsTransitive
  conditions_mem : conditions ∈ ground
  relation_mem : relation ∈ ground
  order_correct : ∀ q p, ZFSet.pair (code q).val (code p).val ∈ relation ↔ q ≤ p

variable {Q : Type v} [PartialOrder Q]

abbrev Context.Name (C : Context.{u,v} Q) :=
  {τ : ZFSet.{u} // τ ∈ C.ground ∧ IsName C.conditions τ}

def Context.filterCode (C : Context.{u,v} Q) (G : PFilter Q) : ZFSet.{u} :=
  filterSet C.conditions C.code G

def Context.valueDomain (C : Context.{u,v} Q) (G : PFilter Q) : ZFSet.{u} :=
  extension C.conditions C.ground (C.filterCode G)

def Context.value (C : Context.{u,v} Q) (G : PFilter Q) (σ : C.Name) : C.valueDomain G :=
  ⟨evaluation (C.filterCode G) σ.val,
    (extension_mem _ _ _ _).mpr ⟨σ.val,σ.property.1,σ.property.2,rfl⟩⟩

def Context.valueAssignment (C : Context.{u,v} Q) (G : PFilter Q) {n}
    (a : Fin n → C.Name) : Fin n → C.valueDomain G := fun i => C.value G (a i)

def Context.groundFamily (C : Context.{u,v} Q) : Set (Set Q) :=
  {D | ∃ d ∈ C.ground, d ⊆ C.conditions ∧ D = {q | (C.code q).val ∈ d}}

def Context.subsetCode (C : Context.{u,v} Q) (D : Set Q) : ZFSet.{u} :=
  C.conditions.sep (fun x => ∃ q ∈ D, (C.code q).val = x)

theorem subsetCode_members (C : Context.{u,v} Q) (D : Set Q) (q : Q) :
    (C.code q).val ∈ C.subsetCode D ↔ q ∈ D := by
  rw [Context.subsetCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,r,hr,he⟩
    have heq : r = q := C.code.injective (Subtype.ext he)
    exact heq ▸ hr
  · intro hq
    exact ⟨(C.code q).property,q,hq,rfl⟩

theorem groundFamily_iff (C : Context.{u,v} Q) (D : Set Q) :
    D ∈ C.groundFamily ↔ C.subsetCode D ∈ C.ground := by
  constructor
  · rintro ⟨d,hd,hsub,rfl⟩
    have he : C.subsetCode {q | (C.code q).val ∈ d} = d := by
      ext x
      rw [Context.subsetCode,ZFSet.mem_sep]
      constructor
      · rintro ⟨_,q,hq,rfl⟩
        exact hq
      · intro hx
        let q := C.code.symm ⟨x,hsub hx⟩
        have hq : (C.code q).val = x := congrArg Subtype.val (C.code.apply_symm_apply _)
        refine ⟨hsub hx,q,?_,hq⟩
        change (C.code q).val ∈ d
        rw [hq]; exact hx
    exact he.symm ▸ hd
  · intro hD
    refine ⟨C.subsetCode D,hD,ZFSet.sep_subset,?_⟩
    ext q
    exact (subsetCode_members C D q).symm

theorem groundFamily_countable (C : Context.{u,v} Q)
    (hM : (C.ground : Set ZFSet.{u}).Countable) : C.groundFamily.Countable := by
  apply (hM.image (fun d => {q | (C.code q).val ∈ d})).mono
  rintro D ⟨d,hd,_,rfl⟩
  exact ⟨d,hd,rfl⟩

theorem conditions_countable (C : Context.{u,v} Q)
    (hM : (C.ground : Set ZFSet.{u}).Countable) : Countable Q := by
  have hp : (C.conditions : Set ZFSet.{u}).Countable :=
    hM.mono (fun x hx => C.transitive _ C.conditions_mem hx)
  have : Countable C.conditions := hp.to_subtype
  exact C.code.injective.countable

theorem generic_through_condition (C : Context.{u,v} Q)
    (hM : (C.ground : Set ZFSet.{u}).Countable) (p : Q) :
    ∃ G : PFilter Q, GenericFor G C.groundFamily ∧ p ∈ G := by
  have : Countable Q := conditions_countable C hM
  obtain ⟨G,hp,hG⟩ := generic_through_countable_family C.groundFamily (groundFamily_countable C hM) p
  exact ⟨G,hG,hp⟩

def Context.auxTruth (C : Context.{u,v} Q) (G : PFilter Q) {n}
    (A : Aux n) (a : Fin n → C.Name) : Prop :=
  A.Holds (fun x y : C.valueDomain G => x.val ∈ y.val) (C.valueAssignment G a)

def Context.semanticAux (C : Context.{u,v} Q) {n}
    (A : Aux n) (a : Fin n → C.Name) (p : Q) : Prop :=
  ∀ G : PFilter Q, GenericFor G C.groundFamily → p ∈ G → C.auxTruth G A a

def Context.semanticForce (C : Context.{u,v} Q) {n}
    (φ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → C.Name) (p : Q) : Prop :=
  ∀ G : PFilter Q, GenericFor G C.groundFamily → p ∈ G →
    setSatisfies (C.valueDomain G) φ (C.valueAssignment G a)

theorem semantic_monotone (C : Context.{u,v} Q) {n}
    (φ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → C.Name)
    {p q : Q} (hqp : q ≤ p) (hp : C.semanticForce φ a p) :
    C.semanticForce φ a q := by
  intro G hG hq
  exact hp G hG (PFilter.mem_of_le hqp hq)

theorem semantic_translation (C : Context.{u,v} Q) {n}
    (φ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → C.Name) (p : Q) :
    C.semanticForce φ a p ↔ C.semanticAux (translate φ) a p := by
  constructor
  · intro h G hG hp
    exact (translate_setSatisfies _ φ _).mp (h G hG hp)
  · intro h G hG hp
    exact (translate_setSatisfies _ φ _).mpr (h G hG hp)

def Attached (C : Context.{u,v} Q) (σ τ : C.Name) (p : Q) : Prop :=
  ZFSet.pair σ.val (C.code p).val ∈ τ.val

def rankKey (C : Context.{u,v} Q) (st : C.Name × C.Name) : Ordinal.{u} × Ordinal.{u} :=
  (min (nameRank st.1.val) (nameRank st.2.val),
   max (nameRank st.1.val) (nameRank st.2.val))

def PairEarlier (C : Context.{u,v} Q) (st uv : C.Name × C.Name) : Prop :=
  Prod.Lex (· < ·) (· < ·) (rankKey C st) (rankKey C uv)

private theorem sorted_rank_decrease {a b c : Ordinal.{u}} (hac : a < c) :
    Prod.Lex (· < ·) (· < ·) (min a b,max a b) (min c b,max c b) := by
  rw [Prod.lex_iff]
  by_cases hcb : c ≤ b
  · exact Or.inl (by simpa only [min_eq_left (hac.le.trans hcb),min_eq_left hcb] using hac)
  · have hbc : b < c := lt_of_not_ge hcb
    by_cases hab : a < b
    · exact Or.inl (by simpa only [min_eq_left hab.le,min_eq_right hbc.le] using hab)
    · have hba : b ≤ a := le_of_not_gt hab
      exact Or.inr ⟨by simp only [min_eq_right hba,min_eq_right hbc.le],
        by simpa only [max_eq_left hba,max_eq_left hbc.le] using hac⟩

theorem pairEarlier_wellFounded (C : Context.{u,v} Q) : WellFounded (PairEarlier C) := by
  exact InvImage.wf (rankKey C) (Ordinal.lt_wf.prod_lex Ordinal.lt_wf)

theorem child_left_earlier (C : Context.{u,v} Q) (θ σ τ : C.Name) (q : Q)
    (h : Attached C θ σ q) : PairEarlier C (θ,τ) (σ,τ) := by
  exact sorted_rank_decrease (nameRank_child ⟨(C.code q).val,h⟩)

theorem child_right_earlier (C : Context.{u,v} Q) (θ σ τ : C.Name) (q : Q)
    (h : Attached C θ τ q) : PairEarlier C (θ,σ) (σ,τ) := by
  have he := sorted_rank_decrease (b := nameRank σ.val) (nameRank_child ⟨(C.code q).val,h⟩)
  simpa only [PairEarlier,rankKey,min_comm,max_comm] using he

inductive AtomKind | mem | neq

def atomicStep (C : Context.{u,v} Q) (st : C.Name × C.Name)
    (rec : (uv : C.Name × C.Name) → PairEarlier C uv st → Q → AtomKind → Prop)
    (p : Q) : AtomKind → Prop
  | .mem => ∃ θ q, ∃ h : Attached C θ st.2 q,
      p ≤ q ∧ ∀ r ≤ p, ¬rec (θ,st.1) (child_right_earlier C θ st.1 st.2 q h) r .neq
  | .neq =>
      (∃ θ q, ∃ h : Attached C θ st.1 q,
        p ≤ q ∧ ∀ r ≤ p, ¬rec (θ,st.2) (child_left_earlier C θ st.1 st.2 q h) r .mem) ∨
      (∃ θ q, ∃ h : Attached C θ st.2 q,
        p ≤ q ∧ ∀ r ≤ p, ¬rec (θ,st.1) (child_right_earlier C θ st.1 st.2 q h) r .mem)

def atomicPositive (C : Context.{u,v} Q) : C.Name × C.Name → Q → AtomKind → Prop :=
  (pairEarlier_wellFounded C).fix (atomicStep C)

def atomicNegative (C : Context.{u,v} Q) (st : C.Name × C.Name) (p : Q) (k : AtomKind) : Prop :=
  ∀ q ≤ p, ¬atomicPositive C st q k

theorem atomic_mem_clause (C : Context.{u,v} Q) (σ τ : C.Name) (p : Q) :
    atomicPositive C (σ,τ) p .mem ↔
      ∃ θ q, Attached C θ τ q ∧ p ≤ q ∧ atomicNegative C (θ,σ) p .neq := by
  rw [atomicPositive,WellFounded.fix_eq]
  change (∃ θ q, ∃ h : Attached C θ τ q, p ≤ q ∧ atomicNegative C (θ,σ) p .neq) ↔ _
  constructor
  · rintro ⟨θ,q,h,hpq,hn⟩
    exact ⟨θ,q,h,hpq,hn⟩
  · rintro ⟨θ,q,h,hpq,hn⟩
    exact ⟨θ,q,h,hpq,hn⟩

theorem atomic_neq_clause (C : Context.{u,v} Q) (σ τ : C.Name) (p : Q) :
    atomicPositive C (σ,τ) p .neq ↔
      (∃ θ q, Attached C θ σ q ∧ p ≤ q ∧ atomicNegative C (θ,τ) p .mem) ∨
      (∃ θ q, Attached C θ τ q ∧ p ≤ q ∧ atomicNegative C (θ,σ) p .mem) := by
  rw [atomicPositive,WellFounded.fix_eq]
  change ((∃ θ q, ∃ h : Attached C θ σ q, p ≤ q ∧ atomicNegative C (θ,τ) p .mem) ∨
    (∃ θ q, ∃ h : Attached C θ τ q, p ≤ q ∧ atomicNegative C (θ,σ) p .mem)) ↔ _
  simp only [exists_prop]

theorem atomic_unique (C : Context.{u,v} Q) (F : C.Name × C.Name → Q → AtomKind → Prop)
    (hF : ∀ st, F st = atomicStep C st (fun uv _ => F uv)) :
    F = atomicPositive C := by
  funext st
  induction st using (pairEarlier_wellFounded C).induction with
  | h st ih =>
    have hr : (fun (uv : C.Name × C.Name) (_ : PairEarlier C uv st) => F uv) =
        (fun (uv : C.Name × C.Name) (_ : PairEarlier C uv st) => atomicPositive C uv) := by
      funext uv h
      exact ih uv h
    rw [hF st,hr]
    exact (WellFounded.fix_eq (pairEarlier_wellFounded C) (atomicStep C) st).symm

theorem atomic_neq_symmetric (C : Context.{u,v} Q) (σ τ : C.Name) (p : Q) :
    atomicPositive C (σ,τ) p .neq ↔ atomicPositive C (τ,σ) p .neq := by
  rw [atomic_neq_clause,atomic_neq_clause]
  exact or_comm

abbrev BoundedName (C : Context.{u,v} Q) (β : Ordinal.{u}) :=
  {σ : C.Name // nameRank σ.val < β}

theorem bounded_names_child_closed (C : Context.{u,v} Q) (β : Ordinal.{u})
    (σ : BoundedName C β) (θ : C.Name) (q : Q) (h : Attached C θ σ.val q) :
    nameRank θ.val < β := by
  exact (nameRank_child ⟨(C.code q).val,h⟩).trans σ.property

theorem atomic_bounded_agreement (C : Context.{u,v} Q) (β : Ordinal.{u})
    (F : BoundedName C β × BoundedName C β → Q → AtomKind → Prop)
    (hmem : ∀ (σ τ : BoundedName C β) p,
      F (σ,τ) p .mem ↔
        ∃ θ : BoundedName C β, ∃ q, Attached C θ.val τ.val q ∧ p ≤ q ∧
          ∀ r ≤ p, ¬F (θ,σ) r .neq)
    (hneq : ∀ (σ τ : BoundedName C β) p,
      F (σ,τ) p .neq ↔
        (∃ θ : BoundedName C β, ∃ q, Attached C θ.val σ.val q ∧ p ≤ q ∧
          ∀ r ≤ p, ¬F (θ,τ) r .mem) ∨
        (∃ θ : BoundedName C β, ∃ q, Attached C θ.val τ.val q ∧ p ≤ q ∧
          ∀ r ≤ p, ¬F (θ,σ) r .mem)) :
    ∀ (σ τ : BoundedName C β) p k, F (σ,τ) p k ↔ atomicPositive C (σ.val,τ.val) p k := by
  have hall : ∀ st : C.Name × C.Name,
      ∀ (hs : nameRank st.1.val < β) (ht : nameRank st.2.val < β) p k,
      F (⟨st.1,hs⟩,⟨st.2,ht⟩) p k ↔ atomicPositive C st p k := by
    intro st
    induction st using (pairEarlier_wellFounded C).induction with
    | h st ih =>
      intro hs ht p k
      cases k with
      | mem =>
        rw [hmem,atomic_mem_clause]
        constructor
        · rintro ⟨θ,q,hθ,hpq,hn⟩
          refine ⟨θ.val,q,hθ,hpq,?_⟩
          intro r hr hp
          exact hn r hr ((ih (θ.val,st.1) (child_right_earlier C θ.val st.1 st.2 q hθ)
            θ.property hs r .neq).mpr hp)
        · rintro ⟨θ,q,hθ,hpq,hn⟩
          have hβ : nameRank θ.val < β := (nameRank_child ⟨(C.code q).val,hθ⟩).trans ht
          refine ⟨⟨θ,hβ⟩,q,hθ,hpq,?_⟩
          intro r hr hp
          exact hn r hr ((ih (θ,st.1) (child_right_earlier C θ st.1 st.2 q hθ)
            hβ hs r .neq).mp hp)
      | neq =>
        rw [hneq,atomic_neq_clause]
        constructor
        · rintro (⟨θ,q,hθ,hpq,hn⟩ | ⟨θ,q,hθ,hpq,hn⟩)
          · refine Or.inl ⟨θ.val,q,hθ,hpq,?_⟩
            intro r hr hp
            exact hn r hr ((ih (θ.val,st.2) (child_left_earlier C θ.val st.1 st.2 q hθ)
              θ.property ht r .mem).mpr hp)
          · refine Or.inr ⟨θ.val,q,hθ,hpq,?_⟩
            intro r hr hp
            exact hn r hr ((ih (θ.val,st.1) (child_right_earlier C θ.val st.1 st.2 q hθ)
              θ.property hs r .mem).mpr hp)
        · rintro (⟨θ,q,hθ,hpq,hn⟩ | ⟨θ,q,hθ,hpq,hn⟩)
          · have hβ : nameRank θ.val < β := (nameRank_child ⟨(C.code q).val,hθ⟩).trans hs
            refine Or.inl ⟨⟨θ,hβ⟩,q,hθ,hpq,?_⟩
            intro r hr hp
            exact hn r hr ((ih (θ,st.2) (child_left_earlier C θ st.1 st.2 q hθ)
              hβ ht r .mem).mp hp)
          · have hβ : nameRank θ.val < β := (nameRank_child ⟨(C.code q).val,hθ⟩).trans ht
            refine Or.inr ⟨⟨θ,hβ⟩,q,hθ,hpq,?_⟩
            intro r hr hp
            exact hn r hr ((ih (θ,st.1) (child_right_earlier C θ st.1 st.2 q hθ)
              hβ hs r .mem).mp hp)
  intro σ τ p k
  exact hall (σ.val,τ.val) σ.property τ.property p k

def Aux.Force (C : Context.{u,v} Q) :
    {n : ℕ} → Aux n → (Fin n → C.Name) → Q → Prop
  | _, .mem i j, a, p => atomicPositive C (a i,a j) p .mem
  | _, .neq i j, a, p => atomicPositive C (a i,a j) p .neq
  | _, .neg A, a, p => ∀ q ≤ p, ¬A.Force C a q
  | _, .disj A B, a, p => A.Force C a p ∨ B.Force C a p
  | _, .ex A, a, p => ∃ σ : C.Name, A.Force C (Fin.snoc a σ) p

def decisionSet (C : Context.{u,v} Q) {n} (A : Aux n) (a : Fin n → C.Name) : Set Q :=
  {p | A.Force C a p ∨ A.neg.Force C a p}

def DecisionClosed (C : Context.{u,v} Q) : Prop :=
  ∀ n (A : Aux n) (a : Fin n → C.Name), decisionSet C A a ∈ C.groundFamily

def internalAssignment (C : Context.{u,v} Q) {n} (p : Q) (a : Fin n → C.Name) :
    Fin (3+n) → C.ground :=
  Fin.append ![⟨(C.code p).val,C.transitive _ C.conditions_mem (C.code p).property⟩,
    ⟨C.conditions,C.conditions_mem⟩,⟨C.relation,C.relation_mem⟩]
    (fun i => ⟨(a i).val,(a i).property.1⟩)

def AuxDefinable (C : Context.{u,v} Q) {n} (A : Aux n) : Prop :=
  ∃ φ : membershipLanguage.BoundedFormula Empty (3+n),
    ∀ p (a : Fin n → C.Name),
      setSatisfies C.ground φ (internalAssignment C p a) ↔ A.Force C a p

def SeparationClosed (C : Context.{u,v} Q) : Prop :=
  ∀ n (φ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → C.ground)
    (i : Fin n),
    C.conditions.sep (fun p => ∃ hp : p ∈ C.ground,
      setSatisfies C.ground φ (Function.update a i ⟨p,hp⟩)) ∈ C.ground


private theorem internal_update [OrderTop Q] (C : Context.{u,v} Q) {n}
    (p : Q) (a : Fin n → C.Name) :
    Function.update (internalAssignment C ⊤ a) (0 : Fin (3+n))
      ⟨(C.code p).val,C.transitive _ C.conditions_mem (C.code p).property⟩ =
        internalAssignment C p a := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp [internalAssignment,Function.update,Fin.ext_iff]
  · have hne : Fin.natAdd 3 j ≠ (0 : Fin (3+n)) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd,Fin.val_zero] at hv
      omega
    rw [Function.update_of_ne hne]
    simp only [internalAssignment,Fin.append_right]

theorem decision_closed_of_definable [OrderTop Q] (C : Context.{u,v} Q)
    (hdef : ∀ n (A : Aux n), AuxDefinable C A) (hsep : SeparationClosed C) :
    DecisionClosed C := by
  intro n A a
  obtain ⟨φ,hφ⟩ := hdef n (A.disj A.neg)
  let b := internalAssignment C ⊤ a
  let S := C.conditions.sep (fun p => ∃ hp : p ∈ C.ground,
    setSatisfies C.ground φ (Function.update b (0 : Fin (3+n)) ⟨p,hp⟩))
  have hS : S ∈ C.ground := hsep (3+n) φ b 0
  have he : C.subsetCode (decisionSet C A a) = S := by
    ext x
    simp only [Context.subsetCode,S,ZFSet.mem_sep]
    change (x ∈ C.conditions ∧ ∃ q ∈ decisionSet C A a, (C.code q).val = x) ↔
      (x ∈ C.conditions ∧ ∃ hx : x ∈ C.ground,
        setSatisfies C.ground φ (Function.update b 0 ⟨x,hx⟩))
    constructor
    · rintro ⟨hx,q,hq,rfl⟩
      refine ⟨(C.code q).property,C.transitive _ C.conditions_mem (C.code q).property,?_⟩
      change setSatisfies C.ground φ (Function.update (internalAssignment C ⊤ a) 0 _)
      rw [internal_update]
      exact (hφ q a).mpr hq
    · rintro ⟨hx,hxM,hSat⟩
      let q := C.code.symm ⟨x,hx⟩
      have hq : (C.code q).val = x := congrArg Subtype.val (C.code.apply_symm_apply _)
      have hs : (⟨x,hxM⟩ : C.ground) =
          ⟨(C.code q).val,C.transitive _ C.conditions_mem (C.code q).property⟩ :=
        Subtype.ext hq.symm
      change setSatisfies C.ground φ (Function.update (internalAssignment C ⊤ a) 0 _) at hSat
      rw [hs,internal_update] at hSat
      exact ⟨hx,q,(hφ q a).mp hSat,hq⟩
  exact (groundFamily_iff C _).mpr (he.symm ▸ hS)

theorem atomic_monotone (C : Context.{u,v} Q) (σ τ : C.Name) (k : AtomKind)
    {p q : Q} (hqp : q ≤ p) (h : atomicPositive C (σ,τ) p k) :
    atomicPositive C (σ,τ) q k := by
  have negmono (st : C.Name × C.Name) (k : AtomKind)
      (h : atomicNegative C st p k) : atomicNegative C st q k :=
    fun r hr => h r (hr.trans hqp)
  cases k with
  | mem =>
    obtain ⟨θ,r,ht,hpr,hn⟩ := (atomic_mem_clause C σ τ p).mp h
    exact (atomic_mem_clause C σ τ q).mpr ⟨θ,r,ht,hqp.trans hpr,negmono _ _ hn⟩
  | neq =>
    rcases (atomic_neq_clause C σ τ p).mp h with ⟨θ,r,ht,hpr,hn⟩ | ⟨θ,r,ht,hpr,hn⟩
    · exact (atomic_neq_clause C σ τ q).mpr (Or.inl ⟨θ,r,ht,hqp.trans hpr,negmono _ _ hn⟩)
    · exact (atomic_neq_clause C σ τ q).mpr (Or.inr ⟨θ,r,ht,hqp.trans hpr,negmono _ _ hn⟩)

theorem auxiliary_monotone (C : Context.{u,v} Q) {n} (A : Aux n) (a : Fin n → C.Name)
    {p q : Q} (hqp : q ≤ p) (h : A.Force C a p) : A.Force C a q := by
  induction A with
  | mem i j => exact atomic_monotone C _ _ .mem hqp h
  | neq i j => exact atomic_monotone C _ _ .neq hqp h
  | neg A ih =>
    exact fun r hr => h r (hr.trans hqp)
  | disj A B ihA ihB =>
    exact h.elim (fun h => Or.inl (ihA a h)) (fun h => Or.inr (ihB a h))
  | ex A ih =>
    obtain ⟨σ,hσ⟩ := h
    exact ⟨σ,ih (Fin.snoc a σ) hσ⟩

theorem decision_dense (C : Context.{u,v} Q) {n} (A : Aux n) (a : Fin n → C.Name) :
    Dense (decisionSet C A a) := by
  intro p
  by_cases h : ∃ q ≤ p, A.Force C a q
  · obtain ⟨q,hqp,hq⟩ := h
    exact ⟨q,Or.inl hq,hqp⟩
  · exact ⟨p,Or.inr (fun q hqp hq => h ⟨q,hqp,hq⟩),le_rfl⟩

theorem generic_decision (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) {n}
    (A : Aux n) (a : Fin n → C.Name) :
    ((∃ p ∈ G, A.neg.Force C a p) ↔ ¬∃ p ∈ G, A.Force C a p) ∧
      ((∃ p ∈ G, A.Force C a p) ∨ (∃ p ∈ G, A.neg.Force C a p)) := by
  have hone : (∃ p ∈ G, A.Force C a p) ∨ ∃ p ∈ G, A.neg.Force C a p := by
    obtain ⟨p,hp,hpA | hpN⟩ := hG _ (hC n A a) (decision_dense C A a)
    · exact Or.inl ⟨p,hp,hpA⟩
    · exact Or.inr ⟨p,hp,hpN⟩
  have hnot : (∃ p ∈ G, A.neg.Force C a p) → ¬∃ p ∈ G, A.Force C a p := by
    rintro ⟨q,hq,hqN⟩ ⟨p,hp,hpA⟩
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed p hp q hq
    exact hqN r hrq (auxiliary_monotone C A a hrp hpA)
  refine ⟨⟨hnot,?_⟩,hone⟩
  intro h
  exact hone.elim (fun hA => (h hA).elim) id

theorem activation (C : Context.{u,v} Q) (G : PFilter Q) (τ : C.Name)
    (B : C.Name → Q → Prop) (T : C.Name → Prop)
    (hmono : ∀ θ {p q}, q ≤ p → B θ p → B θ q)
    (htruth : ∀ θ, T θ ↔ ∃ p ∈ G, B θ p) :
    (∃ θ q, Attached C θ τ q ∧ q ∈ G ∧ T θ) ↔
      ∃ p ∈ G, ∃ θ q, Attached C θ τ q ∧ p ≤ q ∧ B θ p := by
  constructor
  · rintro ⟨θ,q,ht,hq,hθ⟩
    obtain ⟨r,hr,hrB⟩ := (htruth θ).mp hθ
    obtain ⟨p,hp,hpq,hpr⟩ := G.directed q hq r hr
    exact ⟨p,hp,θ,q,ht,hpq,hmono θ hpr hrB⟩
  · rintro ⟨p,hp,θ,q,ht,hpq,hpB⟩
    exact ⟨θ,q,ht,PFilter.mem_of_le hpq hp,(htruth θ).mpr ⟨p,hp,hpB⟩⟩


private theorem value_member (C : Context.{u,v} Q) (G : PFilter Q)
    (x : ZFSet.{u}) (τ : C.Name) :
    x ∈ (C.value G τ).val ↔ ∃ θ q, Attached C θ τ q ∧ q ∈ G ∧ x = (C.value G θ).val := by
  change x ∈ evaluation (C.filterCode G) τ.val ↔ _
  rw [evaluation_mem]
  constructor
  · rintro ⟨σ,p,hσp,hp,he⟩
    obtain ⟨q,hq,rfl⟩ := (filterSet_mem C.conditions C.code G p).mp hp
    obtain ⟨σ',p',hpair,_,hn⟩ := (isName_iff C.conditions τ.val).mp τ.property.2 _ hσp
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
    have hσM := child_in_transitive_domain C.ground C.transitive τ.property.1 ⟨(C.code q).val,hσp⟩
    exact ⟨⟨σ,hσM,hn⟩,q,hσp,hq,he⟩
  · rintro ⟨θ,q,hθ,hq,he⟩
    exact ⟨θ.val,(C.code q).val,hθ,(filterSet_mem C.conditions C.code G _).mpr
      ⟨q,hq,rfl⟩,he⟩

private theorem value_surjective (C : Context.{u,v} Q) (G : PFilter Q)
    (x : C.valueDomain G) : ∃ σ : C.Name, C.value G σ = x := by
  obtain ⟨τ,hτ,hn,he⟩ := (extension_mem C.conditions C.ground (C.filterCode G) x.val).mp x.property
  exact ⟨⟨τ,hτ,hn⟩,Subtype.ext he⟩

private theorem valueAssignment_snoc (C : Context.{u,v} Q) (G : PFilter Q) {n}
    (a : Fin n → C.Name) (σ : C.Name) :
    C.valueAssignment G (Fin.snoc a σ) = Fin.snoc (C.valueAssignment G a) (C.value G σ) :=
  Fin.comp_snoc (C.value G) a σ

theorem atomic_truth (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) (σ τ : C.Name) :
    ((C.value G σ).val ∈ (C.value G τ).val ↔
      ∃ p ∈ G, atomicPositive C (σ,τ) p .mem) ∧
    ((C.value G σ).val ≠ (C.value G τ).val ↔
      ∃ p ∈ G, atomicPositive C (σ,τ) p .neq) ∧
    ((C.value G σ).val ∉ (C.value G τ).val ↔
      ∃ p ∈ G, atomicNegative C (σ,τ) p .mem) ∧
    ((C.value G σ).val = (C.value G τ).val ↔
      ∃ p ∈ G, atomicNegative C (σ,τ) p .neq) := by
  have hall : ∀ st : C.Name × C.Name,
      ((C.value G st.1).val ∈ (C.value G st.2).val ↔
        ∃ p ∈ G, atomicPositive C st p .mem) ∧
      ((C.value G st.1).val ≠ (C.value G st.2).val ↔
        ∃ p ∈ G, atomicPositive C st p .neq) ∧
      ((C.value G st.1).val ∉ (C.value G st.2).val ↔
        ∃ p ∈ G, atomicNegative C st p .mem) ∧
      ((C.value G st.1).val = (C.value G st.2).val ↔
        ∃ p ∈ G, atomicNegative C st p .neq) := by
    intro st
    induction st using (pairEarlier_wellFounded C).induction with
    | h st ih =>
      rcases st with ⟨σ,τ⟩
      have hmem : (C.value G σ).val ∈ (C.value G τ).val ↔
          ∃ p ∈ G, atomicPositive C (σ,τ) p .mem := by
        constructor
        · intro hm
          obtain ⟨θ,q,ht,hq,he⟩ := (value_member C G _ τ).mp hm
          obtain ⟨r,hr,hn⟩ := (ih (θ,σ) (child_right_earlier C θ σ τ q ht)).2.2.2.mp he.symm
          obtain ⟨p,hp,hpq,hpr⟩ := G.directed q hq r hr
          exact ⟨p,hp,(atomic_mem_clause C σ τ p).mpr
            ⟨θ,q,ht,hpq,fun t htp => hn t (htp.trans hpr)⟩⟩
        · rintro ⟨p,hp,hpos⟩
          obtain ⟨θ,q,ht,hpq,hn⟩ := (atomic_mem_clause C σ τ p).mp hpos
          have he := (ih (θ,σ) (child_right_earlier C θ σ τ q ht)).2.2.2.mpr ⟨p,hp,hn⟩
          exact (value_member C G _ τ).mpr ⟨θ,q,ht,PFilter.mem_of_le hpq hp,he.symm⟩
      have hneq : (C.value G σ).val ≠ (C.value G τ).val ↔
          ∃ p ∈ G, atomicPositive C (σ,τ) p .neq := by
        constructor
        · intro hne
          have hex : (∃ x, x ∈ (C.value G σ).val ∧ x ∉ (C.value G τ).val) ∨
              (∃ x, x ∈ (C.value G τ).val ∧ x ∉ (C.value G σ).val) := by
            by_contra h
            push Not at h
            exact hne (ZFSet.ext fun x => ⟨h.1 x,h.2 x⟩)
          rcases hex with ⟨x,hx,hnx⟩ | ⟨x,hx,hnx⟩
          · obtain ⟨θ,q,ht,hq,he⟩ := (value_member C G x σ).mp hx
            have hnθ : (C.value G θ).val ∉ (C.value G τ).val := he ▸ hnx
            obtain ⟨r,hr,hn⟩ := (ih (θ,τ) (child_left_earlier C θ σ τ q ht)).2.2.1.mp hnθ
            obtain ⟨p,hp,hpq,hpr⟩ := G.directed q hq r hr
            exact ⟨p,hp,(atomic_neq_clause C σ τ p).mpr
              (Or.inl ⟨θ,q,ht,hpq,fun t htp => hn t (htp.trans hpr)⟩)⟩
          · obtain ⟨θ,q,ht,hq,he⟩ := (value_member C G x τ).mp hx
            have hnθ : (C.value G θ).val ∉ (C.value G σ).val := he ▸ hnx
            obtain ⟨r,hr,hn⟩ := (ih (θ,σ) (child_right_earlier C θ σ τ q ht)).2.2.1.mp hnθ
            obtain ⟨p,hp,hpq,hpr⟩ := G.directed q hq r hr
            exact ⟨p,hp,(atomic_neq_clause C σ τ p).mpr
              (Or.inr ⟨θ,q,ht,hpq,fun t htp => hn t (htp.trans hpr)⟩)⟩
        · rintro ⟨p,hp,hpos⟩
          rcases (atomic_neq_clause C σ τ p).mp hpos with ⟨θ,q,ht,hpq,hn⟩ | ⟨θ,q,ht,hpq,hn⟩
          · have hnot := (ih (θ,τ) (child_left_earlier C θ σ τ q ht)).2.2.1.mpr ⟨p,hp,hn⟩
            have hin := (value_member C G _ σ).mpr ⟨θ,q,ht,PFilter.mem_of_le hpq hp,rfl⟩
            exact fun he => hnot (he ▸ hin)
          · have hnot := (ih (θ,σ) (child_right_earlier C θ σ τ q ht)).2.2.1.mpr ⟨p,hp,hn⟩
            have hin := (value_member C G _ τ).mpr ⟨θ,q,ht,PFilter.mem_of_le hpq hp,rfl⟩
            exact fun he => hnot (he.symm ▸ hin)
      have hdm := (generic_decision C hC G hG (Aux.mem (0 : Fin 2) 1) ![σ,τ]).1
      change (∃ p ∈ G, atomicNegative C (σ,τ) p .mem) ↔
        ¬∃ p ∈ G, atomicPositive C (σ,τ) p .mem at hdm
      have hdn := (generic_decision C hC G hG (Aux.neq (0 : Fin 2) 1) ![σ,τ]).1
      change (∃ p ∈ G, atomicNegative C (σ,τ) p .neq) ↔
        ¬∃ p ∈ G, atomicPositive C (σ,τ) p .neq at hdn
      refine ⟨hmem,hneq,(not_congr hmem).trans hdm.symm,?_⟩
      simpa only [not_ne_iff] using (not_congr hneq).trans hdn.symm
  exact hall (σ,τ)

theorem auxiliary_truth (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) {n}
    (A : Aux n) (a : Fin n → C.Name) :
    C.auxTruth G A a ↔ ∃ p ∈ G, A.Force C a p := by
  induction A with
  | mem i j =>
    exact (atomic_truth C hC G hG (a i) (a j)).1
  | neq i j =>
    change C.value G (a i) ≠ C.value G (a j) ↔
      ∃ p ∈ G, atomicPositive C (a i,a j) p AtomKind.neq
    constructor
    · intro hne
      apply (atomic_truth C hC G hG (a i) (a j)).2.1.mp
      intro he
      exact hne (Subtype.ext he)
    · intro hpos
      have hne := (atomic_truth C hC G hG (a i) (a j)).2.1.mpr hpos
      intro he
      exact hne (congrArg Subtype.val he)
  | neg A ih =>
    change (¬C.auxTruth G A a) ↔ _
    rw [ih]
    exact (generic_decision C hC G hG A a).1.symm
  | disj A B ihA ihB =>
    change (C.auxTruth G A a ∨ C.auxTruth G B a) ↔
      ∃ p ∈ G, A.Force C a p ∨ B.Force C a p
    rw [ihA,ihB]
    aesop
  | ex A ih =>
    change (∃ x : C.valueDomain G, A.Holds _ (Fin.snoc (C.valueAssignment G a) x)) ↔
      ∃ p ∈ G, ∃ σ : C.Name, A.Force C (Fin.snoc a σ) p
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨σ,he⟩ := value_surjective C G x
      have htruth : C.auxTruth G A (Fin.snoc a σ) := by
        change A.Holds _ (C.valueAssignment G (Fin.snoc a σ))
        rw [valueAssignment_snoc,he]
        exact hx
      obtain ⟨p,hp,hpA⟩ := (ih (Fin.snoc a σ)).mp htruth
      exact ⟨p,hp,σ,hpA⟩
    · rintro ⟨p,hp,σ,hpA⟩
      have htruth := (ih (Fin.snoc a σ)).mpr ⟨p,hp,hpA⟩
      change A.Holds _ (C.valueAssignment G (Fin.snoc a σ)) at htruth
      rw [valueAssignment_snoc] at htruth
      exact ⟨C.value G σ,htruth⟩

theorem semantic_double_negation (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable) {n}
    (A : Aux n) (a : Fin n → C.Name) (p : Q) :
    C.semanticAux A a p ↔ A.neg.neg.Force C a p := by
  constructor
  · intro h q hqp hqN
    obtain ⟨G,hG,hq⟩ := generic_through_condition C hM q
    have hA := h G hG (PFilter.mem_of_le hqp hq)
    have hNA := (auxiliary_truth C hC G hG A.neg a).mpr ⟨q,hq,hqN⟩
    exact hNA hA
  · intro h G hG hp
    have hNN := (auxiliary_truth C hC G hG A.neg.neg a).mpr ⟨p,hp,h⟩
    change ¬¬C.auxTruth G A a at hNN
    exact Classical.not_not.mp hNN

theorem ordinary_truth (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) {n}
    (φ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → C.Name) :
    setSatisfies (C.valueDomain G) φ (C.valueAssignment G a) ↔
      ∃ p ∈ G, C.semanticForce φ a p := by
  constructor
  · intro h
    have hA : C.auxTruth G (translate φ) a := (translate_setSatisfies _ φ _).mp h
    obtain ⟨p,hp,hpA⟩ := (auxiliary_truth C hC G hG _ a).mp hA
    refine ⟨p,hp,?_⟩
    intro H hH hpH
    exact (translate_setSatisfies _ φ _).mpr
      ((auxiliary_truth C hC H hH _ a).mpr ⟨p,hpH,hpA⟩)
  · rintro ⟨p,hp,hforce⟩
    exact hforce G hG hp

theorem ordinary_forcing_definition (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable) {n}
    (φ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → C.Name) (p : Q) :
    C.semanticForce φ a p ↔ (translate φ).neg.neg.Force C a p := by
  exact (semantic_translation C φ a p).trans
    (semantic_double_negation C hC hM (translate φ) a p)

theorem ordinary_forcing_definable (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable) {n}
    (φ : membershipLanguage.BoundedFormula Empty n)
    (hdef : AuxDefinable C (translate φ).neg.neg) :
    ∃ ψ : membershipLanguage.BoundedFormula Empty (3+n),
      ∀ p (a : Fin n → C.Name),
        setSatisfies C.ground ψ (internalAssignment C p a) ↔ C.semanticForce φ a p := by
  obtain ⟨ψ,hψ⟩ := hdef
  exact ⟨ψ,fun p a => (hψ p a).trans (ordinary_forcing_definition C hC hM φ a p).symm⟩

theorem refining_existential (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1)) (a : Fin n → C.Name)
    (p : Q) (hp : C.semanticForce φ.ex a p) :
    ∃ q ≤ p, ∃ σ : C.Name, C.semanticForce φ (Fin.snoc a σ) q := by
  obtain ⟨G,hG,hpG⟩ := generic_through_condition C hM p
  have hex := hp G hG hpG
  let := actualMembershipStructure (C.valueDomain G)
  change φ.ex.Realize Empty.elim (C.valueAssignment G a) at hex
  rw [BoundedFormula.realize_ex] at hex
  obtain ⟨x,hx⟩ := hex
  obtain ⟨σ,he⟩ := value_surjective C G x
  have hφ : setSatisfies (C.valueDomain G) φ (C.valueAssignment G (Fin.snoc a σ)) := by
    rw [valueAssignment_snoc,he]
    exact hx
  obtain ⟨r,hr,hrφ⟩ := (ordinary_truth C hC G hG φ (Fin.snoc a σ)).mp hφ
  obtain ⟨q,hq,hqp,hqr⟩ := G.directed p hpG r hr
  exact ⟨q,hqp,σ,semantic_monotone C φ _ hqr hrφ⟩

theorem refining_disjunction (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable) {n}
    (φ ψ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → C.Name)
    (p : Q) (hp : C.semanticForce (φ ⊔ ψ) a p) :
    ∃ q ≤ p, C.semanticForce φ a q ∨ C.semanticForce ψ a q := by
  obtain ⟨G,hG,hpG⟩ := generic_through_condition C hM p
  have hor := hp G hG hpG
  let := actualMembershipStructure (C.valueDomain G)
  change (φ ⊔ ψ).Realize Empty.elim (C.valueAssignment G a) at hor
  rw [BoundedFormula.realize_sup] at hor
  rcases hor with hφ | hψ
  · obtain ⟨r,hr,hrφ⟩ := (ordinary_truth C hC G hG φ a).mp hφ
    obtain ⟨q,hq,hqp,hqr⟩ := G.directed p hpG r hr
    exact ⟨q,hqp,Or.inl (semantic_monotone C φ _ hqr hrφ)⟩
  · obtain ⟨r,hr,hrψ⟩ := (ordinary_truth C hC G hG ψ a).mp hψ
    obtain ⟨q,hq,hqp,hqr⟩ := G.directed p hpG r hr
    exact ⟨q,hqp,Or.inr (semantic_monotone C ψ _ hqr hrψ)⟩

theorem auxiliary_reflexive_equality (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable) (σ : C.Name) (p : Q) :
    atomicNegative C (σ,σ) p .neq := by
  intro q hqp hq
  obtain ⟨G,hG,hqG⟩ := generic_through_condition C hM q
  have hneq := (atomic_truth C hC G hG σ σ).2.1.mpr ⟨q,hqG,hq⟩
  exact hneq rfl

namespace ThreePoint

inductive Condition | one | left | right deriving DecidableEq

instance partialOrderCondition : PartialOrder Condition where
  le x y := x = y ∨ y = .one
  le_refl := fun _ => Or.inl rfl
  le_trans := by
    intro x y z hxy hyz
    rcases hxy with rfl | hy
    · exact hyz
    · rcases hyz with rfl | hz
      · exact Or.inr hy
      · exact Or.inr hz
  le_antisymm := by
    intro x y hxy hyx
    rcases hxy with he | hy
    · exact he
    · rcases hyx with he | hx
      · exact he.symm
      · exact hx.trans hy.symm

instance orderTopCondition : OrderTop Condition where
  top := .one
  le_top := fun _ => Or.inr rfl

instance : DecidableRel (fun x y : Condition => x ≤ y) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _ ∨ _ = Condition.one))

def splitName (C : Context.{u,0} Condition) : ZFSet.{u} :=
  {ZFSet.pair ∅ (C.code .left).val,ZFSet.pair ∅ (C.code .right).val}

theorem empty_name_valid (C : Context.{u,0} Condition) : IsName C.conditions (∅ : ZFSet.{u}) := by
  apply (isName_iff C.conditions ∅).mpr
  intro z hz
  exact (ZFSet.notMem_empty z hz).elim

theorem split_name_valid (C : Context.{u,0} Condition) : IsName C.conditions (splitName C) := by
  apply (isName_iff C.conditions _).mpr
  intro z hz
  rcases ZFSet.mem_insert_iff.mp hz with rfl | hz
  · exact ⟨∅,(C.code .left).val,rfl,(C.code .left).property,empty_name_valid C⟩
  · have he := ZFSet.mem_singleton.mp hz
    subst z
    exact ⟨∅,(C.code .right).val,rfl,(C.code .right).property,empty_name_valid C⟩

def emptyGroundName (C : Context.{u,0} Condition) (h0 : (∅ : ZFSet.{u}) ∈ C.ground) : C.Name :=
  ⟨∅,h0,empty_name_valid C⟩

def splitGroundName (C : Context.{u,0} Condition) (hτ : splitName C ∈ C.ground) : C.Name :=
  ⟨splitName C,hτ,split_name_valid C⟩

theorem finite_order :
    Condition.left ≤ Condition.one ∧ Condition.right ≤ Condition.one ∧
      ¬Compatible Condition.left Condition.right ∧
      ¬Condition.one ≤ Condition.left ∧ ¬Condition.one ≤ Condition.right ∧
      (∀ p : Condition, p ≤ Condition.left → p = Condition.left) ∧
      (∀ p : Condition, p ≤ Condition.right → p = Condition.right) := by
  have hl (p : Condition) (h : p ≤ .left) : p = .left := by
    rcases h with h | h
    · exact h
    · cases h
  have hr (p : Condition) (h : p ≤ .right) : p = .right := by
    rcases h with h | h
    · exact h
    · cases h
  refine ⟨Or.inr rfl,Or.inr rfl,?_,?_,?_,hl,hr⟩
  · rintro ⟨p,hpl,hpr⟩
    exact Condition.noConfusion ((hl p hpl).symm.trans (hr p hpr))
  · rintro (h | h) <;> cases h
  · rintro (h | h) <;> cases h

theorem split_dense : Dense ({Condition.left,Condition.right} : Set Condition) := by
  intro p
  cases p with
  | one => exact ⟨.left,by simp,Or.inr rfl⟩
  | left => exact ⟨.left,by simp,le_rfl⟩
  | right => exact ⟨.right,by simp,le_rfl⟩

theorem split_ground (C : Context.{u,0} Condition) (hsep : SeparationClosed C) :
    ({Condition.left,Condition.right} : Set Condition) ∈ C.groundFamily := by
  let φ : membershipLanguage.BoundedFormula Empty 3 :=
    (.equal (.var (.inr 0)) (.var (.inr 1))) ⊔ (.equal (.var (.inr 0)) (.var (.inr 2)))
  let b : Fin 3 → C.ground :=
    ![⟨(C.code .one).val,C.transitive _ C.conditions_mem (C.code .one).property⟩,
      ⟨(C.code .left).val,C.transitive _ C.conditions_mem (C.code .left).property⟩,
      ⟨(C.code .right).val,C.transitive _ C.conditions_mem (C.code .right).property⟩]
  have hφ (a : Fin 3 → C.ground) :
      setSatisfies C.ground φ a ↔ a 0 = a 1 ∨ a 0 = a 2 := by
    let := actualMembershipStructure C.ground
    change φ.Realize Empty.elim a ↔ _
    simp only [φ,BoundedFormula.realize_sup,BoundedFormula.Realize,Term.realize_var]
    rfl
  have hS := hsep 3 φ b 0
  have he : C.subsetCode ({Condition.left,Condition.right} : Set Condition) =
      C.conditions.sep (fun p => ∃ hp : p ∈ C.ground,
        setSatisfies C.ground φ (Function.update b 0 ⟨p,hp⟩)) := by
    ext p
    rw [Context.subsetCode,ZFSet.mem_sep,ZFSet.mem_sep]
    simp only [hφ,Function.update_self,Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
      Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0),Subtype.ext_iff]
    change (p ∈ C.conditions ∧ ∃ q ∈ ({Condition.left,Condition.right} : Set Condition),
      (C.code q).val = p) ↔
      (p ∈ C.conditions ∧ ∃ hp : p ∈ C.ground,
        p = (C.code .left).val ∨ p = (C.code .right).val)
    constructor
    · rintro ⟨hp,q,hq,he⟩
      refine ⟨hp,C.transitive _ C.conditions_mem hp,?_⟩
      rcases hq with rfl | hq
      · exact Or.inl he.symm
      · have heq := Set.mem_singleton_iff.mp hq
        subst q
        exact Or.inr he.symm
    · rintro ⟨hp,_,he | he⟩
      · exact ⟨hp,.left,by simp,he.symm⟩
      · exact ⟨hp,.right,by simp,he.symm⟩
  exact (groundFamily_iff C _).mpr (he.symm ▸ hS)

theorem membership_counterexample (C : Context.{u,0} Condition) (hsep : SeparationClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable)
    (h0 : (∅ : ZFSet.{u}) ∈ C.ground) (hτ : splitName C ∈ C.ground) :
    let a : Fin 2 → C.Name := ![emptyGroundName C h0,splitGroundName C hτ]
    C.semanticForce (memScoped (0 : Fin 2) 1) a Condition.one ∧
      ¬(Aux.mem (0 : Fin 2) 1).Force C a Condition.one ∧
      ∃ G : PFilter Condition, GenericFor G C.groundFamily ∧ Condition.one ∈ G := by
  dsimp only
  refine ⟨?_,?_,generic_through_condition C hM .one⟩
  · intro G hG htop
    obtain ⟨q,hq,hqD⟩ := hG _ (split_ground C hsep) split_dense
    have hattach : ZFSet.pair (∅ : ZFSet.{u}) (C.code q).val ∈ splitName C := by
      rcases hqD with rfl | hqD
      · simp [splitName]
      · have he := Set.mem_singleton_iff.mp hqD
        subst q
        simp [splitName]
    have hempty : evaluation (C.filterCode G) (∅ : ZFSet.{u}) = ∅ := by
      ext x
      simp only [evaluation_mem,ZFSet.notMem_empty,false_and,exists_false]
    have hmem : (∅ : ZFSet.{u}) ∈ evaluation (C.filterCode G) (splitName C) :=
      (evaluation_mem _ _ _).mpr ⟨∅,(C.code q).val,hattach,
        (filterSet_mem C.conditions C.code G _).mpr ⟨q,hq,rfl⟩,hempty.symm⟩
    change evaluation (C.filterCode G) ∅ ∈ evaluation (C.filterCode G) (splitName C)
    rw [hempty]
    exact hmem
  · intro h
    obtain ⟨θ,q,ha,hq,_⟩ := (atomic_mem_clause C _ _ .one).mp h
    change ZFSet.pair θ.val (C.code q).val ∈
      {ZFSet.pair ∅ (C.code .left).val,ZFSet.pair ∅ (C.code .right).val} at ha
    rcases ZFSet.mem_insert_iff.mp ha with he | he
    · have heq := C.code.injective (Subtype.ext (ZFSet.pair_inj.mp he).2)
      subst q
      rcases hq with hq | hq <;> cases hq
    · have he := ZFSet.mem_singleton.mp he
      have heq := C.code.injective (Subtype.ext (ZFSet.pair_inj.mp he).2)
      subst q
      rcases hq with hq | hq <;> cases hq

end ThreePoint

end
end Lemmatheca.SetTheory.ForcingTheorem
