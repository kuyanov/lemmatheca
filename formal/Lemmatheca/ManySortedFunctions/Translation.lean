import Lemmatheca.ManySortedFunctions.Syntax

/-! Actual ordinary-language erasure, typing axioms, and the two model constructions. -/
namespace Lemmatheca.MathematicalLogic.ManySortedFunctions
open FirstOrder FirstOrder.Language
universe u v w
variable (L : Signature.{u,v})
inductive ErasedRelation : ℕ → Type (max u v)
  | sort (s : L.Sorts) : ErasedRelation 1
  | symbol {k} (r : L.Relations k) : ErasedRelation k
def erasedLanguage : Language where
  Functions := L.Functions
  Relations := ErasedRelation L

namespace Term
variable {L}
def erase {n} {γ : Context L n} :
    {s : L.Sorts} → Term L γ s → (erasedLanguage L).Term (Fin n)
  | _, .var i _ => .var i
  | _, .app f ts => .func f (fun i => erase (ts i))
end Term

namespace Formula
variable {L}
def erase : {n : ℕ} → {γ : Context L n} → Formula L γ →
    (erasedLanguage L).BoundedFormula Empty n
  | _, _, .falsum => .falsum
  | _, _, .equal t r => .equal (t.erase.relabel Sum.inr) (r.erase.relabel Sum.inr)
  | _, _, .rel r ts => .rel (.symbol r) (fun i => (ts i).erase.relabel Sum.inr)
  | _, _, .imp p q => (erase p).imp (erase q)
  | n, _, .all s p =>
      (BoundedFormula.imp
        (BoundedFormula.rel (L := erasedLanguage L) (ErasedRelation.sort s) (fun _ => .var (.inr (Fin.last n)))) (erase p)).all
end Formula

abbrev OrdinaryModel (U : Type w) := (erasedLanguage L).Structure U
namespace OrdinaryModel
variable {L} {U : Type w}
def sort (M : OrdinaryModel L U) (s : L.Sorts) (x : U) : Prop :=
  @Structure.RelMap (erasedLanguage L) U M 1 (.sort s) (fun _ => x)
def rel (M : OrdinaryModel L U) {k} (r : L.Relations k) (xs : Fin k → U) : Prop :=
  @Structure.RelMap (erasedLanguage L) U M k (.symbol r) xs
def func (M : OrdinaryModel L U) {k} (f : L.Functions k) (xs : Fin k → U) : U :=
  @Structure.funMap (erasedLanguage L) U M k f xs
def NonemptySorts (M : OrdinaryModel L U) : Prop := ∀ s, ∃ x, M.sort s x
def Sorted (M : OrdinaryModel L U) {n} (γ : Context L n) (a : Fin n → U) : Prop :=
  ∀ i, M.sort (γ i) (a i)
def Closed (M : OrdinaryModel L U) : Prop :=
  ∀ {k} (f : L.Functions k) (xs : Fin k → U),
    (∀ i, M.sort (L.input f i) (xs i)) → M.sort (L.output f) (M.func f xs)
def Typed (M : OrdinaryModel L U) : Prop := M.NonemptySorts ∧ M.Closed
end OrdinaryModel

def sortAxiom (s : L.Sorts) : (erasedLanguage L).Sentence :=
  (BoundedFormula.rel (L := erasedLanguage L) (ErasedRelation.sort s) (fun _ => .var (.inr (0 : Fin 1)))).ex
def closureFormula {k} (f : L.Functions k) : (erasedLanguage L).Formula (Fin k) :=
  ((List.ofFn fun i : Fin k =>
    FirstOrder.Language.Relations.formula (L := erasedLanguage L)
      (ErasedRelation.sort (L.input f i)) (fun _ => .var i)).foldr (· ⊓ ·) ⊤).imp
    (FirstOrder.Language.Relations.formula (L := erasedLanguage L)
      (ErasedRelation.sort (L.output f)) (fun _ => .func f FirstOrder.Language.Term.var))
def closureAxiom {k} (f : L.Functions k) : (erasedLanguage L).Sentence :=
  (BoundedFormula.relabel (Sum.inr : Fin k → Empty ⊕ Fin k) (closureFormula L f)).alls
def typingAxioms : (erasedLanguage L).Theory :=
  Set.range (sortAxiom L) ∪ {p | ∃ k, ∃ f : L.Functions k, closureAxiom L f = p}


namespace Model
variable {L} (D : Model.{u,v,w} L)
private theorem apply_carrier_cast {V : Type*} (f : ∀ s, D.Carrier s → V)
    {s t : L.Sorts} (h : s = t) (e : D.Carrier s = D.Carrier t) (x : D.Carrier s) :
    f t (cast e x) = f s x := by
  cases h
  rfl
private theorem assignSnoc_map {V : Type*}
    (f : ∀ s, D.Carrier s → V) {n} {γ : Context L n}
    (a : D.Assignment γ) {s} (x : D.Carrier s) :
    (fun i => f ((Fin.snoc γ s : Context L (n+1)) i) (D.assignSnoc a x i)) =
      Fin.snoc (fun i => f (γ i) (a i)) (f s x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [assignSnoc, Fin.lastCases_last, Fin.snoc_last]
    exact D.apply_carrier_cast f (s := s)
      (t := (Fin.snoc γ s : Context L (n+1)) (Fin.last n)) (by simp) _ x
  · simp only [assignSnoc, Fin.lastCases_castSucc, Fin.snoc_castSucc]
    exact D.apply_carrier_cast f (s := γ j)
      (t := (Fin.snoc γ s : Context L (n+1)) j.castSucc) (by simp) _ (a j)
end Model

namespace OrdinaryModel
variable {L} {U : Type w}
theorem exists_guard (M : OrdinaryModel L U) {n} {γ : Context L n}
    (s : L.Sorts) (p : Formula L (Fin.snoc γ s)) (a : Fin n → U) :
    @BoundedFormula.Realize _ U M Empty _
      (Formula.imp (Formula.all s (Formula.imp p Formula.falsum)) Formula.falsum).erase
      Empty.elim a ↔
    ∃ x, M.sort s x ∧
      @BoundedFormula.Realize _ U M Empty _ p.erase Empty.elim (Fin.snoc a x) := by
  let _ := M
  classical
  simp only [Formula.erase, BoundedFormula.Realize, FirstOrder.Language.Term.realize,
    Sum.elim_inr, Fin.snoc_last, OrdinaryModel.sort]
  constructor
  · intro h
    by_contra hn
    apply h
    intro x hx hp
    exact hn ⟨x,hx,hp⟩
  · rintro ⟨x,hx,hp⟩ h
    exact h x hx hp


theorem realizes_sortAxiom (M : OrdinaryModel L U) (s : L.Sorts) :
    @FirstOrder.Language.Sentence.Realize _ U M (sortAxiom L s) ↔
      ∃ x, M.sort s x := by
  let _ := M
  simp [sortAxiom, Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.realize_ex, BoundedFormula.Realize, Term.realize, sort, Fin.snoc]

theorem realizes_closureAxiom (M : OrdinaryModel L U) {k} (f : L.Functions k) :
    @FirstOrder.Language.Sentence.Realize _ U M (closureAxiom L f) ↔
      ∀ xs : Fin k → U, (∀ i, M.sort (L.input f i) (xs i)) →
        M.sort (L.output f) (M.func f xs) := by
  let _ := M
  simp only [closureAxiom, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_relabel, Function.comp_def, Sum.elim_inr,
    Fin.castAdd_zero, Nat.add_zero, Fin.cast_eq_self]
  apply forall_congr'
  intro xs
  simp only [closureFormula, BoundedFormula.realize_imp, BoundedFormula.realize_foldr_inf]
  apply imp_congr
  · simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
    rfl
  · rfl


theorem models_typingAxioms (M : OrdinaryModel L U) :
    @FirstOrder.Language.Theory.Model _ U M (typingAxioms L) ↔ M.Typed := by
  let _ := M
  rw [FirstOrder.Language.Theory.model_iff]
  constructor
  · intro h
    constructor
    · intro s
      exact (M.realizes_sortAxiom s).mp (h _ (Or.inl ⟨s,rfl⟩))
    · intro k f xs hxs
      exact (M.realizes_closureAxiom f).mp (h _ (Or.inr ⟨k,f,rfl⟩)) xs hxs
  · rintro ⟨hs,hf⟩ p (⟨s,rfl⟩|⟨k,f,rfl⟩)
    · exact (M.realizes_sortAxiom s).mpr (hs s)
    · exact (M.realizes_closureAxiom f).mpr (hf f)

theorem term_sort (M : OrdinaryModel L U) (hM : M.Closed) {n} {γ : Context L n}
    {s} (t : Term L γ s) (a : Fin n → U) (ha : M.Sorted γ a) :
    M.sort s (@FirstOrder.Language.Term.realize _ U M _ a t.erase) := by
  induction t with
  | var i h => cases h; exact ha i
  | app f ts ih =>
    exact hM f _ (fun i => ih i)


def toSorted (M : OrdinaryModel L U) (hM : M.Typed) : Model.{u,v,w} L where
  Carrier := fun s => {x : U // M.sort s x}
  nonempty := fun s => let ⟨x,hx⟩ := hM.1 s; ⟨⟨x,hx⟩⟩
  func := fun f xs => ⟨M.func f (fun i => (xs i).val),
    hM.2 f (fun i => (xs i).val) (fun i => (xs i).property)⟩
  rel := fun r xs => M.rel r (fun i => (xs i).val)

theorem eval_subtype (M : OrdinaryModel L U) (hM : M.Typed) {n}
    {γ : Context L n} {s} (t : Term L γ s) (a : (M.toSorted hM).Assignment γ) :
    ((M.toSorted hM).eval a t).val =
      @FirstOrder.Language.Term.realize _ U M _ (fun i => (a i).val) t.erase := by
  induction t with
  | var i h => cases h; rfl
  | app f ts ih =>
    change M.func f (fun i => ((M.toSorted hM).eval a (ts i)).val) = _
    congr 1
    funext i
    exact ih i


theorem realize_subtypes (M : OrdinaryModel L U) (hM : M.Typed) {n}
    {γ : Context L n} (p : Formula L γ) (a : (M.toSorted hM).Assignment γ) :
    (M.toSorted hM).Realize p a ↔
      @BoundedFormula.Realize _ U M Empty _ p.erase Empty.elim (fun i => (a i).val) := by
  induction p with
  | falsum => rfl
  | equal t r =>
    simp only [Formula.erase, Model.Realize, BoundedFormula.Realize,
      FirstOrder.Language.Term.realize_relabel, Function.comp_def, Sum.elim_inr]
    exact Subtype.ext_iff.trans (by rw [eval_subtype, eval_subtype])
  | rel r ts =>
    simp only [Formula.erase, Model.Realize, BoundedFormula.Realize,
      FirstOrder.Language.Term.realize_relabel, Function.comp_def, Sum.elim_inr]
    change M.rel r (fun i => ((M.toSorted hM).eval a (ts i)).val) ↔ _
    simp only [eval_subtype]
    rfl
  | imp p q ihp ihq => exact imp_congr (ihp a) (ihq a)
  | @all n γ s p ih =>
    simp only [Formula.erase, Model.Realize, BoundedFormula.Realize,
      FirstOrder.Language.Term.realize, Sum.elim_inr, Fin.snoc_last]
    change (∀ x : {x : U // M.sort s x},
      (M.toSorted hM).Realize p ((M.toSorted hM).assignSnoc a x)) ↔
      ∀ x, M.sort s x → @BoundedFormula.Realize _ U M Empty _ p.erase Empty.elim
        (Fin.snoc (fun i => (a i).val) x)
    constructor
    · intro h x hx
      have hi := (ih _).mp (h ⟨x,hx⟩)
      erw [Model.assignSnoc_map (M.toSorted hM) (fun _ x => x.val) a ⟨x,hx⟩] at hi
      exact hi
    · intro h x
      apply (ih _).mpr
      erw [Model.assignSnoc_map (M.toSorted hM) (fun _ x => x.val) a x]
      exact h x.val x.property

end OrdinaryModel

namespace Model
variable {L} (D : Model.{u,v,w} L)
noncomputable def defaults (s : L.Sorts) : D.Carrier s := Classical.choice (D.nonempty s)
@[instance_reducible]
noncomputable def tagged (d : ∀ s, D.Carrier s) :
    OrdinaryModel L (Σ s, D.Carrier s) := by
  classical
  exact {
  funMap := fun f xs =>
    if h : ∀ i, (xs i).1 = L.input f i then
      ⟨L.output f, D.func f (fun i => cast (congrArg D.Carrier (h i)) (xs i).2)⟩
    else ⟨L.output f, d (L.output f)⟩
  RelMap := fun r xs => match r with
    | .sort s => (xs 0).1 = s
    | .symbol r => ∃ a : ∀ i, D.Carrier (L.profile r i),
        (∀ i, xs i = ⟨L.profile r i, a i⟩) ∧ D.rel r a }

@[instance_reducible]
noncomputable def toAmbient : OrdinaryModel L (Σ s, D.Carrier s) := D.tagged D.defaults

theorem tag_bijective (s : L.Sorts) (d : ∀ s, D.Carrier s) :
    Function.Bijective (fun x : D.Carrier s =>
      (⟨⟨s,x⟩,rfl⟩ : {z : (Σ t, D.Carrier t) // (D.tagged d).sort s z})) := by
  constructor
  · intro x y h
    exact sigma_mk_injective (congrArg Subtype.val h)
  · rintro ⟨⟨t,x⟩,h⟩
    change t = s at h
    subst t
    exact ⟨x,rfl⟩


theorem tagged_nonempty [Nonempty L.Sorts] : Nonempty (Σ s, D.Carrier s) := by
  obtain ⟨s⟩ := (inferInstance : Nonempty L.Sorts)
  obtain ⟨x⟩ := D.nonempty s
  exact ⟨⟨s,x⟩⟩

theorem tagged_typed (d : ∀ s, D.Carrier s) : (D.tagged d).Typed := by
  classical
  constructor
  · intro s
    obtain ⟨x⟩ := D.nonempty s
    exact ⟨⟨s,x⟩,rfl⟩
  · intro k f xs _
    dsimp only [OrdinaryModel.sort, OrdinaryModel.func, tagged]
    split <;> rfl

theorem tagged_nullary {f : L.Functions 0} (d : ∀ s, D.Carrier s) :
    (D.tagged d).func f Fin.elim0 = ⟨L.output f, D.func f (fun i => Fin.elim0 i)⟩ := by
  classical
  dsimp +instances only [OrdinaryModel.func, tagged, erasedLanguage]
  rw [dite_eq_left (by intro i; exact Fin.elim0 i)]
  congr 2
  exact Subsingleton.elim _ _

theorem eval_tagged (d : ∀ s, D.Carrier s) {n} {γ : Context L n} {s}
    (t : Term L γ s) (a : D.Assignment γ) :
    @FirstOrder.Language.Term.realize _ (Σ s, D.Carrier s) (D.tagged d) _
      (fun i => ⟨γ i,a i⟩) t.erase = ⟨s,D.eval a t⟩ := by
  classical
  induction t with
  | var i h => cases h; rfl
  | app f ts ih =>
    simp only [Term.erase, FirstOrder.Language.Term.realize]
    change (D.tagged d).func f _ = _
    have he : (fun i => @FirstOrder.Language.Term.realize _
        (Σ s,D.Carrier s) (D.tagged d) _ (fun j => ⟨γ j,a j⟩) (ts i).erase) =
        (fun i => (⟨L.input f i,D.eval a (ts i)⟩ : Σ s,D.Carrier s)) := funext ih
    rw [he]
    dsimp +instances only [OrdinaryModel.func, tagged, erasedLanguage]
    simp [eval]

private theorem tagged_rel (d : ∀ s, D.Carrier s) {k} (r : L.Relations k)
    (a : ∀ i, D.Carrier (L.profile r i)) :
    (D.tagged d).rel r (fun i => ⟨L.profile r i,a i⟩) ↔ D.rel r a := by
  change (∃ b, (∀ i, (⟨L.profile r i,a i⟩ : Σ s, D.Carrier s) =
    ⟨L.profile r i,b i⟩) ∧ D.rel r b) ↔ _
  constructor
  · rintro ⟨b,h,hb⟩
    have e : a = b := funext fun i => sigma_mk_injective (h i)
    simpa [e] using hb
  · intro h
    exact ⟨a,fun _ => rfl,h⟩

theorem realize_tagged (d : ∀ s, D.Carrier s) {n} {γ : Context L n}
    (p : Formula L γ) (a : D.Assignment γ) :
    D.Realize p a ↔ @BoundedFormula.Realize _ (Σ s, D.Carrier s) (D.tagged d) Empty _
      p.erase Empty.elim (fun i => ⟨γ i,a i⟩) := by
  induction p with
  | falsum => rfl
  | equal t r =>
    simp only [Formula.erase, Model.Realize, BoundedFormula.Realize,
      FirstOrder.Language.Term.realize_relabel, Function.comp_def, Sum.elim_inr,
      eval_tagged, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  | rel r ts =>
    simp only [Formula.erase, Model.Realize, BoundedFormula.Realize,
      FirstOrder.Language.Term.realize_relabel, Function.comp_def, Sum.elim_inr,
      eval_tagged]
    exact (D.tagged_rel d r (fun i => D.eval a (ts i))).symm
  | imp p q ihp ihq => exact imp_congr (ihp a) (ihq a)
  | @all n γ s p ih =>
    simp only [Formula.erase, Model.Realize, BoundedFormula.Realize,
      FirstOrder.Language.Term.realize, Sum.elim_inr, Fin.snoc_last]
    change (∀ x : D.Carrier s, D.Realize p (D.assignSnoc a x)) ↔
      ∀ x : (Σ s, D.Carrier s), x.1 = s →
        @BoundedFormula.Realize _ _ (D.tagged d) Empty _ p.erase Empty.elim
          (Fin.snoc (fun i => ⟨γ i,a i⟩) x)
    constructor
    · intro h x hx
      rcases x with ⟨t,x⟩
      change t = s at hx
      subst t
      have hi := (ih _).mp (h x)
      rw [D.assignSnoc_map (fun s x => (⟨s,x⟩ : Σ s, D.Carrier s))] at hi
      exact hi
    · intro h x
      apply (ih _).mpr
      rw [D.assignSnoc_map (fun s x => (⟨s,x⟩ : Σ s, D.Carrier s))]
      exact h ⟨s,x⟩ rfl

end Model

def relationalInclusion :
    (ManySortedLogic.erasedLanguage L.toSignature) →ᴸ erasedLanguage L where
  onFunction := fun _ f => Empty.elim f
  onRelation := fun _ r => match r with
    | .sort s => .sort s
    | .symbol r => .symbol r

theorem erase_includeRelational {n} {γ : Context L n}
    (p : ManySortedLogic.Formula L.toSignature γ) :
    (includeRelational L p).erase = (relationalInclusion L).onBoundedFormula p.erase := by
  induction p with
  | falsum => rfl
  | equal i j h => rfl
  | rel r args h => rfl
  | imp p q ihp ihq =>
    simp only [includeRelational, Formula.erase, ManySortedLogic.Formula.erase,
      LHom.onBoundedFormula, ihp, ihq]
  | all s p ih =>
    simp only [includeRelational, Formula.erase, ManySortedLogic.Formula.erase,
      LHom.onBoundedFormula, ih]
    rfl


def eraseTheory (T : Theory L) : (erasedLanguage L).Theory :=
  Formula.erase '' T ∪ typingAxioms L

theorem satisfiable_iff [Nonempty L.Sorts] (T : Theory L) :
    IsSatisfiable L T ↔ (eraseTheory L T).IsSatisfiable := by
  constructor
  · rintro ⟨D,hD⟩
    let U := Σ s, D.Carrier s
    let M : OrdinaryModel L U := D.toAmbient
    let _ := M
    let _ : Nonempty U := D.tagged_nonempty
    have htyping : U ⊨ typingAxioms L := (M.models_typingAxioms).mpr (D.tagged_typed D.defaults)
    let _ : U ⊨ eraseTheory L T := by
      constructor
      intro p hp
      rcases hp with ⟨q,hq,rfl⟩ | hp
      · have ht := (D.realize_tagged D.defaults q (fun i => Fin.elim0 i)).mp (hD q hq)
        simpa only [Sentence.Realize, FirstOrder.Language.Formula.Realize,
          Unique.eq_default] using ht
      · exact htyping.realize_of_mem p hp
    exact FirstOrder.Language.Theory.Model.isSatisfiable U
  · intro h
    let B := h.some
    let M : OrdinaryModel L B := B.struc
    have htyping : @FirstOrder.Language.Theory.Model _ B M (typingAxioms L) := by
      constructor
      intro p hp
      exact B.is_model.realize_of_mem p (Or.inr hp)
    have ht := (M.models_typingAxioms).mp htyping
    refine ⟨M.toSorted ht, ?_⟩
    intro p hp
    apply (M.realize_subtypes ht p (fun i => Fin.elim0 i)).mpr
    have htrue := B.is_model.realize_of_mem p.erase (Or.inl ⟨p,hp,rfl⟩)
    simpa only [Sentence.Realize, FirstOrder.Language.Formula.Realize,
      Unique.eq_default] using htrue


theorem compactness [Nonempty L.Sorts] (T : Theory L) :
    IsSatisfiable L T ↔
      ∀ T₀ : Finset (Sentence L), (T₀ : Set (Sentence L)) ⊆ T →
        IsSatisfiable L (T₀ : Set (Sentence L)) := by
  classical
  constructor
  · rintro ⟨D,ht⟩ T₀ hT₀
    exact ⟨D,fun p hp => ht p (hT₀ hp)⟩
  · intro h
    rw [satisfiable_iff, FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable]
    intro F hF
    let chooseOriginal (p : (erasedLanguage L).Sentence) : Finset (Sentence L) :=
      if hp : ∃ q ∈ T, Formula.erase q = p then {hp.choose} else ∅
    let T₀ := F.biUnion chooseOriginal
    have hT₀ : (T₀ : Set (Sentence L)) ⊆ T := by
      intro q hq
      obtain ⟨p,hp,hq⟩ := Finset.mem_biUnion.mp hq
      by_cases he : ∃ q ∈ T, Formula.erase q = p
      · have eq := (Finset.mem_singleton.mp (by simpa [chooseOriginal,he] using hq))
        exact eq ▸ he.choose_spec.1
      · simp [chooseOriginal,he] at hq
    have hmodel := (satisfiable_iff L _).mp (h T₀ hT₀)
    apply hmodel.mono
    intro p hp
    rcases hF hp with ⟨q,hq,he⟩ | ht
    · have hex : ∃ q ∈ T, Formula.erase q = p := ⟨q,hq,he⟩
      apply Or.inl
      refine ⟨hex.choose,?_,hex.choose_spec.2⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨p,hp,by simp [chooseOriginal,hex]⟩
    · exact Or.inr ht


namespace OrdinaryModel
variable {L} {U : Type w}
structure AgreeOnSorted (M N : OrdinaryModel L U) : Prop where
  sorts : ∀ s x, M.sort s x ↔ N.sort s x
  funcs : ∀ {k} (f : L.Functions k) (xs : Fin k → U),
    (∀ i, M.sort (L.input f i) (xs i)) → M.func f xs = N.func f xs
  rels : ∀ {k} (r : L.Relations k) (xs : Fin k → U),
    (∀ i, M.sort (L.profile r i) (xs i)) → (M.rel r xs ↔ N.rel r xs)

theorem eval_agree (M N : OrdinaryModel L U) (hM : M.Closed)
    (h : AgreeOnSorted M N) {n} {γ : Context L n} {s}
    (t : Term L γ s) (a : Fin n → U) (ha : M.Sorted γ a) :
    @FirstOrder.Language.Term.realize _ U M _ a t.erase =
      @FirstOrder.Language.Term.realize _ U N _ a t.erase := by
  induction t with
  | var i h => rfl
  | app f ts ih =>
    change M.func f (fun i => @FirstOrder.Language.Term.realize _ U M _ a (ts i).erase) =
      N.func f (fun i => @FirstOrder.Language.Term.realize _ U N _ a (ts i).erase)
    rw [h.funcs f _ (fun i => M.term_sort hM (ts i) a ha)]
    congr 1
    funext i
    exact ih i


theorem realize_agree (M N : OrdinaryModel L U) (hM : M.Closed)
    (h : AgreeOnSorted M N) {n} {γ : Context L n}
    (p : Formula L γ) (a : Fin n → U) (ha : M.Sorted γ a) :
    @BoundedFormula.Realize _ U M Empty _ p.erase Empty.elim a ↔
      @BoundedFormula.Realize _ U N Empty _ p.erase Empty.elim a := by
  induction p with
  | falsum => rfl
  | equal t r =>
    simp only [Formula.erase, BoundedFormula.Realize,
      FirstOrder.Language.Term.realize_relabel, Function.comp_def, Sum.elim_inr]
    rw [M.eval_agree N hM h t a ha, M.eval_agree N hM h r a ha]
  | rel r ts =>
    simp only [Formula.erase, BoundedFormula.Realize,
      FirstOrder.Language.Term.realize_relabel, Function.comp_def, Sum.elim_inr]
    have ht : (fun i => @FirstOrder.Language.Term.realize _ U M _ a (ts i).erase) =
        (fun i => @FirstOrder.Language.Term.realize _ U N _ a (ts i).erase) :=
      funext fun i => M.eval_agree N hM h (ts i) a ha
    have hr := h.rels r _ (fun i => M.term_sort hM (ts i) a ha)
    unfold OrdinaryModel.rel at hr
    rw [←ht]
    exact hr
  | imp p q ihp ihq => exact imp_congr (ihp a ha) (ihq a ha)
  | @all n γ s p ih =>
    simp only [Formula.erase, BoundedFormula.Realize, FirstOrder.Language.Term.realize,
      Sum.elim_inr, Fin.snoc_last]
    change (∀ x, M.sort s x → @BoundedFormula.Realize _ U M Empty _ p.erase Empty.elim
      (Fin.snoc a x)) ↔
      ∀ x, N.sort s x → @BoundedFormula.Realize _ U N Empty _ p.erase Empty.elim
        (Fin.snoc a x)
    have hs (x : U) (hx : M.sort s x) : M.Sorted (Fin.snoc γ s) (Fin.snoc a x) := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hx
      · simpa only [Fin.snoc_castSucc] using ha j
    constructor
    · intro hp x hx
      have hxM := (h.sorts s x).mpr hx
      exact (ih (Fin.snoc a x) (hs x hxM)).mp (hp x hxM)
    · intro hp x hx
      exact (ih (Fin.snoc a x) (hs x hx)).mpr (hp x ((h.sorts s x).mp hx))

end OrdinaryModel
end Lemmatheca.MathematicalLogic.ManySortedFunctions
