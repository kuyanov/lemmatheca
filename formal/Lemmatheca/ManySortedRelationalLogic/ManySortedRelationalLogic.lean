import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Fin.Tuple.Basic

/-! Relational many-sorted syntax and its guarded translation into shared first-order syntax. -/
namespace Lemmatheca.MathematicalLogic.ManySortedLogic

open FirstOrder FirstOrder.Language

universe u v w

structure Signature where
  Sorts : Type u
  Relations : ℕ → Type v
  profile : ∀ {k}, Relations k → Fin k → Sorts

variable (L : Signature.{u,v})

inductive ErasedRelation : ℕ → Type (max u v)
  | sort (s : L.Sorts) : ErasedRelation 1
  | symbol {k} (r : L.Relations k) : ErasedRelation k

def erasedLanguage : Language where
  Functions := fun _ => Empty
  Relations := ErasedRelation L

abbrev Model (U : Type w) := (erasedLanguage L).Structure U

namespace Model
variable {L} {U : Type w}
def sort (M : Model L U) (s : L.Sorts) (x : U) : Prop :=
  @Structure.RelMap (erasedLanguage L) U M 1 (.sort s) (fun _ => x)
def rel (M : Model L U) {k} (r : L.Relations k) (xs : Fin k → U) : Prop :=
  @Structure.RelMap (erasedLanguage L) U M k (.symbol r) xs
def NonemptySorts (M : Model L U) : Prop := ∀ s, ∃ x, M.sort s x
def Sorted (M : Model L U) {n} (γ : Fin n → L.Sorts) (a : Fin n → U) : Prop :=
  ∀ i, M.sort (γ i) (a i)
end Model

inductive Formula : {n : ℕ} → (Fin n → L.Sorts) → Type (max u v)
  | falsum {n γ} : @Formula n γ
  | equal {n γ} (i j : Fin n) (typed : γ i = γ j) : @Formula n γ
  | rel {n γ k} (r : L.Relations k) (args : Fin k → Fin n)
      (typed : ∀ i, γ (args i) = L.profile r i) : @Formula n γ
  | imp {n γ} (p q : @Formula n γ) : @Formula n γ
  | all {n γ} (s : L.Sorts) (p : @Formula (n+1) (Fin.snoc γ s)) : @Formula n γ

namespace Formula
variable {L}
def Realize {U : Type w} (M : Model L U) :
    {n : ℕ} → {γ : Fin n → L.Sorts} → Formula L γ → (Fin n → U) → Prop
  | _, _, .falsum, _ => False
  | _, _, .equal i j _, a => a i = a j
  | _, _, .rel r args _, a => M.rel r (a ∘ args)
  | _, _, .imp p q, a => Realize M p a → Realize M q a
  | _, _, .all s p, a => ∀ x, M.sort s x → Realize M p (Fin.snoc a x)

def erase : {n : ℕ} → {γ : Fin n → L.Sorts} → Formula L γ →
    (erasedLanguage L).BoundedFormula Empty n
  | _, _, .falsum => .falsum
  | _, _, .equal i j _ => .equal (.var (.inr i)) (.var (.inr j))
  | _, _, .rel r args _ => .rel (.symbol r) (fun i => .var (.inr (args i)))
  | _, _, .imp p q => (erase p).imp (erase q)
  | n, _, .all s p =>
      (BoundedFormula.imp (BoundedFormula.rel (ErasedRelation.sort s) (fun _ => .var (.inr (Fin.last n)))) (erase p)).all

theorem realize_erase {U : Type w} (M : Model L U) {n} {γ : Fin n → L.Sorts}
    (p : Formula L γ) (a : Fin n → U) :
    @BoundedFormula.Realize _ U M Empty _ p.erase Empty.elim a ↔ p.Realize M a := by
  induction p with
  | falsum => rfl
  | equal i j typed => rfl
  | rel r args typed => rfl
  | imp p q ihp ihq =>
      simp only [erase, BoundedFormula.Realize, Realize, ihp, ihq]
  | all s p ih =>
      simp only [erase, BoundedFormula.Realize, Term.realize, Sum.elim_inr,
        Fin.snoc_last, Realize]
      exact forall_congr' (fun x => imp_congr_right (fun _ => ih _))

theorem exists_guard {U : Type w} (M : Model L U) {n} {γ : Fin n → L.Sorts}
    (s : L.Sorts) (p : Formula L (Fin.snoc γ s)) (a : Fin n → U) :
    (¬ ∀ x, M.sort s x → ¬p.Realize M (Fin.snoc a x)) ↔
      ∃ x, M.sort s x ∧ p.Realize M (Fin.snoc a x) := by
  simp only [not_forall, Classical.not_not, exists_prop]
end Formula

structure FamilyModel where
  Carrier : L.Sorts → Type w
  rel : ∀ {k} (r : L.Relations k), (∀ i, Carrier (L.profile r i)) → Prop

namespace FamilyModel
variable {L} (M : FamilyModel.{u,v,w} L)
@[instance_reducible] def toAmbient : Model L (Σ s, M.Carrier s) where
  funMap := fun f => Empty.elim f
  RelMap := fun r xs => match r with
    | .sort s => (xs 0).1 = s
    | .symbol r => ∃ a : ∀ i, M.Carrier (L.profile r i),
        (∀ i, xs i = ⟨L.profile r i, a i⟩) ∧ M.rel r a

theorem tag_bijective (s : L.Sorts) :
    Function.Bijective (fun x : M.Carrier s =>
      (⟨⟨s,x⟩,rfl⟩ : {z : (Σ t, M.Carrier t) // z.1 = s})) := by
  constructor
  · intro x y h
    exact sigma_mk_injective (congrArg Subtype.val h)
  · rintro ⟨⟨t,x⟩,h⟩
    change t = s at h
    subst t
    exact ⟨x,rfl⟩

theorem nonemptySorts (h : ∀ s, Nonempty (M.Carrier s)) :
    M.toAmbient.NonemptySorts := by
  intro s
  obtain ⟨x⟩ := h s
  exact ⟨⟨s,x⟩,rfl⟩

def assignSnoc {n} {γ : Fin n → L.Sorts} (a : ∀ i, M.Carrier (γ i))
    {s : L.Sorts} (x : M.Carrier s) : ∀ i : Fin (n+1), M.Carrier ((Fin.snoc γ s : Fin (n+1) → L.Sorts) i) :=
  fun i => Fin.lastCases (by simpa using x) (fun j => by simpa using a j) i

def Realize : {n : ℕ} → {γ : Fin n → L.Sorts} →
    Formula L γ → (∀ i, M.Carrier (γ i)) → Prop
  | _, _, .falsum, _ => False
  | _, _, .equal i j _, a => HEq (a i) (a j)
  | _, _, .rel r args typed, a =>
      M.rel r (fun i => (typed i) ▸ a (args i))
  | _, _, .imp p q, a => Realize p a → Realize q a
  | _, _, .all _ p, a => ∀ x, Realize p (M.assignSnoc a x)

private theorem apply_carrier_cast {V : Type*} (f : ∀ s, M.Carrier s → V)
    {s t : L.Sorts} (h : s = t) (e : M.Carrier s = M.Carrier t) (x : M.Carrier s) :
    f t (cast e x) = f s x := by
  cases h
  rfl

private theorem assignSnoc_map {V : Type*}
    (f : ∀ s, M.Carrier s → V) {n} {γ : Fin n → L.Sorts}
    (a : ∀ i, M.Carrier (γ i)) {s} (x : M.Carrier s) :
    (fun i => f ((Fin.snoc γ s : Fin (n+1) → L.Sorts) i) (M.assignSnoc a x i)) =
      Fin.snoc (fun i => f (γ i) (a i)) (f s x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [assignSnoc, Fin.lastCases_last, Fin.snoc_last]
    exact M.apply_carrier_cast f (s := s)
      (t := (Fin.snoc γ s : Fin (n+1) → L.Sorts) (Fin.last n)) (by simp) _ x
  · simp only [assignSnoc, Fin.lastCases_castSucc, Fin.snoc_castSucc]
    exact M.apply_carrier_cast f (s := γ j)
      (t := (Fin.snoc γ s : Fin (n+1) → L.Sorts) j.castSucc) (by simp) _ (a j)

private theorem tag_cast {s t : L.Sorts} (h : s = t) (x : M.Carrier s) :
    (⟨t, h ▸ x⟩ : Σ s, M.Carrier s) = ⟨s,x⟩ := by
  cases h
  rfl

private theorem tagged_rel {k} (r : L.Relations k)
    (a : ∀ i, M.Carrier (L.profile r i)) :
    M.toAmbient.rel r (fun i => ⟨L.profile r i,a i⟩) ↔ M.rel r a := by
  change (∃ b, (∀ i, (⟨L.profile r i,a i⟩ : Σ s, M.Carrier s) =
    ⟨L.profile r i,b i⟩) ∧ M.rel r b) ↔ _
  constructor
  · rintro ⟨b,h,hb⟩
    have e : a = b := funext fun i => sigma_mk_injective (h i)
    simpa [e] using hb
  · intro h
    exact ⟨a,fun _ => rfl,h⟩

theorem realize_tagged {n} {γ : Fin n → L.Sorts} (p : Formula L γ)
    (a : ∀ i, M.Carrier (γ i)) :
    p.Realize M.toAmbient (fun i => ⟨γ i,a i⟩) ↔ M.Realize p a := by
  induction p with
  | falsum => rfl
  | equal i j typed =>
      change (⟨_,a i⟩ : Σ s, M.Carrier s) = ⟨_,a j⟩ ↔ HEq (a i) (a j)
      rw [Sigma.mk.inj_iff]
      exact and_iff_right typed
  | rel r args typed =>
      have e : (fun i => (⟨_,a (args i)⟩ : Σ s, M.Carrier s)) =
          (fun i => ⟨L.profile r i,(typed i) ▸ a (args i)⟩) := by
        funext i
        exact (M.tag_cast (typed i) (a (args i))).symm
      change M.toAmbient.rel r (fun i => ⟨_,a (args i)⟩) ↔ _
      rw [e]
      exact M.tagged_rel r _
  | imp p q ihp ihq =>
      simp only [Formula.Realize, Realize, ihp, ihq]
  | all s p ih =>
      change (∀ x : (Σ s, M.Carrier s), x.1 = s →
        p.Realize M.toAmbient (Fin.snoc (fun i => ⟨_,a i⟩) x)) ↔
        ∀ x : M.Carrier s, M.Realize p (M.assignSnoc a x)
      constructor
      · intro h x
        apply (ih _).mp
        rw [M.assignSnoc_map (fun s x => (⟨s,x⟩ : Σ s, M.Carrier s))]
        exact h ⟨s,x⟩ rfl
      · intro h x hx
        rcases x with ⟨t,x⟩
        change t = s at hx
        subst t
        have hi := (ih _).mpr (h x)
        rw [M.assignSnoc_map (fun s x => (⟨s,x⟩ : Σ s, M.Carrier s))] at hi
        exact hi
end FamilyModel

namespace Model
variable {L} {U : Type w}
abbrev toFamily (M : Model L U) : FamilyModel L where
  Carrier := fun s => {x : U // M.sort s x}
  rel := fun r xs => M.rel r (fun i => (xs i).val)

theorem toFamily_nonempty (M : Model L U) (h : M.NonemptySorts) (s : L.Sorts) :
    Nonempty (M.toFamily.Carrier s) := by
  obtain ⟨x,hx⟩ := h s
  exact ⟨⟨x,hx⟩⟩

private theorem subtype_heq (M : Model L U) {s t : L.Sorts} (h : s = t)
    (x : M.toFamily.Carrier s) (y : M.toFamily.Carrier t) :
    HEq x y ↔ x.val = y.val := by
  cases h
  rw [heq_eq_eq]
  exact Subtype.ext_iff

private theorem subtype_cast_val (M : Model L U) {s t : L.Sorts} (h : s = t)
    (x : M.toFamily.Carrier s) :
    ((h ▸ x : M.toFamily.Carrier t)).val = x.val := by
  cases h
  rfl

theorem realize_subtypes (M : Model L U) {n} {γ : Fin n → L.Sorts}
    (p : Formula L γ) (a : ∀ i, M.toFamily.Carrier (γ i)) :
    M.toFamily.Realize p a ↔ p.Realize M (fun i => (a i).val) := by
  induction p with
  | falsum => rfl
  | equal i j typed =>
      change HEq (a i) (a j) ↔ (a i).val = (a j).val
      exact subtype_heq M typed (a i) (a j)
  | rel r args typed =>
      change M.rel r (fun i => ((typed i) ▸ a (args i)).val) ↔ _
      have e : (fun i => ((typed i) ▸ a (args i)).val) =
          (fun i => (a (args i)).val) := by
        funext i
        exact subtype_cast_val M (typed i) (a (args i))
      rw [e]
      rfl
  | imp p q ihp ihq =>
      simp only [FamilyModel.Realize, Formula.Realize, ihp, ihq]
  | all s p ih =>
      change (∀ x : {x : U // M.sort s x},
        M.toFamily.Realize p (M.toFamily.assignSnoc a x)) ↔
        ∀ x, M.sort s x → p.Realize M (Fin.snoc (fun i => (a i).val) x)
      constructor
      · intro h x hx
        have hi := (ih _).mp (h ⟨x,hx⟩)
        rw [FamilyModel.assignSnoc_map M.toFamily (fun _ x => x.val)] at hi
        exact hi
      · intro h x
        apply (ih _).mpr
        rw [FamilyModel.assignSnoc_map M.toFamily (fun _ x => x.val)]
        exact h x.val x.property

theorem all_falsum_iff_empty (M : Model L U) {n} {γ : Fin n → L.Sorts}
    (s : L.Sorts) (a : Fin n → U) :
    (Formula.all s (Formula.falsum : Formula L (Fin.snoc γ s))).Realize M a ↔
      ¬∃ x, M.sort s x := by
  simp only [Formula.Realize, not_exists]
end Model

abbrev Sentence := Formula L (Fin.elim0 : Fin 0 → L.Sorts)
abbrev Theory := Set (Sentence L)

def sortAxiom (s : L.Sorts) : (erasedLanguage L).Sentence :=
  (BoundedFormula.rel (L := erasedLanguage L) (ErasedRelation.sort s) (fun _ => .var (.inr (0 : Fin 1)))).ex

def eraseTheory (T : Theory L) : (erasedLanguage L).Theory :=
  Formula.erase '' T ∪ Set.range (sortAxiom L)

namespace Model
variable {L} {U : Type w}
def Models (M : Model L U) (T : Theory L) : Prop :=
  ∀ p ∈ T, Formula.Realize M p Fin.elim0

theorem realizes_sortAxiom (M : Model L U) (s : L.Sorts) :
    @Sentence.Realize _ U M (sortAxiom L s) ↔ ∃ x, M.sort s x := by
  let _ := M
  simp [sortAxiom, Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.realize_ex, BoundedFormula.Realize, Term.realize,
    Model.sort, Fin.snoc]

private theorem realizes_eraseSentence (M : Model L U) (p : Sentence L) :
    @FirstOrder.Language.Sentence.Realize _ U M p.erase ↔
      p.Realize M Fin.elim0 := by
  have he : (default : Empty → U) = Empty.elim := Subsingleton.elim _ _
  have hf : (default : Fin 0 → U) = Fin.elim0 := Subsingleton.elim _ _
  simpa only [FirstOrder.Language.Sentence.Realize,
    FirstOrder.Language.Formula.Realize,he,hf] using Formula.realize_erase M p Fin.elim0

theorem models_eraseTheory (M : Model L U) (T : Theory L) :
    @FirstOrder.Language.Theory.Model _ U M (eraseTheory L T) ↔
      M.Models T ∧ M.NonemptySorts := by
  let _ := M
  rw [FirstOrder.Language.Theory.model_iff]
  constructor
  · intro h
    constructor
    · intro p hp
      have hp' := h p.erase (Or.inl ⟨p,hp,rfl⟩)
      exact (realizes_eraseSentence M p).mp hp'
    · intro s
      exact (M.realizes_sortAxiom s).mp (h (sortAxiom L s) (Or.inr ⟨s,rfl⟩))
  · rintro ⟨ht,hs⟩ p (⟨q,hq,rfl⟩ | ⟨s,rfl⟩)
    · exact (realizes_eraseSentence M q).mpr (ht q hq)
    · exact (M.realizes_sortAxiom s).mpr (hs s)
end Model

def IsSatisfiable (T : Theory L) : Prop :=
  ∃ (U : Type (max u v)) (M : Model L U), Nonempty U ∧ M.NonemptySorts ∧ M.Models T

theorem satisfiable_iff (T : Theory L) :
    IsSatisfiable L T ↔ (eraseTheory L T).IsSatisfiable := by
  constructor
  · rintro ⟨U,M,hn,hs,ht⟩
    let _ := M
    let _ := hn
    let _ : U ⊨ eraseTheory L T := (M.models_eraseTheory T).mpr ⟨ht,hs⟩
    exact FirstOrder.Language.Theory.Model.isSatisfiable U
  · intro h
    let B := h.some
    have hb := (Model.models_eraseTheory B.struc T).mp B.is_model
    exact ⟨B,B.struc,B.nonempty',hb.2,hb.1⟩

theorem compactness (T : Theory L) :
    IsSatisfiable L T ↔
      ∀ T₀ : Finset (Sentence L), (T₀ : Set (Sentence L)) ⊆ T →
        IsSatisfiable L (T₀ : Set (Sentence L)) := by
  classical
  constructor
  · rintro ⟨U,M,hn,hs,ht⟩ T₀ hT₀
    exact ⟨U,M,hn,hs,fun p hp => ht p (hT₀ hp)⟩
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
    rcases hF hp with ⟨q,hq,he⟩ | ⟨s,rfl⟩
    · have hex : ∃ q ∈ T, Formula.erase q = p := ⟨q,hq,he⟩
      apply Or.inl
      refine ⟨hex.choose,?_,hex.choose_spec.2⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨p,hp,by simp [chooseOriginal,hex]⟩
    · exact Or.inr ⟨s,rfl⟩

end Lemmatheca.MathematicalLogic.ManySortedLogic
