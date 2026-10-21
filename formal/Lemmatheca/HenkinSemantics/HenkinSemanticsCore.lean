import Lemmatheca.SecondOrderLogic.SecondOrderLogic
import Lemmatheca.FirstOrderProofs.FirstOrderProofs

/-! General second-order semantics and its actual guarded first-order translation. -/
namespace Lemmatheca.MathematicalLogic.HenkinSemantics
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.SecondOrderLogic
noncomputable section
universe u v w w'

inductive ApplicationRelation (L : Language.{u,v}) : ℕ → Type (max u v)
  | original {n : ℕ} : L.Relations n → ApplicationRelation L n
  | individual : ApplicationRelation L 1
  | relationSort (n : ℕ) : ApplicationRelation L 1
  | application (n : ℕ) : ApplicationRelation L (n+1)

def applicationLanguage (L : Language.{u,v}) : Language.{u,max u v} where
  Functions := L.Functions
  Relations := ApplicationRelation L

abbrev Name := ℕ ⊕ (ℕ × ℕ)

def individual {L : Language} {α : Type*} {k : ℕ}
    (t : (applicationLanguage L).Term (α ⊕ Fin k)) :
    (applicationLanguage L).BoundedFormula α k := .rel .individual (fun _ => t)
def relationSort {L : Language} {α : Type*} {k : ℕ} (n : ℕ)
    (t : (applicationLanguage L).Term (α ⊕ Fin k)) :
    (applicationLanguage L).BoundedFormula α k := .rel (.relationSort n) (fun _ => t)

def translateTerm {L : Language} {α β : Type*} (f : α → β) :
    L.Term α → (applicationLanguage L).Term β
  | .var x => .var (f x)
  | .func g ts => .func g (fun i => translateTerm f (ts i))

def translateFirstOrder {L : Language} : {k : ℕ} →
    L.BoundedFormula ℕ k → (applicationLanguage L).BoundedFormula Name k
  | _, .falsum => .falsum
  | _, .equal t s => .equal (translateTerm (Sum.map Sum.inl id) t)
      (translateTerm (Sum.map Sum.inl id) s)
  | _, .rel R ts => .rel (.original R)
      (fun i => translateTerm (Sum.map Sum.inl id) (ts i))
  | _, .imp φ ψ => .imp (translateFirstOrder φ) (translateFirstOrder ψ)
  | k, .all φ => .all ((individual (.var (.inr (Fin.last k)))).imp
      (translateFirstOrder φ))

def allName {L : Language} (x : Name) (φ : L.Formula Name) : L.Formula Name :=
  (BoundedFormula.relabel (n:=1) (k:=0)
    (fun y => if y=x then Sum.inr 0 else Sum.inl y) φ).all

def translate {L : Language} : Formula L → (applicationLanguage L).Formula Name
  | .firstOrder φ => translateFirstOrder φ
  | .relation (n:=n) X ts => Relations.formula (L:=applicationLanguage L) (.application n)
      (Fin.cons (.var (.inr (n,X))) (fun i => translateTerm Sum.inl (ts i)))
  | .falsum => .falsum
  | .imp φ ψ => .imp (translate φ) (translate ψ)
  | .allIndividual x φ => allName (.inl x)
      ((individual (.var (.inl (.inl x)))).imp (translate φ))
  | .allRelation n X φ => allName (.inr (n,X))
      ((relationSort n (.var (.inl (.inr (n,X))))).imp (translate φ))

variable {L : Language.{u,v}} {M : Type w} {U : Type w'}
variable [L.Structure M] [(applicationLanguage L).Structure U]

def IsIndividual (x : U) : Prop := Structure.RelMap (L:=applicationLanguage L) (ApplicationRelation.individual (L:=L)) (fun _ => x)
def IsRelation (n : ℕ) (x : U) : Prop := Structure.RelMap (L:=applicationLanguage L) (ApplicationRelation.relationSort (L:=L) n) (fun _ => x)
def extension (e : M → U) (n : ℕ) (A : U) : (Fin n → M) → Prop :=
  fun xs => Structure.RelMap (L:=applicationLanguage L) (ApplicationRelation.application (L:=L) n) (Fin.cons A (e ∘ xs))

/-- A semantic presentation includes both directions of each quantifier's range. -/
structure Presentation (D : RelationDomains M) where
  embed : M → U
  injective : Function.Injective embed
  individuals : ∀ x : U, IsIndividual (L:=L) x ↔ ∃ m, embed m = x
  functions : ∀ {n} (f : L.Functions n) (xs : Fin n → M),
    Structure.funMap (L:=applicationLanguage L) f (embed ∘ xs) =
      embed (Structure.funMap f xs)
  relations : ∀ {n} (R : L.Relations n) (xs : Fin n → M),
    Structure.RelMap (L:=applicationLanguage L) (ApplicationRelation.original R) (embed ∘ xs) ↔ Structure.RelMap R xs
  relationDomains : ∀ n R, R ∈ D n ↔ ∃ A : U, IsRelation (L:=L) n A ∧ extension (L:=L) embed n A = R

def AssignmentCorresponds {D : RelationDomains M} (P : Presentation (L:=L) (U:=U) D)
    (a : ℕ → M) (r : RelationAssignment M) (s : Name → U) : Prop :=
  (∀ x, s (.inl x) = P.embed (a x)) ∧
  (∀ n X, IsRelation (L:=L) n (s (.inr (n,X))) ∧
    extension (L:=L) P.embed n (s (.inr (n,X))) = r n X)

theorem allName_realize (x : Name) (φ : (applicationLanguage L).Formula Name) (a : Name → U) :
    (allName x φ).Realize a ↔ ∀ b : U, φ.Realize (Function.update a x b) := by
  simp only [allName, FirstOrder.Language.Formula.Realize, BoundedFormula.realize_all]
  apply forall_congr'
  intro b
  rw [BoundedFormula.realize_relabel]
  have ha : (Sum.elim a (Fin.snoc (default : Fin 0 → U) b ∘ Fin.castAdd 0) ∘
      fun z => if z=x then Sum.inr (0 : Fin 1) else Sum.inl z) = Function.update a x b := by
    funext z
    by_cases hz : z=x
    · subst z; simp [Function.comp_apply, Fin.snoc, Fin.castAdd]
    · simp [Function.comp_apply, hz]
  rw [ha]
  exact FirstOrder.Language.Formula.boundedFormula_realize_eq_realize _ _ _


theorem Presentation.translateTerm_realize {D : RelationDomains M}
    (P : Presentation (L:=L) (U:=U) D) {α β : Type*} (f : α → β)
    (t : L.Term α) (a : α → M) (b : β → U)
    (h : ∀ x, b (f x) = P.embed (a x)) :
    (translateTerm f t).realize b = P.embed (t.realize a) := by
  induction t with
  | var x => exact h x
  | func g ts ih =>
    simp only [translateTerm, Term.realize]
    have hh : (fun i => (translateTerm f (ts i)).realize b) =
        P.embed ∘ (fun i => (ts i).realize a) := funext ih
    rw [hh]
    exact P.functions g _


theorem Presentation.translateFirstOrder_realize {D : RelationDomains M}
    (P : Presentation (L:=L) (U:=U) D) {k : ℕ} (φ : L.BoundedFormula ℕ k)
    (a : ℕ → M) (s : Name → U) (b : Fin k → M)
    (h : ∀ x, s (.inl x) = P.embed (a x)) :
    (translateFirstOrder φ).Realize s (P.embed ∘ b) ↔ φ.Realize a b := by
  induction φ generalizing a s with
  | falsum => rfl
  | equal t q =>
    have ht (t : L.Term (ℕ ⊕ Fin _)) :
        (translateTerm (Sum.map Sum.inl id) t).realize (Sum.elim s (P.embed ∘ b)) =
          P.embed (t.realize (Sum.elim a b)) := by
      apply P.translateTerm_realize
      intro x
      cases x with
      | inl x => exact h x
      | inr i => rfl
    simp only [translateFirstOrder, BoundedFormula.Realize, ht]
    exact P.injective.eq_iff
  | rel R ts =>
    have ht : (fun i => (translateTerm (Sum.map Sum.inl id) (ts i)).realize
        (Sum.elim s (P.embed ∘ b))) = P.embed ∘ (fun i => (ts i).realize (Sum.elim a b)) := by
      funext i
      apply P.translateTerm_realize
      intro x
      cases x with
      | inl x => exact h x
      | inr j => rfl
    simp only [translateFirstOrder, BoundedFormula.Realize]
    rw [ht]
    exact P.relations R _
  | imp φ ψ ihφ ihψ =>
    exact imp_congr (ihφ a s b h) (ihψ a s b h)
  | @all k φ ih =>
    have hg (u : U) :
        (individual (.var (.inr (Fin.last k))) : (applicationLanguage L).BoundedFormula Name (k+1)).Realize
          s (Fin.snoc (P.embed ∘ b) u) ↔ IsIndividual (L:=L) u := by
      change Structure.RelMap (L:=applicationLanguage L) ApplicationRelation.individual
        (fun _ => Fin.snoc (α := fun _ : Fin (k+1) => U) (P.embed ∘ b) u (Fin.last k)) ↔ _
      simp only [Fin.snoc_last]
      rfl
    simp only [translateFirstOrder, BoundedFormula.realize_all, BoundedFormula.realize_imp, hg]
    change (∀ u : U, IsIndividual (L:=L) u →
      (translateFirstOrder φ).Realize s (Fin.snoc (P.embed ∘ b) u)) ↔
      ∀ m : M, φ.Realize a (Fin.snoc b m)
    constructor
    · intro hall m
      apply (ih a s (Fin.snoc b m) h).mp
      simpa only [Fin.comp_snoc] using hall (P.embed m) ((P.individuals _).mpr ⟨m,rfl⟩)
    · intro hall u hu
      obtain ⟨m,rfl⟩ := (P.individuals u).mp hu
      simpa only [Fin.comp_snoc] using (ih a s (Fin.snoc b m) h).mpr (hall m)


private theorem correspond_update_individual {D : RelationDomains M}
    (P : Presentation (L:=L) (U:=U) D) (a : ℕ → M) (r : RelationAssignment M) (s : Name → U)
    (h : AssignmentCorresponds P a r s) (x : ℕ) (m : M) :
    AssignmentCorresponds P (Function.update a x m) r
      (Function.update s (.inl x) (P.embed m)) := by
  constructor
  · intro y
    by_cases hy : y=x
    · subst y; simp
    · simpa [hy] using h.1 y
  · intro n X
    simpa using h.2 n X

private theorem correspond_update_relation {D : RelationDomains M}
    (P : Presentation (L:=L) (U:=U) D) (a : ℕ → M) (r : RelationAssignment M) (s : Name → U)
    (h : AssignmentCorresponds P a r s) (n X : ℕ) (A : U) (hA : IsRelation (L:=L) n A) :
    AssignmentCorresponds P a (updateRelation r n X (extension (L:=L) P.embed n A))
      (Function.update s (.inr (n,X)) A) := by
  constructor
  · intro y; simpa using h.1 y
  · intro k Y
    by_cases hp : (k,Y)=(n,X)
    · have hk : k=n := congrArg Prod.fst hp
      subst k
      have hY : Y=X := congrArg Prod.snd hp
      subst Y
      simpa only [Function.update_self, updateRelation_same, and_true] using hA
    · have hn : (Sum.inr (k,Y) : Name) ≠ .inr (n,X) := fun he => hp (Sum.inr.inj he)
      rw [Function.update_of_ne hn, updateRelation_other r n X _ k Y hp]
      exact h.2 k Y

theorem Presentation.translate_realize {D : RelationDomains M}
    (P : Presentation (L:=L) (U:=U) D) (φ : Formula L)
    (a : ℕ → M) (r : RelationAssignment M) (s : Name → U)
    (h : AssignmentCorresponds P a r s) :
    (translate φ).Realize s ↔ realize D a r φ := by
  induction φ generalizing a r s with
  | firstOrder φ =>
    simpa only [translate, realize, FirstOrder.Language.Formula.Realize,
      Subsingleton.elim (P.embed ∘ (default : Fin 0 → M)) (default : Fin 0 → U)] using
        P.translateFirstOrder_realize φ a s default h.1
  | @relation n X ts =>
    rw [translate]
    rw [FirstOrder.Language.Formula.realize_rel (L:=applicationLanguage L) (R:=ApplicationRelation.application n)]
    have ht : (fun i => (translateTerm Sum.inl (ts i)).realize s) =
        P.embed ∘ (fun i => (ts i).realize a) := by
      funext i
      exact P.translateTerm_realize Sum.inl (ts i) a s h.1
    let terms : Fin (n+1) → (applicationLanguage L).Term Name :=
      Fin.cons (.var (.inr (n,X))) (fun j => translateTerm Sum.inl (ts j))
    have hv : (fun i => (terms i).realize s) =
        Fin.cons (s (.inr (n,X))) (P.embed ∘ (fun i => (ts i).realize a)) := by
      rw [← ht]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    change Structure.RelMap (L:=applicationLanguage L) (.application n) _ ↔ _
    rw [hv]
    change extension (L:=L) P.embed n (s (.inr (n,X))) _ ↔ _
    rw [(h.2 n X).2]
    rfl
  | falsum => rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ a r s h) (ihψ a r s h)
  | allIndividual x φ ih =>
    simp only [translate, allName_realize]
    change (∀ u : U, IsIndividual (L:=L) (Function.update s (.inl x) u (.inl x)) →
      (translate φ).Realize (Function.update s (.inl x) u)) ↔ _
    simp only [Function.update_self]
    constructor
    · intro hall m
      apply (ih _ _ _ (correspond_update_individual P a r s h x m)).mp
      exact hall (P.embed m) ((P.individuals _).mpr ⟨m,rfl⟩)
    · intro hall u hu
      obtain ⟨m,rfl⟩ := (P.individuals u).mp hu
      exact (ih _ _ _ (correspond_update_individual P a r s h x m)).mpr (hall m)
  | allRelation n X φ ih =>
    simp only [translate, allName_realize]
    change (∀ A : U, IsRelation (L:=L) n (Function.update s (.inr (n,X)) A (.inr (n,X))) →
      (translate φ).Realize (Function.update s (.inr (n,X)) A)) ↔ _
    simp only [Function.update_self]
    constructor
    · intro hall R hR
      obtain ⟨A,hA,rfl⟩ := (P.relationDomains n R).mp hR
      exact (ih _ _ _ (correspond_update_relation P a r s h n X A hA)).mp (hall A hA)
    · intro hall A hA
      exact (ih _ _ _ (correspond_update_relation P a r s h n X A hA)).mpr
        (hall _ ((P.relationDomains n _).mpr ⟨A,hA,rfl⟩))


/-- Ordinary models must provide nonempty sorts and closure of original functions. -/
structure Admissible : Prop where
  individuals : ∃ x : U, IsIndividual (L:=L) x
  relations : ∀ n, ∃ A : U, IsRelation (L:=L) n A
  functions : ∀ {n} (f : L.Functions n) (xs : Fin n → U),
    (∀ i, IsIndividual (L:=L) (xs i)) → IsIndividual (L:=L) (Structure.funMap (L:=applicationLanguage L) f xs)

abbrev DecodedIndividual (L : Language) (U : Type*) [(applicationLanguage L).Structure U] :=
  {x : U // IsIndividual (L:=L) x}

@[instance_reducible]
def decodedStructure (h : Admissible (L:=L) (U:=U)) : L.Structure (DecodedIndividual L U) where
  funMap f xs := ⟨Structure.funMap (L:=applicationLanguage L) f (fun i => (xs i).val), h.functions f _ (fun i => (xs i).property)⟩
  RelMap R xs := Structure.RelMap (L:=applicationLanguage L) (ApplicationRelation.original R) (fun i => (xs i).val)

def decodedDomains : RelationDomains (DecodedIndividual L U) :=
  fun n => {R | ∃ A : U, IsRelation (L:=L) n A ∧ extension (L:=L) Subtype.val n A = R}

def decodedPresentation (h : Admissible (L:=L) (U:=U)) :
    letI := decodedStructure h
    Presentation (L:=L) (U:=U) (decodedDomains (L:=L) (U:=U)) := by
  letI := decodedStructure h
  exact ⟨Subtype.val, Subtype.val_injective,
    fun x => ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨m,hm⟩ => hm ▸ m.property⟩,
    fun _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

theorem decoded_nonempty (h : Admissible (L:=L) (U:=U)) :
    Nonempty (DecodedIndividual L U) ∧ ∀ n, (decodedDomains (L:=L) (U:=U) n).Nonempty := by
  obtain ⟨x,hx⟩ := h.individuals
  refine ⟨⟨⟨x,hx⟩⟩,?_⟩
  intro n
  obtain ⟨A,hA⟩ := h.relations n
  exact ⟨extension (L:=L) Subtype.val n A, A,hA,rfl⟩


/-- Extensional equality of relation objects is exactly equality of their extensions. -/
def Extensional : Prop := ∀ n (A B : U),
  IsRelation (L:=L) n A → IsRelation (L:=L) n B →
  (∀ xs : Fin n → DecodedIndividual L U,
    extension (L:=L) Subtype.val n A xs ↔ extension (L:=L) Subtype.val n B xs) → A=B

theorem extensional_iff_injective : Extensional (L:=L) (U:=U) ↔
    ∀ n, Function.Injective (fun A : {x : U // IsRelation (L:=L) n x} =>
      extension (L:=L) (M:=DecodedIndividual L U) Subtype.val n A.val) := by
  constructor
  · intro h n A B he
    apply Subtype.ext
    exact h n A.val B.val A.property B.property (fun xs => Iff.of_eq (congrFun he xs))
  · intro h n A B hA hB he
    have hab : (⟨A,hA⟩ : {x : U // IsRelation (L:=L) n x}) = ⟨B,hB⟩ :=
      h n (funext (fun xs => propext (he xs)))
    exact congrArg Subtype.val hab



/-- One syntactic comprehension instance, leaving its parameters free. -/
def comprehensionInstance (n X : ℕ) (φ : Formula L) : Formula L :=
  .exRelation n X (allIndividuals n ((Formula.relation X (fun i : Fin n => .var i.val)).iff φ))

def ComprehensionFor (D : RelationDomains M) (n : ℕ) (φ : Formula L) : Prop :=
  ∀ a : ℕ → M, ∀ r : RelationAssignment M,
    (∀ k X, r k X ∈ D k) →
    ∃ R ∈ D n, ∀ b : Fin n → M, R b ↔ realize D (fill n a b) r φ

theorem comprehensionInstance_realize (D : RelationDomains M) (n X : ℕ) (φ : Formula L)
    (hfresh : (n,X) ∉ freeRelation φ) (a : ℕ → M) (r : RelationAssignment M) :
    realize D a r (comprehensionInstance n X φ) ↔
      ∃ R ∈ D n, ∀ xs : Fin n → M, R xs ↔ realize D (fill n a xs) r φ := by
  have hagree (R : (Fin n → M) → Prop) (xs : Fin n → M) :
      realize D (fill n a xs) (updateRelation r n X R) φ ↔ realize D (fill n a xs) r φ := by
    apply realize_agree
    · intro x _; rfl
    · intro p hp
      exact updateRelation_other r n X R p.1 p.2 (fun he => hfresh (he ▸ hp))
  simp only [comprehensionInstance, realize_exRelation, realize_allIndividuals, realize_iff,
    realize, updateRelation_same, hagree]
  have ht (xs : Fin n → M) : (fun i : Fin n => fill n a xs i.val) = xs := by
    funext i
    simp [fill, i.isLt]
  simp only [Term.realize, ht]


theorem full_comprehension (n X : ℕ) (φ : Formula L)
    (hfresh : (n,X) ∉ freeRelation φ) (a : ℕ → M) (r : RelationAssignment M) :
    fullRealize a r (comprehensionInstance n X φ) := by
  apply (comprehensionInstance_realize (fun _ => Set.univ) n X φ hfresh a r).mpr
  exact ⟨fun xs => realize (fun _ => Set.univ) (fill n a xs) r φ, Set.mem_univ _, fun _ => Iff.rfl⟩


theorem full_comprehensionFor (n : ℕ) (φ : Formula L) :
    ComprehensionFor (M:=M) (fun _ => Set.univ) n φ := by
  intro a r _
  exact ⟨fun xs => realize (fun _ => Set.univ) (fill n a xs) r φ, Set.mem_univ _, fun _ => Iff.rfl⟩


theorem empty_unary_omits_comprehension [Nonempty M] :
    ¬ ∃ R ∈ ({fun _ : Fin 1 → M => False} : Set ((Fin 1 → M) → Prop)),
      ∀ b, R b ↔ b 0 = b 0 := by
  rintro ⟨R,hR,h⟩
  obtain rfl := Set.mem_singleton_iff.mp hR
  exact (h (fun _ => Classical.choice ‹Nonempty M›)).mpr rfl


abbrev ForwardCarrier (D : RelationDomains M) := M ⊕ ((n : ℕ) × {R // R ∈ D n})

def forwardIndividual [Nonempty M] {D : RelationDomains M} : ForwardCarrier D → M
  | .inl m => m
  | .inr _ => Classical.choice inferInstance

def forwardExtension {D : RelationDomains M} (n : ℕ) :
    ForwardCarrier D → (Fin n → M) → Prop
  | .inl _ => fun _ => False
  | .inr ⟨k,R⟩ => if h : k=n then fun xs => R.val (xs ∘ Fin.cast h) else fun _ => False

@[instance_reducible]
def forwardStructure [Nonempty M] (D : RelationDomains M) :
    (applicationLanguage L).Structure (ForwardCarrier D) where
  funMap f xs := .inl (Structure.funMap (L:=L) f (forwardIndividual ∘ xs))
  RelMap := fun R xs => match R with
    | .original R => Structure.RelMap (L:=L) R (forwardIndividual ∘ xs)
    | .individual => match xs 0 with | .inl _ => True | .inr _ => False
    | .relationSort n => match xs 0 with | .inl _ => False | .inr ⟨k,_⟩ => k=n
    | .application n => forwardExtension n (xs 0) (fun i => forwardIndividual (xs i.succ))

theorem exists_forward_presentation [Nonempty M] (D : RelationDomains M) :
    letI := forwardStructure (L:=L) D
    ∃ P : Presentation (L:=L) (U:=ForwardCarrier D) D, P.embed = Sum.inl := by
  let _ := forwardStructure (L:=L) D
  have hext (n : ℕ) (R : {R // R ∈ D n}) :
      extension (L:=L) Sum.inl n (Sum.inr ⟨n,R⟩ : ForwardCarrier D) = R.val := by
    funext xs
    change forwardExtension n (Sum.inr ⟨n,R⟩ : ForwardCarrier D)
      (fun i => forwardIndividual (Sum.inl (xs i) : ForwardCarrier D)) = R.val xs
    simp [forwardExtension, forwardIndividual]
  refine ⟨⟨Sum.inl, Sum.inl_injective, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro x
    cases x with
    | inl m => exact ⟨fun _ => ⟨m,rfl⟩,fun _ => trivial⟩
    | inr R =>
      change False ↔ ∃ m : M, Sum.inl m = (Sum.inr R : ForwardCarrier D)
      simp
  · intro n f xs
    rfl
  · intro n R xs
    rfl
  · intro n R
    constructor
    · intro hR
      exact ⟨Sum.inr ⟨n,⟨R,hR⟩⟩, rfl, hext n ⟨R,hR⟩⟩
    · rintro ⟨A,hA,hR⟩
      cases A with
      | inl m => exact hA.elim
      | inr A =>
        rcases A with ⟨k,A⟩
        change k=n at hA
        subst k
        rw [hext] at hR
        exact hR ▸ A.property


def individualExists (L : Language) : (applicationLanguage L).Sentence :=
  (individual (.var (.inr 0)) : (applicationLanguage L).BoundedFormula Empty 1).ex

def relationExists (L : Language) (n : ℕ) : (applicationLanguage L).Sentence :=
  (relationSort n (.var (.inr 0)) : (applicationLanguage L).BoundedFormula Empty 1).ex

def functionClosure {n : ℕ} (f : L.Functions n) : (applicationLanguage L).Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin n)
    (((FirstOrder.Language.Formula.iInf (fun i : Fin n =>
      (individual (.var (.inl i)) : (applicationLanguage L).Formula (Fin n)))).imp
      (individual (.func f (fun i => .var (.inl i))))).relabel Sum.inr)

def backgroundTheory (L : Language) : (applicationLanguage L).Theory :=
  {individualExists L} ∪ Set.range (relationExists L) ∪
    {φ | ∃ n, ∃ f : L.Functions n, functionClosure f = φ}

theorem background_model_iff : U ⊨ backgroundTheory L ↔ Admissible (L:=L) (U:=U) := by
  have hi : U ⊨ individualExists L ↔ ∃ x : U, IsIndividual (L:=L) x := by
    simp [individualExists, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      individual, BoundedFormula.Realize, Term.realize, IsIndividual, Fin.snoc]
  have hr (n : ℕ) : U ⊨ relationExists L n ↔ ∃ A : U, IsRelation (L:=L) n A := by
    simp [relationExists, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      relationSort, BoundedFormula.Realize, Term.realize, IsRelation, Fin.snoc]
  have hf {n : ℕ} (f : L.Functions n) : U ⊨ functionClosure f ↔
      ∀ xs : Fin n → U, (∀ i, IsIndividual (L:=L) (xs i)) →
        IsIndividual (L:=L) (Structure.funMap (L:=applicationLanguage L) f xs) := by
    simp only [functionClosure, Sentence.Realize, FirstOrder.Language.Formula.realize_iAlls,
      FirstOrder.Language.Formula.realize_relabel, FirstOrder.Language.Formula.realize_imp,
      FirstOrder.Language.Formula.realize_iInf]
    simp [individual, FirstOrder.Language.Formula.Realize, BoundedFormula.Realize,
      Term.realize, IsIndividual, Function.comp_def]
  constructor
  · intro h
    refine ⟨hi.mp (h.realize_of_mem _ (Or.inl (Or.inl rfl))), ?_, ?_⟩
    · intro n
      exact (hr n).mp (h.realize_of_mem _ (Or.inl (Or.inr ⟨n,rfl⟩)))
    · intro n f
      exact (hf f).mp (h.realize_of_mem _ (Or.inr ⟨n,f,rfl⟩))
  · intro h
    constructor
    intro φ hφ
    rcases hφ with (hφ | ⟨n,rfl⟩) | ⟨n,f,rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hφ
      exact hi.mpr h.individuals
    · exact (hr n).mpr (h.relations n)
    · exact (hf f).mpr (h.functions f)


private def supportImage {α β : Type*} [DecidableEq β] {n : ℕ}
    (f : α → β ⊕ Fin n) (x : α) : Finset β :=
  match f x with | .inl y => {y} | .inr _ => ∅

private theorem term_relabelAux_support {K : Language} {α β : Type*}
    [DecidableEq α] [DecidableEq β] {n k : ℕ}
    (f : α → β ⊕ Fin n) (t : K.Term (α ⊕ Fin k)) :
    (t.relabel (BoundedFormula.relabelAux f k)).varFinsetLeft =
      t.varFinsetLeft.biUnion (supportImage f) := by
  induction t with
  | var x =>
    cases x with
    | inl x =>
      cases hx : f x <;>
        simp [Term.relabel, Term.varFinsetLeft, BoundedFormula.relabelAux,supportImage,hx]
    | inr x =>
      simp [Term.relabel,Term.varFinsetLeft,BoundedFormula.relabelAux]
  | func g ts ih =>
    simp only [Term.relabel, Term.varFinsetLeft, ih,Finset.biUnion_biUnion]

private theorem formula_relabel_support {K : Language} {α β : Type*}
    [DecidableEq α] [DecidableEq β] {n k : ℕ}
    (f : α → β ⊕ Fin n) (φ : K.BoundedFormula α k) :
    (φ.relabel f).freeVarFinset = φ.freeVarFinset.biUnion (supportImage f) := by
  induction φ with
  | falsum => simp [BoundedFormula.relabel,BoundedFormula.mapTermRel]
  | equal t s =>
    simp [BoundedFormula.relabel,BoundedFormula.mapTermRel,
      term_relabelAux_support,Finset.union_biUnion]
  | rel R ts =>
    simp [BoundedFormula.relabel,BoundedFormula.mapTermRel,
      term_relabelAux_support,Finset.biUnion_biUnion]
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormula.relabel_imp,BoundedFormula.freeVarFinset,ihφ,ihψ,
      Finset.union_biUnion]
  | all φ ih =>
    simpa only [BoundedFormula.relabel_all,BoundedFormula.freeVarFinset] using ih

private theorem allName_support (x y : Name) (φ : (applicationLanguage L).Formula Name) :
    y ∈ (allName x φ).freeVarFinset ↔ y ∈ φ.freeVarFinset ∧ y ≠ x := by
  rw [allName,BoundedFormula.freeVarFinset,formula_relabel_support]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨a,ha,hy⟩
    by_cases hax : a=x
    · simp [supportImage,hax] at hy
    · have hya : y=a := by simpa [supportImage,hax] using hy
      subst y
      exact ⟨ha,hax⟩
  · rintro ⟨hy,hyx⟩
    exact ⟨y,hy,by simp [supportImage,hyx]⟩

private theorem translateTerm_support {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (t : L.Term α) :
    (translateTerm f t).varFinset = t.varFinset.image f := by
  induction t with
  | var x => simp [translateTerm]
  | func g ts ih =>
    simp [translateTerm,ih,Finset.biUnion_image]

private theorem translateScopedTerm_support {k : ℕ} (t : L.Term (ℕ ⊕ Fin k)) :
    (translateTerm (Sum.map Sum.inl id) t).varFinsetLeft =
      t.varFinsetLeft.image (Sum.inl : ℕ → Name) := by
  induction t with
  | var x => cases x <;> simp [translateTerm]
  | func g ts ih =>
    simp [translateTerm,ih,Finset.biUnion_image]

private theorem translateFO_support {k : ℕ} (φ : L.BoundedFormula ℕ k) :
    (translateFirstOrder φ).freeVarFinset =
      φ.freeVarFinset.image (Sum.inl : ℕ → Name) := by
  induction φ with
  | falsum => simp [translateFirstOrder]
  | equal t s =>
    simp [translateFirstOrder,translateScopedTerm_support,Finset.image_union]
  | rel R ts =>
    simp [translateFirstOrder,translateScopedTerm_support,Finset.biUnion_image]
  | imp φ ψ ihφ ihψ =>
    simp [translateFirstOrder,ihφ,ihψ,Finset.image_union]
  | all φ ih =>
    simpa [translateFirstOrder,individual] using ih

private theorem term_relabel_inl_support {K : Language} {α β : Type*} [DecidableEq α]
    (t : K.Term α) :
    (t.relabel (Sum.inl : α → α ⊕ β)).varFinsetLeft = t.varFinset := by
  induction t with
  | var x => rfl
  | func f ts ih => simp only [Term.relabel,Term.varFinsetLeft,Term.varFinset,ih]

private theorem translate_support (φ : Formula L) (x : Name) :
    x ∈ (translate φ).freeVarFinset ↔
      match x with
      | .inl y => y ∈ freeIndividual φ
      | .inr p => p ∈ freeRelation φ := by
  induction φ generalizing x with
  | firstOrder φ =>
    rw [translate,translateFO_support]
    cases x <;> simp [freeIndividual,freeRelation]
  | @relation n X ts =>
    simp only [translate,Relations.formula,Relations.boundedFormula,
      BoundedFormula.freeVarFinset]
    simp_rw [term_relabel_inl_support]
    cases x with
    | inl y =>
      simp [Finset.mem_biUnion,Fin.exists_fin_succ,translateTerm_support,
        freeIndividual,Finset.mem_image]
    | inr p =>
      simp [Finset.mem_biUnion,Fin.exists_fin_succ,translateTerm_support,
        freeRelation,Finset.mem_image]
  | falsum =>
    cases x <;> simp [translate,freeIndividual,freeRelation]
  | imp φ ψ ihφ ihψ =>
    cases x <;> simp [translate,freeIndividual,freeRelation,ihφ,ihψ]
  | allIndividual y φ ih =>
    rw [translate,allName_support]
    cases x <;> simp [BoundedFormula.freeVarFinset,individual,
      freeIndividual,freeRelation,ih]
    all_goals tauto
  | allRelation n X φ ih =>
    rw [translate,allName_support]
    cases x <;> simp [BoundedFormula.freeVarFinset,relationSort,
      freeIndividual,freeRelation,ih]
    all_goals tauto

theorem translate_closed (φ : Formula L) (h : IsSentence φ) :
    (translate φ).freeVarFinset = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hs := (translate_support φ x).mp hx
  cases x with
  | inl x => simp [h.1] at hs
  | inr x => simp [h.2] at hs

abbrev Sentence (L : Language) := {φ : Formula L // IsSentence φ}
abbrev Theory (L : Language) := Set (Sentence L)

def translateSentence (φ : Sentence L) : (applicationLanguage L).Sentence :=
  Lemmatheca.MathematicalLogic.FirstOrderSyntax.sentenceOfNoFreeVar (translate φ.val)
    (translate_closed φ.val φ.property)

def translateTheory (T : Theory L) : (applicationLanguage L).Theory :=
  backgroundTheory L ∪ translateSentence '' T

theorem Presentation.admissible {D : RelationDomains M}
    (P : Presentation (L:=L) (U:=U) D) [Nonempty M] (hD : ∀ n, (D n).Nonempty) :
    Admissible (L:=L) (U:=U) := by
  refine ⟨?_,?_,?_⟩
  · exact ⟨P.embed (Classical.choice ‹Nonempty M›), (P.individuals _).mpr ⟨_,rfl⟩⟩
  · intro n
    obtain ⟨R,hR⟩ := hD n
    obtain ⟨A,hA,_⟩ := (P.relationDomains n R).mp hR
    exact ⟨A,hA⟩
  · intro n f xs hxs
    choose ms hms using fun i => (P.individuals (xs i)).mp (hxs i)
    have he : P.embed ∘ ms = xs := funext hms
    rw [← he, P.functions f ms]
    exact (P.individuals _).mpr ⟨_,rfl⟩


private theorem Presentation.assignment_exists {D : RelationDomains M}
    (P : Presentation (L:=L) (U:=U) D) (a : ℕ → M) (r : RelationAssignment M)
    (hr : ∀ n X, r n X ∈ D n) : ∃ s : Name → U, AssignmentCorresponds P a r s := by
  choose A hA hR using fun n X => (P.relationDomains n (r n X)).mp (hr n X)
  refine ⟨Sum.elim (P.embed ∘ a) (fun p => A p.1 p.2), ?_⟩
  exact ⟨fun _ => rfl, fun n X => ⟨hA n X, hR n X⟩⟩

theorem Presentation.sentence_realize {D : RelationDomains M}
    (P : Presentation (L:=L) (U:=U) D) [Nonempty M] (hD : ∀ n, (D n).Nonempty)
    (φ : Sentence L) :
    U ⊨ translateSentence φ ↔
      ∀ a : ℕ → M, ∀ r : RelationAssignment M,
        (∀ n X, r n X ∈ D n) → realize D a r φ.val := by
  have hs (s : Name → U) : U ⊨ translateSentence φ ↔ (translate φ.val).Realize s :=
    FirstOrderSemantics.sentenceOfNoFreeVar_realize (translate φ.val) (translate_closed _ φ.property) s
  constructor
  · intro h a r hr
    obtain ⟨s,hcorr⟩ := P.assignment_exists a r hr
    exact (P.translate_realize φ.val a r s hcorr).mp ((hs s).mp h)
  · intro h
    let a : ℕ → M := fun _ => Classical.choice ‹Nonempty M›
    let r : RelationAssignment M := fun n _ => Classical.choose (hD n)
    have hr : ∀ n X, r n X ∈ D n := fun n _ => Classical.choose_spec (hD n)
    obtain ⟨s,hcorr⟩ := P.assignment_exists a r hr
    exact (hs s).mpr ((P.translate_realize φ.val a r s hcorr).mpr (h a r hr))


structure GeneralModel (L : Language.{u,v}) where
  Carrier : Type (max u v)
  str : L.Structure Carrier
  nonempty : Nonempty Carrier
  domains : RelationDomains Carrier
  domains_nonempty : ∀ n, (domains n).Nonempty

attribute [instance] GeneralModel.str GeneralModel.nonempty

def GeneralModel.Models (H : GeneralModel L) (φ : Formula L) : Prop :=
  ∀ a : ℕ → H.Carrier, ∀ r : RelationAssignment H.Carrier,
    (∀ n X, r n X ∈ H.domains n) → realize H.domains a r φ

def closeFormula (φ : Formula L) : Formula L :=
  (freeRelation φ).toList.foldr (fun p ψ => Formula.allRelation p.1 p.2 ψ)
    ((freeIndividual φ).toList.foldr Formula.allIndividual φ)

private theorem freeIndividual_allIndividualsList (xs : List ℕ) (φ : Formula L) :
    freeIndividual (xs.foldr Formula.allIndividual φ) = freeIndividual φ \ xs.toFinset := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    ext y
    simp only [List.foldr_cons, freeIndividual, ih, List.toFinset_cons,
      Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
    tauto

private theorem freeRelation_allIndividualsList (xs : List ℕ) (φ : Formula L) :
    freeRelation (xs.foldr Formula.allIndividual φ) = freeRelation φ := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldr_cons, freeRelation] using ih

private theorem freeIndividual_allRelationsList (xs : List (ℕ × ℕ)) (φ : Formula L) :
    freeIndividual (xs.foldr (fun p ψ => Formula.allRelation p.1 p.2 ψ) φ) =
      freeIndividual φ := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldr_cons, freeIndividual] using ih

private theorem freeRelation_allRelationsList (xs : List (ℕ × ℕ)) (φ : Formula L) :
    freeRelation (xs.foldr (fun p ψ => Formula.allRelation p.1 p.2 ψ) φ) =
      freeRelation φ \ xs.toFinset := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    ext y
    simp only [List.foldr_cons, freeRelation, ih, List.toFinset_cons,
      Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
    tauto

theorem closeFormula_sentence (φ : Formula L) : IsSentence (closeFormula φ) := by
  simp only [IsSentence, closeFormula, freeIndividual_allRelationsList,
    freeIndividual_allIndividualsList, freeRelation_allRelationsList,
    freeRelation_allIndividualsList]
  simp


def comprehensionTheory (L : Language) : Theory L :=
  {σ | ∃ n X, ∃ φ : Formula L, (n,X) ∉ freeRelation φ ∧
    σ.val = closeFormula (comprehensionInstance n X φ)}

def GeneralModel.FullComprehension (H : GeneralModel L) : Prop :=
  ∀ n, ∀ φ : Formula L, ComprehensionFor H.domains n φ

private theorem Models_allIndividual_iff (H : GeneralModel L) (x : ℕ) (φ : Formula L) :
    H.Models (.allIndividual x φ) ↔ H.Models φ := by
  constructor
  · intro h a r hr
    have hi := h a r hr (a x)
    simpa only [Function.update_eq_self] using hi
  · intro h a r hr b
    exact h (Function.update a x b) r hr

private theorem admissible_updateRelation (H : GeneralModel L) (r : RelationAssignment H.Carrier)
    (hr : ∀ n X, r n X ∈ H.domains n) (n X : ℕ)
    (R : (Fin n → H.Carrier) → Prop) (hR : R ∈ H.domains n) :
    ∀ k Y, updateRelation r n X R k Y ∈ H.domains k := by
  intro k Y
  by_cases hk : k = n
  · subst k
    by_cases hY : Y = X
    · subst Y
      simpa [updateRelation] using hR
    · simpa [updateRelation, hY] using hr n Y
  · simpa [updateRelation, hk] using hr k Y

private theorem Models_allRelation_iff (H : GeneralModel L) (n X : ℕ) (φ : Formula L) :
    H.Models (.allRelation n X φ) ↔ H.Models φ := by
  constructor
  · intro h a r hr
    have hi := h a r hr (r n X) (hr n X)
    simpa only [updateRelation, Function.update_eq_self] using hi
  · intro h a r hr R hR
    exact h a (updateRelation r n X R) (admissible_updateRelation H r hr n X R hR)

private theorem Models_allIndividualsList (H : GeneralModel L) (xs : List ℕ) (φ : Formula L) :
    H.Models (xs.foldr Formula.allIndividual φ) ↔ H.Models φ := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact (Models_allIndividual_iff H x _).trans ih

private theorem Models_allRelationsList (H : GeneralModel L) (xs : List (ℕ × ℕ)) (φ : Formula L) :
    H.Models (xs.foldr (fun p ψ => Formula.allRelation p.1 p.2 ψ) φ) ↔ H.Models φ := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact (Models_allRelation_iff H x.1 x.2 _).trans ih

theorem GeneralModel.models_closeFormula (H : GeneralModel L) (φ : Formula L) :
    H.Models (closeFormula φ) ↔ H.Models φ := by
  unfold closeFormula
  exact (Models_allRelationsList H _ _).trans (Models_allIndividualsList H _ _)


theorem models_comprehensionTheory_iff (H : GeneralModel L) :
    (∀ σ ∈ comprehensionTheory L, H.Models σ.val) ↔ H.FullComprehension := by
  constructor
  · intro h n φ a r hr
    let X := (freeRelation φ).sup Prod.snd + 1
    have hfresh : (n,X) ∉ freeRelation φ := by
      intro hp
      have hh := Finset.le_sup (f:=Prod.snd) hp
      dsimp [X] at hh
      omega
    let σ : Sentence L := ⟨closeFormula (comprehensionInstance n X φ), closeFormula_sentence _⟩
    have hσ : σ ∈ comprehensionTheory L := ⟨n,X,φ,hfresh,rfl⟩
    have hcomp := (H.models_closeFormula _).mp (h σ hσ)
    exact (comprehensionInstance_realize H.domains n X φ hfresh a r).mp (hcomp a r hr)
  · intro h σ hσ
    obtain ⟨n,X,φ,hfresh,he⟩ := hσ
    rw [he]
    apply (H.models_closeFormula _).mpr
    intro a r hr
    apply (comprehensionInstance_realize H.domains n X φ hfresh a r).mpr
    exact h n φ a r hr


def fullGeneralModel (L : Language.{u,v}) (N : Type (max u v)) [L.Structure N] [Nonempty N] :
    GeneralModel L where
  Carrier := N
  str := inferInstance
  nonempty := inferInstance
  domains := fun _ => Set.univ
  domains_nonempty := fun _ => ⟨fun _ => False, Set.mem_univ _⟩

theorem full_models_comprehensionTheory (N : Type (max u v)) [L.Structure N] [Nonempty N] :
    ∀ σ ∈ comprehensionTheory L, (fullGeneralModel L N).Models σ.val := by
  apply (models_comprehensionTheory_iff (fullGeneralModel L N)).mpr
  intro n φ
  exact full_comprehensionFor n φ


def Satisfiable (T : Theory L) : Prop :=
  ∃ H : GeneralModel L, ∀ φ ∈ T, H.Models φ.val

def Models (T : Theory L) (φ : Sentence L) : Prop :=
  ∀ H : GeneralModel L, (∀ ψ ∈ T, H.Models ψ.val) → H.Models φ.val

def Derives (T : Theory L) (φ : Sentence L) : Prop :=
  Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives (translateTheory T) (translateSentence φ)

end
end Lemmatheca.MathematicalLogic.HenkinSemantics
