import Lemmatheca.IntuitionisticFirstOrderQuantifierPrinciples.Laws
import Lemmatheca.IntuitionisticFirstOrderKripkeSemantics.Examples
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.FinCases

namespace Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples
open _root_.FirstOrder _root_.FirstOrder.Language
open Kripke
universe u v w d a
noncomputable section
set_option maxHeartbeats 1200000

/-- Fixed carriers and actual identity homomorphisms; structures may vary by world. -/
structure IdentityTransport (L : Language.{u,v}) (W : Type w) [Preorder W] (D : Type d) where
  world_nonempty : Nonempty W
  domain_nonempty : Nonempty D
  structureAt : W → L.Structure D
  identityHom : ∀ {w z}, w ≤ z → @Language.Hom L D D (structureAt w) (structureAt z)
  identity_map : ∀ {w z} (h : w ≤ z) (x : D), identityHom h x = x

def IdentityTransport.toModel {L : Language.{u,v}} {W : Type w} [Preorder W] {D : Type d}
    (K : IdentityTransport L W D) : Model L W where
  world_nonempty := K.world_nonempty
  Domain _ := D
  domain_nonempty _ := K.domain_nonempty
  structureAt := K.structureAt
  map := K.identityHom
  map_refl w x := K.identity_map (le_refl w) x
  map_trans h₁ h₂ x := by simp only [K.identity_map]

private theorem forces_vacuous {L : Language.{u,v}} {W : Type w} [Preorder W]
    (K : Model L W) {α : Type a} (A : Formula L α) (w : W)
    (s : α → K.Domain w) (x : K.Domain w) :
    Forces K (vacuous A) w (Sum.elim s (fun _ => x)) ↔ Holds K w A s := by
  rw [← holds_open K (vacuous A) w s x, vacuous_open, holds_rename]
  rfl

private theorem closed_forcing {L : Language.{u,v}} {W : Type w} [Preorder W]
    (K : Model L W) (A : Formula L Empty) (w : W)
    (s : Empty ⊕ Fin 0 → K.Domain w) :
    Forces K A w s ↔ Holds K w A Empty.elim := by
  have he : s = Sum.elim Empty.elim Fin.elim0 := Subsingleton.elim _ _
  rw [he]
  rfl

theorem identityTransport_constantDomain {L : Language.{u,v}} {W : Type w}
    [Preorder W] {D : Type d} (K : IdentityTransport L W D) {α : Type a}
    (A : Formula L α) (P : BoundedFormula L α 1) (w : W) (s : α → D) :
    Holds K.toModel w (constantDomain A P) s := by
  classical
  change ∀ z (h : w ≤ z), _
  intro z hwz hAll
  have hEq {β : Type a} {q r : W} (h : q ≤ r) (s : β → D) :
      K.toModel.transport h s = s := by
    funext x
    exact K.identity_map h (s x)
  have ha : Holds K.toModel z (.all (.disj (vacuous A) P)) s := by
    change Forces K.toModel (.all (.disj (vacuous A) P)) z
      (K.toModel.transport hwz (Sum.elim s Fin.elim0)) at hAll
    erw [hEq] at hAll
    exact hAll
  by_cases hA : Holds K.toModel z A s
  · apply Or.inl
    erw [hEq]
    exact hA
  · apply Or.inr
    have hP : ∀ x : D, Forces K.toModel P z (Sum.elim s (fun _ => x)) := by
      intro x
      have hp := (holds_all K.toModel (.disj (vacuous A) P) z s).mp ha z le_rfl x
      erw [hEq] at hp
      exact hp.resolve_left (fun hn => hA ((forces_vacuous K.toModel A z s x).mp hn))
    have hf : Holds K.toModel z (.all P) s := by
      apply (holds_all K.toModel P z s).mpr
      intro q hzq x
      have hp := forces_mono K.toModel P hzq (Sum.elim s (fun _ => x)) (hP x)
      erw [hEq] at hp
      erw [hEq]
      exact hp
    change Forces K.toModel (.all P) z (K.toModel.transport hwz (Sum.elim s Fin.elim0))
    erw [hEq]
    exact hf

inductive UnaryRelation : ℕ → Type
  | predicate : UnaryRelation 1

def predicateLanguage : Language := ⟨fun _ => Empty, UnaryRelation⟩

@[instance_reducible]
def eventualStructure (w : ℕ) : predicateLanguage.Structure ℕ where
  funMap f := f.elim
  RelMap R xs := match R with | .predicate => xs 0 ≤ w

/-- Each object becomes verified at its own stage; all transports are identity. -/
def eventualIdentity : IdentityTransport predicateLanguage ℕ ℕ where
  world_nonempty := inferInstance
  domain_nonempty := inferInstance
  structureAt := eventualStructure
  identityHom {w z} h := @Language.Hom.mk _ _ _ (eventualStructure w) (eventualStructure z)
    id (by intro n f; exact f.elim) (by intro n R xs hx; cases R; exact le_trans hx h)
  identity_map _ _ := rfl

def eventualModel : Model predicateLanguage ℕ := eventualIdentity.toModel

def predicateBody : BoundedFormula predicateLanguage Empty 1 :=
  .rel UnaryRelation.predicate (fun _ => .var (.inr 0))

def allPredicate : Formula predicateLanguage Empty := .all predicateBody

def allDoubleNegPredicate : Formula predicateLanguage Empty := .all (.neg (.neg predicateBody))

def allExcludedMiddle : Formula predicateLanguage Empty :=
  .all (.disj predicateBody (.neg predicateBody))

def allDoubleNegExcludedMiddle : Formula predicateLanguage Empty :=
  .all (.neg (.neg (.disj predicateBody (.neg predicateBody))))

def doubleNegationShift : Formula predicateLanguage Empty :=
  .impl allDoubleNegPredicate (.neg (.neg allPredicate))

theorem eventual_atomic (w n : ℕ) :
    Forces eventualModel predicateBody w (Sum.elim Empty.elim (fun _ => n)) ↔ n ≤ w := by
  rfl

theorem eventual_allDoubleNegPredicate (w : ℕ) :
    Holds eventualModel w allDoubleNegPredicate Empty.elim := by
  apply (holds_all eventualModel (.neg (.neg predicateBody)) w Empty.elim).mpr
  intro z _ n y _ hn
  change ℕ at n
  apply hn (max y n) (le_max_left _ _)
  change n ≤ max y n
  exact le_max_right _ _

theorem eventual_not_allPredicate (w : ℕ) :
    ¬ Holds eventualModel w allPredicate Empty.elim := by
  intro h
  have hp := (holds_all eventualModel predicateBody w Empty.elim).mp h w le_rfl (w+1)
  change w + 1 ≤ w at hp
  omega

theorem eventual_neg_allPredicate (w : ℕ) :
    Holds eventualModel w (.neg allPredicate) Empty.elim := by
  intro z _ h
  exact eventual_not_allPredicate z ((closed_forcing eventualModel allPredicate z _).mp h)

theorem eventual_not_doubleNeg_allPredicate (w : ℕ) :
    ¬ Holds eventualModel w (.neg (.neg allPredicate)) Empty.elim := by
  intro h
  have hp := h w le_rfl
  rw [transport_refl] at hp
  exact hp (eventual_neg_allPredicate w)

theorem eventual_not_DNS (w : ℕ) :
    ¬ Holds eventualModel w doubleNegationShift Empty.elim := by
  intro h
  have hp := h w le_rfl
  rw [transport_refl] at hp
  exact eventual_not_doubleNeg_allPredicate w (hp (eventual_allDoubleNegPredicate w))

theorem DNS_nonderivable (e : Bool) :
    ¬ NaturalDeduction.Derives false e predicateLanguage ∅ doubleNegationShift := by
  rintro ⟨p⟩
  exact eventual_not_DNS 0 (proof_sound eventualModel p 0 Empty.elim (by simp))

def quantifiedExcludedMiddle_raw (e : Bool) :
    NaturalDeduction.Derivation true e predicateLanguage (α := Empty) ∅ allExcludedMiddle := by
  apply NaturalDeduction.Derivation.allIntro
  exact NaturalDeduction.Derivation.excludedMiddle _ predicateBody.toFormula

def quantifiedExcludedMiddle (e : Bool) :
    NaturalDeduction.Proof true e predicateLanguage ∅ allExcludedMiddle := by
  have hp := (quantifiedExcludedMiddle_raw e).rename (Sum.inl : Empty → Empty ⊕ ℕ)
  simpa only [NaturalDeduction.Proof, Finset.image_empty] using hp

theorem eventual_not_G (w : ℕ) :
    ¬ Holds eventualModel w allExcludedMiddle Empty.elim := by
  intro h
  have hp := (holds_all eventualModel (.disj predicateBody (.neg predicateBody)) w Empty.elim).mp h
    w le_rfl (w+1)
  rcases hp with hp | hn
  · change w + 1 ≤ w at hp
    omega
  · apply hn (w+1) (Nat.le_succ w)
    change w + 1 ≤ w + 1
    exact le_rfl

theorem eventual_neg_G (w : ℕ) :
    Holds eventualModel w (.neg allExcludedMiddle) Empty.elim := by
  intro z _ h
  exact eventual_not_G z ((closed_forcing eventualModel allExcludedMiddle z _).mp h)

theorem eventual_not_doubleNeg_G (w : ℕ) :
    ¬ Holds eventualModel w (.neg (.neg allExcludedMiddle)) Empty.elim := by
  intro h
  have hp := h w le_rfl
  rw [transport_refl] at hp
  exact hp (eventual_neg_G w)

theorem doubleNeg_G_nonderivable (e : Bool) :
    ¬ NaturalDeduction.Derives false e predicateLanguage ∅ (.neg (.neg allExcludedMiddle)) := by
  rintro ⟨p⟩
  exact eventual_not_doubleNeg_G 0 (proof_sound eventualModel p 0 Empty.elim (by simp))

def doubleNegExcludedMiddle_raw {L : Language.{u,v}} {α : Type a} (e : Bool)
    (Γ : NaturalDeduction.Context L α) (A : Formula L α) :
    NaturalDeduction.Derivation false e L Γ (.neg (.neg (.disj A (.neg A)))) := by
  classical
  apply NaturalDeduction.Derivation.negIntro
  have hnA : NaturalDeduction.Derivation false e L (insert (.neg (.disj A (.neg A))) Γ) (.neg A) := by
    apply NaturalDeduction.Derivation.negIntro
    exact .negElim (.disjIntroLeft (.assumption (Finset.mem_insert_self _ _)))
      (.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  exact .negElim (.disjIntroRight hnA) (.assumption (Finset.mem_insert_self _ _))

def quantifiedDoubleNegExcludedMiddle_raw (e : Bool) :
    NaturalDeduction.Derivation false e predicateLanguage (α := Empty) ∅ allDoubleNegExcludedMiddle := by
  apply NaturalDeduction.Derivation.allIntro
  exact doubleNegExcludedMiddle_raw e _ predicateBody.toFormula

def quantifiedDoubleNegExcludedMiddle (e : Bool) :
    NaturalDeduction.Proof false e predicateLanguage ∅ allDoubleNegExcludedMiddle := by
  have hp := (quantifiedDoubleNegExcludedMiddle_raw e).rename (Sum.inl : Empty → Empty ⊕ ℕ)
  simpa only [NaturalDeduction.Proof, Finset.image_empty] using hp

theorem maximal_G {W : Type w} [PartialOrder W] (K : Model predicateLanguage W)
    (w : W) (hw : IsMax w) : Holds K w allExcludedMiddle Empty.elim := by
  classical
  apply (holds_all K (.disj predicateBody (.neg predicateBody)) w Empty.elim).mpr
  intro z hwz x
  have hz : z = w := le_antisymm (hw hwz) hwz
  subst z
  by_cases hp : Forces K predicateBody w (Sum.elim (K.transport hwz Empty.elim) (fun _ => x))
  · exact Or.inl hp
  · apply Or.inr
    intro z hwz hn
    have hz : z = w := le_antisymm (hw hwz) hwz
    subst z
    rw [transport_refl] at hn
    exact hp hn

theorem finite_doubleNeg_G {W : Type w} [PartialOrder W] [Finite W]
    (K : Model predicateLanguage W) (w : W) :
    Holds K w (.neg (.neg allExcludedMiddle)) Empty.elim := by
  intro z _ hn
  obtain ⟨q, hzq, hq⟩ := Finite.exists_le_maximal (p := fun _ : W => True) (a := z) trivial
  have hmax : IsMax q := fun r hqr => hq.2 trivial hqr
  exact hn q hzq ((closed_forcing K allExcludedMiddle q _).mpr (maximal_G K q hmax))

open Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics

def growingCD : Formula Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage Empty :=
  constantDomain Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.existsNew Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody

def growingCounterdual : Formula Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage Empty :=
  .impl (.neg (.all Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody)) (.ex (.neg Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody))

theorem growing_CD_antecedent :
    Holds Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingModel 0 (.all (.disj (vacuous Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.existsNew) Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody))
      Empty.elim := by
  apply (holds_all growingModel (.disj (vacuous existsNew) presentBody) 0 Empty.elim).mpr
  intro z hz x
  fin_cases z
  · apply Or.inr
    change x.val = 0
    have hx := x.isLt
    change x.val < 1 at hx
    omega
  · apply Or.inl
    apply (forces_vacuous growingModel existsNew 1 _ x).mpr
    have hs : growingModel.transport hz Empty.elim = Empty.elim := Subsingleton.elim _ _
    rw [hs]
    exact growing_upper_new

theorem growing_not_CD : ¬ Holds Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingModel 0 growingCD Empty.elim := by
  intro h
  have hp := h 0 le_rfl
  rw [transport_refl] at hp
  rcases hp growing_CD_antecedent with hE | hP
  · exact growing_root_values.1 hE
  · exact growing_not_allPresent hP

theorem growing_neg_allPresent :
    Holds Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingModel 0 (.neg (.all Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody)) Empty.elim := by
  intro z _ hn
  have hp := (holds_all growingModel presentBody z Empty.elim).mp
    ((closed_forcing growingModel (.all presentBody) z _).mp hn) 1 (by omega) ⟨1, by decide⟩
  change (1 : ℕ) = 0 at hp
  omega

theorem growing_not_exNegPresent :
    ¬ Holds Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingModel 0 (.ex (.neg Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody)) Empty.elim := by
  intro h
  rcases (holds_ex growingModel (.neg presentBody) 0 Empty.elim).mp h with ⟨x, hx⟩
  have hp := hx 0 le_rfl
  rw [transport_refl] at hp
  exact hp (growing_present x)

theorem growing_not_counterdual :
    ¬ Holds Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingModel 0 growingCounterdual Empty.elim := by
  intro h
  have hp := h 0 le_rfl
  rw [transport_refl] at hp
  exact growing_not_exNegPresent (hp growing_neg_allPresent)

theorem growing_nonderivable (e : Bool) :
    (¬ NaturalDeduction.Derives false e Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage ∅ growingCD) ∧
    (¬ NaturalDeduction.Derives false e Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage ∅ growingCounterdual) := by
  constructor
  · rintro ⟨p⟩
    exact growing_not_CD (proof_sound growingModel p 0 Empty.elim (by simp))
  · rintro ⟨p⟩
    exact growing_not_counterdual (proof_sound growingModel p 0 Empty.elim (by simp))

end
end Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples
