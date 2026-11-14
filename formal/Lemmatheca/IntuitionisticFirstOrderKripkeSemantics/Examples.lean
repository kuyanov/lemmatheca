import Lemmatheca.IntuitionisticFirstOrderKripkeSemantics.Bridges

namespace Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder
open Lemmatheca.ProofTheory.FirstOrder.Kripke

inductive GrowingRelation : ℕ → Type
  | present : GrowingRelation 1
  | newObject : GrowingRelation 1

def growingLanguage : Language := ⟨fun _ => Empty, GrowingRelation⟩

@[instance_reducible]
def growingStructure (w : Fin 2) : growingLanguage.Structure (Fin (w.val+1)) where
  funMap := fun f => f.elim
  RelMap := fun R ts => match R with
    | .present => (ts 0).val = 0
    | .newObject => (ts 0).val = 1

def growingMap {w z : Fin 2} (h : w ≤ z) (x : Fin (w.val+1)) : Fin (z.val+1) :=
  ⟨x.val, lt_of_lt_of_le x.isLt (Nat.succ_le_succ h)⟩

/-- Two ordered worlds, with domains {0} and {0,1} and inclusion maps. -/
def growingModel : Model growingLanguage (Fin 2) where
  world_nonempty := inferInstance
  Domain w := Fin (w.val + 1)
  domain_nonempty _ := ⟨⟨0, Nat.zero_lt_succ _⟩⟩
  structureAt := growingStructure
  map := fun {w z} h => @Language.Hom.mk _ _ _
    (growingStructure w) (growingStructure z) (growingMap h)
    (by intro n f; exact f.elim) (by
      intro n R xs hx
      cases R <;> exact hx)
  map_refl _ _ := rfl
  map_trans _ _ _ := rfl

def presentBody : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula growingLanguage Empty 1 :=
  .rel GrowingRelation.present (fun _ => .var (.inr 0))

def newBody : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula growingLanguage Empty 1 :=
  .rel GrowingRelation.newObject (fun _ => .var (.inr 0))

/-- The actual closed existential formula E used throughout the counterexample. -/
def existsNew : Lemmatheca.ProofTheory.FirstOrder.Formula growingLanguage Empty := .ex newBody

theorem growing_present : ∀ x : growingModel.Domain 0,
    Forces growingModel presentBody 0 (Sum.elim Empty.elim (fun _ => x)) := by
  intro x
  change x.val = 0
  have hx := x.isLt
  change x.val < 1 at hx
  omega

theorem growing_not_allPresent :
    ¬ Holds growingModel 0 (.all presentBody) Empty.elim := by
  intro h
  have hp := (holds_all growingModel presentBody 0 Empty.elim).mp h 1 (by decide) ⟨1, by decide⟩
  change (1 : ℕ) = 0 at hp
  omega

theorem growing_somePresent : Holds growingModel 0 (.ex presentBody) Empty.elim := by
  apply (holds_ex growingModel presentBody 0 Empty.elim).mpr
  exact ⟨⟨0, by decide⟩, rfl⟩

theorem growing_upper_new : Holds growingModel 1 existsNew Empty.elim := by
  apply (holds_ex growingModel newBody 1 Empty.elim).mpr
  exact ⟨⟨1, by decide⟩, rfl⟩

private theorem closed_forcing (A : Lemmatheca.ProofTheory.FirstOrder.Formula growingLanguage Empty)
    (w : Fin 2) (s : Empty ⊕ Fin 0 → growingModel.Domain w) :
    Forces growingModel A w s ↔ Holds growingModel w A Empty.elim := by
  have he : s = Sum.elim Empty.elim Fin.elim0 := Subsingleton.elim _ _
  rw [he]
  rfl

theorem growing_root_values :
    ¬ Holds growingModel 0 existsNew Empty.elim ∧
    ¬ Holds growingModel 0 (.neg existsNew) Empty.elim ∧
    Holds growingModel 0 (.neg (.neg existsNew)) Empty.elim := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rcases (holds_ex growingModel newBody 0 Empty.elim).mp h with ⟨x,hx⟩
    change x.val = 1 at hx
    have hb := x.isLt
    change x.val < 1 at hb
    omega
  · intro hn
    exact hn 1 (by decide) ((closed_forcing existsNew 1 _).mpr growing_upper_new)
  · intro z _ hn
    exact hn 1 (by omega) ((closed_forcing existsNew 1 _).mpr growing_upper_new)

theorem growing_not_classical :
    ¬ Holds growingModel 0 (.disj existsNew (.neg existsNew)) Empty.elim ∧
    ¬ Holds growingModel 0 (.impl (.neg (.neg existsNew)) existsNew) Empty.elim := by
  constructor
  · rintro (h | h)
    · exact growing_root_values.1 h
    · exact growing_root_values.2.1 h
  · intro h
    have hp := h 0 le_rfl
    rw [transport_refl] at hp
    exact growing_root_values.1 (hp growing_root_values.2.2)

theorem growing_nonderivability (e : Bool) :
    ¬ NaturalDeduction.Derives false e growingLanguage ∅ (.disj existsNew (.neg existsNew)) ∧
    ¬ NaturalDeduction.Derives false e growingLanguage ∅ (.impl (.neg (.neg existsNew)) existsNew) := by
  constructor
  · rintro ⟨p⟩
    exact growing_not_classical.1 (proof_sound growingModel p 0 Empty.elim (by simp))
  · rintro ⟨p⟩
    exact growing_not_classical.2 (proof_sound growingModel p 0 Empty.elim (by simp))

theorem growing_classical_truth {M : Type*} [growingLanguage.Structure M] (s : Empty → M) :
    NaturalDeduction.Holds (.disj existsNew (.neg existsNew)) s ∧
    NaturalDeduction.Holds (.impl (.neg (.neg existsNew)) existsNew) s := by
  classical
  change (existsNew.Realize s Fin.elim0 ∨ ¬ existsNew.Realize s Fin.elim0) ∧
    (¬¬ existsNew.Realize s Fin.elim0 → existsNew.Realize s Fin.elim0)
  exact ⟨em _, not_not.mp⟩

end Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics
