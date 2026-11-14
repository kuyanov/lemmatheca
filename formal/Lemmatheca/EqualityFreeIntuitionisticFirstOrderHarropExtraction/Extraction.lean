import Lemmatheca.EqualityFreeIntuitionisticFirstOrderHarropExtraction.Packets

/-! Structural continuations keep the original names, selected child and left spine. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifohExtractionEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

private def DisjunctTarget (Γ : Context L α) : Formula L α → Type max u v (w+1)
  | .disj A B => ContextHarrop Γ → A.EqualityFree → B.EqualityFree → DisjunctPacket Γ A B
  | _ => PUnit

private def disjunctAux {Γ : Context L α} {C : Formula L α}
    (p : CoreProof L Γ C) : DisjunctTarget Γ C :=
  match p with
  | .relation _ _ _ => PUnit.unit
  | .falsumLeft h => match C with
    | .disj _ _ => fun hΓ hA _ => Sum.inl ⟨.falsumLeft h, context_pure hΓ, hA⟩
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .impl _ _ | .all _ | .ex _ => PUnit.unit
  | .conjLeft h q => match C with
    | .disj _ _ => fun hΓ hA hB =>
      mapDisjunct (fun _ => conjunctionLift h)
        (disjunctAux q (context_conjunction hΓ h) hA hB)
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .impl _ _ | .all _ | .ex _ => PUnit.unit
  | .conjRight _ _ => PUnit.unit
  | .disjLeft h _ _ => match C with
    | .disj _ _ => fun hΓ _ _ => False.elim (context_no_disjunction hΓ _ _ h)
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .impl _ _ | .all _ | .ex _ => PUnit.unit
  | .disjRightLeft q => fun hΓ hA _ => Sum.inl ⟨q, context_pure hΓ, hA⟩
  | .disjRightRight q => fun hΓ _ hB => Sum.inr ⟨q, context_pure hΓ, hB⟩
  | .implLeft h antecedent q => match C with
    | .disj _ _ => fun hΓ hA hB =>
      mapDisjunct (fun _ => implicationLift h
        ⟨antecedent, context_pure hΓ, (hΓ _ h).1⟩)
        (disjunctAux q (context_implication hΓ h) hA hB)
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .impl _ _ | .all _ | .ex _ => PUnit.unit
  | .implRight _ => PUnit.unit
  | .negLeft h antecedent => match C with
    | .disj _ _ => fun hΓ hA _ => Sum.inl ⟨.negLeft h antecedent, context_pure hΓ, hA⟩
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .impl _ _ | .all _ | .ex _ => PUnit.unit
  | .negRight _ => PUnit.unit
  | .allLeft s h q => match C with
    | .disj _ _ => fun hΓ hA hB =>
      mapDisjunct (fun _ => universalLift s h)
        (disjunctAux q (context_universal hΓ h s) hA hB)
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .impl _ _ | .all _ | .ex _ => PUnit.unit
  | .allRight _ => PUnit.unit
  | .exLeft h _ => match C with
    | .disj _ _ => fun hΓ _ _ => False.elim (context_no_existential hΓ _ h)
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .impl _ _ | .all _ | .ex _ => PUnit.unit
  | .exRight _ _ => PUnit.unit
termination_by structural p

def disjunction {Γ : Context L α} {A B : Formula L α} (hΓ : ContextHarrop Γ)
    (p : RawProof L Γ (.disj A B)) : DisjunctPacket Γ A B :=
  disjunctAux p.tree hΓ p.conclusion_pure.1 p.conclusion_pure.2

private def OutcomeTarget (Γ : Context L α) : Formula L α → Type max u v (w+1)
  | .ex B => ContextHarrop Γ → B.EqualityFree → Outcome Γ B
  | _ => PUnit

private def outcomeAux {Γ : Context L α} {C : Formula L α}
    (p : CoreProof L Γ C) : OutcomeTarget Γ C :=
  match p with
  | .relation _ _ _ => PUnit.unit
  | .falsumLeft h => match C with
    | .ex _ => fun hΓ _ => Sum.inr ⟨.falsumLeft h, context_pure hΓ, True.intro⟩
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .disj _ _ | .impl _ _ | .all _ => PUnit.unit
  | .conjLeft h q => match C with
    | .ex _ => fun hΓ hB =>
      mapOutcome (fun _ => conjunctionLift h)
        (outcomeAux q (context_conjunction hΓ h) hB)
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .disj _ _ | .impl _ _ | .all _ => PUnit.unit
  | .conjRight _ _ => PUnit.unit
  | .disjLeft h _ _ => match C with
    | .ex _ => fun hΓ _ => False.elim (context_no_disjunction hΓ _ _ h)
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .disj _ _ | .impl _ _ | .all _ => PUnit.unit
  | .disjRightLeft _ | .disjRightRight _ => PUnit.unit
  | .implLeft h antecedent q => match C with
    | .ex _ => fun hΓ hB =>
      mapOutcome (fun _ => implicationLift h
        ⟨antecedent, context_pure hΓ, (hΓ _ h).1⟩)
        (outcomeAux q (context_implication hΓ h) hB)
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .disj _ _ | .impl _ _ | .all _ => PUnit.unit
  | .implRight _ => PUnit.unit
  | .negLeft h antecedent => match C with
    | .ex _ => fun hΓ _ => Sum.inr ⟨.negLeft h antecedent, context_pure hΓ, True.intro⟩
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .disj _ _ | .impl _ _ | .all _ => PUnit.unit
  | .negRight _ => PUnit.unit
  | .allLeft s h q => match C with
    | .ex _ => fun hΓ hB =>
      mapOutcome (fun _ => universalLift s h)
        (outcomeAux q (context_universal hΓ h s) hB)
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .disj _ _ | .impl _ _ | .all _ => PUnit.unit
  | .allRight _ => PUnit.unit
  | .exLeft h _ => match C with
    | .ex _ => fun hΓ _ => False.elim (context_no_existential hΓ _ h)
    | .falsum | .equal _ _ | .rel _ _ | .neg _ | .conj _ _ | .disj _ _ | .impl _ _ | .all _ => PUnit.unit
  | .exRight t q => fun hΓ hB => Sum.inl
      ⟨t, ⟨q, context_pure hΓ,
        (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr hB⟩⟩
termination_by structural p

def outcome {Γ : Context L α} {B : BF L α 1} (hΓ : ContextHarrop Γ)
    (p : RawProof L Γ (.ex B)) : Outcome Γ B :=
  outcomeAux p.tree hΓ p.conclusion_pure

/-- Remove the actual contradiction alternative using consistency in this scope. -/
def resolveConsistent {Γ : Context L α} {B : BF L α 1}
    (hCon : Consistent Γ) (d : Outcome Γ B) : WitnessPacket Γ B :=
  match d with
  | .inl witness => witness
  | .inr contradiction => False.elim (hCon ⟨contradiction⟩)

/-- Keep every selected term; the default is used only for the actual contradiction tag. -/
def resolveDefault {Γ : Context L α} {B : BF L α 1} (hB : B.EqualityFree)
    (r : L.Term α) (d : Outcome Γ B) : WitnessPacket Γ B :=
  match d with
  | .inl witness => witness
  | .inr contradiction =>
    ⟨r, contradiction.explode (B.instantiate r)
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr hB)⟩

def witnessOfConsistent {Γ : Context L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hCon : Consistent Γ) (p : RawProof L Γ (.ex B)) :
    WitnessPacket Γ B := resolveConsistent hCon (outcome hΓ p)

def witnessWithDefault {Γ : Context L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (r : L.Term α) (p : RawProof L Γ (.ex B)) :
    WitnessPacket Γ B := resolveDefault p.conclusion_pure r (outcome hΓ p)

section DisjunctionEquations
variable {Γ : Context L α} {A B C D : Formula L α}

theorem disjunction_left (hΓ : ContextHarrop Γ) (hB : B.EqualityFree)
    (p : RawProof L Γ A) :
    disjunction hΓ (⟨.disjRightLeft p.tree, p.context_pure,
      ⟨p.conclusion_pure, hB⟩⟩ : RawProof L Γ (.disj A B)) = Sum.inl p := by
  rfl

theorem disjunction_right (hΓ : ContextHarrop Γ) (hA : A.EqualityFree)
    (p : RawProof L Γ B) :
    disjunction hΓ (⟨.disjRightRight p.tree, p.context_pure,
      ⟨hA, p.conclusion_pure⟩⟩ : RawProof L Γ (.disj A B)) = Sum.inr p := by
  rfl

theorem disjunction_falsum (hΓ : ContextHarrop Γ) (h : .falsum ∈ Γ)
    (hA : A.EqualityFree) (hB : B.EqualityFree) :
    disjunction hΓ (⟨.falsumLeft h, context_pure hΓ,
      ⟨hA, hB⟩⟩ : RawProof L Γ (.disj A B)) =
      Sum.inl ⟨.falsumLeft h, context_pure hΓ, hA⟩ := by
  rfl

theorem disjunction_negation (hΓ : ContextHarrop Γ) (h : .neg C ∈ Γ)
    (antecedent : RawProof L Γ C) (hA : A.EqualityFree) (hB : B.EqualityFree) :
    disjunction hΓ (⟨.negLeft h antecedent.tree, context_pure hΓ,
      ⟨hA, hB⟩⟩ : RawProof L Γ (.disj A B)) =
      Sum.inl ⟨.negLeft h antecedent.tree, context_pure hΓ, hA⟩ := by
  rfl

theorem disjunction_conjunction (hΓ : ContextHarrop Γ) (h : .conj C D ∈ Γ)
    (q : RawProof L (insert C (insert D Γ)) (.disj A B)) :
    disjunction hΓ (conjunctionLift h q) =
      mapDisjunct (fun _ => conjunctionLift h)
        (disjunction (context_conjunction hΓ h) q) := by
  rfl

theorem disjunction_implication (hΓ : ContextHarrop Γ) (h : .impl C D ∈ Γ)
    (antecedent : RawProof L Γ C) (q : RawProof L (insert D Γ) (.disj A B)) :
    disjunction hΓ (implicationLift h antecedent q) =
      mapDisjunct (fun _ => implicationLift h antecedent)
        (disjunction (context_implication hΓ h) q) := by
  rfl

theorem disjunction_universal {C : BF L α 1} (hΓ : ContextHarrop Γ)
    (s : L.Term α) (h : .all C ∈ Γ)
    (q : RawProof L (insert (C.instantiate s) Γ) (.disj A B)) :
    disjunction hΓ (universalLift s h q) =
      mapDisjunct (fun _ => universalLift s h)
        (disjunction (context_universal hΓ h s) q) := by
  rfl
end DisjunctionEquations

section OutcomeEquations
variable {Γ : Context L α} {B : BF L α 1} {C D : Formula L α}

theorem outcome_existential (hΓ : ContextHarrop Γ) (hB : B.EqualityFree)
    (t : L.Term α) (q : RawProof L Γ (B.instantiate t)) :
    outcome hΓ (⟨.exRight t q.tree, q.context_pure, hB⟩ : RawProof L Γ (.ex B)) =
      Sum.inl (⟨t, q⟩ : WitnessPacket Γ B) := by
  rfl

theorem outcome_falsum (hΓ : ContextHarrop Γ) (h : .falsum ∈ Γ)
    (hB : B.EqualityFree) :
    outcome hΓ (⟨.falsumLeft h, context_pure hΓ, hB⟩ : RawProof L Γ (.ex B)) =
      Sum.inr ⟨.falsumLeft h, context_pure hΓ, True.intro⟩ := by
  rfl

theorem outcome_negation (hΓ : ContextHarrop Γ) (h : .neg C ∈ Γ)
    (antecedent : RawProof L Γ C) (hB : B.EqualityFree) :
    outcome hΓ (⟨.negLeft h antecedent.tree, context_pure hΓ, hB⟩ : RawProof L Γ (.ex B)) =
      Sum.inr ⟨.negLeft h antecedent.tree, context_pure hΓ, True.intro⟩ := by
  rfl

theorem outcome_conjunction (hΓ : ContextHarrop Γ) (h : .conj C D ∈ Γ)
    (q : RawProof L (insert C (insert D Γ)) (.ex B)) :
    outcome hΓ (conjunctionLift h q) =
      mapOutcome (fun _ => conjunctionLift h)
        (outcome (context_conjunction hΓ h) q) := by
  rfl

theorem outcome_implication (hΓ : ContextHarrop Γ) (h : .impl C D ∈ Γ)
    (antecedent : RawProof L Γ C) (q : RawProof L (insert D Γ) (.ex B)) :
    outcome hΓ (implicationLift h antecedent q) =
      mapOutcome (fun _ => implicationLift h antecedent)
        (outcome (context_implication hΓ h) q) := by
  rfl

theorem outcome_universal {C : BF L α 1} (hΓ : ContextHarrop Γ)
    (s : L.Term α) (h : .all C ∈ Γ)
    (q : RawProof L (insert (C.instantiate s) Γ) (.ex B)) :
    outcome hΓ (universalLift s h q) =
      mapOutcome (fun _ => universalLift s h)
        (outcome (context_universal hΓ h s) q) := by
  rfl
end OutcomeEquations

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
