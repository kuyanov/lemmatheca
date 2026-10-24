import Lemmatheca.FirstOrderHornRules.FirstOrderHornRules

/-! Specified successor, reachability, and quantified-consequence examples. -/
namespace Lemmatheca.Entry.FirstOrderHornRules

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.HerbrandModels
open Lemmatheca.MathematicalLogic.FirstOrderHornRules

noncomputable section

inductive SuccessorFunction : ℕ → Type
  | zero : SuccessorFunction 0
  | succ : SuccessorFunction 1
  deriving DecidableEq
inductive SuccessorRelation : ℕ → Type
  | r : SuccessorRelation 1
  deriving DecidableEq

def successorLanguage : Language := ⟨SuccessorFunction, SuccessorRelation⟩

def successorZero {α : Type*} : successorLanguage.Term α := .func .zero Fin.elim0

def successorTerm {α : Type*} (t : successorLanguage.Term α) : successorLanguage.Term α :=
  .func .succ (fun _ => t)

def successorNumeral : ℕ → GroundTerm successorLanguage
  | 0 => successorZero
  | n + 1 => successorTerm (successorNumeral n)

def successorAtom {α : Type*} (t : successorLanguage.Term α) : Atom successorLanguage α :=
  ⟨1, .r, fun _ => t⟩

def successorFact : Rule successorLanguage := ⟨0, ∅, successorAtom successorZero⟩
def successorRule : Rule successorLanguage :=
  ⟨1, {successorAtom (.var 0)}, successorAtom (successorTerm (.var 0))⟩
def successorProgram : Set (Rule successorLanguage) := {successorFact, successorRule}

instance successorGroundNonempty : Nonempty (GroundTerm successorLanguage) := ⟨successorZero⟩

private def successorDepth : GroundTerm successorLanguage → ℕ
  | .var x => x.elim
  | .func .zero _ => 0
  | .func .succ ts => successorDepth (ts 0) + 1

private theorem successorDepth_numeral (n : ℕ) : successorDepth (successorNumeral n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [successorNumeral, successorTerm, successorDepth] using congrArg Nat.succ ih

private def successorAtomTerm : GroundAtom successorLanguage → GroundTerm successorLanguage
  | ⟨_, .r, ts⟩ => ts 0

private theorem successorAtom_injective : Function.Injective (successorAtom : GroundTerm successorLanguage → _) := by
  intro t u h
  exact congrArg successorAtomTerm h

private def successorGroundFact : DefiniteRule (GroundAtom successorLanguage) :=
  ⟨∅, successorAtom successorZero⟩
private def successorGroundRule (t : GroundTerm successorLanguage) : DefiniteRule (GroundAtom successorLanguage) :=
  ⟨{successorAtom t}, successorAtom (successorTerm t)⟩

private theorem successor_grounding : grounding successorProgram =
    {successorGroundFact} ∪ Set.range successorGroundRule := by
  ext g
  constructor
  · rintro ⟨r, hr, σ, rfl⟩
    rcases hr with rfl | rfl
    · left
      simp only [successorFact, Rule.ground, successorGroundFact, successorAtom, successorZero,
        Atom.subst, Finset.image_empty, Term.subst]
      congr 1
      apply congrArg (fun t : GroundTerm successorLanguage => successorAtom t)
      apply congrArg (Term.func (L := successorLanguage) (α := Empty) SuccessorFunction.zero)
      exact Subsingleton.elim _ _
    · right
      change Fin 1 → GroundTerm successorLanguage at σ
      refine ⟨σ 0, ?_⟩
      simp [successorRule, Rule.ground, successorGroundRule, successorAtom, successorTerm,
        Atom.subst, Term.subst]
  · rintro (h | ⟨t, rfl⟩)
    · have he : g = successorGroundFact := h
      subst g
      refine ⟨successorFact, Or.inl rfl, Fin.elim0, ?_⟩
      simp only [successorFact, Rule.ground, successorGroundFact, successorAtom, successorZero,
        Atom.subst, Finset.image_empty, Term.subst]
      congr 1
      apply congrArg (fun t : GroundTerm successorLanguage => successorAtom t)
      apply congrArg (Term.func (L := successorLanguage) (α := Empty) SuccessorFunction.zero)
      exact Subsingleton.elim _ _
    · refine ⟨successorRule, Or.inr rfl, fun _ => t, ?_⟩
      simp [successorRule, Rule.ground, successorGroundRule, successorAtom, successorTerm,
        Atom.subst, Term.subst]

theorem successor_terms : Function.Bijective successorNumeral := by
  constructor
  · intro n m h
    simpa only [successorDepth_numeral] using congrArg successorDepth h
  · intro t
    induction t with
    | var x => exact x.elim
    | func f ts ih =>
      cases f with
      | zero =>
        refine ⟨0, ?_⟩
        exact congrArg (Term.func (L := successorLanguage) (α := Empty) SuccessorFunction.zero) (Subsingleton.elim _ _)
      | succ =>
        obtain ⟨n, hn⟩ := ih 0
        refine ⟨n + 1, ?_⟩
        change Term.func SuccessorFunction.succ (fun _ => successorNumeral n) = Term.func _ ts
        congr 1
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simpa only [hi] using hn

theorem successor_stages (n : ℕ) :
    stage (grounding successorProgram) n =
      {a | ∃ k < n, a = successorAtom (successorNumeral k)} := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    ext a
    constructor
    · rintro (ha | ⟨r, hr, he, hb⟩)
      · rw [ih] at ha
        obtain ⟨k, hk, rfl⟩ := ha
        exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
      · rw [successor_grounding] at hr
        rcases hr with hr | ⟨t, rfl⟩
        · have hr' : r = successorGroundFact := hr
          subst r
          exact ⟨0, Nat.zero_lt_succ _, he.symm⟩
        · have ht := hb (successorAtom t) (Finset.mem_singleton_self _)
          rw [ih] at ht
          obtain ⟨k, hk, heq⟩ := ht
          have hterm := successorAtom_injective heq
          refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
          simpa only [successorGroundRule, successorNumeral, hterm] using he.symm
    · rintro ⟨k, hk, rfl⟩
      cases k with
      | zero =>
        exact Or.inr ⟨successorGroundFact, by rw [successor_grounding]; exact Or.inl rfl,
          rfl, by simp [successorGroundFact]⟩
      | succ k =>
        apply Or.inr
        refine ⟨successorGroundRule (successorNumeral k), ?_, rfl, ?_⟩
        · rw [successor_grounding]
          exact Or.inr ⟨_, rfl⟩
        · intro b hb
          have hb' : b = successorAtom (successorNumeral k) := Finset.mem_singleton.mp hb
          subst b
          rw [ih]
          exact ⟨k, Nat.lt_of_succ_lt_succ hk, rfl⟩

theorem successor_least :
    least (grounding successorProgram) =
      {a | ∃ k, a = successorAtom (successorNumeral k)} ∧
    ∀ n, stage (grounding successorProgram) (n + 1) ≠
      stage (grounding successorProgram) n := by
  constructor
  · ext a
    rw [least_mem_iff_stage]
    simp only [successor_stages, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, k, _, hk⟩
      exact ⟨k, hk⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k + 1, k, Nat.lt_succ_self k, rfl⟩
  · intro n h
    have hn : successorAtom (successorNumeral n) ∈ stage (grounding successorProgram) (n + 1) := by
      rw [successor_stages]
      exact ⟨n, Nat.lt_succ_self n, rfl⟩
    rw [h, successor_stages] at hn
    obtain ⟨k, hk, he⟩ := hn
    have hnk : n = k := successor_terms.1 (successorAtom_injective he)
    omega

inductive ReachFunction : ℕ → Type
  | constant (i : Fin 4) : ReachFunction 0
  deriving DecidableEq
inductive ReachRelation : ℕ → Type
  | edge : ReachRelation 2
  | reachable : ReachRelation 2
  deriving DecidableEq

def reachLanguage : Language := ⟨ReachFunction, ReachRelation⟩

def reachConstant {α : Type*} (i : Fin 4) : reachLanguage.Term α :=
  .func (.constant i) Fin.elim0

def edge {α : Type*} (s t : reachLanguage.Term α) : Atom reachLanguage α :=
  ⟨2, .edge, ![s,t]⟩
def reachable {α : Type*} (s t : reachLanguage.Term α) : Atom reachLanguage α :=
  ⟨2, .reachable, ![s,t]⟩
def edgeAt (i j : Fin 4) : GroundAtom reachLanguage := edge (reachConstant i) (reachConstant j)
def reachAt (i j : Fin 4) : GroundAtom reachLanguage := reachable (reachConstant i) (reachConstant j)

def edgeFact (i j : Fin 4) : Rule reachLanguage :=
  ⟨0, ∅, edge (reachConstant i) (reachConstant j)⟩
def edgeToReach : Rule reachLanguage :=
  ⟨2, {edge (.var 0) (.var 1)}, reachable (.var 0) (.var 1)⟩
def reachTransitive : Rule reachLanguage :=
  ⟨3, {reachable (.var 0) (.var 1), edge (.var 1) (.var 2)},
    reachable (.var 0) (.var 2)⟩
def reachProgram : Set (Rule reachLanguage) :=
  {edgeFact 0 1, edgeFact 1 2, edgeFact 2 1, edgeToReach, reachTransitive}

def reachEdges : Set (GroundAtom reachLanguage) := {edgeAt 0 1, edgeAt 1 2, edgeAt 2 1}
def reachRoundTwo : Set (GroundAtom reachLanguage) :=
  reachEdges ∪ {reachAt 0 1, reachAt 1 2, reachAt 2 1}
def reachLeast : Set (GroundAtom reachLanguage) :=
  reachEdges ∪ {reachAt 0 1, reachAt 0 2, reachAt 1 1, reachAt 1 2, reachAt 2 1, reachAt 2 2}

instance reachGroundNonempty : Nonempty (GroundTerm reachLanguage) := ⟨reachConstant 0⟩

private def reachIndex : GroundTerm reachLanguage → Fin 4
  | .var x => x.elim
  | .func (.constant i) _ => i

theorem reach_terms : Function.Bijective (reachConstant : Fin 4 → GroundTerm reachLanguage) := by
  constructor
  · intro i j h
    exact congrArg reachIndex h
  · intro t
    cases t with
    | var x => exact x.elim
    | func f ts =>
      cases f with
      | constant i =>
        exact ⟨i, congrArg (Term.func (L := reachLanguage) (α := Empty) (.constant i))
          (Subsingleton.elim _ _)⟩

@[simp] private theorem reachConstant_subst {α β : Type*} (σ : α → reachLanguage.Term β)
    (i : Fin 4) : (reachConstant i : reachLanguage.Term α).subst σ = reachConstant i := by
  apply congrArg (FirstOrder.Language.Term.func (L := reachLanguage) (α := β) (.constant i))
  exact Subsingleton.elim _ _

@[simp] private theorem edge_subst {α β : Type*} (σ : α → reachLanguage.Term β)
    (s t : reachLanguage.Term α) :
    (edge s t).subst σ = edge (s.subst σ) (t.subst σ) := by
  unfold Atom.subst edge
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

@[simp] private theorem reachable_subst {α β : Type*} (σ : α → reachLanguage.Term β)
    (s t : reachLanguage.Term α) :
    (reachable s t).subst σ = reachable (s.subst σ) (t.subst σ) := by
  unfold Atom.subst reachable
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

private def groundEdge (i j : Fin 4) : DefiniteRule (GroundAtom reachLanguage) :=
  ⟨∅,edgeAt i j⟩
private def groundStep (i j : Fin 4) : DefiniteRule (GroundAtom reachLanguage) :=
  ⟨{edgeAt i j},reachAt i j⟩
private def groundTrans (i j k : Fin 4) : DefiniteRule (GroundAtom reachLanguage) :=
  ⟨{reachAt i j,edgeAt j k},reachAt i k⟩

private theorem reach_constant_index (t : GroundTerm reachLanguage) :
    reachConstant (reachIndex t) = t := by
  obtain ⟨i,rfl⟩ := reach_terms.2 t
  rfl

private theorem ground_edgeFact (i j : Fin 4) (σ : Fin 0 → GroundTerm reachLanguage) :
    (edgeFact i j).ground σ = groundEdge i j := by
  simp [Rule.ground, edgeFact, groundEdge, edgeAt]

private theorem ground_edgeToReach (σ : Fin 2 → GroundTerm reachLanguage) :
    edgeToReach.ground σ = groundStep (reachIndex (σ 0)) (reachIndex (σ 1)) := by
  simp [Rule.ground, edgeToReach, groundStep, edgeAt, reachAt,
    reach_constant_index, Term.subst]

private theorem ground_transitive (σ : Fin 3 → GroundTerm reachLanguage) :
    reachTransitive.ground σ =
      groundTrans (reachIndex (σ 0)) (reachIndex (σ 1)) (reachIndex (σ 2)) := by
  simp [Rule.ground, reachTransitive, groundTrans, edgeAt, reachAt,
    reach_constant_index, Term.subst]

private theorem reach_grounding : grounding reachProgram =
    {groundEdge 0 1,groundEdge 1 2,groundEdge 2 1} ∪
      {r | ∃ i j, r = groundStep i j} ∪ {r | ∃ i j k, r = groundTrans i j k} := by
  ext r
  constructor
  · rintro ⟨s,hs,σ,rfl⟩
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (ground_edgeFact 0 1 σ)))
    · exact Or.inl (Or.inl (Or.inr (Or.inl (ground_edgeFact 1 2 σ))))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (ground_edgeFact 2 1 σ))))
    · exact Or.inl (Or.inr ⟨_,_,ground_edgeToReach σ⟩)
    · exact Or.inr ⟨_,_,_,ground_transitive σ⟩
  · rintro ((h|⟨i,j,rfl⟩)|⟨i,j,k,rfl⟩)
    · rcases h with h|h|h
      · have he : r = groundEdge 0 1 := h
        subst r
        exact ⟨edgeFact 0 1,by simp [reachProgram],Fin.elim0,ground_edgeFact 0 1 _⟩
      · have he : r = groundEdge 1 2 := h
        subst r
        exact ⟨edgeFact 1 2,by simp [reachProgram],Fin.elim0,ground_edgeFact 1 2 _⟩
      · have he : r = groundEdge 2 1 := h
        subst r
        exact ⟨edgeFact 2 1,by simp [reachProgram],Fin.elim0,ground_edgeFact 2 1 _⟩
    · refine ⟨edgeToReach,by simp [reachProgram],![reachConstant i,reachConstant j],?_⟩
      simpa [reachIndex,reachConstant] using ground_edgeToReach ![reachConstant i,reachConstant j]
    · refine ⟨reachTransitive,by simp [reachProgram],
        ![reachConstant i,reachConstant j,reachConstant k],?_⟩
      simpa [reachIndex,reachConstant] using
        ground_transitive ![reachConstant i,reachConstant j,reachConstant k]

private theorem reach_step (X : Set (GroundAtom reachLanguage)) :
    step (grounding reachProgram) X =
      X ∪ reachEdges ∪ {a | ∃ i j, edgeAt i j ∈ X ∧ a = reachAt i j} ∪
        {a | ∃ i j k, reachAt i j ∈ X ∧ edgeAt j k ∈ X ∧ a = reachAt i k} := by
  ext a
  simp only [step,reach_grounding,Set.mem_union,Set.mem_ofPred_eq,
    Set.mem_insert_iff,Set.mem_singleton_iff,reachEdges,groundEdge,groundStep,groundTrans]
  aesop

private def reachAtomCode : GroundAtom reachLanguage → Bool × (Fin 4 × Fin 4)
  | ⟨_,.edge,ts⟩ => (false,reachIndex (ts 0),reachIndex (ts 1))
  | ⟨_,.reachable,ts⟩ => (true,reachIndex (ts 0),reachIndex (ts 1))

@[simp] private theorem edgeAt_inj (i j k l : Fin 4) :
    edgeAt i j = edgeAt k l ↔ i = k ∧ j = l := by
  constructor
  · intro h
    have hc := congrArg reachAtomCode h
    simpa [reachAtomCode,edgeAt,edge,reachConstant,reachIndex] using hc
  · rintro ⟨rfl,rfl⟩
    rfl
@[simp] private theorem reachAt_inj (i j k l : Fin 4) :
    reachAt i j = reachAt k l ↔ i = k ∧ j = l := by
  constructor
  · intro h
    have hc := congrArg reachAtomCode h
    simpa [reachAtomCode,reachAt,reachable,reachConstant,reachIndex] using hc
  · rintro ⟨rfl,rfl⟩
    rfl
@[simp] private theorem edgeAt_ne_reachAt (i j k l : Fin 4) :
    edgeAt i j ≠ reachAt k l := by
  intro h
  have hc := congrArg reachAtomCode h
  simp [reachAtomCode,edgeAt,reachAt,edge,reachable,reachConstant,reachIndex] at hc
@[simp] private theorem reachAt_ne_edgeAt (i j k l : Fin 4) :
    reachAt i j ≠ edgeAt k l := Ne.symm (edgeAt_ne_reachAt k l i j)


theorem reach_stages :
    stage (grounding reachProgram) 1 = reachEdges ∧
    stage (grounding reachProgram) 2 = reachRoundTwo ∧
    stage (grounding reachProgram) 3 = reachLeast ∧
    step (grounding reachProgram) reachLeast = reachLeast ∧
    least (grounding reachProgram) = reachLeast := by
  have h0 : step (grounding reachProgram) ∅ = reachEdges := by
    ext a
    simp [reach_step]
  have h1 : step (grounding reachProgram) reachEdges = reachRoundTwo := by
    ext a
    simp [reach_step,reachEdges,reachRoundTwo,Fin.exists_fin_succ]
    aesop
  have h2 : step (grounding reachProgram) reachRoundTwo = reachLeast := by
    ext a
    simp [reach_step,reachEdges,reachRoundTwo,reachLeast,Fin.exists_fin_succ]
    aesop
  have hf : step (grounding reachProgram) reachLeast = reachLeast := by
    ext a
    simp [reach_step,reachEdges,reachLeast,Fin.exists_fin_succ]
    aesop
  have s1 : stage (grounding reachProgram) 1 = reachEdges := by
    simpa only [stage] using h0
  have s2 : stage (grounding reachProgram) 2 = reachRoundTwo := by
    simpa only [stage,←s1] using h1
  have s3 : stage (grounding reachProgram) 3 = reachLeast := by
    simpa only [stage,←s2] using h2
  refine ⟨s1,s2,s3,hf,Set.Subset.antisymm ?_ ?_⟩
  · exact (least_model _).2 _ ((fixed_iff_model _ _).mp hf)
  · rw [←s3]
    exact stage_le_model _ (least_model _).1 3

theorem reach_base_card : Nat.card (GroundAtom reachLanguage) = 32 := by
  let e : GroundAtom reachLanguage ≃ Bool × (Fin 4 × Fin 4) := {
    toFun := reachAtomCode
    invFun := fun x => if x.1 then reachAt x.2.1 x.2.2 else edgeAt x.2.1 x.2.2
    left_inv := by
      rintro ⟨n,r,ts⟩
      cases r <;>
        simp only [reachAtomCode,Bool.false_eq_true,↓reduceIte]
      · unfold edgeAt edge
        congr 1
        funext i
        exact Fin.cases (reach_constant_index (ts 0))
          (fun j => Fin.cases (reach_constant_index (ts 1)) (fun k => Fin.elim0 k) j) i
      · unfold reachAt reachable
        congr 1
        funext i
        exact Fin.cases (reach_constant_index (ts 0))
          (fun j => Fin.cases (reach_constant_index (ts 1)) (fun k => Fin.elim0 k) j) i
    right_inv := by
      rintro ⟨b,i,j⟩
      cases b <;> rfl }
  rw [Nat.card_congr e]
  simp

theorem reach_consequences :
    theory reachProgram ⊨ᵇ (reachAt 0 2).toFormula ∧
    ¬theory reachProgram ⊨ᵇ (reachAt 3 0).toFormula := by
  rw [←ground_consequence,←ground_consequence,reach_stages.2.2.2.2]
  simp [reachLeast,reachEdges]

/-- The specified ordinary term-domain model has all reachable pairs. -/
def reachAll : Set (GroundAtom reachLanguage) :=
  reachEdges ∪ {a | ∃ i j : Fin 4, a = reachAt i j}

theorem closed_world_countermodel :
    @Theory.Model reachLanguage (GroundTerm reachLanguage) (interpretation reachAll)
      (theory reachProgram) ∧
    @Sentence.Realize reachLanguage (GroundTerm reachLanguage) (interpretation reachAll)
      (reachAt 3 0).toFormula ∧
    ¬theory reachProgram ⊨ᵇ (reachAt 3 0).toFormula.not := by
  have hAll : Models (grounding reachProgram) reachAll := by
    intro r hr _
    rw [reach_grounding] at hr
    rcases hr with ((h|⟨i,j,rfl⟩)|⟨i,j,k,rfl⟩)
    · rcases h with h|h|h
      · have he : r = groundEdge 0 1 := h
        subst r
        exact Or.inl (by simp [reachEdges,groundEdge])
      · have he : r = groundEdge 1 2 := h
        subst r
        exact Or.inl (by simp [reachEdges,groundEdge])
      · have he : r = groundEdge 2 1 := h
        subst r
        exact Or.inl (by simp [reachEdges,groundEdge])
    · exact Or.inr ⟨i,j,rfl⟩
    · exact Or.inr ⟨i,k,rfl⟩
  let _ := interpretation reachAll
  have hm : GroundTerm reachLanguage ⊨ theory reachProgram :=
    (interpretation_models reachProgram reachAll).mpr hAll
  have ha : @Sentence.Realize reachLanguage (GroundTerm reachLanguage)
      (interpretation reachAll) (reachAt 3 0).toFormula := by
    change (reachAt 3 0).toFormula.Realize (default : Empty → GroundTerm reachLanguage)
    have he : (default : Empty → GroundTerm reachLanguage) = Empty.elim :=
      Subsingleton.elim _ _
    rw [he]
    apply (Atom.realize_toFormula _ Empty.elim).mpr
    exact (interpretation_atom reachAll _).mpr (Or.inr ⟨3,0,rfl⟩)
  refine ⟨hm,ha,?_⟩
  intro h
  let _ : GroundTerm reachLanguage ⊨ theory reachProgram := hm
  exact (h.realize_sentence (GroundTerm reachLanguage)) ha

inductive OneFunction : ℕ → Type
  | a : OneFunction 0
  deriving DecidableEq
inductive OneRelation : ℕ → Type
  | q : OneRelation 1
  deriving DecidableEq

def oneLanguage : Language := ⟨OneFunction, OneRelation⟩
def oneConstant {α : Type*} : oneLanguage.Term α := .func .a Fin.elim0
def oneAtom {α : Type*} (t : oneLanguage.Term α) : Atom oneLanguage α := ⟨1, .q, fun _ => t⟩
def oneFact : Rule oneLanguage := ⟨0, ∅, oneAtom oneConstant⟩
def oneProgram : Set (Rule oneLanguage) := {oneFact}
def allQ : oneLanguage.Sentence :=
  (BoundedFormula.rel OneRelation.q (fun _ => Term.var (.inr (0 : Fin 1))) :
    oneLanguage.BoundedFormula Empty 1).all

instance oneGroundNonempty : Nonempty (GroundTerm oneLanguage) := ⟨oneConstant⟩

@[instance_reducible]
def twoPointStructure : oneLanguage.Structure Bool where
  funMap := fun f _ => match f with | .a => false
  RelMap := fun r ts => match r with | .q => ts 0 = false

theorem one_ground_term : ∀ t : GroundTerm oneLanguage, t = oneConstant := by
  intro t
  cases t with
  | var x => exact x.elim
  | func f ts =>
    cases f
    exact congrArg (Term.func (L := oneLanguage) (α := Empty) OneFunction.a)
      (Subsingleton.elim _ _)

theorem herbrand_allQ (I : Set (GroundAtom oneLanguage))
    (hI : Models (grounding oneProgram) I) :
    @Sentence.Realize oneLanguage (GroundTerm oneLanguage) (interpretation I) allQ := by
  classical
  let _ := interpretation I
  have hm := (interpretation_models oneProgram I).mpr hI
  have hr := (theory_models_iff oneProgram).mp hm oneFact (Set.mem_singleton _)
  have hf := hr Fin.elim0
  have ha : oneAtom oneConstant ∈ I := by
    have hh := hf (by intro a ha; exact False.elim (Finset.notMem_empty a ha))
    change decide ((oneAtom (FirstOrder.Language.Term.func OneFunction.a _)) ∈ I) = true at hh
    simpa only [one_ground_term, decide_eq_true_eq] using hh
  change ∀ x : GroundTerm oneLanguage, decide ((oneAtom x) ∈ I) = true
  intro x
  rw [one_ground_term x]
  exact decide_eq_true ha

theorem quantified_countermodel :
    @Theory.Model oneLanguage Bool twoPointStructure (theory oneProgram) ∧
    ¬@Sentence.Realize oneLanguage Bool twoPointStructure allQ ∧
    ¬theory oneProgram ⊨ᵇ allQ := by
  let _ := twoPointStructure
  have hm : @Theory.Model oneLanguage Bool twoPointStructure (theory oneProgram) := by
    rw [theory_models_iff]
    intro r hr
    have hr' : r = oneFact := hr
    subst r
    intro vs _
    change false = false
    rfl
  have hn : ¬@Sentence.Realize oneLanguage Bool twoPointStructure allQ := by
    intro h
    change ∀ x : Bool, x = false at h
    exact Bool.noConfusion (h true)
  refine ⟨hm, hn, ?_⟩
  intro h
  exact hn (h.realize_sentence Bool)

end
end Lemmatheca.Entry.FirstOrderHornRules
