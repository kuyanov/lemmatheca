import Lemmatheca.EqualityFreeFirstOrderExistentialHerbrandExtraction.Extraction
import Lemmatheca.HerbrandModels.Examples
import Lemmatheca.EqualityFreeFirstOrderSequents.Examples

/-! The two-instance theorem, its refuted singleton candidates, and the exact
reserved tuple in a language without ground terms. Existing example signatures
and closed-term classification are reused. -/
namespace Lemmatheca.Entry.EqualityFreeFirstOrderExistentialHerbrandExtraction
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.ClassicalFirstOrder
open ExistentialHerbrand
noncomputable section

/-- The literal signed matrix not P(x) or P(f(x)). -/
def workedMatrix : Nnf Lemmatheca.Entry.HerbrandModels.exampleLanguage Empty 1 :=
  .or (.neg Lemmatheca.Entry.HerbrandModels.Relations.p (fun _ => .var (.inr 0)))
    (.pos Lemmatheca.Entry.HerbrandModels.Relations.p (fun _ => .func Lemmatheca.Entry.HerbrandModels.Functions.f (fun _ => .var (.inr 0))))

/-- Precisely the two ordered tuples c and f(c). -/
def workedTuples : List (Fin 1 → Lemmatheca.Entry.HerbrandModels.exampleLanguage.Term Empty) :=
  [fun _ => Lemmatheca.Entry.HerbrandModels.c, fun _ => Lemmatheca.Entry.HerbrandModels.f Lemmatheca.Entry.HerbrandModels.c]

theorem workedMatrix_quantifierFree : workedMatrix.QuantifierFree := by trivial

theorem workedTuples_nonempty : workedTuples ≠ [] := by simp [workedTuples]

private def proofNodes {γ : Type*} [DecidableEq γ] :
    {Γ : Finset (PropNnf γ)} → PropProof Γ → ℕ
  | _, .identity _ _ _ | _, .truth _ => 1
  | _, .andIntro p q => proofNodes p + proofNodes q + 1
  | _, .orIntro p | _, .botIntro p => proofNodes p + 1

private def factorCast {γ : Type*} [DecidableEq γ]
    {Γ Δ : Finset (PropNnf γ)} (he : Γ = Δ) (p : PropProof Γ) : PropProof Δ := he ▸ p

private theorem nodes_factorCast {γ : Type*} [DecidableEq γ]
    {Γ Δ : Finset (PropNnf γ)} (he : Γ = Δ) (p : PropProof Γ) :
    proofNodes (factorCast he p) = proofNodes p := by
  subst Δ
  rfl

private theorem worked_read (t : Lemmatheca.Entry.HerbrandModels.exampleLanguage.Term Empty) :
    propositionalize (workedMatrix.instantiate t) =
      .or (.neg (Lemmatheca.Entry.HerbrandModels.p t))
        (.pos (Lemmatheca.Entry.HerbrandModels.p (Lemmatheca.Entry.HerbrandModels.f t))) := by
  unfold Lemmatheca.Entry.HerbrandModels.exampleLanguage at *
  simp [workedMatrix,Nnf.instantiate,Nnf.instantiateSlots,Nnf.map,propositionalize,
    Lemmatheca.Entry.HerbrandModels.p,Lemmatheca.Entry.HerbrandModels.f,
    Term.subst]
  unfold Lemmatheca.Entry.HerbrandModels.exampleLanguage at *
  exact ⟨rfl,rfl⟩

def workedFactor : PropProof
    ((workedTuples.map (fun ts => propositionalize (workedMatrix.instantiateSlots ts))).toFinset) := by
  let a := Lemmatheca.Entry.HerbrandModels.p Lemmatheca.Entry.HerbrandModels.c
  let b := Lemmatheca.Entry.HerbrandModels.p (Lemmatheca.Entry.HerbrandModels.f Lemmatheca.Entry.HerbrandModels.c)
  let c := Lemmatheca.Entry.HerbrandModels.p (Lemmatheca.Entry.HerbrandModels.f (Lemmatheca.Entry.HerbrandModels.f Lemmatheca.Entry.HerbrandModels.c))
  let p : PropProof (insert (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.neg b) (insert (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.pos c) {Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.neg a,Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.pos b})) :=
    .identity b (by simp) (by simp)
  let q := Lemmatheca.ProofTheory.ClassicalPropositional.Proof.orIntro p
  have he : (insert (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.or (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.neg b) (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.pos c)) {Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.neg a,Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.pos b} : Finset (PropNnf (Atom Lemmatheca.Entry.HerbrandModels.exampleLanguage Empty))) =
      insert (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.neg a) (insert (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.pos b) {Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.or (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.neg b) (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.pos c)}) := by
    ext C; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  let r := Lemmatheca.ProofTheory.ClassicalPropositional.Proof.orIntro (factorCast he q)
  have hc : (insert (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.or (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.neg a) (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.pos b)) {Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.or (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.neg b) (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.pos c)} : Finset (PropNnf (Atom Lemmatheca.Entry.HerbrandModels.exampleLanguage Empty))) =
      (workedTuples.map (fun ts => propositionalize (workedMatrix.instantiateSlots ts))).toFinset := by
    change _ = ([propositionalize (workedMatrix.instantiate Lemmatheca.Entry.HerbrandModels.c),
      propositionalize (workedMatrix.instantiate (Lemmatheca.Entry.HerbrandModels.f Lemmatheca.Entry.HerbrandModels.c))]).toFinset
    simp only [worked_read,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty]
    rfl
  exact factorCast hc r

/-- This packet retains exactly the displayed tuples and the constructed factor. -/
def workedCertificate : Certificate workedMatrix where
  matrix_qf := workedMatrix_quantifierFree
  tuples := workedTuples
  nonempty := workedTuples_nonempty
  factor := workedFactor

def workedExistence : CoreProof Lemmatheca.Entry.HerbrandModels.exampleLanguage {existsBlock workedMatrix} := reconstruct workedMatrix workedCertificate

/-- The explicit core has one identity and two one-premise disjunction nodes. -/
theorem workedFactor_nodes : proofNodes workedFactor = 3 := by
  simp only [workedFactor,nodes_factorCast,proofNodes]

/-- Only the whole relation atom P(t) is assigned true. -/
def workedCountervaluation (t : Lemmatheca.Entry.HerbrandModels.exampleLanguage.Term Empty) : Atom Lemmatheca.Entry.HerbrandModels.exampleLanguage Empty → Bool :=
  fun a => decide (a = Lemmatheca.Entry.HerbrandModels.p t)

private theorem p_injective (t s : Lemmatheca.Entry.HerbrandModels.exampleLanguage.Term Empty)
    (h : Lemmatheca.Entry.HerbrandModels.p t = Lemmatheca.Entry.HerbrandModels.p s) : t = s := by
  unfold Lemmatheca.Entry.HerbrandModels.p at h
  injection h with ha hr ht
  exact congrFun ht 0

private theorem f_ne_self (t : Lemmatheca.Entry.HerbrandModels.exampleLanguage.Term Empty) :
    Lemmatheca.Entry.HerbrandModels.f t ≠ t := by
  obtain ⟨n,hn,hu⟩ := Lemmatheca.Entry.HerbrandModels.ground_terms_unique t
  intro he
  have hn' : t = Lemmatheca.Entry.HerbrandModels.iterate (n+1) := by
    rw [← he,hn]
    rfl
  have hnum := hu (n+1) hn'
  omega

theorem workedInstance_false (t : Lemmatheca.Entry.HerbrandModels.exampleLanguage.Term Empty) :
    Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.eval (workedCountervaluation t)
      (propositionalize (workedMatrix.instantiate t)) = false := by
  have hn : Lemmatheca.Entry.HerbrandModels.p (Lemmatheca.Entry.HerbrandModels.f t) ≠
      Lemmatheca.Entry.HerbrandModels.p t := fun he => f_ne_self t (p_injective _ _ he)
  rw [worked_read]
  simp [Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.eval,workedCountervaluation,hn]

theorem no_single_factor (t : Lemmatheca.Entry.HerbrandModels.exampleLanguage.Term Empty) :
    ¬ Nonempty (PropProof {propositionalize (workedMatrix.instantiate t)}) := by
  rintro ⟨p⟩
  have hs := p.sound (workedCountervaluation t)
  obtain ⟨C,hC,htrue⟩ := hs
  have he := Finset.mem_singleton.mp hC
  subst C
  rw [workedInstance_false] at htrue
  contradiction

abbrev constantFreeMatrix : Nnf Lemmatheca.Entry.EqualityFreeFirstOrderSequents.unaryLanguage Empty 1 :=
  Lemmatheca.Entry.EqualityFreeFirstOrderSequents.excludedMiddleBody Lemmatheca.Entry.EqualityFreeFirstOrderSequents.UnaryRelation.r

/-- The single tuple is the original reserved parameter indexed by zero. -/
def constantFreeTuple : Fin 1 → Lemmatheca.Entry.EqualityFreeFirstOrderSequents.unaryLanguage.Term (Empty ⊕ ℕ) :=
  fun _ => .var (.inr 0)

theorem constantFreeMatrix_quantifierFree :
    (constantFreeMatrix.rename (Sum.inl : Empty → Empty ⊕ ℕ)).QuantifierFree :=
  (Nnf.quantifierFree_map _ _).mpr (by trivial)

def constantFreeFactor : PropProof
    {propositionalize ((constantFreeMatrix.rename (Sum.inl : Empty → Empty ⊕ ℕ)).instantiateSlots constantFreeTuple)} := by
  let a : Atom Lemmatheca.Entry.EqualityFreeFirstOrderSequents.unaryLanguage (Empty ⊕ ℕ) :=
    ⟨1,Lemmatheca.Entry.EqualityFreeFirstOrderSequents.UnaryRelation.r,fun _ => .var (.inr 0)⟩
  have p : PropProof (insert (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.pos a) (insert (Lemmatheca.ProofTheory.ClassicalPropositional.Nnf.neg a) ∅)) := .identity a (by simp) (by simp)
  have q := Lemmatheca.ProofTheory.ClassicalPropositional.Proof.orIntro p
  convert q using 1
  simp [constantFreeMatrix,Lemmatheca.Entry.EqualityFreeFirstOrderSequents.excludedMiddleBody,
      constantFreeTuple,Nnf.rename,Nnf.subst,Nnf.instantiateSlots,Nnf.map,propositionalize,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,Term.subst,a]
  all_goals
    unfold Lemmatheca.Entry.EqualityFreeFirstOrderSequents.unaryLanguage at *
    simp [propositionalize]

def constantFreeCertificate :
    Certificate (constantFreeMatrix.rename (Sum.inl : Empty → Empty ⊕ ℕ)) where
  matrix_qf := constantFreeMatrix_quantifierFree
  tuples := [constantFreeTuple]
  nonempty := List.cons_ne_nil _ _
  factor := by simpa only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty] using constantFreeFactor

/-- The stronger cutful raw obstruction follows through actual extraction/elimination. -/
theorem no_constantFree_raw_with_cut :
    ¬ Nonempty (CutProof Lemmatheca.Entry.EqualityFreeFirstOrderSequents.unaryLanguage {existsBlock constantFreeMatrix}) := by
  rintro ⟨p⟩
  have hq : constantFreeMatrix.QuantifierFree := by trivial
  let H := extractCut constantFreeMatrix hq p
  have he : ∃ ts, ts ∈ H.tuples := List.exists_mem_of_ne_nil _ H.nonempty
  obtain ⟨ts,hts⟩ := he
  exact Lemmatheca.Entry.EqualityFreeFirstOrderSequents.noClosedTerm (ts 0)

end
end Lemmatheca.Entry.EqualityFreeFirstOrderExistentialHerbrandExtraction
