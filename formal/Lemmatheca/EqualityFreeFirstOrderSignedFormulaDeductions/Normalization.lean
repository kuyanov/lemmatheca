import Lemmatheca.EqualityFreeFirstOrderSignedFormulaDeductions.Conversions

/-! Conditional constructor packages and the depth-recursive normalization
construction on actual equality-free full formulas. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w} {e : Bool}
noncomputable section
local instance signedNormalizationFormulaEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

private def identityBridge {c e : Bool} (A : Formula L α) : Bridge c e A A :=
  ⟨fun p => p, fun p => p⟩

private def compose {c e : Bool} {A B C : Formula L α}
    (p : Bridge c e A B) (q : Bridge c e B C) : Bridge c e A C :=
  ⟨fun h => q.forward (p.forward h), fun h => p.backward (q.backward h)⟩

namespace Package

def falsum (e : Bool) (L : Language.{u,v}) (α : Type w) :
    Package e (.falsum : Formula L α) True.intro :=
  ⟨identityBridge _, identityBridge _⟩

def rel (e : Bool) {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin 0)) :
    Package e (.rel R ts) True.intro :=
  ⟨identityBridge _, identityBridge _⟩

def neg {F : Formula L α} {h : F.EqualityFree} (p : Package e F h) :
    Package e (.neg F) h :=
  ⟨p.negative,
    ⟨fun d => p.positive.forward
      (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.doubleNegElim d),
     fun d => doubleNegIntro (p.positive.backward d)⟩⟩

def conj {F G : Formula L α} {hF : F.EqualityFree} {hG : G.EqualityFree}
    (p : Package e F hF) (q : Package e G hG) :
    Package e (.conj F G) ⟨hF,hG⟩ :=
  ⟨Bridge.conj p.positive q.positive,
    compose (Bridge.negConj F G) (Bridge.disj p.negative q.negative)⟩

def disj {F G : Formula L α} {hF : F.EqualityFree} {hG : G.EqualityFree}
    (p : Package e F hF) (q : Package e G hG) :
    Package e (.disj F G) ⟨hF,hG⟩ :=
  ⟨Bridge.disj p.positive q.positive,
    compose (Bridge.negDisj F G) (Bridge.conj p.negative q.negative)⟩

def implication {F G : Formula L α} {hF : F.EqualityFree} {hG : G.EqualityFree}
    (p : Package e F hF) (q : Package e G hG) :
    Package e (.impl F G) ⟨hF,hG⟩ :=
  ⟨compose (Bridge.implication F G) (Bridge.disj p.negative q.positive),
    compose (Bridge.negImplication F G) (Bridge.conj p.positive q.negative)⟩

def all (B : BF L α 1) (h : B.EqualityFree)
    (p : Package e B.toFormula
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).2 h)) :
    Package e (.all B) h := by
  have hp : Bridge true e B.toFormula (Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions.positive B h).toFormula := by
    have hp := p.positive
    change Bridge true e B.toFormula (reading B.toFormula _ true) at hp
    rw [reading_open B h true] at hp
    exact hp
  have hn : Bridge true e (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.neg B).toFormula (Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions.negative B h).toFormula := by
    have hp := p.negative
    change Bridge true e (.neg B.toFormula) (reading B.toFormula _ false) at hp
    rw [reading_open B h false] at hp
    exact hp
  exact ⟨Bridge.all hp, compose (Bridge.negAll B) (Bridge.ex hn)⟩

def ex (B : BF L α 1) (h : B.EqualityFree)
    (p : Package e B.toFormula
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).2 h)) :
    Package e (.ex B) h := by
  have hp : Bridge true e B.toFormula (Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions.positive B h).toFormula := by
    have hp := p.positive
    change Bridge true e B.toFormula (reading B.toFormula _ true) at hp
    rw [reading_open B h true] at hp
    exact hp
  have hn : Bridge true e (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.neg B).toFormula (Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions.negative B h).toFormula := by
    have hp := p.negative
    change Bridge true e (.neg B.toFormula) (reading B.toFormula _ false) at hp
    rw [reading_open B h false] at hp
    exact hp
  exact ⟨Bridge.ex hp, compose (Bridge.negEx B) (Bridge.all hn)⟩

end Package

private def normalizationAux (α : Type w) (e : Bool) (F : Formula L α)
    (h : F.EqualityFree) : Package e F h := by
  revert h
  cases hF : F with
  | falsum => intro h; exact Package.falsum e L α
  | equal _ _ => intro h; exact False.elim h
  | rel R ts => intro h; exact Package.rel e R ts
  | neg F => intro h; exact Package.neg (normalizationAux α e F h)
  | conj F G => intro h; exact Package.conj (normalizationAux α e F h.1) (normalizationAux α e G h.2)
  | disj F G => intro h; exact Package.disj (normalizationAux α e F h.1) (normalizationAux α e G h.2)
  | impl F G => intro h; exact Package.implication (normalizationAux α e F h.1) (normalizationAux α e G h.2)
  | all B => intro h; exact Package.all B h (normalizationAux (α ⊕ Fin 1) e B.toFormula
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).2 h))
  | ex B => intro h; exact Package.ex B h (normalizationAux (α ⊕ Fin 1) e B.toFormula
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).2 h))
termination_by F.depth
  decreasing_by all_goals
    simp_all only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map]
    omega

/-- The specified depth-inductive construction supplies all four actual conversions. -/
def normalization (e : Bool) (F : Formula L α) (h : F.EqualityFree) : Package e F h :=
  normalizationAux α e F h

namespace Raw
variable {Γ : Context L α}

def toPositive (F : Formula L α) (h : F.EqualityFree) (p : Derivation true e L Γ F) :
    Derivation true e L Γ (positive F h) := (normalization e F h).positive.forward p

def fromPositive (F : Formula L α) (h : F.EqualityFree)
    (p : Derivation true e L Γ (positive F h)) : Derivation true e L Γ F :=
  (normalization e F h).positive.backward p

def toNegative (F : Formula L α) (h : F.EqualityFree) (p : Derivation true e L Γ (.neg F)) :
    Derivation true e L Γ (negative F h) := (normalization e F h).negative.forward p

def fromNegative (F : Formula L α) (h : F.EqualityFree)
    (p : Derivation true e L Γ (negative F h)) : Derivation true e L Γ (.neg F) :=
  (normalization e F h).negative.backward p

def negToDual (A : Nnf L α 0) (p : Derivation true e L Γ (.neg A.read)) :
    Derivation true e L Γ A.dual.read := by
  simpa only [negative, reading_negative_read] using toNegative A.read A.read_equalityFree p

def dualToNeg (A : Nnf L α 0) (p : Derivation true e L Γ A.dual.read) :
    Derivation true e L Γ (.neg A.read) := by
  apply fromNegative A.read A.read_equalityFree
  simpa only [negative, reading_negative_read] using p

end Raw
end
end Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions
