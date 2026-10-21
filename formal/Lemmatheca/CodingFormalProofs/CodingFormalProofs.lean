import Lemmatheca.CodingFiniteSequences.FiniteSequenceCoding
import Lemmatheca.FirstOrderProofs.FirstOrderProofs
import Lemmatheca.ArithmeticTheories.ArithmeticTheories
import Mathlib.ModelTheory.Order

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.CodingFormalProofs
open FirstOrder FirstOrder.Language
namespace Seq
export FiniteSequenceCoding (code decode cons head tail length entry append)
end Seq
universe u v
structure EffectiveSignature (L : Language.{u,v}) where
  functionCode : {n : ℕ} → L.Functions n → ℕ
  relationCode : {n : ℕ} → L.Relations n → ℕ
  functionTest : ℕ → ℕ → Bool
  relationTest : ℕ → ℕ → Bool
  function_iff : ∀ a n, functionTest a n = true ↔ ∃ f : L.Functions n, functionCode f = a
  relation_iff : ∀ a n, relationTest a n = true ↔ ∃ r : L.Relations n, relationCode r = a
  function_injective : ∀ n, Function.Injective (@functionCode n)
  relation_injective : ∀ n, Function.Injective (@relationCode n)
  function_primrec : Primrec₂ functionTest
  relation_primrec : Primrec₂ relationTest

def node (t : ℕ) (a : List ℕ) : ℕ := 1 + Nat.pair t (Seq.code a)
def tag (e : ℕ) : ℕ := (Nat.unpair (e-1)).1
def args (e : ℕ) : List ℕ := Seq.decode (Nat.unpair (e-1)).2
def arg (e i : ℕ) : ℕ := (args e)[i]?.getD 0
def freeName (i : ℕ) := node 0 [i]
def boundName (i : ℕ) := node 1 [i]
def auxName (i : ℕ) := node 8 [i]
def botCode := node 3 []
def equalCode (s t : ℕ) := node 4 [s,t]
def impCode (a b : ℕ) := node 6 [a,b]
def allCode (a : ℕ) := node 7 [a]
def negCode (a : ℕ) := impCode a botCode
def andCode (a b : ℕ) := negCode (impCode a (negCode b))
def orCode (a b : ℕ) := impCode (negCode a) b
def exCode (a : ℕ) := negCode (allCode (negCode a))
variable {L : Language.{u,v}} (S : EffectiveSignature L)
def termCode {α : Type*} (name : α → ℕ) : L.Term α → ℕ
  | .var i => name i
  | @Term.func _ _ n f ts => node 2 (S.functionCode f :: List.ofFn (fun i : Fin n => termCode name (ts i)))
def formulaCode {α : Type*} (name : α → ℕ) {n : ℕ} : L.BoundedFormula α n → ℕ
  | .falsum => botCode
  | .equal s t => equalCode (termCode S (Sum.elim name (fun i => boundName i.val)) s)
      (termCode S (Sum.elim name (fun i => boundName i.val)) t)
  | @BoundedFormula.rel _ _ n k r ts => node 5 (S.relationCode r :: List.ofFn (fun i : Fin k =>
      termCode S (Sum.elim name (fun j => boundName j.val)) (ts i)))
  | .imp a b => impCode (formulaCode name a) (formulaCode name b)
  | .all a => allCode (formulaCode name a)
def sentenceCode (a : L.Sentence) := formulaCode S Empty.elim a
def namedCode {n : ℕ} (a : L.BoundedFormula ℕ n) := formulaCode S auxName a
def contextCode (Γ : List (L.Formula ℕ)) := Seq.code (Γ.map (namedCode S))
def earlierFold (h : ℕ → ℕ → ℕ) (e : ℕ) := FiniteSequenceCoding.historyValue h e
abbrev Stats := ℕ × ℕ × ℕ × ℕ
def statsAt (hist e : ℕ) : Stats := Denumerable.ofNat Stats (Seq.entry hist e)
def children (e : ℕ) := if tag e = 2 ∨ tag e = 5 then (args e).tail else args e
/-- Positive required depth codes; original-free-name flag; auxiliary-name bound. -/
def summaryStep (e hist : ℕ) : ℕ :=
  let aa := args e
  let ss := (children e).map (statsAt hist)
  let td := ss.foldl (fun m s => max m s.1) 1
  let fd := ss.foldl (fun m s => max m s.2.1) 1
  let fv := ss.foldl (fun m s => max m s.2.2.1) 0
  let av := ss.foldl (fun m s => max m s.2.2.2) 0
  let goodT := ss.all (fun s => s.1 > 0)
  let goodF := ss.all (fun s => s.2.1 > 0)
  let res : Stats := if e = 0 then (0,0,0,0) else match tag e with
    | 0 => if aa.length = 1 then (1,0,1,0) else (0,0,0,0)
    | 1 => if aa.length = 1 then (arg e 0 + 2,0,0,0) else (0,0,0,0)
    | 2 => if aa.length > 0 ∧ S.functionTest (arg e 0) (aa.length-1) ∧ goodT then (td,0,fv,av) else (0,0,0,0)
    | 3 => if aa.isEmpty then (0,1,0,0) else (0,0,0,0)
    | 4 => if aa.length = 2 ∧ goodT then (0,td,fv,av) else (0,0,0,0)
    | 5 => if aa.length > 0 ∧ S.relationTest (arg e 0) (aa.length-1) ∧ goodT then (0,td,fv,av) else (0,0,0,0)
    | 6 => if aa.length = 2 ∧ goodF then (0,fd,fv,av) else (0,0,0,0)
    | 7 => if aa.length = 1 ∧ goodF then (0,max 1 (fd-1),fv,av) else (0,0,0,0)
    | 8 => if aa.length = 1 then (1,0,0,arg e 0+1) else (0,0,0,0)
    | _ => (0,0,0,0)
  Encodable.encode res

def stats (e : ℕ) : Stats := Denumerable.ofNat Stats (earlierFold (summaryStep S) e)
def isTerm (n e : ℕ) : Bool := (stats S e).1 > 0 && (stats S e).1 ≤ n+1
def isForm (n e : ℕ) : Bool := (stats S e).2.1 > 0 && (stats S e).2.1 ≤ n+1
def namedForm (n e : ℕ) : Bool := isForm S n e && (stats S e).2.2.1 = 0
def namedTerm (e : ℕ) : Bool := isTerm S 0 e && (stats S e).2.2.1 = 0
def isSentence (e : ℕ) : Bool := namedForm S 0 e && (stats S e).2.2.2 = 0

def rewriteStep (mode i t e hist : ℕ) : ℕ :=
  let aa := args e
  if e = 0 then 0 else
  if tag e = 0 then (if mode = 0 ∧ arg e 0 = i then t else e) else
  if tag e = 8 then (if mode = 1 ∧ arg e 0 = i then t else e) else
  if tag e = 1 then (if mode = 2 then (if arg e 0 = 0 then t else boundName (arg e 0-1)) else e)
  else node (tag e) (if tag e = 2 ∨ tag e = 5 then arg e 0 :: aa.tail.map (Seq.entry hist) else aa.map (Seq.entry hist))
def rewrite (mode i t e : ℕ) := earlierFold (rewriteStep mode i t) e
def substitute (n e i t : ℕ) := if isForm S n e && isTerm S 0 t then rewrite 0 i t e else 0
def instantiate (e t : ℕ) := if namedForm S 1 e && namedTerm S t then rewrite 2 0 t e else 0
def replaceAux (n e i t : ℕ) := if namedForm S n e && namedTerm S t then rewrite 1 i t e else 0

def numeralCode (zeroSymbol succ : ℕ) : ℕ → ℕ
  | 0 => node 2 [zeroSymbol]
  | n+1 => node 2 [succ, numeralCode zeroSymbol succ n]
def occursStep (j e hist : ℕ) := if tag e = 8 then (if arg e 0 = j then 1 else 0)
  else if tag e = 0 ∨ tag e = 1 then 0
  else if (children e).any (fun c => Seq.entry hist c > 0) then 1 else 0
def occursAux (j e : ℕ) : Bool := earlierFold (occursStep j) e > 0
def freshAux (es : List ℕ) := es.foldl (fun m e => max m (stats S e).2.2.2) 0

def proofContext (d : ℕ) := arg d 0
def proofConclusion (d : ℕ) := arg d 1
def contextIncluded (γ δ : ℕ) : Bool := (Seq.decode γ).all (fun a => a ∈ Seq.decode δ)
def contextInsert (a γ : ℕ) := Seq.cons a γ
def contextFresh (c γ : ℕ) : Bool := (Seq.decode γ).all (fun a => !occursAux c a)
def localCheck (d hist : ℕ) : Bool :=
  let γ := proofContext d
  let a := proofConclusion d
  let p := arg d 2
  let q := arg d 3
  let r := arg d 4
  let holds (c δ b : ℕ) := Seq.entry hist c > 0 && proofConclusion c = b && contextIncluded (proofContext c) δ
  let ordinary (c : ℕ) := holds c γ (proofConclusion c)
  let form (n e : ℕ) := namedForm S n e
  let term (e : ℕ) := namedTerm S e
  let sized (n : ℕ) := (args d).length = n
  let rule := match tag d with
  | 100 => sized 2 && a ∈ Seq.decode γ
  | 101 => sized 4 && ordinary p && ordinary q && a = andCode (proofConclusion p) (proofConclusion q)
  | 102 => sized 4 && form 0 q && holds p γ (andCode a q)
  | 103 => sized 4 && form 0 q && holds p γ (andCode q a)
  | 104 => sized 4 && ordinary p && form 0 q && a = orCode (proofConclusion p) q
  | 105 => sized 4 && ordinary p && form 0 q && a = orCode q (proofConclusion p)
  | 106 => let b := arg d 5; let c := arg d 6
    sized 7 && form 0 b && form 0 c && holds p γ (orCode b c) && holds q (contextInsert b γ) a && holds r (contextInsert c γ) a
  | 107 => sized 4 && form 0 q && a = impCode q (proofConclusion p) && holds p (contextInsert q γ) (proofConclusion p)
  | 108 => sized 4 && holds p γ (impCode (proofConclusion q) a) && ordinary q
  | 109 => sized 4 && form 0 q && a = negCode q && holds p (contextInsert q γ) botCode
  | 110 => sized 4 && a = botCode && ordinary p && holds q γ (negCode (proofConclusion p))
  | 111 => sized 3 && holds p γ botCode
  | 112 => sized 3 && holds p (contextInsert (negCode a) γ) botCode
  | 113 => let b := arg d 3; let t := arg d 4
    sized 5 && form 1 b && term t && a = instantiate S b t && holds p γ (allCode b)
  | 114 => let b := arg d 3; let t := arg d 4
    sized 5 && form 1 b && term t && a = exCode b && holds p γ (instantiate S b t)
  | 115 => let b := arg d 3; let c := arg d 4
    sized 5 && form 1 b && a = allCode b && holds p γ (instantiate S b (auxName c)) && !occursAux c b && contextFresh c γ
  | 116 => let b := arg d 4; let c := arg d 5
    sized 6 && form 1 b && holds p γ (exCode b) && holds q (contextInsert (instantiate S b (auxName c)) γ) a &&
      !occursAux c b && !occursAux c a && contextFresh c γ
  | 117 => sized 3 && term p && a = equalCode p p
  | 118 => let b := arg d 4; let s := arg d 5; let t := arg d 6
    sized 7 && form 1 b && term s && term t && a = instantiate S b t && holds p γ (equalCode s t) && holds q γ (instantiate S b s)
  | _ => false
  d > 0 && form 0 a && (Seq.decode γ).all (form 0) && rule

def derivationCheck (d : ℕ) : Bool := earlierFold (fun e h => if localCheck S e h then 1 else 0) d > 0
def Der (d γ a : ℕ) : Prop := derivationCheck S d = true ∧ proofContext d = γ ∧ proofConclusion d = a

def certificateCheck (E : ℕ → ℕ → Bool) (p a : ℕ) : Bool :=
  let ps := Seq.decode p
  let d := ps[0]?.getD 0
  let ws := Seq.decode (ps[1]?.getD 0)
  let Γ := Seq.decode (proofContext d)
  ps.length = 2 && derivationCheck S d && proofConclusion d = a && isSentence S a &&
    Γ.length = ws.length && ((Γ.zip ws).all (fun aw => isSentence S aw.1 && E aw.1 aw.2))
def theory (E : ℕ → ℕ → Bool) : L.Theory := {A | ∃ s, E (sentenceCode S A) s = true}

-- Step 4 targets: executable definition bodies above; proofs belong to step 6.
theorem node_tag (t : ℕ) (aa : List ℕ) : tag (node t aa) = t := by
  simp [tag, node, Nat.add_comm]
theorem node_args (t : ℕ) (aa : List ℕ) : args (node t aa) = aa := by
  simp [args, node, Nat.add_comm, Seq.decode, Seq.code]
theorem child_lt {t a : ℕ} {aa : List ℕ} (h : a ∈ aa) : a < node t aa := by
  exact (FiniteSequenceCoding.member_lt_code h).trans_le (by
    have := Nat.right_le_pair t (Seq.code aa)
    simp only [node]
    omega)















noncomputable local instance : DecidableEq (L.Formula ℕ) := Classical.decEq _



def mixedCode {n : ℕ} (a : L.BoundedFormula (ℕ ⊕ ℕ) n) := formulaCode S (Sum.elim freeName auxName) a








def arithFunctionCode : {n : ℕ} → ArithmeticTheories.FunctionSymbol n → ℕ
  | _, .zero => 0
  | _, .succ => 1
  | _, .add => 2
  | _, .mul => 3

def arithFunctionTest (a n : ℕ) : Bool :=
  (a = 0 && n = 0) || (a = 1 && n = 1) || ((a = 2 || a = 3) && n = 2)

theorem arith_function_iff (a n : ℕ) : arithFunctionTest a n = true ↔
    ∃ f : ArithmeticTheories.FunctionSymbol n, arithFunctionCode f = a := by
  constructor
  · intro h
    simp only [arithFunctionTest, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | ⟨h,rfl⟩)
    · exact ⟨.zero,rfl⟩
    · exact ⟨.succ,rfl⟩
    · rcases h with rfl | rfl
      · exact ⟨.add,rfl⟩
      · exact ⟨.mul,rfl⟩
  · rintro ⟨f,rfl⟩
    cases f <;> decide

theorem arith_function_injective (n : ℕ) : Function.Injective (@arithFunctionCode n) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

theorem arith_function_primrec : Primrec₂ arithFunctionTest := by
  let eqc (c : ℕ) : Primrec (fun x : ℕ => decide (x=c)) := Primrec.eq.decide.comp Primrec.id (Primrec.const c)
  unfold Primrec₂ arithFunctionTest
  exact (Primrec.dom_bool₂ Bool.or).comp
    ((Primrec.dom_bool₂ Bool.or).comp
      ((Primrec.dom_bool₂ Bool.and).comp ((eqc 0).comp Primrec.fst) ((eqc 0).comp Primrec.snd))
      ((Primrec.dom_bool₂ Bool.and).comp ((eqc 1).comp Primrec.fst) ((eqc 1).comp Primrec.snd)))
    ((Primrec.dom_bool₂ Bool.and).comp
      ((Primrec.dom_bool₂ Bool.or).comp ((eqc 2).comp Primrec.fst) ((eqc 3).comp Primrec.fst))
      ((eqc 2).comp Primrec.snd))

def arithmeticSignature : EffectiveSignature ArithmeticTheories.language where
  functionCode := arithFunctionCode
  relationCode := Empty.elim
  functionTest := arithFunctionTest
  relationTest := fun _ _ => false
  function_iff := arith_function_iff
  relation_iff := fun _ _ => by
    constructor
    · intro h; cases h
    · rintro ⟨r,_⟩; exact r.elim
  function_injective := arith_function_injective
  relation_injective := fun _ => by intro x; exact x.elim
  function_primrec := arith_function_primrec
  relation_primrec := Primrec.const false






def modusPonensRecord (d e b : ℕ) :=
  node 108 [Seq.append (proofContext d) (proofContext e), b, d, e]

def implicationRecord (d γ a : ℕ) := node 107 [γ, impCode a (proofConclusion d), d, a]



end Lemmatheca.ProofTheory.CodingFormalProofs
