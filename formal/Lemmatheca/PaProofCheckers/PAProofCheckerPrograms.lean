import Lemmatheca.PaListsAndSyntax.PASyntaxPrograms
import Lemmatheca.PaListsAndSyntax.PANativeSyntax
import Lemmatheca.PaProofCheckers.ArithmeticProofPredicatesPA

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Native program DAGs for the actual 19-rule CoreProof record checker.
The axiom verifier is a parameter: preservation reuses its outputs at unchanged
axiom/certificate pairs, so its own internal equations are not assumed. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u

/-- Same local rule predicate as `CodingFormalProofs.localCheck`: current code,
then the table of accept/reject values of all smaller codes. -/
def localRule : Program 2 :=
  let d : Program 2 := .proj 0
  let hist : Program 2 := .proj 1
  let argD (i : ℕ) := unary (argument i) d
  let ctx (e : Program 2) := unary (argument 0) e
  let concl (e : Program 2) := unary (argument 1) e
  let gamma := argD 0
  let a := argD 1
  let p := argD 2
  let q := argD 3
  let r := argD 4
  let holds (e delta b : Program 2) := conjunction [
    unary sign (binary listEntry hist e), binary equalTest (concl e) b,
    binary contextIncluded (ctx e) delta]
  let ordinary (e : Program 2) := holds e gamma (concl e)
  let form (n : ℕ) (e : Program 2) := binary namedForm (constant n) e
  let term (e : Program 2) := unary namedTerm e
  let sized (n : ℕ) := binary equalTest (unary listLength (unary args d)) (constant n)
  let insert (b delta : Program 2) := binary listCons b delta
  let rule (n : ℕ) (body rest : Program 2) :=
    ternary select (binary equalTest (unary tag d) (constant n)) body rest
  rule 100 (conjunction [sized 2, binary listMember a gamma])
    (rule 101 (conjunction [sized 4, ordinary p, ordinary q,
      binary equalTest a (andCode (concl p) (concl q))])
    (rule 102 (conjunction [sized 4, form 0 q, holds p gamma (andCode a q)])
    (rule 103 (conjunction [sized 4, form 0 q, holds p gamma (andCode q a)])
    (rule 104 (conjunction [sized 4, ordinary p, form 0 q,
      binary equalTest a (orCode (concl p) q)])
    (rule 105 (conjunction [sized 4, ordinary p, form 0 q,
      binary equalTest a (orCode q (concl p))])
    (rule 106 (conjunction [sized 7, form 0 (argD 5), form 0 (argD 6),
      holds p gamma (orCode (argD 5) (argD 6)),
      holds q (insert (argD 5) gamma) a, holds r (insert (argD 6) gamma) a])
    (rule 107 (conjunction [sized 4, form 0 q,
      binary equalTest a (impCode q (concl p)), holds p (insert q gamma) (concl p)])
    (rule 108 (conjunction [sized 4, holds p gamma (impCode (concl q) a), ordinary q])
    (rule 109 (conjunction [sized 4, form 0 q, binary equalTest a (negCode q),
      holds p (insert q gamma) bottom])
    (rule 110 (conjunction [sized 4, binary equalTest a bottom, ordinary p,
      holds q gamma (negCode (concl p))])
    (rule 111 (conjunction [sized 3, holds p gamma bottom])
    (rule 112 (conjunction [sized 3, holds p (insert (negCode a) gamma) bottom])
    (rule 113 (conjunction [sized 5, form 1 q, term r,
      binary equalTest a (binary instantiate q r), holds p gamma (allCode q)])
    (rule 114 (conjunction [sized 5, form 1 q, term r,
      binary equalTest a (exCode q), holds p gamma (binary instantiate q r)])
    (rule 115 (conjunction [sized 5, form 1 q, binary equalTest a (allCode q),
      holds p gamma (binary instantiate q (auxCode r)), booleanNot (binary occursAux r q),
      binary contextFresh r gamma])
    (rule 116 (conjunction [sized 6, form 1 r, holds p gamma (exCode r),
      holds q (insert (binary instantiate r (auxCode (argD 5))) gamma) a,
      booleanNot (binary occursAux (argD 5) r), booleanNot (binary occursAux (argD 5) a),
      binary contextFresh (argD 5) gamma])
    (rule 117 (conjunction [sized 3, term p, binary equalTest a (equalCode p p)])
    (rule 118 (conjunction [sized 7, form 1 r, term (argD 5), term (argD 6),
      binary equalTest a (binary instantiate r (argD 6)),
      holds p gamma (equalCode (argD 5) (argD 6)),
      holds q gamma (binary instantiate r (argD 5))]) (constant 0)))))))))))))))))))

def localCheck : Program 2 :=
  conjunction [unary sign (.proj 0),
    binary namedForm (constant 0) (unary (argument 1) (.proj 0)),
    binary formList (constant 0) (unary (argument 0) (.proj 0)), localRule]

def derivationCheck : Program 1 := unary sign (courseValue localCheck)

/-- Verify one axiom pair at index k, retaining a running Boolean product.
Inputs: context code, witness-list code, k, previous result. -/
def axiomScanStep (E : Program 2) : Program 4 :=
  let a := binary listEntry (.proj 0) (.proj 2)
  let w := binary listEntry (.proj 1) (.proj 2)
  conjunction [.proj 3, unary isSentence a, binary E a w]

def axiomScan (E : Program 2) : Program 3 := .prec (constant 1) (axiomScanStep E)

/-- Inputs: proof certificate and intended sentence code. -/
def certificateCheck (E : Program 2) : Program 2 :=
  let p : Program 2 := .proj 0
  let a : Program 2 := .proj 1
  let d := binary listEntry p (constant 0)
  let ws := binary listEntry p (constant 1)
  let gamma := unary (argument 0) d
  let len := unary listLength gamma
  conjunction [binary equalTest (unary listLength p) (constant 2),
    unary derivationCheck d, binary equalTest (unary (argument 1) d) a,
    unary isSentence a, binary equalTest len (unary listLength ws),
    ternary (axiomScan E) gamma ws len]

def modusPonensRecord : Program 3 :=
  syntaxNode 108 [binary listAppend (unary (argument 0) (.proj 0))
      (unary (argument 0) (.proj 1)), .proj 2, .proj 0, .proj 1]

def modusPonensCertificate : Program 3 :=
  list [ternary modusPonensRecord
      (binary listEntry (.proj 0) (constant 0))
      (binary listEntry (.proj 1) (constant 0)) (.proj 2),
    binary listAppend (binary listEntry (.proj 0) (constant 1))
      (binary listEntry (.proj 1) (constant 1))]

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
