import Lemmatheca.CodingFormalProofs.CodingFormalProofs
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursiveAutomation

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.CodingFormalProofs
attribute [local irreducible] rewrite stats
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

theorem primrec_node : Primrec₂ (fun t (aa : List ℕ) => node t aa) := by
  unfold Primrec₂ node
  fun_prop

theorem primrec_earlierFold {h : ℕ → ℕ → ℕ} (hh : Primrec₂ h) : Primrec (earlierFold h) := by
  exact FiniteSequenceCoding.primrec_historyValue hh

variable {α : Type*} [Primcodable α]

@[fun_prop] private theorem node_comp {f : α → ℕ} {g : α → List ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => node (f x) (g x)) :=
  primrec_node.comp hf hg

@[fun_prop] theorem tag_comp {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun x => tag (f x)) := by unfold tag; fun_prop

@[fun_prop] theorem args_comp {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun x => args (f x)) := by unfold args; fun_prop

@[fun_prop] theorem arg_comp {f i : α → ℕ} (hf : Primrec f) (hi : Primrec i) :
    Primrec (fun x => arg (f x) (i x)) := by unfold arg; fun_prop

@[fun_prop] private theorem entry_comp {f i : α → ℕ} (hf : Primrec f) (hi : Primrec i) :
    Primrec (fun x => Seq.entry (f x) (i x)) := FiniteSequenceCoding.primrec_entry.comp hf hi

@[fun_prop] private theorem cons_comp {a c : α → ℕ} (ha : Primrec a) (hc : Primrec c) :
    Primrec (fun x => Seq.cons (a x) (c x)) := FiniteSequenceCoding.primrec_cons.comp ha hc

@[fun_prop] private theorem statsAt_comp {h e : α → ℕ} (hh : Primrec h) (he : Primrec e) :
    Primrec (fun x => statsAt (h x) (e x)) := by unfold statsAt; fun_prop

@[fun_prop] private theorem children_comp {e : α → ℕ} (he : Primrec e) :
    Primrec (fun x => children (e x)) := by
  unfold children
  simp only [← Bool.cond_decide, Bool.decide_or]
  fun_prop

private theorem primrec_earlierFold_param {β : Type*} [Denumerable β]
    {h : β → ℕ → ℕ → ℕ} (hh : Primrec fun p : β × ℕ × ℕ => h p.1 p.2.1 p.2.2) :
    Primrec₂ (fun a e => earlierFold (h a) e) := by
  have hp : Primrec (fun p : ℕ × ℕ × ℕ => h (Denumerable.ofNat β p.1) p.2.1 p.2.2) :=
    hh.comp (((Primrec.ofNat β).comp Primrec.fst).pair Primrec.snd)
  exact ((FiniteSequenceCoding.primrec_historyValue_param (h := fun a e hist => h (Denumerable.ofNat β a) e hist) hp).comp
    (Primrec.encode.comp Primrec.fst) Primrec.snd).of_eq fun p => by
      simp [earlierFold]

@[fun_prop] private theorem function_comp {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => S.functionTest (f x) (g x)) := S.function_primrec.comp hf hg

@[fun_prop] private theorem relation_comp {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => S.relationTest (f x) (g x)) := S.relation_primrec.comp hf hg

private def summaryStepIf (e hist : ℕ) : ℕ :=
  let aa := args e
  let ss := (children e).map (statsAt hist)
  let td := ss.foldl (fun m s => max m s.1) 1
  let fd := ss.foldl (fun m s => max m s.2.1) 1
  let fv := ss.foldl (fun m s => max m s.2.2.1) 0
  let av := ss.foldl (fun m s => max m s.2.2.2) 0
  let goodT := ss.all (fun s => s.1 > 0)
  let goodF := ss.all (fun s => s.2.1 > 0)
  let res : Stats := if e = 0 then (0,0,0,0) else

    if tag e = 0 then if aa.length = 1 then (1,0,1,0) else (0,0,0,0) else
    if tag e = 1 then if aa.length = 1 then (arg e 0 + 2,0,0,0) else (0,0,0,0) else
    if tag e = 2 then if aa.length > 0 ∧ S.functionTest (arg e 0) (aa.length-1) ∧ goodT then (td,0,fv,av) else (0,0,0,0) else
    if tag e = 3 then if aa.isEmpty then (0,1,0,0) else (0,0,0,0) else
    if tag e = 4 then if aa.length = 2 ∧ goodT then (0,td,fv,av) else (0,0,0,0) else
    if tag e = 5 then if aa.length > 0 ∧ S.relationTest (arg e 0) (aa.length-1) ∧ goodT then (0,td,fv,av) else (0,0,0,0) else
    if tag e = 6 then if aa.length = 2 ∧ goodF then (0,fd,fv,av) else (0,0,0,0) else
    if tag e = 7 then if aa.length = 1 ∧ goodF then (0,max 1 (fd-1),fv,av) else (0,0,0,0) else
    if tag e = 8 then if aa.length = 1 then (1,0,0,arg e 0+1) else (0,0,0,0) else
    (0,0,0,0)
  Encodable.encode res

private theorem summaryStepIf_eq (e hist : ℕ) : summaryStepIf S e hist = summaryStep S e hist := by
  rcases ht : tag e with _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;>
    simp [summaryStepIf, summaryStep, ht]

set_option maxHeartbeats 1000000 in
private theorem primrec_summaryStep : Primrec₂ (summaryStep S) := by
  have hp : Primrec₂ (summaryStepIf S) := by
    unfold Primrec₂ summaryStepIf
    simp only [← Bool.cond_decide, Bool.decide_and]
    fun_prop
  exact hp.of_eq fun e hist => summaryStepIf_eq S e hist

theorem primrec_stats : Primrec (stats S) := by
  unfold stats
  exact (Primrec.ofNat Stats).comp (primrec_earlierFold (primrec_summaryStep S))

@[fun_prop] private theorem stats_comp {e : α → ℕ} (he : Primrec e) :
    Primrec (fun x => stats S (e x)) := (primrec_stats S).comp he

theorem primrec_isTerm : Primrec₂ (isTerm S) := by
  have hd : Primrec (fun p : ℕ × ℕ => (stats S p.2).1) :=
    Primrec.fst.comp ((primrec_stats S).comp Primrec.snd)
  exact (Primrec.dom_bool₂ Bool.and).comp
    (Primrec.nat_lt.decide.comp (Primrec.const 0) hd)
    (Primrec.nat_le.decide.comp hd (Primrec.succ.comp Primrec.fst))

theorem primrec_isForm : Primrec₂ (isForm S) := by
  have hd : Primrec (fun p : ℕ × ℕ => (stats S p.2).2.1) :=
    Primrec.fst.comp (Primrec.snd.comp ((primrec_stats S).comp Primrec.snd))
  exact (Primrec.dom_bool₂ Bool.and).comp
    (Primrec.nat_lt.decide.comp (Primrec.const 0) hd)
    (Primrec.nat_le.decide.comp hd (Primrec.succ.comp Primrec.fst))

@[fun_prop] private theorem isTerm_comp {n e : α → ℕ} (hn : Primrec n) (he : Primrec e) :
    Primrec (fun x => isTerm S (n x) (e x)) := (primrec_isTerm S).comp hn he

@[fun_prop] private theorem isForm_comp {n e : α → ℕ} (hn : Primrec n) (he : Primrec e) :
    Primrec (fun x => isForm S (n x) (e x)) := (primrec_isForm S).comp hn he

@[fun_prop] private theorem namedForm_comp {n e : α → ℕ} (hn : Primrec n) (he : Primrec e) :
    Primrec (fun x => namedForm S (n x) (e x)) := by
  have hf : Primrec (fun x => (stats S (e x)).2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ((primrec_stats S).comp he)))
  exact (Primrec.dom_bool₂ Bool.and).comp ((primrec_isForm S).comp hn he)
    (Primrec.eq.decide.comp hf (Primrec.const 0))

@[fun_prop] private theorem namedTerm_comp {e : α → ℕ} (he : Primrec e) :
    Primrec (fun x => namedTerm S (e x)) := by
  have hf : Primrec (fun x => (stats S (e x)).2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ((primrec_stats S).comp he)))
  exact (Primrec.dom_bool₂ Bool.and).comp ((primrec_isTerm S).comp (Primrec.const 0) he)
    (Primrec.eq.decide.comp hf (Primrec.const 0))

theorem primrec_namedForm : Primrec₂ (namedForm S) :=
  namedForm_comp S Primrec.fst Primrec.snd

theorem primrec_namedTerm : Primrec (namedTerm S) :=
  namedTerm_comp S Primrec.id

theorem primrec_isSentence : Primrec (isSentence S) := by
  have hf : Primrec (fun x => (stats S x).2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (primrec_stats S)))
  exact (Primrec.dom_bool₂ Bool.and).comp (namedForm_comp S (Primrec.const 0) Primrec.id)
    (Primrec.eq.decide.comp hf (Primrec.const 0))

private theorem primrec_rewriteStep : Primrec (fun p : (ℕ × ℕ × ℕ) × ℕ × ℕ =>
    rewriteStep p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2) := by
  unfold rewriteStep boundName
  simp only [← Bool.cond_decide, Bool.decide_and, Bool.decide_or]
  fun_prop

private theorem primrec_history_three (h : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (hh : Primrec (fun p : (ℕ × ℕ × ℕ) × ℕ × ℕ => h p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2)) :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ =>
      FiniteSequenceCoding.historyValue (h p.1 p.2.1 p.2.2.1) p.2.2.2) := by
  have hc : Primrec (fun p : ℕ × ℕ × ℕ =>
      ((p.1.unpair.1, p.1.unpair.2.unpair.1, p.1.unpair.2.unpair.2), p.2)) := by fun_prop
  have hs : Primrec (fun p : ℕ × ℕ × ℕ =>
      h p.1.unpair.1 p.1.unpair.2.unpair.1 p.1.unpair.2.unpair.2 p.2.1 p.2.2) :=
    Primrec.comp (f := fun p : (ℕ × ℕ × ℕ) × ℕ × ℕ =>
      h p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2) hh hc
  have hp := FiniteSequenceCoding.primrec_historyValue_param
    (h := fun a e hist => h a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2 e hist) hs
  have hk : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => Nat.pair p.1 (Nat.pair p.2.1 p.2.2.1)) := by fun_prop
  have he : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.2) := by fun_prop
  have hres := Primrec₂.comp
    (f := fun a e => FiniteSequenceCoding.historyValue
      (fun e hist => h a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2 e hist) e)
    hp hk he
  exact hres.of_eq fun p => by simp only [Nat.unpair_pair]

theorem primrec_rewrite : Primrec fun p : ℕ × ℕ × ℕ × ℕ => rewrite p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold rewrite earlierFold
  exact primrec_history_three rewriteStep primrec_rewriteStep

@[fun_prop] private theorem rewrite_comp {m i t e : α → ℕ}
    (hm : Primrec m) (hi : Primrec i) (ht : Primrec t) (he : Primrec e) :
    Primrec (fun x => rewrite (m x) (i x) (t x) (e x)) :=
  Primrec.comp (f := fun p : ℕ × ℕ × ℕ × ℕ => rewrite p.1 p.2.1 p.2.2.1 p.2.2.2)
    primrec_rewrite (hm.pair (hi.pair (ht.pair he)))

theorem primrec_substitute : Primrec fun p : ℕ × ℕ × ℕ × ℕ => substitute S p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hc : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => isForm S p.1 p.2.1 && isTerm S 0 p.2.2.2) :=
    (Primrec.dom_bool₂ Bool.and).comp
      (isForm_comp S Primrec.fst (Primrec.fst.comp Primrec.snd))
      (isTerm_comp S (Primrec.const 0) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hr : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => rewrite 0 p.2.2.1 p.2.2.2 p.2.1) :=
    rewrite_comp (Primrec.const 0) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.fst.comp Primrec.snd)
  apply (Primrec.cond hc hr (Primrec.const 0)).of_eq
  intro p
  unfold substitute
  cases h : isForm S p.1 p.2.1 && isTerm S 0 p.2.2.2 <;> rfl

theorem primrec_instantiate : Primrec₂ (instantiate S) := by
  have hc : Primrec (fun p : ℕ × ℕ => namedForm S 1 p.1 && namedTerm S p.2) :=
    (Primrec.dom_bool₂ Bool.and).comp (namedForm_comp S (Primrec.const 1) Primrec.fst)
      (namedTerm_comp S Primrec.snd)
  have hr : Primrec (fun p : ℕ × ℕ => rewrite 2 0 p.2 p.1) :=
    rewrite_comp (Primrec.const 2) (Primrec.const 0) Primrec.snd Primrec.fst
  apply (Primrec.cond hc hr (Primrec.const 0)).of_eq
  intro p
  unfold instantiate
  cases h : namedForm S 1 p.1 && namedTerm S p.2 <;> rfl

theorem primrec_replaceAux : Primrec fun p : ℕ × ℕ × ℕ × ℕ => replaceAux S p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hc : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => namedForm S p.1 p.2.1 && namedTerm S p.2.2.2) :=
    (Primrec.dom_bool₂ Bool.and).comp
      (namedForm_comp S Primrec.fst (Primrec.fst.comp Primrec.snd))
      (namedTerm_comp S (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hr : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => rewrite 1 p.2.2.1 p.2.2.2 p.2.1) :=
    rewrite_comp (Primrec.const 1) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.fst.comp Primrec.snd)
  apply (Primrec.cond hc hr (Primrec.const 0)).of_eq
  intro p
  unfold replaceAux
  cases h : namedForm S p.1 p.2.1 && namedTerm S p.2.2.2 <;> rfl

@[fun_prop] private theorem instantiate_comp {e t : α → ℕ} (he : Primrec e) (ht : Primrec t) :
    Primrec (fun x => instantiate S (e x) (t x)) := (primrec_instantiate S).comp he ht

theorem numeral_primrec (z s : ℕ) : Primrec (numeralCode z s) := by
  have hh : Primrec₂ (fun (_ : ℕ) (v : ℕ) => node 2 [s, v]) := by
    unfold Primrec₂ node
    fun_prop
  exact (Primrec.nat_rec₁ (node 2 [z]) hh).of_eq fun n => by
    induction n <;> simp [numeralCode, *]

theorem primrec_occursAux : Primrec₂ occursAux := by
  have hs : Primrec (fun p : ℕ × ℕ × ℕ => occursStep p.1 p.2.1 p.2.2) := by
    unfold occursStep
    simp only [← Bool.cond_decide, Bool.decide_or]
    fun_prop
  have hv := primrec_earlierFold_param (h := occursStep) hs
  exact (Primrec.nat_lt.comp (Primrec.const 0) hv).decide

theorem primrec_freshAux : Primrec (freshAux S) := by
  unfold freshAux
  fun_prop

@[fun_prop] private theorem occurs_comp {j e : α → ℕ} (hj : Primrec j) (he : Primrec e) :
    Primrec (fun x => occursAux (j x) (e x)) := primrec_occursAux.comp hj he

private def localCheckIf (d hist : ℕ) : Bool :=
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
  let rule :=
    if tag d = 100 then
      sized 2 && a ∈ Seq.decode γ
    else
    if tag d = 101 then
      sized 4 && ordinary p && ordinary q && a = andCode (proofConclusion p) (proofConclusion q)
    else
    if tag d = 102 then
      sized 4 && form 0 q && holds p γ (andCode a q)
    else
    if tag d = 103 then
      sized 4 && form 0 q && holds p γ (andCode q a)
    else
    if tag d = 104 then
      sized 4 && ordinary p && form 0 q && a = orCode (proofConclusion p) q
    else
    if tag d = 105 then
      sized 4 && ordinary p && form 0 q && a = orCode q (proofConclusion p)
    else
    if tag d = 106 then
      let b := arg d 5; let c := arg d 6
      sized 7 && form 0 b && form 0 c && holds p γ (orCode b c) && holds q (contextInsert b γ) a && holds r (contextInsert c γ) a
    else
    if tag d = 107 then
      sized 4 && form 0 q && a = impCode q (proofConclusion p) && holds p (contextInsert q γ) (proofConclusion p)
    else
    if tag d = 108 then
      sized 4 && holds p γ (impCode (proofConclusion q) a) && ordinary q
    else
    if tag d = 109 then
      sized 4 && form 0 q && a = negCode q && holds p (contextInsert q γ) botCode
    else
    if tag d = 110 then
      sized 4 && a = botCode && ordinary p && holds q γ (negCode (proofConclusion p))
    else
    if tag d = 111 then
      sized 3 && holds p γ botCode
    else
    if tag d = 112 then
      sized 3 && holds p (contextInsert (negCode a) γ) botCode
    else
    if tag d = 113 then
      let b := arg d 3; let t := arg d 4
      sized 5 && form 1 b && term t && a = instantiate S b t && holds p γ (allCode b)
    else
    if tag d = 114 then
      let b := arg d 3; let t := arg d 4
      sized 5 && form 1 b && term t && a = exCode b && holds p γ (instantiate S b t)
    else
    if tag d = 115 then
      let b := arg d 3; let c := arg d 4
      sized 5 && form 1 b && a = allCode b && holds p γ (instantiate S b (auxName c)) && !occursAux c b && contextFresh c γ
    else
    if tag d = 116 then
      let b := arg d 4; let c := arg d 5
      sized 6 && form 1 b && holds p γ (exCode b) && holds q (contextInsert (instantiate S b (auxName c)) γ) a &&
        !occursAux c b && !occursAux c a && contextFresh c γ
    else
    if tag d = 117 then
      sized 3 && term p && a = equalCode p p
    else
    if tag d = 118 then
      let b := arg d 4; let s := arg d 5; let t := arg d 6
      sized 7 && form 1 b && term s && term t && a = instantiate S b t && holds p γ (equalCode s t) && holds q γ (instantiate S b s)
    else
      false
  d > 0 && form 0 a && (Seq.decode γ).all (form 0) && rule


private theorem ruleDispatch_eq (n : ℕ) (b100 b101 b102 b103 b104 b105 b106 b107 b108 b109 b110 b111 b112 b113 b114 b115 b116 b117 b118 : Bool) :
    (if n = 100 then b100 else
    if n = 101 then b101 else
    if n = 102 then b102 else
    if n = 103 then b103 else
    if n = 104 then b104 else
    if n = 105 then b105 else
    if n = 106 then b106 else
    if n = 107 then b107 else
    if n = 108 then b108 else
    if n = 109 then b109 else
    if n = 110 then b110 else
    if n = 111 then b111 else
    if n = 112 then b112 else
    if n = 113 then b113 else
    if n = 114 then b114 else
    if n = 115 then b115 else
    if n = 116 then b116 else
    if n = 117 then b117 else
    if n = 118 then b118 else false) =
    (match n with
    | 100 => b100
    | 101 => b101
    | 102 => b102
    | 103 => b103
    | 104 => b104
    | 105 => b105
    | 106 => b106
    | 107 => b107
    | 108 => b108
    | 109 => b109
    | 110 => b110
    | 111 => b111
    | 112 => b112
    | 113 => b113
    | 114 => b114
    | 115 => b115
    | 116 => b116
    | 117 => b117
    | 118 => b118
    | _ => false) := by
  by_cases h : n < 119
  · interval_cases n <;> rfl
  · have h100 : n ≠ 100 := by omega
    have h101 : n ≠ 101 := by omega
    have h102 : n ≠ 102 := by omega
    have h103 : n ≠ 103 := by omega
    have h104 : n ≠ 104 := by omega
    have h105 : n ≠ 105 := by omega
    have h106 : n ≠ 106 := by omega
    have h107 : n ≠ 107 := by omega
    have h108 : n ≠ 108 := by omega
    have h109 : n ≠ 109 := by omega
    have h110 : n ≠ 110 := by omega
    have h111 : n ≠ 111 := by omega
    have h112 : n ≠ 112 := by omega
    have h113 : n ≠ 113 := by omega
    have h114 : n ≠ 114 := by omega
    have h115 : n ≠ 115 := by omega
    have h116 : n ≠ 116 := by omega
    have h117 : n ≠ 117 := by omega
    have h118 : n ≠ 118 := by omega
    simp only [h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, ite_false]

private theorem localCheckIf_eq (d hist : ℕ) : localCheckIf S d hist = localCheck S d hist := by
  unfold localCheckIf localCheck
  dsimp only
  rw [ruleDispatch_eq]
  rfl

set_option maxHeartbeats 1000000 in
theorem primrec_localCheck : Primrec₂ (localCheck S) := by
  have hp : Primrec₂ (localCheckIf S) := by
    unfold Primrec₂ localCheckIf proofContext proofConclusion contextIncluded contextInsert contextFresh
    simp only [andCode, orCode, negCode, botCode, allCode, exCode, equalCode, impCode, auxName]
    simp only [← Bool.cond_decide]
    fun_prop
  exact hp.of_eq fun d hist => localCheckIf_eq S d hist

theorem primrec_derivationCheck : Primrec (derivationCheck S) := by
  have hs : Primrec₂ (fun e h => if localCheck S e h then 1 else 0) := by
    unfold Primrec₂
    have hc := primrec_localCheck S
    have hb : Primrec (fun b : Bool => if b then (1 : ℕ) else 0) := Primrec.dom_bool _
    exact hb.comp hc
  exact (Primrec.nat_lt.comp (Primrec.const 0) (primrec_earlierFold hs)).decide

@[fun_prop] private theorem derivation_comp {d : α → ℕ} (hd : Primrec d) :
    Primrec (fun x => derivationCheck S (d x)) := (primrec_derivationCheck S).comp hd

@[fun_prop] private theorem sentence_comp {d : α → ℕ} (hd : Primrec d) :
    Primrec (fun x => isSentence S (d x)) := (primrec_isSentence S).comp hd

theorem primrec_certificateCheck (E : ℕ → ℕ → Bool) (hE : Primrec₂ E) : Primrec₂ (certificateCheck S E) := by
  have hd : Primrec (fun p : ℕ × ℕ => (Seq.decode p.1)[0]?.getD 0) := by fun_prop
  have hw : Primrec (fun p : ℕ × ℕ => Seq.decode ((Seq.decode p.1)[1]?.getD 0)) := by fun_prop
  have hg : Primrec (fun p : ℕ × ℕ => Seq.decode (proofContext ((Seq.decode p.1)[0]?.getD 0))) := by
    unfold proofContext
    fun_prop
  have hcell : Primrec (fun aw : ℕ × ℕ => isSentence S aw.1 && E aw.1 aw.2) :=
    (Primrec.dom_bool₂ Bool.and).comp ((primrec_isSentence S).comp Primrec.fst) hE
  have hchecks : Primrec (fun p : ℕ × ℕ =>
      ((Seq.decode (proofContext ((Seq.decode p.1)[0]?.getD 0))).zip
        (Seq.decode ((Seq.decode p.1)[1]?.getD 0))).all
        (fun aw => isSentence S aw.1 && E aw.1 aw.2)) :=
    PrimitiveRecursiveAutomation.listAll (PrimitiveRecursiveAutomation.listZip hg hw)
      (hcell.comp Primrec.snd)
  have hfirst : Primrec (fun p : ℕ × ℕ =>
      decide ((Seq.decode p.1).length = 2) && derivationCheck S ((Seq.decode p.1)[0]?.getD 0) &&
      decide (proofConclusion ((Seq.decode p.1)[0]?.getD 0) = p.2) && isSentence S p.2 &&
      decide ((Seq.decode (proofContext ((Seq.decode p.1)[0]?.getD 0))).length =
        (Seq.decode ((Seq.decode p.1)[1]?.getD 0)).length)) := by
    unfold proofConclusion proofContext
    fun_prop
  exact (Primrec.dom_bool₂ Bool.and).comp hfirst hchecks

theorem modusPonens_primitive : Primrec fun p : ℕ × ℕ × ℕ => modusPonensRecord p.1 p.2.1 p.2.2 := by
  unfold modusPonensRecord proofContext Seq.append
  fun_prop

theorem implication_primitive : Primrec fun p : ℕ × ℕ × ℕ => implicationRecord p.1 p.2.1 p.2.2 := by
  unfold implicationRecord proofConclusion impCode
  fun_prop

end Lemmatheca.ProofTheory.CodingFormalProofs
