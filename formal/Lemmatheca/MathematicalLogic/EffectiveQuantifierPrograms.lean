import Lemmatheca.MathematicalLogic.PrimitiveRecursiveAutomation
import Lemmatheca.MathematicalLogic.FiniteSequenceCoding

/-! Numerical implementations of the finite Boolean and clause operations used
by effective quantifier elimination. These are untyped code operations; their
connection to shared scoped formulas is established in the elimination module. -/
namespace Lemmatheca.MathematicalLogic.EffectiveQuantifierPrograms

open PrimitiveRecursiveAutomation
namespace Seq
export FiniteSequenceCoding (code decode head tail length entry)
end Seq

abbrev Atom := Bool × ℕ × ℕ
abbrev Literal := Bool × Atom
abbrev Clause := List Literal
abbrev DNF := List Clause

def node (t : ℕ) (aa : List ℕ) := 1 + Nat.pair t (Seq.code aa)
def tag (c : ℕ) := (c-1).unpair.1
def args (c : ℕ) := Seq.decode (c-1).unpair.2
def arg (c i : ℕ) := (args c)[i]?.getD 0

def bot := node 3 []
def neg (a : ℕ) := node 6 [a,bot]
def top := neg bot
def conj (a b : ℕ) := neg (node 6 [a,neg b])
def disj (a b : ℕ) := node 6 [neg a,b]
def andList : List ℕ → ℕ
  | [] => top
  | a::l => conj a (andList l)
def orList : List ℕ → ℕ
  | [] => bot
  | a::l => disj a (orList l)

def varCode (i : ℕ) := node 1 [i]
def atomCode (a : Atom) :=
  if a.1 then node 5 [0,varCode a.2.1,varCode a.2.2]
  else node 4 [varCode a.2.1,varCode a.2.2]
def literalCode (l : Literal) := if l.1 then atomCode l.2 else neg (atomCode l.2)
def fromAtom (c : ℕ) : Atom :=
  if tag c = 4 then (false,arg (arg c 0) 0,arg (arg c 1) 0)
  else (true,arg (arg c 1) 0,arg (arg c 2) 0)

def cross {α : Type*} (a b : List (List α)) :=
  a.flatMap fun u => b.map fun v => u ++ v

def normalFuel : ℕ → ℕ → DNF × DNF
  | 0, _ => ([],[])
  | k+1, c =>
    if c = 0 then ([],[]) else
    if tag c = 3 then ([],[ [] ]) else
    if tag c = 4 ∨ tag c = 5 then
      ([ [(true,fromAtom c)] ],[ [(false,fromAtom c)] ]) else
    if tag c = 6 then
      let a := normalFuel k (arg c 0)
      let b := normalFuel k (arg c 1)
      (a.2 ++ b.1,cross a.1 b.2)
    else ([],[])

def normal (c : ℕ) := normalFuel c c

def fixed (n : ℕ) (a : Atom) : Option ℕ :=
  if a.1 then none else
  if a.2.1 = n ∧ a.2.2 < n then some a.2.2 else
  if a.2.1 < n ∧ a.2.2 = n then some a.2.1 else none

def fixedLiteral (n : ℕ) (l : Literal) := if l.1 then fixed n l.2 else none

def replace (n w : ℕ) (a : Atom) : Atom :=
  (a.1,if a.2.1 < n then a.2.1 else w,if a.2.2 < n then a.2.2 else w)

def freshAtom (n : ℕ) (a : Atom) :=
  if a.2.1 < n ∧ a.2.2 < n then atomCode a else
  if a.2.1 = n ∧ a.2.2 = n then top else bot

def equalityClause (n : ℕ) (c : Clause) : ℕ :=
  (c.findSome? (fixedLiteral n)).elim
    (andList (c.map fun (l : Literal) => if l.1 then freshAtom n l.2 else neg (freshAtom n l.2)))
    (fun w => andList (c.map fun (l : Literal) => literalCode (l.1,replace n w l.2)))

def positiveLiteral (l : Literal) : List (List Atom) :=
  if l.1 then [ [l.2] ] else
  if l.2.1 then [ [(false,l.2.2.1,l.2.2.2)],[(true,l.2.2.2,l.2.2.1)] ]
  else [ [(true,l.2.2.1,l.2.2.2)],[(true,l.2.2.2,l.2.2.1)] ]

def positiveClause (c : Clause) := c.foldr (fun l cs => cross (positiveLiteral l) cs) [ [] ]

def independent (n : ℕ) (a : Atom) :=
  if a.2.1 < n ∧ a.2.2 < n then atomCode a else top

def lower (n : ℕ) (a : Atom) : Option ℕ :=
  if a.1 ∧ a.2.1 < n ∧ a.2.2 = n then some a.2.1 else none

def upper (n : ℕ) (a : Atom) : Option ℕ :=
  if a.1 ∧ a.2.1 = n ∧ a.2.2 < n then some a.2.2 else none

def selfStrict (n : ℕ) (a : Atom) := a.1 && a.2.1 = n && a.2.2 = n

def orderClause (n : ℕ) (c : List Atom) : ℕ :=
  if c.any (selfStrict n) then bot else
  (c.findSome? (fixed n)).elim
    (andList (c.map (independent n) ++
      (c.filterMap (lower n)).flatMap fun i =>
        (c.filterMap (upper n)).map fun j => atomCode (true,i,j)))
    (fun w => andList (c.map fun a => atomCode (replace n w a)))

def oneExistential (o : Bool) (n c : ℕ) :=
  if o then orList (((normal c).1.flatMap positiveClause).map (orderClause n))
  else orList ((normal c).1.map (equalityClause n))

def readIndex (n c : ℕ) : Option ℕ :=
  if c ≠ 0 ∧ tag c = 1 ∧ (args c).length = 1 ∧ arg c 0 < n then some (arg c 0) else none

abbrev Result := Option (ℕ × ℕ)

def runStep (o : Bool) (n c : ℕ) (a b u : Result) : Result :=
    if c = 0 then none else
    if tag c = 3 ∧ (args c).isEmpty then some (bot,bot) else
    if tag c = 4 ∧ (args c).length = 2 then
      (readIndex n (arg c 0)).elim none fun i =>
        (readIndex n (arg c 1)).elim none fun j =>
          let z := atomCode (false,i,j)
          some (z,z)
    else if o ∧ tag c = 5 ∧ (args c).length = 3 ∧ arg c 0 = 0 then
      (readIndex n (arg c 1)).elim none fun i =>
        (readIndex n (arg c 2)).elim none fun j =>
          let z := atomCode (true,i,j)
          some (z,z)
    else if tag c = 6 ∧ (args c).length = 2 then
      a.elim none fun a => b.elim none fun b => some (node 6 [a.1,b.1],node 6 [a.2,b.2])
    else if tag c = 7 ∧ (args c).length = 1 then
      u.elim none fun a => some (node 7 [a.1],neg (oneExistential o n (neg a.2)))
    else none


def runFuel (o : Bool) : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _, _ => none
  | fuel+1, n, c => runStep o n c (runFuel o fuel n (arg c 0)) (runFuel o fuel n (arg c 1)) (runFuel o fuel (n+1) (arg c 0))

def eliminate (o : Bool) (n c : ℕ) :=
  (runFuel o c n c).elim 0 (fun r => if r.1 = c then r.2 else 0)

def evalFuel : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel+1, c => if tag c = 6 then
      !(evalFuel fuel (arg c 0)) || evalFuel fuel (arg c 1)
    else false

def decideCode (o : Bool) (c : ℕ) :=
  let e := eliminate o 0 c
  evalFuel e e

section PrimitivePrograms
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

@[fun_prop] private theorem pr_flatMap {f : α → List β} {g : α → β → List γ}
    (hf : Primrec f) (hg : Primrec fun p : α × β => g p.1 p.2) :
    Primrec (fun x => (f x).flatMap (g x)) := Primrec.list_flatMap hf hg.to₂

@[fun_prop] private theorem pr_filterMap {f : α → List β} {g : α → β → Option γ}
    (hf : Primrec f) (hg : Primrec fun p : α × β => g p.1 p.2) :
    Primrec (fun x => (f x).filterMap (g x)) := Primrec.listFilterMap hf hg.to₂

@[fun_prop] private theorem pr_findSome {f : α → List β} {g : α → β → Option γ}
    (hf : Primrec f) (hg : Primrec fun p : α × β => g p.1 p.2) :
    Primrec (fun x => (f x).findSome? (g x)) := by
  have hs : Primrec fun p : α × (β × Option γ) => g p.1 p.2.1 <|> p.2.2 :=
    Primrec.option_orElse.comp (hg.to₂.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr hf (Primrec.const none) hs.to₂).of_eq
  intro x
  induction f x with
  | nil => rfl
  | cons b l ih => simp only [List.foldr_cons, List.findSome?_cons, ih]; cases g x b <;> rfl

@[fun_prop] private theorem pr_some {f : α → β} (hf : Primrec f) :
    Primrec (fun x => some (f x)) := Primrec.option_some.comp hf

@[fun_prop] private theorem pr_orElse {f g : α → Option β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x <|> g x) := Primrec.option_orElse.comp hf hg

@[fun_prop] private theorem pr_append {f g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x ++ g x) := Primrec.list_append.comp hf hg

@[fun_prop] private theorem pr_cross : Primrec (fun p : List (List β) × List (List β) => cross p.1 p.2) := by
  unfold cross
  fun_prop

@[fun_prop] private theorem pr_node : Primrec fun p : ℕ × List ℕ => node p.1 p.2 := by
  unfold node Seq.code
  fun_prop

@[fun_prop] private theorem pr_tag : Primrec tag := by unfold tag; fun_prop
@[fun_prop] private theorem pr_args : Primrec args := by unfold args Seq.decode; fun_prop
@[fun_prop] private theorem pr_arg : Primrec fun p : ℕ × ℕ => arg p.1 p.2 := by unfold arg; fun_prop
@[fun_prop] private theorem pr_neg : Primrec neg := by unfold neg; fun_prop
@[fun_prop] private theorem pr_conj : Primrec fun p : ℕ × ℕ => conj p.1 p.2 := by unfold conj; fun_prop
@[fun_prop] private theorem pr_disj : Primrec fun p : ℕ × ℕ => disj p.1 p.2 := by unfold disj; fun_prop
@[fun_prop] private theorem pr_varCode : Primrec varCode := by unfold varCode; fun_prop
@[fun_prop] private theorem pr_atomCode : Primrec atomCode := by unfold atomCode; fun_prop
@[fun_prop] private theorem pr_literalCode : Primrec literalCode := by unfold literalCode; fun_prop
@[fun_prop] private theorem pr_fromAtom : Primrec fromAtom := by unfold fromAtom; fun_prop
@[fun_prop] private theorem pr_fixed : Primrec fun p : ℕ × Atom => fixed p.1 p.2 := by unfold fixed; simp only [← Bool.cond_decide, Bool.decide_and]; fun_prop
@[fun_prop] private theorem pr_fixedLiteral : Primrec fun p : ℕ × Literal => fixedLiteral p.1 p.2 := by
  unfold fixedLiteral; fun_prop
@[fun_prop] private theorem pr_replace : Primrec fun p : (ℕ × ℕ) × Atom => replace p.1.1 p.1.2 p.2 := by
  unfold replace; fun_prop
@[fun_prop] private theorem pr_replace_apply {f g : α → ℕ} {h : α → Atom}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun x => replace (f x) (g x) (h x)) :=
  pr_replace.comp ((hf.pair hg).pair hh)
@[fun_prop] private theorem pr_fresh : Primrec fun p : ℕ × Atom => freshAtom p.1 p.2 := by
  unfold freshAtom; simp only [← Bool.cond_decide, Bool.decide_and]; fun_prop
@[fun_prop] private theorem pr_positiveLiteral : Primrec positiveLiteral := by unfold positiveLiteral; fun_prop
@[fun_prop] private theorem pr_independent : Primrec fun p : ℕ × Atom => independent p.1 p.2 := by
  unfold independent; simp only [← Bool.cond_decide, Bool.decide_and]; fun_prop
@[fun_prop] private theorem pr_lower : Primrec fun p : ℕ × Atom => lower p.1 p.2 := by unfold lower; simp only [← Bool.cond_decide, Bool.decide_and]; fun_prop
@[fun_prop] private theorem pr_upper : Primrec fun p : ℕ × Atom => upper p.1 p.2 := by unfold upper; simp only [← Bool.cond_decide, Bool.decide_and]; fun_prop
@[fun_prop] private theorem pr_selfStrict : Primrec fun p : ℕ × Atom => selfStrict p.1 p.2 := by
  unfold selfStrict; fun_prop

@[fun_prop] private theorem pr_andList : Primrec andList := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const top)
    ((pr_conj.to₂.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)).of_eq
  intro l
  change l.foldr conj top = andList l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons,andList,ih]

@[fun_prop] private theorem pr_orList : Primrec orList := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const bot)
    ((pr_disj.to₂.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)).of_eq
  intro l
  change l.foldr disj bot = orList l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons,orList,ih]

end PrimitivePrograms

def normalChildren (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  if p.1 = 0 then [] else [(p.1-1,arg p.2 0),(p.1-1,arg p.2 1)]

def normalResult (p : ℕ × ℕ) (rs : List (DNF × DNF)) : Option (DNF × DNF) :=
  some (if p.1 = 0 then ([],[]) else
    if p.2 = 0 then ([],[]) else
    if tag p.2 = 3 then ([],[ [] ]) else
    if tag p.2 = 4 ∨ tag p.2 = 5 then
      ([ [(true,fromAtom p.2)] ],[ [(false,fromAtom p.2)] ]) else
    if tag p.2 = 6 then
      let a := rs[0]?.getD ([],[])
      let b := rs[1]?.getD ([],[])
      (a.2 ++ b.1,cross a.1 b.2)
    else ([],[]))

private theorem normalChildren_primitive : Primrec normalChildren := by
  unfold normalChildren
  fun_prop

private theorem normalResult_primitive : Primrec₂ normalResult := by
  change Primrec (fun p : (ℕ × ℕ) × List (DNF × DNF) => normalResult p.1 p.2)
  unfold normalResult
  simp only [← Bool.cond_decide, Bool.decide_or]
  fun_prop

@[fun_prop] theorem normalFuel_primitive : Primrec (fun p : ℕ × ℕ => normalFuel p.1 p.2) := by
  apply Primrec.nat_omega_rec' _ Primrec.fst normalChildren_primitive normalResult_primitive
  · rintro ⟨fuel,c⟩ q hq
    cases fuel with
    | zero => simp [normalChildren] at hq
    | succ k =>
      simp only [normalChildren, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ↓reduceIte, Nat.add_sub_cancel, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> exact Nat.lt_succ_self _
  · rintro ⟨fuel,c⟩
    cases fuel with
    | zero => rfl
    | succ k => simp [normalChildren, normalResult, normalFuel]

@[fun_prop] theorem normal_primitive : Primrec normal := by
  exact normalFuel_primitive.comp (Primrec.id.pair Primrec.id)

@[fun_prop] private theorem pr_optionCases {α β γ : Type*}
    [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → Option β} {g : α → γ} {h : α → β → γ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec fun p : α × β => h p.1 p.2) :
    Primrec (fun x => (f x).elim (g x) (h x)) :=
  (Primrec.option_casesOn hf hg hh.to₂).of_eq fun x => by cases f x <;> rfl

@[fun_prop] private theorem positiveClause_primitive : Primrec positiveClause := by
  unfold positiveClause
  exact Primrec.list_foldr Primrec.id (Primrec.const [ [] ])
    ((pr_cross.to₂.comp (pr_positiveLiteral.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂)

@[fun_prop] private theorem equalityClause_primitive :
    Primrec (fun p : ℕ × Clause => equalityClause p.1 p.2) := by
  change Primrec (fun p : ℕ × Clause =>
    Option.elim (p.2.findSome? (fixedLiteral p.1))
      (andList (p.2.map fun l => if l.1 then freshAtom p.1 l.2 else neg (freshAtom p.1 l.2)))
      (fun w => andList (p.2.map fun l => literalCode (l.1,replace p.1 w l.2))))
  apply pr_optionCases <;> fun_prop

@[fun_prop] private theorem orderClause_primitive :
    Primrec (fun p : ℕ × List Atom => orderClause p.1 p.2) := by
  change Primrec (fun p : ℕ × List Atom =>
    if p.2.any (selfStrict p.1) then bot else
    Option.elim (p.2.findSome? (fixed p.1))
      (andList (p.2.map (independent p.1) ++
        (p.2.filterMap (lower p.1)).flatMap fun i =>
          (p.2.filterMap (upper p.1)).map fun j => atomCode (true,i,j)))
      (fun w => andList (p.2.map fun a => atomCode (replace p.1 w a))))
  apply PrimitiveRecursiveAutomation.ite
  · fun_prop
  · fun_prop
  · apply pr_optionCases <;> fun_prop

@[fun_prop] theorem oneExistential_primitive :
    Primrec (fun p : Bool × ℕ × ℕ => oneExistential p.1 p.2.1 p.2.2) := by
  unfold oneExistential
  fun_prop

@[fun_prop] private theorem readIndex_primitive : Primrec fun p : ℕ × ℕ => readIndex p.1 p.2 := by
  unfold readIndex
  simp only [← Bool.cond_decide, Bool.decide_and, decide_not]
  fun_prop


def runChildren (p : ℕ × ℕ × ℕ) : List (ℕ × ℕ × ℕ) :=
  if p.1 = 0 then [] else
    [(p.1-1,p.2.1,arg p.2.2 0),(p.1-1,p.2.1,arg p.2.2 1),
     (p.1-1,p.2.1+1,arg p.2.2 0)]

def runResult (o : Bool) (p : ℕ × ℕ × ℕ) (rs : List Result) : Option Result :=
  some (if p.1 = 0 then none else
    runStep o p.2.1 p.2.2 (rs[0]?.getD none) (rs[1]?.getD none) (rs[2]?.getD none))

@[fun_prop] private theorem pr_bind {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → Option β} {g : α → β → Option γ}
    (hf : Primrec f) (hg : Primrec fun p : α × β => g p.1 p.2) :
    Primrec (fun x => (f x).bind (g x)) := Primrec.option_bind hf hg.to₂

@[fun_prop] private theorem runStep_primitive (o : Bool) :
    Primrec (fun p : (ℕ × ℕ) × Result × Result × Result =>
      runStep o p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold runStep
  simp only [← Bool.cond_decide, Bool.decide_and]
  fun_prop

private theorem runChildren_primitive : Primrec runChildren := by
  unfold runChildren
  fun_prop

private theorem runResult_primitive (o : Bool) : Primrec₂ (runResult o) := by
  change Primrec (fun p : (ℕ × ℕ × ℕ) × List Result => runResult o p.1 p.2)
  unfold runResult
  apply pr_some
  apply PrimitiveRecursiveAutomation.ite
  · fun_prop
  · fun_prop
  · exact (runStep_primitive o).comp
      (show Primrec (fun x : (ℕ × ℕ × ℕ) × List Result =>
        ((x.1.2.1,x.1.2.2),x.2[0]?.getD none,x.2[1]?.getD none,x.2[2]?.getD none)) by fun_prop)

@[fun_prop] theorem runFuel_primitive (o : Bool) :
    Primrec (fun p : ℕ × ℕ × ℕ => runFuel o p.1 p.2.1 p.2.2) := by
  apply Primrec.nat_omega_rec' _ Primrec.fst runChildren_primitive (runResult_primitive o)
  · rintro ⟨fuel,n,c⟩ q hq
    cases fuel with
    | zero => simp [runChildren] at hq
    | succ k =>
      simp only [runChildren, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ↓reduceIte, Nat.add_sub_cancel, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact Nat.lt_succ_self _
  · rintro ⟨fuel,n,c⟩
    cases fuel with
    | zero => rfl
    | succ k => simp [runChildren, runResult, runFuel]


@[fun_prop] theorem eliminate_uncurried (o : Bool) : Primrec (fun p : ℕ × ℕ => eliminate o p.1 p.2) := by
  change Primrec (fun p : ℕ × ℕ => Option.elim (runFuel o p.2 p.1 p.2) 0
    (fun r => if r.1 = p.2 then r.2 else 0))
  fun_prop

def evalResult (p : ℕ × ℕ) (rs : List Bool) : Option Bool :=
  some (if p.1 = 0 then false else if tag p.2 = 6 then
    !(rs[0]?.getD false) || rs[1]?.getD false else false)

private theorem evalResult_primitive : Primrec₂ evalResult := by
  change Primrec (fun p : (ℕ × ℕ) × List Bool => evalResult p.1 p.2)
  unfold evalResult
  fun_prop

@[fun_prop] theorem evalFuel_primitive : Primrec (fun p : ℕ × ℕ => evalFuel p.1 p.2) := by
  apply Primrec.nat_omega_rec' _ Primrec.fst normalChildren_primitive evalResult_primitive
  · rintro ⟨fuel,c⟩ q hq
    cases fuel with
    | zero => simp [normalChildren] at hq
    | succ k =>
      simp only [normalChildren, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ↓reduceIte, Nat.add_sub_cancel, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> exact Nat.lt_succ_self _
  · rintro ⟨fuel,c⟩
    cases fuel with
    | zero => rfl
    | succ k => simp [normalChildren, evalResult, evalFuel]

theorem decideCode_primitive (o : Bool) : Primrec (decideCode o) := by
  unfold decideCode
  fun_prop

theorem eliminate_primitive (o : Bool) : Primrec₂ (eliminate o) := eliminate_uncurried o

end Lemmatheca.MathematicalLogic.EffectiveQuantifierPrograms
