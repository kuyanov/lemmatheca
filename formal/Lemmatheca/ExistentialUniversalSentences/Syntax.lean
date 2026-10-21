import Lemmatheca.CodingFormalProofs.CodingFormalProofsSyntax
import Mathlib.ModelTheory.Complexity

/-! Finite relational presentations and decoding the shared syntax codes. -/
namespace Lemmatheca.MathematicalLogic.ExistentialUniversalSentences
open FirstOrder FirstOrder.Language
open Lemmatheca.ProofTheory.CodingFormalProofs

inductive ConstantSymbol (c : ℕ) : ℕ → Type
  | constant (i : Fin c) : ConstantSymbol c 0

def lang (c : ℕ) (arities : List ℕ) : Language :=
  ⟨ConstantSymbol c, fun n => {i : Fin arities.length // arities[i] = n}⟩

variable (c : ℕ) (arities : List ℕ)

def signature : EffectiveSignature (lang c arities) where
  functionCode := fun f => match f with | .constant i => i.val
  relationCode := fun r => r.val.val
  functionTest := fun i n => decide (i < c ∧ n = 0)
  relationTest := fun i n => decide (i < arities.length ∧ arities[i]?.getD 0 = n)
  function_iff := by
    intro i n
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hi, rfl⟩
      exact ⟨.constant ⟨i, hi⟩, rfl⟩
    · rintro ⟨f, hf⟩
      cases f with | constant j => exact ⟨hf ▸ j.isLt, rfl⟩
  relation_iff := by
    intro i n
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hi, he⟩
      exact ⟨⟨⟨i, hi⟩, by simpa [List.getElem?_eq_getElem hi] using he⟩, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r.val.isLt, by simpa using r.property⟩
  function_injective := by
    intro n f g h
    cases f with | constant i => cases g with | constant j => exact congrArg ConstantSymbol.constant (Fin.ext h)
  relation_injective := by
    intro n f g h
    exact Subtype.ext (Fin.ext h)
  function_primrec := by
    exact ((Primrec.nat_lt.comp Primrec.fst (Primrec.const c)).and
      (Primrec.eq.comp Primrec.snd (Primrec.const 0))).decide
  relation_primrec := by
    have hget : Primrec (fun p : ℕ × ℕ => arities[p.1]?.getD 0) := by
      exact (Primrec.list_getD 0).comp (Primrec.const arities) Primrec.fst
    exact ((Primrec.nat_lt.comp Primrec.fst (Primrec.const arities.length)).and
      (Primrec.eq.comp hget Primrec.snd)).decide

def allBlock : (n : ℕ) → {m : ℕ} →
    (lang c arities).BoundedFormula Empty (m+n) → (lang c arities).BoundedFormula Empty m
  | 0, _, φ => φ
  | n+1, _, φ => allBlock n φ.all

def exBlock : (m : ℕ) → (lang c arities).BoundedFormula Empty m → (lang c arities).Sentence
  | 0, φ => φ
  | m+1, φ => exBlock m φ.ex

def sentence {m n : ℕ} (φ : (lang c arities).BoundedFormula Empty (m+n)) :
    (lang c arities).Sentence := exBlock c arities m (allBlock c arities n φ)

def readTerm (depth e : ℕ) : Option ((lang c arities).Term (Empty ⊕ Fin depth)) :=
  if e = 0 then none else
  match tag e, args e with
  | 1, [i] => if h : i < depth then some (.var (.inr ⟨i,h⟩)) else none
  | 2, [i] => if h : i < c then some (.func (.constant ⟨i,h⟩) Fin.elim0) else none
  | _, _ => none

def readFuel : ℕ → (depth : ℕ) → ℕ → Option {φ : (lang c arities).BoundedFormula Empty depth // φ.IsQF}
  | 0, _, _ => none
  | fuel+1, depth, e =>
    if e = 0 then none else
    match tag e, args e with
    | 3, [] => some ⟨.falsum, .falsum⟩
    | 4, [a,b] => do
      let t ← readTerm c arities depth a
      let u ← readTerm c arities depth b
      pure ⟨.equal t u, .of_isAtomic (.equal t u)⟩
    | 5, i :: aa =>
      if hi : i < arities.length then
        if hn : aa.length = arities[i] then do
          let ts ← aa.mapM (readTerm c arities depth)
          if ht : ts.length = arities[i] then
            pure ⟨.rel ⟨⟨i,hi⟩, rfl⟩ (fun j => ts[j.val]'(by simp [ht])),
              .of_isAtomic (.rel _ _)⟩
          else none
        else none
      else none
    | 6, [a,b] => do
      let φ ← readFuel fuel depth a
      let ψ ← readFuel fuel depth b
      pure ⟨.imp φ.val ψ.val, .imp φ.property ψ.property⟩
    | _, _ => none

def readMatrix (depth e : ℕ) : Option ((lang c arities).BoundedFormula Empty depth) :=
  ((readFuel c arities e depth e).map Subtype.val).filter
    (fun φ => decide (formulaCode (signature c arities) Empty.elim φ = e))

theorem readMatrix_spec {depth e : ℕ} {φ : (lang c arities).BoundedFormula Empty depth} :
    readMatrix c arities depth e = some φ →
    φ.IsQF ∧ formulaCode (signature c arities) Empty.elim φ = e := by
  intro h
  obtain ⟨h,hcode⟩ := Option.filter_eq_some_iff.mp h
  obtain ⟨q,hq,hval⟩ := Option.map_eq_some_iff.mp h
  subst φ
  exact ⟨q.property, of_decide_eq_true hcode⟩

private theorem node_ne_zero (t : ℕ) (aa : List ℕ) : node t aa ≠ 0 := by
  unfold node
  omega

private theorem readTerm_complete {depth : ℕ}
    (t : (lang c arities).Term (Empty ⊕ Fin depth)) :
    readTerm c arities depth
      (termCode (signature c arities) (Sum.elim Empty.elim (fun i => boundName i.val)) t) = some t := by
  cases t with
  | var i =>
    cases i with
    | inl e => exact e.elim
    | inr i => simp [termCode, boundName, readTerm, node_ne_zero, node_tag, node_args, i.isLt]
  | func f ts =>
    cases f with
    | constant i =>
      have he : ts = Fin.elim0 := Subsingleton.elim _ _
      subst ts
      simp [termCode, signature, readTerm, node_ne_zero, node_tag, node_args, i.isLt]

private theorem readFuel_complete {depth : ℕ}
    (φ : (lang c arities).BoundedFormula Empty depth) (hq : φ.IsQF)
    (fuel : ℕ) (hf : formulaCode (signature c arities) Empty.elim φ ≤ fuel) :
    readFuel c arities fuel depth (formulaCode (signature c arities) Empty.elim φ) =
      some ⟨φ,hq⟩ := by
  induction hq generalizing fuel with
  | falsum =>
    cases fuel with
    | zero => simp [formulaCode,botCode,node] at hf
    | succ fuel => simp [formulaCode,botCode,readFuel,node_ne_zero,node_tag,node_args]
  | of_isAtomic ha =>
    cases fuel with
    | zero => cases ha <;> simp [Term.bdEqual,Relations.boundedFormula,formulaCode,equalCode,node] at hf
    | succ fuel =>
      cases ha with
      | equal t u =>
        simp [Term.bdEqual,formulaCode,equalCode,readFuel,node_ne_zero,node_tag,node_args,readTerm_complete]
      | @rel ar r ts =>
        rcases r with ⟨i,hi⟩
        cases hi
        have hm : (List.ofFn (fun j => termCode (signature c arities)
            (Sum.elim Empty.elim (fun i => boundName i.val)) (ts j))).mapM
            (readTerm c arities depth) = some (List.ofFn ts) := by
          have he : List.ofFn (fun j => termCode (signature c arities)
              (Sum.elim Empty.elim (fun i => boundName i.val)) (ts j)) =
              (List.ofFn ts).map (termCode (signature c arities)
                (Sum.elim Empty.elim (fun i => boundName i.val))) := by
            simp only [List.map_ofFn]
            rfl
          rw [he,List.mapM_map]
          simp only [Function.comp_def,readTerm_complete]
          simpa using (List.mapM_pure (m := Option) (l := List.ofFn ts) (f := id))
        change readFuel c arities (fuel+1) depth
          (node 5 (i.val :: List.ofFn (fun j => termCode (signature c arities)
            (Sum.elim Empty.elim (fun i => boundName i.val)) (ts j)))) = _
        simp only [readFuel,node_ne_zero,node_tag,node_args,i.isLt,↓reduceDIte,↓reduceIte,
          List.length_ofFn,Fin.eta]
        rw [hm]
        simp [Relations.boundedFormula]

  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases fuel with
    | zero => simp [formulaCode,impCode,node] at hf
    | succ fuel =>
      have hp : formulaCode (signature c arities) Empty.elim φ ≤ fuel := by
        have hh : formulaCode (signature c arities) Empty.elim φ <
            formulaCode (signature c arities) Empty.elim (φ.imp ψ) := child_lt (by simp)
        omega
      have hq : formulaCode (signature c arities) Empty.elim ψ ≤ fuel := by
        have hh : formulaCode (signature c arities) Empty.elim ψ <
            formulaCode (signature c arities) Empty.elim (φ.imp ψ) := child_lt (by simp)
        omega
      simp [formulaCode,impCode,readFuel,node_ne_zero,node_tag,node_args,ihφ fuel hp,ihψ fuel hq]

theorem readMatrix_complete {depth : ℕ} (φ : (lang c arities).BoundedFormula Empty depth)
    (hq : φ.IsQF) :
    readMatrix c arities depth (formulaCode (signature c arities) Empty.elim φ) = some φ := by
  simp [readMatrix, readFuel_complete c arities φ hq _ le_rfl]

theorem readMatrix_recognition (depth e : ℕ) :
    (readMatrix c arities depth e).isSome = true ↔
    ∃ φ : (lang c arities).BoundedFormula Empty depth,
      φ.IsQF ∧ formulaCode (signature c arities) Empty.elim φ = e := by
  constructor
  · intro h
    obtain ⟨φ,hφ⟩ := Option.isSome_iff_exists.mp h
    exact ⟨φ,readMatrix_spec c arities hφ⟩
  · rintro ⟨φ,hq,rfl⟩
    simp [readMatrix_complete c arities φ hq]

end Lemmatheca.MathematicalLogic.ExistentialUniversalSentences
