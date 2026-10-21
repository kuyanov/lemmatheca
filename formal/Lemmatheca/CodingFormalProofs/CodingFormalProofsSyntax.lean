import Lemmatheca.CodingFormalProofs.CodingFormalProofs

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.CodingFormalProofs
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
noncomputable local instance : DecidableEq (L.Formula ℕ) := Classical.decEq _

private theorem termCode_injective_general {α : Type*} (name : α → ℕ)
    (hn : Function.Injective name) (ht : ∀ x, tag (name x) ≠ 2) :
    Function.Injective (termCode S name) := by
  intro t q h
  induction t generalizing q with
  | var x =>
    cases q with
    | var y => exact congrArg Term.var (hn h)
    | func f ts =>
      exact False.elim (ht x (by simpa only [termCode, node_tag] using congrArg tag h))
  | @func n f ts ih =>
    cases q with
    | var y =>
      exact False.elim (ht y (by simpa only [termCode, node_tag] using (congrArg tag h).symm))
    | @func m g us =>
      have hp := congrArg args h
      simp only [termCode, node_args, List.cons.injEq] at hp
      have hm : n = m := by simpa using congrArg List.length hp.2
      subst m
      have hg := S.function_injective n hp.1
      subst g
      congr 1
      funext i
      apply ih i
      have hh := congrArg (fun l : List ℕ => l[i.val]?) hp.2
      simpa using hh

private theorem freeName_injective : Function.Injective freeName := by
  intro a b h
  have := congrArg args h
  simpa only [freeName, node_args, List.cons.injEq, and_true] using this

private theorem auxName_injective : Function.Injective auxName := by
  intro a b h
  have := congrArg args h
  simpa only [auxName, node_args, List.cons.injEq, and_true] using this

private theorem mixedName_injective : Function.Injective (Sum.elim freeName auxName : ℕ ⊕ ℕ → ℕ) := by
  intro a b h
  cases a <;> cases b
  · exact congrArg Sum.inl (freeName_injective h)
  · have := congrArg tag h; simp [freeName,auxName,node_tag] at this
  · have := congrArg tag h; simp [freeName,auxName,node_tag] at this
  · exact congrArg Sum.inr (auxName_injective h)

private theorem scopedName_injective {α : Type*} (name : α → ℕ) (hn : Function.Injective name)
    (ht : ∀ a, tag (name a) = 0 ∨ tag (name a) = 8) (n : ℕ) :
    Function.Injective (Sum.elim name (fun i : Fin n => boundName i.val)) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (hn h)
    | inr b =>
      have hh : tag (name a) = 1 := by simpa only [Sum.elim_inl, Sum.elim_inr,boundName,node_tag] using congrArg tag h
      rcases ht a with hh' | hh' <;> omega
  | inr a =>
    cases b with
    | inl b =>
      have hh : tag (name b) = 1 := by simpa only [Sum.elim_inl, Sum.elim_inr,boundName,node_tag] using (congrArg tag h).symm
      rcases ht b with hh' | hh' <;> omega
    | inr b =>
      have hh := congrArg args h
      simp only [Sum.elim_inr,boundName,node_args,List.cons.injEq,and_true] at hh
      exact congrArg Sum.inr (Fin.ext hh)

private theorem scopedName_not_function {α : Type*} (name : α → ℕ)
    (ht : ∀ a, tag (name a) = 0 ∨ tag (name a) = 8) (n : ℕ)
    (a : α ⊕ Fin n) : tag (Sum.elim name (fun i : Fin n => boundName i.val) a) ≠ 2 := by
  cases a with
  | inl a => rcases ht a with h | h <;> simp [h]
  | inr a => simp [boundName,node_tag]

private theorem formulaCode_injective_general {α : Type*} (name : α → ℕ)
    (hn : Function.Injective name) (ht : ∀ a, tag (name a) = 0 ∨ tag (name a) = 8) {n : ℕ} :
    Function.Injective (fun a : L.BoundedFormula α n => formulaCode S name a) := by
  intro a b h
  induction a with
  | falsum =>
    cases b <;> first
    | rfl
    | have hh := congrArg tag h
      simp [formulaCode,botCode,equalCode,impCode,allCode,node_tag] at hh
  | equal t u =>
    cases b with
    | equal v w =>
      have hh := congrArg args h
      simp only [formulaCode,equalCode,node_args,List.cons.injEq,and_true] at hh
      exact congrArg₂ BoundedFormula.equal
        (termCode_injective_general S _ (scopedName_injective name hn ht _) (scopedName_not_function name ht _) hh.1)
        (termCode_injective_general S _ (scopedName_injective name hn ht _) (scopedName_not_function name ht _) hh.2)
    | _ =>
      have hh := congrArg tag h
      simp [formulaCode,botCode,equalCode,impCode,allCode,node_tag] at hh
  | @rel n k r ts =>
    cases b with
    | @rel m l q us =>
      have hp := congrArg args h
      simp only [formulaCode,node_args,List.cons.injEq] at hp
      have hk : k = l := by simpa using congrArg List.length hp.2
      subst l
      have hr := S.relation_injective k hp.1
      subst q
      congr 1
      funext i
      apply termCode_injective_general S _ (scopedName_injective name hn ht _) (scopedName_not_function name ht _)
      have hh := congrArg (fun xs : List ℕ => xs[i.val]?) hp.2
      simpa using hh
    | _ =>
      have hh := congrArg tag h
      simp [formulaCode,botCode,equalCode,impCode,allCode,node_tag] at hh
  | imp φ ψ ihφ ihψ =>
    cases b with
    | imp φ' ψ' =>
      have hh := congrArg args h
      simp only [formulaCode,impCode,node_args,List.cons.injEq,and_true] at hh
      exact congrArg₂ BoundedFormula.imp (ihφ hh.1) (ihψ hh.2)
    | _ =>
      have hh := congrArg tag h
      simp [formulaCode,botCode,equalCode,impCode,allCode,node_tag] at hh
  | all φ ih =>
    cases b with
    | all φ' =>
      have hh := congrArg args h
      simp only [formulaCode,allCode,node_args,List.cons.injEq,and_true] at hh
      exact congrArg BoundedFormula.all (ih hh)
    | _ =>
      have hh := congrArg tag h
      simp [formulaCode,botCode,equalCode,impCode,allCode,node_tag] at hh


theorem node_decompose (e : ℕ) (he : e ≠ 0) : node (tag e) (args e) = e := by
  simp only [node,tag,args,FiniteSequenceCoding.code_decode,Nat.pair_unpair]
  omega

theorem raw_child_lt (e a : ℕ) (he : e ≠ 0) (ha : a ∈ args e) : a < e := by
  simpa only [node_decompose e he] using (child_lt (t := tag e) ha)

theorem child_mem_args (e c : ℕ) (hc : c ∈ children e) : c ∈ args e := by
  unfold children at hc
  split at hc
  · exact List.mem_of_mem_tail hc
  · exact hc

theorem statsAt_history (e c : ℕ) (hc : c < e) :
    statsAt (FiniteSequenceCoding.historyCode (summaryStep S) e) c = stats S c := by
  simp only [statsAt,FiniteSequenceCoding.entry,FiniteSequenceCoding.history_identity,
    List.getElem?_map,List.getElem?_range,hc,Option.map_some,Option.getD_some]
  rfl


def summaryValue (t : ℕ) (aa : List ℕ) (ss : List Stats) : Stats :=
  let td := ss.foldl (fun m s => max m s.1) 1
  let fd := ss.foldl (fun m s => max m s.2.1) 1
  let fv := ss.foldl (fun m s => max m s.2.2.1) 0
  let av := ss.foldl (fun m s => max m s.2.2.2) 0
  let goodT := ss.all (fun s => s.1 > 0)
  let goodF := ss.all (fun s => s.2.1 > 0)
  let res : Stats := match t with
    | 0 => if aa.length = 1 then (1,0,1,0) else (0,0,0,0)
    | 1 => if aa.length = 1 then (aa[0]?.getD 0 + 2,0,0,0) else (0,0,0,0)
    | 2 => if aa.length > 0 ∧ S.functionTest (aa[0]?.getD 0) (aa.length-1) ∧ goodT then (td,0,fv,av) else (0,0,0,0)
    | 3 => if aa.isEmpty then (0,1,0,0) else (0,0,0,0)
    | 4 => if aa.length = 2 ∧ goodT then (0,td,fv,av) else (0,0,0,0)
    | 5 => if aa.length > 0 ∧ S.relationTest (aa[0]?.getD 0) (aa.length-1) ∧ goodT then (0,td,fv,av) else (0,0,0,0)
    | 6 => if aa.length = 2 ∧ goodF then (0,fd,fv,av) else (0,0,0,0)
    | 7 => if aa.length = 1 ∧ goodF then (0,max 1 (fd-1),fv,av) else (0,0,0,0)
    | 8 => if aa.length = 1 then (1,0,0,aa[0]?.getD 0+1) else (0,0,0,0)
    | _ => (0,0,0,0)
  res


theorem stats_node (t : ℕ) (aa : List ℕ) :
    stats S (node t aa) = summaryValue S t aa
      ((if t = 2 ∨ t = 5 then aa.tail else aa).map (stats S)) := by
  let e := node t aa
  let hist := FiniteSequenceCoding.historyCode (summaryStep S) e
  have he : e ≠ 0 := by simp [e,node]
  have hss : (children e).map (statsAt hist) = (children e).map (stats S) := by
    apply List.map_congr_left
    intro c hc
    exact statsAt_history S e c (raw_child_lt e c he (child_mem_args e c hc))
  change Denumerable.ofNat Stats (summaryStep S e hist) = _
  unfold summaryStep
  rw [hss]
  simp only [he,↓reduceIte]
  change Denumerable.ofNat Stats (Encodable.encode
    (summaryValue S (tag e) (args e) ((children e).map (stats S)))) = _
  rw [Denumerable.ofNat_encode]
  simp only [e,node_tag,node_args,children]

@[simp] theorem stats_free (i : ℕ) : stats S (freeName i) = (1,0,1,0) := by
  rw [freeName,stats_node]; rfl
@[simp] theorem stats_bound (i : ℕ) : stats S (boundName i) = (i+2,0,0,0) := by
  rw [boundName,stats_node]; rfl
@[simp] theorem stats_aux (i : ℕ) : stats S (auxName i) = (1,0,0,i+1) := by
  rw [auxName,stats_node]; rfl
@[simp] theorem stats_bot : stats S botCode = (0,1,0,0) := by
  rw [botCode,stats_node]; rfl

private theorem fold_max_bounds (xs : List Stats) (b z : ℕ) (hz : 0 < z ∧ z ≤ b)
    (hxs : ∀ x ∈ xs, 0 < x.1 ∧ x.1 ≤ b) :
    0 < (xs.foldl (fun m s => max m s.1) z) ∧ (xs.foldl (fun m s => max m s.1) z) ≤ b := by
  induction xs generalizing z with
  | nil => exact hz
  | cons a xs ih =>
    apply ih (max z a.1)
    · exact ⟨lt_of_lt_of_le hz.1 (le_max_left _ _), max_le hz.2 (hxs a (by simp)).2⟩
    · intro x hx; exact hxs x (by simp [hx])

theorem stats_function {k : ℕ} (f : L.Functions k) (cs : List ℕ) (hlen : cs.length = k)
    (hc : (cs.map (stats S)).all (fun s => s.1 > 0) = true) :
    stats S (node 2 (S.functionCode f :: cs)) =
      ((cs.map (stats S)).foldl (fun m s => max m s.1) 1, 0,
       (cs.map (stats S)).foldl (fun m s => max m s.2.2.1) 0,
       (cs.map (stats S)).foldl (fun m s => max m s.2.2.2) 0) := by
  have hf : S.functionTest (S.functionCode f) k = true := (S.function_iff _ _).mpr ⟨f,rfl⟩
  simp [stats_node,summaryValue,hlen,hf,hc]

attribute [local irreducible] stats

private theorem term_stats_valid {α : Type*} (name : α → ℕ) (n : ℕ)
    (hv : ∀ x, 0 < (stats S (name x)).1 ∧ (stats S (name x)).1 ≤ n+1)
    (t : L.Term α) :
    0 < (stats S (termCode S name t)).1 ∧ (stats S (termCode S name t)).1 ≤ n+1 := by
  induction t with
  | var x => exact hv x
  | @func k f ts ih =>
    let cs := List.ofFn (fun i : Fin k => termCode S name (ts i))
    have hcs : ∀ c ∈ cs.map (stats S), 0 < c.1 ∧ c.1 ≤ n+1 := by
      intro c hc
      rcases List.mem_map.mp hc with ⟨e,he,rfl⟩
      rcases List.mem_ofFn.mp he with ⟨i,rfl⟩
      exact ih i
    have hc : (cs.map (stats S)).all (fun s => s.1 > 0) = true := by
      apply List.all_eq_true.mpr
      intro c h
      exact decide_eq_true (hcs c h).1
    change 0 < (stats S (node 2 (S.functionCode f :: cs))).1 ∧ _
    have heq := congrArg Prod.fst (stats_function S f cs (List.length_ofFn) hc)
    have hb := fold_max_bounds (cs.map (stats S)) (n+1) 1
      ⟨by decide, Nat.succ_le_succ (Nat.zero_le n)⟩ hcs
    exact ⟨heq.symm ▸ hb.1, heq.symm ▸ hb.2⟩


private theorem fold_max_second_bounds (xs : List Stats) (b z : ℕ) (hz : 0 < z ∧ z ≤ b)
    (hxs : ∀ x ∈ xs, 0 < x.2.1 ∧ x.2.1 ≤ b) :
    0 < (xs.foldl (fun m s => max m s.2.1) z) ∧ (xs.foldl (fun m s => max m s.2.1) z) ≤ b := by
  induction xs generalizing z with
  | nil => exact hz
  | cons a xs ih =>
    apply ih (max z a.2.1)
    · exact ⟨lt_of_lt_of_le hz.1 (le_max_left _ _), max_le hz.2 (hxs a (by simp)).2⟩
    · intro x hx; exact hxs x (by simp [hx])

private theorem formula_stats_valid {α : Type*} (name : α → ℕ)
    (hv : ∀ x, (stats S (name x)).1 = 1) {n : ℕ} (a : L.BoundedFormula α n) :
    0 < (stats S (formulaCode S name a)).2.1 ∧ (stats S (formulaCode S name a)).2.1 ≤ n+1 := by
  induction a with
  | falsum => simp [formulaCode]
  | @equal n t u =>
    have hvar : ∀ x : α ⊕ Fin n,
        0 < (stats S (Sum.elim name (fun i => boundName i.val) x)).1 ∧
          (stats S (Sum.elim name (fun i => boundName i.val) x)).1 ≤ n+1 := by
      intro x; cases x with
      | inl i => simp [hv]
      | inr i => simp
    have ht := term_stats_valid S _ n hvar t
    have hu := term_stats_valid S _ n hvar u
    simp [formulaCode,equalCode,stats_node,summaryValue,ht.1,hu.1,ht.2,hu.2]

  | @rel n k r ts =>
    have hvar : ∀ x : α ⊕ Fin n,
        0 < (stats S (Sum.elim name (fun i => boundName i.val) x)).1 ∧
          (stats S (Sum.elim name (fun i => boundName i.val) x)).1 ≤ n+1 := by
      intro x; cases x with
      | inl i => simp [hv]
      | inr i => simp
    have ht (i : Fin k) := term_stats_valid S _ n hvar (ts i)
    let cs := List.ofFn (fun i : Fin k => termCode S (Sum.elim name (fun j => boundName j.val)) (ts i))
    have hcs : ∀ c ∈ cs.map (stats S), 0 < c.1 ∧ c.1 ≤ n+1 := by
      intro c hc
      rcases List.mem_map.mp hc with ⟨e,he,rfl⟩
      rcases List.mem_ofFn.mp he with ⟨i,rfl⟩
      exact ht i
    have hc : (cs.map (stats S)).all (fun s => s.1 > 0) = true := by
      apply List.all_eq_true.mpr
      intro c h
      exact decide_eq_true (hcs c h).1
    have hr : S.relationTest (S.relationCode r) k = true := (S.relation_iff _ _).mpr ⟨r,rfl⟩
    change 0 < (stats S (node 5 (S.relationCode r :: cs))).2.1 ∧ _
    have hs : (stats S (node 5 (S.relationCode r :: cs))).2.1 =
        (cs.map (stats S)).foldl (fun m s => max m s.1) 1 := by
      simp [stats_node,summaryValue,show cs.length = k from List.length_ofFn,hr,hc]
    have hb := fold_max_bounds (cs.map (stats S)) (n+1) 1
      ⟨by decide,Nat.succ_le_succ (Nat.zero_le n)⟩ hcs
    exact ⟨hs.symm ▸ hb.1, hs.symm ▸ hb.2⟩

  | imp a b iha ihb =>
    simp [formulaCode,impCode,stats_node,summaryValue,iha.1,ihb.1,iha.2,ihb.2]

  | all a ih =>
    simp [formulaCode,allCode,stats_node,summaryValue,ih.1]
    omega


private theorem foldMax_le_iff (p : Stats → ℕ) (xs : List Stats) (z b : ℕ) :
    xs.foldl (fun m s => max m (p s)) z ≤ b ↔ z ≤ b ∧ ∀ s ∈ xs, p s ≤ b := by
  induction xs generalizing z with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons,ih,max_le_iff,List.mem_cons,forall_eq_or_imp]
    tauto

private theorem foldMax_positive (p : Stats → ℕ) (xs : List Stats) :
    0 < xs.foldl (fun m s => max m (p s)) 1 := by
  have hb : ∀ z, 0 < z → 0 < xs.foldl (fun m s => max m (p s)) z := by
    induction xs with
    | nil => intro z hz; exact hz
    | cons a xs ih =>
      intro z hz
      exact ih _ (lt_of_lt_of_le hz (le_max_left _ _))
  exact hb 1 (by decide)

theorem isTerm_function_iff (n a : ℕ) (cs : List ℕ) :
    isTerm S n (node 2 (a :: cs)) = true ↔
      S.functionTest a cs.length = true ∧ ∀ c ∈ cs, isTerm S n c = true := by
  let ss := cs.map (stats S)
  by_cases hf : S.functionTest a cs.length = true
  · by_cases hc : ss.all (fun s => s.1 > 0) = true
    · have hpos := foldMax_positive Prod.fst ss
      have hbd := foldMax_le_iff Prod.fst ss 1 (n+1)
      have hall : ∀ c ∈ cs, 0 < (stats S c).1 := by
        intro c h
        exact of_decide_eq_true (List.all_eq_true.mp hc _ (List.mem_map.mpr ⟨c,h,rfl⟩))
      simp only [isTerm,Bool.and_eq_true,decide_eq_true_eq]
      simp [stats_node,summaryValue,hf,show (cs.map (stats S)).all (fun s => s.1 > 0) = true from hc,
        hpos,hbd,ss]
      constructor
      · intro h c hc; exact ⟨hall c hc,h c hc⟩
      · intro h c hc; exact (h c hc).2
    · have hnot : ¬ ∀ c ∈ cs, isTerm S n c = true := by
        intro h
        apply hc
        apply List.all_eq_true.mpr
        intro s hs
        rcases List.mem_map.mp hs with ⟨c,hc',rfl⟩
        have hp := h c hc'
        simp only [isTerm,Bool.and_eq_true,decide_eq_true_eq] at hp
        exact decide_eq_true hp.1
      have hbad : isTerm S n (node 2 (a :: cs)) = false := by
        simp [isTerm,stats_node,summaryValue,hf,show (cs.map (stats S)).all (fun s => s.1 > 0) ≠ true from hc]
      constructor
      · intro h; simp only [hbad,Bool.false_eq_true] at h
      · intro h; exact (hnot h.2).elim
  · simp [isTerm,stats_node,summaryValue,hf]


theorem term_code_recognition {n : ℕ} (t : L.Term (ℕ ⊕ Fin n)) :
    isTerm S n (termCode S (Sum.elim freeName (fun i => boundName i.val)) t) = true := by
  have h := term_stats_valid S (Sum.elim freeName (fun i : Fin n => boundName i.val)) n (fun x => by
    cases x with
    | inl i => simp
    | inr i => simp) t
  simpa only [isTerm,Bool.and_eq_true,decide_eq_true_eq] using h

theorem formula_code_recognition {n : ℕ} (a : L.BoundedFormula ℕ n) :
    isForm S n (formulaCode S freeName a) = true := by
  simpa only [isForm,Bool.and_eq_true,decide_eq_true_eq] using
    formula_stats_valid S freeName (fun _ => by simp) a

theorem term_code_injective {n : ℕ} : Function.Injective
    (termCode S (Sum.elim freeName (fun i : Fin n => boundName i.val))) := by
  exact termCode_injective_general S _
    (scopedName_injective freeName freeName_injective (fun _ => Or.inl (node_tag _ _)) n)
    (scopedName_not_function freeName (fun _ => Or.inl (node_tag _ _)) n)

theorem formula_code_injective {n : ℕ} : Function.Injective
    (fun a : L.BoundedFormula ℕ n => formulaCode S freeName a) := by
  exact formulaCode_injective_general S freeName freeName_injective (fun _ => Or.inl (node_tag _ _))

theorem sentence_code_injective : Function.Injective (sentenceCode S) := by
  exact formulaCode_injective_general S Empty.elim (by intro a; exact a.elim) (fun a => a.elim)

private theorem foldMax_start_le (p : Stats → ℕ) (xs : List Stats) (z : ℕ) :
    z ≤ xs.foldl (fun m s => max m (p s)) z := by
  induction xs generalizing z with
  | nil => exact le_rfl
  | cons a xs ih => exact (le_max_left z (p a)).trans (ih _)

private theorem foldMax_member_le (p : Stats → ℕ) (xs : List Stats) (z : ℕ)
    {a : Stats} (ha : a ∈ xs) : p a ≤ xs.foldl (fun m s => max m (p s)) z := by
  induction xs generalizing z with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact (le_max_right z (p a)).trans (foldMax_start_le p xs _)
    · exact ih _ ha

private theorem term_stats_support {α : Type*} [DecidableEq α] (name : α → ℕ) (n : ℕ)
    (hv : ∀ x, 0 < (stats S (name x)).1 ∧ (stats S (name x)).1 ≤ n+1)
    (t : L.Term α) (x : α) (hx : x ∈ t.varFinset) :
    (stats S (name x)).2.2.1 ≤ (stats S (termCode S name t)).2.2.1 ∧
    (stats S (name x)).2.2.2 ≤ (stats S (termCode S name t)).2.2.2 := by
  induction t with
  | var y =>
    have hxy : x = y := by simpa only [Term.varFinset, Finset.mem_singleton] using hx
    subst x
    exact ⟨le_rfl,le_rfl⟩
  | @func k f ts ih =>
    simp only [Term.varFinset,Finset.mem_biUnion,Finset.mem_univ,true_and] at hx
    rcases hx with ⟨i,hx⟩
    let cs := List.ofFn (fun i : Fin k => termCode S name (ts i))
    have hc : (cs.map (stats S)).all (fun s => s.1 > 0) = true := by
      apply List.all_eq_true.mpr
      intro c hc
      rcases List.mem_map.mp hc with ⟨e,he,rfl⟩
      rcases List.mem_ofFn.mp he with ⟨j,rfl⟩
      exact decide_eq_true (term_stats_valid S name n hv (ts j)).1
    have hi : stats S (termCode S name (ts i)) ∈ cs.map (stats S) :=
      List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i,rfl⟩, rfl⟩
    have heq := stats_function S f cs (List.length_ofFn) hc
    have hfv := congrArg (fun s : Stats => s.2.2.1) heq
    have hav := congrArg (fun s : Stats => s.2.2.2) heq
    exact ⟨(ih i hx).1.trans (hfv.symm ▸ foldMax_member_le (fun s : Stats => s.2.2.1) _ 0 hi),
      (ih i hx).2.trans (hav.symm ▸ foldMax_member_le (fun s : Stats => s.2.2.2) _ 0 hi)⟩

private theorem inl_mem_varFinset_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (t : L.Term (α ⊕ β)) (x : α) : Sum.inl x ∈ t.varFinset ↔ x ∈ t.varFinsetLeft := by
  induction t with
  | var y => cases y <;> simp
  | func f ts ih => simp only [Term.varFinset,Term.varFinsetLeft,Finset.mem_biUnion,Finset.mem_univ,true_and,ih]

private theorem scoped_stats_valid {α : Type*} (name : α → ℕ)
    (hv : ∀ x, (stats S (name x)).1 = 1) (n : ℕ) (x : α ⊕ Fin n) :
    0 < (stats S (Sum.elim name (fun i => boundName i.val) x)).1 ∧
      (stats S (Sum.elim name (fun i => boundName i.val) x)).1 ≤ n+1 := by
  cases x with
  | inl x => simp [hv]
  | inr i => simp

theorem formula_stats_support {α : Type*} [DecidableEq α] (name : α → ℕ)
    (hv : ∀ x, (stats S (name x)).1 = 1) {n : ℕ} (a : L.BoundedFormula α n)
    (x : α) (hx : x ∈ a.freeVarFinset) :
    (stats S (name x)).2.2.1 ≤ (stats S (formulaCode S name a)).2.2.1 ∧
    (stats S (name x)).2.2.2 ≤ (stats S (formulaCode S name a)).2.2.2 := by
  induction a with
  | falsum => simp at hx
  | @equal n t u =>
    have ht := term_stats_valid S _ n (scoped_stats_valid S name hv n) t
    have hu := term_stats_valid S _ n (scoped_stats_valid S name hv n) u
    have heq : stats S (formulaCode S name (.equal t u)) =
        (0, max (stats S (termCode S (Sum.elim name (fun i : Fin n => boundName i.val)) t)).1
          (stats S (termCode S (Sum.elim name (fun i : Fin n => boundName i.val)) u)).1,
        max (stats S (termCode S (Sum.elim name (fun i : Fin n => boundName i.val)) t)).2.2.1
          (stats S (termCode S (Sum.elim name (fun i : Fin n => boundName i.val)) u)).2.2.1,
        max (stats S (termCode S (Sum.elim name (fun i : Fin n => boundName i.val)) t)).2.2.2
          (stats S (termCode S (Sum.elim name (fun i : Fin n => boundName i.val)) u)).2.2.2) := by
      simp [formulaCode,equalCode,stats_node,summaryValue,ht.1,hu.1]
      omega
    simp only [BoundedFormula.freeVarFinset, Finset.mem_union] at hx
    rcases hx with hx | hx
    · have h := term_stats_support S _ n (scoped_stats_valid S name hv n) t (.inl x)
        ((inl_mem_varFinset_iff t x).mpr hx)
      rw [heq]
      exact ⟨h.1.trans (le_max_left _ _),h.2.trans (le_max_left _ _)⟩
    · have h := term_stats_support S _ n (scoped_stats_valid S name hv n) u (.inl x)
        ((inl_mem_varFinset_iff u x).mpr hx)
      rw [heq]
      exact ⟨h.1.trans (le_max_right _ _),h.2.trans (le_max_right _ _)⟩
  | @rel n k r ts =>
    simp only [BoundedFormula.freeVarFinset,Finset.mem_biUnion,Finset.mem_univ,true_and] at hx
    rcases hx with ⟨i,hx⟩
    let cs := List.ofFn (fun i : Fin k => termCode S (Sum.elim name (fun j : Fin n => boundName j.val)) (ts i))
    have hc : (cs.map (stats S)).all (fun s => s.1 > 0) = true := by
      apply List.all_eq_true.mpr
      intro c hc
      rcases List.mem_map.mp hc with ⟨e,he,rfl⟩
      rcases List.mem_ofFn.mp he with ⟨j,rfl⟩
      exact decide_eq_true (term_stats_valid S _ n (scoped_stats_valid S name hv n) (ts j)).1
    have hr : S.relationTest (S.relationCode r) k = true := (S.relation_iff _ _).mpr ⟨r,rfl⟩
    have heq : stats S (node 5 (S.relationCode r :: cs)) =
        (0, (cs.map (stats S)).foldl (fun m s => max m s.1) 1,
        (cs.map (stats S)).foldl (fun m s => max m s.2.2.1) 0,
        (cs.map (stats S)).foldl (fun m s => max m s.2.2.2) 0) := by
      simp [stats_node,summaryValue,show cs.length = k from List.length_ofFn,hr,hc]
    have hi : stats S (termCode S (Sum.elim name (fun j : Fin n => boundName j.val)) (ts i)) ∈
        cs.map (stats S) := List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
    have h := term_stats_support S _ n (scoped_stats_valid S name hv n) (ts i) (.inl x)
      ((inl_mem_varFinset_iff (ts i) x).mpr hx)
    have hfv := congrArg (fun s : Stats => s.2.2.1) heq
    have hav := congrArg (fun s : Stats => s.2.2.2) heq
    exact ⟨h.1.trans (hfv.symm ▸ foldMax_member_le (fun s : Stats => s.2.2.1) _ 0 hi),
      h.2.trans (hav.symm ▸ foldMax_member_le (fun s : Stats => s.2.2.2) _ 0 hi)⟩
  | imp a b iha ihb =>
    have ha := formula_stats_valid S name hv a
    have hb := formula_stats_valid S name hv b
    have heq : (stats S (formulaCode S name (.imp a b))).2.2 =
        (max (stats S (formulaCode S name a)).2.2.1 (stats S (formulaCode S name b)).2.2.1,
        max (stats S (formulaCode S name a)).2.2.2 (stats S (formulaCode S name b)).2.2.2) := by
      simp [formulaCode,impCode,stats_node,summaryValue,ha.1,hb.1]
    simp only [BoundedFormula.freeVarFinset,Finset.mem_union] at hx
    rcases hx with hx | hx
    · have h := iha hx
      have heq1 := congrArg Prod.fst heq
      have heq2 := congrArg Prod.snd heq
      exact ⟨heq1.symm ▸ h.1.trans (le_max_left _ _),heq2.symm ▸ h.2.trans (le_max_left _ _)⟩
    · have h := ihb hx
      have heq1 := congrArg Prod.fst heq
      have heq2 := congrArg Prod.snd heq
      exact ⟨heq1.symm ▸ h.1.trans (le_max_right _ _),heq2.symm ▸ h.2.trans (le_max_right _ _)⟩
  | all a ih =>
    have ha := formula_stats_valid S name hv a
    have h := ih hx
    have heq : (stats S (formulaCode S name (.all a))).2.2 =
        (stats S (formulaCode S name a)).2.2 := by
      simp [formulaCode,allCode,stats_node,summaryValue,ha.1]
    exact ⟨(congrArg Prod.fst heq).symm ▸ h.1,(congrArg Prod.snd heq).symm ▸ h.2⟩

theorem named_aux_mem_bound {n : ℕ} (a : L.BoundedFormula ℕ n) {j : ℕ}
    (h : j ∈ a.freeVarFinset) : j < (stats S (namedCode S a)).2.2.2 := by
  have hb := (formula_stats_support S auxName (fun _ => by simp) a j h).2
  simp only [stats_aux] at hb
  exact Nat.lt_of_succ_le hb

theorem mixed_aux_mem_bound {n : ℕ} (a : L.BoundedFormula (ℕ ⊕ ℕ) n) {j : ℕ}
    (h : Sum.inr j ∈ a.freeVarFinset) : j < (stats S (mixedCode S a)).2.2.2 := by
  have hv : ∀ x : ℕ ⊕ ℕ, (stats S (Sum.elim freeName auxName x)).1 = 1 := by
    intro x; cases x <;> simp
  have hb := (formula_stats_support S (Sum.elim freeName auxName) hv a (.inr j) h).2
  simp only [Sum.elim_inr,stats_aux] at hb
  exact Nat.lt_of_succ_le hb

private def statsFlag (aux : Bool) (s : Stats) : ℕ := if aux then s.2.2.2 else s.2.2.1

private theorem term_stats_flag_zero {α : Type*} (name : α → ℕ) (n : ℕ) (aux : Bool)
    (hv : ∀ x, 0 < (stats S (name x)).1 ∧ (stats S (name x)).1 ≤ n+1)
    (hz : ∀ x, statsFlag aux (stats S (name x)) = 0) (t : L.Term α) :
    statsFlag aux (stats S (termCode S name t)) = 0 := by
  induction t with
  | var x => exact hz x
  | @func k f ts ih =>
    let cs := List.ofFn (fun i : Fin k => termCode S name (ts i))
    have hc : (cs.map (stats S)).all (fun s => s.1 > 0) = true := by
      apply List.all_eq_true.mpr
      intro c hc
      rcases List.mem_map.mp hc with ⟨e,he,rfl⟩
      rcases List.mem_ofFn.mp he with ⟨j,rfl⟩
      exact decide_eq_true (term_stats_valid S name n hv (ts j)).1
    have hm : (cs.map (stats S)).foldl (fun m s => max m (statsFlag aux s)) 0 = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply (foldMax_le_iff _ _ _ _).mpr
      refine ⟨le_rfl,?_⟩
      intro s hs
      rcases List.mem_map.mp hs with ⟨e,he,rfl⟩
      rcases List.mem_ofFn.mp he with ⟨i,rfl⟩
      exact (ih i).le
    change statsFlag aux (stats S (node 2 (S.functionCode f :: cs))) = 0
    rw [stats_function S f cs List.length_ofFn hc]
    cases aux <;> simpa [statsFlag] using hm

private theorem formula_stats_flag_zero {α : Type*} (name : α → ℕ) (aux : Bool)
    (hv : ∀ x, (stats S (name x)).1 = 1)
    (hz : ∀ x, statsFlag aux (stats S (name x)) = 0)
    {n : ℕ} (a : L.BoundedFormula α n) : statsFlag aux (stats S (formulaCode S name a)) = 0 := by
  have hzScoped (n : ℕ) (x : α ⊕ Fin n) :
      statsFlag aux (stats S (Sum.elim name (fun j => boundName j.val) x)) = 0 := by
    cases x with
    | inl x => exact hz x
    | inr i => cases aux <;> simp [statsFlag]
  induction a with
  | falsum => cases aux <;> simp [formulaCode,statsFlag]
  | @equal n t u =>
    have ht := term_stats_valid S _ n (scoped_stats_valid S name hv n) t
    have hu := term_stats_valid S _ n (scoped_stats_valid S name hv n) u
    have htz := term_stats_flag_zero S _ n aux (scoped_stats_valid S name hv n) (hzScoped n) t
    have huz := term_stats_flag_zero S _ n aux (scoped_stats_valid S name hv n) (hzScoped n) u
    cases aux <;> simp [statsFlag] at htz huz ⊢ <;>
      simp [formulaCode,equalCode,stats_node,summaryValue,ht.1,hu.1,htz,huz]
  | @rel n k r ts =>
    let cs := List.ofFn (fun i : Fin k => termCode S (Sum.elim name (fun j : Fin n => boundName j.val)) (ts i))
    have hc : (cs.map (stats S)).all (fun s => s.1 > 0) = true := by
      apply List.all_eq_true.mpr
      intro c hc
      rcases List.mem_map.mp hc with ⟨e,he,rfl⟩
      rcases List.mem_ofFn.mp he with ⟨j,rfl⟩
      exact decide_eq_true (term_stats_valid S _ n (scoped_stats_valid S name hv n) (ts j)).1
    have hm : (cs.map (stats S)).foldl (fun m s => max m (statsFlag aux s)) 0 = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply (foldMax_le_iff _ _ _ _).mpr
      refine ⟨le_rfl,?_⟩
      intro s hs
      rcases List.mem_map.mp hs with ⟨e,he,rfl⟩
      rcases List.mem_ofFn.mp he with ⟨i,rfl⟩
      exact (term_stats_flag_zero S _ n aux (scoped_stats_valid S name hv n) (hzScoped n) (ts i)).le
    have hr : S.relationTest (S.relationCode r) k = true := (S.relation_iff _ _).mpr ⟨r,rfl⟩
    change statsFlag aux (stats S (node 5 (S.relationCode r :: cs))) = 0
    cases aux <;> simpa [statsFlag,stats_node,summaryValue,show cs.length = k from List.length_ofFn,hr,hc] using hm
  | imp a b iha ihb =>
    have ha := formula_stats_valid S name hv a
    have hb := formula_stats_valid S name hv b
    cases aux <;> simp [statsFlag] at iha ihb ⊢ <;>
      simp [formulaCode,impCode,stats_node,summaryValue,ha.1,hb.1,iha,ihb]
  | all a ih =>
    have ha := formula_stats_valid S name hv a
    cases aux <;> simp [statsFlag] at ih ⊢ <;>
      simp [formulaCode,allCode,stats_node,summaryValue,ha.1,ih]

private theorem termCode_restrictVar {α β : Type*} [DecidableEq α]
    (name : α → ℕ) (name' : β → ℕ) (t : L.Term α) :
    ∀ (f : t.varFinset → β), (∀ x, name' (f x) = name x.val) →
      termCode S name' (t.restrictVar f) = termCode S name t := by
  induction t with
  | var x => intro f hf; exact hf ⟨x,by simp⟩
  | func g ts ih =>
    intro f hf
    simp only [Term.restrictVar,termCode]
    congr 2
    apply congrArg List.ofFn
    funext i
    apply ih i
    intro x
    exact hf _

private theorem termCode_restrictVarLeft {α β γ : Type*} [DecidableEq α]
    (name : α → ℕ) (name' : β → ℕ) (bound : γ → ℕ) (t : L.Term (α ⊕ γ)) :
    ∀ (f : t.varFinsetLeft → β), (∀ x, name' (f x) = name x.val) →
      termCode S (Sum.elim name' bound) (t.restrictVarLeft f) =
        termCode S (Sum.elim name bound) t := by
  induction t with
  | var x =>
    intro f hf
    cases x with
    | inl x => exact hf ⟨x,by simp⟩
    | inr i => rfl
  | func g ts ih =>
    intro f hf
    simp only [Term.restrictVarLeft,termCode]
    congr 2
    apply congrArg List.ofFn
    funext i
    apply ih i
    intro x
    exact hf _

theorem formulaCode_restrictFreeVar {α β : Type*} [DecidableEq α]
    (name : α → ℕ) (name' : β → ℕ) {n : ℕ} (a : L.BoundedFormula α n) :
    ∀ (f : a.freeVarFinset → β), (∀ x, name' (f x) = name x.val) →
      formulaCode S name' (a.restrictFreeVar f) = formulaCode S name a := by
  induction a with
  | falsum => intros; rfl
  | equal t u =>
    intro f hf
    simp only [BoundedFormula.restrictFreeVar,formulaCode]
    congr 1
    · apply termCode_restrictVarLeft S
      intro x
      exact hf _
    · apply termCode_restrictVarLeft S
      intro x
      exact hf _
  | rel r ts =>
    intro f hf
    simp only [BoundedFormula.restrictFreeVar,formulaCode]
    congr 2
    apply congrArg List.ofFn
    funext i
    apply termCode_restrictVarLeft S
    intro x
    exact hf _
  | imp a b iha ihb =>
    intro f hf
    simp only [BoundedFormula.restrictFreeVar,formulaCode]
    congr 1
    · apply iha; intro x; exact hf _
    · apply ihb; intro x; exact hf _
  | all a ih =>
    intro f hf
    simp only [BoundedFormula.restrictFreeVar,formulaCode]
    congr 1
    apply ih; intro x; exact hf _

private theorem raw_stats_zero : stats S 0 = (0,0,0,0) := by
  unfold stats earlierFold FiniteSequenceCoding.historyValue summaryStep
  simp only [ite_true, Denumerable.ofNat_encode]

private theorem mixed_term_valid {n : ℕ} (t : L.Term ((ℕ ⊕ ℕ) ⊕ Fin n)) :
    isTerm S n (termCode S (Sum.elim (Sum.elim freeName auxName) (fun j => boundName j.val)) t) = true := by
  induction t with
  | var x =>
    cases x with
    | inl x => cases x <;> simp [termCode, isTerm]
    | inr i => simp [termCode, isTerm]
  | @func k f ts ih =>
    apply (isTerm_function_iff S n _ _).mpr
    refine ⟨by simpa only [List.length_ofFn] using (S.function_iff _ k).mpr ⟨f, rfl⟩, ?_⟩
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact ih i

set_option maxHeartbeats 500000 in
private theorem mixed_term_reconstruct (n e : ℕ) (h : isTerm S n e = true) :
    ∃ t : L.Term ((ℕ ⊕ ℕ) ⊕ Fin n),
      termCode S (Sum.elim (Sum.elim freeName auxName) (fun j => boundName j.val)) t = e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e = 0
    · subst e
      simp [isTerm, raw_stats_zero] at h
    generalize haa : args e = aa
    generalize htag : tag e = t
    have heq : node t aa = e := by
      rw [← haa, ← htag]
      exact node_decompose e he
    rw [← heq] at h ⊢
    rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | t
    · have hlen : aa.length = 1 := by
        by_contra hn
        simp [isTerm, stats_node, summaryValue, hn] at h
      obtain ⟨i, hia⟩ := List.length_eq_one_iff.mp hlen
      rw [hia] at h ⊢
      exact ⟨.var (.inl (.inl i)), rfl⟩
    · have hlen : aa.length = 1 := by
        by_contra hn
        simp [isTerm, stats_node, summaryValue, hn] at h
      obtain ⟨i, hia⟩ := List.length_eq_one_iff.mp hlen
      rw [hia] at h ⊢
      have hi : i < n := by
        simp [isTerm, stats_node, summaryValue] at h
        omega
      exact ⟨.var (.inr ⟨i, hi⟩), rfl⟩
    · cases aa with
      | nil => simp [isTerm, stats_node, summaryValue] at h
      | cons a cs =>
        obtain ⟨hf, hc⟩ := (isTerm_function_iff S n a cs).mp h
        obtain ⟨f, hf⟩ := (S.function_iff a cs.length).mp hf
        have ht (i : Fin cs.length) :
            ∃ t : L.Term ((ℕ ⊕ ℕ) ⊕ Fin n),
              termCode S (Sum.elim (Sum.elim freeName auxName) (fun j => boundName j.val)) t = cs[i] := by
          have hi : cs[i] ∈ cs := List.getElem_mem _
          have hlt : cs[i] < e := by
            rw [← heq]
            exact child_lt (List.mem_cons_of_mem _ hi)
          exact ih _ hlt (hc _ hi)
        choose ts hts using ht
        refine ⟨.func f ts, ?_⟩
        simp only [termCode, hf, hts]
        congr 2
        exact List.ofFn_getElem
    · simp only [isTerm, stats_node, summaryValue] at h
      split_ifs at h <;> simp at h
    · simp only [isTerm, stats_node, summaryValue] at h
      split_ifs at h <;> simp at h
    · simp only [isTerm, stats_node, summaryValue] at h
      split_ifs at h <;> simp at h
    · simp only [isTerm, stats_node, summaryValue] at h
      split_ifs at h <;> simp at h
    · simp only [isTerm, stats_node, summaryValue] at h
      split_ifs at h <;> simp at h
    · have hlen : aa.length = 1 := by
        by_contra hn
        simp [isTerm, stats_node, summaryValue, hn] at h
      obtain ⟨i, hia⟩ := List.length_eq_one_iff.mp hlen
      rw [hia] at h ⊢
      exact ⟨.var (.inl (.inr i)), rfl⟩
    · simp [isTerm, stats_node, summaryValue] at h

theorem mixed_term_recognition_iff (n e : ℕ) : isTerm S n e = true ↔
    ∃ t : L.Term ((ℕ ⊕ ℕ) ⊕ Fin n),
      termCode S (Sum.elim (Sum.elim freeName auxName) (fun j => boundName j.val)) t = e := by
  constructor
  · exact mixed_term_reconstruct S n e
  · rintro ⟨t,rfl⟩
    exact mixed_term_valid S t

private theorem raw_fold_le (p : Stats → ℕ) (xs : List Stats) (z b : ℕ) :
    xs.foldl (fun m s => max m (p s)) z ≤ b ↔ z ≤ b ∧ ∀ s ∈ xs, p s ≤ b := by
  induction xs generalizing z with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons,ih,max_le_iff,List.mem_cons,forall_eq_or_imp]
    tauto

private theorem raw_fold_positive (p : Stats → ℕ) (xs : List Stats) :
    0 < xs.foldl (fun m s => max m (p s)) 1 := by
  have hb : ∀ z, 0 < z → 0 < xs.foldl (fun m s => max m (p s)) z := by
    induction xs with
    | nil => intro z hz; exact hz
    | cons a xs ih =>
      intro z hz
      exact ih _ (lt_of_lt_of_le hz (le_max_left _ _))
  exact hb 1 (by decide)

private theorem raw_relation_iff (n a : ℕ) (cs : List ℕ) :
    isForm S n (node 5 (a :: cs)) = true ↔
      S.relationTest a cs.length = true ∧ ∀ c ∈ cs, isTerm S n c = true := by
  let ss := cs.map (stats S)
  by_cases hf : S.relationTest a cs.length = true
  · by_cases hc : ss.all (fun s => s.1 > 0) = true
    · have hpos := raw_fold_positive Prod.fst ss
      have hbd := raw_fold_le Prod.fst ss 1 (n+1)
      have hall : ∀ c ∈ cs, 0 < (stats S c).1 := by
        intro c h
        exact of_decide_eq_true (List.all_eq_true.mp hc _ (List.mem_map.mpr ⟨c,h,rfl⟩))
      simp only [isForm,isTerm,Bool.and_eq_true,decide_eq_true_eq]
      simp [stats_node,summaryValue,hf,show (cs.map (stats S)).all (fun s => s.1 > 0) = true from hc,
        hpos,hbd,ss]
      constructor
      · intro h c hc; exact ⟨hall c hc,h c hc⟩
      · intro h c hc; exact (h c hc).2
    · have hnot : ¬ ∀ c ∈ cs, isTerm S n c = true := by
        intro h
        apply hc
        apply List.all_eq_true.mpr
        intro s hs
        rcases List.mem_map.mp hs with ⟨c,hc',rfl⟩
        have hp := h c hc'
        simp only [isTerm,Bool.and_eq_true,decide_eq_true_eq] at hp
        exact decide_eq_true hp.1
      have hbad : isForm S n (node 5 (a :: cs)) = false := by
        simp [isForm,stats_node,summaryValue,hf,show (cs.map (stats S)).all (fun s => s.1 > 0) ≠ true from hc]
      constructor
      · intro h; simp only [hbad,Bool.false_eq_true] at h
      · intro h; exact (hnot h.2).elim
  · simp [isForm,stats_node,summaryValue,hf]


private theorem raw_equal_iff (n a b : ℕ) :
    isForm S n (equalCode a b) = true ↔ isTerm S n a = true ∧ isTerm S n b = true := by
  by_cases ha : 0 < (stats S a).1 <;> by_cases hb : 0 < (stats S b).1
  all_goals simp [isForm, isTerm, equalCode, stats_node, summaryValue, ha, hb ]

private theorem raw_imp_iff (n a b : ℕ) :
    isForm S n (impCode a b) = true ↔ isForm S n a = true ∧ isForm S n b = true := by
  by_cases ha : 0 < (stats S a).2.1 <;> by_cases hb : 0 < (stats S b).2.1
  all_goals simp [isForm, impCode, stats_node, summaryValue, ha, hb ]

private theorem raw_all_iff (n a : ℕ) :
    isForm S n (allCode a) = true ↔ isForm S (n+1) a = true := by
  by_cases ha : 0 < (stats S a).2.1
  · simp [isForm, allCode, stats_node, summaryValue, ha ]
  · simp [isForm, allCode, stats_node, summaryValue, ha]

private theorem raw_length_two {α : Type*} (xs : List α) (h : xs.length = 2) :
    ∃ a b, xs = [a,b] := by
  cases xs with
  | nil => simp at h
  | cons a tail =>
    cases tail with
    | nil => simp at h
    | cons b rest =>
      have hr : rest.length = 0 := by simp only [List.length_cons] at h; omega
      have he : rest = [] := List.length_eq_zero_iff.mp hr
      exact ⟨a,b,by rw [he]⟩

private theorem mixed_formula_valid {n : ℕ} (a : L.BoundedFormula (ℕ ⊕ ℕ) n) :
    isForm S n (mixedCode S a) = true := by
  induction a with
  | falsum => simp [mixedCode, formulaCode, isForm]
  | equal s t => exact (raw_equal_iff S _ _ _).mpr ⟨mixed_term_valid S s, mixed_term_valid S t⟩
  | @rel n k r ts =>
    apply (raw_relation_iff S n _ _).mpr
    refine ⟨by simpa only [List.length_ofFn] using (S.relation_iff _ k).mpr ⟨r, rfl⟩, ?_⟩
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact mixed_term_valid S (ts i)
  | imp a b iha ihb => exact (raw_imp_iff S _ _ _).mpr ⟨iha, ihb⟩
  | all a ih => exact (raw_all_iff S _ _).mpr ih

set_option maxHeartbeats 600000 in
private theorem mixed_formula_reconstruct (n e : ℕ) (h : isForm S n e = true) :
    ∃ a : L.BoundedFormula (ℕ ⊕ ℕ) n, mixedCode S a = e := by
  induction e using Nat.strong_induction_on generalizing n with
  | h e ih =>
    by_cases he : e = 0
    · subst e
      simp [isForm, raw_stats_zero] at h
    generalize haa : args e = aa
    generalize htag : tag e = t
    have heq : node t aa = e := by
      rw [← haa, ← htag]
      exact node_decompose e he
    rw [← heq] at h ⊢
    rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | t
    · simp only [isForm, stats_node, summaryValue] at h
      split_ifs at h <;> simp at h
    · simp only [isForm, stats_node, summaryValue] at h
      split_ifs at h <;> simp at h
    · simp only [isForm, stats_node, summaryValue] at h
      split_ifs at h <;> simp at h
    · by_cases ha : aa = []
      · rw [ha]
        exact ⟨.falsum, rfl⟩
      · simp [isForm, stats_node, summaryValue, ha] at h
    · have hlen : aa.length = 2 := by
        by_contra hn
        simp [isForm, stats_node, summaryValue, hn] at h
      obtain ⟨a, b, hab⟩ := raw_length_two aa hlen
      rw [hab] at h ⊢
      obtain ⟨ha, hb⟩ := (raw_equal_iff S n a b).mp h
      obtain ⟨s, hs⟩ := (mixed_term_recognition_iff S n a).mp ha
      obtain ⟨t, ht⟩ := (mixed_term_recognition_iff S n b).mp hb
      exact ⟨.equal s t, by simp only [mixedCode, formulaCode, hs, ht, equalCode]⟩
    · cases aa with
      | nil => simp [isForm, stats_node, summaryValue] at h
      | cons a cs =>
        obtain ⟨hr, hc⟩ := (raw_relation_iff S n a cs).mp h
        obtain ⟨r, hr⟩ := (S.relation_iff a cs.length).mp hr
        have ht (i : Fin cs.length) :
            ∃ t : L.Term ((ℕ ⊕ ℕ) ⊕ Fin n),
              termCode S (Sum.elim (Sum.elim freeName auxName) (fun j => boundName j.val)) t = cs[i] :=
          (mixed_term_recognition_iff S n _).mp (hc _ (List.getElem_mem _))
        choose ts hts using ht
        refine ⟨.rel r ts, ?_⟩
        simp only [mixedCode, formulaCode, hr, hts]
        congr 2
        exact List.ofFn_getElem
    · have hlen : aa.length = 2 := by
        by_contra hn
        simp [isForm, stats_node, summaryValue, hn] at h
      obtain ⟨a, b, hab⟩ := raw_length_two aa hlen
      rw [hab] at h ⊢
      obtain ⟨ha, hb⟩ := (raw_imp_iff S n a b).mp h
      have hla : a < e := by
        rw [← heq, hab]
        exact child_lt (by simp)
      have hlb : b < e := by
        rw [← heq, hab]
        exact child_lt (by simp)
      obtain ⟨A, hA⟩ := ih a hla n ha
      obtain ⟨B, hB⟩ := ih b hlb n hb
      refine ⟨.imp A B, ?_⟩
      change impCode (mixedCode S A) (mixedCode S B) = node 6 [a,b]
      rw [hA,hB]
      rfl
    · have hlen : aa.length = 1 := by
        by_contra hn
        simp [isForm, stats_node, summaryValue, hn] at h
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hlen
      rw [hb] at h ⊢
      have hv := (raw_all_iff S n b).mp h
      have hlb : b < e := by
        rw [← heq, hb]
        exact child_lt (by simp)
      obtain ⟨A, hA⟩ := ih b hlb (n+1) hv
      refine ⟨.all A, ?_⟩
      change allCode (mixedCode S A) = node 7 [b]
      rw [hA]
      rfl
    · simp only [isForm, stats_node, summaryValue] at h
      split_ifs at h <;> simp at h
    · simp [isForm, stats_node, summaryValue] at h

theorem mixed_recognition_iff (n e : ℕ) : isForm S n e = true ↔
    ∃ a : L.BoundedFormula (ℕ ⊕ ℕ) n, mixedCode S a = e := by
  constructor
  · exact mixed_formula_reconstruct S n e
  · rintro ⟨a,rfl⟩
    exact mixed_formula_valid S a

theorem named_term_recognition_iff (e : ℕ) : namedTerm S e = true ↔
    ∃ t : L.Term ℕ, termCode S auxName t = e := by
  classical
  constructor
  · intro h
    simp only [namedTerm,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨t,ht⟩ := mixed_term_reconstruct S 0 e h.1
    let name : ((ℕ ⊕ ℕ) ⊕ Fin 0) → ℕ :=
      Sum.elim (Sum.elim freeName auxName) (fun j => boundName j.val)
    have hv : ∀ x, 0 < (stats S (name x)).1 ∧ (stats S (name x)).1 ≤ 0+1 := by
      intro x
      cases x with
      | inl x => cases x <;> simp [name]
      | inr i => exact Fin.elim0 i
    let f : t.varFinset → ℕ := fun x => Sum.elim (Sum.elim id id) Fin.elim0 x.val
    have hf : ∀ x, auxName (f x) = name x.val := by
      intro x
      rcases x with ⟨x,hx⟩
      cases x with
      | inl x =>
        cases x with
        | inl i =>
          have hb := (term_stats_support S name 0 hv t (.inl (.inl i)) hx).1
          have hz : (stats S (termCode S name t)).2.2.1 = 0 := by rw [ht]; exact h.2
          simp only [name,Sum.elim_inl,stats_free,hz] at hb
          omega
        | inr i => rfl
      | inr i => exact Fin.elim0 i
    exact ⟨t.restrictVar f,(termCode_restrictVar S name auxName t f hf).trans ht⟩
  · rintro ⟨t,rfl⟩
    have hv : ∀ i : ℕ, 0 < (stats S (auxName i)).1 ∧ (stats S (auxName i)).1 ≤ 0+1 := by simp
    have ht := term_stats_valid S auxName 0 hv t
    have hz := term_stats_flag_zero S auxName 0 false hv (fun _ => by simp [statsFlag]) t
    simp only [statsFlag,Bool.false_eq_true,ite_false] at hz
    simp only [namedTerm,isTerm,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨ht,hz⟩

theorem named_recognition_iff (n e : ℕ) : namedForm S n e = true ↔
    ∃ a : L.BoundedFormula ℕ n, namedCode S a = e := by
  classical
  constructor
  · intro h
    simp only [namedForm,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨a,ha⟩ := mixed_formula_reconstruct S n e h.1
    let name : ℕ ⊕ ℕ → ℕ := Sum.elim freeName auxName
    have hv : ∀ x, (stats S (name x)).1 = 1 := by intro x; cases x <;> simp [name]
    let f : a.freeVarFinset → ℕ := fun x => Sum.elim id id x.val
    have hf : ∀ x, auxName (f x) = name x.val := by
      intro x
      rcases x with ⟨x,hx⟩
      cases x with
      | inl i =>
        have hb := (formula_stats_support S name hv a (.inl i) hx).1
        have hz : (stats S (formulaCode S name a)).2.2.1 = 0 := by
          change (stats S (mixedCode S a)).2.2.1 = 0
          rw [ha]
          exact h.2
        simp only [name,Sum.elim_inl,stats_free,hz] at hb
        omega
      | inr i => rfl
    exact ⟨a.restrictFreeVar f,(formulaCode_restrictFreeVar S name auxName a f hf).trans ha⟩
  · rintro ⟨a,rfl⟩
    have hv : ∀ i : ℕ, (stats S (auxName i)).1 = 1 := by simp
    have ha := formula_stats_valid S auxName hv a
    have hz := formula_stats_flag_zero S auxName false hv (fun _ => by simp [statsFlag]) a
    simp only [statsFlag,Bool.false_eq_true,ite_false] at hz
    simp only [namedForm,isForm,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨ha,hz⟩

theorem sentence_recognition_iff (e : ℕ) : isSentence S e = true ↔
    ∃ a : L.Sentence, sentenceCode S a = e := by
  classical
  constructor
  · intro h
    simp only [isSentence,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨a,ha⟩ := (named_recognition_iff S 0 e).mp h.1
    have hn : ∀ x : a.freeVarFinset, False := by
      intro x
      have hb := named_aux_mem_bound S a x.property
      rw [ha] at hb
      omega
    let f : a.freeVarFinset → Empty := fun x => False.elim (hn x)
    have hf : ∀ x, Empty.elim (f x) = auxName x.val := fun x => False.elim (hn x)
    exact ⟨a.restrictFreeVar f,(formulaCode_restrictFreeVar S auxName Empty.elim a f hf).trans ha⟩
  · rintro ⟨a,rfl⟩
    have hv : ∀ x : Empty, (stats S (Empty.elim x)).1 = 1 := fun x => x.elim
    have ha := formula_stats_valid S Empty.elim hv a
    have hf := formula_stats_flag_zero S Empty.elim false hv (fun x => x.elim) a
    have hg := formula_stats_flag_zero S Empty.elim true hv (fun x => x.elim) a
    simp only [statsFlag,Bool.false_eq_true,ite_false] at hf
    simp only [statsFlag,ite_true] at hg
    simp only [isSentence,namedForm,isForm,sentenceCode,Bool.and_eq_true]
    exact ⟨⟨⟨decide_eq_true ha.1,decide_eq_true ha.2⟩,decide_eq_true hf⟩,decide_eq_true hg⟩

theorem mixed_code_injective {n : ℕ} : Function.Injective
    (fun a : L.BoundedFormula (ℕ ⊕ ℕ) n => mixedCode S a) := by
  apply formulaCode_injective_general S _ mixedName_injective
  intro a; cases a <;> simp [freeName,auxName,node_tag]


theorem named_code_injective {n : ℕ} : Function.Injective
    (fun a : L.BoundedFormula ℕ n => namedCode S a) := by
  exact formulaCode_injective_general S auxName auxName_injective (fun _ => Or.inr (node_tag _ _))



end Lemmatheca.ProofTheory.CodingFormalProofs
