import Lemmatheca.LogicalCompactness.Compactness
import Mathlib.Order.WellFounded
import Mathlib.Tactic

open Lemmatheca.MathematicalLogic

/-! Compactness obstructions in the actual first-order language with one binary
relation. Walks have external natural-number lengths and their formulas use the
shared `FirstOrder.Language.Formula` syntax. -/
namespace Lemmatheca.ModelTheory.ExpressiveLimits
open FirstOrder FirstOrder.Language
universe u
noncomputable section

inductive BinaryRelation : ℕ → Type
  | edge : BinaryRelation 2

def language : Language := ⟨fun _ => Empty, BinaryRelation⟩

abbrev edgeSymbol : language.Relations 2 := BinaryRelation.edge

@[instance_reducible] def relationStructure {M : Type u} (r : M → M → Prop) :
    language.Structure M where
  funMap f := nomatch f
  RelMap | .edge => fun x => r (x 0) (x 1)

def edge {M : Type u} [language.Structure M] (a b : M) : Prop :=
  Structure.RelMap edgeSymbol ![a,b]

def atom {α : Type} (a b : language.Term α) : language.Formula α :=
  edgeSymbol.formula₂ a b

def Walk {M : Type u} (r : M → M → Prop) : ℕ → M → M → Prop
  | 0, a, b => a = b
  | n+1, a, b => ∃ c, r a c ∧ Walk r n c b

def Reachable {M : Type u} (r : M → M → Prop) (a b : M) : Prop :=
  ∃ n : ℕ, Walk r n a b

def ConnectedRelation {M : Type u} (r : M → M → Prop) : Prop :=
  Std.Symm r ∧ Std.Irrefl r ∧ ∀ a b, Reachable r a b

def WellOrdered {M : Type u} (r : M → M → Prop) : Prop :=
  IsStrictTotalOrder M r ∧ WellFounded r

theorem wellOrdered_iff_least {M : Type u} {r : M → M → Prop} :
    WellOrdered r ↔ IsStrictTotalOrder M r ∧
      ∀ s : Set M, s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, a = b ∨ r a b := by
  constructor
  · rintro ⟨ht,hw⟩
    let := ht
    refine ⟨ht, fun s hs => ?_⟩
    obtain ⟨a,ha,hmin⟩ := hw.has_min s hs
    refine ⟨a,ha,fun b hb => ?_⟩
    rcases trichotomous_of r a b with h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · exact False.elim (hmin b hb h)
  · rintro ⟨ht,h⟩
    let := ht
    refine ⟨ht, WellFounded.wellFounded_iff_has_min.mpr (fun s hs => ?_)⟩
    obtain ⟨a,ha,hm⟩ := h s hs
    refine ⟨a,ha,fun b hb hab => ?_⟩
    rcases hm b hb with he | he
    · subst b; exact irrefl a hab
    · exact asymm_of r he hab

def pathFormula : ℕ → language.Formula (Fin 2)
  | 0 => (Term.var 0).equal (Term.var 1)
  | n+1 => ((atom (.var (.inl 0)) (.var (.inr ()))) ⊓
      ((pathFormula n).relabel (fun i => if i = 0 then .inr () else .inl 1))).iExs Unit

theorem pathFormula_realize {M : Type u} [language.Structure M]
    (n : ℕ) (a b : M) :
    (pathFormula n).Realize ![a,b] ↔ Walk edge n a b := by
  induction n generalizing a b with
  | zero => simp [pathFormula, Walk]
  | succ n ih =>
    simp only [pathFormula, Formula.realize_iExs, Formula.realize_inf,
      atom, Formula.realize_rel₂, Term.realize_var, Formula.realize_relabel]
    have hx (w : Unit → M) :
        (Sum.elim ![a,b] w) ∘ (fun i : Fin 2 => if i = 0 then .inr () else .inl 1) =
          ![w (), b] := by funext i; fin_cases i <;> rfl
    simp only [hx, ih, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero]
    change (∃ w : Unit → M, edge a (w ()) ∧ Walk edge n (w ()) b) ↔ _
    constructor
    · rintro ⟨w, hw⟩; exact ⟨w (), hw⟩
    · rintro ⟨w, hw⟩; exact ⟨fun _ => w, hw⟩

theorem wellOrdered_no_descent {M : Type u} {r : M → M → Prop}
    (h : WellOrdered r) (a : ℕ → M) : ¬ ∀ i, r (a (i+1)) (a i) := by
  intro ha
  have hn (x : M) (hx : Acc r x) : ∀ i, a i ≠ x := by
    induction hx with
    | intro x hx ih =>
      intro i he
      exact ih (a (i+1)) (he ▸ ha i) (i+1) rfl
  exact hn (a 0) (h.2.apply _) 0 rfl

theorem natural_wellOrdered : WellOrdered (fun a b : ℕ => a < b) := by
  exact ⟨inferInstance, Nat.lt_wfRel.wf⟩

theorem finite_descent (N i : ℕ) (hi : i ≤ N) :
    N+1-(i+1) < N+1-i := by omega

theorem directed_walk (n a b : ℕ) :
    Walk (fun i j : ℕ => j = i+1) n a b ↔ b = a+n := by
  induction n generalizing a b with
  | zero => simp [Walk, eq_comm]
  | succ n ih => simp [Walk, ih, Nat.add_comm, Nat.add_left_comm]

def chainEdge {N : ℕ} (a b : Fin (N+2)) : Prop :=
  a.val+1 = b.val ∨ b.val+1 = a.val

private theorem walk_along {M : Type u} {r : M → M → Prop}
    (f : ℕ → M) (n : ℕ) (h : ∀ i < n, r (f i) (f (i+1))) :
    Walk r n (f 0) (f n) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    exact ⟨f 1, h 0 (by omega), ih (fun i => f (i+1)) (fun i hi => h (i+1) (by omega))⟩

theorem walk_iff_tuple {M : Type u} {r : M → M → Prop} (n : ℕ) (a b : M) :
    Walk r n a b ↔ ∃ f : Fin (n+1) → M,
      f 0 = a ∧ f (Fin.last n) = b ∧ ∀ i : Fin n, r (f i.castSucc) (f i.succ) := by
  constructor
  · intro h
    induction n generalizing a with
    | zero => exact ⟨fun _ => a, rfl, h, fun i => i.elim0⟩
    | succ n ih =>
      obtain ⟨c,hac,hcb⟩ := h
      obtain ⟨g,hg0,hgn,hg⟩ := ih c hcb
      refine ⟨Fin.cons a g, by simp, ?_, ?_⟩
      · simpa only [Fin.cons_last] using hgn
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hg0] using hac
        · have he : j.succ.castSucc = j.castSucc.succ := by apply Fin.ext; rfl
          simpa only [he, Fin.cons_succ] using hg j
  · rintro ⟨f,ha,hb,hf⟩
    let g : ℕ → M := fun i => f ⟨min i n, by have := Nat.min_le_right i n; omega⟩
    have hg := walk_along g n (by
      intro i hi
      convert hf (⟨i,hi⟩ : Fin n) using 1
      · change f _ = f _
        congr 1
        apply Fin.ext
        simp only [Fin.val_castSucc]
        omega
      · change f _ = f _
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega)
    have h0 : g 0 = a := by
      change f _ = a
      convert ha using 1
      congr 1
    have hn : g n = b := by
      change f _ = b
      convert hb using 1
      congr 1
      apply Fin.ext
      simp
    simpa only [h0,hn] using hg

theorem finite_chain_connected (N : ℕ) :
    ConnectedRelation (chainEdge (N := N)) := by
  refine ⟨⟨fun _ _ h => h.elim Or.inr Or.inl⟩, ⟨?_⟩, ?_⟩
  · intro a h
    rcases h with h | h <;> omega
  · intro a b
    by_cases hab : a.val ≤ b.val
    · let f : ℕ → Fin (N+2) := fun i =>
        ⟨a.val + min i (b.val-a.val), by
          have := Nat.min_le_right i (b.val-a.val)
          have := b.isLt
          omega⟩
      refine ⟨b.val-a.val, ?_⟩
      have hw := walk_along (r := chainEdge) f (b.val-a.val) (by
        intro i hi
        apply Or.inl
        change a.val + min i (b.val-a.val) + 1 = a.val + min (i+1) (b.val-a.val)
        rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
        omega)
      have h0 : f 0 = a := by apply Fin.ext; simp [f]
      have hn : f (b.val-a.val) = b := by apply Fin.ext; simp only [f, min_self]; omega
      simpa only [h0, hn] using hw
    · have hba : b.val ≤ a.val := by omega
      let f : ℕ → Fin (N+2) := fun i =>
        ⟨a.val - min i (a.val-b.val), lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩
      refine ⟨a.val-b.val, ?_⟩
      have hw := walk_along (r := chainEdge) f (a.val-b.val) (by
        intro i hi
        apply Or.inr
        change a.val - min (i+1) (a.val-b.val) + 1 = a.val - min i (a.val-b.val)
        rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
        omega)
      have h0 : f 0 = a := by apply Fin.ext; simp [f]
      have hn : f (a.val-b.val) = b := by apply Fin.ext; simp only [f, min_self]; omega
      simpa only [h0, hn] using hw

theorem finite_chain_walk_bound {N n : ℕ} {a b : Fin (N+2)}
    (h : Walk chainEdge n a b) : b.val ≤ a.val+n := by
  induction n generalizing a with
  | zero => subst b; omega
  | succ n ih =>
    obtain ⟨c, hc, h⟩ := h
    have hb := ih h
    rcases hc with h | h <;> omega

theorem finite_chain_endpoints (N n : ℕ) (hn : n ≤ N) :
    ¬ Walk chainEdge n (0 : Fin (N+2)) ⟨N+1, by omega⟩ := by
  intro h
  have hb := finite_chain_walk_bound h
  simp only [Fin.val_zero] at hb
  omega

theorem transitive_reachability {M : Type u} {r : M → M → Prop}
    (hr : ∀ a b c, r a b → r b c → r a c) (a b : M) :
    Reachable r a b ↔ a = b ∨ r a b := by
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing a with
    | zero => exact Or.inl hn
    | succ n ih =>
      obtain ⟨c, hac, hcb⟩ := hn
      rcases ih c hcb with h | h
      · exact Or.inr (h ▸ hac)
      · exact Or.inr (hr a c b hac h)
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, b, h, rfl⟩

/-- The actual constants and edge atom forcing one step of a descending chain. -/
def descentSentence (i : ℕ) : language[[ℕ]].Sentence :=
  ((language.lhomWithConstants ℕ).onRelation BinaryRelation.edge).formula₂
    (Constants.term (language.con (i+1))) (Constants.term (language.con i))

def descentTheory (T : language.Theory) : language[[ℕ]].Theory :=
  (language.lhomWithConstants ℕ).onTheory T ∪ Set.range descentSentence

private theorem finite_index_bound {L : Language} (Γ : Finset L.Sentence)
    (f : ℕ → L.Sentence) :
    ∃ N : ℕ, ∀ A ∈ Γ, A ∈ Set.range f → ∃ n ≤ N, f n = A := by
  classical
  let index (A : Γ) : ℕ := if h : (A : L.Sentence) ∈ Set.range f then
    Classical.choose h else 0
  refine ⟨Finset.univ.sup index, fun A hA h => ?_⟩
  have he : f (index ⟨A,hA⟩) = A := by
    simpa only [index, dite_eq_left h] using Classical.choose_spec h
  exact ⟨index ⟨A,hA⟩, Finset.le_sup (Finset.mem_univ _), he⟩

private theorem descentSentence_realize {M : Type u} [language.Structure M]
    [language[[ℕ]].Structure M] [(language.lhomWithConstants ℕ).IsExpansionOn M]
    (i : ℕ) : M ⊨ descentSentence i ↔
      edge (language.con (i+1) : M) (language.con i : M) := by
  simp only [descentSentence, Sentence.Realize, Formula.realize_rel₂,
    Term.realize_constants]
  exact Iff.of_eq ((language.lhomWithConstants ℕ).map_onRelation edgeSymbol
    (![(language.con (i+1) : M), (language.con i : M)] : Fin 2 → M))

/-- Every theory true in the ordinary natural-number order has an actual model
with an infinite descending sequence. The original theory is retained by reduct. -/
theorem descending_model (T : language.Theory)
    (hT : letI := relationStructure (fun a b : ℕ => a < b); ℕ ⊨ T) :
    ∃ M : Theory.ModelType.{0,0,0} T, ∃ a : ℕ → M, ∀ i, edge (a (i+1)) (a i) := by
  have hs : (descentTheory T).IsSatisfiable := by
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Γ hΓ
    obtain ⟨N,hN⟩ := finite_index_bound Γ descentSentence
    let : language.Structure ℕ := relationStructure (fun a b : ℕ => a < b)
    let : (constantsOn ℕ).Structure ℕ := constantsOn.structure (fun i => N+1-i)
    let : language[[ℕ]].Structure ℕ :=
      @Language.withConstantsStructure language ℕ inferInstance ℕ inferInstance
    let : ℕ ⊨ T := hT
    let : ℕ ⊨ (language.lhomWithConstants ℕ).onTheory T :=
      (LHom.onTheory_model (M := ℕ) _ T).mpr inferInstance
    let : ℕ ⊨ (↑Γ : language[[ℕ]].Theory) := by
      refine ⟨fun A hA => ?_⟩
      rcases hΓ hA with h | h
      · exact Theory.realize_sentence_of_mem ((language.lhomWithConstants ℕ).onTheory T) h
      · obtain ⟨i,hi,rfl⟩ := hN A hA h
        rw [descentSentence_realize]
        have hc (j : ℕ) : (language.con j : ℕ) = N+1-j := rfl
        rw [hc, hc]
        exact finite_descent N i hi
    exact Theory.Model.isSatisfiable ℕ
  obtain ⟨M⟩ := hs
  let : language.Structure M := (language.lhomWithConstants ℕ).reduct M
  let : M ⊨ (language.lhomWithConstants ℕ).onTheory T :=
    M.is_model.mono Set.subset_union_left
  let : M ⊨ T := (LHom.onTheory_model (M := M) (language.lhomWithConstants ℕ) T).mp inferInstance
  have ha (i : ℕ) : edge (language.con (i+1) : M) (language.con i : M) := by
    apply (descentSentence_realize i).mp
    exact Theory.realize_sentence_of_mem (descentTheory T) (Or.inr ⟨i,rfl⟩)
  exact ⟨Theory.ModelType.of T M, (fun i => (language.con i : M)), ha⟩

theorem wellOrders_not_axiomatizable :
    ¬ ∃ T : language.Theory, ∀ (M : Type) (_ : language.Structure M),
      Nonempty M → (M ⊨ T ↔ WellOrdered (edge (M := M))) := by
  rintro ⟨T,hT⟩
  have hn : letI := relationStructure (fun a b : ℕ => a < b); ℕ ⊨ T := by
    exact (hT ℕ (relationStructure (fun a b : ℕ => a < b)) inferInstance).mpr natural_wellOrdered
  obtain ⟨M,a,ha⟩ := descending_model T hn
  have hw := (hT M inferInstance inferInstance).mp M.is_model
  exact wellOrdered_no_descent hw a ha

/-- Naming the two free variables uses the existing shared syntax equivalence. -/
def namedPair (A : language.Formula (Fin 2)) : language[[Fin 2]].Sentence :=
  Formula.equivSentence A

def noPathSentence (n : ℕ) : language[[Fin 2]].Sentence :=
  (namedPair (pathFormula n)).not

private theorem namedPair_realize {M : Type u} [language.Structure M]
    [language[[Fin 2]].Structure M]
    [(language.lhomWithConstants (Fin 2)).IsExpansionOn M]
    (A : language.Formula (Fin 2)) :
    M ⊨ namedPair A ↔ A.Realize
      ![(language.con (0 : Fin 2) : M), (language.con (1 : Fin 2) : M)] := by
  rw [namedPair, Formula.realize_equivSentence]
  have he : (fun i : Fin 2 => (language.con i : M)) =
      ![(language.con (0 : Fin 2) : M), (language.con (1 : Fin 2) : M)] := by
    funext i
    fin_cases i <;> rfl
  rw [he]

def reachabilityTheory (ρ : language.Formula (Fin 2)) : language[[Fin 2]].Theory :=
  {namedPair ρ} ∪ Set.range noPathSentence

theorem reachability_not_definable :
    ¬ ∃ ρ : language.Formula (Fin 2),
      ∀ (M : Type) (_ : language.Structure M), Nonempty M → ∀ a b : M,
        (ρ.Realize ![a,b] ↔ Reachable edge a b) := by
  rintro ⟨ρ,hρ⟩
  have hs : (reachabilityTheory ρ).IsSatisfiable := by
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Γ hΓ
    obtain ⟨N,hN⟩ := finite_index_bound Γ noPathSentence
    let : language.Structure ℕ := relationStructure (fun i j : ℕ => j = i+1)
    let : (constantsOn (Fin 2)).Structure ℕ := constantsOn.structure ![0,N+1]
    let : language[[Fin 2]].Structure ℕ :=
      @Language.withConstantsStructure language ℕ inferInstance (Fin 2) inferInstance
    have hreach : Reachable (edge (M := ℕ)) 0 (N+1) :=
      ⟨N+1, (directed_walk (N+1) 0 (N+1)).mpr (by omega)⟩
    have hρ' : ρ.Realize ![0,N+1] := (hρ ℕ inferInstance inferInstance 0 (N+1)).mpr hreach
    let : ℕ ⊨ (↑Γ : language[[Fin 2]].Theory) := by
      refine ⟨fun A hA => ?_⟩
      rcases hΓ hA with h | h
      · obtain rfl := Set.mem_singleton_iff.mp h
        exact (namedPair_realize ρ).mpr hρ'
      · obtain ⟨i,hi,rfl⟩ := hN A hA h
        rw [noPathSentence, Sentence.realize_not, namedPair_realize, pathFormula_realize]
        change ¬ Walk (fun i j : ℕ => j = i+1) i 0 (N+1)
        rw [directed_walk]
        omega
    exact Theory.Model.isSatisfiable ℕ
  obtain ⟨M⟩ := hs
  let : language.Structure M := (language.lhomWithConstants (Fin 2)).reduct M
  have hm : M ⊨ namedPair ρ :=
    Theory.realize_sentence_of_mem (reachabilityTheory ρ) (Or.inl rfl)
  have hr := (hρ M inferInstance inferInstance
    (language.con (0 : Fin 2) : M) (language.con (1 : Fin 2) : M)).mp
      ((namedPair_realize ρ).mp hm)
  obtain ⟨n,hn⟩ := hr
  have hnot : M ⊨ noPathSentence n :=
    Theory.realize_sentence_of_mem (reachabilityTheory ρ) (Or.inr ⟨n,rfl⟩)
  rw [noPathSentence, Sentence.realize_not, namedPair_realize, pathFormula_realize] at hnot
  exact hnot hn

def disconnectedTheory (T : language.Theory) : language[[Fin 2]].Theory :=
  (language.lhomWithConstants (Fin 2)).onTheory T ∪ Set.range noPathSentence

theorem connectedRelations_not_axiomatizable :
    ¬ ∃ T : language.Theory, ∀ (M : Type) (_ : language.Structure M),
      Nonempty M → (M ⊨ T ↔ ConnectedRelation (edge (M := M))) := by
  rintro ⟨T,hT⟩
  have hs : (disconnectedTheory T).IsSatisfiable := by
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Γ hΓ
    obtain ⟨N,hN⟩ := finite_index_bound Γ noPathSentence
    let M := Fin (N+2)
    let : language.Structure M := relationStructure chainEdge
    let : (constantsOn (Fin 2)).Structure M :=
      constantsOn.structure ![0,⟨N+1, by omega⟩]
    let : language[[Fin 2]].Structure M :=
      @Language.withConstantsStructure language M inferInstance (Fin 2) inferInstance
    let : M ⊨ T := (hT M inferInstance inferInstance).mpr (finite_chain_connected N)
    let : M ⊨ (language.lhomWithConstants (Fin 2)).onTheory T :=
      (LHom.onTheory_model (M := M) _ T).mpr inferInstance
    let : M ⊨ (↑Γ : language[[Fin 2]].Theory) := by
      refine ⟨fun A hA => ?_⟩
      rcases hΓ hA with h | h
      · exact Theory.realize_sentence_of_mem
          ((language.lhomWithConstants (Fin 2)).onTheory T) h
      · obtain ⟨i,hi,rfl⟩ := hN A hA h
        rw [noPathSentence, Sentence.realize_not, namedPair_realize, pathFormula_realize]
        exact finite_chain_endpoints N i hi
    exact Theory.Model.isSatisfiable M
  obtain ⟨M⟩ := hs
  let : language.Structure M := (language.lhomWithConstants (Fin 2)).reduct M
  let : M ⊨ (language.lhomWithConstants (Fin 2)).onTheory T :=
    M.is_model.mono Set.subset_union_left
  let : M ⊨ T :=
    (LHom.onTheory_model (M := M) (language.lhomWithConstants (Fin 2)) T).mp inferInstance
  have hc := (hT M inferInstance inferInstance).mp inferInstance
  obtain ⟨n,hn⟩ := hc.2.2 (language.con (0 : Fin 2) : M) (language.con (1 : Fin 2) : M)
  have hnot : M ⊨ noPathSentence n :=
    Theory.realize_sentence_of_mem (disconnectedTheory T) (Or.inr ⟨n,rfl⟩)
  rw [noPathSentence, Sentence.realize_not, namedPair_realize, pathFormula_realize] at hnot
  exact hnot hn

end
end Lemmatheca.ModelTheory.ExpressiveLimits
