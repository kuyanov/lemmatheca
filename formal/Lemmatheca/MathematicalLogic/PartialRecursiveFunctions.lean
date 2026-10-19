import Mathlib.Computability.Partrec
import Lemmatheca.MathematicalLogic.PrimitiveRecursion

/-! Finite-arity partial recursion, with the recursion/search variable last.
The inductive class below uses exactly the human closure rules; `Part` supplies
partial values, not a distinguished natural-number value for divergence. -/

namespace Lemmatheca.MathematicalLogic.PartialRecursiveFunctions

abbrev Args (n : ℕ) := List.Vector ℕ n
abbrev PFunction (n : ℕ) := Args n → Part ℕ

def graph {n : ℕ} (f : PFunction n) : Set (Args n × ℕ) :=
  {p | p.2 ∈ f p.1}

def domain {n : ℕ} (f : PFunction n) : Set (Args n) :=
  {x | (f x).Dom}

def IsTotal {n : ℕ} (f : PFunction n) : Prop := ∀ x, (f x).Dom

def lift {n : ℕ} (f : Args n → ℕ) : PFunction n := fun x => Part.some (f x)

def snoc {n : ℕ} (x : Args n) (a : ℕ) : Args (n + 1) :=
  List.Vector.ofFn (Fin.snoc x.get a)

def init {n : ℕ} (x : Args (n + 1)) : Args n :=
  List.Vector.ofFn (fun i => x.get i.castSucc)

def last {n : ℕ} (x : Args (n + 1)) : ℕ := x.get (Fin.last n)

/-- Collect every coordinate; the empty collection is always defined. -/
def collect {m : ℕ} (p : Fin m → Part ℕ) : Part (Args m) :=
  ⟨∀ i, (p i).Dom, fun h => List.Vector.ofFn (fun i => (p i).get (h i))⟩

def strictComp {m n : ℕ} (h : PFunction m) (g : Fin m → PFunction n) : PFunction n :=
  fun x => (collect (fun i => g i x)).bind h

def recValue {k : ℕ} (g : PFunction k) (h : PFunction (k + 2))
    (x : Args k) : ℕ → Part ℕ
  | 0 => g x
  | n + 1 => (recValue g h x n).bind (fun a => h (snoc (snoc x n) a))

def partialRec {k : ℕ} (g : PFunction k) (h : PFunction (k + 2)) : PFunction (k + 1) :=
  fun x => recValue g h (init x) (last x)

def minimize {k : ℕ} (f : PFunction (k + 1)) : PFunction k :=
  fun x => Nat.rfind (fun n => (fun a => decide (a = 0)) <$> f (snoc x n))

/-- Exactly the finite-arity initial functions and three human closure rules. -/
inductive Recursive : {n : ℕ} → PFunction n → Prop
  | zero (n : ℕ) : Recursive (fun _ : Args n => Part.some 0)
  | succ : Recursive (fun x : Args 1 => Part.some (x.get 0 + 1))
  | proj {n : ℕ} (i : Fin n) : Recursive (fun x : Args n => Part.some (x.get i))
  | comp {m n : ℕ} {h : PFunction m} {g : Fin m → PFunction n} :
      Recursive h → (∀ i, Recursive (g i)) → Recursive (strictComp h g)
  | prec {k : ℕ} {g : PFunction k} {h : PFunction (k + 2)} :
      Recursive g → Recursive h → Recursive (partialRec g h)
  | search {k : ℕ} {f : PFunction (k + 1)} : Recursive f → Recursive (minimize f)

def TotalRecursive {n : ℕ} (f : PFunction n) : Prop := Recursive f ∧ IsTotal f

theorem graph_representation {n : ℕ} (G : Set (Args n × ℕ))
    (hG : ∀ x a b, (x, a) ∈ G → (x, b) ∈ G → a = b) :
    ∃ f : PFunction n, graph f = G := by
  classical
  refine ⟨fun x => ⟨∃ a, (x, a) ∈ G, fun h => Classical.choose h⟩, ?_⟩
  ext ⟨x, a⟩
  change (∃ h : ∃ b, (x, b) ∈ G, Classical.choose h = a) ↔ (x, a) ∈ G
  constructor
  · rintro ⟨h, he⟩
    rw [← he]
    exact Classical.choose_spec h
  · intro ha
    exact ⟨⟨a, ha⟩, hG x _ _ (Classical.choose_spec (show ∃ b, (x, b) ∈ G from ⟨a, ha⟩)) ha⟩

theorem graph_functional {n : ℕ} (f : PFunction n) {x : Args n} {a b : ℕ}
    (ha : (x, a) ∈ graph f) (hb : (x, b) ∈ graph f) : a = b := by
  exact Part.mem_unique ha hb

theorem domain_iff {n : ℕ} (f : PFunction n) (x : Args n) :
    x ∈ domain f ↔ ∃ a, (x, a) ∈ graph f := by
  exact Part.dom_iff_mem

theorem total_iff {n : ℕ} (f : PFunction n) :
    IsTotal f ↔ ∀ x, ∃ a, a ∈ f x := by
  simp only [IsTotal, Part.dom_iff_mem]

theorem collect_spec {m : ℕ} (p : Fin m → Part ℕ) (a : Args m) :
    a ∈ collect p ↔ ∀ i, a.get i ∈ p i := by
  constructor
  · rintro ⟨h, ha⟩ i
    change List.Vector.ofFn (fun i => (p i).get (h i)) = a at ha
    rw [← ha]
    simp only [List.Vector.get_ofFn]
    exact Part.get_mem (h i)
  · intro h
    refine ⟨fun i => (h i).1, ?_⟩
    change List.Vector.ofFn (fun i => (p i).get ((h i).1)) = a
    apply List.Vector.ext
    intro i
    simp only [List.Vector.get_ofFn]
    exact (h i).2

theorem strictComp_spec {m n : ℕ} (h : PFunction m) (g : Fin m → PFunction n)
    (x : Args n) (b : ℕ) :
    b ∈ strictComp h g x ↔ ∃ a : Args m, (∀ i, a.get i ∈ g i x) ∧ b ∈ h a := by
  simp only [strictComp, Part.mem_bind_iff, collect_spec]

theorem strictComp_zero {n : ℕ} (h : PFunction 0) (g : Fin 0 → PFunction n)
    (x : Args n) : strictComp h g x = h List.Vector.nil := by
  apply Part.ext
  intro b
  simp only [strictComp_spec]
  constructor
  · rintro ⟨a, _, ha⟩
    have : a = List.Vector.nil := Subsingleton.elim _ _
    simpa [this] using ha
  · intro hb
    exact ⟨List.Vector.nil, (fun i => i.elim0), hb⟩

theorem strictComp_total {m n : ℕ} (h : Args m → ℕ) (g : Fin m → Args n → ℕ) :
    strictComp (lift h) (fun i => lift (g i)) = lift (fun x => h (List.Vector.ofFn (fun i => g i x))) := by
  funext x
  apply Part.ext
  intro b
  simp only [strictComp_spec, lift, Part.mem_some_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    have : a = List.Vector.ofFn (fun i => g i x) := by
      apply List.Vector.ext
      intro i
      simpa using ha i
    simpa [this] using hb
  · intro hb
    exact ⟨List.Vector.ofFn (fun i => g i x), by simp, hb⟩

theorem constant_strict_domain (f : ℕ → Part ℕ) (x : ℕ) :
    ((f x).bind (fun _ => Part.some 0)).Dom ↔ (f x).Dom := by
  constructor
  · exact Part.Dom.of_bind
  · intro hf
    exact Part.bind_defined hf trivial

@[simp] theorem get_snoc_castSucc {n : ℕ} (x : Args n) (a : ℕ) (i : Fin n) :
    (snoc x a).get i.castSucc = x.get i := by simp [snoc]

@[simp] theorem get_snoc_last {n : ℕ} (x : Args n) (a : ℕ) :
    (snoc x a).get (Fin.last n) = a := by simp [snoc]

@[simp] theorem init_snoc {n : ℕ} (x : Args n) (a : ℕ) : init (snoc x a) = x := by
  apply List.Vector.ext
  intro i
  simp [init]

@[simp] theorem last_snoc {n : ℕ} (x : Args n) (a : ℕ) : last (snoc x a) = a := by
  simp [last]

@[simp] theorem snoc_init_last {n : ℕ} (x : Args (n + 1)) : snoc (init x) (last x) = x := by
  apply List.Vector.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [last]
  · simp [init]

@[simp] theorem partialRec_snoc {k : ℕ} (g : PFunction k) (h : PFunction (k + 2))
    (x : Args k) (n : ℕ) : partialRec g h (snoc x n) = recValue g h x n := by
  simp [partialRec]

private theorem recValue_domain_initial {k : ℕ} (g : PFunction k)
    (h : PFunction (k + 2)) (x : Args k) {i n : ℕ} (hin : i ≤ n)
    (hd : (recValue g h x n).Dom) : (recValue g h x i).Dom := by
  induction n with
  | zero => simpa [Nat.eq_zero_of_le_zero hin] using hd
  | succ n ih =>
    rcases hin.eq_or_lt with rfl | hi
    · exact hd
    · exact ih (Nat.le_of_lt_succ hi) (Part.Dom.of_bind hd)

theorem recursion_equations {k : ℕ} (g : PFunction k) (h : PFunction (k + 2))
    (x : Args k) (n : ℕ) :
    partialRec g h (snoc x 0) = g x ∧
    partialRec g h (snoc x (n + 1)) =
      (partialRec g h (snoc x n)).bind (fun a => h (snoc (snoc x n) a)) := by
  simp [recValue]

theorem recursion_chain_iff {k : ℕ} (g : PFunction k) (h : PFunction (k + 2))
    (x : Args k) (n b : ℕ) :
    b ∈ partialRec g h (snoc x n) ↔
      ∃ a : Fin (n + 1) → ℕ, a 0 ∈ g x ∧ a (Fin.last n) = b ∧
        ∀ i : Fin n, a i.succ ∈ h (snoc (snoc x i.val) (a i.castSucc)) := by
  rw [partialRec_snoc]
  constructor
  · intro hb
    have hd (i : Fin (n + 1)) : (recValue g h x i.val).Dom :=
      recValue_domain_initial g h x (Nat.le_of_lt_succ i.isLt) hb.1
    let a : Fin (n + 1) → ℕ := fun i => (recValue g h x i.val).get (hd i)
    refine ⟨a, Part.get_mem (hd 0), ?_, ?_⟩
    · exact Part.mem_unique (Part.get_mem (hd (Fin.last n))) hb
    · intro i
      have hi := Part.get_mem (hd i.succ)
      change a i.succ ∈ (recValue g h x i.val).bind _ at hi
      obtain ⟨c, hc, hstep⟩ := Part.mem_bind_iff.mp hi
      have he : c = a i.castSucc := Part.mem_unique hc (Part.get_mem (hd i.castSucc))
      simpa only [he] using hstep
  · rintro ⟨a, ha, hab, hs⟩
    have hv (j : ℕ) (hj : j ≤ n) : a ⟨j, Nat.lt_succ_of_le hj⟩ ∈ recValue g h x j := by
      induction j with
      | zero => exact ha
      | succ j ih =>
        have hjn : j < n := by omega
        exact Part.mem_bind (ih (by omega)) (hs ⟨j, hjn⟩)
    have hn := hv n (Nat.le_refl n)
    change a (Fin.last n) ∈ recValue g h x n at hn
    rwa [hab] at hn

theorem recursion_unique {k : ℕ} (g : PFunction k) (h : PFunction (k + 2))
    (r : PFunction (k + 1))
    (hz : ∀ x, r (snoc x 0) = g x)
    (hs : ∀ x n, r (snoc x (n + 1)) =
      (r (snoc x n)).bind (fun a => h (snoc (snoc x n) a))) : r = partialRec g h := by
  have he : ∀ x n, r (snoc x n) = recValue g h x n := by
    intro x n
    induction n with
    | zero => exact hz x
    | succ n ih => rw [hs, ih]; rfl
  funext v
  rw [← snoc_init_last v]
  exact (he _ _).trans (partialRec_snoc g h _ _).symm

theorem recursion_domain_initial {k : ℕ} (g : PFunction k) (h : PFunction (k + 2))
    (x : Args k) {i n : ℕ} (hin : i ≤ n)
    (hd : (partialRec g h (snoc x n)).Dom) :
    (partialRec g h (snoc x i)).Dom := by
  simp only [partialRec_snoc] at hd ⊢
  exact recValue_domain_initial g h x hin hd

theorem recursion_total {k : ℕ} (g : PFunction k) (h : PFunction (k + 2))
    (hg : IsTotal g) (hh : IsTotal h) : IsTotal (partialRec g h) := by
  intro v
  unfold partialRec
  induction last v with
  | zero => exact hg _
  | succ n ih => exact Part.bind_defined ih (hh _)

theorem minimize_spec {k : ℕ} (f : PFunction (k + 1)) (x : Args k) (n : ℕ) :
    n ∈ minimize f x ↔ 0 ∈ f (snoc x n) ∧
      ∀ i < n, ∃ a, 0 < a ∧ a ∈ f (snoc x i) := by
  change n ∈ Nat.rfind _ ↔ _
  erw [Nat.mem_rfind]
  change (true ∈ Part.map (fun a => decide (a = 0)) (f (snoc x n)) ∧
    ∀ {i}, i < n → false ∈ Part.map (fun a => decide (a = 0)) (f (snoc x i))) ↔ _
  simp only [Part.mem_map_iff]
  constructor
  · rintro ⟨⟨a, ha, haz⟩, hi⟩
    have az : a = 0 := by simpa using haz
    refine ⟨az ▸ ha, ?_⟩
    intro i hin
    obtain ⟨a, ha, han⟩ := hi hin
    exact ⟨a, Nat.pos_of_ne_zero (by simpa using han), ha⟩
  · rintro ⟨hn, hi⟩
    refine ⟨⟨0, hn, by simp⟩, ?_⟩
    intro i hin
    obtain ⟨a, ha, hap⟩ := hi i hin
    exact ⟨a, hap, by simp [Nat.ne_of_gt ha]⟩

theorem Recursive.of_eq {n : ℕ} {f g : PFunction n} (hf : Recursive f)
    (h : ∀ x, f x = g x) : Recursive g := (funext h) ▸ hf

private theorem recursive_precomp {m n : ℕ} {f : PFunction m}
    (hf : Recursive f) (g : Fin m → Args n → ℕ)
    (hg : ∀ i, Recursive (lift (g i))) :
    Recursive (fun x => f (List.Vector.ofFn (fun i => g i x))) := by
  apply Recursive.of_eq (Recursive.comp hf hg)
  intro x
  apply Part.ext
  intro b
  simp only [strictComp_spec, lift, Part.mem_some_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    have he : a = List.Vector.ofFn (fun i => g i x) := by
      apply List.Vector.ext
      intro i
      simpa using ha i
    simpa only [he] using hb
  · intro hb
    exact ⟨List.Vector.ofFn (fun i => g i x), by simp, hb⟩

private def rotateStep (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases (Fin.last n).castSucc
    (Fin.cases (Fin.last (n + 1)) (fun i => i.castSucc.castSucc))

private theorem rotateStep_snoc {n : ℕ} (x : Args n) (i a : ℕ) :
    List.Vector.ofFn (fun j => (snoc (snoc x i) a).get (rotateStep n j)) =
      List.Vector.cons i (List.Vector.cons a x) := by
  apply List.Vector.ext
  intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) j
  · change (snoc (snoc x i) a).get (Fin.last n).castSucc = i
    simp
  · change (snoc (snoc x i) a).get (Fin.last (n + 1)) = a
    simp
  · simp [rotateStep]

private theorem recursive_first_rec {n : ℕ} {f : Args n → ℕ} {g : Args (n + 2) → ℕ}
    (hf : Recursive (lift f)) (hg : Recursive (lift g)) :
    Recursive (lift (fun v : Args (n + 1) =>
      v.head.rec (f v.tail) (fun i a => g (List.Vector.cons i (List.Vector.cons a v.tail))))) := by
  let ordered : Args (n + 2) → ℕ :=
    fun v => g (List.Vector.ofFn (fun j => v.get (rotateStep n j)))
  have ho : Recursive (lift ordered) := by
    exact recursive_precomp hg (fun j v => v.get (rotateStep n j)) (fun j => Recursive.proj _)
  have hr := Recursive.prec hf ho
  have hi (j : Fin (n + 1)) :
      Recursive (lift (fun v : Args (n + 1) => (snoc v.tail v.head).get j)) := by
    refine Fin.lastCases ?_ (fun l => ?_) j
    · exact (Recursive.proj (0 : Fin (n + 1))).of_eq (fun v => by simp [lift])
    · exact (Recursive.proj l.succ).of_eq (fun v => by simp [lift])
  have hp : Recursive (fun v : Args (n + 1) =>
      partialRec (lift f) (lift ordered) (snoc v.tail v.head)) := by
    simpa only [List.Vector.ofFn_get] using
      recursive_precomp hr (fun j v => (snoc v.tail v.head).get j) hi
  apply hp.of_eq
  intro v
  rw [partialRec_snoc]
  change recValue (lift f) (lift ordered) v.tail v.head =
    Part.some (v.head.rec (f v.tail) (fun i a => g (List.Vector.cons i (List.Vector.cons a v.tail))))
  induction v.head with
  | zero => rfl
  | succ j ih =>
    simp only [recValue, ih, Part.bind_some, lift, ordered, rotateStep_snoc]

theorem primitive_recursive_inclusion {n : ℕ} {f : Args n → ℕ}
    (hf : Nat.Primrec' f) : TotalRecursive (lift f) := by
  refine ⟨?_, fun _ => trivial⟩
  induction hf with
  | zero => exact Recursive.zero 0
  | succ =>
    exact Recursive.succ.of_eq (fun v => by simp [lift])
  | get i => exact Recursive.proj i
  | comp g _ _ ihf ihg =>
    simpa only [strictComp_total] using Recursive.comp ihf ihg
  | prec _ _ ihf ihg => exact recursive_first_rec ihf ihg

noncomputable def characteristic {n : ℕ} (P : Args n → Prop) : Args n → ℕ :=
  by
    classical
    exact fun x => if P x then 1 else 0

noncomputable def predicateSearch {k : ℕ} (P : Args (k + 1) → Prop) : PFunction k :=
  minimize (lift (fun x => 1 - characteristic P x))

theorem predicateSearch_spec {k : ℕ} (P : Args (k + 1) → Prop) (x : Args k) (n : ℕ) :
    n ∈ predicateSearch P x ↔ P (snoc x n) ∧ ∀ i < n, ¬ P (snoc x i) := by
  classical
  rw [predicateSearch, minimize_spec]
  simp only [lift, Part.mem_some_iff, characteristic]
  constructor
  · rintro ⟨hn, hi⟩
    refine ⟨by by_contra hp; simp [hp] at hn, ?_⟩
    intro i hin hp
    obtain ⟨a, ha, he⟩ := hi i hin
    simp [hp] at he
    omega
  · rintro ⟨hn, hi⟩
    exact ⟨by simp [hn], fun i hin => ⟨1, by omega, by simp [hi i hin]⟩⟩

theorem predicateSearch_domain {k : ℕ} (P : Args (k + 1) → Prop) (x : Args k) :
    (predicateSearch P x).Dom ↔ ∃ n, P (snoc x n) := by
  classical
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (predicateSearch_spec P x n).mp hn |>.1⟩
  · intro h
    refine ⟨Nat.find h, (predicateSearch_spec P x _).mpr ?_⟩
    exact ⟨Nat.find_spec h, fun i hi => Nat.find_min h hi⟩

theorem recursive_predicateSearch {k : ℕ} {P : Args (k + 1) → Prop}
    (hP : TotalRecursive (lift (characteristic P))) : Recursive (predicateSearch P) := by
  have hsub : Nat.Primrec' (fun v : Args 1 => 1 - v.get 0) :=
    Nat.Primrec'.sub.comp₂ _ (Nat.Primrec'.const 1) (Nat.Primrec'.get 0)
  have hz := (primitive_recursive_inclusion hsub).1
  have ht : Recursive (lift (fun x => 1 - characteristic P x)) := by
    apply (recursive_precomp hz (fun _ x => characteristic P x) (fun _ => hP.1)).of_eq
    intro x
    simp [lift]
  exact Recursive.search ht

theorem predicateSearch_recursive {k : ℕ} {P : Args (k + 1) → Prop}
    (hP : Nat.Primrec' (characteristic P)) : Recursive (predicateSearch P) := by
  exact recursive_predicateSearch (primitive_recursive_inclusion hP)

theorem witnessed_search_total {k : ℕ} {P : Args (k + 1) → Prop}
    (hP : TotalRecursive (lift (characteristic P)))
    (hex : ∀ x, ∃ n, P (snoc x n)) : TotalRecursive (predicateSearch P) := by
  exact ⟨recursive_predicateSearch hP, fun x => (predicateSearch_domain P x).mpr (hex x)⟩

theorem blocked_zero_search {k : ℕ} (f : PFunction (k + 1)) (x : Args k)
    (h0 : ¬ (f (snoc x 0)).Dom) : minimize f x = Part.none := by
  apply Part.eq_none_iff.mpr
  intro n hn
  obtain ⟨hn, hi⟩ := (minimize_spec f x n).mp hn
  cases n with
  | zero => exact h0 hn.1
  | succ n =>
    obtain ⟨a, _, ha⟩ := hi 0 (Nat.zero_lt_succ n)
    exact h0 ha.1

noncomputable def boundedPredicateSearch {k : ℕ} (P : Args (k + 1) → Prop)
    (x : Args k) (b : ℕ) : ℕ :=
  PrimitiveRecursion.boundedSearch (fun x i => P (snoc x i)) x b

theorem bounded_unbounded_agreement {k : ℕ} (P : Args (k + 1) → Prop)
    (x : Args k) (b : ℕ) (hex : ∃ i < b, P (snoc x i)) :
    boundedPredicateSearch P x b ∈ predicateSearch P x ∧ boundedPredicateSearch P x b < b := by
  have hs := PrimitiveRecursion.boundedSearch_spec (fun x i => P (snoc x i)) x b
  have hlt : boundedPredicateSearch P x b < b := by
    apply lt_of_le_of_ne hs.1
    intro heq
    obtain ⟨i, hi, hPi⟩ := hex
    exact hs.2.2.mp heq i hi hPi
  exact ⟨(predicateSearch_spec P x _).mpr (hs.2.1 hlt), hlt⟩

theorem bounded_failure {k : ℕ} (P : Args (k + 1) → Prop)
    (x : Args k) (b : ℕ) (hn : ∀ i < b, ¬ P (snoc x i)) :
    boundedPredicateSearch P x b = b := by
  exact (PrimitiveRecursion.boundedSearch_spec (fun x i => P (snoc x i)) x b).2.2.mpr hn

theorem boundedPredicateSearch_primitive {k : ℕ} {P : Args (k + 1) → Prop}
    (hP : Nat.Primrec' (characteristic P)) {b : Args k → ℕ} (hb : Nat.Primrec' b) :
    Nat.Primrec' (fun x => boundedPredicateSearch P x (b x)) := by
  classical
  have hp : PrimrecPred P :=
    (Primrec.eq.comp hP.to_prim (Primrec.const 1)).of_eq (fun v => by simp [characteristic])
  have hs : Primrec₂ (@snoc k) := by
    change Primrec (fun p : Args k × ℕ => List.Vector.ofFn (Fin.snoc p.1.get p.2))
    apply Primrec.vector_ofFn
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (@Primrec.snd (Args k) ℕ _ _)
    · simpa only [Fin.snoc_castSucc] using
        (Primrec.vector_get.comp Primrec.fst (Primrec.const j))
  have hr : PrimrecRel (fun x i => P (snoc x i)) := hp.comp hs
  exact Nat.Primrec'.prim_iff.mpr
    ((PrimitiveRecursion.boundedSearch_primrec hr).comp Primrec.id hb.to_prim)

end Lemmatheca.MathematicalLogic.PartialRecursiveFunctions
