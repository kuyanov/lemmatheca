import Lemmatheca.OracleComputation.Program

/-! Oracle-independent finite successful derivations, with ordered query records. -/
namespace Lemmatheca.ComputabilityTheory.OracleComputation

open UniversalComputation

set_option backward.isDefEq.respectTransparency false

abbrev QueryRecord := List (ℕ × ℕ)

def ValidRecord (τ : QueryRecord) : Prop :=
  ∀ q b, (q, b) ∈ τ → b = 0 ∨ b = 1

def Consistent (A : Set ℕ) (τ : QueryRecord) : Prop :=
  ∀ q b, (q, b) ∈ τ → b = indicator (fun n => n ∈ A) q

inductive Derives : Code → ℕ → QueryRecord → ℕ → Prop
  | zero (x : ℕ) : Derives .zero x [] 0
  | succ (x : ℕ) : Derives .succ x [] (x + 1)
  | left (x : ℕ) : Derives .left x [] x.unpair.1
  | right (x : ℕ) : Derives .right x [] x.unpair.2
  | query (q b : ℕ) (hb : b = 0 ∨ b = 1) : Derives .query q [(q, b)] b
  | pair {c d : Code} {x u v : ℕ} {σ τ : QueryRecord} :
      Derives c x σ u → Derives d x τ v →
      Derives (.pair c d) x (σ ++ τ) (Nat.pair u v)
  | comp {c d : Code} {x v y : ℕ} {σ τ : QueryRecord} :
      Derives d x σ v → Derives c v τ y → Derives (.comp c d) x (σ ++ τ) y
  | prec_zero {c d : Code} {a y : ℕ} {τ : QueryRecord} :
      Derives c a τ y → Derives (.prec c d) (Nat.pair a 0) τ y
  | prec_succ {c d : Code} {a n v y : ℕ} {σ τ : QueryRecord} :
      Derives (.prec c d) (Nat.pair a n) σ v →
      Derives d (Nat.pair a (Nat.pair n v)) τ y →
      Derives (.prec c d) (Nat.pair a (n + 1)) (σ ++ τ) y
  | find_zero {c : Code} {a m : ℕ} {τ : QueryRecord} :
      Derives c (Nat.pair a m) τ 0 → Derives (.find' c) (Nat.pair a m) τ m
  | find_succ {c : Code} {a m v j : ℕ} {σ τ : QueryRecord} :
      Derives c (Nat.pair a m) σ v → 0 < v →
      Derives (.find' c) (Nat.pair a (m + 1)) τ j →
      Derives (.find' c) (Nat.pair a m) (σ ++ τ) j

private theorem consistent_append {A : Set ℕ} {σ τ : QueryRecord} :
    Consistent A (σ ++ τ) ↔ Consistent A σ ∧ Consistent A τ := by
  simp only [Consistent, List.mem_append]
  aesop

private theorem consistent_nil (A : Set ℕ) : Consistent A [] := by simp [Consistent]

theorem derives_valid {c : Code} {x y : ℕ} {τ : QueryRecord}
    (h : Derives c x τ y) : ValidRecord τ := by
  induction h <;> simp_all [ValidRecord, List.mem_append] <;> aesop

private theorem prec_zero_iff (c d : Code) (a y : ℕ) (τ : QueryRecord) :
    Derives (.prec c d) (Nat.pair a 0) τ y ↔ Derives c a τ y := by
  constructor
  · intro h
    generalize hx : Nat.pair a 0 = x at h
    cases h <;> simp only [Nat.pair_eq_pair] at hx
    · obtain ⟨rfl, _⟩ := hx
      assumption
    · omega
  · exact Derives.prec_zero

private theorem prec_succ_iff (c d : Code) (a n y : ℕ) (τ : QueryRecord) :
    Derives (.prec c d) (Nat.pair a (n + 1)) τ y ↔
      ∃ σ ρ v, Derives (.prec c d) (Nat.pair a n) σ v ∧
        Derives d (Nat.pair a (Nat.pair n v)) ρ y ∧ τ = σ ++ ρ := by
  constructor
  · intro h
    generalize hx : Nat.pair a (n + 1) = x at h
    cases h <;> simp only [Nat.pair_eq_pair] at hx
    · omega
    · obtain ⟨rfl, hn⟩ := hx
      cases Nat.succ.inj hn
      exact ⟨_, _, _, by assumption, by assumption, rfl⟩
  · rintro ⟨σ,ρ,v,hσ,hρ,rfl⟩
    exact .prec_succ hσ hρ

private theorem find_iff (c : Code) (a m j : ℕ) (τ : QueryRecord) :
    Derives (.find' c) (Nat.pair a m) τ j ↔
      (m = j ∧ Derives c (Nat.pair a m) τ 0) ∨
      ∃ σ ρ v, Derives c (Nat.pair a m) σ v ∧ 0 < v ∧
        Derives (.find' c) (Nat.pair a (m+1)) ρ j ∧ τ = σ ++ ρ := by
  constructor
  · intro h
    generalize hx : Nat.pair a m = x at h
    cases h <;> obtain ⟨rfl,rfl⟩ := Nat.pair_eq_pair.mp hx
    · exact Or.inl ⟨rfl,by assumption⟩
    · exact Or.inr ⟨_,_,_,by assumption,by assumption,by assumption,rfl⟩
  · rintro (⟨rfl,h⟩ | ⟨σ,ρ,v,hσ,hv,hρ,rfl⟩)
    · exact .find_zero h
    · exact .find_succ hσ hv hρ

private theorem find_lower {p : Code} {x y : ℕ} {τ : QueryRecord}
    (h : Derives p x τ y) : ∀ c, p = .find' c → x.unpair.2 ≤ y := by
  induction h <;> intro e he <;> cases he
  · simp
  · rename_i ih
    have ht := ih _ rfl
    simp only [Nat.unpair_pair] at ht ⊢
    omega

theorem derives_prec_chain (c d : Code) (a n y : ℕ) (τ : QueryRecord) :
    Derives (.prec c d) (Nat.pair a n) τ y ↔
      ∃ values : Fin (n + 1) → ℕ, ∃ records : Fin (n + 1) → QueryRecord,
        Derives c a (records 0) (values 0) ∧
        (∀ i : Fin n, Derives d (Nat.pair a (Nat.pair i.val (values i.castSucc)))
          (records i.succ) (values i.succ)) ∧
        τ = (List.ofFn records).flatten ∧ y = values (Fin.last n) := by
  induction n generalizing τ y with
  | zero =>
      rw [prec_zero_iff]
      constructor
      · intro h
        exact ⟨fun _ => y, fun _ => τ, h, by simp, by simp, rfl⟩
      · rintro ⟨values,records,h,_,hτ,hy⟩
        simpa [List.ofFn_succ, hy, hτ] using h
  | succ n ih =>
      rw [prec_succ_iff]
      constructor
      · rintro ⟨σ,ρ,v,hσ,hρ,rfl⟩
        obtain ⟨values,records,h0,hs,hσ,hv⟩ := (ih v σ).mp hσ
        refine ⟨Fin.snoc values y,Fin.snoc records ρ,?_,?_,?_,?_⟩
        · simpa using h0
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa [Fin.snoc_last, Fin.snoc_castSucc, ← hv] using hρ
          · simpa only [← Fin.castSucc_succ,Fin.snoc_castSucc,Fin.val_castSucc] using hs j
        · rw [List.ofFn_succ']
          simp [hσ]
        · simp
      · rintro ⟨values,records,h0,hs,hτ,hy⟩
        let vs : Fin (n+1) → ℕ := fun i => values i.castSucc
        let rs : Fin (n+1) → QueryRecord := fun i => records i.castSucc
        have hp : Derives (.prec c d) (Nat.pair a n) (List.ofFn rs).flatten
            (vs (Fin.last n)) := (ih _ _).mpr ⟨vs,rs,by simpa [vs,rs] using h0,
              fun i => by simpa [vs,rs,Fin.castSucc_succ] using hs i.castSucc,rfl,rfl⟩
        refine ⟨(List.ofFn rs).flatten, records (Fin.last (n+1)), vs (Fin.last n), hp, ?_, ?_⟩
        · simpa [vs,hy] using hs (Fin.last n)
        · rw [hτ, List.ofFn_succ']
          simp [rs]

theorem derives_find_chain (c : Code) (a m j : ℕ) (τ : QueryRecord) :
    Derives (.find' c) (Nat.pair a m) τ j ↔
      m ≤ j ∧ ∃ values : Fin (j - m + 1) → ℕ,
        ∃ records : Fin (j - m + 1) → QueryRecord,
          (∀ i : Fin (j - m + 1),
            Derives c (Nat.pair a (m + i.val)) (records i) (values i)) ∧
          (∀ i : Fin (j - m), 0 < values i.castSucc) ∧
          values (Fin.last (j - m)) = 0 ∧ τ = (List.ofFn records).flatten := by
  have go : ∀ k m j (τ : QueryRecord), j-m = k →
      (Derives (.find' c) (Nat.pair a m) τ j ↔
        m ≤ j ∧ ∃ values : Fin (k+1) → ℕ, ∃ records : Fin (k+1) → QueryRecord,
          (∀ i, Derives c (Nat.pair a (m+i.val)) (records i) (values i)) ∧
          (∀ i : Fin k, 0 < values i.castSucc) ∧
          values (Fin.last k) = 0 ∧ τ = (List.ofFn records).flatten) := by
    intro k
    induction k with
    | zero =>
        intro m j τ hk
        constructor
        · intro h
          have hmj : m ≤ j := by simpa using find_lower h c rfl
          have he : m = j := by omega
          subst j
          rcases (find_iff c a m m τ).mp h with ⟨_,ht⟩ | ⟨σ,ρ,v,_,_,ht,_⟩
          · refine ⟨le_rfl,fun _ => 0,fun _ => τ,?_,by simp,rfl,by simp⟩
            intro i
            have hi : i = 0 := Fin.eq_zero i
            subst i
            simpa using ht
          · have := find_lower ht c rfl
            simp only [Nat.unpair_pair] at this
            omega
        · rintro ⟨hmj,values,records,ht,_,hz,hτ⟩
          have he : m = j := by omega
          subst j
          have hp := ht 0
          have hy : values 0 = 0 := by simpa using hz
          have hr : τ = records 0 := by simpa using hτ
          rw [hr]
          exact .find_zero (by simpa [hy] using hp)
    | succ k ih =>
        intro m j τ hk
        constructor
        · intro h
          have hmj : m ≤ j := by simpa using find_lower h c rfl
          have hlt : m < j := by omega
          rcases (find_iff c a m j τ).mp h with ⟨he,_⟩ | ⟨σ,ρ,v,hσ,hv,hρ,rfl⟩
          · omega
          · obtain ⟨_,values,records,ht,hp,hz,hr⟩ := (ih (m+1) j ρ (by omega)).mp hρ
            refine ⟨hmj,Fin.cons v values,Fin.cons σ records,?_,?_,?_,?_⟩
            · intro i
              refine Fin.cases ?_ (fun i => ?_) i
              · simpa using hσ
              · simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ht i
            · intro i
              refine Fin.cases ?_ (fun i => ?_) i
              · simpa using hv
              · simpa only [Fin.castSucc_succ,Fin.cons_succ] using hp i
            · simpa only [← Fin.succ_last,Fin.cons_succ] using hz
            · simp [hr]
        · rintro ⟨hmj,values,records,ht,hp,hz,hτ⟩
          let vs : Fin (k+1) → ℕ := fun i => values i.succ
          let rs : Fin (k+1) → QueryRecord := fun i => records i.succ
          have htail : Derives (.find' c) (Nat.pair a (m+1)) (List.ofFn rs).flatten j :=
            (ih (m+1) j _ (by omega)).mpr ⟨by omega,vs,rs,
              fun i => by simpa [vs,rs,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ht i.succ,
              fun i => by simpa [vs,Fin.castSucc_succ] using hp i.succ,
              by simpa [vs,Fin.succ_last] using hz,rfl⟩
          have hhead : Derives c (Nat.pair a m) (records 0) (values 0) := by simpa using ht 0
          have hpos : 0 < values 0 := by simpa using hp 0
          have hout := Derives.find_succ hhead hpos htail
          rw [hτ,List.ofFn_succ]
          simpa [rs] using hout
  exact go (j-m) m j τ rfl

theorem trace_sound {A : Set ℕ} {c : Code} {x y : ℕ} {τ : QueryRecord}
    (h : Derives c x τ y) (hA : Consistent A τ) : y ∈ eval A c x := by
  induction h with
  | zero | succ | left | right => simp [eval]
  | query q b hb =>
      have he := hA q b (by simp)
      simpa [eval] using he
  | pair hc hd ihc ihd =>
      obtain ⟨hσ, hτ⟩ := consistent_append.mp hA
      exact (eval_pair _ _ _ _ _).2 ⟨_, _, ihc hσ, ihd hτ, rfl⟩
  | comp hd hc ihd ihc =>
      obtain ⟨hσ, hτ⟩ := consistent_append.mp hA
      exact (eval_comp _ _ _ _ _).2 ⟨_, ihd hσ, ihc hτ⟩
  | prec_zero hc ih => simpa only [eval_prec_zero] using ih hA
  | prec_succ hc hd ihc ihd =>
      obtain ⟨hσ, hτ⟩ := consistent_append.mp hA
      rw [eval_prec_succ, Part.mem_bind_iff]
      exact ⟨_, ihc hσ, ihd hτ⟩
  | @find_zero c a m τ hc ih =>
      apply (eval_find A c a m m).2
      exact ⟨le_rfl, ih hA, by omega⟩
  | @find_succ c a m v j σ τ hc hv hd ihc ihd =>
      obtain ⟨hσ, hτ⟩ := consistent_append.mp hA
      obtain ⟨hmj, hj, hp⟩ := (eval_find A c a (m + 1) j).1 (ihd hτ)
      apply (eval_find A c a m j).2
      refine ⟨by omega, hj, ?_⟩
      intro i hmi hij
      by_cases hi : i = m
      · subst i; exact ⟨v, ihc hσ, hv⟩
      · exact hp i (by omega) hij

theorem trace_complete (A : Set ℕ) (c : Code) (x y : ℕ) :
    y ∈ eval A c x ↔ ∃ τ : QueryRecord, Derives c x τ y ∧ Consistent A τ := by
  constructor
  · induction c generalizing x y with
    | zero =>
        intro hy; obtain rfl := Part.mem_some_iff.mp hy
        exact ⟨[], .zero x, consistent_nil A⟩
    | succ =>
        intro hy; obtain rfl := Part.mem_some_iff.mp hy
        exact ⟨[], .succ x, consistent_nil A⟩
    | left =>
        intro hy; obtain rfl := Part.mem_some_iff.mp hy
        exact ⟨[], .left x, consistent_nil A⟩
    | right =>
        intro hy; obtain rfl := Part.mem_some_iff.mp hy
        exact ⟨[], .right x, consistent_nil A⟩
    | query =>
        intro hy; obtain rfl := Part.mem_some_iff.mp hy
        refine ⟨[(x, indicator (fun q => q ∈ A) x)], .query _ _ ?_, ?_⟩
        · classical
          simp only [indicator]
          split <;> simp
        · simp [Consistent]
    | pair c d ihc ihd =>
        intro hy
        obtain ⟨u,v,hu,hv,rfl⟩ := (eval_pair A c d x y).1 hy
        obtain ⟨σ,hσ,hσA⟩ := ihc x u hu
        obtain ⟨τ,hτ,hτA⟩ := ihd x v hv
        exact ⟨σ ++ τ, .pair hσ hτ, consistent_append.mpr ⟨hσA,hτA⟩⟩
    | comp c d ihc ihd =>
        intro hy
        obtain ⟨v,hv,hy⟩ := (eval_comp A c d x y).1 hy
        obtain ⟨σ,hσ,hσA⟩ := ihd x v hv
        obtain ⟨τ,hτ,hτA⟩ := ihc v y hy
        exact ⟨σ ++ τ, .comp hσ hτ, consistent_append.mpr ⟨hσA,hτA⟩⟩
    | prec c d ihc ihd =>
        obtain ⟨⟨a,n⟩,rfl⟩ := Nat.pairEquiv.surjective x
        change y ∈ eval A (.prec c d) (Nat.pair a n) →
          ∃ τ, Derives (.prec c d) (Nat.pair a n) τ y ∧ Consistent A τ
        induction n generalizing y with
        | zero =>
            intro hy
            obtain ⟨τ,hτ,hτA⟩ := ihc a y (by simpa only [eval_prec_zero] using hy)
            exact ⟨τ,.prec_zero hτ,hτA⟩
        | succ n ihn =>
            rw [eval_prec_succ, Part.mem_bind_iff]
            rintro ⟨v,hv,hy⟩
            obtain ⟨σ,hσ,hσA⟩ := ihn v hv
            obtain ⟨τ,hτ,hτA⟩ := ihd _ y hy
            exact ⟨σ ++ τ,.prec_succ hσ hτ,consistent_append.mpr ⟨hσA,hτA⟩⟩
    | find' c ihc =>
        obtain ⟨⟨a,m⟩,rfl⟩ := Nat.pairEquiv.surjective x
        intro hy
        obtain ⟨hmj,hj,hp⟩ := (eval_find A c a m y).1 hy
        have go : ∀ k m j, j - m = k → m ≤ j →
            0 ∈ eval A c (Nat.pair a j) →
            (∀ i, m ≤ i → i < j → ∃ v, v ∈ eval A c (Nat.pair a i) ∧ 0 < v) →
            ∃ τ, Derives (.find' c) (Nat.pair a m) τ j ∧ Consistent A τ := by
          intro k
          induction k with
          | zero =>
              intro m j hk hmj hj _
              have he : m = j := by omega
              subst j
              obtain ⟨τ,hτ,hτA⟩ := ihc _ 0 hj
              exact ⟨τ,.find_zero hτ,hτA⟩
          | succ k ih =>
              intro m j hk hmj hj hp
              obtain ⟨v,hv,hvpos⟩ := hp m le_rfl (by omega)
              obtain ⟨σ,hσ,hσA⟩ := ihc _ v hv
              obtain ⟨τ,hτ,hτA⟩ := ih (m+1) j (by omega) (by omega) hj
                (fun i hmi hij => hp i (by omega) hij)
              exact ⟨σ ++ τ,.find_succ hσ hvpos hτ,consistent_append.mpr ⟨hσA,hτA⟩⟩
        exact go (y-m) m y rfl hmj hj hp
  · rintro ⟨τ,hτ,hA⟩
    exact trace_sound hτ hA

theorem consistent_derivations_unique {A : Set ℕ} {c : Code} {x a b : ℕ}
    {σ τ : QueryRecord} (ha : Derives c x σ a) (hb : Derives c x τ b)
    (hσ : Consistent A σ) (hτ : Consistent A τ) : a = b := by
  exact Part.mem_unique (trace_sound ha hσ) (trace_sound hb hτ)

private def QueryFree : Code → Prop
  | .query => False
  | .pair c d | .comp c d | .prec c d => QueryFree c ∧ QueryFree d
  | .find' c => QueryFree c
  | _ => True

private theorem free_record_empty {c : Code} {x y : ℕ} {τ : QueryRecord}
    (h : Derives c x τ y) : QueryFree c → τ = [] := by
  induction h <;> simp_all [QueryFree]

theorem embed_record_empty {c : Nat.Partrec.Code} {x y : ℕ} {τ : QueryRecord}
    (h : Derives (embed c) x τ y) : τ = [] := by
  apply free_record_empty h
  clear h
  induction c <;> simp_all [embed, QueryFree]

theorem embed_empty_trace (c : Nat.Partrec.Code) (x y : ℕ) :
    y ∈ Nat.Partrec.Code.eval c x ↔ Derives (embed c) x [] y := by
  rw [← eval_embed (∅ : Set ℕ) c x, trace_complete]
  constructor
  · rintro ⟨τ,hτ,_⟩
    simpa only [embed_record_empty hτ] using hτ
  · intro h
    exact ⟨[],h,consistent_nil ∅⟩

end Lemmatheca.ComputabilityTheory.OracleComputation
