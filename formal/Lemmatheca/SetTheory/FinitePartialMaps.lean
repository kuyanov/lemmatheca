import Lemmatheca.SetTheory.DeltaSystems
import Mathlib.Data.Finmap
import Mathlib.SetTheory.Cardinal.Finite

namespace Lemmatheca.SetTheory.FinitePartialMaps

open Set Cardinal
universe u
variable {α : Type u}

abbrev BinaryMap (α : Type u) := Finmap (fun _ : α => Bool)

def graph (p : BinaryMap α) : Set (α × Bool) :=
  {xb | (⟨xb.1, xb.2⟩ : Sigma (fun _ : α => Bool)) ∈ p.entries}

def Extends (p q : BinaryMap α) : Prop := graph q ⊆ graph p

def Compatible (p q : BinaryMap α) : Prop := ∃ r, Extends r p ∧ Extends r q

def Agree (p q : BinaryMap α) : Prop :=
  ∀ x b c, (x, b) ∈ graph p → (x, c) ∈ graph q → b = c

private theorem graph_lookup [DecidableEq α] (p : BinaryMap α) (x : α) (b : Bool) :
    (x, b) ∈ graph p ↔ p.lookup x = some b := by
  exact Finmap.lookup_eq_some_iff.symm

private theorem graph_unique (p : BinaryMap α) (x : α) (b c : Bool)
    (hb : (x, b) ∈ graph p) (hc : (x, c) ∈ graph p) : b = c := by
  classical
  exact Option.some.inj ((graph_lookup p x b).mp hb |>.symm.trans ((graph_lookup p x c).mp hc))

private theorem agree_union [DecidableEq α] {p q : BinaryMap α} (h : Agree p q) :
    Extends (p ∪ q) p ∧ Extends (p ∪ q) q ∧ graph (p ∪ q) = graph p ∪ graph q := by
  have hp : Extends (p ∪ q) p := by
    rintro ⟨x, b⟩ hb
    rw [graph_lookup] at hb ⊢
    rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hb)]
    exact hb
  have hq : Extends (p ∪ q) q := by
    rintro ⟨x, b⟩ hb
    by_cases hx : x ∈ p
    · obtain ⟨c, hc⟩ := Finmap.mem_iff.mp hx
      have hcb := h x c b ((graph_lookup p x c).mpr hc) hb
      rw [graph_lookup, Finmap.lookup_union_left hx, hc, hcb]
    · rw [graph_lookup, Finmap.lookup_union_right hx]
      exact (graph_lookup q x b).mp hb
  refine ⟨hp, hq, ?_⟩
  ext xb
  rcases xb with ⟨x, b⟩
  constructor
  · intro hb
    have hb' : b ∈ (p ∪ q).lookup x := (graph_lookup _ x b).mp hb
    rcases Finmap.mem_lookup_union.mp hb' with hb | ⟨_, hb⟩
    · exact Or.inl ((graph_lookup p x b).mpr hb)
    · exact Or.inr ((graph_lookup q x b).mpr hb)
  · rintro (hb | hb)
    · exact hp hb
    · exact hq hb

theorem compatible_iff_agree (p q : BinaryMap α) : Compatible p q ↔ Agree p q := by
  classical
  constructor
  · rintro ⟨r, hrp, hrq⟩ x b c hb hc
    exact graph_unique r x b c (hrp hb) (hrq hc)
  · intro h
    exact ⟨p ∪ q, (agree_union h).1, (agree_union h).2.1⟩

theorem graph_union_common_extension {p q : BinaryMap α} (h : Agree p q) :
    ∃ r, Extends r p ∧ Extends r q ∧ graph r = graph p ∪ graph q := by
  classical
  exact ⟨p ∪ q, agree_union h⟩

private noncomputable def domainEquiv (D : Finset α) :
    {p : BinaryMap α // p.keys = D} ≃ (D → Bool) := by
  classical
  let make (g : D → Bool) : BinaryMap α :=
    Finmap.keysLookupEquiv.symm ⟨(D, fun x => if hx : x ∈ D then some (g ⟨x, hx⟩) else none),
      fun x => by by_cases hx : x ∈ D <;> simp [hx]⟩
  have make_keys (g : D → Bool) : (make g).keys = D := by
    simp [make]
  have make_lookup (g : D → Bool) (x : α) :
      (make g).lookup x = if hx : x ∈ D then some (g ⟨x, hx⟩) else none := by
    simp [make]
  exact {
    toFun := fun p x => (p.1.lookup x.1).getD false
    invFun := fun g => ⟨make g, make_keys g⟩
    left_inv := fun p => by
      apply Subtype.ext
      apply Finmap.ext_lookup
      intro x
      change (make (fun z : D => (p.1.lookup z.1).getD false)).lookup x = p.1.lookup x
      rw [make_lookup (fun z : D => (p.1.lookup z.1).getD false) x]
      by_cases hx : x ∈ D
      · have hx' : x ∈ p.1 := by simpa [← Finmap.mem_keys, p.2] using hx
        obtain ⟨b, hb⟩ := Finmap.mem_iff.mp hx'
        simp [hx, hb]
      · have hx' : x ∉ p.1 := by simpa [← Finmap.mem_keys, p.2] using hx
        simp [hx, Finmap.lookup_eq_none.mpr hx']
    right_inv := fun g => by
      funext x
      change ((make g).lookup x.1).getD false = g x
      rw [make_lookup]
      simp [x.2] }

theorem fixed_domain_cardinality (D : Finset α) :
    #{p : BinaryMap α // p.keys = D} = (2 : Cardinal) ^ D.card := by
  classical
  rw [Cardinal.mk_congr (domainEquiv D)]
  simp

theorem uncountable_compatible_subfamily {P : Set (BinaryMap α)} (hP : ¬ P.Countable) :
    ∃ Q ⊆ P, ¬ Q.Countable ∧ Q.Pairwise Compatible := by
  classical
  have hfiber (D : Finset α) : Set.Finite {p : BinaryMap α | p.keys = D} := by
    let : Finite {p : BinaryMap α // p.keys = D} :=
      Finite.of_injective (domainEquiv D) (domainEquiv D).injective
    change Finite {p : BinaryMap α // p.keys = D}
    infer_instance
  let dom (p : BinaryMap α) : Set α := p.keys
  have hdom : ¬ (dom '' P).Countable := by
    intro h
    have hkeys : (Finmap.keys '' P).Countable := by
      have hinj : Function.Injective (fun D : Finset α => (D : Set α)) := Finset.coe_injective
      apply Set.countable_of_injective_of_countable_image hinj.injOn
      simpa only [Set.image_image] using h
    apply hP
    apply (hkeys.biUnion (fun D _ => (hfiber D).countable)).mono
    intro p hp
    exact mem_iUnion₂.mpr ⟨p.keys, ⟨p, hp, rfl⟩, rfl⟩
  obtain ⟨B, hB, hBu, r, hr, hdelta⟩ :=
    Lemmatheca.SetTheory.DeltaSystems.uncountable_delta_system hdom
      (by rintro _ ⟨p, _, rfl⟩; exact p.keys.finite_toSet)
  have hsurj : Set.SurjOn dom {p | p ∈ P ∧ dom p ∈ B} B := by
    intro D hD
    obtain ⟨p, hp, hpd⟩ := hB hD
    exact ⟨p, ⟨hp, hpd.symm ▸ hD⟩, hpd⟩
  obtain ⟨P', hP'sub, hinj, himage⟩ := hsurj.exists_subset_injOn_image_eq
  have hP' : ¬ P'.Countable := by
    intro h
    apply hBu
    simpa [himage] using h.image dom
  let : Finite r := hr.to_subtype
  let code (p : BinaryMap α) (x : r) : Option Bool := p.lookup x.1
  have hf : ∃ c, ¬ (P' ∩ code ⁻¹' {c}).Countable := by
    by_contra! h
    apply hP'
    have hc := Set.countable_iUnion h
    have heq : (⋃ c, P' ∩ code ⁻¹' {c}) = P' := by ext p; simp
    rwa [heq] at hc
  obtain ⟨c, hc⟩ := hf
  refine ⟨P' ∩ code ⁻¹' {c}, fun p hp => (hP'sub hp.1).1, hc, ?_⟩
  intro p hp q hq hpq
  apply (compatible_iff_agree p q).mpr
  intro x b d hpb hqd
  have hxp : x ∈ dom p := Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some ((graph_lookup p x b).mp hpb))
  have hxq : x ∈ dom q := Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some ((graph_lookup q x d).mp hqd))
  by_cases hdompq : dom p = dom q
  · exact False.elim (hpq (hinj hp.1 hq.1 hdompq))
  · have hxr : x ∈ r := (hdelta _ (hP'sub hp.1).2 _ (hP'sub hq.1).2 hdompq) ▸ (show x ∈ dom p ∩ dom q from ⟨hxp, hxq⟩)
    have hl : p.lookup x = q.lookup x := congrFun (hp.2.trans hq.2.symm) ⟨x, hxr⟩
    exact Option.some.inj (((graph_lookup p x b).mp hpb).symm.trans (hl.trans ((graph_lookup q x d).mp hqd)))

theorem incompatible_family_countable {P : Set (BinaryMap α)}
    (hP : P.Pairwise (fun p q => ¬ Compatible p q)) : P.Countable := by
  by_contra h
  obtain ⟨Q, hQP, hQ, hcomp⟩ := uncountable_compatible_subfamily h
  have hn : ¬ Q.Subsingleton := fun hs => hQ hs.countable
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.not_subsingleton_iff.mp hn
  exact hP (hQP hp) (hQP hq) hpq (hcomp hp hq hpq)

def zeroSingletons (α : Type u) : Set (BinaryMap α) :=
  Set.range (fun x : α => Finmap.singleton x false)

theorem zero_singletons_specification [Uncountable α] :
    ¬ (zeroSingletons α).Countable ∧ (zeroSingletons α).Pairwise Compatible ∧
      (¬ ∃ r : BinaryMap α, ∀ p ∈ zeroSingletons α, Extends r p) ∧
      (⋃ p ∈ zeroSingletons α, graph p) = Set.range (fun x : α => (x, false)) := by
  classical
  have hgraph (x : α) : graph (Finmap.singleton x false) = {(x, false)} := by
    ext ⟨z, b⟩
    simp [graph, Finmap.singleton, AList.singleton]
  have hinj : Function.Injective (fun x : α => Finmap.singleton x false) := by
    intro x y h
    have h' := congrArg Finmap.keys h
    simpa using h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h' : (univ : Set α).Countable :=
      Set.countable_of_injective_of_countable_image hinj.injOn
        (by simpa [zeroSingletons] using h)
    exact not_countable (Set.countable_univ_iff.mp h')
  · rintro p ⟨x, rfl⟩ q ⟨y, rfl⟩ _
    apply (compatible_iff_agree _ _).mpr
    intro z b c hb hc
    rw [hgraph, mem_singleton_iff] at hb hc
    exact (congrArg Prod.snd hb).trans (congrArg Prod.snd hc).symm
  · rintro ⟨r, hr⟩
    have hall : (univ : Set α) ⊆ (r.keys : Set α) := by
      intro x _
      have hx := hr (Finmap.singleton x false) ⟨x, rfl⟩
        (show (x, false) ∈ graph (Finmap.singleton x false) by rw [hgraph]; simp)
      exact Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some ((graph_lookup r x false).mp hx))
    have : (univ : Set α).Finite := r.keys.finite_toSet.subset hall
    exact Set.infinite_univ this
  · ext xb
    constructor
    · intro h
      obtain ⟨p, hp, hxb⟩ := mem_iUnion₂.mp h
      obtain ⟨x, rfl⟩ := hp
      rw [hgraph, mem_singleton_iff] at hxb
      exact ⟨x, hxb.symm⟩
    · rintro ⟨x, rfl⟩
      exact mem_iUnion₂.mpr ⟨_, ⟨x, rfl⟩, by rw [hgraph]; simp⟩

end Lemmatheca.SetTheory.FinitePartialMaps
