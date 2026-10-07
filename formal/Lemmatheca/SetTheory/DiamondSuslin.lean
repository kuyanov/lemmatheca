import Lemmatheca.SetTheory.InfiniteTrees
import Lemmatheca.SetTheory.Clubs
import Lemmatheca.SetTheory.NormalFunctions
import Mathlib.SetTheory.Ordinal.FixedPoint

/-! Diamond is an explicit guessing-sequence hypothesis. No global axiom
asserting diamond or the existence of a Suslin tree is introduced. -/

noncomputable section
namespace Lemmatheca.SetTheory.DiamondSuslin

open Set Order Cardinal Ordinal

abbrev OmegaOne := Clubs.Carrier (ℵ₁ : Cardinal.{0})
abbrev BinaryNode := InfiniteTrees.FunctionNode (Cardinal.ord (ℵ₁ : Cardinal.{0})) Bool

local instance : Fact (ℵ₁ : Cardinal.{0}).IsRegular := ⟨Cardinal.isRegular_aleph_one⟩

local instance : PartialOrder BinaryNode := InfiniteTrees.functionNodePartialOrder

private theorem position_lt {α β : OmegaOne} :
    α < β ↔ α.toOrd.val < β.toOrd.val :=
  Ordinal.ToType.mk.symm.lt_iff_lt.symm

@[simp] private theorem position_mk (a : Set.Iio (Cardinal.ord (ℵ₁ : Cardinal.{0}))) :
    (Ordinal.ToType.mk a).toOrd.val = a.val :=
  congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply a)

def IsDiamondSequence (D : OmegaOne → Set OmegaOne) : Prop :=
  (∀ α, D α ⊆ Set.Iio α) ∧
    ∀ X : Set OmegaOne, IsStationary {α | D α = X ∩ Set.Iio α}

def Diamond : Prop := ∃ D, IsDiamondSequence D

def IsSuslinTree (T : InfiniteTrees.Tree.{0}) : Prop :=
  InfiniteTrees.treeHeight T = (Cardinal.ord (ℵ₁ : Cardinal.{0})) ∧
    (∀ C : Set T, IsChain (· ≤ ·) C → C.Countable) ∧
    ∀ A : Set T, IsAntichain (· ≤ ·) A → A.Countable

def BinaryLevel (S : Set BinaryNode) (α : (Cardinal.ord (ℵ₁ : Cardinal.{0})).ToType) : Set BinaryNode :=
  {t | t ∈ S ∧ t.1 = α}

def IsNormalBinaryTree (S : Set BinaryNode) : Prop :=
  InfiniteTrees.RestrictionClosed S ∧
    (∀ α, (BinaryLevel S α).Nonempty ∧ (BinaryLevel S α).Countable) ∧
    (∀ s ∈ S, ∀ α, s.1 < α →
      ∃ t ∈ S, t.1 = α ∧ InfiniteTrees.Extends s t) ∧
    ∀ s ∈ S, ∃ t₀ ∈ S, ∃ t₁ ∈ S,
      t₀ ≠ t₁ ∧ t₀.1 = Order.succ s.1 ∧ t₁.1 = Order.succ s.1 ∧
        InfiniteTrees.Extends s t₀ ∧ InfiniteTrees.Extends s t₁

def IsNormalBelow (S : Set BinaryNode) (δ : OmegaOne) : Prop :=
  InfiniteTrees.RestrictionClosed S ∧
    (∀ t ∈ S, t.1 < δ) ∧
    (∀ α < δ, (BinaryLevel S α).Nonempty ∧ (BinaryLevel S α).Countable) ∧
    ∀ s ∈ S, ∀ α, s.1 < α → α < δ →
      ∃ t ∈ S, t.1 = α ∧ InfiniteTrees.Extends s t

def IsMaxAntichainIn (S A : Set BinaryNode) : Prop :=
  A ⊆ S ∧ IsAntichain InfiniteTrees.Extends A ∧
    ∀ s ∈ S, ∃ a ∈ A, InfiniteTrees.Extends s a ∨ InfiniteTrees.Extends a s

private theorem extends_refl (s : BinaryNode) : InfiniteTrees.Extends s s :=
  ⟨le_rfl, by funext i; rfl⟩

private theorem extends_trans {s t u : BinaryNode}
    (hst : InfiniteTrees.Extends s t) (htu : InfiniteTrees.Extends t u) :
    InfiniteTrees.Extends s u := by
  refine ⟨hst.1.trans htu.1, ?_⟩
  funext i
  exact (congrFun hst.2 i).trans
    (congrFun htu.2 (InfiniteTrees.initialSegmentEmbedding hst.1 i))

private theorem binary_chain_limit (S : Set BinaryNode) (δ : OmegaOne)
    (hS : IsNormalBelow S δ) (v : ℕ → S) (hv : Monotone (fun n => (v n).val))
    (hcover : ∀ α < δ, ∃ n, α < (v n).val.1) :
    ∃ t : BinaryNode, ∃ ht : t.1 = δ,
      (∀ β (h : β < δ), InfiniteTrees.restrictNode t β (by rw [ht]; exact h.le) ∈ S) ∧
      ∀ n, InfiniteTrees.Extends (v n).val t := by
  classical
  choose index hindex using fun i : Set.Iio δ => hcover i.val i.property
  let f : Set.Iio δ → Bool := fun i => (v (index i)).val.2 ⟨i.val, hindex i⟩
  let t : BinaryNode := ⟨δ, f⟩
  have hext (n : ℕ) : InfiniteTrees.Extends (v n).val t := by
    refine ⟨(hS.2.1 _ (v n).property).le, ?_⟩
    funext i
    let j : Set.Iio δ := ⟨i.val, i.property.trans (hS.2.1 _ (v n).property)⟩
    let m := max n (index j)
    have hn := hv (le_max_left n (index j))
    have hj := hv (le_max_right n (index j))
    have hn' := congrFun hn.2 i
    have hj' := congrFun hj.2 (⟨i.val, hindex j⟩ : Set.Iio (v (index j)).val.1)
    exact hn'.trans hj'.symm
  refine ⟨t, rfl, ?_, hext⟩
  intro β hβ
  obtain ⟨n, hn⟩ := hcover β hβ
  have he := hext n
  have hr : InfiniteTrees.restrictNode t β hβ.le =
      InfiniteTrees.restrictNode (v n).val β hn.le := by
    apply congrArg (Sigma.mk β)
    funext i
    exact (congrFun he.2 (⟨i.val, i.property.trans_le hn.le⟩ : Set.Iio (v n).val.1)).symm
  rw [hr]
  exact hS.1 _ (v n).property β hn.le

theorem countable_limit_extension (S A : Set BinaryNode) (δ : OmegaOne)
    (hδ : Order.IsSuccLimit δ) (hS : IsNormalBelow S δ)
    (hA : A = ∅ ∨ IsMaxAntichainIn S A) :
    ∃ L : Set BinaryNode, L.Countable ∧ L.Nonempty ∧
      (∀ t ∈ L, ∃ ht : t.1 = δ, ∀ β (h : β < δ), InfiniteTrees.restrictNode t β
        (by rw [ht]; exact h.le) ∈ S) ∧
      (∀ s ∈ S, ∃ t ∈ L, InfiniteTrees.Extends s t) ∧
      ∀ t ∈ L, A ≠ ∅ → ∃ a ∈ A, InfiniteTrees.Extends a t := by
  classical
  have hcount : (Set.Iio δ).Countable :=
    Cardinal.le_aleph0_iff_set_countable.mp
      (Cardinal.lt_aleph_one_iff.mp (by
        simpa [OmegaOne, Clubs.Carrier] using Cardinal.mk_Iio_lt δ
          (by simp [OmegaOne, Clubs.Carrier])))
  let : Countable (Set.Iio δ) := hcount.to_subtype
  let : Nonempty (Set.Iio δ) := hδ.nonempty_Iio.to_subtype
  let : NoMaxOrder (Set.Iio δ) := ⟨fun α =>
    ⟨⟨Order.succ α.val, hδ.succ_lt α.property⟩, by change α.val < Order.succ α.val; exact Order.lt_succ_of_not_isMax α.property.not_isMax⟩⟩
  obtain ⟨β, _, hβtop⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop (Set.Iio δ)
  have hβcover (α : OmegaOne) (hα : α < δ) : ∃ n, α < (β n).val := by
    obtain ⟨γ, hγ⟩ := exists_gt (⟨α, hα⟩ : Set.Iio δ)
    obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.mp hβtop γ).exists
    exact ⟨n, hγ.trans_le hn⟩
  have hScount : S.Countable := by
    apply (Set.countable_iUnion fun α : Set.Iio δ => (hS.2.2.1 α.val α.property).2).mono
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t.1, hS.2.1 t ht⟩, ht, rfl⟩
  let : Countable S := hScount.to_subtype
  have hSne : S.Nonempty := by
    obtain ⟨α, hα⟩ := hδ.nonempty_Iio
    obtain ⟨t, ht, _⟩ := (hS.2.2.1 α hα).1
    exact ⟨t, ht⟩
  have hstart (s : S) : ∃ v ∈ S, InfiniteTrees.Extends s.val v ∧
      (A ≠ ∅ → ∃ a ∈ A, InfiniteTrees.Extends a v) := by
    rcases hA with he | ha
    · exact ⟨s.val, s.property, extends_refl s.val, fun hn => (hn he).elim⟩
    · obtain ⟨a, haA, hcomp⟩ := ha.2.2 s.val s.property
      rcases hcomp with hs | hs
      · exact ⟨a, ha.1 haA, hs, fun _ => ⟨a, haA, extends_refl a⟩⟩
      · exact ⟨s.val, s.property, extends_refl s.val, fun _ => ⟨a, haA, hs⟩⟩
  have hnext (s : S) (n : ℕ) : ∃ t ∈ S,
      t.1 = Order.succ (max s.val.1 (β n).val) ∧ InfiniteTrees.Extends s.val t := by
    apply hS.2.2.2 s.val s.property
    · exact (le_max_left _ _).trans_lt
        (Order.lt_succ_of_not_isMax (max_lt (hS.2.1 _ s.property) (β n).property).not_isMax)
    · exact hδ.succ_lt (max_lt (hS.2.1 _ s.property) (β n).property)
  choose next hnS hnheight hnExt using hnext
  have hbranch (s : S) : ∃ t : BinaryNode, ∃ ht : t.1 = δ,
      (∀ α (h : α < δ), InfiniteTrees.restrictNode t α (by rw [ht]; exact h.le) ∈ S) ∧
      InfiniteTrees.Extends s.val t ∧ (A ≠ ∅ → ∃ a ∈ A, InfiniteTrees.Extends a t) := by
    obtain ⟨v, hvS, hsv, hvA⟩ := hstart s
    let nodes : ℕ → S := Nat.rec ⟨v, hvS⟩ (fun n t => ⟨next t n, hnS t n⟩)
    have hnodes : Monotone (fun n => (nodes n).val) :=
      monotone_nat_of_le_succ fun n => hnExt (nodes n) n
    have hcover (α : OmegaOne) (hα : α < δ) : ∃ n, α < (nodes n).val.1 := by
      obtain ⟨n, hn⟩ := hβcover α hα
      refine ⟨n + 1, ?_⟩
      change α < (next (nodes n) n).1
      rw [hnheight]
      exact hn.trans_le (le_max_right _ _) |>.trans
        (Order.lt_succ_of_not_isMax
          (max_lt (hS.2.1 _ (nodes n).property) (β n).property).not_isMax)
    obtain ⟨t, ht, hr, he⟩ := binary_chain_limit S δ hS nodes hnodes hcover
    refine ⟨t, ht, hr, extends_trans hsv (he 0), ?_⟩
    intro hAne
    obtain ⟨a, ha, hav⟩ := hvA hAne
    exact ⟨a, ha, extends_trans hav (he 0)⟩
  choose branch hbheight hbrestrict hbExt hbA using hbranch
  let L := Set.range branch
  refine ⟨L, Set.countable_range branch, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hSne
    exact ⟨branch ⟨s, hs⟩, mem_range_self _⟩
  · rintro t ⟨s, rfl⟩
    exact ⟨hbheight s, hbrestrict s⟩
  · intro s hs
    exact ⟨branch ⟨s, hs⟩, mem_range_self _, hbExt ⟨s, hs⟩⟩
  · rintro t ⟨s, rfl⟩ hAne
    exact hbA s hAne


def LabelsInLevelIntervals (S : Set BinaryNode) (q : S ↪ OmegaOne) : Prop :=
  ∀ t : S, Ordinal.omega0 * t.val.1.toOrd.val ≤ (q t).toOrd.val ∧
    (q t).toOrd.val < Ordinal.omega0 * t.val.1.toOrd.val + Ordinal.omega0

private noncomputable def nodeCode (L : Set BinaryNode) : BinaryNode → ℕ := by
  classical
  exact if h : L.Countable then Classical.choose (Set.countable_iff_exists_injOn.mp h)
    else fun _ => 0

private theorem nodeCode_injective (L : Set BinaryNode) (hL : L.Countable) :
    Set.InjOn (nodeCode L) L := by
  classical
  unfold nodeCode
  rw [dite_eq_left hL]
  exact Classical.choose_spec (Set.countable_iff_exists_injOn.mp hL)

private theorem block_end_lt (α : OmegaOne) :
    Ordinal.omega0 * α.toOrd.val + Ordinal.omega0 < Cardinal.ord (ℵ₁ : Cardinal.{0}) := by
  have ha : α.toOrd.val.card ≤ (ℵ₀ : Cardinal.{0}) :=
    Cardinal.card_le_iff.mpr (by simpa using α.toOrd.property)
  have hc : (Ordinal.omega0 * α.toOrd.val + Ordinal.omega0).card ≤ (ℵ₀ : Cardinal.{0}) := by
    rw [Ordinal.card_add, Ordinal.card_mul, Ordinal.card_omega0]
    calc
      ℵ₀ * α.toOrd.val.card + ℵ₀ ≤ ℵ₀ * ℵ₀ + ℵ₀ := by gcongr
      _ = ℵ₀ := by simp
  have hh := Cardinal.card_le_iff.mp hc
  simpa using hh

private theorem canonical_labels (S : Set BinaryNode)
    (hc : ∀ α, (BinaryLevel S α).Countable) :
    ∃ q : S ↪ OmegaOne, LabelsInLevelIntervals S q ∧
      ∀ t : S, (q t).toOrd.val = Ordinal.omega0 * t.val.1.toOrd.val +
        nodeCode (BinaryLevel S t.val.1) t.val := by
  classical
  let code (α : OmegaOne) := nodeCode (BinaryLevel S α)
  have hcode (α : OmegaOne) := nodeCode_injective (BinaryLevel S α) (hc α)
  let label : S → Ordinal.{0} := fun t =>
    Ordinal.omega0 * t.val.1.toOrd.val + code t.val.1 t.val
  have hlo (t : S) : Ordinal.omega0 * t.val.1.toOrd.val ≤ label t :=
    le_self_add
  have hhi (t : S) : label t <
      Ordinal.omega0 * t.val.1.toOrd.val + Ordinal.omega0 :=
    (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)
  have hlt (t : S) : label t < Cardinal.ord (ℵ₁ : Cardinal.{0}) := by
    apply (hhi t).trans
    exact block_end_lt t.val.1
  let q : S → OmegaOne := fun t => Ordinal.ToType.mk ⟨label t, hlt t⟩
  have hqpos (t : S) : (q t).toOrd.val = label t := position_mk _
  have hdiv (t : S) : label t / Ordinal.omega0 = t.val.1.toOrd.val := by
    dsimp [label]
    rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
      Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 _), add_zero]
  have hqi : Function.Injective q := by
    intro t s he
    have he' : label t = label s := by
      simpa only [hqpos] using congrArg (fun α : OmegaOne => α.toOrd.val) he
    have hheight : t.val.1.toOrd.val = s.val.1.toOrd.val := by
      rw [← hdiv t, ← hdiv s, he']
    have hα : t.val.1 = s.val.1 :=
      Ordinal.ToType.mk.symm.injective (Subtype.ext hheight)
    have hc' : (code s.val.1 t.val : Ordinal) = code s.val.1 s.val := by
      have hlabel := he'
      dsimp [label] at hlabel
      rw [hα] at hlabel
      exact add_left_cancel hlabel
    have hcn : code s.val.1 t.val = code s.val.1 s.val := by exact_mod_cast hc'
    apply Subtype.ext
    exact hcode s.val.1 ⟨t.property, hα⟩ ⟨s.property, rfl⟩ hcn
  exact ⟨⟨q, hqi⟩, fun t =>
    ⟨(hlo t).trans_eq (hqpos t).symm, (hqpos t).trans_lt (hhi t)⟩, hqpos⟩


theorem level_labels_exist (S : Set BinaryNode)
    (hc : ∀ α, (BinaryLevel S α).Countable) :
    ∃ q : S ↪ OmegaOne, LabelsInLevelIntervals S q := by
  obtain ⟨q, hq, _⟩ := canonical_labels S hc
  exact ⟨q, hq⟩

theorem coding_club (S : Set BinaryNode) (q : S ↪ OmegaOne)
    (hq : LabelsInLevelIntervals S q) :
    IsClub {δ : OmegaOne | Order.IsSuccLimit δ ∧
      ∀ t : S, q t < δ ↔ t.val.1 < δ} := by
  classical
  let C : Set OmegaOne := {δ | Order.IsSuccLimit δ ∧
    ∀ t : S, q t < δ ↔ t.val.1 < δ}
  let f : OmegaOne → OmegaOne := fun β => Ordinal.ToType.mk
    ⟨Ordinal.omega0 * β.toOrd.val + Ordinal.omega0, block_end_lt β⟩
  have hreverse (t : S) (δ : OmegaOne) (ht : q t < δ) : t.val.1 < δ := by
    apply position_lt.mpr
    have hd : t.val.1.toOrd.val ≤ Ordinal.omega0 * t.val.1.toOrd.val :=
      (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.le_apply
    exact (hd.trans (hq t).1).trans_lt (position_lt.mp ht)
  have hclosure : Clubs.closurePoints f ⊆ C := by
    intro δ hδ
    refine ⟨hδ.1, fun t => ⟨hreverse t δ, ?_⟩⟩
    intro ht
    have hh := hδ.2 t.val.1 ht
    apply position_lt.mpr
    exact (hq t).2.trans (by simpa [f] using position_lt.mp hh)
  have hcof : ℵ₀ < Order.cof OmegaOne := by simp [OmegaOne, Clubs.Carrier]
  let : Fact (ℵ₁ : Cardinal.{0}).IsRegular := ⟨Cardinal.isRegular_aleph_one⟩
  apply (Clubs.club_iff C).mpr
  refine ⟨?_, (Clubs.unbounded_iff C).mpr
    ((Clubs.closurePoints_club hcof f).2.mono hclosure)⟩
  intro δ hδ hC
  refine ⟨hδ, fun t => ⟨hreverse t δ, ?_⟩⟩
  intro ht
  obtain ⟨γ, hγ, htγ, hγδ⟩ := hC t.val.1 ht
  exact ((hγ.2 t).mpr htγ).trans hγδ



theorem fixed_point_coding_club (S : Set BinaryNode) (q : S ↪ OmegaOne)
    (hq : LabelsInLevelIntervals S q) :
    IsClub {δ : OmegaOne | Order.IsSuccLimit δ ∧
      Ordinal.omega0 * δ.toOrd.val = δ.toOrd.val} ∧
    ∀ δ : OmegaOne, Order.IsSuccLimit δ →
      Ordinal.omega0 * δ.toOrd.val = δ.toOrd.val →
      ∀ t : S, q t < δ ↔ t.val.1 < δ := by
  classical
  let f : OmegaOne → OmegaOne := fun β => Ordinal.ToType.mk
    ⟨Ordinal.omega0 * β.toOrd.val + Ordinal.omega0, block_end_lt β⟩
  have hnormal := Ordinal.isNormal_mul_right Ordinal.omega0_pos
  have hlimit (δ : OmegaOne) (hδ : Order.IsSuccLimit δ) :
      Order.IsSuccLimit δ.toOrd.val := by
    refine ⟨?_, Order.isSuccPrelimit_iff_forall_lt_nonempty_Ioo.mpr ?_⟩
    · obtain ⟨β, hβ⟩ := hδ.nonempty_Iio
      exact not_isMin_of_lt (position_lt.mp hβ)
    · intro β hβ
      let b : OmegaOne := Ordinal.ToType.mk ⟨β, hβ.trans δ.toOrd.property⟩
      have hb : b < δ := position_lt.mpr (by simpa [b] using hβ)
      obtain ⟨γ, hbγ, hγδ⟩ := hδ.isSuccPrelimit.nonempty_Ioo_of_lt hb
      exact ⟨γ.toOrd.val, by simpa [b] using position_lt.mp hbγ,
        position_lt.mp hγδ⟩
  have heq : Clubs.closurePoints f =
      {δ : OmegaOne | Order.IsSuccLimit δ ∧
        Ordinal.omega0 * δ.toOrd.val = δ.toOrd.val} := by
    ext δ
    constructor
    · intro hδ
      refine ⟨hδ.1, le_antisymm ?_ hnormal.strictMono.le_apply⟩
      apply (hnormal.le_iff_forall_le (hlimit δ hδ.1)).mpr
      intro β hβ
      let b : OmegaOne := Ordinal.ToType.mk ⟨β, hβ.trans δ.toOrd.property⟩
      have hb : b < δ := position_lt.mpr (by simpa [b] using hβ)
      have hf := position_lt.mp (hδ.2 b hb)
      have hf' : Ordinal.omega0 * β + Ordinal.omega0 < δ.toOrd.val := by
        simpa [f, b] using hf
      exact le_self_add.trans hf'.le
    · rintro ⟨hδ, hfix⟩
      refine ⟨hδ, fun β hβ => position_lt.mpr ?_⟩
      simp only [f, position_mk]
      have hstep := hnormal.strictMono ((hlimit δ hδ).add_one_lt (position_lt.mp hβ))
      simpa only [mul_add, mul_one, hfix] using hstep
  refine ⟨heq ▸ Clubs.closurePoints_club (by simp [OmegaOne, Clubs.Carrier]) f, ?_⟩
  intro δ hδ hfix t
  constructor
  · intro ht
    apply position_lt.mpr
    exact (hnormal.strictMono.le_apply.trans (hq t).1).trans_lt (position_lt.mp ht)
  · intro ht
    apply position_lt.mpr
    have hstep := hnormal.strictMono ((hlimit δ hδ).add_one_lt (position_lt.mp ht))
    have hstep' : Ordinal.omega0 * t.val.1.toOrd.val + Ordinal.omega0 < δ.toOrd.val := by
      simpa only [mul_add, mul_one, hfix] using hstep
    exact (hq t).2.trans hstep'

def ReflectionBound (T : InfiniteTrees.Tree.{0}) (a : T → T) (β : OmegaOne) :
    Ordinal.{0} :=
  ⨆ t : {t : T // InfiniteTrees.nodeHeight T t < (β.toOrd.val + 1)},
    InfiniteTrees.nodeHeight T (a t.val) + 1

theorem antichain_reflection (T : InfiniteTrees.Tree.{0})
    (hheight : InfiniteTrees.treeHeight T = Cardinal.ord (ℵ₁ : Cardinal.{0}))
    (hc : ∀ α, (InfiniteTrees.level T α).Countable)
    (A : Set T) (hA : IsMaxAntichain (· ≤ ·) A) :
    ∃ a : T → T,
      (∀ t, a t ∈ A ∧ (a t ≤ t ∨ t ≤ a t)) ∧
      (∀ β, ReflectionBound T a β < Cardinal.ord (ℵ₁ : Cardinal.{0})) ∧
      (∀ δ : OmegaOne, Order.IsSuccLimit δ →
        (∀ β < δ, ReflectionBound T a β < δ.toOrd.val) →
        (∀ t : T, InfiniteTrees.nodeHeight T t < δ.toOrd.val →
          InfiniteTrees.nodeHeight T (a t) < δ.toOrd.val) ∧
        IsMaxAntichain (· ≤ ·)
          {t : {t : T // InfiniteTrees.nodeHeight T t < δ.toOrd.val} | t.val ∈ A}) ∧
      IsClub {δ : OmegaOne | Order.IsSuccLimit δ ∧
        ∀ t : T, InfiniteTrees.nodeHeight T t < δ.toOrd.val →
          InfiniteTrees.nodeHeight T (a t) < δ.toOrd.val} := by
  classical
  have hex (t : T) : ∃ s ∈ A, s ≤ t ∨ t ≤ s := by
    by_contra hn
    push Not at hn
    have htA : t ∉ A := fun ht => (hn t ht).1 le_rfl
    have hins : IsAntichain (· ≤ ·) (insert t A) :=
      Set.pairwise_insert.mpr ⟨hA.1, fun s hs _ => ⟨(hn s hs).2, (hn s hs).1⟩⟩
    have he := hA.2 hins (subset_insert t A)
    exact htA (he.symm ▸ mem_insert t A)
  choose a ha hcomp using hex
  have hheight' (t : T) : InfiniteTrees.nodeHeight T t < Cardinal.ord (ℵ₁ : Cardinal.{0}) := by
    have hle := Ordinal.le_iSup (fun t : T => InfiniteTrees.nodeHeight T t + 1) t
    change InfiniteTrees.nodeHeight T t + 1 ≤ InfiniteTrees.treeHeight T at hle
    exact (lt_add_one _).trans_le (hheight ▸ hle)
  have hbound (β : OmegaOne) : ReflectionBound T a β < Cardinal.ord (ℵ₁ : Cardinal.{0}) := by
    let R := {t : T | InfiniteTrees.nodeHeight T t < β.toOrd.val + 1}
    have hβ : β.toOrd.val + 1 < Ordinal.omega 1 := by
      have hh := (Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_aleph 1)).add_one_lt β.toOrd.property
      simpa using hh
    let : Countable (Set.Iio (β.toOrd.val + 1)) := Cardinal.countable_Iio_of_lt_omega_one hβ
    have hR : R.Countable := by
      apply (Set.countable_iUnion (fun α : Set.Iio (β.toOrd.val + 1) => hc α.val)).mono
      intro t ht
      exact mem_iUnion.mpr ⟨⟨InfiniteTrees.nodeHeight T t, ht⟩, rfl⟩
    let : Countable R := hR.to_subtype
    have hs : (⨆ t : R, InfiniteTrees.nodeHeight T (a t.val) + 1) < Ordinal.omega 1 := by
      apply Ordinal.iSup_lt_omega_one
      intro t
      have hh := (Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_aleph 1)).add_one_lt (hheight' (a t.val))
      simpa using hh
    exact hs.trans_eq (Cardinal.ord_aleph 1).symm
  let f : OmegaOne → OmegaOne := fun β => Ordinal.ToType.mk ⟨ReflectionBound T a β, hbound β⟩
  let C : Set OmegaOne := {δ | Order.IsSuccLimit δ ∧
    ∀ t : T, InfiniteTrees.nodeHeight T t < δ.toOrd.val →
      InfiniteTrees.nodeHeight T (a t) < δ.toOrd.val}
  have hclosed (δ : OmegaOne)
      (hf : ∀ β < δ, ReflectionBound T a β < δ.toOrd.val) :
      ∀ t : T, InfiniteTrees.nodeHeight T t < δ.toOrd.val →
        InfiniteTrees.nodeHeight T (a t) < δ.toOrd.val := by
    intro t ht
    let β : OmegaOne := Ordinal.ToType.mk ⟨InfiniteTrees.nodeHeight T t, hheight' t⟩
    have hβ : β < δ := position_lt.mpr (by simpa [β] using ht)
    have hi := Ordinal.le_iSup
      (fun s : {s : T // InfiniteTrees.nodeHeight T s < β.toOrd.val + 1} =>
        InfiniteTrees.nodeHeight T (a s.val) + 1)
      ⟨t, by simp [β]⟩
    exact (lt_add_one _).trans_le hi |>.trans (hf β hβ)
  have hrestricted (δ : OmegaOne)
      (hf : ∀ β < δ, ReflectionBound T a β < δ.toOrd.val) :
      IsMaxAntichain (· ≤ ·)
        {t : {t : T // InfiniteTrees.nodeHeight T t < δ.toOrd.val} | t.val ∈ A} := by
    refine ⟨?_, ?_⟩
    · intro s hs t ht hne hst
      exact hA.1 hs ht (fun he => hne (Subtype.ext he)) hst
    · intro B hB hAB
      apply subset_antisymm hAB
      intro t htB
      let w : {t : T // InfiniteTrees.nodeHeight T t < δ.toOrd.val} :=
        ⟨a t.val, hclosed δ hf t.val t.property⟩
      have hwA : w ∈ {t | t.val ∈ A} := ha t.val
      have hwB := hAB hwA
      have htw : t = w := by
        by_contra hne
        rcases hcomp t.val with hwle | htle
        · exact hB hwB htB (Ne.symm hne) hwle
        · exact hB htB hwB hne htle
      rw [htw]
      exact hwA
  have hclosure : Clubs.closurePoints f ⊆ C := by
    intro δ hδ
    refine ⟨hδ.1, hclosed δ ?_⟩
    intro β hβ
    simpa [f] using position_lt.mp (hδ.2 β hβ)
  have hcof : ℵ₀ < Order.cof OmegaOne := by simp [OmegaOne, Clubs.Carrier]
  let : Fact (ℵ₁ : Cardinal.{0}).IsRegular := ⟨Cardinal.isRegular_aleph_one⟩
  have hclub : IsClub C := by
    apply (Clubs.club_iff C).mpr
    refine ⟨?_, (Clubs.unbounded_iff C).mpr
      ((Clubs.closurePoints_club hcof f).2.mono hclosure)⟩
    intro δ hδ hC
    refine ⟨hδ, ?_⟩
    intro t ht
    let β : OmegaOne := Ordinal.ToType.mk ⟨InfiniteTrees.nodeHeight T t, hheight' t⟩
    have hβ : β < δ := position_lt.mpr (by simpa [β] using ht)
    obtain ⟨γ, hγ, hβγ, hγδ⟩ := hC β hβ
    exact (hγ.2 t (by simpa [β] using position_lt.mp hβγ)).trans (position_lt.mp hγδ)
  exact ⟨a, fun t => ⟨ha t, hcomp t⟩, hbound,
    fun δ _ hf => ⟨hclosed δ hf, hrestricted δ hf⟩, hclub⟩


theorem diamond_implies_ch (h : Diamond) : (Cardinal.continuum : Cardinal.{0}) = ℵ₁ := by
  classical
  obtain ⟨D, hD⟩ := h
  have hω : Ordinal.omega0 < Cardinal.ord (ℵ₁ : Cardinal.{0}) := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_strictMono (Cardinal.aleph0_lt_aleph_one :
      (ℵ₀ : Cardinal.{0}) < ℵ₁)
  let w0 : OmegaOne := Ordinal.ToType.mk ⟨Ordinal.omega0, hω⟩
  let e : ℕ ↪ OmegaOne :=
    ⟨fun n => Ordinal.ToType.mk ⟨n, (Ordinal.natCast_lt_omega0 n).trans hω⟩,
      fun n m hnm => by
        have he := congrArg (fun x : OmegaOne => x.toOrd.val) hnm
        simpa using he⟩
  have he (n : ℕ) : (e n).toOrd.val = n := position_mk _
  have hw : w0.toOrd.val = Ordinal.omega0 := position_mk _
  have hc : ℵ₀ < Order.cof OmegaOne := by
    simp [OmegaOne, Clubs.Carrier]
  have hex (S : Set ℕ) : ∃ α : OmegaOne, D α = e '' S := by
    obtain ⟨α, hα, hωα⟩ := Clubs.stationary_unbounded hc (hD.2 (e '' S)) w0
    have hs : e '' S ⊆ Set.Iio α := by
      rintro _ ⟨n, _, rfl⟩
      have hn : e n < w0 := by
        change (e n).toOrd.val < w0.toOrd.val
        rw [he, hw]
        exact Ordinal.natCast_lt_omega0 n
      exact hn.trans hωα
    exact ⟨α, hα.trans (Set.inter_eq_left.mpr hs)⟩
  choose guess hg using hex
  have hguess : Function.Injective guess := by
    intro S T hST
    have he : e '' S = e '' T := (hg S).symm.trans (hST ▸ hg T)
    exact (Set.image_injective.mpr e.injective) he
  have hle := Cardinal.mk_le_of_injective hguess
  have hcle : Cardinal.continuum ≤ (ℵ₁ : Cardinal.{0}) := by
    simpa [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0,
      OmegaOne, Clubs.Carrier] using hle
  exact le_antisymm hcle Cardinal.aleph_one_le_continuum

theorem suslin_levels_countable (T : InfiniteTrees.Tree.{0}) (h : IsSuslinTree T)
    (α : Ordinal.{0}) : (InfiniteTrees.level T α).Countable := by
  exact h.2.2 _ (InfiniteTrees.levels_antichain T α)

theorem binary_tree_heights (S : Set BinaryNode) (h : IsNormalBinaryTree S) :
    InfiniteTrees.treeHeight (InfiniteTrees.functionTree S h.1) = (Cardinal.ord (ℵ₁ : Cardinal.{0})) ∧
      ∀ t : S, InfiniteTrees.nodeHeight (InfiniteTrees.functionTree S h.1) t =
        t.val.1.toOrd.val := by
  have he (t : S) : InfiniteTrees.nodeHeight (InfiniteTrees.functionTree S h.1) t =
      t.val.1.toOrd.val := InfiniteTrees.functionTree_nodeHeight S h.1 t
  refine ⟨le_antisymm ?_ ?_, he⟩
  · apply Ordinal.iSup_le
    intro t
    exact (congrArg (fun a : Ordinal => a + 1) (he t)).trans_le
      (Order.add_one_le_of_lt t.val.1.toOrd.property)
  · apply le_of_forall_lt
    intro a ha
    let α : OmegaOne := Ordinal.ToType.mk ⟨a, ha⟩
    obtain ⟨t, htS, htα⟩ := (h.2.1 α).1
    let s : S := ⟨t, htS⟩
    have hs : InfiniteTrees.nodeHeight (InfiniteTrees.functionTree S h.1) s = a := by
      rw [he]
      simp [s, htα, α]
    have hi := Ordinal.le_iSup
      (fun s : S => InfiniteTrees.nodeHeight (InfiniteTrees.functionTree S h.1) s + 1) s
    rw [hs] at hi
    exact (lt_add_one a).trans_le hi

private def oldNodes (α : OmegaOne) (history : Set.Iio α → Set BinaryNode) : Set BinaryNode :=
  ⋃ β, history β

private noncomputable def oldLabel (α : OmegaOne) (history : Set.Iio α → Set BinaryNode)
    (t : BinaryNode) : Ordinal.{0} := by
  classical
  exact if ht : t.1 < α then
    Ordinal.omega0 * t.1.toOrd.val + nodeCode (history ⟨t.1, ht⟩) t else 0

private def guessedAntichain (D : OmegaOne → Set OmegaOne) (α : OmegaOne)
    (history : Set.Iio α → Set BinaryNode) : Set BinaryNode :=
  {t | t ∈ oldNodes α history ∧ ∃ i ∈ D α, i.toOrd.val = oldLabel α history t}

private structure GoodLevel (D : OmegaOne → Set OmegaOne) (α : OmegaOne)
    (history : Set.Iio α → Set BinaryNode) (L : Set BinaryNode) : Prop where
  countable : L.Countable
  nonempty : L.Nonempty
  height : ∀ t ∈ L, t.1 = α
  restriction : ∀ t ∈ L, ∀ β (hβ : β < α),
    ∃ hb : β ≤ t.1, InfiniteTrees.restrictNode t β hb ∈ history ⟨β, hβ⟩
  extension : ∀ β : Set.Iio α, ∀ s ∈ history β,
    ∃ t ∈ L, InfiniteTrees.Extends s t
  splitting : ∀ β (he : Order.succ β = α),
    ∀ s ∈ history ⟨β, by rw [← he]; exact Order.lt_succ β⟩,
      ∃ t₀ ∈ L, ∃ t₁ ∈ L, t₀ ≠ t₁ ∧
        InfiniteTrees.Extends s t₀ ∧ InfiniteTrees.Extends s t₁
  sealing : Order.IsSuccLimit α →
    IsMaxAntichainIn (oldNodes α history) (guessedAntichain D α history) →
      ∀ t ∈ L, ∃ a ∈ guessedAntichain D α history, InfiniteTrees.Extends a t

private theorem restriction_self (s : BinaryNode) (h : s.1 ≤ s.1) :
    InfiniteTrees.restrictNode s s.1 h = s := by
  cases s
  rfl

private theorem restrict_eq_self (s : BinaryNode) (β : OmegaOne) (hβ : β ≤ s.1)
    (he : β = s.1) : InfiniteTrees.restrictNode s β hβ = s := by
  subst β
  exact restriction_self s hβ

private theorem old_normal (D : OmegaOne → Set OmegaOne) (α : OmegaOne)
    (history : Set.Iio α → Set BinaryNode)
    (hgood : ∀ β : Set.Iio α,
      GoodLevel D β.val (fun γ : Set.Iio β.val => history ⟨γ.val, show γ.val < α from γ.property.trans β.property⟩) (history β)) :
    IsNormalBelow (oldNodes α history) α ∧
      ∀ β (hβ : β < α), BinaryLevel (oldNodes α history) β = history ⟨β, hβ⟩ := by
  classical
  have hheight (t : BinaryNode) (ht : t ∈ oldNodes α history) : t.1 < α := by
    obtain ⟨β, hβ⟩ := mem_iUnion.mp ht
    exact (hgood β).height t hβ ▸ β.property
  have hlevels (β : OmegaOne) (hβ : β < α) :
      BinaryLevel (oldNodes α history) β = history ⟨β, hβ⟩ := by
    ext t
    constructor
    · rintro ⟨ht, hth⟩
      obtain ⟨γ, hγ⟩ := mem_iUnion.mp ht
      have he : γ.val = β := ((hgood γ).height t hγ).symm.trans hth
      have he' : γ = ⟨β, hβ⟩ := Subtype.ext he
      exact he' ▸ hγ
    · intro ht
      exact ⟨mem_iUnion.mpr ⟨⟨β, hβ⟩, ht⟩, (hgood ⟨β, hβ⟩).height t ht⟩
  refine ⟨⟨?_, hheight, ?_, ?_⟩, hlevels⟩
  · intro t ht β hβ
    obtain ⟨γ, hγ⟩ := mem_iUnion.mp ht
    have htγ := (hgood γ).height t hγ
    have hβγ : β ≤ γ.val := hβ.trans_eq htγ
    rcases hβγ.eq_or_lt with he | he
    · have he' : β = t.1 := he.trans htγ.symm
      exact (restrict_eq_self t β hβ he').symm ▸ ht
    · obtain ⟨hb, hm⟩ := (hgood γ).restriction t hγ β he
      exact mem_iUnion.mpr ⟨⟨β, he.trans γ.property⟩, hm⟩
  · intro β hβ
    rw [hlevels β hβ]
    exact ⟨(hgood ⟨β, hβ⟩).nonempty, (hgood ⟨β, hβ⟩).countable⟩
  · intro s hs β hsβ hβα
    have hsα := hheight s hs
    have hslevel : s ∈ history ⟨s.1, hsα⟩ :=
      (hlevels s.1 hsα) ▸ And.intro hs rfl
    obtain ⟨t, ht, he⟩ := (hgood ⟨β, hβα⟩).extension ⟨s.1, hsβ⟩ s hslevel
    exact ⟨t, mem_iUnion.mpr ⟨⟨β, hβα⟩, ht⟩,
      (hgood ⟨β, hβα⟩).height t ht, he⟩

private def child (s : BinaryNode) (b : Bool) : BinaryNode :=
  ⟨Order.succ s.1, fun i => if h : i.val < s.1 then s.2 ⟨i.val, h⟩ else b⟩

private theorem child_extends (s : BinaryNode) (b : Bool) : InfiniteTrees.Extends s (child s b) := by
  refine ⟨Order.le_succ _, ?_⟩
  funext i
  change s.2 i = if h : i.val < s.1 then s.2 ⟨i.val, h⟩ else b
  split_ifs with h
  · rfl
  · exact (h i.property).elim

private theorem children_ne (s : BinaryNode) : child s false ≠ child s true := by
  intro he
  have hfun := eq_of_heq (Sigma.mk.inj he).2
  have hh := congrFun hfun (⟨s.1, Order.lt_succ s.1⟩ : Set.Iio (Order.succ s.1))
  simp at hh

private theorem restrict_of_extends {s t : BinaryNode} (hst : InfiniteTrees.Extends s t)
    (β : OmegaOne) (hb : β ≤ s.1) :
    InfiniteTrees.restrictNode s β hb = InfiniteTrees.restrictNode t β (hb.trans hst.1) := by
  apply congrArg (Sigma.mk β)
  funext i
  exact congrFun hst.2 (⟨i.val, i.property.trans_le hb⟩ : Set.Iio s.1)

private theorem good_level_exists (D : OmegaOne → Set OmegaOne) (α : OmegaOne)
    (history : Set.Iio α → Set BinaryNode)
    (hgood : ∀ β : Set.Iio α,
      GoodLevel D β.val (fun γ : Set.Iio β.val => history
        ⟨γ.val, show γ.val < α from γ.property.trans β.property⟩) (history β)) :
    ∃ L, GoodLevel D α history L := by
  classical
  obtain ⟨hnormal, hlevels⟩ := old_normal D α history hgood
  by_cases hlim : Order.IsSuccLimit α
  · let G := guessedAntichain D α history
    let A := if IsMaxAntichainIn (oldNodes α history) G then G else ∅
    have hA : A = ∅ ∨ IsMaxAntichainIn (oldNodes α history) A := by
      by_cases hm : IsMaxAntichainIn (oldNodes α history) G <;> simp [A, hm]
    obtain ⟨L, hc, hn, hh, he, hs⟩ := countable_limit_extension (oldNodes α history) A α hlim hnormal hA
    refine ⟨L, ⟨hc, hn, fun t ht => (hh t ht).choose, ?_, ?_, ?_, ?_⟩⟩
    · intro t ht β hβ
      obtain ⟨hheight, hr⟩ := hh t ht
      refine ⟨by rw [hheight]; exact hβ.le, ?_⟩
      have hm := hr β hβ
      have hbl : InfiniteTrees.restrictNode t β (by rw [hheight]; exact hβ.le) ∈
          BinaryLevel (oldNodes α history) β := ⟨hm, rfl⟩
      exact (hlevels β hβ) ▸ hbl
    · intro β s hS
      exact he s (mem_iUnion.mpr ⟨β, hS⟩)
    · intro β hβ
      exact (hlim.succ_ne β hβ).elim
    · intro _ hm t ht
      have heA : A = G := by simp [A, G, hm]
      have hAne : A ≠ ∅ := by
        obtain ⟨β, hβ⟩ := hlim.nonempty_Iio
        obtain ⟨s, hsS, _⟩ := (hnormal.2.2.1 β hβ).1
        obtain ⟨a, ha, _⟩ := hm.2.2 s hsS
        rw [heA]
        exact Set.nonempty_iff_ne_empty.mp ⟨a, ha⟩
      simpa only [heA] using hs t ht hAne
  · rcases Order.not_isSuccLimit_iff.mp hlim with hmin | hnpre
    · let t : BinaryNode := ⟨α, fun i => (hmin.not_lt i.property).elim⟩
      refine ⟨{t}, ⟨Set.countable_singleton _, Set.singleton_nonempty _, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro s hs; obtain rfl := Set.mem_singleton_iff.mp hs; rfl
      · intro s hs β hβ; exact (hmin.not_lt hβ).elim
      · intro β; exact (hmin.not_lt β.property).elim
      · intro β hb; exact (hmin.not_lt (hb ▸ Order.lt_succ β)).elim
      · exact fun hl => (hlim hl).elim
    · obtain ⟨β, hβmax, hβα⟩ := Order.not_isSuccPrelimit_iff_succ_eq.mp hnpre
      have hβ : β < α := hβα ▸ Order.lt_succ_of_not_isMax hβmax
      let B := history ⟨β, hβ⟩
      let L := (fun s => child s false) '' B ∪ (fun s => child s true) '' B
      have hbGood := hgood ⟨β, hβ⟩
      have hLheight (t : BinaryNode) (ht : t ∈ L) : t.1 = α := by
        rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ <;>
          exact congrArg Order.succ (hbGood.height s hs) |>.trans hβα
      have hLcount : L.Countable := (hbGood.countable.image _).union (hbGood.countable.image _)
      have hLne : L.Nonempty := by
        obtain ⟨s, hs⟩ := hbGood.nonempty
        exact ⟨child s false, Or.inl (mem_image_of_mem _ hs)⟩
      have hrestrict (s : BinaryNode) (hs : s ∈ B) (b : Bool)
          (γ : OmegaOne) (hγ : γ < α) :
          ∃ hb : γ ≤ (child s b).1,
            InfiniteTrees.restrictNode (child s b) γ hb ∈ history ⟨γ, hγ⟩ := by
        have hsβ := hbGood.height s hs
        have hγβ : γ ≤ β := Order.lt_succ_iff.mp (hβα.symm ▸ hγ)
        have hγs : γ ≤ s.1 := hγβ.trans_eq hsβ.symm
        refine ⟨hγs.trans (child_extends s b).1, ?_⟩
        rw [← restrict_of_extends (child_extends s b) γ hγs]
        rcases hγβ.eq_or_lt with he | he
        · have he' : γ = s.1 := he.trans hsβ.symm
          have hr := restrict_eq_self s γ hγs he'
          rw [hr]
          have hh : (⟨γ, hγ⟩ : Set.Iio α) = ⟨β, hβ⟩ := Subtype.ext he
          exact hh.symm ▸ hs
        · obtain ⟨hb, hm⟩ := hbGood.restriction s hs γ he
          exact hm
      refine ⟨L, ⟨hLcount, hLne, hLheight, ?_, ?_, ?_, ?_⟩⟩
      · intro t ht γ hγ
        rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
        · exact hrestrict s hs false γ hγ
        · exact hrestrict s hs true γ hγ
      · intro γ s hs
        have hγβ : γ.val ≤ β := Order.lt_succ_iff.mp (hβα.symm ▸ γ.property)
        rcases hγβ.eq_or_lt with he | he
        · have hsB : s ∈ B := by
            have hh : γ = ⟨β, hβ⟩ := Subtype.ext he
            change s ∈ history ⟨β, hβ⟩
            exact hh ▸ hs
          exact ⟨child s false, Or.inl (mem_image_of_mem _ hsB), child_extends s false⟩
        · obtain ⟨t, ht, hst⟩ := hbGood.extension ⟨γ.val, he⟩ s hs
          exact ⟨child t false, Or.inl (mem_image_of_mem _ ht), extends_trans hst (child_extends t false)⟩
      · intro γ hγα s hs
        have he : γ = β := Order.succ_injective (hγα.trans hβα.symm)
        have hsB : s ∈ B := by subst γ; exact hs
        exact ⟨child s false, Or.inl (mem_image_of_mem _ hsB),
          child s true, Or.inr (mem_image_of_mem _ hsB), children_ne s,
          child_extends s false, child_extends s true⟩
      · intro hl
        exact (hl.succ_ne β hβα).elim

private noncomputable def levelRule (D : OmegaOne → Set OmegaOne) :
    RecursionRule OmegaOne (Set BinaryNode) := by
  classical
  exact fun α history => if h : ∃ L, GoodLevel D α history L then Classical.choose h else ∅

private theorem levels_exist (D : OmegaOne → Set OmegaOne) :
    ∃ levels : OmegaOne → Set BinaryNode,
      ∀ α, GoodLevel D α (fun β => levels β.val) (levels α) := by
  classical
  obtain ⟨levels, heq, _⟩ := recursion_exists_unique (levelRule D)
  refine ⟨levels, ?_⟩
  intro α
  induction α using (wellFounded_lt (α := OmegaOne)).induction with
  | h α ih =>
    have hex := good_level_exists D α (fun β => levels β.val) (fun β => ih β.val β.property)
    have hh := Classical.choose_spec hex
    rw [heq α]
    unfold levelRule
    rw [dite_eq_left hex]
    exact hh

private theorem normal_from_levels (D : OmegaOne → Set OmegaOne)
    (levels : OmegaOne → Set BinaryNode)
    (hgood : ∀ α, GoodLevel D α (fun β => levels β.val) (levels α)) :
    IsNormalBinaryTree (⋃ α, levels α) ∧
      ∀ α, BinaryLevel (⋃ β, levels β) α = levels α := by
  classical
  let S := ⋃ α, levels α
  have hlevels (α : OmegaOne) : BinaryLevel S α = levels α := by
    ext t
    constructor
    · rintro ⟨ht, hh⟩
      obtain ⟨β, hβ⟩ := mem_iUnion.mp ht
      have he : β = α := ((hgood β).height t hβ).symm.trans hh
      exact he ▸ hβ
    · intro ht
      exact ⟨mem_iUnion.mpr ⟨α, ht⟩, (hgood α).height t ht⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hlevels⟩
  · intro t ht β hb
    obtain ⟨α, hα⟩ := mem_iUnion.mp ht
    have hth := (hgood α).height t hα
    have hβα : β ≤ α := hb.trans_eq hth
    rcases hβα.eq_or_lt with he | he
    · have he' : β = t.1 := he.trans hth.symm
      exact (restrict_eq_self t β hb he').symm ▸ ht
    · obtain ⟨_, hm⟩ := (hgood α).restriction t hα β he
      exact mem_iUnion.mpr ⟨β, hm⟩
  · intro α
    rw [hlevels]
    exact ⟨(hgood α).nonempty, (hgood α).countable⟩
  · intro s hs α hα
    have hsm : s ∈ levels s.1 := (hlevels s.1) ▸ And.intro hs rfl
    obtain ⟨t, ht, he⟩ := (hgood α).extension ⟨s.1, hα⟩ s hsm
    exact ⟨t, mem_iUnion.mpr ⟨α, ht⟩, (hgood α).height t ht, he⟩
  · intro s hs
    have hsm : s ∈ levels s.1 := (hlevels s.1) ▸ And.intro hs rfl
    obtain ⟨t₀, ht₀, t₁, ht₁, hne, he₀, he₁⟩ :=
      (hgood (Order.succ s.1)).splitting s.1 rfl s hsm
    exact ⟨t₀, mem_iUnion.mpr ⟨_, ht₀⟩, t₁, mem_iUnion.mpr ⟨_, ht₁⟩, hne,
      (hgood _).height _ ht₀, (hgood _).height _ ht₁, he₀, he₁⟩

private theorem normal_levels_countable (S : Set BinaryNode) (hS : IsNormalBinaryTree S)
    (α : Ordinal.{0}) : (InfiniteTrees.level (InfiniteTrees.functionTree S hS.1) α).Countable := by
  classical
  let T := InfiniteTrees.functionTree S hS.1
  by_cases hα : α < Cardinal.ord (ℵ₁ : Cardinal.{0})
  · let β : OmegaOne := Ordinal.ToType.mk ⟨α, hα⟩
    apply Set.MapsTo.countable_of_injOn (f := Subtype.val)
      (t := BinaryLevel S β) _ Subtype.val_injective.injOn (hS.2.1 β).2
    intro t ht
    refine ⟨t.property, ?_⟩
    apply Ordinal.ToType.mk.symm.injective
    apply Subtype.ext
    have ht' : InfiniteTrees.nodeHeight (InfiniteTrees.functionTree S hS.1) t = α := ht
    exact ((InfiniteTrees.functionTree_nodeHeight S hS.1 t).symm.trans ht').trans
      (position_mk ⟨α, hα⟩).symm
  · have he : InfiniteTrees.level T α = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hh := InfiniteTrees.functionTree_nodeHeight S hS.1 t
      have ht' : InfiniteTrees.nodeHeight T t = α := ht
      have he' : t.val.1.toOrd.val = α := hh.symm.trans ht'
      exact hα (he' ▸ t.val.1.toOrd.property)
    rw [he]
    exact Set.countable_empty

private theorem maximal_antichain_extension (T : InfiniteTrees.Tree.{0})
    (A : Set T) (hA : IsAntichain (· ≤ ·) A) :
    ∃ M, A ⊆ M ∧ IsMaxAntichain (· ≤ ·) M := by
  classical
  have hchains : ∀ C ⊆ {M : Set T | IsAntichain (· ≤ ·) M},
      IsChain (· ⊆ ·) C → C.Nonempty →
        ∃ ub ∈ {M : Set T | IsAntichain (· ≤ ·) M}, ∀ M ∈ C, M ⊆ ub := by
    intro C hC hchain _
    refine ⟨⋃₀ C, ?_, fun M hM => subset_sUnion_of_mem hM⟩
    rintro x ⟨M, hM, hx⟩ y ⟨N, hN, hy⟩ hxy
    rcases hchain.total hM hN with hMN | hNM
    · exact hC hN (hMN hx) hy hxy
    · exact hC hM hx (hNM hy) hxy
  obtain ⟨M, hAM, hm⟩ := zorn_subset_nonempty {M : Set T | IsAntichain (· ≤ ·) M}
    hchains A hA
  exact ⟨M, hAM, hm.1, fun _ hN hMN => Subset.antisymm hMN (hm.2 hN hMN)⟩

private theorem bounded_nodes_countable (T : InfiniteTrees.Tree.{0})
    (hc : ∀ α, (InfiniteTrees.level T α).Countable) (δ : OmegaOne) :
    ({t : T | InfiniteTrees.nodeHeight T t < δ.toOrd.val} : Set T).Countable := by
  let : Countable (Set.Iio δ.toOrd.val) :=
    (Cardinal.countable_Iio_of_lt_omega_one (by simpa using δ.toOrd.property)).to_subtype
  apply (Set.countable_iUnion (fun α : Set.Iio δ.toOrd.val => hc α.val)).mono
  intro t ht
  exact mem_iUnion.mpr ⟨⟨InfiniteTrees.nodeHeight T t, ht⟩, rfl⟩

private theorem restrict_le_restrict (t : BinaryNode) (α β : OmegaOne)
    (ha : α ≤ t.1) (hb : β ≤ t.1) (hab : α ≤ β) :
    InfiniteTrees.Extends (InfiniteTrees.restrictNode t α ha) (InfiniteTrees.restrictNode t β hb) :=
  ⟨hab, by funext i; rfl⟩

private theorem extends_eq_restrict {s t : BinaryNode} (h : InfiniteTrees.Extends s t) :
    s = InfiniteTrees.restrictNode t s.1 h.1 := by
  cases s with
  | mk α f => exact congrArg (Sigma.mk α) h.2

private theorem same_height_predecessors {s r t : BinaryNode}
    (hs : InfiniteTrees.Extends s t) (hr : InfiniteTrees.Extends r t) (he : s.1 = r.1) : s = r := by
  have hres : InfiniteTrees.restrictNode t s.1 hs.1 = InfiniteTrees.restrictNode t r.1 hr.1 := by
    cases s with
    | mk α f =>
      cases r with
      | mk β g => dsimp at he; subst β; rfl
  exact (extends_eq_restrict hs).trans (hres.trans (extends_eq_restrict hr).symm)

private theorem normal_chain_countable (S : Set BinaryNode) (hS : IsNormalBinaryTree S)
    (hA : ∀ A : Set (InfiniteTrees.functionTree S hS.1), IsAntichain (· ≤ ·) A → A.Countable) :
    ∀ C : Set (InfiniteTrees.functionTree S hS.1), IsChain (· ≤ ·) C → C.Countable := by
  classical
  let T := InfiniteTrees.functionTree S hS.1
  intro C hC
  by_contra hunc
  have hcofinal (α : OmegaOne) : ∃ t ∈ C, α < t.val.1 := by
    by_contra hn
    push Not at hn
    have hc := bounded_nodes_countable T (normal_levels_countable S hS) (Order.succ α)
    apply hunc (hc.mono ?_)
    intro t ht
    have hle : t.val.1 ≤ α := hn t ht
    have hh : t.val.1 < Order.succ α := hle.trans_lt (Order.lt_succ α)
    exact (InfiniteTrees.functionTree_nodeHeight S hS.1 t).trans_lt (position_lt.mp hh)
  choose c hc hcHeight using hcofinal
  let b : OmegaOne → T := fun α =>
    ⟨InfiniteTrees.restrictNode (c α).val α (hcHeight α).le,
      hS.1 _ (c α).property α (hcHeight α).le⟩
  have hbheight (α) : (b α).val.1 = α := rfl
  have hbmono (α β : OmegaOne) (hab : α ≤ β) : InfiniteTrees.Extends (b α).val (b β).val := by
    change InfiniteTrees.Extends (InfiniteTrees.restrictNode (c α).val α (hcHeight α).le)
      (InfiniteTrees.restrictNode (c β).val β (hcHeight β).le)
    rcases hC.total (hc α) (hc β) with hαβ | hβα
    · have he := restrict_of_extends hαβ α (hcHeight α).le
      exact he.symm ▸ restrict_le_restrict (c β).val α β
        ((hcHeight α).le.trans hαβ.1) (hcHeight β).le hab
    · have he := restrict_of_extends hβα β (hcHeight β).le
      exact he.symm ▸ restrict_le_restrict (c α).val α β
        (hcHeight α).le ((hcHeight β).le.trans hβα.1) hab
  have hoff (α : OmegaOne) : ∃ v ∈ S, v.1 = Order.succ α ∧
      InfiniteTrees.Extends (b α).val v ∧ v ≠ (b (Order.succ α)).val := by
    obtain ⟨v₀, hv₀, v₁, hv₁, hne, hh₀, hh₁, he₀, he₁⟩ := hS.2.2.2 (b α).val (b α).property
    by_cases he : v₀ = (b (Order.succ α)).val
    · exact ⟨v₁, hv₁, hh₁, he₁, fun h => hne (he.trans h.symm)⟩
    · exact ⟨v₀, hv₀, hh₀, he₀, he⟩
  choose off hoS hoHeight hoExt hoNe using hoff
  have hoffAnti (α β : OmegaOne) (hne : α ≠ β) : ¬ InfiniteTrees.Extends (off α) (off β) := by
    intro he
    rcases lt_or_gt_of_ne hne with h | h
    · have hbb := hbmono (Order.succ α) β (Order.succ_le_of_lt h)
      have hbt := extends_trans hbb (hoExt β)
      have heq := same_height_predecessors he hbt ((hoHeight α).trans (hbheight _).symm)
      exact hoNe α heq
    · have hle : Order.succ α ≤ Order.succ β := (hoHeight α).symm.trans_le he.1 |>.trans_eq (hoHeight β)
      exact (Order.succ_strictMono h).not_ge hle
  let v : OmegaOne → T := fun α => ⟨off α, hoS α⟩
  have hvi : Function.Injective v := by
    intro α β he
    apply Order.succ_injective
    exact (hoHeight α).symm.trans ((congrArg (fun t : T => t.val.1) he).trans (hoHeight β))
  have hrange : IsAntichain (· ≤ ·) (range v) := by
    rintro _ ⟨α, rfl⟩ _ ⟨β, rfl⟩ hne he
    exact hoffAnti α β (fun h => hne (congrArg v h)) he
  have hcount := hA (range v) hrange
  let : Countable (range v) := hcount.to_subtype
  let e : OmegaOne → range v := fun α => ⟨v α, mem_range_self α⟩
  have hei : Function.Injective e := fun α β he => hvi (congrArg Subtype.val he)
  have hcOmega : Countable OmegaOne := hei.countable
  have hcard : Cardinal.mk OmegaOne ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr hcOmega
  have he : Cardinal.mk OmegaOne = ℵ₁ := by simp [OmegaOne, Clubs.Carrier]
  exact Cardinal.aleph0_lt_aleph_one.not_ge (he ▸ hcard)

theorem diamond_suslin_binary (h : Diamond) :
    ∃ S : Set BinaryNode, ∃ hS : IsNormalBinaryTree S,
      IsSuslinTree (InfiniteTrees.functionTree S hS.1) := by
  classical
  obtain ⟨D, hD⟩ := h
  obtain ⟨levels, hgood⟩ := levels_exist D
  let S := ⋃ α, levels α
  obtain ⟨hS, hlevels⟩ := normal_from_levels D levels hgood
  let T := InfiniteTrees.functionTree S hS.1
  have hheight : InfiniteTrees.treeHeight T = Cardinal.ord (ℵ₁ : Cardinal.{0}) :=
    (binary_tree_heights S hS).1
  have hcount (α : Ordinal.{0}) : (InfiniteTrees.level T α).Countable :=
    normal_levels_countable S hS α
  obtain ⟨q, hq, hqcode⟩ := canonical_labels S (fun α => (hS.2.1 α).2)
  have hcof : ℵ₀ < Order.cof OmegaOne := by simp [OmegaOne, Clubs.Carrier]
  have hmaxcount (A : Set T) (hA : IsMaxAntichain (· ≤ ·) A) : A.Countable := by
    obtain ⟨a, ha, _, _, hreflection⟩ := antichain_reflection T hheight hcount A hA
    let X : Set OmegaOne := q '' A
    obtain ⟨δ, hguess, hδcode, hδreflect⟩ := hD.2 X
      ((coding_club S q hq).inter hcof.ne' hreflection)
    have hδ : Order.IsSuccLimit δ := hδcode.1
    let history : Set.Iio δ → Set BinaryNode := fun β => levels β.val
    obtain ⟨hold, hOldLevels⟩ := old_normal D δ history (fun β => hgood β.val)
    have hOldS : oldNodes δ history ⊆ S := by
      intro t ht
      obtain ⟨β, hβ⟩ := mem_iUnion.mp ht
      exact mem_iUnion.mpr ⟨β.val, hβ⟩
    have hSbelow (t : T) (ht : t.val.1 < δ) : t.val ∈ oldNodes δ history := by
      have hl : t.val ∈ levels t.val.1 := (hlevels t.val.1) ▸ And.intro t.property rfl
      exact mem_iUnion.mpr ⟨⟨t.val.1, ht⟩, hl⟩
    have hlabel (t : BinaryNode) (ht : t ∈ oldNodes δ history) :
        oldLabel δ history t = (q ⟨t, hOldS ht⟩).toOrd.val := by
      have hh := hold.2.1 t ht
      have hc := hqcode ⟨t, hOldS ht⟩
      rw [hlevels] at hc
      unfold oldLabel
      rw [dite_eq_left hh]
      exact hc.symm
    let G := guessedAntichain D δ history
    have hG (t : BinaryNode) (ht : t ∈ oldNodes δ history) :
        t ∈ G ↔ (⟨t, hOldS ht⟩ : T) ∈ A := by
      constructor
      · rintro ⟨_, i, hi, hlabeli⟩
        have hiX : i ∈ X := (hguess ▸ hi).1
        obtain ⟨b, hb, hbi⟩ := hiX
        have hiq : i = q ⟨t, hOldS ht⟩ :=
          Ordinal.ToType.mk.symm.injective (Subtype.ext (hlabeli.trans (hlabel t ht)))
        have he : b = ⟨t, hOldS ht⟩ := q.injective (hbi.trans hiq)
        exact he ▸ hb
      · intro htA
        refine ⟨ht, q ⟨t, hOldS ht⟩, ?_, (hlabel t ht).symm⟩
        rw [hguess]
        refine ⟨mem_image_of_mem q htA, ?_⟩
        exact (hδcode.2 ⟨t, hOldS ht⟩).mpr (hold.2.1 t ht)
    have hGmax : IsMaxAntichainIn (oldNodes δ history) G := by
      refine ⟨fun _ ht => ht.1, ?_, ?_⟩
      · intro s hs t ht hne hst
        have hsA := (hG s hs.1).mp hs
        have htA := (hG t ht.1).mp ht
        exact hA.1 hsA htA (fun he => hne (congrArg Subtype.val he)) hst
      · intro s hs
        let t : T := ⟨s, hOldS hs⟩
        have htHeight : InfiniteTrees.nodeHeight T t < δ.toOrd.val := by
          rw [InfiniteTrees.functionTree_nodeHeight]
          exact position_lt.mp (hold.2.1 s hs)
        have haHeight := hδreflect.2 t htHeight
        have haBelow : (a t).val.1 < δ := by
          apply position_lt.mpr
          exact (InfiniteTrees.functionTree_nodeHeight S hS.1 (a t)).symm ▸ haHeight
        have haOld := hSbelow (a t) haBelow
        refine ⟨(a t).val, (hG _ haOld).mpr (ha t).1, ?_⟩
        exact (ha t).2.symm
    have hsealed := (hgood δ).sealing hδ hGmax
    have hbounded : A ⊆ {t : T | InfiniteTrees.nodeHeight T t < δ.toOrd.val} := by
      intro t htA
      by_contra hn
      change ¬ InfiniteTrees.nodeHeight T t < δ.toOrd.val at hn
      have hδt : δ ≤ t.val.1 := le_of_not_gt (by
        intro hh
        exact hn ((InfiniteTrees.functionTree_nodeHeight S hS.1 t).trans_lt (position_lt.mp hh)))
      let r : BinaryNode := InfiniteTrees.restrictNode t.val δ hδt
      have hrS : r ∈ S := hS.1 t.val t.property δ hδt
      have hrLevel : r ∈ levels δ := (hlevels δ) ▸ And.intro hrS rfl
      obtain ⟨b, hbG, hbr⟩ := hsealed r hrLevel
      let b' : T := ⟨b, hOldS hbG.1⟩
      have hbA : b' ∈ A := (hG b hbG.1).mp hbG
      have hrt : InfiniteTrees.Extends r t.val := ⟨hδt, rfl⟩
      have hbt : b' ≤ t := extends_trans hbr hrt
      have hbHeight : InfiniteTrees.nodeHeight T b' < δ.toOrd.val := by
        rw [InfiniteTrees.functionTree_nodeHeight]
        exact position_lt.mp (hold.2.1 b hbG.1)
      have hne : b' ≠ t := fun he => hn (he ▸ hbHeight)
      exact hA.1 hbA htA hne hbt
    exact (bounded_nodes_countable T hcount δ).mono hbounded
  have hantichain (A : Set T) (hA : IsAntichain (· ≤ ·) A) : A.Countable := by
    obtain ⟨M, hAM, hM⟩ := maximal_antichain_extension T A hA
    exact (hmaxcount M hM).mono hAM
  refine ⟨S, hS, hheight, ?_, hantichain⟩
  exact normal_chain_countable S hS hantichain


theorem diamond_suslin (h : Diamond) :
    ∃ T : InfiniteTrees.Tree.{0}, IsSuslinTree T := by
  obtain ⟨S, hS, hs⟩ := diamond_suslin_binary h
  exact ⟨InfiniteTrees.functionTree S hS.1, hs⟩

theorem no_subset_enumeration (f : OmegaOne → Set OmegaOne) :
    ¬ Function.Surjective f := Function.cantor_surjective f

end Lemmatheca.SetTheory.DiamondSuslin
