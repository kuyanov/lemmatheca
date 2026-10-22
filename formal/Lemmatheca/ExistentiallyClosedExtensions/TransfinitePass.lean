import Lemmatheca.ExistentiallyClosedExtensions.PassRecursion
import Mathlib.Order.SuccPred.InitialSeg
import Mathlib.Order.Interval.Set.SuccOrder

/-! The actual bounded ordinal request pass, with compatible maps and limit coverage. -/
namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
open FirstOrder FirstOrder.Language Cardinal CategoryTheory
open Lemmatheca.ModelTheory
open ModelCompleteness InductiveTheories
universe u v w
variable {L : Language.{u, v}}

def firstIndex (o : Ordinal.{w}) : Set.Iic o :=
  ⟨0, by change (0 : Ordinal) ≤ o; exact zero_le⟩

def lastIndex (o : Ordinal.{w}) : Set.Iic o :=
  ⟨o, by change o ≤ o; exact le_rfl⟩

/-- A set-sized well-ordered pass, with ordinary transition embeddings and genuine limit coverage. -/
structure TransfinitePass (T : L.Theory) (κ : Cardinal.{max u v w})
    (A : Theory.ModelType.{u, v, max u v w} T) where
  length : Ordinal.{max u v w}
  length_bound : length.card ≤ κ
  stage : Set.Iic length → CodedModel T κ
  transition : ∀ i j, i ≤ j → (stage i).asModel ↪[L] (stage j).asModel
  system : DirectedSystem (fun i => (stage i).asModel) (fun i j h => transition i j h)
  initial : A ≃[L] (stage (firstIndex length)).asModel
  request : Set.Iio length → Request L A
  enumerates : Function.Surjective request
  handled : ∀ i : Set.Iio length,
    let before : Set.Iic length := ⟨i.val, by change i.val ≤ length; exact le_of_lt i.property⟩
    let after : Set.Iic length := ⟨i.val + 1, (by
      change i.val + 1 ≤ length
      exact Order.add_one_le_iff.mpr i.property)⟩
    let baseBefore := (transition (firstIndex length) before (by change (0 : Ordinal) ≤ i.val; exact zero_le)).comp initial.toEmbedding
    let baseAfter := (transition (firstIndex length) after (by change (0 : Ordinal) ≤ i.val + 1; exact zero_le)).comp initial.toEmbedding
    (request i).Possible T baseBefore → (request i).Realized baseAfter
  limit_cover : ∀ (β : Set.Iic length), Order.IsSuccLimit β.val →
    ∀ b : (stage β).asModel,
      ∃ (α : Set.Iic length) (hα : α < β) (a : (stage α).asModel), transition α β hα.le a = b

private theorem request_card_bound (κ : Cardinal.{max u v w}) (hω : ℵ₀ ≤ κ)
    (hL : Cardinal.lift (#L.Symbols) ≤ κ)
    (A : Type (max u v w)) (hA : #A ≤ κ) : #(Request L A) ≤ κ := by
  apply (requests_card_le (L := L) A).trans
  dsimp [sizeBound]
  rw [Cardinal.lift_umax.{max u v, w}, Cardinal.lift_id'.{max u v, w}]
  exact max_le hω (max_le hL hA)

private theorem request_schedule (κ : Cardinal.{max u v w}) (hω : ℵ₀ ≤ κ)
    (hL : Cardinal.lift (#L.Symbols) ≤ κ)
    (A : Type (max u v w)) (hA : #A ≤ κ) :
    ∃ s : κ.ord.ToType → Request L A, Function.Surjective s := by
  classical
  let : Nonempty (Request L A) :=
    ⟨⟨0, ⊤, FirstOrder.Language.BoundedFormula.IsExistential.of_isQF
      FirstOrder.Language.BoundedFormula.IsQF.top, Fin.elim0⟩⟩
  have h : #(Request L A) ≤ #κ.ord.ToType := by
    simpa using request_card_bound κ hω hL A hA
  obtain ⟨f⟩ := (Cardinal.le_def _ _).mp h
  exact ⟨Function.invFun f, Function.invFun_surjective f.injective⟩

private theorem ordinal_schedule_index_card (κ : Cardinal.{w}) (hω : ℵ₀ ≤ κ) :
    #((κ.ord + 1).ToType) ≤ κ := by
  simp only [Cardinal.mk_toType, Ordinal.card_add_one, Cardinal.card_ord]
  exact le_of_eq (Cardinal.add_one_eq hω)

private theorem request_closed_schedule (κ : Cardinal.{max u v w}) (hω : ℵ₀ ≤ κ)
    (hL : Cardinal.lift (#L.Symbols) ≤ κ)
    (A : Type (max u v w)) (hA : #A ≤ κ)
    {J : Type (max u v w)} [Preorder J] (e : Set.Iic κ.ord ≃o J) :
    ∃ schedule : J → Request L A, Function.Surjective
      (fun i : Set.Iio κ.ord => schedule (e ⟨i.val, show i.val ≤ κ.ord from i.property.le⟩)) := by
  classical
  obtain ⟨s, hs⟩ := request_schedule κ hω hL A hA
  let r : Set.Iio κ.ord → Request L A := s ∘ Ordinal.ToType.mk
  have hr : Function.Surjective r := hs.comp Ordinal.ToType.mk.surjective
  let g : Set.Iio κ.ord → J := fun i => e ⟨i.val, show i.val ≤ κ.ord from i.property.le⟩
  have hg : Function.Injective g := by
    intro a b h
    exact Subtype.ext (congrArg (fun z : Set.Iic κ.ord => z.val) (e.injective h))
  let d : Request L A := ⟨0, ⊤, FirstOrder.Language.BoundedFormula.IsExistential.of_isQF
    FirstOrder.Language.BoundedFormula.IsQF.top, Fin.elim0⟩
  refine ⟨Function.extend g r (fun _ => d), ?_⟩
  intro a
  obtain ⟨i, hi⟩ := hr a
  exact ⟨i, (hg.extend_apply r (fun _ => d) i).trans hi⟩


private noncomputable def ordinalIndexIso (μ : Ordinal.{w}) : Set.Iic μ ≃o (μ + 1).ToType :=
  (show Set.Iic μ ≃o Set.Iio (μ + 1) from
    { toFun := fun a => ⟨a.val, by change a.val < μ + 1; exact Order.lt_add_one_iff.mpr a.property⟩
      invFun := fun a => ⟨a.val, (show a.val ≤ μ from Order.lt_add_one_iff.mp a.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }).trans Ordinal.ToType.mk


private noncomputable def ordinalIicInitial (μ : Ordinal.{w}) :
    Set.Iic μ ≤i Ordinal.{w} where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl
  mem_range_of_rel' a b h := ⟨⟨b, h.le.trans a.property⟩, rfl⟩


/-- Extract the actual ordinal-indexed pass from a completed small-index prefix. -/
private theorem ordinalPass_of_prefix
    (T : L.Theory) (κ : Cardinal.{max u v w})
    (A : Theory.ModelType.{u, v, max u v w} T)
    (μ : Ordinal.{max u v w}) (hμ : μ.card ≤ κ)
    {J : Type (max u v w)} [LinearOrder J] [SuccOrder J] [OrderBot J] [OrderTop J]
    (e : Set.Iic μ ≃o J) (schedule : J → Request L A)
    (hs : Function.Surjective (fun i : Set.Iio μ =>
      schedule (e ⟨i.val, show i.val ≤ μ from i.property.le⟩)))
    (B₀ : CodedModel T κ) (e₀ : A ≃[L] B₀.asModel)
    (p : PassPrefix.Data T κ A schedule B₀ e₀ (⊤ : J)) :
    Nonempty (TransfinitePass T κ A) := by
  classical
  let r : Set.Iic μ →o Set.Iic (⊤ : J) :=
    ⟨fun i => ⟨e i, le_top⟩, fun _ _ h => e.monotone h⟩
  have hz : r (firstIndex μ) = ⟨⊥, bot_le⟩ := Subtype.ext e.map_bot
  have hi : p.F.obj (r (firstIndex μ)) = B₀ := (congrArg p.F.obj hz).trans p.starts
  refine ⟨{
    length := μ
    length_bound := hμ
    stage := fun i => p.F.obj (r i)
    transition := fun i j h => codedHom (p.F.map (homOfLE (r.monotone h)))
    system := ?_
    initial := hi.symm ▸ e₀
    request := fun i => schedule (e ⟨i.val, show i.val ≤ μ from i.property.le⟩)
    enumerates := hs
    handled := ?_
    limit_cover := ?_ }⟩
  · constructor
    · intro i a
      change codedHom (p.F.map (𝟙 (r i))) a = a
      rw [p.F.map_id]
      rfl
    · intro i j k hij hjk a
      change codedHom (p.F.map (homOfLE (r.monotone hij)) ≫
        p.F.map (homOfLE (r.monotone hjk))) a = _
      rw [← p.F.map_comp]
      rfl
  · intro i
    let a : Set.Iic μ := ⟨i.val, show i.val ≤ μ from i.property.le⟩
    let b : Set.Iic μ := ⟨i.val + 1, by
      change i.val + 1 ≤ μ
      exact Order.add_one_le_iff.mpr i.property⟩
    have hn : ¬ IsMax a := not_isMax_iff.mpr ⟨⟨μ, show μ ≤ μ from le_rfl⟩, i.property⟩
    have he : e b = Order.succ (e a) := by
      have hh := e.map_succ a
      simpa only [Set.Iic.succ_eq_of_not_isMax hn, Order.succ_eq_add_one] using hh
    have hlt : e a < (⊤ : J) := by
      have hh := e.strictMono (show a < (lastIndex μ) from i.property)
      simpa only [show e (lastIndex μ) = ⊤ from e.map_top] using hh
    have hy : r b = (⟨Order.succ (e a), le_top⟩ : Set.Iic (⊤ : J)) :=
      Subtype.ext he
    have aux (z x y : Set.Iic (⊤ : J))
        (hz' : z = ⟨⊥, bot_le⟩)
        (hx : x = ⟨e a, le_top⟩)
        (hy' : y = ⟨Order.succ (e a), le_top⟩)
        (hzx : z ≤ x) (hzy : z ≤ y) :
        (schedule (e a)).Possible T
          ((codedHom (p.F.map (homOfLE hzx))).comp
            (((congrArg p.F.obj hz').trans p.starts).symm ▸ e₀).toEmbedding) →
        (schedule (e a)).Realized
          ((codedHom (p.F.map (homOfLE hzy))).comp
            (((congrArg p.F.obj hz').trans p.starts).symm ▸ e₀).toEmbedding) := by
      subst z
      subst x
      subst y
      exact p.handled (e a) hlt
    exact aux _ _ _ hz rfl hy _ _

  · intro β hβ b
    have hb : Order.IsSuccLimit β :=
      (ordinalIicInitial μ).isSuccLimit_apply_iff.mp hβ
    have heb : Order.IsSuccLimit (e β) := e.toRelIsoLT.toInitialSeg.map_isSuccLimit hb
    obtain ⟨k, hk, a, ha⟩ := p.limit_cover (r β) heb b
    have hα : e.symm k.val < β := by
      have hx := e.symm.strictMono (show k.val < e β from hk)
      simpa only [OrderIso.symm_apply_apply] using hx
    refine ⟨e.symm k.val, hα, ?_⟩
    have hr : r (e.symm k.val) = k := Subtype.ext (e.apply_symm_apply k.val)
    change ∃ a : (p.F.obj (r (e.symm k.val))).asModel,
      codedHom (p.F.map (homOfLE (r.monotone hα.le))) a = b
    have aux (t : Set.Iic (⊤ : J)) (ht : t ≤ r β) (he : t = k) :
        ∃ a : (p.F.obj t).asModel, codedHom (p.F.map (homOfLE ht)) a = b := by
      subst t
      exact ⟨a, ha⟩
    exact aux _ _ hr

/-- Every stage is a genuine coded model, and no parameters from later stages enter its schedule. -/
theorem exists_transfinite_pass (T : L.Theory) (hT : IsInductive.{u, v, w} T)
    (κ : Cardinal.{max u v w}) (hω : Cardinal.aleph0 ≤ κ)
    (hL : Cardinal.lift (#L.Symbols) ≤ κ)
    (A : Theory.ModelType.{u, v, max u v w} T) (hA : #A ≤ κ) :
    Nonempty (TransfinitePass T κ A) := by
  classical
  let μ := κ.ord
  let J := (μ + 1).ToType
  let : OrderTop J := by
    change OrderTop (Order.succ μ).ToType
    infer_instance
  let : OrderBot J := WellFoundedLT.toOrderBot J
  let e : Set.Iic μ ≃o J := ordinalIndexIso μ
  obtain ⟨schedule, hs⟩ := request_closed_schedule κ hω hL A hA e
  obtain ⟨B₀, ⟨e₀⟩⟩ := code_model T κ A hA
  obtain ⟨p⟩ := PassPrefix.exists_prefix (A := A) (schedule := schedule) (B₀ := B₀)
    (e₀ := e₀) hT hω hL (ordinal_schedule_index_card κ hω) (⊤ : J)
  exact ordinalPass_of_prefix T κ A μ (by simp [μ]) e schedule hs B₀ e₀ p

end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
