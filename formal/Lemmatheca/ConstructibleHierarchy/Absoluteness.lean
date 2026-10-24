import Lemmatheca.ConstructibleHierarchy.Levels

/-! The bound results below retain the actual subdomain, the same finite formula
and the exact parameter maps. They are not an encoding of the theorem that an
arbitrary transitive ZF model internally contains all codes, tuples, satisfaction
sets or the definability collection. Those full ZF-model claims remain unbound. -/
namespace Lemmatheca.SetTheory.ConstructibleHierarchy
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
universe u
noncomputable section

abbrev NestedDomain (N M : ZFSet.{u}) := {x : N // x.val ∈ M}
def nestedMembership (N M : ZFSet.{u}) (x y : NestedDomain N M) : Prop :=
  x.val.val ∈ y.val.val

def nestedDomainEquiv (N M : ZFSet.{u}) (hN : N.IsTransitive) (hM : M ∈ N) :
    NestedDomain N M ≃ M where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,hN M hM x.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nestedDomainEquiv_values (N M : ZFSet.{u}) (hN : N.IsTransitive)
    (hM : M ∈ N) :
    (∀ x, (nestedDomainEquiv N M hN hM x).val = x.val.val) ∧
    (∀ x, ((nestedDomainEquiv N M hN hM).symm x).val.val = x.val) := by
  exact ⟨fun _ => rfl,fun _ => rfl⟩

theorem nested_satisfaction (N M : ZFSet.{u}) (hN : N.IsTransitive) (hM : M ∈ N)
    {n} (p : membershipLanguage.BoundedFormula Empty n)
    (a : Fin n → NestedDomain N M) :
    nativeSatisfies (nestedMembership N M) p a ↔
      setSatisfies M p (fun i => nestedDomainEquiv N M hN hM (a i)) := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure
    (NestedDomain N M) (nestedMembership N M)
  let := actualMembershipStructure M
  let e : NestedDomain N M ≃[membershipLanguage] M :=
    { toEquiv := nestedDomainEquiv N M hN hM
      map_fun' := by intro n f; exact Empty.elim f
      map_rel' := by intro n r xs; cases r; rfl }
  have he := (StrongHomClass.realize_boundedFormula e p (v := Empty.elim) (xs := a)).symm
  have hempty : e ∘ (Empty.elim : Empty → NestedDomain N M) = (Empty.elim : Empty → M) :=
    Subsingleton.elim _ _
  rw [hempty] at he
  exact he

abbrev InsideDefinitionCode (N M : ZFSet.{u}) :=
  Σ n : ℕ, membershipLanguage.BoundedFormula Empty (n+1) × (Fin n → NestedDomain N M)

def codeIntoNested (N M : ZFSet.{u}) (hN : N.IsTransitive) (hM : M ∈ N)
    (c : DefinitionCode M) : InsideDefinitionCode N M :=
  ⟨c.1,c.2.1,fun i => (nestedDomainEquiv N M hN hM).symm (c.2.2 i)⟩

def codeOutOfNested (N M : ZFSet.{u}) (hN : N.IsTransitive) (hM : M ∈ N)
    (c : InsideDefinitionCode N M) : DefinitionCode M :=
  ⟨c.1,c.2.1,fun i => nestedDomainEquiv N M hN hM (c.2.2 i)⟩

theorem nested_code_bijection (N M : ZFSet.{u}) (hN : N.IsTransitive) (hM : M ∈ N) :
    Function.LeftInverse (codeOutOfNested N M hN hM) (codeIntoNested N M hN hM) ∧
    Function.RightInverse (codeOutOfNested N M hN hM) (codeIntoNested N M hN hM) := by
  constructor
  · rintro ⟨n,p,a⟩
    rfl
  · rintro ⟨n,p,a⟩
    rfl

def insideDefinedSubset (N M : ZFSet.{u}) (c : InsideDefinitionCode N M) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ b : NestedDomain N M, b.val.val = y ∧
    nativeSatisfies (nestedMembership N M) c.2.1 (Fin.snoc c.2.2 b)) M

def insideDef (N M : ZFSet.{u}) : ZFSet.{u} := ZFSet.range (insideDefinedSubset N M)

theorem specified_inside_subset (N M : ZFSet.{u}) (hN : N.IsTransitive) (hM : M ∈ N)
    (c : DefinitionCode M) :
    insideDefinedSubset N M (codeIntoNested N M hN hM c) = definedSubset M c := by
  let e := nestedDomainEquiv N M hN hM
  have htuple (b : NestedDomain N M) :
      (fun i => e ((Fin.snoc (α := fun _ : Fin (c.1+1) => NestedDomain N M)
        (fun i => e.symm (c.2.2 i)) b) i)) = Fin.snoc c.2.2 (e b) := by
    change e ∘ Fin.snoc (fun i => e.symm (c.2.2 i)) b = _
    rw [Fin.comp_snoc]
    congr 1
  ext y
  simp only [insideDefinedSubset,definedSubset,ZFSet.mem_sep,codeIntoNested]
  constructor
  · rintro ⟨hy,b,hby,htruth⟩
    refine ⟨hy,hy,?_⟩
    have ht := (nested_satisfaction N M hN hM c.2.1
      (Fin.snoc (fun i => e.symm (c.2.2 i)) b)).mp htruth
    have hbe : e b = ⟨y,hy⟩ := Subtype.ext hby
    change setSatisfies M c.2.1 (fun i => e (Fin.snoc (α := fun _ : Fin (c.1+1) => NestedDomain N M) (fun i => e.symm (c.2.2 i)) b i)) at ht
    rw [htuple,hbe] at ht
    exact ht
  · rintro ⟨hy,_,htruth⟩
    let b := e.symm ⟨y,hy⟩
    refine ⟨hy,b,rfl,?_⟩
    apply (nested_satisfaction N M hN hM c.2.1
      (Fin.snoc (fun i => e.symm (c.2.2 i)) b)).mpr
    change setSatisfies M c.2.1 (fun i => e (Fin.snoc (α := fun _ : Fin (c.1+1) => NestedDomain N M) (fun i => e.symm (c.2.2 i)) b i))
    rw [htuple,e.apply_symm_apply]
    exact htruth

theorem inside_Def_agreement (N M : ZFSet.{u}) (hN : N.IsTransitive) (hM : M ∈ N) :
    insideDef N M = Def M := by
  ext X
  rw [insideDef,ZFSet.mem_range,Def_members]
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨codeOutOfNested N M hN hM c,?_⟩
    have he := specified_inside_subset N M hN hM (codeOutOfNested N M hN hM c)
    rw [(nested_code_bijection N M hN hM).2 c] at he
    exact he.symm
  · rintro ⟨c,hc⟩
    exact ⟨codeIntoNested N M hN hM c,(specified_inside_subset N M hN hM c).trans hc⟩

/-- A supplied history over actual ordinal indices. This does not assert that
an arbitrary ZF model contains that history or correctly encodes recursion. -/
def AgreesThrough (F : Ordinal.{u} → ZFSet.{u}) (a : Ordinal.{u}) : Prop :=
  ∀ b ≤ a, F b = level b

theorem supplied_history_agreement (F : Ordinal.{u} → ZFSet.{u}) (a : Ordinal.{u})
    (h0 : F 0 = ∅)
    (hs : ∀ b, b+1 ≤ a → F (b+1) = Def (F b))
    (hl : ∀ l, l ≤ a → Order.IsSuccLimit l →
      F l = ZFSet.iUnion (fun b : Set.Iio l => F b.val)) :
    AgreesThrough F a := by
  intro b hb
  induction b using Ordinal.limitRecOn with
  | zero => exact h0.trans level_zero.symm
  | add_one b ih =>
    rw [hs b hb,level_successor,ih (le_trans (le_add_right (le_refl _)) hb)]
  | limit l hlim ih =>
    rw [hl l hb hlim,level_limit l hlim]
    congr 1
    funext b
    exact ih b.val b.property (b.property.le.trans hb)

theorem omega_Def_proper :
    Def (Ordinal.toZFSet (Ordinal.omega0 : Ordinal.{u})) ⊂
      ZFSet.powerset (Ordinal.toZFSet (Ordinal.omega0 : Ordinal.{u})) := by
  let f : ℕ → (Ordinal.omega0 : Ordinal.{u}).toZFSet := fun n =>
    ⟨(n : Ordinal.{u}).toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr (Ordinal.natCast_lt_omega0 n)⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨b,hb,hx⟩ := Ordinal.mem_toZFSet_iff.mp x.property
    obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp hb
    refine ⟨n,Subtype.ext ?_⟩
    simpa only [f,hn] using hx
  let : Countable (Ordinal.omega0 : Ordinal.{u}).toZFSet := hf.countable
  let : Infinite (Ordinal.omega0 : Ordinal.{u}).toZFSet := Infinite.of_injective f (by
    intro n m h
    exact_mod_cast Ordinal.toZFSet_injective (congrArg Subtype.val h))
  exact (countable_infinite_Def _).2.2.2

end
end Lemmatheca.SetTheory.ConstructibleHierarchy
