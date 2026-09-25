/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GromovWitten.AlgebraicGeometry.Stacks.StackProducts
import GromovWitten.AlgebraicGeometry.Stacks.StackProductProjections

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

/-! # From isomorphism schemes to the constructed stack diagonal

An isomorphism-scheme presentation yields a complete scheme presentation of the actual
stack diagonal. The first component of a product comparison forces the source-object
isomorphism, while the ratio of the second component to the first determines the unique
scheme map. This retains the classification equation and both uniqueness conditions.

The resulting theorems transfer representability and properties of isomorphism schemes
to the diagonal. The unramifiedness corollary still assumes the chart-isomorphism property;
no implication from an étale atlas alone is asserted here.
-/

noncomputable def selfProdObj {X : FppfStack.{u}} {T : Scheme.{u}}
    (x y : StackFiber X T) : StackFiber (stackSelfProduct X).pullback T := by
  exact stackProdObj x y

noncomputable def diagonalComparisonFst
    {X : FppfStack.{u}} {T S : Scheme.{u}}
    {x y : StackFiber X T} {z : StackFiber X S} (toBase : S ⟶ T)
    (c : ((stackDiagonal X).appFunctor S).obj
      z ≅
      (stackPullback (stackSelfProduct X).pullback toBase).obj (selfProdObj x y)) :
    z ≅ (stackPullback X toBase).obj x := by
  exact Iso.mk c.hom.fst c.inv.fst
    (by
      have h := congrArg CategoricalPullback.Hom.fst c.hom_inv_id
      change c.hom.fst ≫ c.inv.fst = 𝟙 _ at h
      exact h)
    (by
      have h := congrArg CategoricalPullback.Hom.fst c.inv_hom_id
      change c.inv.fst ≫ c.hom.fst = 𝟙 _ at h
      exact h)

noncomputable def diagonalComparisonSnd
    {X : FppfStack.{u}} {T S : Scheme.{u}}
    {x y : StackFiber X T} {z : StackFiber X S} (toBase : S ⟶ T)
    (c : ((stackDiagonal X).appFunctor S).obj
      z ≅
      (stackPullback (stackSelfProduct X).pullback toBase).obj (selfProdObj x y)) :
    z ≅ (stackPullback X toBase).obj y := by
  exact Iso.mk c.hom.snd c.inv.snd
    (by
      have h := congrArg CategoricalPullback.Hom.snd c.hom_inv_id
      change c.hom.snd ≫ c.inv.snd = 𝟙 _ at h
      exact h)
    (by
      have h := congrArg CategoricalPullback.Hom.snd c.inv_hom_id
      change c.inv.snd ≫ c.hom.snd = 𝟙 _ at h
      exact h)

noncomputable def diagonalComparisonIso
    {X : FppfStack.{u}} {T S : Scheme.{u}}
    {x y : StackFiber X T} {z : StackFiber X S} (toBase : S ⟶ T)
    (c : ((stackDiagonal X).appFunctor S).obj
      z ≅
      (stackPullback (stackSelfProduct X).pullback toBase).obj (selfProdObj x y)) :
    (stackPullback X toBase).obj x ≅ (stackPullback X toBase).obj y :=
  (diagonalComparisonFst toBase c).symm.trans (diagonalComparisonSnd toBase c)

/-! A product comparison attached to a diagonal presentation.  This is kept as a separate
definition because the codomain of the constructed diagonal is the canonical self-product,
whereas `stackProdObj` is named through the binary-product presentation. -/

noncomputable def diagonalUniversalComparison
    {X : FppfStack.{u}} {T U : Scheme.{u}}
    {x y : StackFiber X T} (map : U ⟶ T)
    (e : (stackPullback X map).obj x ≅ (stackPullback X map).obj y) :
    ((stackDiagonal X).appFunctor U).obj ((stackPullback X map).obj x) ≅
      (stackPullback (stackSelfProduct X).pullback map).obj (selfProdObj x y) := by
  exact (stackProdObjIso (Iso.refl _) e).trans
    (stackPullback_stackProdObj map x y)

noncomputable def diagonalLiftObjectIso
    {X : FppfStack.{u}} {T S : Scheme.{u}}
    {x y : StackFiber X T} {z : StackFiber X S}
    {U : Scheme.{u}} {map : U ⟶ T} {l : S ⟶ U}
    (toBase : S ⟶ T)
    (c : ((stackDiagonal X).appFunctor S).obj z ≅
      (stackPullback (stackSelfProduct X).pullback toBase).obj
        (selfProdObj x y))
    (map_eq : l ≫ map = toBase) :
    z ≅ (stackPullback X l).obj ((stackPullback X map).obj x) :=
  (diagonalComparisonFst toBase c).trans
    ((stackPullbackObjIsoOfEq X map_eq x).symm.trans
      (stackPullbackCompIso X l map x).symm)

set_option backward.isDefEq.respectTransparency false in
theorem diagonalComparison_classifies
    {X : FppfStack.{u}} {T S : Scheme.{u}}
    {x y : StackFiber X T}
    (D : DiagonalPresentation X T x y)
    {z : StackFiber X S} (toBase : S ⟶ T)
    (c : ((stackDiagonal X).appFunctor S).obj z ≅
      (stackPullback (stackSelfProduct X).pullback toBase).obj
        (selfProdObj x y)) :
    StackMorphismClassifies (stackDiagonal X) D.map
      ((stackPullback X D.map).obj x) (selfProdObj x y)
      (diagonalUniversalComparison D.map D.universalIso) toBase z c
      (D.lift toBase (diagonalComparisonIso toBase c))
      (diagonalLiftObjectIso toBase c (D.lift_map toBase
        (diagonalComparisonIso toBase c))) := by
  obtain ⟨map_eq, hcomp⟩ := D.lift_compatible toBase
    (diagonalComparisonIso toBase c)
  refine ⟨map_eq, ?_⟩
  apply Iso.ext
  apply CategoricalPullback.hom_ext
  · change
      (stackMorphismInducedComparison (stackDiagonal X) D.map
        ((stackPullback X D.map).obj x) (selfProdObj x y)
        (diagonalUniversalComparison D.map D.universalIso)
        (D.lift toBase (diagonalComparisonIso toBase c)) z
        (diagonalLiftObjectIso toBase c (D.lift_map toBase
          (diagonalComparisonIso toBase c)))).hom.fst ≫
        (stackPullbackObjIsoOfEq (stackSelfProduct X).pullback map_eq
          (selfProdObj x y)).hom.fst = c.hom.fst
    rw [stackDiagonal_inducedComparison_hom_fst]
    have hu : (diagonalUniversalComparison D.map D.universalIso).hom.fst =
        𝟙 ((stackPullback X D.map).obj x) := by
      simp only [diagonalUniversalComparison, Iso.trans_hom]
      rw [CategoricalPullback.comp_fst]
      rw [stackProdObjIso_hom_fst, stackPullback_stackProdObj_hom_fst]
      change (𝟙 _ ≫ 𝟙 _) = 𝟙 _
      simp
    rw [hu]
    rw [(stackPullback X (D.lift toBase (diagonalComparisonIso toBase c))).map_id]
    have heq :
        (stackPullbackObjIsoOfEq (stackSelfProduct X).pullback map_eq
          (selfProdObj x y)).hom.fst =
          (stackPullbackObjIsoOfEq X map_eq x).hom := by
      change
        (stackPullbackObjIsoOfEq (stackProduct X X).pullback map_eq
          (stackProdObj x y)).hom.fst = _
      exact stackProduct_pullbackEq_hom_fst map_eq (stackProdObj x y)
    rw [heq]
    dsimp only [diagonalLiftObjectIso, diagonalComparisonFst, Iso.trans_hom,
      Iso.symm_hom]
    simp only [Category.assoc]
    change c.hom.fst ≫ (stackPullbackObjIsoOfEq X map_eq x).inv ≫
      (stackPullbackCompIso X (D.lift toBase (diagonalComparisonIso toBase c))
        D.map x).inv ≫ 𝟙 _ ≫
      (stackPullbackCompIso X (D.lift toBase (diagonalComparisonIso toBase c))
        D.map x).hom ≫ (stackPullbackObjIsoOfEq X map_eq x).hom = c.hom.fst
    simp only [Category.id_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  · change
      (stackMorphismInducedComparison (stackDiagonal X) D.map
        ((stackPullback X D.map).obj x) (selfProdObj x y)
        (diagonalUniversalComparison D.map D.universalIso)
        (D.lift toBase (diagonalComparisonIso toBase c)) z
        (diagonalLiftObjectIso toBase c (D.lift_map toBase
          (diagonalComparisonIso toBase c)))).hom.snd ≫
        (stackPullbackObjIsoOfEq (stackSelfProduct X).pullback map_eq
          (selfProdObj x y)).hom.snd = c.hom.snd
    rw [stackDiagonal_inducedComparison_hom_snd]
    have hu : (diagonalUniversalComparison D.map D.universalIso).hom.snd = D.universalIso.hom := by
      simp only [diagonalUniversalComparison, Iso.trans_hom]
      rw [CategoricalPullback.comp_snd]
      rw [stackProdObjIso_hom_snd, stackPullback_stackProdObj_hom_snd]
      change (_ ≫ 𝟙 _) = _
      simp
    rw [hu]
    have heq :
        (stackPullbackObjIsoOfEq (stackSelfProduct X).pullback map_eq
          (selfProdObj x y)).hom.snd =
          (stackPullbackObjIsoOfEq X map_eq y).hom := by
      change
        (stackPullbackObjIsoOfEq (stackProduct X X).pullback map_eq
          (stackProdObj x y)).hom.snd = _
      exact stackProduct_pullbackEq_hom_snd map_eq (stackProdObj x y)
    rw [heq]
    have htarget := congrArg (fun k => (diagonalComparisonFst toBase c).hom ≫ k.hom) hcomp
    simp only [diagonalComparisonIso, Iso.trans_hom, Iso.symm_hom,
      Iso.hom_inv_id_assoc] at htarget
    simp only [diagonalLiftObjectIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    change (diagonalComparisonFst toBase c).hom ≫
      (stackPullbackObjIsoOfEq X map_eq x).inv ≫
      (stackPullbackCompIso X (D.lift toBase (diagonalComparisonIso toBase c))
        D.map x).inv ≫
      (stackPullback X (D.lift toBase (diagonalComparisonIso toBase c))).map
        D.universalIso.hom ≫
      (stackPullbackCompIso X (D.lift toBase (diagonalComparisonIso toBase c))
        D.map y).hom ≫ (stackPullbackObjIsoOfEq X map_eq y).hom =
        (diagonalComparisonSnd toBase c).hom
    simpa only [diagonalComparisonIso, diagonalInducedIso, stackPullbackIso,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using! htarget

set_option backward.isDefEq.respectTransparency false in
/-- A classification by the diagonal gives both component equations, with all pullback
comparisons retained. -/
theorem diagonalComparison_components
    {X : FppfStack.{u}} {T U S : Scheme.{u}}
    {x y : StackFiber X T} (map : U ⟶ T)
    (e : (stackPullback X map).obj x ≅ (stackPullback X map).obj y)
    {z : StackFiber X S} (toBase : S ⟶ T)
    (c : ((stackDiagonal X).appFunctor S).obj z ≅
      (stackPullback (stackSelfProduct X).pullback toBase).obj (selfProdObj x y))
    (l : S ⟶ U) (a : z ≅ (stackPullback X l).obj ((stackPullback X map).obj x))
    (h : StackMorphismClassifies (stackDiagonal X) map ((stackPullback X map).obj x)
      (selfProdObj x y) (diagonalUniversalComparison map e) toBase z c l a) :
    ∃ hm : l ≫ map = toBase,
      a.hom ≫ (stackPullbackCompIso X l map x).hom ≫
        (stackPullbackObjIsoOfEq X hm x).hom = (diagonalComparisonFst toBase c).hom ∧
      a.hom ≫ (stackPullback X l).map e.hom ≫ (stackPullbackCompIso X l map y).hom ≫
        (stackPullbackObjIsoOfEq X hm y).hom = (diagonalComparisonSnd toBase c).hom := by
  obtain ⟨hm, hc⟩ := h
  refine ⟨hm, ?_, ?_⟩
  · have hf := congrArg (fun k ↦ k.hom.fst) hc
    change (stackMorphismInducedComparison (stackDiagonal X) map
      ((stackPullback X map).obj x) (selfProdObj x y)
      (diagonalUniversalComparison map e) l z a).hom.fst ≫
      (stackPullbackObjIsoOfEq (stackSelfProduct X).pullback hm (selfProdObj x y)).hom.fst =
        c.hom.fst at hf
    rw [stackDiagonal_inducedComparison_hom_fst] at hf
    have he := stackProduct_pullbackEq_hom_fst (X := X) (Y := X) hm (stackProdObj x y)
    change (stackPullbackObjIsoOfEq (stackSelfProduct X).pullback hm
      (selfProdObj x y)).hom.fst = (stackPullbackObjIsoOfEq X hm x).hom at he
    rw [he] at hf
    change (a.hom ≫ (stackPullback X l).map (𝟙 _ ≫ 𝟙 _) ≫
      (stackPullbackCompIso X l map x).hom) ≫ (stackPullbackObjIsoOfEq X hm x).hom =
      (diagonalComparisonFst toBase c).hom at hf
    simp only [Category.id_comp] at hf
    rw [(stackPullback X l).map_id] at hf
    simpa only [Category.id_comp, Category.assoc] using! hf
  · have hs := congrArg (fun k ↦ k.hom.snd) hc
    change (stackMorphismInducedComparison (stackDiagonal X) map
      ((stackPullback X map).obj x) (selfProdObj x y)
      (diagonalUniversalComparison map e) l z a).hom.snd ≫
      (stackPullbackObjIsoOfEq (stackSelfProduct X).pullback hm (selfProdObj x y)).hom.snd =
        c.hom.snd at hs
    rw [stackDiagonal_inducedComparison_hom_snd] at hs
    have he := stackProduct_pullbackEq_hom_snd (X := X) (Y := X) hm (stackProdObj x y)
    change (stackPullbackObjIsoOfEq (stackSelfProduct X).pullback hm
      (selfProdObj x y)).hom.snd = (stackPullbackObjIsoOfEq X hm y).hom at he
    rw [he] at hs
    change (a.hom ≫ (stackPullback X l).map (e.hom ≫ 𝟙 _) ≫
      (stackPullbackCompIso X l map y).hom) ≫ (stackPullbackObjIsoOfEq X hm y).hom =
      (diagonalComparisonSnd toBase c).hom at hs
    simpa only [Category.comp_id, Category.assoc] using hs

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the source-object comparison gives the classified isomorphism between the two
factor objects. -/
theorem diagonalClassifies_of_stackMorphismClassifies
    {X : FppfStack.{u}} {T U S : Scheme.{u}}
    {x y : StackFiber X T} (map : U ⟶ T)
    (e : (stackPullback X map).obj x ≅ (stackPullback X map).obj y)
    {z : StackFiber X S} (toBase : S ⟶ T)
    (c : ((stackDiagonal X).appFunctor S).obj z ≅
      (stackPullback (stackSelfProduct X).pullback toBase).obj (selfProdObj x y))
    (l : S ⟶ U) (a : z ≅ (stackPullback X l).obj ((stackPullback X map).obj x))
    (h : StackMorphismClassifies (stackDiagonal X) map ((stackPullback X map).obj x)
      (selfProdObj x y) (diagonalUniversalComparison map e) toBase z c l a) :
    DiagonalClassifies X map e toBase (diagonalComparisonIso toBase c) l := by
  obtain ⟨hm, hf, hs⟩ := diagonalComparison_components map e toBase c l a h
  refine ⟨hm, ?_⟩
  apply Iso.ext
  simp only [diagonalInducedIso, stackPullbackIso, diagonalComparisonIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  apply (cancel_epi (diagonalComparisonFst toBase c).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← hf]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hs

set_option backward.isDefEq.respectTransparency false in
/-- The first projection forces the source-object isomorphism uniquely. -/
theorem diagonalLiftObjectIso_forced
    {X : FppfStack.{u}} {T U S : Scheme.{u}}
    {x y : StackFiber X T} (map : U ⟶ T)
    (e : (stackPullback X map).obj x ≅ (stackPullback X map).obj y)
    {z : StackFiber X S} (toBase : S ⟶ T)
    (c : ((stackDiagonal X).appFunctor S).obj z ≅
      (stackPullback (stackSelfProduct X).pullback toBase).obj (selfProdObj x y))
    (l : S ⟶ U) (a : z ≅ (stackPullback X l).obj ((stackPullback X map).obj x))
    (hm : l ≫ map = toBase)
    (h : StackMorphismClassifies (stackDiagonal X) map ((stackPullback X map).obj x)
      (selfProdObj x y) (diagonalUniversalComparison map e) toBase z c l a) :
    a = diagonalLiftObjectIso toBase c hm := by
  obtain ⟨hm', hf, _⟩ := diagonalComparison_components map e toBase c l a h
  apply Iso.ext
  change a.hom = (diagonalComparisonFst toBase c).hom ≫
    (stackPullbackObjIsoOfEq X hm' x).inv ≫ (stackPullbackCompIso X l map x).inv
  rw [← hf]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Convert an isomorphism-scheme presentation into a complete scheme presentation of the
constructed diagonal. Both uniqueness conditions follow from the two component equations. -/
noncomputable def DiagonalPresentation.toStackMorphismPresentation
    {X : FppfStack.{u}} {T : Scheme.{u}} {x y : StackFiber X T}
    (D : DiagonalPresentation X T x y) :
    StackMorphismPresentation (stackDiagonal X) T (selfProdObj x y) where
  space := D.space
  map := D.map
  object := (stackPullback X D.map).obj x
  comparison := diagonalUniversalComparison D.map D.universalIso
  lift toBase _ c := D.lift toBase (diagonalComparisonIso toBase c)
  lift_map toBase _ c := D.lift_map toBase (diagonalComparisonIso toBase c)
  liftObjectIso toBase _ c :=
    diagonalLiftObjectIso toBase c (D.lift_map toBase (diagonalComparisonIso toBase c))
  lift_compatible toBase _ c := diagonalComparison_classifies D toBase c
  liftObjectIso_unique toBase _ c a h := diagonalLiftObjectIso_forced
    D.map D.universalIso toBase c _ a _ h
  lift_unique toBase _ c l a h := D.lift_unique toBase (diagonalComparisonIso toBase c)
    l (diagonalClassifies_of_stackMorphismClassifies D.map D.universalIso toBase c l a h)

/-- Representability of all isomorphism sheaves proves representability of the actual
constructed diagonal morphism. -/
theorem stackDiagonal_isRepresentable_of_hasRepresentableDiagonal
    {X : FppfStack.{u}} (hX : HasRepresentableDiagonal X) :
    (stackDiagonal X).IsRepresentable := by
  refine ⟨stackDiagonal X, ⟨StackIso2.refl _⟩, ?_⟩
  intro T p
  obtain ⟨D⟩ := hX T (CategoricalPullback.fst p) (CategoricalPullback.snd p)
  have hp : selfProdObj (CategoricalPullback.fst p) (CategoricalPullback.snd p) = p :=
    stackProdObj_components p
  rw [← hp]
  exact ⟨⟨D.toStackMorphismPresentation, trivial⟩⟩

/-- Properties of all isomorphism schemes hold representably on the actual diagonal. -/
theorem stackDiagonal_hasRepresentableProperty_of_diagonalHasProperty
    {X : FppfStack.{u}} (P : MorphismProperty Scheme.{u}) (hX : DiagonalHasProperty X P) :
    (stackDiagonal X).HasRepresentableProperty P := by
  refine ⟨stackDiagonal X, ⟨StackIso2.refl _⟩, ?_⟩
  intro T p
  obtain ⟨⟨D, hD⟩⟩ := hX T (CategoricalPullback.fst p) (CategoricalPullback.snd p)
  have hp : selfProdObj (CategoricalPullback.fst p) (CategoricalPullback.snd p) = p :=
    stackProdObj_components p
  rw [← hp]
  exact ⟨⟨D.toStackMorphismPresentation, hD⟩⟩

/-- The diagonal morphism of an algebraic stack is representable in the morphism encoding. -/
theorem AlgebraicStack.stackDiagonal_isRepresentable (A : AlgebraicStack.{u}) :
    (stackDiagonal A.toStack).IsRepresentable :=
  stackDiagonal_isRepresentable_of_hasRepresentableDiagonal A.diagonal_representable

/-- The inertia projection of an algebraic stack is representable. -/
theorem AlgebraicStack.inertiaProjection_isRepresentable (A : AlgebraicStack.{u}) :
    A.inertiaProjection.IsRepresentable :=
  inertiaProjection_hasRepresentableProperty A.toStack ⊤ A.stackDiagonal_isRepresentable

/-- The chart-isomorphism hypothesis gives an unramified diagonal without a separate
morphism-level representability assumption. -/
theorem DeligneMumfordStack.stackDiagonal_unramified_of_chartIsom
    (A : DeligneMumfordStack.{u})
    (hIsom : ∀ c : StackChart A.toStack, c.IsEtaleSurjective → c.HasUnramifiedIsom) :
    (stackDiagonal A.toStack).Unramified :=
  A.stackDiagonal_unramified A.toAlgebraicStack.stackDiagonal_isRepresentable hIsom

end GromovWitten.AlgebraicGeometry
