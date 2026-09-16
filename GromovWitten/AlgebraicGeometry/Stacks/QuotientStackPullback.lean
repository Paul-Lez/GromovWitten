/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientStack
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Base change of equivariant torsors

For a morphism of schemes `b : T' ⟶ T` this file constructs the base change of the objects of
`ActionTorsor G U T`.  The underlying sheaf is the actual fibre product `P ×_T T'` of fppf
sheaves, the `G`-action is the induced action on that fibre product, the equivariant map to `U`
is obtained from the projection to `P`, and both the principal map and the fppf-local section
are constructed: local triviality uses the base change of the original cover, which stays flat,
locally of finite presentation and surjective.  Nothing is assumed; every field of the
base-changed torsor is built and its defining equations are proved.

The construction is functorial: `ActionTorsor.pullbackFunctor b` is a functor between the
quotient groupoids, `ActionTorsor.pullbackFunctorIdIso` compares base change along an identity
with the identity functor, `ActionTorsor.pullbackFunctorCompIso` compares base change along a
composite with the composite of base changes, and the three coherence laws
(`ActionTorsor.pullbackFunctor_comp_id`, `ActionTorsor.pullbackFunctor_id_comp`,
`ActionTorsor.pullbackFunctor_assoc`) are proved.  They assemble into the contravariant
pseudofunctor `ActionTorsor.pullbackPseudofunctor` from the locally discrete bicategory of
schemes to `Cat`, whose fibres are the groupoids `ActionTorsor G U T`.

`FppfTorsor.pullbackTorsor`, `ActionTorsor.pullbackObj` and `ActionTorsor.pullbackFunctor` are
marked `@[reducible]` so that an iterated base change still presents its underlying fibre
products to `simp` and `rw`; no statement below depends on that choice.

No stackification is claimed here; the descent condition for this pseudofunctor remains open.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace FppfTorsor

variable {G : AlgebraicSpaceGroup.{u}} {T T' : Scheme.{u}}

/-- The sheaf underlying the base change of an fppf torsor along a scheme morphism. -/
noncomputable abbrev pullbackSheaf (P : FppfTorsor G T) (b : T' ⟶ T) : FppfSheaf.{u} :=
  Limits.pullback P.projection (fppfYoneda.map b)

section

variable (P : FppfTorsor G T) (b : T' ⟶ T)

theorem pullbackSheaf_condition :
    (G.space.toSheaf ◁ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫
        ModObj.smul (M := G.space.toSheaf) (X := P.P) ≫ P.projection =
      (snd G.space.toSheaf (pullbackSheaf P b) ≫
        Limits.pullback.snd P.projection (fppfYoneda.map b)) ≫ fppfYoneda.map b := by
  rw [P.action_over, Category.assoc, ← Category.assoc _ (snd _ _), whiskerLeft_snd]
  simp [Limits.pullback.condition]

/-- The action of `G` on the base-changed sheaf. -/
noncomputable def pullbackSmul :
    G.space.toSheaf ⊗ pullbackSheaf P b ⟶ pullbackSheaf P b :=
  Limits.pullback.lift
    ((G.space.toSheaf ◁ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫
      ModObj.smul (M := G.space.toSheaf) (X := P.P))
    (snd G.space.toSheaf (pullbackSheaf P b) ≫
      Limits.pullback.snd P.projection (fppfYoneda.map b))
    (by simpa using pullbackSheaf_condition P b)

@[reassoc (attr := simp)]
theorem pullbackSmul_fst :
    pullbackSmul P b ≫ Limits.pullback.fst P.projection (fppfYoneda.map b) =
      (G.space.toSheaf ◁ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫
        ModObj.smul (M := G.space.toSheaf) (X := P.P) :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackSmul_snd :
    pullbackSmul P b ≫ Limits.pullback.snd P.projection (fppfYoneda.map b) =
      snd G.space.toSheaf (pullbackSheaf P b) ≫
        Limits.pullback.snd P.projection (fppfYoneda.map b) :=
  Limits.pullback.lift_snd _ _ _

/-- The base-changed sheaf is again a `G`-object. -/
@[instance_reducible]
noncomputable def pullbackAction : ModObj G.space.toSheaf (pullbackSheaf P b) where
  smul := pullbackSmul P b
  one_smul := by
    apply Limits.pullback.hom_ext
    · simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
        MonoidalCategory.selfLeftAction_actionUnitIso, Category.assoc, pullbackSmul_fst]
      rw [← Category.assoc, ← MonoidalCategory.whisker_exchange, Category.assoc]
      simp [leftUnitor_hom]
    · simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
        MonoidalCategory.selfLeftAction_actionUnitIso, Category.assoc, pullbackSmul_snd]
      simp [leftUnitor_hom]
  mul_smul := by
    apply Limits.pullback.hom_ext
    · simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
        MonoidalCategory.selfLeftAction_actionHomRight,
        MonoidalCategory.selfLeftAction_actionAssocIso, Category.assoc, pullbackSmul_fst]
      rw [← Category.assoc, ← MonoidalCategory.whisker_exchange, Category.assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, pullbackSmul_fst,
        MonoidalCategory.whiskerLeft_comp]
      have hmul := ModObj.mul_smul (M := G.space.toSheaf) (X := P.P)
      simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
        MonoidalCategory.selfLeftAction_actionHomRight,
        MonoidalCategory.selfLeftAction_actionAssocIso] at hmul
      rw [hmul, MonoidalCategory.associator_naturality_right_assoc]
      simp
    · simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
        MonoidalCategory.selfLeftAction_actionHomRight,
        MonoidalCategory.selfLeftAction_actionAssocIso, Category.assoc, pullbackSmul_snd]
      simp

/-- The principal map of a torsor is the canonical lift of its action and its projection. -/
theorem principalMap_eq :
    P.principalMap =
      Limits.pullback.lift (ModObj.smul (M := G.space.toSheaf) (X := P.P))
        (snd G.space.toSheaf P.P) P.action_over := by
  apply Limits.pullback.hom_ext
  · rw [P.principal_fst, Limits.pullback.lift_fst]
  · rw [P.principal_snd, Limits.pullback.lift_snd]

/-- The principal map of the base-changed torsor. -/
noncomputable def pullbackPrincipalMap :
    G.space.toSheaf ⊗ pullbackSheaf P b ⟶
      Limits.pullback (Limits.pullback.snd P.projection (fppfYoneda.map b))
        (Limits.pullback.snd P.projection (fppfYoneda.map b)) :=
  Limits.pullback.lift (pullbackSmul P b) (snd G.space.toSheaf (pullbackSheaf P b))
    (pullbackSmul_snd P b)

@[reassoc (attr := simp)]
theorem pullbackPrincipalMap_fst :
    pullbackPrincipalMap P b ≫
        Limits.pullback.fst (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (Limits.pullback.snd P.projection (fppfYoneda.map b)) = pullbackSmul P b :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackPrincipalMap_snd :
    pullbackPrincipalMap P b ≫
        Limits.pullback.snd (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (Limits.pullback.snd P.projection (fppfYoneda.map b)) =
      snd G.space.toSheaf (pullbackSheaf P b) :=
  Limits.pullback.lift_snd _ _ _

/-- The comparison map from the self-product of the base-changed torsor to the self-product of
the original torsor. -/
noncomputable def pullbackDiagonalCompare :
    Limits.pullback (Limits.pullback.snd P.projection (fppfYoneda.map b))
        (Limits.pullback.snd P.projection (fppfYoneda.map b)) ⟶
      Limits.pullback P.projection P.projection :=
  Limits.pullback.lift
    (Limits.pullback.fst _ _ ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
    (Limits.pullback.snd _ _ ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
    (by
      rw [Category.assoc, Category.assoc, Limits.pullback.condition, ← Category.assoc,
        ← Category.assoc, Limits.pullback.condition])

@[reassoc (attr := simp)]
theorem pullbackDiagonalCompare_fst :
    pullbackDiagonalCompare P b ≫ Limits.pullback.fst P.projection P.projection =
      Limits.pullback.fst (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (Limits.pullback.snd P.projection (fppfYoneda.map b)) ≫
        Limits.pullback.fst P.projection (fppfYoneda.map b) :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackDiagonalCompare_snd :
    pullbackDiagonalCompare P b ≫ Limits.pullback.snd P.projection P.projection =
      Limits.pullback.snd (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (Limits.pullback.snd P.projection (fppfYoneda.map b)) ≫
        Limits.pullback.fst P.projection (fppfYoneda.map b) :=
  Limits.pullback.lift_snd _ _ _

/-- The inverse of the principal map of the base-changed torsor. -/
noncomputable def pullbackPrincipalInv :
    Limits.pullback (Limits.pullback.snd P.projection (fppfYoneda.map b))
        (Limits.pullback.snd P.projection (fppfYoneda.map b)) ⟶
      G.space.toSheaf ⊗ pullbackSheaf P b :=
  lift (pullbackDiagonalCompare P b ≫ inv P.principalMap ≫ fst G.space.toSheaf P.P)
    (Limits.pullback.snd _ _)

@[reassoc (attr := simp)]
theorem pullbackPrincipalInv_fst :
    pullbackPrincipalInv P b ≫ fst G.space.toSheaf (pullbackSheaf P b) =
      pullbackDiagonalCompare P b ≫ inv P.principalMap ≫ fst G.space.toSheaf P.P :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem pullbackPrincipalInv_snd :
    pullbackPrincipalInv P b ≫ snd G.space.toSheaf (pullbackSheaf P b) =
      Limits.pullback.snd (Limits.pullback.snd P.projection (fppfYoneda.map b))
        (Limits.pullback.snd P.projection (fppfYoneda.map b)) :=
  lift_snd _ _

theorem pullbackPrincipalMap_comp_compare :
    pullbackPrincipalMap P b ≫ pullbackDiagonalCompare P b =
      (G.space.toSheaf ◁ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫
        P.principalMap := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, pullbackDiagonalCompare_fst, Category.assoc, P.principal_fst,
      pullbackPrincipalMap_fst_assoc, pullbackSmul_fst]
  · rw [Category.assoc, pullbackDiagonalCompare_snd, Category.assoc, P.principal_snd,
      pullbackPrincipalMap_snd_assoc, whiskerLeft_snd]

theorem pullbackPrincipalMap_inv :
    pullbackPrincipalMap P b ≫ pullbackPrincipalInv P b = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, pullbackPrincipalInv_fst, ← Category.assoc,
      pullbackPrincipalMap_comp_compare]
    simp
  · rw [Category.assoc, pullbackPrincipalInv_snd, pullbackPrincipalMap_snd, Category.id_comp]

theorem pullbackPrincipalInv_whiskerLeft :
    pullbackPrincipalInv P b ≫
        (G.space.toSheaf ◁ Limits.pullback.fst P.projection (fppfYoneda.map b)) =
      pullbackDiagonalCompare P b ≫ inv P.principalMap := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerLeft_fst, pullbackPrincipalInv_fst, Category.assoc]
  · rw [Category.assoc, whiskerLeft_snd, pullbackPrincipalInv_snd_assoc, Category.assoc,
      ← P.principal_snd, IsIso.inv_hom_id_assoc, pullbackDiagonalCompare_snd]

theorem pullbackPrincipalInv_map :
    pullbackPrincipalInv P b ≫ pullbackPrincipalMap P b = 𝟙 _ := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, pullbackPrincipalMap_fst, Category.id_comp]
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, pullbackSmul_fst, ← Category.assoc,
        pullbackPrincipalInv_whiskerLeft, Category.assoc, ← P.principal_fst,
        IsIso.inv_hom_id_assoc, pullbackDiagonalCompare_fst]
    · rw [Category.assoc, pullbackSmul_snd, pullbackPrincipalInv_snd_assoc]
      exact Limits.pullback.condition.symm
  · rw [Category.assoc, pullbackPrincipalMap_snd, pullbackPrincipalInv_snd, Category.id_comp]

instance : IsIso (pullbackPrincipalMap P b) :=
  ⟨pullbackPrincipalInv P b, pullbackPrincipalMap_inv P b, pullbackPrincipalInv_map P b⟩

/-- Base change of an fppf-local section along a scheme morphism.  The cover is the fibre
product of the original cover with the base-change morphism. -/
noncomputable def pullbackLocalSection :
    FppfLocalSection (pullbackSheaf P b) T'
      (Limits.pullback.snd P.projection (fppfYoneda.map b)) where
  coverScheme := Limits.pullback b P.locallyTrivial.cover
  cover := Limits.pullback.fst b P.locallyTrivial.cover
  flat :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.Flat)
      (IsPullback.of_hasPullback b P.locallyTrivial.cover).flip P.locallyTrivial.flat
  locallyOfFinitePresentation :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.LocallyOfFinitePresentation)
      (IsPullback.of_hasPullback b P.locallyTrivial.cover).flip
      P.locallyTrivial.locallyOfFinitePresentation
  surjective :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.Surjective)
      (IsPullback.of_hasPullback b P.locallyTrivial.cover).flip P.locallyTrivial.surjective
  localLift :=
    Limits.pullback.lift
      (fppfYoneda.map (Limits.pullback.snd b P.locallyTrivial.cover) ≫
        P.locallyTrivial.localLift)
      (fppfYoneda.map (Limits.pullback.fst b P.locallyTrivial.cover))
      (by
        rw [Category.assoc, P.locallyTrivial.localLift_over, ← fppfYoneda.map_comp,
          ← fppfYoneda.map_comp, Limits.pullback.condition])
  localLift_over := Limits.pullback.lift_snd _ _ _

/-- The base change of an fppf torsor along a morphism of schemes. -/
@[reducible]
noncomputable def pullbackTorsor : FppfTorsor G T' where
  P := pullbackSheaf P b
  action := pullbackAction P b
  projection := Limits.pullback.snd P.projection (fppfYoneda.map b)
  action_over := pullbackSmul_snd P b
  principalMap := pullbackPrincipalMap P b
  principal_fst := pullbackPrincipalMap_fst P b
  principal_snd := pullbackPrincipalMap_snd P b
  principal_isIso := inferInstance
  locallyTrivial := pullbackLocalSection P b

theorem pullbackTorsor_P : (pullbackTorsor P b).P = pullbackSheaf P b :=
  rfl

theorem pullbackTorsor_projection :
    (pullbackTorsor P b).projection =
      Limits.pullback.snd P.projection (fppfYoneda.map b) :=
  rfl

@[simp]
theorem pullbackTorsor_smul :
    ModObj.smul (M := G.space.toSheaf) (X := (pullbackTorsor P b).P)
      (self := FppfTorsor.action (pullbackTorsor P b)) = pullbackSmul P b :=
  rfl

/-- The principal map of the base change is the constructed one; in particular it is again an
isomorphism. -/
theorem pullbackTorsor_principalMap :
    (pullbackTorsor P b).principalMap = pullbackPrincipalMap P b :=
  rfl

/-- Local triviality survives base change: the cover of the base-changed torsor is the fibre
product of the original cover with the base-change morphism. -/
theorem pullbackTorsor_cover :
    (pullbackTorsor P b).locallyTrivial.cover =
      Limits.pullback.fst b P.locallyTrivial.cover :=
  rfl

end

section

variable {G : AlgebraicSpaceGroup.{u}} {T T' : Scheme.{u}} {P Q : FppfTorsor G T}

/-- Base change of a morphism of torsors over the same base. -/
noncomputable def pullbackMap (b : T' ⟶ T) (h : P.P ⟶ Q.P)
    (hover : h ≫ Q.projection = P.projection) : pullbackSheaf P b ⟶ pullbackSheaf Q b :=
  Limits.pullback.lift (Limits.pullback.fst P.projection (fppfYoneda.map b) ≫ h)
    (Limits.pullback.snd P.projection (fppfYoneda.map b))
    (by rw [Category.assoc, hover, Limits.pullback.condition])

@[reassoc (attr := simp)]
theorem pullbackMap_fst (b : T' ⟶ T) (h : P.P ⟶ Q.P)
    (hover : h ≫ Q.projection = P.projection) :
    pullbackMap b h hover ≫ Limits.pullback.fst Q.projection (fppfYoneda.map b) =
      Limits.pullback.fst P.projection (fppfYoneda.map b) ≫ h :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackMap_snd (b : T' ⟶ T) (h : P.P ⟶ Q.P)
    (hover : h ≫ Q.projection = P.projection) :
    pullbackMap b h hover ≫ Limits.pullback.snd Q.projection (fppfYoneda.map b) =
      Limits.pullback.snd P.projection (fppfYoneda.map b) :=
  Limits.pullback.lift_snd _ _ _

theorem pullbackMap_id (b : T' ⟶ T) (hover : 𝟙 P.P ≫ P.projection = P.projection) :
    pullbackMap b (𝟙 P.P) hover = 𝟙 (pullbackSheaf P b) := by
  apply Limits.pullback.hom_ext <;> simp

theorem pullbackMap_comp (b : T' ⟶ T) {R : FppfTorsor G T} (h : P.P ⟶ Q.P) (k : Q.P ⟶ R.P)
    (hover : h ≫ Q.projection = P.projection) (kover : k ≫ R.projection = Q.projection)
    (hkover : (h ≫ k) ≫ R.projection = P.projection) :
    pullbackMap b (h ≫ k) hkover = pullbackMap b h hover ≫ pullbackMap b k kover := by
  apply Limits.pullback.hom_ext <;> simp

/-- Base change of an equivariant morphism is equivariant. -/
theorem pullbackSmul_pullbackMap (b : T' ⟶ T) (h : P.P ⟶ Q.P)
    (hover : h ≫ Q.projection = P.projection)
    (hequiv : ModObj.smul (M := G.space.toSheaf) (X := P.P) ≫ h =
      G.space.toSheaf ◁ h ≫ ModObj.smul (M := G.space.toSheaf) (X := Q.P)) :
    pullbackSmul P b ≫ pullbackMap b h hover =
      G.space.toSheaf ◁ pullbackMap b h hover ≫ pullbackSmul Q b := by
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, pullbackMap_fst, pullbackSmul_fst, pullbackSmul_fst_assoc,
      hequiv, ← MonoidalCategory.whiskerLeft_comp_assoc]
  · rw [Category.assoc, pullbackMap_snd, pullbackSmul_snd, Category.assoc, pullbackSmul_snd,
      ← Category.assoc, whiskerLeft_snd, Category.assoc, pullbackMap_snd]

/-- Base change of an isomorphism of torsors over the same base. -/
noncomputable def pullbackMapIso (b : T' ⟶ T) (e : P.P ≅ Q.P)
    (hover : e.hom ≫ Q.projection = P.projection) : pullbackSheaf P b ≅ pullbackSheaf Q b where
  hom := pullbackMap b e.hom hover
  inv := pullbackMap b e.inv (by rw [← hover, ← Category.assoc, e.inv_hom_id, Category.id_comp])
  hom_inv_id := by apply Limits.pullback.hom_ext <;> simp
  inv_hom_id := by apply Limits.pullback.hom_ext <;> simp

@[simp]
theorem pullbackMapIso_hom (b : T' ⟶ T) (e : P.P ≅ Q.P)
    (hover : e.hom ≫ Q.projection = P.projection) :
    (pullbackMapIso b e hover).hom = pullbackMap b e.hom hover :=
  rfl

end

section

variable {T'' : Scheme.{u}} (P : FppfTorsor G T) (a : T'' ⟶ T') (b : T' ⟶ T)

/-- Base change along an identity recovers the original torsor sheaf. -/
noncomputable def pullbackIdIso : pullbackSheaf P (𝟙 T) ≅ P.P where
  hom := Limits.pullback.fst P.projection (fppfYoneda.map (𝟙 T))
  inv := Limits.pullback.lift (𝟙 P.P) P.projection (by simp)
  hom_inv_id := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.id_comp,
        Limits.pullback.condition]
      simp
  inv_hom_id := Limits.pullback.lift_fst _ _ _

@[simp]
theorem pullbackIdIso_hom :
    (pullbackIdIso P).hom = Limits.pullback.fst P.projection (fppfYoneda.map (𝟙 T)) :=
  rfl

/-- The identity comparison is equivariant. -/
theorem pullbackSmul_pullbackIdIso :
    pullbackSmul P (𝟙 T) ≫ (pullbackIdIso P).hom =
      G.space.toSheaf ◁ (pullbackIdIso P).hom ≫
        ModObj.smul (M := G.space.toSheaf) (X := P.P) := by
  rw [pullbackIdIso_hom, pullbackSmul_fst]

/-- The action on a twice base-changed torsor, computed on the first leg. -/
@[reassoc (attr := simp)]
theorem pullbackSmul_pullbackTorsor_fst :
    pullbackSmul (pullbackTorsor P b) a ≫
        Limits.pullback.fst (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (fppfYoneda.map a) =
      G.space.toSheaf ◁ Limits.pullback.fst (Limits.pullback.snd P.projection
          (fppfYoneda.map b)) (fppfYoneda.map a) ≫ pullbackSmul P b :=
  pullbackSmul_fst _ _

/-- The action on a twice base-changed torsor, computed on the second leg. -/
@[reassoc (attr := simp)]
theorem pullbackSmul_pullbackTorsor_snd :
    pullbackSmul (pullbackTorsor P b) a ≫
        Limits.pullback.snd (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (fppfYoneda.map a) =
      snd G.space.toSheaf (pullbackSheaf (pullbackTorsor P b) a) ≫
        Limits.pullback.snd (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (fppfYoneda.map a) :=
  pullbackSmul_snd _ _

/-- Base change along a composite agrees with the two successive base changes. -/
noncomputable def pullbackCompIso :
    pullbackSheaf P (a ≫ b) ≅ pullbackSheaf (pullbackTorsor P b) a where
  hom :=
    Limits.pullback.lift
      (Limits.pullback.lift (Limits.pullback.fst P.projection (fppfYoneda.map (a ≫ b)))
        (Limits.pullback.snd P.projection (fppfYoneda.map (a ≫ b)) ≫ fppfYoneda.map a)
        (by rw [Limits.pullback.condition, Category.assoc, ← fppfYoneda.map_comp]))
      (Limits.pullback.snd P.projection (fppfYoneda.map (a ≫ b)))
      (Limits.pullback.lift_snd _ _ _)
  inv :=
    Limits.pullback.lift
      (Limits.pullback.fst (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (fppfYoneda.map a) ≫
        Limits.pullback.fst P.projection (fppfYoneda.map b))
      (Limits.pullback.snd (Limits.pullback.snd P.projection (fppfYoneda.map b))
        (fppfYoneda.map a))
      (by
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
          Limits.pullback.condition, Category.assoc, ← fppfYoneda.map_comp])
  hom_inv_id := by
    apply Limits.pullback.hom_ext <;>
      simp only [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_snd,
        Limits.pullback.lift_fst_assoc, Category.id_comp]
  inv_hom_id := by
    apply Limits.pullback.hom_ext
    · apply Limits.pullback.hom_ext <;>
        simp only [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_snd,
          Limits.pullback.lift_snd_assoc, Category.id_comp, Limits.pullback.condition]
    · simp only [Category.assoc, Limits.pullback.lift_snd, Category.id_comp]

@[reassoc (attr := simp)]
theorem pullbackCompIso_hom_fst_fst :
    (pullbackCompIso P a b).hom ≫
        Limits.pullback.fst (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (fppfYoneda.map a) ≫
        Limits.pullback.fst P.projection (fppfYoneda.map b) =
      Limits.pullback.fst P.projection (fppfYoneda.map (a ≫ b)) := by
  simp only [pullbackCompIso, Limits.pullback.lift_fst_assoc, Limits.pullback.lift_fst]

@[reassoc (attr := simp)]
theorem pullbackCompIso_hom_fst_snd :
    (pullbackCompIso P a b).hom ≫
        Limits.pullback.fst (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (fppfYoneda.map a) ≫
        Limits.pullback.snd P.projection (fppfYoneda.map b) =
      Limits.pullback.snd P.projection (fppfYoneda.map (a ≫ b)) ≫ fppfYoneda.map a := by
  simp only [pullbackCompIso, Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd]

@[reassoc (attr := simp)]
theorem pullbackCompIso_hom_snd :
    (pullbackCompIso P a b).hom ≫
        Limits.pullback.snd (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (fppfYoneda.map a) =
      Limits.pullback.snd P.projection (fppfYoneda.map (a ≫ b)) := by
  simp only [pullbackCompIso, Limits.pullback.lift_snd]

/-- The composition comparison is equivariant. -/
theorem pullbackSmul_pullbackCompIso :
    pullbackSmul P (a ≫ b) ≫ (pullbackCompIso P a b).hom =
      G.space.toSheaf ◁ (pullbackCompIso P a b).hom ≫ pullbackSmul (pullbackTorsor P b) a := by
  apply Limits.pullback.hom_ext
  · apply Limits.pullback.hom_ext
    · simp only [Category.assoc, pullbackCompIso_hom_fst_fst, pullbackSmul_fst,
        pullbackSmul_pullbackTorsor_fst_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, pullbackCompIso_hom_fst_fst]
    · simp only [Category.assoc, pullbackCompIso_hom_fst_snd, pullbackSmul_snd_assoc,
        pullbackSmul_pullbackTorsor_fst_assoc, pullbackSmul_snd, whiskerLeft_snd_assoc,
        pullbackCompIso_hom_fst_snd]
  · simp only [Category.assoc, pullbackCompIso_hom_snd, pullbackSmul_snd,
      pullbackSmul_pullbackTorsor_snd, whiskerLeft_snd_assoc, pullbackCompIso_hom_snd]

end

end FppfTorsor

namespace FppfTorsor

section

variable {G : AlgebraicSpaceGroup.{u}} {T T' T'' : Scheme.{u}} {P Q : FppfTorsor G T}

/-- Base change of a torsor morphism through two successive base changes. -/
@[reassoc (attr := simp)]
theorem pullbackMap_pullbackTorsor_fst (a : T'' ⟶ T') (b : T' ⟶ T) (h : P.P ⟶ Q.P)
    (hover : h ≫ Q.projection = P.projection)
    (hover' : pullbackMap b h hover ≫ (pullbackTorsor Q b).projection =
      (pullbackTorsor P b).projection) :
    pullbackMap (P := pullbackTorsor P b) (Q := pullbackTorsor Q b) a
          (pullbackMap b h hover) hover' ≫
        Limits.pullback.fst (Limits.pullback.snd Q.projection (fppfYoneda.map b))
          (fppfYoneda.map a) =
      Limits.pullback.fst (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (fppfYoneda.map a) ≫
        pullbackMap b h hover :=
  pullbackMap_fst _ _ _

/-- Base change of a torsor morphism through two successive base changes, second leg. -/
@[reassoc (attr := simp)]
theorem pullbackMap_pullbackTorsor_snd (a : T'' ⟶ T') (b : T' ⟶ T) (h : P.P ⟶ Q.P)
    (hover : h ≫ Q.projection = P.projection)
    (hover' : pullbackMap b h hover ≫ (pullbackTorsor Q b).projection =
      (pullbackTorsor P b).projection) :
    pullbackMap (P := pullbackTorsor P b) (Q := pullbackTorsor Q b) a
          (pullbackMap b h hover) hover' ≫
        Limits.pullback.snd (Limits.pullback.snd Q.projection (fppfYoneda.map b))
          (fppfYoneda.map a) =
      Limits.pullback.snd (Limits.pullback.snd P.projection (fppfYoneda.map b))
        (fppfYoneda.map a) :=
  pullbackMap_snd _ _ _

/-- The composition comparison is natural in the torsor. -/
theorem pullbackCompIso_naturality (a : T'' ⟶ T') (b : T' ⟶ T) (h : P.P ⟶ Q.P)
    (hover : h ≫ Q.projection = P.projection)
    (hover' : pullbackMap b h hover ≫ (pullbackTorsor Q b).projection =
      (pullbackTorsor P b).projection)
    (hover'' : h ≫ Q.projection = P.projection) :
    pullbackMap (a ≫ b) h hover'' ≫ (pullbackCompIso Q a b).hom =
      (pullbackCompIso P a b).hom ≫
        pullbackMap (P := pullbackTorsor P b) (Q := pullbackTorsor Q b) a
          (pullbackMap b h hover) hover' := by
  apply Limits.pullback.hom_ext
  · apply Limits.pullback.hom_ext <;>
      simp only [Category.assoc, pullbackCompIso_hom_fst_fst, pullbackCompIso_hom_fst_snd,
        pullbackMap_fst, pullbackMap_snd, pullbackMap_snd_assoc,
        pullbackMap_pullbackTorsor_fst_assoc, pullbackCompIso_hom_fst_fst_assoc]
  · simp only [Category.assoc, pullbackCompIso_hom_snd, pullbackMap_snd,
      pullbackMap_pullbackTorsor_snd, pullbackCompIso_hom_snd]

end

section

variable {G : AlgebraicSpaceGroup.{u}} {T T' T'' : Scheme.{u}} (P : FppfTorsor G T)
  (a : T'' ⟶ T') (b : T' ⟶ T)

@[reassoc (attr := simp)]
theorem pullbackCompIso_inv_fst :
    (pullbackCompIso P a b).inv ≫
        Limits.pullback.fst P.projection (fppfYoneda.map (a ≫ b)) =
      Limits.pullback.fst (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (fppfYoneda.map a) ≫
        Limits.pullback.fst P.projection (fppfYoneda.map b) := by
  simp only [pullbackCompIso, Limits.pullback.lift_fst]

@[reassoc (attr := simp)]
theorem pullbackCompIso_inv_snd :
    (pullbackCompIso P a b).inv ≫
        Limits.pullback.snd P.projection (fppfYoneda.map (a ≫ b)) =
      Limits.pullback.snd (Limits.pullback.snd P.projection (fppfYoneda.map b))
        (fppfYoneda.map a) := by
  simp only [pullbackCompIso, Limits.pullback.lift_snd]

end

end FppfTorsor

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T T' T'' : Scheme.{u}}

@[simp]
theorem id_iso_hom (P : ActionTorsor G U T) : (𝟙 P : P ⟶ P).iso.hom = 𝟙 P.P :=
  rfl

@[simp]
theorem comp_iso_hom {P Q R : ActionTorsor G U T} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).iso.hom = f.iso.hom ≫ g.iso.hom :=
  rfl

/-- Base change of an equivariant torsor along a morphism of schemes.  The torsor, its action
and its local triviality are pulled back, and the map to `U` is precomposed with the projection
to the original torsor. -/
@[reducible]
noncomputable def pullbackObj (b : T' ⟶ T) (P : ActionTorsor G U T) : ActionTorsor G U T' where
  toFppfTorsor := P.toFppfTorsor.pullbackTorsor b
  target := Limits.pullback.fst P.projection (fppfYoneda.map b) ≫ P.target
  target_equivariant := by
    rw [FppfTorsor.pullbackTorsor_smul, ← Category.assoc, FppfTorsor.pullbackSmul_fst,
      Category.assoc, P.target_equivariant, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp]

@[simp]
theorem pullbackObj_target (b : T' ⟶ T) (P : ActionTorsor G U T) :
    (pullbackObj b P).target =
      Limits.pullback.fst P.projection (fppfYoneda.map b) ≫ P.target :=
  rfl

/-- Base change of equivariant torsors along a fixed morphism of schemes is a functor of
quotient groupoids. -/
@[reducible]
noncomputable def pullbackFunctor (b : T' ⟶ T) :
    ActionTorsor G U T ⥤ ActionTorsor G U T' where
  obj P := pullbackObj b P
  map {P Q} f :=
    { iso := FppfTorsor.pullbackMapIso b f.iso f.over
      over := FppfTorsor.pullbackMap_snd b f.iso.hom f.over
      equivariant := FppfTorsor.pullbackSmul_pullbackMap b f.iso.hom f.over f.equivariant
      target := by
        rw [pullbackObj_target, pullbackObj_target, FppfTorsor.pullbackMapIso_hom,
          ← Category.assoc, FppfTorsor.pullbackMap_fst, Category.assoc, f.target] }
  map_id P := by
    apply Hom.ext
    exact FppfTorsor.pullbackMap_id b (by simp)
  map_comp f g := by
    apply Hom.ext
    exact FppfTorsor.pullbackMap_comp b f.iso.hom g.iso.hom f.over g.over
      (by rw [Category.assoc, g.over, f.over])

@[simp]
theorem pullbackFunctor_map_iso_hom (b : T' ⟶ T) {P Q : ActionTorsor G U T} (f : P ⟶ Q) :
    ((pullbackFunctor (U := U) b).map f).iso.hom =
      FppfTorsor.pullbackMap b f.iso.hom f.over :=
  rfl

/-- Base change along the identity is the identity, on objects. -/
noncomputable def pullbackIdIsoApp (P : ActionTorsor G U T) : pullbackObj (𝟙 T) P ≅ P :=
  asIso
    { iso := FppfTorsor.pullbackIdIso P.toFppfTorsor
      over := by
        rw [FppfTorsor.pullbackIdIso_hom, Limits.pullback.condition]
        simp
      equivariant := FppfTorsor.pullbackSmul_pullbackIdIso P.toFppfTorsor
      target := rfl }

/-- Base change along the identity is naturally isomorphic to the identity functor. -/
noncomputable def pullbackFunctorIdIso :
    pullbackFunctor (U := U) (𝟙 T) ≅ 𝟭 (ActionTorsor G U T) :=
  NatIso.ofComponents pullbackIdIsoApp (fun {P Q} f ↦ by
    apply Hom.ext
    exact FppfTorsor.pullbackMap_fst (𝟙 T) f.iso.hom f.over)

/-- Base change along a composite is the composite of the base changes, on objects. -/
noncomputable def pullbackCompIsoApp (a : T'' ⟶ T') (b : T' ⟶ T) (P : ActionTorsor G U T) :
    pullbackObj (a ≫ b) P ≅ pullbackObj a (pullbackObj b P) :=
  asIso
    { iso := FppfTorsor.pullbackCompIso P.toFppfTorsor a b
      over := FppfTorsor.pullbackCompIso_hom_snd P.toFppfTorsor a b
      equivariant := FppfTorsor.pullbackSmul_pullbackCompIso P.toFppfTorsor a b
      target := FppfTorsor.pullbackCompIso_hom_fst_fst_assoc P.toFppfTorsor a b P.target }

/-- Base change along a composite is naturally isomorphic to the composite of base changes. -/
noncomputable def pullbackFunctorCompIso (a : T'' ⟶ T') (b : T' ⟶ T) :
    pullbackFunctor (U := U) (a ≫ b) ≅
      pullbackFunctor (U := U) b ⋙ pullbackFunctor (U := U) a :=
  NatIso.ofComponents (pullbackCompIsoApp a b) (fun {P Q} f ↦ by
    apply Hom.ext
    exact FppfTorsor.pullbackCompIso_naturality a b f.iso.hom f.over
      (FppfTorsor.pullbackMap_snd b f.iso.hom f.over) f.over)

@[simp]
theorem pullbackIdIsoApp_hom_iso_hom (P : ActionTorsor G U T) :
    (pullbackIdIsoApp P).hom.iso.hom =
      Limits.pullback.fst P.projection (fppfYoneda.map (𝟙 T)) :=
  rfl

@[simp]
theorem pullbackCompIsoApp_hom_iso_hom (a : T'' ⟶ T') (b : T' ⟶ T)
    (P : ActionTorsor G U T) :
    (pullbackCompIsoApp a b P).hom.iso.hom =
      (FppfTorsor.pullbackCompIso P.toFppfTorsor a b).hom :=
  rfl

@[simp]
theorem pullbackFunctorIdIso_hom_app (P : ActionTorsor G U T) :
    (pullbackFunctorIdIso (U := U)).hom.app P = (pullbackIdIsoApp P).hom :=
  rfl

@[simp]
theorem pullbackFunctorCompIso_hom_app (a : T'' ⟶ T') (b : T' ⟶ T)
    (P : ActionTorsor G U T) :
    (pullbackFunctorCompIso (U := U) a b).hom.app P = (pullbackCompIsoApp a b P).hom :=
  rfl

/-- The underlying sheaf map of an equality of base-changed torsors. -/
theorem eqToHom_iso_hom {P Q : ActionTorsor G U T} (h : P = Q) (h' : P.P = Q.P) :
    (eqToHom h).iso.hom = eqToHom h' := by
  subst h
  rfl

/-- The comparison natural transformation attached to an equality of base-change morphisms is
the canonical map of fibre products. -/
theorem eqToHom_app_iso_hom {b₁ b₂ : T' ⟶ T} (hb : b₁ = b₂)
    (h : pullbackFunctor (U := U) b₁ = pullbackFunctor b₂) (P : ActionTorsor G U T) :
    ((eqToHom h).app P).iso.hom =
      Limits.pullback.lift (Limits.pullback.fst P.projection (fppfYoneda.map b₁))
        (Limits.pullback.snd P.projection (fppfYoneda.map b₁))
        (by rw [Limits.pullback.condition, hb]) := by
  subst hb
  rw [eqToHom_refl, NatTrans.id_app, Limits.pullback.lift_fst_snd]
  rfl

/-- Unit coherence of base change: pulling back along `c ≫ 𝟙` is the identity comparison
followed by pullback along `c`. -/
theorem pullbackFunctor_comp_id (c : T' ⟶ T) :
    (pullbackFunctorCompIso (U := U) c (𝟙 T)).hom ≫
        Functor.whiskerRight (pullbackFunctorIdIso (U := U)).hom (pullbackFunctor c) ≫
          (Functor.leftUnitor _).hom =
      eqToHom (congrArg (pullbackFunctor (U := U)) (Category.comp_id c)) := by
  ext P
  apply Hom.ext
  rw [eqToHom_app_iso_hom (Category.comp_id c)]
  apply Limits.pullback.hom_ext <;>
    simp [FppfTorsor.pullbackMap, Limits.pullback.lift_fst, Limits.pullback.lift_snd]


/-- Unit coherence of base change: pulling back along `𝟙 ≫ c` is pullback along `c` followed by
the identity comparison. -/
theorem pullbackFunctor_id_comp (c : T' ⟶ T) :
    (pullbackFunctorCompIso (U := U) (𝟙 T') c).hom ≫
        Functor.whiskerLeft (pullbackFunctor (U := U) c) (pullbackFunctorIdIso (U := U)).hom ≫
          (Functor.rightUnitor _).hom =
      eqToHom (congrArg (pullbackFunctor (U := U)) (Category.id_comp c)) := by
  ext P
  apply Hom.ext
  rw [eqToHom_app_iso_hom (Category.id_comp c)]
  apply Limits.pullback.hom_ext <;>
    simp [Limits.pullback.lift_fst, Limits.pullback.lift_snd]

/-- The underlying sheaf map of the inverse of an isomorphism of equivariant torsors. -/
theorem inv_iso_hom {P Q : ActionTorsor G U T} (e : P ≅ Q) :
    e.inv.iso.hom = e.hom.iso.inv := by
  have h : e.hom.iso.hom ≫ e.inv.iso.hom = 𝟙 P.P :=
    congrArg (fun f ↦ Hom.iso f |>.hom) e.hom_inv_id
  calc e.inv.iso.hom = (e.hom.iso.inv ≫ e.hom.iso.hom) ≫ e.inv.iso.hom := by simp
    _ = e.hom.iso.inv := by rw [Category.assoc, h, Category.comp_id]

@[simp]
theorem pullbackCompIsoApp_inv_iso_hom (a : T'' ⟶ T') (b : T' ⟶ T)
    (P : ActionTorsor G U T) :
    (pullbackCompIsoApp a b P).inv.iso.hom =
      (FppfTorsor.pullbackCompIso P.toFppfTorsor a b).inv := by
  rw [inv_iso_hom]
  rfl

@[simp]
theorem pullbackFunctorCompIso_inv_app (a : T'' ⟶ T') (b : T' ⟶ T)
    (P : ActionTorsor G U T) :
    (pullbackFunctorCompIso (U := U) a b).inv.app P = (pullbackCompIsoApp a b P).inv :=
  rfl

/-- Associativity coherence for base change of equivariant torsors. -/
theorem pullbackFunctor_assoc {T₀ T₁ T₂ T₃ : Scheme.{u}} (p : T₁ ⟶ T₀) (q : T₂ ⟶ T₁)
    (r : T₃ ⟶ T₂) :
    (pullbackFunctorCompIso (U := U) r (q ≫ p)).hom ≫
        Functor.whiskerRight (pullbackFunctorCompIso (U := U) q p).hom
            (pullbackFunctor (U := U) r) ≫
          (Functor.associator _ _ _).hom ≫
            Functor.whiskerLeft (pullbackFunctor (U := U) p)
                (pullbackFunctorCompIso (U := U) r q).inv ≫
              (pullbackFunctorCompIso (U := U) (r ≫ q) p).inv =
      eqToHom (congrArg (pullbackFunctor (U := U)) (Category.assoc r q p).symm) := by
  ext P
  apply Hom.ext
  rw [eqToHom_app_iso_hom (Category.assoc r q p).symm]
  apply Limits.pullback.hom_ext <;>
    simp [FppfTorsor.pullbackMap, FppfTorsor.pullbackCompIso, Limits.pullback.lift_fst,
      Limits.pullback.lift_snd, Limits.pullback.lift_fst_assoc]

/-- Base change of equivariant torsors, assembled into a contravariant pseudofunctor from
schemes to categories.  Its fibre over a scheme `T` is the groupoid `ActionTorsor G U T`. -/
noncomputable def pullbackPseudofunctor (G : AlgebraicSpaceGroup.{u})
    (U : AlgebraicSpaceAction G) :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u + 1, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (ActionTorsor G U X.unop))
    (fun f ↦ (pullbackFunctor (U := U) f.unop).toCatHom)
    (fun _ ↦ Cat.Hom.isoMk (pullbackFunctorIdIso (U := U)))
    (fun f g ↦ Cat.Hom.isoMk (pullbackFunctorCompIso (U := U) g.unop f.unop))
    (fun f g h ↦ by
      ext1
      simpa using! pullbackFunctor_assoc (U := U) f.unop g.unop h.unop)
    (fun f ↦ by
      ext1
      simpa using! pullbackFunctor_comp_id (U := U) f.unop)
    (fun f ↦ by
      ext1
      simpa using! pullbackFunctor_id_comp (U := U) f.unop)

/-- Every fibre of the base-change pseudofunctor is the groupoid of equivariant torsors. -/
noncomputable instance (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) :
    (pullbackPseudofunctor G U).IsGroupoidValued where
  fiber T := by
    change IsGroupoid (ActionTorsor G U T)
    infer_instance

@[simp]
theorem pullbackPseudofunctor_obj (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (T : Scheme.{u}) :
    (pullbackPseudofunctor G U).obj ⟨Opposite.op T⟩ = Cat.of (ActionTorsor G U T) :=
  rfl

end ActionTorsor

end GromovWitten.AlgebraicGeometry
