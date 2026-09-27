/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.RelativeProj
/-!
# Gluing relative-Proj base change

Compatible degreewise scalar-extension maps on the affine opens of a new base induce a
morphism of relative Proj schemes. When the original base is affine, the resulting square
is cartesian even when the new base is non-affine. The proof glues the affine Proj
base-change theorem; its input consists of graded algebra maps and tensor-product
properties, not a supplied cartesian square of schemes.
-/

open CategoryTheory Limits AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Cover.RelativeGluingData
variable {X S Y : Scheme.{u}} {𝒰 : X.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  (d : 𝒰.RelativeGluingData) (b : X ⟶ S) (f : Y ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- A square out of a relative gluing is cartesian if its chart squares are cartesian. -/
lemma isPullback_of_charts (t : d.glued ⟶ Y)
    (h : ∀ i, IsPullback (d.natTrans.app i) (colimit.ι d.functor i ≫ t)
      (𝒰.f i ≫ b) f) : IsPullback d.toBase t b f := by
  apply Scheme.isPullback_of_openCover _ _ _ _ 𝒰
  intro i
  let e := (d.isPullback_natTrans_ι_toBase i).flip.isoPullback
  apply (h i).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [e, Scheme.Cover.pullbackHom]
  · change colimit.ι d.functor i ≫ t = e.hom ≫ pullback.fst d.toBase (𝒰.f i) ≫ t
    exact (d.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_fst_assoc t |>.symm
  · simp
  · simp
end AlgebraicGeometry.Scheme.Cover.RelativeGluingData

namespace GromovWitten.AlgebraicGeometry.RelativeProj
open ProjBaseChange ReesBlowupOfEq
-- The directed affine-cover indices are definitionally the affine opens, as in RelativeProj.
set_option backward.isDefEq.respectTransparency false
variable {X X' : Scheme.{u}} [IsAffine X] (b : X' ⟶ X)
  (𝒜 : GradedAlgebraData X) (ℬ : GradedAlgebraData X')

local instance : Algebra Γ(X, ⊤) (𝒜.ring (topIndex X)) := 𝒜.algebra (topIndex X)
local instance : GradedAlgebra (𝒜.grading (topIndex X)) := 𝒜.gradedAlgebra (topIndex X)

/-- Compatible affine scalar extensions of a graded algebra over an affine base. -/
structure AffineBaseChangeData where
  app : ∀ U : X'.affineOpens, 𝒜.grading (topIndex X) →+*ᵍ ℬ.grading U
  naturality : ∀ {U V : X'.affineOpens} (h : U ≤ V),
    (ℬ.map h).comp (app V) = app U
  isBaseChange : ∀ U, IsGradedBaseChangeAlong
    (b.appLE ⊤ U.1 (by simp)).hom
    (𝒜.grading (topIndex X)) (ℬ.grading U) (app U)

namespace AffineBaseChangeData
variable {b 𝒜 ℬ} (D : AffineBaseChangeData b 𝒜 ℬ)
set_option backward.isDefEq.respectTransparency false in
/-- The affine Proj maps form a cocone over the graded algebra on the new base. -/
def cocone : Cocone (gluingData X' ℬ).functor where
  pt := Proj (𝒜.grading (topIndex X))
  ι :=
    { app U := Proj.map (D.app U) (D.isBaseChange U).irrelevant_le
      naturality {U V} h := by
        dsimp [gluingData, gluingFunctor]
        rw [← Proj.map_comp, projMap_congr (D.naturality (leOfHom h))]
        simp }

/-- The induced map to the whole-base affine Proj model. -/
def mapToAffineProj : relativeProj X' ℬ ⟶ Proj (𝒜.grading (topIndex X)) :=
  colimit.desc _ D.cocone

@[reassoc (attr := simp)]
lemma affineι_mapToAffineProj (U : X'.affineOpens) :
    affineι X' ℬ U ≫ D.mapToAffineProj =
      Proj.map (D.app U) (D.isBaseChange U).irrelevant_le :=
  colimit.ι_desc _ _

/-- The affine ring calculation gives a cartesian square over each new-base chart. -/
lemma isPullback_chart (U : X'.affineOpens) :
    IsPullback (gluingApp X' ℬ U)
      (Proj.map (D.app U) (D.isBaseChange U).irrelevant_le)
      (U.1.ι ≫ b)
      (projection (𝒜.grading (topIndex X)) ≫ (isAffineOpen_top X).fromSpec) := by
  have he : IsIso (isAffineOpen_top X).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have H : IsPullback
      (Spec.map (b.appLE ⊤ U.1 (by simp))) U.2.isoSpec.inv
      (isAffineOpen_top X).fromSpec (U.1.ι ≫ b) := by
    apply IsPullback.of_vert_isIso
    constructor
    rw [IsAffineOpen.SpecMap_appLE_fromSpec b (isAffineOpen_top X) U.2]
    simp only [IsAffineOpen.fromSpec, Category.assoc]
  exact ((D.isBaseChange U).isPullback.paste_vert H).flip

/-- Gluing the chart squares yields base change of the whole affine Proj model. -/
lemma isPullback_mapToAffineProj :
    IsPullback (toBase X' ℬ) D.mapToAffineProj b
      (projection (𝒜.grading (topIndex X)) ≫ (isAffineOpen_top X).fromSpec) := by
  apply (gluingData X' ℬ).isPullback_of_charts
  intro U
  change IsPullback (gluingApp X' ℬ U) (affineι X' ℬ U ≫ D.mapToAffineProj)
    (U.1.ι ≫ b) _
  rw [affineι_mapToAffineProj]
  exact D.isPullback_chart U

/-- The induced morphism between the relative Proj schemes. -/
def map : relativeProj X' ℬ ⟶ relativeProj X 𝒜 :=
  D.mapToAffineProj ≫ (affineιIso X 𝒜).hom

/-- Relative Proj commutes with the given scalar extension over an affine original base. -/
lemma isPullback_map : IsPullback D.map (toBase X' ℬ) (toBase X 𝒜) b := by
  apply D.isPullback_mapToAffineProj.flip.of_iso
    (Iso.refl _) (affineιIso X 𝒜) (Iso.refl _) (Iso.refl _)
  · simp [map]
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, affineιIso_hom]
    simpa only [gluingApp, Category.assoc, IsAffineOpen.isoSpec_inv_ι] using
      (isPullback_affine X 𝒜 (topIndex X)).w
  · simp

/-- The canonical identification with the scheme-theoretic base change. -/
def pullbackIso : relativeProj X' ℬ ≅ pullback (toBase X 𝒜) b :=
  D.isPullback_map.isoPullback

@[reassoc (attr := simp)]
lemma pullbackIso_hom_fst : D.pullbackIso.hom ≫ pullback.fst _ _ = D.map :=
  D.isPullback_map.isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma pullbackIso_hom_snd : D.pullbackIso.hom ≫ pullback.snd _ _ = toBase X' ℬ :=
  D.isPullback_map.isoPullback_hom_snd

end AffineBaseChangeData
end GromovWitten.AlgebraicGeometry.RelativeProj
