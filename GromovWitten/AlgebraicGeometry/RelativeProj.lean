/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.ProjBaseChange
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ReesBlowupGlobal

/-!
# Relative `Proj` over a scheme

A *quasi-coherent graded algebra* on a scheme `X` is given affine-locally: a graded algebra
`𝒜 U` over the section ring of every affine open `U`, together with graded transition maps
`𝒜 V → 𝒜 U` for `U ≤ V` which are functorial and which exhibit `𝒜 U` as the base change of
`𝒜 V` along the restriction map of section rings (`GradedAlgebraData`).  The relative `Proj`
of such data is glued from the affine `Proj`s of the `𝒜 U` using Mathlib's relative gluing
along the locally directed cover of `X` by its affine opens, exactly as the global Rees blowup
is glued from affine Rees blowups in `ReesBlowupGlobal`; the cartesian transition squares are
supplied by the general base change theorem for `Proj` of `ProjBaseChange`.

The result is a scheme `relativeProj X 𝒜` with a structure morphism `toBase X 𝒜` to `X` whose
restriction to every affine open `U` is the affine `Proj (𝒜 U)` (`isPullback_affine`); it is
proper over `X` when every `𝒜 U` is of finite type over its degree-zero part and has degree-zero
part equal to the section ring (`toBase_isProper`).
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry

open ProjBaseChange GlobalBlowup ReesBlowupOfEq

universe u

noncomputable section

/-- A quasi-coherent graded algebra on a scheme, given affine-locally: a graded algebra over
the section ring of every affine open, with functorial graded transition maps which are base
changes along the restriction maps of section rings. -/
structure GradedAlgebraData (X : Scheme.{u}) where
  /-- The graded ring over an affine open. -/
  ring : X.affineOpens → Type u
  [commRing : ∀ U, CommRing (ring U)]
  [algebra : ∀ U, Algebra Γ(X, U.1) (ring U)]
  /-- The grading. -/
  grading : ∀ U, ℕ → Submodule Γ(X, U.1) (ring U)
  [gradedAlgebra : ∀ U, GradedAlgebra (grading U)]
  /-- The transition maps. -/
  map : ∀ {U V : X.affineOpens}, U ≤ V → (grading V →+*ᵍ grading U)
  map_id : ∀ U, map (le_refl U) = GradedRingHom.id _
  map_comp : ∀ {U V W : X.affineOpens} (hUV : U ≤ V) (hVW : V ≤ W),
    map (hUV.trans hVW) = (map hUV).comp (map hVW)
  /-- The transition maps are base changes along the restriction maps. -/
  isBaseChange : ∀ {U V : X.affineOpens} (h : U ≤ V),
    IsGradedBaseChangeAlong (res X h) (grading V) (grading U) (map h)

attribute [instance] GradedAlgebraData.commRing GradedAlgebraData.algebra
  GradedAlgebraData.gradedAlgebra

namespace RelativeProj

/- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
type of affine opens; as in Mathlib's own development of that cover, the unifier is told not to
respect transparency in this section. -/
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u}) (𝒜 : GradedAlgebraData X)

theorem irrelevant_le {U V : X.affineOpens} (h : U ≤ V) :
    HomogeneousIdeal.irrelevant (𝒜.grading U) ≤
      HomogeneousIdeal.map (𝒜.map h) (HomogeneousIdeal.irrelevant (𝒜.grading V)) :=
  (𝒜.isBaseChange h).irrelevant_le

/-- The gluing functor: the affine `Proj` of each affine open, with the transition maps. -/
def gluingFunctor : X.affineOpens ⥤ Scheme.{u} where
  obj U := Proj (𝒜.grading U)
  map {U V} h := Proj.map (𝒜.map (leOfHom h)) (irrelevant_le X 𝒜 (leOfHom h))
  map_id U := by
    change Proj.map (𝒜.map (le_refl U)) (irrelevant_le X 𝒜 (le_refl U)) =
      𝟙 (Proj (𝒜.grading U))
    rw [projMap_congr (𝒜.map_id U)]
    exact Proj.map_id (𝒜 := 𝒜.grading U)
  map_comp {U V W} f g := by
    change Proj.map (𝒜.map ((leOfHom f).trans (leOfHom g))) _ =
      Proj.map (𝒜.map (leOfHom f)) (irrelevant_le X 𝒜 (leOfHom f)) ≫
        Proj.map (𝒜.map (leOfHom g)) (irrelevant_le X 𝒜 (leOfHom g))
    rw [projMap_congr (𝒜.map_comp (leOfHom f) (leOfHom g))]
    exact Proj.map_comp (𝒜.map (leOfHom g)) (𝒜.map (leOfHom f)) (irrelevant_le X 𝒜 (leOfHom g))
      (irrelevant_le X 𝒜 (leOfHom f))

/-- The structure map of the affine `Proj` of an affine open to that open. -/
def gluingApp (U : X.affineOpens) :
    (gluingFunctor X 𝒜).obj U ⟶ X.directedAffineCover.functorOfLocallyDirected.obj U :=
  projection (𝒜.grading U) ≫ (isAffineOpen X U).isoSpec.inv

/-- The structure maps form a natural transformation to the cover. -/
def gluingNatTrans : gluingFunctor X 𝒜 ⟶ X.directedAffineCover.functorOfLocallyDirected where
  app := gluingApp X 𝒜
  naturality {U V} h := by
    rw [← homOfLE_leOfHom h, Scheme.Cover.functorOfLocallyDirected_map,
      Scheme.directedAffineCover_trans]
    change Proj.map (𝒜.map (leOfHom h)) _ ≫
        projection (𝒜.grading V) ≫ (isAffineOpen X V).isoSpec.inv =
      (projection (𝒜.grading U) ≫ (isAffineOpen X U).isoSpec.inv) ≫ X.homOfLE (leOfHom h)
    rw [← Category.assoc, (𝒜.isBaseChange (leOfHom h)).map_projection, Category.assoc,
      Category.assoc, specMap_res_comp_isoSpec_inv]

/-- The transition squares are cartesian. -/
theorem gluingNatTrans_equifibered : (gluingNatTrans X 𝒜).Equifibered := by
  intro U V h
  rw [← homOfLE_leOfHom h, Scheme.Cover.functorOfLocallyDirected_map,
    Scheme.directedAffineCover_trans]
  change IsPullback (Proj.map (𝒜.map (leOfHom h)) _)
    (projection (𝒜.grading U) ≫ (isAffineOpen X U).isoSpec.inv)
    (projection (𝒜.grading V) ≫ (isAffineOpen X V).isoSpec.inv) (X.homOfLE (leOfHom h))
  exact (𝒜.isBaseChange (leOfHom h)).isPullback.paste_vert (isPullback_specMap_res X (leOfHom h))

/-- The relative gluing datum of the affine `Proj`s over the affine opens. -/
def gluingData : X.directedAffineCover.RelativeGluingData where
  functor := gluingFunctor X 𝒜
  natTrans := gluingNatTrans X 𝒜
  equifibered := gluingNatTrans_equifibered X 𝒜

/-- The relative `Proj` of a quasi-coherent graded algebra on `X`. -/
abbrev relativeProj : Scheme.{u} := (gluingData X 𝒜).glued

/-- The structure morphism `Proj_X 𝒜 → X`. -/
def toBase : relativeProj X 𝒜 ⟶ X := (gluingData X 𝒜).toBase

/-- The affine `Proj` of an affine open embeds into the relative `Proj`. -/
def affineι (U : X.affineOpens) : Proj (𝒜.grading U) ⟶ relativeProj X 𝒜 :=
  colimit.ι (gluingData X 𝒜).functor U

instance affineι_isOpenImmersion (U : X.affineOpens) : IsOpenImmersion (affineι X 𝒜 U) := by
  have := (gluingData X 𝒜).cover.map_prop U
  rwa [Scheme.Cover.RelativeGluingData.cover_f] at this

/-- Over every affine open, the relative `Proj` is the affine `Proj`. -/
theorem isPullback_affine (U : X.affineOpens) :
    IsPullback (projection (𝒜.grading U) ≫ (isAffineOpen X U).isoSpec.inv) (affineι X 𝒜 U)
      U.1.ι (toBase X 𝒜) :=
  (gluingData X 𝒜).isPullback_natTrans_ι_toBase U

/-- The affine pieces cover the relative `Proj`. -/
theorem iSup_opensRange_affineι : ⨆ U : X.affineOpens, (affineι X 𝒜 U).opensRange = ⊤ :=
  (gluingData X 𝒜).cover.iSup_opensRange

/-- A property of morphisms which respects isomorphisms holds for the structure morphism over an
affine open if and only if it holds for the affine `Proj`. -/
theorem property_restrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : X.affineOpens) :
    P (toBase X 𝒜 ∣_ U.1.ι.opensRange) ↔
      P (projection (𝒜.grading U) ≫ (isAffineOpen X U).isoSpec.inv) := by
  rw [P.arrow_mk_iso_iff (morphismRestrictOpensRange (toBase X 𝒜) U.1.ι)]
  exact (P.arrow_mk_iso_iff (Arrow.isoMk (isPullback_affine X 𝒜 U).flip.isoPullback
    (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id]
      exact (isPullback_affine X 𝒜 U).flip.isoPullback_hom_snd))).symm

theorem property_restrict_iff' (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : X.affineOpens) :
    P (toBase X 𝒜 ∣_ U.1) ↔
      P (projection (𝒜.grading U) ≫ (isAffineOpen X U).isoSpec.inv) := by
  rw [← property_restrict_iff X 𝒜 P U, Scheme.Opens.opensRange_ι]

/-- The relative `Proj` of a graded algebra which is affine-locally of finite type over its
degree-zero part, with degree-zero part the section ring, is proper over `X`. -/
theorem toBase_isProper [∀ U, Algebra.FiniteType (𝒜.grading U 0) (𝒜.ring U)]
    (h0 : ∀ U, Function.Bijective (algebraMap Γ(X, U.1) (𝒜.grading U 0))) :
    IsProper (toBase X 𝒜) := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsProper)
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X)).mpr fun U ↦ ?_
  rw [property_restrict_iff' X 𝒜 @IsProper U]
  have : IsProper (projection (𝒜.grading U)) := projection_isProper (𝒜.grading U) (h0 U)
  infer_instance

end RelativeProj

end

end GromovWitten.AlgebraicGeometry
