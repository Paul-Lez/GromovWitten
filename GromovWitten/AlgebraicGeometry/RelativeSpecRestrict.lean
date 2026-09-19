/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.RelativeSpec
import GromovWitten.AlgebraicGeometry.Cones.NormalConeGlobal

/-!
# Restriction of a relative `Spec` to an open subscheme

Let `𝒜` be a quasi-coherent algebra on a scheme `X` (an `AlgebraData X`, see `RelativeSpec`) and
let `V : X.Opens` be an open subscheme.  Every affine open `W` of `V` is an affine open
`V.ι ''ᵁ W` of `X` with the *same* ring of sections, so the affine-local data of `𝒜` restricts to
a quasi-coherent algebra `𝒜.restrict V` on `V` (`AlgebraData.restrict`).

The relative `Spec` of the restriction is the restriction of the relative `Spec`: the affine
pieces of `relativeSpec V (𝒜.restrict V)` are literally the affine pieces of `relativeSpec X 𝒜`
belonging to affine opens contained in `V`, so they assemble into a comparison morphism
`RelativeSpec.restrictι` which lies over `V.ι` (`RelativeSpec.restrictι_toBase`) and is an open
immersion onto the preimage of `V` (`RelativeSpec.isOpenImmersion_restrictι`,
`RelativeSpec.opensRange_restrictι`).  The resulting square is cartesian
(`RelativeSpec.isPullback_restrict`), i.e. `Spec_V (𝒜|_V) = Spec_X 𝒜 ×_X V`.

As an application, quasi-coherent ideal sheaves restrict to open subschemes
(`Scheme.IdealSheafData.restrict`) compatibly with the associated graded algebra, so the global
normal cone of the restricted ideal sheaf is the base change of the global normal cone
(`NormalCone.isPullback_restrict`).
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry

open GlobalBlowup

universe u

noncomputable section

variable {X : Scheme.{u}} (𝒜 : AlgebraData X) (V : X.Opens)

/-! ### Affine opens of an open subscheme -/

namespace RelativeSpec

/-- An affine open of an open subscheme `V` of `X`, viewed as an affine open of `X`. -/
def imageAffineOpen (W : V.toScheme.affineOpens) : X.affineOpens :=
  ⟨V.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion V.ι⟩

/-- The underlying open of the image of an affine open of `V`. -/
theorem imageAffineOpen_coe (W : V.toScheme.affineOpens) :
    (imageAffineOpen V W).1 = V.ι ''ᵁ W.1 :=
  rfl

/-- Passing to the image in `X` is monotone. -/
theorem imageAffineOpen_mono {W₁ W₂ : V.toScheme.affineOpens} (h : W₁ ≤ W₂) :
    imageAffineOpen V W₁ ≤ imageAffineOpen V W₂ :=
  V.ι.image_mono h

/-- The image of an affine open of `V` is contained in `V`. -/
theorem imageAffineOpen_le (W : V.toScheme.affineOpens) : (imageAffineOpen V W).1 ≤ V :=
  V.ι_image_le W.1

/-- The canonical morphism from the spectrum of the sections of an affine open `W` of an open
subscheme `V` of `X` is the canonical morphism of the image of `W` in `X`. -/
theorem fromSpec_image {W : V.toScheme.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ V.ι = (hW.image_of_isOpenImmersion V.ι).fromSpec := by
  have hle : W ≤ V.ι ⁻¹ᵁ (V.ι ''ᵁ W) := (V.ι.preimage_image_eq W).ge
  have hspec : Spec.map (V.ι.appLE (V.ι ''ᵁ W) W hle) = 𝟙 _ := by
    rw [← Scheme.Hom.appIso_hom' V.ι W, Scheme.Opens.ι_appIso]
    exact Spec.map_id _
  have key := IsAffineOpen.SpecMap_appLE_fromSpec V.ι (hW.image_of_isOpenImmersion V.ι) hW hle
  rw [hspec] at key
  exact key.symm.trans (Category.id_comp _)

/-- The canonical morphism of an affine open of an open subscheme is the canonical morphism of
the corresponding affine open of `X`. -/
theorem fromSpec_imageAffineOpen (W : V.toScheme.affineOpens) :
    (isAffineOpen V.toScheme W).fromSpec ≫ V.ι =
      (isAffineOpen X (imageAffineOpen V W)).fromSpec :=
  fromSpec_image V W.2

/-- Every point of a scheme lies in an affine open. -/
theorem exists_affineOpen_mem {Y : Scheme.{u}} (y : Y) : ∃ W : Y.affineOpens, y ∈ W.1 := by
  have h : y ∈ (⊤ : Y.Opens) := trivial
  rw [← iSup_affineOpens_eq_top Y] at h
  simpa using h

end RelativeSpec

/-! ### Restriction of quasi-coherent algebra data -/

open RelativeSpec in
/-- The restriction of a quasi-coherent algebra on `X` to an open subscheme `V`: the ring over an
affine open `W` of `V` is the ring of `𝒜` over the affine open `V.ι ''ᵁ W` of `X` (the two opens
have the same ring of sections). -/
def AlgebraData.restrict : AlgebraData V.toScheme where
  ring W := 𝒜.ring (imageAffineOpen V W)
  commRing W := 𝒜.commRing (imageAffineOpen V W)
  algebra W := 𝒜.algebra (imageAffineOpen V W)
  map h := 𝒜.map (imageAffineOpen_mono V h)
  map_id _ := 𝒜.map_id _
  map_comp _ _ := 𝒜.map_comp _ _
  isPushout h := 𝒜.isPushout (imageAffineOpen_mono V h)

open RelativeSpec in
/-- The ring of the restricted algebra over an affine open of `V`. -/
theorem AlgebraData.restrict_ring (W : V.toScheme.affineOpens) :
    (𝒜.restrict V).ring W = 𝒜.ring (imageAffineOpen V W) :=
  rfl

open RelativeSpec in
/-- The transition maps of the restricted algebra. -/
theorem AlgebraData.restrict_map {W₁ W₂ : V.toScheme.affineOpens} (h : W₁ ≤ W₂) :
    (𝒜.restrict V).map h = 𝒜.map (imageAffineOpen_mono V h) :=
  rfl

/-! ### The comparison morphism of relative spectra -/

namespace RelativeSpec

/- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
type of affine opens; as in Mathlib's own development of that cover, the unifier is told not to
respect transparency in this section. -/
set_option backward.isDefEq.respectTransparency false

/-- The affine pieces of the relative `Spec` of the restriction, mapped into the relative `Spec`
over `X`, form a cocone. -/
def restrictCocone : Cocone (gluingData V.toScheme (𝒜.restrict V)).functor where
  pt := relativeSpec X 𝒜
  ι :=
    { app W := affineι X 𝒜 (imageAffineOpen V W)
      naturality := by
        intro W₁ W₂ h
        change Spec.map (CommRingCat.ofHom (𝒜.map (imageAffineOpen_mono V (leOfHom h)))) ≫
          affineι X 𝒜 (imageAffineOpen V W₂) = affineι X 𝒜 (imageAffineOpen V W₁) ≫ 𝟙 _
        rw [Category.comp_id]
        exact colimit.w (gluingData X 𝒜).functor
          (homOfLE (imageAffineOpen_mono V (leOfHom h))) }

/-- The comparison morphism `Spec_V (𝒜|_V) ⟶ Spec_X 𝒜`. -/
def restrictι : relativeSpec V.toScheme (𝒜.restrict V) ⟶ relativeSpec X 𝒜 :=
  colimit.desc _ (restrictCocone 𝒜 V)

/-- The comparison morphism restricted to an affine piece is the corresponding affine piece
over `X`. -/
@[reassoc]
theorem affineι_restrictι (W : V.toScheme.affineOpens) :
    affineι V.toScheme (𝒜.restrict V) W ≫ restrictι 𝒜 V = affineι X 𝒜 (imageAffineOpen V W) :=
  colimit.ι_desc (restrictCocone 𝒜 V) W

/-- The structure morphism of an affine piece, composed with the inclusion of the affine open. -/
theorem projection_comp_ι (U : X.affineOpens) :
    projection X 𝒜 U ≫ U.1.ι =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U))) ≫
        (isAffineOpen X U).fromSpec := by
  rw [Category.assoc]
  rfl

/-- The comparison morphism lies over the open immersion `V.ι`. -/
theorem restrictι_toBase :
    restrictι 𝒜 V ≫ toBase X 𝒜 = toBase V.toScheme (𝒜.restrict V) ≫ V.ι := by
  refine colimit.hom_ext fun W ↦ ?_
  change affineι V.toScheme (𝒜.restrict V) W ≫ restrictι 𝒜 V ≫ toBase X 𝒜 =
    affineι V.toScheme (𝒜.restrict V) W ≫ toBase V.toScheme (𝒜.restrict V) ≫ V.ι
  rw [← Category.assoc, affineι_restrictι, affineι_toBase, ← Category.assoc, affineι_toBase,
    projection_comp_ι, projection_comp_ι, Category.assoc, fromSpec_imageAffineOpen]
  rfl

/-! ### The comparison morphism is an open immersion onto the preimage of `V` -/

/-- The preimage of an affine open under the structure morphism is the corresponding affine
piece of the relative `Spec`. -/
theorem toBase_preimage_affineOpen (U : X.affineOpens) :
    toBase X 𝒜 ⁻¹ᵁ U.1 = (affineι X 𝒜 U).opensRange := by
  have h := (gluingData X 𝒜).toBase_preimage_eq_opensRange_ι U
  have h2 : (X.directedAffineCover.f U).opensRange = U.1 := Scheme.Opens.opensRange_ι U.1
  rw [h2] at h
  exact h

/-- The comparison morphism on the affine pieces, evaluated at a point. -/
theorem restrictι_affineι_apply (W : V.toScheme.affineOpens)
    (a : Spec (CommRingCat.of ((𝒜.restrict V).ring W))) :
    restrictι 𝒜 V (affineι V.toScheme (𝒜.restrict V) W a) =
      affineι X 𝒜 (imageAffineOpen V W) a := by
  rw [← Scheme.Hom.comp_apply, affineι_restrictι]
  rfl

/-- The comparison morphism is injective. -/
theorem injective_restrictι : Function.Injective (restrictι 𝒜 V) := by
  intro x y hxy
  have hb : toBase V.toScheme (𝒜.restrict V) x = toBase V.toScheme (𝒜.restrict V) y := by
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← restrictι_toBase,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hxy]
  obtain ⟨W, hW⟩ := exists_affineOpen_mem (toBase V.toScheme (𝒜.restrict V) x)
  have hx : x ∈ toBase V.toScheme (𝒜.restrict V) ⁻¹ᵁ W.1 := hW
  have hy : y ∈ toBase V.toScheme (𝒜.restrict V) ⁻¹ᵁ W.1 := by
    change toBase V.toScheme (𝒜.restrict V) y ∈ W.1
    rw [← hb]
    exact hW
  rw [toBase_preimage_affineOpen] at hx hy
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hbe⟩ := hy
  have hab : a = b := (affineι X 𝒜 (imageAffineOpen V W)).isOpenEmbedding.injective (by
    rw [← restrictι_affineι_apply, ← restrictι_affineι_apply, ha, hbe, hxy])
  rw [← ha, ← hbe, hab]

/-- The comparison morphism is an open immersion. -/
instance isOpenImmersion_restrictι : IsOpenImmersion (restrictι 𝒜 V) := by
  refine IsOpenImmersion.of_openCover_source _ (gluingData V.toScheme (𝒜.restrict V)).cover
    (injective_restrictι 𝒜 V) fun W ↦ ?_
  change IsOpenImmersion (affineι V.toScheme (𝒜.restrict V) W ≫ restrictι 𝒜 V)
  rw [affineι_restrictι]
  infer_instance

/-- The image of the comparison morphism is the preimage of `V`. -/
theorem opensRange_restrictι : (restrictι 𝒜 V).opensRange = toBase X 𝒜 ⁻¹ᵁ V := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    have hz : toBase X 𝒜 (restrictι 𝒜 V z) = V.ι (toBase V.toScheme (𝒜.restrict V) z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, restrictι_toBase]
    have hmem : V.ι (toBase V.toScheme (𝒜.restrict V) z) ∈ V.ι.opensRange := ⟨_, rfl⟩
    rw [Scheme.Opens.opensRange_ι] at hmem
    change toBase X 𝒜 (restrictι 𝒜 V z) ∈ V
    rw [hz]
    exact hmem
  · intro z hz
    have hzV : toBase X 𝒜 z ∈ V.ι.opensRange := by
      rw [Scheme.Opens.opensRange_ι]
      exact hz
    obtain ⟨v, hv⟩ := hzV
    obtain ⟨W, hW⟩ := exists_affineOpen_mem v
    have hmem : z ∈ toBase X 𝒜 ⁻¹ᵁ (imageAffineOpen V W).1 := by
      change toBase X 𝒜 z ∈ V.ι ''ᵁ W.1
      rw [← hv]
      exact ⟨v, hW, rfl⟩
    rw [toBase_preimage_affineOpen] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨affineι V.toScheme (𝒜.restrict V) W a, ?_⟩
    rw [← ha]
    exact restrictι_affineι_apply 𝒜 V W a

/-- The comparison morphism identifies the relative `Spec` over `V` with the preimage of `V` in
the relative `Spec` over `X`. -/
def restrictIso :
    relativeSpec V.toScheme (𝒜.restrict V) ≅ (toBase X 𝒜 ⁻¹ᵁ V).toScheme :=
  IsOpenImmersion.isoOfRangeEq (restrictι 𝒜 V) (toBase X 𝒜 ⁻¹ᵁ V).ι (by
    have h : (restrictι 𝒜 V).opensRange = (toBase X 𝒜 ⁻¹ᵁ V).ι.opensRange := by
      rw [Scheme.Opens.opensRange_ι]
      exact opensRange_restrictι 𝒜 V
    exact congrArg (fun U : (relativeSpec X 𝒜).Opens ↦ (U : Set (relativeSpec X 𝒜))) h)

/-- The comparison isomorphism is compatible with the comparison morphism. -/
@[reassoc (attr := simp)]
theorem restrictIso_hom_ι :
    (restrictIso 𝒜 V).hom ≫ (toBase X 𝒜 ⁻¹ᵁ V).ι = restrictι 𝒜 V := by
  unfold restrictIso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The main theorem: the relative `Spec` of the restricted algebra is the base change of the
relative `Spec` along the open immersion `V.ι`, i.e. `Spec_V (𝒜|_V) = Spec_X 𝒜 ×_X V`. -/
theorem isPullback_restrict :
    IsPullback (toBase V.toScheme (𝒜.restrict V)) (restrictι 𝒜 V) V.ι (toBase X 𝒜) := by
  have hfst : toBase X 𝒜 ∣_ V = (restrictIso 𝒜 V).inv ≫ toBase V.toScheme (𝒜.restrict V) := by
    rw [Iso.eq_inv_comp, ← cancel_mono V.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, restrictIso_hom_ι, restrictι_toBase]
  refine (isPullback_morphismRestrict (toBase X 𝒜) V).of_iso (restrictIso 𝒜 V).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    exact hfst
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← restrictIso_hom_ι 𝒜 V,
      Iso.inv_hom_id_assoc]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

end RelativeSpec

end

/-! ### Restriction of the global normal cone -/

noncomputable section

variable {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.Opens)

open RelativeSpec in
/-- The restriction of a quasi-coherent ideal sheaf to an open subscheme: the ideal over an
affine open `W` of `V` is the ideal over the affine open `V.ι ''ᵁ W` of `X`. -/
def _root_.AlgebraicGeometry.Scheme.IdealSheafData.restrict : V.toScheme.IdealSheafData where
  ideal W := I.ideal (imageAffineOpen V W)
  map_ideal_basicOpen W f :=
    I.map_ideal (imageAffineOpen_mono V (V.toScheme.affineBasicOpen_le f))

open RelativeSpec in
/-- The components of the restricted ideal sheaf. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.restrict_ideal
    (W : V.toScheme.affineOpens) :
    (I.restrict V).ideal W = I.ideal (imageAffineOpen V W) :=
  rfl

namespace NormalCone

/-- The associated graded algebra of the restricted ideal sheaf is the restriction of the
associated graded algebra. -/
theorem algebraData_restrict :
    algebraData V.toScheme (I.restrict V) = (algebraData X I).restrict V :=
  rfl

/-- The comparison morphism `C_{Z ∩ V / V} ⟶ C_{Z / X}` of normal cones. -/
def restrictι : normalCone V.toScheme (I.restrict V) ⟶ normalCone X I :=
  RelativeSpec.restrictι (algebraData X I) V

/-- The comparison morphism of normal cones is an open immersion. -/
instance restrictι_isOpenImmersion : IsOpenImmersion (restrictι I V) :=
  RelativeSpec.isOpenImmersion_restrictι (algebraData X I) V

/-- The normal cone of the restriction of an ideal sheaf to an open subscheme `V` is the base
change along `V.ι` of the normal cone, i.e. `C_{Z ∩ V / V} = C_{Z / X} ×_X V`. -/
theorem isPullback_restrict :
    IsPullback (toBase V.toScheme (I.restrict V)) (restrictι I V) V.ι (toBase X I) :=
  RelativeSpec.isPullback_restrict (algebraData X I) V

end NormalCone

end

end GromovWitten.AlgebraicGeometry
