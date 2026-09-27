/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Flat base change of scheme-theoretic images

The map from a quasi-compact morphism to its scheme-theoretic image is schematically
dominant. After flat base change it remains schematically dominant, so the kernel ideal
of the base-changed morphism is the pullback of the original kernel. This identifies the
new image with the base change of the old image, compatibly with its closed immersion.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Hom
-- Scheme pullback and image objects use categorical type aliases, as in Mathlib's image API.
set_option backward.isDefEq.respectTransparency false
variable {X Y Y' : Scheme.{u}}

/-- A quasi-compact morphism is schematically dominant onto its scheme-theoretic image. -/
lemma isSchemeTheoreticallyDominant_toImage (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  constructor
  ext1
  funext U
  rw [ker_apply, IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injective_iff_ker_eq_bot]
  exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
    (F := f.image.sheaf) f.toImage.c U.1 (fun x _ => f.stalkFunctor_toImage_injective x)


/-- The map to the pulled-back scheme-theoretic image. -/
def pullbackToImage (f : X ⟶ Y) (b : Y' ⟶ Y) :
    pullback b f ⟶ pullback b f.imageι :=
  pullback.map b f b f.imageι (𝟙 _) f.toImage (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma pullbackToImage_fst (f : X ⟶ Y) (b : Y' ⟶ Y) :
    pullbackToImage f b ≫ pullback.fst b f.imageι = pullback.fst b f := by
  simp only [pullbackToImage, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma pullbackToImage_snd (f : X ⟶ Y) (b : Y' ⟶ Y) :
    pullbackToImage f b ≫ pullback.snd b f.imageι = pullback.snd b f ≫ f.toImage := by
  simp only [pullbackToImage, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The map to the pulled-back image is the base change of the original image factor. -/
lemma isPullback_toImage (f : X ⟶ Y) (b : Y' ⟶ Y) :
    IsPullback (pullback.snd b f) (pullbackToImage f b)
      f.toImage (pullback.snd b f.imageι) := by
  apply IsPullback.of_bot _ (pullbackToImage_snd f b).symm
    (IsPullback.of_hasPullback b f.imageι).flip
  simpa using (IsPullback.of_hasPullback b f).flip

/-- Scheme-theoretic kernel ideals commute with flat base change of quasi-compact morphisms. -/
lemma ker_pullbackFst_of_flat (f : X ⟶ Y) (b : Y' ⟶ Y)
    [QuasiCompact f] [Flat b] :
    (pullback.fst b f).ker = f.ker.comap b := by
  have : IsSchemeTheoreticallyDominant f.toImage := f.isSchemeTheoreticallyDominant_toImage
  have : IsSchemeTheoreticallyDominant (pullbackToImage f b) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_toImage f b)
  rw [← pullbackToImage_fst f b, ker_comp, (pullbackToImage f b).ker_eq_bot,
    IdealSheafData.map_bot, IdealSheafData.ker_fst_of_isClosedImmersion]
  simp


/-- The kernel equality for any cartesian square with flat base-change map. -/
lemma ker_of_isPullback_of_flat {X' : Scheme.{u}} {f : X ⟶ Y} {b : Y' ⟶ Y}
    {g : X' ⟶ X} {f' : X' ⟶ Y'} (H : IsPullback g f' f b)
    [QuasiCompact f] [Flat b] : f'.ker = f.ker.comap b := by
  rw [← H.flip.isoPullback_hom_fst, ker_comp_of_isIso, ker_pullbackFst_of_flat]

private lemma eqToHom_subschemeι {Z : Scheme.{u}} {I J : Z.IdealSheafData} (h : I = J) :
    eqToHom (congrArg IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  cases h
  simp

/-- Scheme-theoretic images of quasi-compact morphisms commute with flat base change. -/
def imageBaseChangeIso (f : X ⟶ Y) (b : Y' ⟶ Y) [QuasiCompact f] [Flat b] :
    (pullback.fst b f).image ≅ pullback b f.imageι :=
  eqToIso (congrArg IdealSheafData.subscheme (ker_pullbackFst_of_flat f b)) ≪≫
    f.ker.comapIso b

@[reassoc (attr := simp)]
lemma imageBaseChangeIso_hom_fst (f : X ⟶ Y) (b : Y' ⟶ Y)
    [QuasiCompact f] [Flat b] :
    (imageBaseChangeIso f b).hom ≫ pullback.fst b f.imageι = (pullback.fst b f).imageι := by
  simp only [imageBaseChangeIso, Iso.trans_hom, Category.assoc,
    IdealSheafData.comapIso_hom_fst, eqToIso.hom]
  exact eqToHom_subschemeι (ker_pullbackFst_of_flat f b)

/-- The closed immersion of the new image is the base change of the original one. -/
lemma isPullback_imageBaseChange (f : X ⟶ Y) (b : Y' ⟶ Y)
    [QuasiCompact f] [Flat b] :
    IsPullback (pullback.fst b f).imageι
      ((imageBaseChangeIso f b).hom ≫ pullback.snd b f.imageι) b f.imageι := by
  refine IsPullback.of_iso_pullback ?_ (imageBaseChangeIso f b)
    (imageBaseChangeIso_hom_fst f b) rfl
  constructor
  rw [← imageBaseChangeIso_hom_fst f b, Category.assoc, pullback.condition]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Hom
