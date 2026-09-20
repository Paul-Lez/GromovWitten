/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.RelativeSpec
import GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

/-!
# Affine morphisms and relative spectra

This file relates the relative `Spec` construction of `RelativeSpec.lean` to arbitrary affine
morphisms of schemes.

* `RelativeSpec.ringEquivGamma` identifies the coordinate ring `𝒜.ring U` of a quasi-coherent
  algebra with the sections of `relativeSpec X 𝒜` over the preimage of the affine open `U`.
* `RelativeSpec.AlgebraData.ofAffineHom` turns an affine morphism `g : C ⟶ X` into an
  `AlgebraData X` whose ring over an affine open `W` is `Γ(C, g ⁻¹ᵁ W)`.
* `RelativeSpec.Hom.ofOver` and `RelativeSpec.Hom.ofOverRelativeSpec` produce morphisms of
  algebra data from morphisms of schemes over `X`.

-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry

open GlobalBlowup VectorBundleTotalSpace

universe u

noncomputable section

namespace RelativeSpec

set_option backward.isDefEq.respectTransparency false

section Gamma

variable (X : Scheme.{u}) (𝒜 : AlgebraData X)

/-- The affine chart of the relative `Spec` over an affine open `U` is exactly the preimage
of `U` under the structure morphism. -/
theorem affineι_preimage_toBase_preimage (U : X.affineOpens) :
    affineι X 𝒜 U ⁻¹ᵁ (toBase X 𝒜 ⁻¹ᵁ U.1) = ⊤ := by
  rw [← opensRange_affineι]
  exact Scheme.Hom.preimage_opensRange _

/-- The comparison map from the sections of `relativeSpec X 𝒜` over the preimage of an affine
open `U` to the coordinate ring `𝒜.ring U`. -/
def gammaHom (U : X.affineOpens) :
    Γ(relativeSpec X 𝒜, toBase X 𝒜 ⁻¹ᵁ U.1) ⟶ CommRingCat.of (𝒜.ring U) :=
  (affineι X 𝒜 U).appLE (toBase X 𝒜 ⁻¹ᵁ U.1) ⊤
      (affineι_preimage_toBase_preimage X 𝒜 U).ge ≫
    (Scheme.ΓSpecIso (CommRingCat.of (𝒜.ring U))).hom

/-- The comparison map is an isomorphism. -/
instance isIso_gammaHom (U : X.affineOpens) : IsIso (gammaHom X 𝒜 U) := by
  have h₁ : IsIso ((affineι X 𝒜 U).app (toBase X 𝒜 ⁻¹ᵁ U.1)) :=
    Scheme.Hom.isIso_app _ _ (opensRange_affineι X 𝒜 U).ge
  have h₂ : IsIso ((Spec (CommRingCat.of (𝒜.ring U))).presheaf.map
      (homOfLE (affineι_preimage_toBase_preimage X 𝒜 U).ge).op) := by
    rw [Subsingleton.elim (homOfLE (affineι_preimage_toBase_preimage X 𝒜 U).ge)
      (eqToHom (affineι_preimage_toBase_preimage X 𝒜 U).symm)]
    infer_instance
  rw [gammaHom, Scheme.Hom.appLE]
  infer_instance

/-- The coordinate ring of a quasi-coherent algebra over an affine open `U` is the ring of
sections of the relative `Spec` over the preimage of `U`. -/
def ringEquivGamma (U : X.affineOpens) :
    𝒜.ring U ≃+* Γ(relativeSpec X 𝒜, toBase X 𝒜 ⁻¹ᵁ U.1) :=
  (asIso (gammaHom X 𝒜 U)).symm.commRingCatIsoToRingEquiv

/-- `ringEquivGamma` is the inverse of the comparison map `gammaHom`. -/
theorem ringEquivGamma_symm_apply (U : X.affineOpens)
    (a : Γ(relativeSpec X 𝒜, toBase X 𝒜 ⁻¹ᵁ U.1)) :
    (ringEquivGamma X 𝒜 U).symm a = gammaHom X 𝒜 U a := rfl

/-- `gammaHom` undoes `ringEquivGamma`. -/
@[simp]
theorem gammaHom_ringEquivGamma (U : X.affineOpens) (a : 𝒜.ring U) :
    gammaHom X 𝒜 U (ringEquivGamma X 𝒜 U a) = a :=
  (ringEquivGamma X 𝒜 U).symm_apply_apply a

/-- `ringEquivGamma` undoes `gammaHom`. -/
@[simp]
theorem ringEquivGamma_gammaHom (U : X.affineOpens)
    (a : Γ(relativeSpec X 𝒜, toBase X 𝒜 ⁻¹ᵁ U.1)) :
    ringEquivGamma X 𝒜 U (gammaHom X 𝒜 U a) = a :=
  (ringEquivGamma X 𝒜 U).apply_symm_apply a

/-- The sections functor applied to a morphism only depends on the morphism. -/
theorem appLE_of_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (hfg : f = g) (U : Z.Opens) (V : Y.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst hfg; rfl

/-- Sections of `Spec Γ(Y, V)` over the preimage of an affine open `V` along the canonical
morphism `fromSpec`. -/
theorem fromSpec_appLE_top {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V)
    (e : (⊤ : (Spec Γ(Y, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V) :
    hV.fromSpec.appLE V ⊤ e = (Scheme.ΓSpecIso Γ(Y, V)).inv := by
  have hid : (Spec Γ(Y, V)).presheaf.map (homOfLE (le_top : hV.fromSpec ⁻¹ᵁ V ≤ ⊤)).op ≫
      (Spec Γ(Y, V)).presheaf.map (homOfLE e).op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp,
      Subsingleton.elim ((homOfLE (le_top : hV.fromSpec ⁻¹ᵁ V ≤ ⊤)).op ≫ (homOfLE e).op) (𝟙 _),
      CategoryTheory.Functor.map_id]
  rw [Scheme.Hom.appLE, hV.fromSpec_app_of_le V le_rfl]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    hid, Category.comp_id]

/-- `appLE` between the top opens is the map on global sections. -/
theorem appLE_top_top {Y Z : Scheme.{u}} (f : Y ⟶ Z) (e : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app f

/-- The structure morphism of `relativeSpec X 𝒜` induces on sections the structure map of the
algebra `𝒜.ring U`. -/
theorem toBase_app_comp_gammaHom (U : X.affineOpens) :
    (toBase X 𝒜).app U.1 ≫ gammaHom X 𝒜 U =
      CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U)) := by
  have hp : projection X 𝒜 U ≫ U.1.ι =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U))) ≫
        (isAffineOpen X U).fromSpec := by
    rw [IsAffineOpen.fromSpec, projection, Category.assoc]
  have he : (⊤ : (Spec (CommRingCat.of (𝒜.ring U))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U))) ≫
        (isAffineOpen X U).fromSpec) ⁻¹ᵁ U.1 := by
    rw [← hp, ← affineι_toBase]
    exact (affineι_preimage_toBase_preimage X 𝒜 U).ge
  have he1 : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ (isAffineOpen X U).fromSpec ⁻¹ᵁ U.1 := by
    intro x _
    have hx : x ∈ (isAffineOpen X U).fromSpec ⁻¹ᵁ (isAffineOpen X U).fromSpec.opensRange := by
      rw [Scheme.Hom.preimage_opensRange]; trivial
    rwa [(isAffineOpen X U).opensRange_fromSpec] at hx
  have key : (isAffineOpen X U).fromSpec.appLE U.1 ⊤ he1 ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U)))).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U))) ≫
        (isAffineOpen X U).fromSpec).appLE U.1 ⊤ he :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [gammaHom, ← Category.assoc, ← Scheme.Hom.comp_appLE,
    appLE_of_eq ((affineι_toBase X 𝒜 U).trans hp) U.1 ⊤ _ he, ← key,
    fromSpec_appLE_top, appLE_top_top, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp

/-- `gammaHom` sends the restriction of a section of `X` to the structure map of `𝒜.ring U`. -/
theorem gammaHom_toBase_app (U : X.affineOpens) (r : Γ(X, U.1)) :
    gammaHom X 𝒜 U ((toBase X 𝒜).app U.1 r) = algebraMap Γ(X, U.1) (𝒜.ring U) r := by
  rw [← CommRingCat.comp_apply, toBase_app_comp_gammaHom, CommRingCat.ofHom_apply]

/-- `ringEquivGamma` is `Γ(X, U)`-linear: it sends the structure map of `𝒜.ring U` to the
restriction of sections along the structure morphism. -/
theorem ringEquivGamma_algebraMap (U : X.affineOpens) (r : Γ(X, U.1)) :
    ringEquivGamma X 𝒜 U (algebraMap Γ(X, U.1) (𝒜.ring U) r) = (toBase X 𝒜).app U.1 r := by
  rw [← gammaHom_toBase_app, ringEquivGamma_gammaHom]

/-- The affine charts of the relative `Spec` are compatible with the transition maps. -/
theorem specMap_map_affineι {U V : X.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (𝒜.map h)) ≫ affineι X 𝒜 V = affineι X 𝒜 U :=
  colimit.w (gluingData X 𝒜).functor (homOfLE h)

/-- The comparison maps `gammaHom` are compatible with the transition maps of `𝒜` and with the
restriction maps of the structure sheaf of `relativeSpec X 𝒜`. -/
theorem gammaHom_map {U V : X.affineOpens} (h : U ≤ V) :
    (relativeSpec X 𝒜).presheaf.map (homOfLE ((toBase X 𝒜).preimage_mono h)).op ≫
        gammaHom X 𝒜 U =
      gammaHom X 𝒜 V ≫ CommRingCat.ofHom (𝒜.map h) := by
  have eU : (⊤ : (Spec (CommRingCat.of (𝒜.ring U))).Opens) ≤
      affineι X 𝒜 U ⁻¹ᵁ (toBase X 𝒜 ⁻¹ᵁ V.1) :=
    (affineι_preimage_toBase_preimage X 𝒜 U).ge.trans
      ((affineι X 𝒜 U).preimage_mono ((toBase X 𝒜).preimage_mono h))
  have key : (affineι X 𝒜 V).appLE (toBase X 𝒜 ⁻¹ᵁ V.1) ⊤
        (affineι_preimage_toBase_preimage X 𝒜 V).ge ≫
      (Spec.map (CommRingCat.ofHom (𝒜.map h))).appTop =
      (affineι X 𝒜 U).appLE (toBase X 𝒜 ⁻¹ᵁ V.1) ⊤ eU := by
    rw [← appLE_top_top (Spec.map (CommRingCat.ofHom (𝒜.map h))) le_top]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      (appLE_of_eq (specMap_map_affineι X 𝒜 h) _ _ _ eU)
  simp only [gammaHom, Category.assoc, ← Scheme.ΓSpecIso_naturality]
  rw [← Category.assoc, Scheme.Hom.map_appLE, ← Category.assoc, key]

/-- `ringEquivGamma` is compatible with the transition maps of `𝒜` and with the restriction
maps of the structure sheaf of `relativeSpec X 𝒜`. -/
theorem ringEquivGamma_map {U V : X.affineOpens} (h : U ≤ V) (a : 𝒜.ring V) :
    ringEquivGamma X 𝒜 U (𝒜.map h a) =
      (relativeSpec X 𝒜).presheaf.map (homOfLE ((toBase X 𝒜).preimage_mono h)).op
        (ringEquivGamma X 𝒜 V a) := by
  refine (ringEquivGamma X 𝒜 U).symm.injective ?_
  rw [RingEquiv.symm_apply_apply, ringEquivGamma_symm_apply, ← CommRingCat.comp_apply,
    gammaHom_map, CommRingCat.comp_apply, gammaHom_ringEquivGamma, CommRingCat.ofHom_apply]

end Gamma

section OfAffineHom

variable {X : Scheme.{u}}

/-- For a morphism `g : C ⟶ X` and opens `W ≤ V` of `X`, the square of restrictions of `g` is
cartesian. -/
theorem isPullback_resLE_of_le {C : Scheme.{u}} (g : C ⟶ X) {W V : X.Opens} (h : W ≤ V) :
    IsPullback (Scheme.Hom.resLE (𝟙 C) (g ⁻¹ᵁ V) (g ⁻¹ᵁ W) (g.preimage_mono h))
      (g.resLE W (g ⁻¹ᵁ W) le_rfl) (g.resLE V (g ⁻¹ᵁ V) le_rfl)
      (Scheme.Hom.resLE (𝟙 X) V W h) := by
  have H : IsPullback (𝟙 C) g g (𝟙 X) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact Scheme.Hom.isPullback_resLE H (US := V) (UT := W) (UX := g ⁻¹ᵁ V) (UY := g ⁻¹ᵁ W) h le_rfl
    (by simp [inf_eq_right.mpr (g.preimage_mono h)])

/-- The quasi-coherent algebra attached to an affine morphism `g : C ⟶ X`: over an affine open
`W` of the base its ring is the ring of sections of `C` over the preimage of `W`. -/
def AlgebraData.ofAffineHom {C : Scheme.{u}} (g : C ⟶ X) [IsAffineHom g] : AlgebraData X where
  ring W := Γ(C, g ⁻¹ᵁ W.1)
  algebra W := (g.app W.1).hom.toAlgebra
  map {W V} h := (C.presheaf.map (homOfLE (g.preimage_mono (h : W.1 ≤ V.1))).op).hom
  map_id W := by
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp hUV hVW := by
    rw [← CommRingCat.hom_comp, ← CategoryTheory.Functor.map_comp, ← op_comp]
    rfl
  isPushout {W V} h := by
    have h1 : IsAffine (g ⁻¹ᵁ V.1).toScheme := V.2.preimage g
    have h2 : IsAffine (g ⁻¹ᵁ W.1).toScheme := W.2.preimage g
    have h3 : IsAffine W.1.toScheme := W.2
    have h4 : IsAffine V.1.toScheme := V.2
    refine (isPushout_appTop_of_isPullback (isPullback_resLE_of_le g (h : W.1 ≤ V.1))).of_iso'
      V.1.topIso.symm (g ⁻¹ᵁ V.1).topIso.symm W.1.topIso.symm (g ⁻¹ᵁ W.1).topIso.symm ?_ ?_ ?_ ?_
    · simp only [Iso.symm_hom, Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc,
        Scheme.Hom.appLE_eq_app, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
    · simp only [Iso.symm_hom, Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc, Scheme.Hom.appLE,
        _root_.AlgebraicGeometry.Scheme.Hom.id_app, Category.id_comp, res, CommRingCat.ofHom_hom]
      rfl
    · simp only [Iso.symm_hom, Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc, Scheme.Hom.appLE,
        _root_.AlgebraicGeometry.Scheme.Hom.id_app, Category.id_comp, CommRingCat.ofHom_hom]
    · simp only [Iso.symm_hom, Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc,
        Scheme.Hom.appLE_eq_app, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]

/-- The ring of `AlgebraData.ofAffineHom g` over an affine open. -/
theorem AlgebraData.ofAffineHom_ring {C : Scheme.{u}} (g : C ⟶ X) [IsAffineHom g]
    (W : X.affineOpens) : (AlgebraData.ofAffineHom g).ring W = Γ(C, g ⁻¹ᵁ W.1) := rfl

/-- The transition map of `AlgebraData.ofAffineHom g`. -/
theorem AlgebraData.ofAffineHom_map {C : Scheme.{u}} (g : C ⟶ X) [IsAffineHom g]
    {W V : X.affineOpens} (h : W ≤ V) :
    (AlgebraData.ofAffineHom g).map h =
      (C.presheaf.map (homOfLE (g.preimage_mono (h : W.1 ≤ V.1))).op).hom := rfl

/-- The structure map of `AlgebraData.ofAffineHom g` is the map on sections induced by `g`. -/
theorem AlgebraData.ofAffineHom_algebraMap {C : Scheme.{u}} (g : C ⟶ X) [IsAffineHom g]
    (W : X.affineOpens) (r : Γ(X, W.1)) :
    algebraMap Γ(X, W.1) ((AlgebraData.ofAffineHom g).ring W) r = g.app W.1 r := rfl

end OfAffineHom

section OfOver

variable {X : Scheme.{u}}

/-- For a commuting triangle over `X`, the preimage of an open of `X` in the source is the
preimage of its preimage in the intermediate scheme. -/
theorem preimage_eq_of_over {C C' : Scheme.{u}} {g : C ⟶ X} {g' : C' ⟶ X} (h : C ⟶ C')
    (hh : h ≫ g' = g) (W : X.Opens) : h ⁻¹ᵁ (g' ⁻¹ᵁ W) = g ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, hh]

/-- The inequality of opens underlying `preimage_eq_of_over`. -/
theorem preimage_le_preimage_of_over {C C' : Scheme.{u}} {g : C ⟶ X} {g' : C' ⟶ X} (h : C ⟶ C')
    (hh : h ≫ g' = g) (W : X.Opens) : g ⁻¹ᵁ W ≤ h ⁻¹ᵁ (g' ⁻¹ᵁ W) :=
  (preimage_eq_of_over h hh W).ge

/-- The maps on sections in a commuting triangle over `X` compose to the map on sections of the
structure morphism. -/
theorem app_comp_appLE_of_over {C C' : Scheme.{u}} {g : C ⟶ X} {g' : C' ⟶ X} (h : C ⟶ C')
    (hh : h ≫ g' = g) (W : X.Opens) :
    g'.app W ≫ h.appLE (g' ⁻¹ᵁ W) (g ⁻¹ᵁ W) (preimage_le_preimage_of_over h hh W) = g.app W := by
  rw [← Scheme.Hom.comp_appLE, appLE_of_eq hh W (g ⁻¹ᵁ W) _ le_rfl, Scheme.Hom.appLE_eq_app]

/-- A morphism of schemes over `X` between two affine morphisms induces a morphism of the
associated quasi-coherent algebras. -/
def Hom.ofOver {C C' : Scheme.{u}} {g : C ⟶ X} {g' : C' ⟶ X} [IsAffineHom g] [IsAffineHom g']
    (h : C ⟶ C') (hh : h ≫ g' = g) :
    Hom X (AlgebraData.ofAffineHom g) (AlgebraData.ofAffineHom g') where
  app W :=
    { (h.appLE (g' ⁻¹ᵁ W.1) (g ⁻¹ᵁ W.1) (preimage_le_preimage_of_over h hh W.1)).hom with
      commutes' := fun r ↦ by
        change (h.appLE (g' ⁻¹ᵁ W.1) (g ⁻¹ᵁ W.1) _) ((g'.app W.1) r) = (g.app W.1) r
        rw [← CommRingCat.comp_apply, app_comp_appLE_of_over h hh W.1] }
  naturality {U V} hle := by
    have key : C'.presheaf.map (homOfLE (g'.preimage_mono (hle : U.1 ≤ V.1))).op ≫
          h.appLE (g' ⁻¹ᵁ U.1) (g ⁻¹ᵁ U.1) (preimage_le_preimage_of_over h hh U.1) =
        h.appLE (g' ⁻¹ᵁ V.1) (g ⁻¹ᵁ V.1) (preimage_le_preimage_of_over h hh V.1) ≫
          C.presheaf.map (homOfLE (g.preimage_mono (hle : U.1 ≤ V.1))).op := by
      rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
    exact congrArg CommRingCat.Hom.hom key

/-- The components of `Hom.ofOver`. -/
theorem Hom.ofOver_app_apply {C C' : Scheme.{u}} {g : C ⟶ X} {g' : C' ⟶ X} [IsAffineHom g]
    [IsAffineHom g'] (h : C ⟶ C') (hh : h ≫ g' = g) (W : X.affineOpens)
    (a : Γ(C', g' ⁻¹ᵁ W.1)) :
    (Hom.ofOver h hh).app W a =
      h.appLE (g' ⁻¹ᵁ W.1) (g ⁻¹ᵁ W.1) (preimage_le_preimage_of_over h hh W.1) a := rfl

variable (𝒜 : AlgebraData X)

/-- The inverse comparison maps are compatible with the transition maps of `𝒜`. -/
theorem inv_gammaHom_map {U V : X.affineOpens} (h : U ≤ V) :
    CommRingCat.ofHom (𝒜.map h) ≫ inv (gammaHom X 𝒜 U) =
      inv (gammaHom X 𝒜 V) ≫ (relativeSpec X 𝒜).presheaf.map
        (homOfLE ((toBase X 𝒜).preimage_mono h)).op := by
  rw [IsIso.comp_inv_eq, Category.assoc, gammaHom_map, IsIso.inv_hom_id_assoc]

/-- A morphism `C ⟶ relativeSpec X 𝒜` over `X`, with `C` affine over `X`, induces a morphism of
quasi-coherent algebras from `𝒜` to the algebra of `C`. -/
def Hom.ofOverRelativeSpec {C : Scheme.{u}} {g : C ⟶ X} [IsAffineHom g]
    (h : C ⟶ relativeSpec X 𝒜) (hh : h ≫ toBase X 𝒜 = g) :
    Hom X (AlgebraData.ofAffineHom g) 𝒜 where
  app W :=
    { (inv (gammaHom X 𝒜 W) ≫ h.appLE (toBase X 𝒜 ⁻¹ᵁ W.1) (g ⁻¹ᵁ W.1)
        (preimage_le_preimage_of_over h hh W.1)).hom with
      commutes' := fun r ↦ by
        change (h.appLE (toBase X 𝒜 ⁻¹ᵁ W.1) (g ⁻¹ᵁ W.1) _)
          (ringEquivGamma X 𝒜 W (algebraMap Γ(X, W.1) (𝒜.ring W) r)) = (g.app W.1) r
        rw [ringEquivGamma_algebraMap, ← CommRingCat.comp_apply,
          app_comp_appLE_of_over h hh W.1] }
  naturality {U V} hle := by
    have key : (relativeSpec X 𝒜).presheaf.map
          (homOfLE ((toBase X 𝒜).preimage_mono (hle : U.1 ≤ V.1))).op ≫
          h.appLE (toBase X 𝒜 ⁻¹ᵁ U.1) (g ⁻¹ᵁ U.1) (preimage_le_preimage_of_over h hh U.1) =
        h.appLE (toBase X 𝒜 ⁻¹ᵁ V.1) (g ⁻¹ᵁ V.1) (preimage_le_preimage_of_over h hh V.1) ≫
          C.presheaf.map (homOfLE (g.preimage_mono (hle : U.1 ≤ V.1))).op := by
      rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
    have main : CommRingCat.ofHom (𝒜.map hle) ≫ (inv (gammaHom X 𝒜 U) ≫
          h.appLE (toBase X 𝒜 ⁻¹ᵁ U.1) (g ⁻¹ᵁ U.1) (preimage_le_preimage_of_over h hh U.1)) =
        (inv (gammaHom X 𝒜 V) ≫
            h.appLE (toBase X 𝒜 ⁻¹ᵁ V.1) (g ⁻¹ᵁ V.1) (preimage_le_preimage_of_over h hh V.1)) ≫
          C.presheaf.map (homOfLE (g.preimage_mono (hle : U.1 ≤ V.1))).op := by
      rw [← Category.assoc, inv_gammaHom_map, Category.assoc, key]
      simp only [Category.assoc]
    exact congrArg CommRingCat.Hom.hom main

/-- The components of `Hom.ofOverRelativeSpec`. -/
theorem Hom.ofOverRelativeSpec_app_apply {C : Scheme.{u}} {g : C ⟶ X} [IsAffineHom g]
    (h : C ⟶ relativeSpec X 𝒜) (hh : h ≫ toBase X 𝒜 = g) (W : X.affineOpens) (a : 𝒜.ring W) :
    (Hom.ofOverRelativeSpec 𝒜 h hh).app W a =
      h.appLE (toBase X 𝒜 ⁻¹ᵁ W.1) (g ⁻¹ᵁ W.1) (preimage_le_preimage_of_over h hh W.1)
        (ringEquivGamma X 𝒜 W a) := rfl

/-- If `h` is a closed immersion then all the components of `Hom.ofOverRelativeSpec` are
surjective, so that the induced morphism of relative spectra is a closed immersion. -/
theorem Hom.ofOverRelativeSpec_app_surjective {C : Scheme.{u}} {g : C ⟶ X} [IsAffineHom g]
    (h : C ⟶ relativeSpec X 𝒜) (hh : h ≫ toBase X 𝒜 = g) [IsClosedImmersion h]
    (W : X.affineOpens) : Function.Surjective ((Hom.ofOverRelativeSpec 𝒜 h hh).app W) := by
  have hpre : IsAffineOpen (toBase X 𝒜 ⁻¹ᵁ W.1) := W.2.preimage (toBase X 𝒜)
  have h1 : Function.Surjective (h.app (toBase X 𝒜 ⁻¹ᵁ W.1)) :=
    Scheme.Hom.app_surjective h _ hpre
  have hiso : IsIso (C.presheaf.map (homOfLE (preimage_le_preimage_of_over h hh W.1)).op) := by
    rw [Subsingleton.elim (homOfLE (preimage_le_preimage_of_over h hh W.1))
      (eqToHom (preimage_eq_of_over h hh W.1).symm)]
    infer_instance
  have h2 : Function.Surjective
      (C.presheaf.map (homOfLE (preimage_le_preimage_of_over h hh W.1)).op) :=
    (ConcreteCategory.bijective_of_isIso _).2
  have h3 : Function.Surjective (inv (gammaHom X 𝒜 W)) := (ConcreteCategory.bijective_of_isIso _).2
  intro b
  obtain ⟨c, rfl⟩ := h2 b
  obtain ⟨d, rfl⟩ := h1 c
  obtain ⟨a, rfl⟩ := h3 d
  exact ⟨a, rfl⟩

end OfOver

section OfAffineHomIso

variable {X C : Scheme.{u}} (g : C ⟶ X) [IsAffineHom g]

/-- The structure map of `AlgebraData.ofAffineHom g`, as a morphism of `CommRingCat`. -/
theorem ofHom_algebraMap_ofAffineHom (U : X.affineOpens) :
    CommRingCat.ofHom (algebraMap Γ(X, U.1) ((AlgebraData.ofAffineHom g).ring U)) =
      g.app U.1 := rfl

/-- The comparison morphism from the relative `Spec` of the quasi-coherent algebra of an affine
morphism `g : C ⟶ X` to `C`, glued from the canonical morphisms `Spec Γ(C, g ⁻¹ᵁ U) ⟶ C`. -/
def ofAffineHomHom : relativeSpec X (AlgebraData.ofAffineHom g) ⟶ C :=
  colimit.desc (gluingData X (AlgebraData.ofAffineHom g)).functor
    { pt := C
      ι :=
        { app := fun (U : X.affineOpens) ↦ (U.2.preimage g).fromSpec
          naturality := by
            intro U V f
            dsimp
            rw [Category.comp_id]
            exact (V.2.preimage g).map_fromSpec (U.2.preimage g)
              (homOfLE (g.preimage_mono (leOfHom f : U.1 ≤ V.1))).op } }

/-- On the affine chart over `U`, the comparison morphism is the canonical morphism
`Spec Γ(C, g ⁻¹ᵁ U) ⟶ C`. -/
@[reassoc]
theorem affineι_ofAffineHomHom (U : X.affineOpens) :
    affineι X (AlgebraData.ofAffineHom g) U ≫ ofAffineHomHom g = (U.2.preimage g).fromSpec := by
  rw [affineι, ofAffineHomHom, colimit.ι_desc]

/-- The comparison morphism is a morphism over `X`. -/
theorem ofAffineHomHom_comp : ofAffineHomHom g ≫ g = toBase X (AlgebraData.ofAffineHom g) := by
  refine colimit.hom_ext fun (U : X.affineOpens) ↦ ?_
  change affineι X (AlgebraData.ofAffineHom g) U ≫ ofAffineHomHom g ≫ g =
    affineι X (AlgebraData.ofAffineHom g) U ≫ toBase X (AlgebraData.ofAffineHom g)
  rw [← Category.assoc, affineι_ofAffineHomHom, affineι_toBase, projection, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι, ofHom_algebraMap_ofAffineHom,
    ← Scheme.Hom.appLE_eq_app (f := g) (U := U.1)]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen X U) (U.2.preimage g) le_rfl).symm

/-- The affine chart of the relative `Spec` over `U` is the pullback of `g ⁻¹ᵁ U` along the
comparison morphism. -/
theorem isPullback_ofAffineHomHom (U : X.affineOpens) :
    IsPullback (U.2.preimage g).isoSpec.inv (affineι X (AlgebraData.ofAffineHom g) U)
      (g ⁻¹ᵁ U.1).ι (ofAffineHomHom g) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [affineι_ofAffineHomHom, IsAffineOpen.isoSpec_inv_ι]
  · rw [Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage, ofAffineHomHom_comp]
    exact (opensRange_affineι X (AlgebraData.ofAffineHom g) U).symm

/-- A property of morphisms which respects isomorphisms holds for the comparison morphism over
`g ⁻¹ᵁ U` if and only if it holds for the canonical isomorphism `Spec Γ(C, g ⁻¹ᵁ U) ≅ g ⁻¹ᵁ U`. -/
theorem property_restrict_ofAffineHomHom_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : X.affineOpens) :
    P (ofAffineHomHom g ∣_ (g ⁻¹ᵁ U.1).ι.opensRange) ↔ P ((U.2.preimage g).isoSpec.inv) := by
  rw [P.arrow_mk_iso_iff (morphismRestrictOpensRange (ofAffineHomHom g) (g ⁻¹ᵁ U.1).ι)]
  exact (P.arrow_mk_iso_iff (Arrow.isoMk (isPullback_ofAffineHomHom g U).flip.isoPullback
    (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id]
      exact (isPullback_ofAffineHomHom g U).flip.isoPullback_hom_snd))).symm

/-- The version of `property_restrict_ofAffineHomHom_iff` phrased with the open `g ⁻¹ᵁ U`. -/
theorem property_restrict_ofAffineHomHom_iff' (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : X.affineOpens) :
    P (ofAffineHomHom g ∣_ (g ⁻¹ᵁ U.1)) ↔ P ((U.2.preimage g).isoSpec.inv) := by
  rw [← property_restrict_ofAffineHomHom_iff g P U, Scheme.Opens.opensRange_ι]

/-- The comparison morphism is an isomorphism: every affine morphism is the relative `Spec` of
its quasi-coherent algebra of sections. -/
instance isIso_ofAffineHomHom : IsIso (ofAffineHomHom g) := by
  have hcover : ⨆ U : X.affineOpens, (g ⁻¹ᵁ U.1) = ⊤ :=
    g.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)
  have key := (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme.{u}) (f := ofAffineHomHom g) _ hcover).mpr
    fun U : X.affineOpens ↦
      (property_restrict_ofAffineHomHom_iff' g (MorphismProperty.isomorphisms Scheme.{u})
        U).mpr (by change IsIso _; infer_instance)
  exact key

/-- Every affine morphism `g : C ⟶ X` is the relative `Spec` over `X` of the quasi-coherent
algebra `W ↦ Γ(C, g ⁻¹ᵁ W)`. -/
def relativeSpecOfAffineHomIso : relativeSpec X (AlgebraData.ofAffineHom g) ≅ C :=
  asIso (ofAffineHomHom g)

/-- The isomorphism of `relativeSpecOfAffineHomIso` is a morphism over `X`. -/
theorem relativeSpecOfAffineHomIso_hom_comp :
    (relativeSpecOfAffineHomIso g).hom ≫ g = toBase X (AlgebraData.ofAffineHom g) :=
  ofAffineHomHom_comp g

end OfAffineHomIso

end RelativeSpec

end

end GromovWitten.AlgebraicGeometry
