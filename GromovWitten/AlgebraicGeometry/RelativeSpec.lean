/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ReesBlowupGlobal
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Relative `Spec` over a scheme

A *quasi-coherent algebra* on a scheme `X` is given affine-locally: an algebra `𝒜 U` over the
section ring of every affine open `U`, together with transition maps `𝒜 V → 𝒜 U` for `U ≤ V`
which are functorial and which exhibit `𝒜 U` as the base change of `𝒜 V` along the restriction
map of section rings, in the form of a pushout square of commutative rings (`AlgebraData`).  The
relative `Spec` of such data is glued from the affine spectra `Spec (𝒜 U)` using Mathlib's
relative gluing along the locally directed cover of `X` by its affine opens, exactly as the
relative `Proj` of `RelativeProj` and the global Rees blowup of `ReesBlowupGlobal`.

The result is a scheme `relativeSpec X 𝒜` with an affine structure morphism `toBase X 𝒜` to `X`
whose restriction to every affine open `U` is `Spec (𝒜 U)` (`isPullback_affine`,
`toBase_isAffineHom`).  A morphism of algebra data `ℬ → 𝒜` (contravariantly, a compatible family
of algebra maps `ℬ U → 𝒜 U`) induces a morphism `relativeSpec X 𝒜 ⟶ relativeSpec X ℬ` over `X`
whose restriction to every affine piece is the corresponding `Spec.map` (`Hom.map`,
`Hom.isPullback_map`); a property local on the target holds for it as soon as it holds for all
these affine maps, so in particular a surjective family of algebra maps induces a closed immersion
(`Hom.map_isClosedImmersion`).

The pushout condition is verified in practice from a bijective base-change map
`𝒜 V ⊗ Γ(U) → 𝒜 U`; the helper `isPushout_of_algEquiv` performs this translation.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

open GlobalBlowup

universe u

noncomputable section

/-! ### From a bijective base-change map to a pushout square -/

section Pushout

variable {A S B T : Type u} [CommRing A] [CommRing S] [CommRing B] [CommRing T]
  [Algebra A S] [Algebra A B] [Algebra B T]

/-- A `B`-algebra isomorphism `B ⊗[A] S ≃ T` restricting to `φ` on `S` exhibits the square
`A → S, A → B, S → T, B → T` as a pushout of commutative rings. -/
theorem isPushout_of_algEquiv (φ : S →+* T) (e : B ⊗[A] S ≃ₐ[B] T)
    (he : ∀ s : S, e ((1 : B) ⊗ₜ[A] s) = φ s) :
    IsPushout (CommRingCat.ofHom (algebraMap A S)) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap B T)) := by
  refine (CommRingCat.isPushout_tensorProduct A B S).flip.of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [Iso.refl_hom, Category.id_comp]
    ext s
    exact he s
  · rw [Iso.refl_hom, Category.id_comp]
    ext b
    change e (b ⊗ₜ[A] (1 : S)) = algebraMap B T b
    rw [← e.commutes b]
    rfl

end Pushout

/-! ### Quasi-coherent algebra data -/

/-- A quasi-coherent algebra on a scheme, given affine-locally: an algebra over the section ring
of every affine open, with functorial transition maps which are base changes along the
restriction maps of section rings. -/
structure AlgebraData (X : Scheme.{u}) where
  /-- The ring over an affine open. -/
  ring : X.affineOpens → Type u
  [commRing : ∀ U, CommRing (ring U)]
  [algebra : ∀ U, Algebra Γ(X, U.1) (ring U)]
  /-- The transition maps. -/
  map : ∀ {U V : X.affineOpens}, U ≤ V → (ring V →+* ring U)
  map_id : ∀ U, map (le_refl U) = RingHom.id _
  map_comp : ∀ {U V W : X.affineOpens} (hUV : U ≤ V) (hVW : V ≤ W),
    map (hUV.trans hVW) = (map hUV).comp (map hVW)
  /-- The transition maps are base changes along the restriction maps. -/
  isPushout : ∀ {U V : X.affineOpens} (h : U ≤ V),
    IsPushout (CommRingCat.ofHom (algebraMap Γ(X, V.1) (ring V))) (CommRingCat.ofHom (res X h))
      (CommRingCat.ofHom (map h)) (CommRingCat.ofHom (algebraMap Γ(X, U.1) (ring U)))

attribute [instance] AlgebraData.commRing AlgebraData.algebra

namespace RelativeSpec

/- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
type of affine opens; as in Mathlib's own development of that cover, the unifier is told not to
respect transparency in this section. -/
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u}) (𝒜 : AlgebraData X)

/-- The transition maps commute with the structure maps. -/
theorem map_algebraMap {U V : X.affineOpens} (h : U ≤ V) (a : Γ(X, V.1)) :
    𝒜.map h (algebraMap Γ(X, V.1) (𝒜.ring V) a) = algebraMap Γ(X, U.1) (𝒜.ring U) (res X h a) :=
  congrArg (fun f : Γ(X, V.1) ⟶ CommRingCat.of (𝒜.ring U) ↦ f a) (𝒜.isPushout h).w

/-- The gluing functor: the affine spectrum of each affine open, with the transition maps. -/
def gluingFunctor : X.affineOpens ⥤ Scheme.{u} where
  obj U := Spec (.of (𝒜.ring U))
  map {U V} h := Spec.map (CommRingCat.ofHom (𝒜.map (leOfHom h)))
  map_id U := by
    change Spec.map (CommRingCat.ofHom (𝒜.map (le_refl U))) = 𝟙 _
    rw [𝒜.map_id, CommRingCat.ofHom_id, Spec.map_id]
  map_comp {U V W} f g := by
    change Spec.map (CommRingCat.ofHom (𝒜.map ((leOfHom f).trans (leOfHom g)))) = _
    rw [𝒜.map_comp, CommRingCat.ofHom_comp, Spec.map_comp]

/-- The structure map of the affine spectrum of an affine open to that open. -/
def gluingApp (U : X.affineOpens) :
    (gluingFunctor X 𝒜).obj U ⟶ X.directedAffineCover.functorOfLocallyDirected.obj U :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U))) ≫ (isAffineOpen X U).isoSpec.inv

/-- The affine transition squares over the restriction maps are cartesian. -/
theorem isPullback_specMap_map {U V : X.affineOpens} (h : U ≤ V) :
    IsPullback (Spec.map (CommRingCat.ofHom (𝒜.map h)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (𝒜.ring V))))
      (Spec.map (CommRingCat.ofHom (res X h))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (𝒜.isPushout h)

/-- The structure maps form a natural transformation to the cover. -/
def gluingNatTrans : gluingFunctor X 𝒜 ⟶ X.directedAffineCover.functorOfLocallyDirected where
  app := gluingApp X 𝒜
  naturality {U V} h := by
    rw [← homOfLE_leOfHom h, Scheme.Cover.functorOfLocallyDirected_map,
      Scheme.directedAffineCover_trans]
    change Spec.map (CommRingCat.ofHom (𝒜.map (leOfHom h))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (𝒜.ring V))) ≫
          (isAffineOpen X V).isoSpec.inv =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U))) ≫
        (isAffineOpen X U).isoSpec.inv) ≫ X.homOfLE (leOfHom h)
    rw [← Category.assoc, (isPullback_specMap_map X 𝒜 (leOfHom h)).w, Category.assoc,
      Category.assoc, specMap_res_comp_isoSpec_inv]

/-- The transition squares are cartesian. -/
theorem gluingNatTrans_equifibered : (gluingNatTrans X 𝒜).Equifibered := by
  intro U V h
  rw [← homOfLE_leOfHom h, Scheme.Cover.functorOfLocallyDirected_map,
    Scheme.directedAffineCover_trans]
  change IsPullback (Spec.map (CommRingCat.ofHom (𝒜.map (leOfHom h))))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U))) ≫
      (isAffineOpen X U).isoSpec.inv)
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (𝒜.ring V))) ≫
      (isAffineOpen X V).isoSpec.inv) (X.homOfLE (leOfHom h))
  exact (isPullback_specMap_map X 𝒜 (leOfHom h)).paste_vert (isPullback_specMap_res X (leOfHom h))

/-- The relative gluing datum of the affine spectra over the affine opens. -/
def gluingData : X.directedAffineCover.RelativeGluingData where
  functor := gluingFunctor X 𝒜
  natTrans := gluingNatTrans X 𝒜
  equifibered := gluingNatTrans_equifibered X 𝒜

/-- The relative `Spec` of a quasi-coherent algebra on `X`. -/
abbrev relativeSpec : Scheme.{u} := (gluingData X 𝒜).glued

/-- The structure morphism `Spec_X 𝒜 → X`. -/
def toBase : relativeSpec X 𝒜 ⟶ X := (gluingData X 𝒜).toBase

/-- The affine spectrum of an affine open embeds into the relative `Spec`. -/
def affineι (U : X.affineOpens) : Spec (.of (𝒜.ring U)) ⟶ relativeSpec X 𝒜 :=
  colimit.ι (gluingData X 𝒜).functor U

instance affineι_isOpenImmersion (U : X.affineOpens) : IsOpenImmersion (affineι X 𝒜 U) := by
  have := (gluingData X 𝒜).cover.map_prop U
  rwa [Scheme.Cover.RelativeGluingData.cover_f] at this

/-- The structure morphism of an affine piece, as a morphism to the affine open. -/
abbrev projection (U : X.affineOpens) : Spec (.of (𝒜.ring U)) ⟶ U.1.toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U))) ≫ (isAffineOpen X U).isoSpec.inv

/-- Over every affine open, the relative `Spec` is the affine spectrum. -/
theorem isPullback_affine (U : X.affineOpens) :
    IsPullback (projection X 𝒜 U) (affineι X 𝒜 U) U.1.ι (toBase X 𝒜) :=
  (gluingData X 𝒜).isPullback_natTrans_ι_toBase U

theorem affineι_toBase (U : X.affineOpens) :
    affineι X 𝒜 U ≫ toBase X 𝒜 = projection X 𝒜 U ≫ U.1.ι :=
  (isPullback_affine X 𝒜 U).w.symm

/-- The affine pieces cover the relative `Spec`. -/
theorem iSup_opensRange_affineι : ⨆ U : X.affineOpens, (affineι X 𝒜 U).opensRange = ⊤ :=
  (gluingData X 𝒜).cover.iSup_opensRange

/-- A property of morphisms which respects isomorphisms holds for the structure morphism over an
affine open if and only if it holds for the affine spectrum. -/
theorem property_restrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : X.affineOpens) :
    P (toBase X 𝒜 ∣_ U.1.ι.opensRange) ↔ P (projection X 𝒜 U) := by
  rw [P.arrow_mk_iso_iff (morphismRestrictOpensRange (toBase X 𝒜) U.1.ι)]
  exact (P.arrow_mk_iso_iff (Arrow.isoMk (isPullback_affine X 𝒜 U).flip.isoPullback
    (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id]
      exact (isPullback_affine X 𝒜 U).flip.isoPullback_hom_snd))).symm

theorem property_restrict_iff' (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : X.affineOpens) :
    P (toBase X 𝒜 ∣_ U.1) ↔ P (projection X 𝒜 U) := by
  rw [← property_restrict_iff X 𝒜 P U, Scheme.Opens.opensRange_ι]

/-- A property local on the target holds for the structure morphism as soon as it holds for all
the affine structure morphisms. -/
theorem property_toBase_of_forall (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ U : X.affineOpens, P (projection X 𝒜 U)) : P (toBase X 𝒜) := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P)
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X)).mpr fun U ↦ ?_
  rw [property_restrict_iff' X 𝒜 P U]
  exact h U

/-- The structure morphism of a relative `Spec` is affine. -/
instance toBase_isAffineHom : IsAffineHom (toBase X 𝒜) :=
  property_toBase_of_forall X 𝒜 @IsAffineHom fun _ ↦ isAffineHom_of_isAffine _

/-- The structure morphism of the relative `Spec` of a quasi-coherent algebra whose structure
maps are all bijective is an isomorphism. -/
theorem isIso_toBase_of_bijective
    (h : ∀ U : X.affineOpens, Function.Bijective (algebraMap Γ(X, U.1) (𝒜.ring U))) :
    IsIso (toBase X 𝒜) := by
  refine property_toBase_of_forall X 𝒜 (MorphismProperty.isomorphisms Scheme) fun U ↦ ?_
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U)))) := by
    rw [isIso_SpecMap_iff]
    exact h U
  exact inferInstanceAs (IsIso (_ ≫ _))

/-! ### Morphisms of algebra data -/

/-- A morphism of quasi-coherent algebras `ℬ → 𝒜`: a compatible family of algebra maps
`ℬ U → 𝒜 U` over the section rings.  It induces a morphism `Spec_X 𝒜 → Spec_X ℬ`. -/
structure Hom (𝒜 ℬ : AlgebraData X) where
  /-- The components. -/
  app : ∀ U : X.affineOpens, ℬ.ring U →ₐ[Γ(X, U.1)] 𝒜.ring U
  naturality : ∀ {U V : X.affineOpens} (h : U ≤ V),
    (app U).toRingHom.comp (ℬ.map h) = (𝒜.map h).comp (app V).toRingHom

namespace Hom

variable {X 𝒜} {ℬ : AlgebraData X} (φ : Hom X 𝒜 ℬ)

/-- The natural transformation of gluing functors induced by a morphism of algebra data. -/
def gluingNatTrans : (gluingData X 𝒜).functor ⟶ (gluingData X ℬ).functor where
  app U := Spec.map (CommRingCat.ofHom (φ.app U).toRingHom)
  naturality {U V} h := by
    change Spec.map (CommRingCat.ofHom (𝒜.map (leOfHom h))) ≫
        Spec.map (CommRingCat.ofHom (φ.app V).toRingHom) =
      Spec.map (CommRingCat.ofHom (φ.app U).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (ℬ.map (leOfHom h)))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      φ.naturality]

/-- The morphism of relative spectra induced by a morphism of algebra data. -/
def map : relativeSpec X 𝒜 ⟶ relativeSpec X ℬ := colimMap φ.gluingNatTrans

theorem affineι_map (U : X.affineOpens) :
    affineι X 𝒜 U ≫ φ.map = Spec.map (CommRingCat.ofHom (φ.app U).toRingHom) ≫ affineι X ℬ U :=
  ι_colimMap φ.gluingNatTrans U

theorem specMap_app_projection (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (φ.app U).toRingHom) ≫ projection X ℬ U = projection X 𝒜 U := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext a
  exact (φ.app U).commutes a

/-- The induced morphism lies over `X`. -/
theorem map_toBase : φ.map ≫ toBase X ℬ = toBase X 𝒜 := by
  apply colimit.hom_ext
  intro U
  change affineι X 𝒜 U ≫ φ.map ≫ toBase X ℬ = affineι X 𝒜 U ≫ toBase X 𝒜
  rw [← Category.assoc, affineι_map, Category.assoc, affineι_toBase, affineι_toBase,
    ← Category.assoc, specMap_app_projection]

/-- Over every affine open, the induced morphism is the affine `Spec.map`. -/
theorem isPullback_map (U : X.affineOpens) :
    IsPullback (Spec.map (CommRingCat.ofHom (φ.app U).toRingHom)) (affineι X 𝒜 U)
      (affineι X ℬ U) φ.map := by
  refine IsPullback.of_right ?_ (φ.affineι_map U).symm (isPullback_affine X ℬ U)
  rw [specMap_app_projection, map_toBase]
  exact isPullback_affine X 𝒜 U

/-- A property of morphisms which respects isomorphisms holds for the induced morphism over an
affine piece if and only if it holds for the affine `Spec.map`. -/
theorem property_restrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : X.affineOpens) :
    P (φ.map ∣_ (affineι X ℬ U).opensRange) ↔
      P (Spec.map (CommRingCat.ofHom (φ.app U).toRingHom)) := by
  rw [P.arrow_mk_iso_iff (morphismRestrictOpensRange φ.map (affineι X ℬ U))]
  exact (P.arrow_mk_iso_iff (Arrow.isoMk (φ.isPullback_map U).flip.isoPullback
    (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id]
      exact (φ.isPullback_map U).flip.isoPullback_hom_snd))).symm

/-- A property local on the target holds for the induced morphism as soon as it holds for all
the affine `Spec.map`s. -/
theorem property_map_of_forall (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ U : X.affineOpens, P (Spec.map (CommRingCat.ofHom (φ.app U).toRingHom))) :
    P φ.map := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P)
    (fun U : X.affineOpens ↦ (affineι X ℬ U).opensRange)
    (iSup_opensRange_affineι X ℬ)).mpr fun U ↦ ?_
  rw [φ.property_restrict_iff P U]
  exact h U

/-- A surjective family of algebra maps induces a closed immersion of relative spectra. -/
theorem map_isClosedImmersion (h : ∀ U : X.affineOpens, Function.Surjective (φ.app U)) :
    IsClosedImmersion φ.map :=
  φ.property_map_of_forall @IsClosedImmersion fun U ↦
    IsClosedImmersion.spec_of_surjective _ (h U)

/-- A bijective family of algebra maps induces an isomorphism of relative spectra. -/
theorem isIso_map (h : ∀ U : X.affineOpens, Function.Bijective (φ.app U)) : IsIso φ.map :=
  φ.property_map_of_forall (MorphismProperty.isomorphisms Scheme) fun U ↦ by
    change IsIso _
    rw [isIso_SpecMap_iff]
    exact h U

end Hom

end RelativeSpec

end

end GromovWitten.AlgebraicGeometry
