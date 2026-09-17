/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ReesBaseChange
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The blowup of a scheme along a quasi-coherent ideal sheaf

The affine Rees blowup `Bl_I (Spec A) = Proj (⨁ Iⁿ)` of `ReesBlowup.lean` is glued here to a
blowup of an arbitrary scheme `X` along a quasi-coherent ideal sheaf `I`.  The gluing uses
Mathlib's relative gluing along the locally directed cover of `X` by all of its affine opens:
over an affine open `U` the piece is the affine blowup of `Spec Γ(X, U)` along `I(U)`, and for
affine opens `U ≤ V` the transition map is the coefficient extension of Rees algebras along the
restriction `Γ(X, V) → Γ(X, U)`, which lands in the Rees algebra of `I(U)` because `I` is
quasi-coherent (`I(U) = I(V)·Γ(X, U)`).  The transition squares are cartesian by the flat base
change theorem of `ReesBaseChange.lean`, since restriction to an affine open is flat.

The result is a scheme `blowup X I` with a projection `toBase X I` to `X` whose restriction to
every affine open is the affine Rees blowup (`isPullback_affine`).  The projection is proper
when `X` is locally Noetherian (`toBase_isProper`), it is an isomorphism away from the support
of `I` (`toBase_restrict_isIso`), and for an affine scheme the construction recovers the affine
blowup (`blowupIsoAffine`).
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Polynomial

namespace GromovWitten.AlgebraicGeometry

universe u

noncomputable section

/-! ### Blowup maps along an equality of extended ideals -/

namespace ReesBlowupOfEq

open ReesBlowup

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Coefficientwise extension of the Rees algebra of `I` into the Rees algebra of an ideal `J`
equal to the extension of `I`. -/
def reesMapOfEq (I : Ideal A) (f : A →+* B) (J : Ideal B) (h : I.map f = J) :
    reesAlgebra I →+* reesAlgebra J :=
  ((Polynomial.mapRingHom f).comp (reesAlgebra I).val.toRingHom).codRestrict (reesAlgebra J) (by
    intro p
    rw [mem_reesAlgebra_iff]
    intro n
    change ((p : A[X]).map f).coeff n ∈ J ^ n
    rw [coeff_map, ← h, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f (((mem_reesAlgebra_iff I (p : A[X])).mp p.property) n))

@[simp]
theorem reesMapOfEq_coe (I : Ideal A) (f : A →+* B) (J : Ideal B) (h : I.map f = J)
    (p : reesAlgebra I) : (reesMapOfEq I f J h p : B[X]) = (p : A[X]).map f :=
  rfl

theorem reesMapOfEq_mem_grade (I : Ideal A) (f : A →+* B) (J : Ideal B) (h : I.map f = J)
    (n : ℕ) (p : reesAlgebra I) (hp : p ∈ grade I n) :
    reesMapOfEq I f J h p ∈ grade J n := by
  change (p : A[X]).map f = monomial n (((p : A[X]).map f).coeff n)
  change (p : A[X]) = monomial n ((p : A[X]).coeff n) at hp
  rw [hp, map_monomial, coeff_monomial]
  simp

/-- The coefficientwise map as a graded ring homomorphism. -/
def gradedMapOfEq (I : Ideal A) (f : A →+* B) (J : Ideal B) (h : I.map f = J) :
    grade I →+*ᵍ grade J where
  toRingHom := reesMapOfEq I f J h
  map_mem := reesMapOfEq_mem_grade I f J h _ _

theorem gradedMapOfEq_rfl (I : Ideal A) (f : A →+* B) :
    gradedMapOfEq I f (I.map f) rfl = gradedMap I f :=
  rfl

theorem irrelevant_le_map_gradedMapOfEq (I : Ideal A) (f : A →+* B) (J : Ideal B)
    (h : I.map f = J) :
    HomogeneousIdeal.irrelevant (grade J) ≤
      (HomogeneousIdeal.irrelevant (grade I)).map (gradedMapOfEq I f J h) := by
  subst h
  exact irrelevant_le_map_gradedMap I f

/-- The blowup map along a ring homomorphism whose extended ideal is `J`. -/
def schemeMapOfEq (I : Ideal A) (f : A →+* B) (J : Ideal B) (h : I.map f = J) :
    scheme J ⟶ scheme I :=
  Proj.map (gradedMapOfEq I f J h) (irrelevant_le_map_gradedMapOfEq I f J h)

theorem schemeMapOfEq_rfl (I : Ideal A) (f : A →+* B) :
    schemeMapOfEq I f (I.map f) rfl = schemeMap I f :=
  rfl

theorem schemeMapOfEq_comp_projection (I : Ideal A) (f : A →+* B) (J : Ideal B)
    (h : I.map f = J) :
    schemeMapOfEq I f J h ≫ projection I = projection J ≫ Spec.map (CommRingCat.ofHom f) := by
  subst h
  exact schemeMap_comp_projection I f

/-- Blowup maps along flat ring homomorphisms are base changes. -/
theorem isPullback_schemeMapOfEq [Algebra A B] [Module.Flat A B] (I : Ideal A) (J : Ideal B)
    (h : I.map (algebraMap A B) = J) :
    IsPullback (schemeMapOfEq I (algebraMap A B) J h) (projection J) (projection I)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  subst h
  exact isPullback_schemeMap I

/-- `Proj.map` only depends on the graded ring homomorphism. -/
theorem projMap_congr {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B]
    [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    {φ φ' : 𝒜 →+*ᵍ ℬ} (e : φ = φ')
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ) :
    Proj.map φ hφ = Proj.map φ' (e ▸ hφ) := by
  subst e
  rfl

theorem schemeMapOfEq_congr (I : Ideal A) {f f' : A →+* B} (e : f = f') (J : Ideal B)
    (h : I.map f = J) :
    schemeMapOfEq I f J h = schemeMapOfEq I f' J (e ▸ h) := by
  subst e
  rfl

theorem gradedMapOfEq_comp {C : Type u} [CommRing C] (I : Ideal A) (f : A →+* B) (J : Ideal B)
    (h₁ : I.map f = J) (g : B →+* C) (K : Ideal C) (h₂ : J.map g = K) :
    (gradedMapOfEq J g K h₂).comp (gradedMapOfEq I f J h₁) =
      gradedMapOfEq I (g.comp f) K (by rw [← Ideal.map_map, h₁, h₂]) := by
  apply GradedRingHom.ext
  intro p
  apply Subtype.ext
  change ((p : A[X]).map f).map g = (p : A[X]).map (g.comp f)
  rw [Polynomial.map_map]

/-- Functoriality of blowup maps. -/
theorem schemeMapOfEq_comp {C : Type u} [CommRing C] (I : Ideal A) (f : A →+* B) (J : Ideal B)
    (h₁ : I.map f = J) (g : B →+* C) (K : Ideal C) (h₂ : J.map g = K) :
    schemeMapOfEq J g K h₂ ≫ schemeMapOfEq I f J h₁ =
      schemeMapOfEq I (g.comp f) K (by rw [← Ideal.map_map, h₁, h₂]) := by
  unfold schemeMapOfEq
  rw [← Proj.map_comp]
  exact projMap_congr (gradedMapOfEq_comp I f J h₁ g K h₂) _

theorem gradedMapOfEq_id (I : Ideal A) :
    gradedMapOfEq I (RingHom.id A) I (Ideal.map_id I) = GradedRingHom.id (grade I) := by
  apply GradedRingHom.ext
  intro p
  apply Subtype.ext
  change (p : A[X]).map (RingHom.id A) = p
  rw [Polynomial.map_id]

theorem schemeMapOfEq_id (I : Ideal A) :
    schemeMapOfEq I (RingHom.id A) I (Ideal.map_id I) = 𝟙 _ := by
  unfold schemeMapOfEq
  rw [projMap_congr (gradedMapOfEq_id I)]
  exact Proj.map_id

end ReesBlowupOfEq

/-! ### Gluing the affine blowups over the affine opens -/

namespace GlobalBlowup

open ReesBlowup ReesBlowupOfEq

/- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
type of affine opens; as in Mathlib's own development of that cover, the unifier is told not to
respect transparency in this section. -/
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The affineness of an affine open, with the type `IsAffineOpen`. -/
abbrev isAffineOpen (U : X.affineOpens) : IsAffineOpen U.1 := U.2

/-- The restriction homomorphism between the section rings of two affine opens. -/
abbrev res {U V : X.affineOpens} (h : U ≤ V) : Γ(X, V.1) →+* Γ(X, U.1) :=
  (X.presheaf.map (homOfLE (h : U.1 ≤ V.1)).op).hom

theorem res_refl (U : X.affineOpens) : res X (le_refl U) = RingHom.id _ := by
  change (X.presheaf.map (𝟙 _)).hom = RingHom.id _
  rw [X.presheaf.map_id]
  rfl

theorem res_comp {U V W : X.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    res X (h₁.trans h₂) = (res X h₁).comp (res X h₂) := by
  rw [res, res, res, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

/-- Restriction to an affine open of an affine open is flat: the general form of the
localization used by the affine gluing data. -/
theorem res_flat {U V : X.affineOpens} (h : U ≤ V) : (res X h).Flat := by
  have key := U.1.ι.flat_appLE (isAffineOpen X V) (isAffineOpen_top U.1.toScheme)
    (show (⊤ : U.1.toScheme.Opens) ≤ U.1.ι ⁻¹ᵁ V.1 from fun x _ ↦ h x.2)
  rw [Scheme.Opens.ι_appLE] at key
  have aux : ∀ (W : X.Opens) (hW : W = U.1) (e : W ≤ V.1),
      (X.presheaf.map (homOfLE e).op).hom.Flat → (res X h).Flat := by
    intro W hW e key'
    subst hW
    exact key'
  exact aux _ (Scheme.Opens.ι_image_top U.1) _ key

/-- The gluing functor: the affine Rees blowup of each affine open, with the coefficient
extension of Rees algebras as transition maps. -/
def gluingFunctor : X.affineOpens ⥤ Scheme.{u} where
  obj U := scheme (I.ideal U)
  map {U V} h :=
    schemeMapOfEq (I.ideal V) (res X (leOfHom h)) (I.ideal U) (I.map_ideal (leOfHom h))
  map_id U := by
    change schemeMapOfEq (I.ideal U) (res X (le_refl U)) (I.ideal U) _ = 𝟙 _
    rw [schemeMapOfEq_congr _ (res_refl X U)]
    exact schemeMapOfEq_id _
  map_comp {U V W} f g := by
    change schemeMapOfEq (I.ideal W) (res X ((leOfHom f).trans (leOfHom g))) (I.ideal U) _ = _
    rw [schemeMapOfEq_congr _ (res_comp X (leOfHom f) (leOfHom g))]
    exact (schemeMapOfEq_comp (I.ideal W) (res X (leOfHom g)) (I.ideal V) (I.map_ideal _)
      (res X (leOfHom f)) (I.ideal U) (I.map_ideal _)).symm

theorem gluingFunctor_obj (U : X.affineOpens) :
    (gluingFunctor X I).obj U = scheme (I.ideal U) :=
  rfl

theorem gluingFunctor_map {U V : X.affineOpens} (h : U ⟶ V) :
    (gluingFunctor X I).map h =
      schemeMapOfEq (I.ideal V) (res X (leOfHom h)) (I.ideal U) (I.map_ideal (leOfHom h)) :=
  rfl

/-- The structure map of the affine blowup of an affine open to that open. -/
def gluingApp (U : X.affineOpens) :
    (gluingFunctor X I).obj U ⟶ X.directedAffineCover.functorOfLocallyDirected.obj U :=
  ReesBlowup.projection (I.ideal U) ≫ (isAffineOpen X U).isoSpec.inv

theorem gluingApp_eq (U : X.affineOpens) :
    gluingApp X I U = ReesBlowup.projection (I.ideal U) ≫ (isAffineOpen X U).isoSpec.inv :=
  rfl

/-- The base isomorphisms are compatible with the restriction maps. -/
theorem specMap_res_comp_isoSpec_inv {U V : X.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (res X h)) ≫ (isAffineOpen X V).isoSpec.inv =
      (isAffineOpen X U).isoSpec.inv ≫ X.homOfLE (h : U.1 ≤ V.1) := by
  rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
  exact (isAffineOpen X V).map_fromSpec (isAffineOpen X U) (homOfLE (h : U.1 ≤ V.1)).op

/-- The cartesian square comparing the base isomorphisms. -/
theorem isPullback_specMap_res {U V : X.affineOpens} (h : U ≤ V) :
    IsPullback (Spec.map (CommRingCat.ofHom (res X h))) (isAffineOpen X U).isoSpec.inv
      (isAffineOpen X V).isoSpec.inv (X.homOfLE (h : U.1 ≤ V.1)) :=
  IsPullback.of_vert_isIso ⟨specMap_res_comp_isoSpec_inv X h⟩

/-- The structure maps form a natural transformation to the cover. -/
def gluingNatTrans : gluingFunctor X I ⟶ X.directedAffineCover.functorOfLocallyDirected where
  app := gluingApp X I
  naturality {U V} h := by
    rw [← homOfLE_leOfHom h, Scheme.Cover.functorOfLocallyDirected_map,
      Scheme.directedAffineCover_trans]
    change schemeMapOfEq (I.ideal V) (res X (leOfHom h)) (I.ideal U) _ ≫
        ReesBlowup.projection (I.ideal V) ≫ (isAffineOpen X V).isoSpec.inv =
      (ReesBlowup.projection (I.ideal U) ≫ (isAffineOpen X U).isoSpec.inv) ≫
        X.homOfLE (leOfHom h)
    rw [← Category.assoc, schemeMapOfEq_comp_projection, Category.assoc, Category.assoc,
      specMap_res_comp_isoSpec_inv]

/-- The transition squares are cartesian. -/
theorem gluingNatTrans_equifibered : (gluingNatTrans X I).Equifibered := by
  intro U V h
  rw [← homOfLE_leOfHom h, Scheme.Cover.functorOfLocallyDirected_map,
    Scheme.directedAffineCover_trans]
  change IsPullback (schemeMapOfEq (I.ideal V) (res X (leOfHom h)) (I.ideal U) _)
    (ReesBlowup.projection (I.ideal U) ≫ (isAffineOpen X U).isoSpec.inv)
    (ReesBlowup.projection (I.ideal V) ≫ (isAffineOpen X V).isoSpec.inv)
    (X.homOfLE (leOfHom h))
  let _ := (res X (leOfHom h)).toAlgebra
  have hflat : Module.Flat Γ(X, V.1) Γ(X, U.1) := res_flat X (leOfHom h)
  exact (isPullback_schemeMapOfEq (I.ideal V) (I.ideal U) (I.map_ideal (leOfHom h))).paste_vert
    (isPullback_specMap_res X (leOfHom h))

/-- The relative gluing datum of the affine Rees blowups over the affine opens. -/
def gluingData : X.directedAffineCover.RelativeGluingData where
  functor := gluingFunctor X I
  natTrans := gluingNatTrans X I
  equifibered := gluingNatTrans_equifibered X I

/-! ### The blowup and its projection -/

/-- The blowup of `X` along the quasi-coherent ideal sheaf `I`. -/
abbrev blowup : Scheme.{u} := (gluingData X I).glued

/-- The blowup projection `Bl_I X → X`. -/
def toBase : blowup X I ⟶ X := (gluingData X I).toBase

/-- The affine blowup of an affine open embeds into the global blowup. -/
def affineι (U : X.affineOpens) : scheme (I.ideal U) ⟶ blowup X I :=
  colimit.ι (gluingData X I).functor U

instance affineι_isOpenImmersion (U : X.affineOpens) : IsOpenImmersion (affineι X I U) := by
  have := (gluingData X I).cover.map_prop U
  rwa [Scheme.Cover.RelativeGluingData.cover_f] at this

/-- Over every affine open, the global blowup is the affine Rees blowup. -/
theorem isPullback_affine (U : X.affineOpens) :
    IsPullback (ReesBlowup.projection (I.ideal U) ≫ (isAffineOpen X U).isoSpec.inv)
      (affineι X I U) U.1.ι (toBase X I) :=
  (gluingData X I).isPullback_natTrans_ι_toBase U

/-- The affine pieces cover the blowup. -/
theorem iSup_opensRange_affineι : ⨆ U : X.affineOpens, (affineι X I U).opensRange = ⊤ :=
  (gluingData X I).cover.iSup_opensRange

/-- A property of morphisms which respects isomorphisms holds for the projection over an affine
open if and only if it holds for the affine blowup projection. -/
theorem property_restrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : X.affineOpens) :
    P (toBase X I ∣_ U.1.ι.opensRange) ↔
      P (ReesBlowup.projection (I.ideal U) ≫ (isAffineOpen X U).isoSpec.inv) := by
  rw [P.arrow_mk_iso_iff (morphismRestrictOpensRange (toBase X I) U.1.ι)]
  exact (P.arrow_mk_iso_iff (Arrow.isoMk (isPullback_affine X I U).flip.isoPullback
    (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id]
      exact (isPullback_affine X I U).flip.isoPullback_hom_snd))).symm

theorem property_restrict_iff' (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : X.affineOpens) :
    P (toBase X I ∣_ U.1) ↔
      P (ReesBlowup.projection (I.ideal U) ≫ (isAffineOpen X U).isoSpec.inv) := by
  rw [← property_restrict_iff X I P U, Scheme.Opens.opensRange_ι]

/-- The blowup of a locally Noetherian scheme is proper over it. -/
theorem toBase_isProper [IsLocallyNoetherian X] : IsProper (toBase X I) := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsProper)
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X)).mpr fun U ↦ ?_
  rw [property_restrict_iff' X I @IsProper U]
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsProper (ReesBlowup.projection (I.ideal U)) := projection_isProper (I.ideal U)
  infer_instance

/-! ### The affine case -/

/-- The whole scheme as an affine open of an affine scheme. -/
abbrev topIndex [IsAffine X] : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩

/-- For an affine scheme, the affine blowup of the whole scheme maps isomorphically onto the
global blowup. -/
theorem isIso_affineι_top [IsAffine X] : IsIso (affineι X I (topIndex X)) := by
  have hι : MorphismProperty.isomorphisms Scheme (⊤ : X.Opens).ι :=
    (MorphismProperty.isomorphisms.iff _).mpr ⟨⟨X.topIso.inv, X.ι_toIso_inv, X.toIso_inv_ι⟩⟩
  exact MorphismProperty.of_isPullback (isPullback_affine X I (topIndex X)) hι

/-- The blowup of an affine scheme is the affine Rees blowup. -/
def blowupIsoAffine [IsAffine X] : scheme (I.ideal (topIndex X)) ≅ blowup X I :=
  have := isIso_affineι_top X I
  asIso (affineι X I (topIndex X))

theorem blowupIsoAffine_hom_toBase [IsAffine X] :
    (blowupIsoAffine X I).hom ≫ toBase X I =
      ReesBlowup.projection (I.ideal (topIndex X)) ≫
        (isAffineOpen X (topIndex X)).isoSpec.inv ≫ (⊤ : X.Opens).ι := by
  have h := (isPullback_affine X I (topIndex X)).w
  change affineι X I _ ≫ toBase X I = _
  rw [← h, Category.assoc]

/-! ### The blowup is an isomorphism away from the centre -/

/-- If a morphism is an isomorphism over an open `U`, it is an isomorphism over every open
contained in `U`. -/
theorem isIso_morphismRestrict_of_le {Y Z : Scheme.{u}} (f : Y ⟶ Z) {U V : Z.Opens}
    (hVU : V ≤ U) (hU : IsIso (f ∣_ U)) : IsIso (f ∣_ V) := by
  have h1 : MorphismProperty.isomorphisms Scheme (f ∣_ U) := hU
  have h2 : MorphismProperty.isomorphisms Scheme ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) :=
    IsZariskiLocalAtTarget.restrict h1 _
  have h3 : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  have h4 := (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp h2
  rw [h3] at h4
  exact h4

/-- The restriction of an isomorphism to any open is an isomorphism. -/
theorem isIso_morphismRestrict_of_isIso {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsIso f]
    (U : Z.Opens) : IsIso (f ∣_ U) := by
  have h : MorphismProperty.isomorphisms Scheme f := inferInstance
  exact IsZariskiLocalAtTarget.restrict h U

/-- The open complement of the support of the ideal sheaf: the locus away from the centre. -/
def centreComplement : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.2.isOpen_compl⟩

theorem mem_centreComplement {x : X} : x ∈ centreComplement X I ↔ x ∉ (I.support : Set X) :=
  Iff.rfl

/-- The part of an affine open lying away from the centre. -/
abbrev affineAway (U : X.affineOpens) : U.1.toScheme.Opens := U.1.ι ⁻¹ᵁ centreComplement X I

/-- Under the identification of an affine open with its spectrum, the locus away from the
centre lies in the complement of the zero locus of the ideal. -/
theorem isoSpec_inv_preimage_affineAway_le (U : X.affineOpens) :
    (isAffineOpen X U).isoSpec.inv ⁻¹ᵁ affineAway X I U ≤ baseComplement (I.ideal U) := by
  intro p hp
  have hp' : (isAffineOpen X U).fromSpec p ∉ (I.support : Set X) := by
    rw [← IsAffineOpen.isoSpec_inv_ι, Scheme.Hom.comp_apply]
    exact hp
  have hmem : (isAffineOpen X U).fromSpec p ∈ (U.1 : Set X) := by
    rw [← IsAffineOpen.range_fromSpec (isAffineOpen X U)]
    exact ⟨p, rfl⟩
  have hz : (isAffineOpen X U).fromSpec p ∉ X.zeroLocus (U := U.1) (I.ideal U : Set _) := by
    intro hz
    apply hp'
    have hI : (isAffineOpen X U).fromSpec p ∈ (I.support : Set X) ∩ U.1 := by
      rw [I.coe_support_inter U]
      exact ⟨hz, hmem⟩
    exact hI.1
  have hz' : p ∉ PrimeSpectrum.zeroLocus (I.ideal U : Set _) := by
    rw [← IsAffineOpen.fromSpec_preimage_zeroLocus]
    exact hz
  rw [PrimeSpectrum.mem_zeroLocus, Set.not_subset] at hz'
  obtain ⟨r, hr, hrp⟩ := hz'
  exact le_iSup (fun r : I.ideal U ↦
    (PrimeSpectrum.basicOpen r.1 : (Spec (.of Γ(X, U.1))).Opens)) ⟨r, hr⟩ hrp

/-- The affine blowup projection is an isomorphism away from the centre. -/
theorem isIso_gluingApp_restrict (U : X.affineOpens) :
    IsIso (gluingApp X I U ∣_ affineAway X I U) := by
  rw [gluingApp_eq, morphismRestrict_comp]
  have h1 : IsIso (ReesBlowup.projection (I.ideal U) ∣_
      ((isAffineOpen X U).isoSpec.inv ⁻¹ᵁ affineAway X I U)) :=
    isIso_morphismRestrict_of_le _ (isoSpec_inv_preimage_affineAway_le X I U)
      (projection_restrict_baseComplement_isIso _)
  have h2 : IsIso ((isAffineOpen X U).isoSpec.inv ∣_ affineAway X I U) :=
    isIso_morphismRestrict_of_isIso _ _
  exact IsIso.comp_isIso' h1 h2

theorem isPullback_affine' (U : X.affineOpens) :
    IsPullback (gluingApp X I U) (affineι X I U) U.1.ι (toBase X I) :=
  isPullback_affine X I U

/-- The restriction of the affine blowup projection to an open of the affine open is a base
change of the global projection. -/
theorem isPullback_restrict (U : X.affineOpens) (V : U.1.toScheme.Opens) :
    IsPullback (gluingApp X I U ∣_ V) ((gluingApp X I U ⁻¹ᵁ V).ι ≫ affineι X I U)
      (V.ι ≫ U.1.ι) (toBase X I) :=
  (isPullback_morphismRestrict (gluingApp X I U) V).paste_vert (isPullback_affine' X I U)

theorem range_affineAway_ι_comp_ι_subset (U : X.affineOpens) :
    Set.range ((affineAway X I U).ι ≫ U.1.ι) ⊆ Set.range (centreComplement X I).ι := by
  rintro _ ⟨q, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
  exact q.2

/-- The piece of the cover of the locus away from the centre given by an affine open. -/
def awayCoverMap (U : X.affineOpens) :
    (affineAway X I U).toScheme ⟶ (centreComplement X I).toScheme :=
  IsOpenImmersion.lift (centreComplement X I).ι ((affineAway X I U).ι ≫ U.1.ι)
    (range_affineAway_ι_comp_ι_subset X I U)

theorem awayCoverMap_ι (U : X.affineOpens) :
    awayCoverMap X I U ≫ (centreComplement X I).ι = (affineAway X I U).ι ≫ U.1.ι :=
  IsOpenImmersion.lift_fac _ _ _

instance awayCoverMap_isOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion (awayCoverMap X I U) := by
  unfold awayCoverMap
  infer_instance

/-- The open cover of the locus away from the centre by the parts of the affine opens. -/
def awayCover : (centreComplement X I).toScheme.OpenCover where
  I₀ := X.affineOpens
  X U := (affineAway X I U).toScheme
  f U := awayCoverMap X I U
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun w ↦ ?_, fun U ↦ ?_⟩
    · obtain ⟨U, hU⟩ : ∃ U : X.affineOpens, (centreComplement X I).ι w ∈ U.1 := by
        have hw : (centreComplement X I).ι w ∈ (⊤ : X.Opens) := trivial
        rw [← iSup_affineOpens_eq_top X] at hw
        exact Opens.mem_iSup.mp hw
      let q : U.1.toScheme := ⟨(centreComplement X I).ι w, hU⟩
      have hq : q ∈ affineAway X I U := w.2
      refine ⟨U, ⟨q, hq⟩, ?_⟩
      apply (centreComplement X I).ι.isOpenEmbedding.injective
      change (awayCoverMap X I U ≫ (centreComplement X I).ι) ⟨q, hq⟩ = _
      rw [awayCoverMap_ι]
      rfl
    · exact awayCoverMap_isOpenImmersion X I U

/-- The affine piece of the blowup away from the centre lifts into the part of the blowup
lying over the locus away from the centre. -/
theorem range_restrict_subset (U : X.affineOpens) :
    Set.range ((gluingApp X I U ⁻¹ᵁ affineAway X I U).ι ≫ affineι X I U) ⊆
      Set.range (toBase X I ⁻¹ᵁ centreComplement X I).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  change toBase X I (((gluingApp X I U ⁻¹ᵁ affineAway X I U).ι ≫ affineι X I U) y) ∈
    centreComplement X I
  rw [← Scheme.Hom.comp_apply, ← (isPullback_restrict X I U (affineAway X I U)).w,
    Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact ((gluingApp X I U ∣_ affineAway X I U) y).2

/-- The affine piece of the blowup away from the centre, as a morphism into the part of the
blowup over the locus away from the centre. -/
def awayPieceMap (U : X.affineOpens) :
    (gluingApp X I U ⁻¹ᵁ affineAway X I U).toScheme ⟶
      (toBase X I ⁻¹ᵁ centreComplement X I).toScheme :=
  IsOpenImmersion.lift (toBase X I ⁻¹ᵁ centreComplement X I).ι
    ((gluingApp X I U ⁻¹ᵁ affineAway X I U).ι ≫ affineι X I U) (range_restrict_subset X I U)

theorem awayPieceMap_ι (U : X.affineOpens) :
    awayPieceMap X I U ≫ (toBase X I ⁻¹ᵁ centreComplement X I).ι =
      (gluingApp X I U ⁻¹ᵁ affineAway X I U).ι ≫ affineι X I U :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restriction of the projection to the locus away from the centre is, over each affine
piece, the restriction of the affine blowup projection. -/
theorem isPullback_awayPiece (U : X.affineOpens) :
    IsPullback (gluingApp X I U ∣_ affineAway X I U) (awayPieceMap X I U) (awayCoverMap X I U)
      (toBase X I ∣_ centreComplement X I) := by
  have big := isPullback_restrict X I U (affineAway X I U)
  rw [← awayCoverMap_ι, ← awayPieceMap_ι] at big
  refine IsPullback.of_bot big ?_ (isPullback_morphismRestrict (toBase X I) (centreComplement X I))
  rw [← cancel_mono (centreComplement X I).ι, Category.assoc, Category.assoc, awayCoverMap_ι,
    morphismRestrict_ι, reassoc_of% (awayPieceMap_ι X I U)]
  exact (isPullback_restrict X I U (affineAway X I U)).w

/-- The blowup projection is an isomorphism away from the centre. -/
theorem toBase_restrict_isIso : IsIso (toBase X I ∣_ centreComplement X I) := by
  refine (MorphismProperty.isomorphisms.iff _).mp ?_
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun U : X.affineOpens ↦ (awayCoverMap X I U).opensRange)
    (awayCover X I).iSup_opensRange).mpr fun U ↦ ?_
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictOpensRange (toBase X I ∣_ centreComplement X I) (awayCoverMap X I U))]
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (Arrow.isoMk (isPullback_awayPiece X I U).flip.isoPullback (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id]
      exact (isPullback_awayPiece X I U).flip.isoPullback_hom_snd))).mp ?_
  exact (MorphismProperty.isomorphisms.iff _).mpr (isIso_gluingApp_restrict X I U)

end GlobalBlowup

end

end GromovWitten.AlgebraicGeometry
