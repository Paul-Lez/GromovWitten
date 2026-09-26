/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.CommonModification
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The closure model: the scheme-theoretic closure of the generic fibre

Let `R` be a discrete valuation ring with fraction field `K` and let `p : Z ⟶ Spec R` be an
arbitrary morphism.  The *closure model* of `Z` is the scheme-theoretic closure of the generic
fibre `Z_K = Z ×_{Spec R} Spec K` inside `Z`, that is, the closed subscheme of `Z` cut out by the
ideal sheaf of `π`-power torsion.  On an affine open `U = Spec A` it is `Spec (A ⧸ A[π^∞])`, where
`A[π^∞] = {a | ∃ n, π ^ n • a = 0}` is exactly the kernel of `A → A ⊗_R K = A[1/π]`.

Rather than building the torsion ideal sheaf by hand (which would require proving the
compatibility of torsion with localisation), we realise it as the kernel ideal sheaf
`Scheme.Hom.ker` of the inclusion of the generic fibre: the component of `Scheme.Hom.ker` at an
affine open `U` is, for a quasi-compact morphism, literally `RingHom.ker (Γ(Z, U) → Γ(Z_K, ·))`
(`AlgebraicGeometry.Scheme.Hom.ker_apply`), and Mathlib's `Scheme.IdealSheafData` structure
supplies the localisation compatibility for free.  The closure model is therefore
`Scheme.Hom.image` of the generic-fibre inclusion.  That this kernel coincides with the `π`-power
torsion is the classical description of the same ideal (`Γ(Z_K, ·)` is the localisation of
`Γ(Z, U)` at `π` over an affine open); that identification is nowhere needed below and is not
formalised here -- all the results are proved directly from the kernel description.

## Main results

* `piTorsionIdeal`, `closureModel`, `closureModelι`: the `π`-power-torsion ideal sheaf, the closure
  model and its closed immersion into `Z`.
* `flat_closureModel`: **the closure model is flat over `R`**.  Chart by chart it is
  `Γ(Z, U) ⧸ RingHom.ker (Γ(Z, U) → Γ(Z_K, ·))`, which embeds into a `K`-algebra, hence is torsion
  free over `R`, hence flat (`RingHom.Flat.quotient_ker_of_field_algebra`).
* `isIso_genericFiberMap_closureModelι`, `closureModelGenericFiberIso`: the closure model has the
  same generic fibre as `Z`, i.e. the base change of `closureModelι` to `Spec K` is an isomorphism.
* `isIso_closureModelι_of_flat`: if `Z` is already flat over `R` then `closureModelι` is an
  isomorphism, so `Z` is its own closure model.
* `quasiCompact_closureModel`, `locallyOfFinitePresentation_closureModel`,
  `isProper_closureModel`: the closure model inherits the finiteness properties of `Z`.
* `isPullback_baseChangeHom`, `ModelModification.isIso_genericFiberMap_pullbackFst`: the generic
  fibre of a fibre product is the fibre product of the generic fibres, so the projections of the
  fibre product of two modifications are isomorphisms on generic fibres.
* `ModelModification.commonModel`: the closure model of the fibre product of two modifications of
  models of a curve `C` is again a model of `C` (unconditionally), and
  `ModelModification.commonModificationFst`, `ModelModification.commonModificationSnd` exhibit it
  as a modification of both `M` and `N`.  This closes both gaps documented in
  `CommonModification.lean`: flatness of the common scheme dominating two modifications, and the
  identification of its generic fibre with the fixed curve `C`.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

/-! ### Flatness of a quotient by the kernel of a map into a `K`-algebra -/

/-- Let `R` be a Bezout domain with a ring map to a field `K`, let `A` be an `R`-algebra and let
`ψ : A →+* B` be a ring map whose target is simultaneously a `K`-algebra, compatibly with the
`R`-structures.  Then `A ⧸ ker ψ` is flat over `R`: it embeds into `B`, on which every nonzero
element of `R` acts invertibly, so it is a torsion-free `R`-module. -/
theorem RingHom.Flat.quotient_ker_of_field_algebra {R A B K : Type u} [CommRing R] [IsDomain R]
    [IsBezout R] [CommRing A] [CommRing B] [Field K] (φ : R →+* A) (ψ : A →+* B) (ι : R →+* K)
    (χ : K →+* B) (J : Ideal A) (hJ : J = RingHom.ker ψ) (hcomm : ψ.comp φ = χ.comp ι)
    (hι : Function.Injective ι) : ((Ideal.Quotient.mk J).comp φ).Flat := by
  have hJψ : ∀ a ∈ J, ψ a = 0 := fun a ha ↦ by rw [hJ] at ha; exact ha
  set ξ : A ⧸ J →+* B := Ideal.Quotient.lift J ψ hJψ with hξdef
  have hξ : Function.Injective ξ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hξdef, Ideal.Quotient.lift_mk] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, hJ]
    exact hx
  let _ := ((Ideal.Quotient.mk J).comp φ).toAlgebra
  change Module.Flat R (A ⧸ J)
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro x hx
  obtain ⟨⟨r, hr⟩, hrx⟩ := (Submodule.mem_torsion_iff x).mp hx
  rw [Submonoid.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hrx
  rw [Submodule.mem_bot]
  have hune : ι r ≠ 0 := fun h ↦
    mem_nonZeroDivisors_iff_ne_zero.mp hr (hι (h.trans (map_zero ι).symm))
  have hunit : IsUnit (χ (ι r)) := (isUnit_iff_ne_zero.mpr hune).map χ
  have hzero : ξ x = 0 := by
    have h0 : ξ (((Ideal.Quotient.mk J).comp φ) r * x) = 0 := by rw [hrx, map_zero]
    rw [map_mul] at h0
    have hmk : ξ (((Ideal.Quotient.mk J).comp φ) r) = χ (ι r) := by
      rw [RingHom.comp_apply, hξdef, Ideal.Quotient.lift_mk, ← RingHom.comp_apply, hcomm,
        RingHom.comp_apply]
    rw [hmk] at h0
    exact (hunit.mul_right_eq_zero).mp h0
  exact hξ (hzero.trans (map_zero ξ).symm)

/-! ### The structure map on an affine chart -/

section AffineChart

/-- Every open of the source is contained in the preimage of the top open.  Stated so that the
proof term has the syntactic type expected by `Scheme.Hom.appLE`, which `le_top` does not. -/
theorem le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) : U ≤ f ⁻¹ᵁ ⊤ := by simp

/-- Two equal morphisms of schemes have the same restriction maps on sections. -/
theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (toBase : Z ⟶ Spec (.of R))

/-- The structure map of a scheme over `Spec R`, restricted to an affine open, as a ring map. -/
def affineBaseMap (U : Z.affineOpens) : R →+* Γ(Z, U.1) :=
  (toBase.appLE ⊤ U.1 (le_preimage_top toBase U.1)).hom.comp
    (Scheme.ΓSpecIso (.of R)).inv.hom

/-- The structure map of a scheme over `Spec R`, restricted to an affine open, is the `Spec` of
`affineBaseMap`. -/
theorem fromSpec_comp_toBase (U : Z.affineOpens) :
    U.2.fromSpec ≫ toBase = Spec.map (CommRingCat.ofHom (affineBaseMap toBase U)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec toBase (isAffineOpen_top _) U.2 le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

end AffineChart

/-! ### The closure model -/

section ClosureModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {Z : Scheme.{u}} (toBase : Z ⟶ Spec (.of R))

/-- The inclusion of the generic fibre of `toBase` into the total space. -/
abbrev genericFiberInclusion : pullback toBase (genericPointMap R K) ⟶ Z :=
  pullback.fst toBase (genericPointMap R K)

/-- The `K`-algebra structure on the sections of the generic fibre over the preimage of an
affine open of `Z`. -/
def genericFiberChartMap (U : Z.affineOpens) :
    K →+* Γ(pullback toBase (genericPointMap R K),
      genericFiberInclusion (K := K) toBase ⁻¹ᵁ U.1) :=
  ((pullback.snd toBase (genericPointMap R K)).appLE ⊤ _ le_top).hom.comp
    (Scheme.ΓSpecIso (.of K)).inv.hom

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- Restricting the structure map of `Z` to an affine open and then to the generic fibre is the
same as going through `K`: the two ring maps `R → Γ(Z_K, ·)` obtained from the two sides of the
pullback square agree. -/
theorem app_comp_affineBaseMap (U : Z.affineOpens) :
    ((genericFiberInclusion (K := K) toBase).app U.1).hom.comp (affineBaseMap toBase U) =
      (genericFiberChartMap (K := K) toBase U).comp (algebraMap R K) := by
  have hcond : genericFiberInclusion (K := K) toBase ≫ toBase =
      pullback.snd toBase (genericPointMap R K) ≫ genericPointMap R K := pullback.condition
  have h1 : toBase.appLE ⊤ U.1 (le_preimage_top toBase U.1) ≫
        (genericFiberInclusion (K := K) toBase).app U.1
      = (genericFiberInclusion (K := K) toBase ≫ toBase).appLE ⊤
          (genericFiberInclusion (K := K) toBase ⁻¹ᵁ U.1)
          (le_preimage_top _ _) := by
    rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]
  have h2 : (pullback.snd toBase (genericPointMap R K) ≫ genericPointMap R K).appLE ⊤
        (genericFiberInclusion (K := K) toBase ⁻¹ᵁ U.1) (le_preimage_top _ _)
      = (genericPointMap R K).appTop ≫
        (pullback.snd toBase (genericPointMap R K)).appLE ⊤
          (genericFiberInclusion (K := K) toBase ⁻¹ᵁ U.1) (le_preimage_top _ _) := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have key : (Scheme.ΓSpecIso (.of R)).inv ≫
        toBase.appLE ⊤ U.1 (le_preimage_top toBase U.1) ≫
          (genericFiberInclusion (K := K) toBase).app U.1
      = CommRingCat.ofHom (algebraMap R K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
        (pullback.snd toBase (genericPointMap R K)).appLE ⊤
          (genericFiberInclusion (K := K) toBase ⁻¹ᵁ U.1) (le_preimage_top _ _) := by
    rw [h1, appLE_congr_hom hcond ⊤ _ _ (le_preimage_top _ _), h2,
      Scheme.ΓSpecIso_inv_naturality_assoc]
    rfl
  have hkey := congrArg CommRingCat.Hom.hom key
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hkey
  simp only [affineBaseMap, genericFiberChartMap]
  exact hkey

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The map on global sections induced by the inclusion of the generic point is injective. -/
theorem injective_appTop_genericPointMap :
    Function.Injective ((genericPointMap R K).appTop).hom := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K))
  have h2 : (genericPointMap R K).appTop =
      (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom (algebraMap R K) ≫
        (Scheme.ΓSpecIso (.of K)).inv := by
    rw [← Category.assoc, ← h]
    simp [genericPointMap]
  rw [h2]
  simp only [CommRingCat.hom_comp]
  exact ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.injective.comp
    (IsFractionRing.injective R K)).comp
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective

/-- The inclusion of the generic point of `Spec R` is scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_genericPointMap :
    IsSchemeTheoreticallyDominant (genericPointMap R K) := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    ← RingHom.injective_iff_ker_eq_bot]
  exact injective_appTop_genericPointMap

/-- The ideal sheaf of `π`-power torsion on `Z`, realised as the kernel ideal sheaf of the
inclusion of the generic fibre: on an affine open `U` its component is the kernel of
`Γ(Z, U) → Γ(Z_K, ·)` (classically, the sections killed by a power of a uniformiser; see the
module docstring). -/
abbrev piTorsionIdeal : Z.IdealSheafData := (genericFiberInclusion (K := K) toBase).ker

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- On an affine open, the `π`-power-torsion ideal is the kernel of the restriction map to the
generic fibre. -/
theorem piTorsionIdeal_ideal (U : Z.affineOpens) :
    (piTorsionIdeal (K := K) toBase).ideal U =
      RingHom.ker ((genericFiberInclusion (K := K) toBase).app U.1).hom :=
  Scheme.Hom.ker_apply _ U

/-- The closure model of `Z` over `R`: the scheme-theoretic closure of the generic fibre inside
`Z`, that is, the closed subscheme cut out by the `π`-power-torsion ideal sheaf. -/
abbrev closureModel : Scheme.{u} := (piTorsionIdeal (K := K) toBase).subscheme

/-- The canonical closed immersion of the closure model into `Z`. -/
abbrev closureModelι : closureModel (K := K) toBase ⟶ Z :=
  (piTorsionIdeal (K := K) toBase).subschemeι

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The closure model is the scheme-theoretic image of the generic fibre. -/
theorem closureModel_eq_image :
    closureModel (K := K) toBase = (genericFiberInclusion (K := K) toBase).image := rfl

/-- Each affine chart of the closure model is flat over `R`: the chart ring is a quotient of
`Γ(Z, U)` by the kernel of the map into the sections of the generic fibre, hence embeds into a
`K`-algebra, hence is torsion free over the Bezout domain `R`. -/
theorem flat_closureModel_chart (U : Z.affineOpens) :
    ((Ideal.Quotient.mk ((piTorsionIdeal (K := K) toBase).ideal U)).comp
      (affineBaseMap toBase U)).Flat :=
  RingHom.Flat.quotient_ker_of_field_algebra (affineBaseMap toBase U)
    ((genericFiberInclusion (K := K) toBase).app U.1).hom (algebraMap R K)
    (genericFiberChartMap (K := K) toBase U) _ (piTorsionIdeal_ideal toBase U)
    (app_comp_affineBaseMap toBase U) (IsFractionRing.injective R K)

/- The index type of the subscheme cover is only definitionally the type of affine opens, and
`Flat` is only definitionally a morphism property; as in `ModelBlowup`, the unifier is told not to
respect reducibility. -/
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
set_option backward.isDefEq.respectTransparency false in
/-- The chart of the closure model attached to an affine open `U` of `Z` is the spectrum of
`Γ(Z, U)` modulo the torsion ideal, over `Spec R`. -/
theorem subschemeCover_comp_closureModelι_comp (U : Z.affineOpens) :
    (piTorsionIdeal (K := K) toBase).subschemeCover.f U ≫
        (closureModelι (K := K) toBase ≫ toBase) =
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk ((piTorsionIdeal (K := K) toBase).ideal U)).comp
          (affineBaseMap toBase U))) := by
  rw [← Category.assoc, Scheme.IdealSheafData.subschemeCover_map_subschemeι,
    Scheme.IdealSheafData.glueDataObjι_ι, Category.assoc, fromSpec_comp_toBase,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- See the comment on `subschemeCover_comp_closureModelι_comp`. -/
set_option backward.isDefEq.respectTransparency false in
/-- **The closure model is flat over the base DVR.**  Chart by chart it is a quotient of
`Γ(Z, U)` by the kernel of the map to the generic fibre, which is a torsion-free `R`-module. -/
theorem flat_closureModel : Flat (closureModelι (K := K) toBase ≫ toBase) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat)
    (piTorsionIdeal (K := K) toBase).subschemeCover.openCover fun U ↦ ?_
  rw [show (piTorsionIdeal (K := K) toBase).subschemeCover.openCover.f U =
    (piTorsionIdeal (K := K) toBase).subschemeCover.f U from rfl,
    subschemeCover_comp_closureModelι_comp]
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (flat_closureModel_chart toBase U)

/-! ### The closure model has the same generic fibre -/

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The generic fibre factors through the closure model, which is its scheme-theoretic image. -/
theorem toImage_comp_closureModelι :
    Scheme.Hom.toImage (genericFiberInclusion (K := K) toBase) ≫ closureModelι toBase =
      genericFiberInclusion (K := K) toBase :=
  Scheme.Hom.toImage_imageι _

/-- The inverse of the base change of `closureModelι` to `Spec K`: the generic fibre of `Z` maps
to the closure model, over `Spec K`. -/
def genericFiberToClosureModel :
    pullback toBase (genericPointMap R K) ⟶
      pullback (closureModelι (K := K) toBase ≫ toBase) (genericPointMap R K) :=
  pullback.lift (Scheme.Hom.toImage (genericFiberInclusion (K := K) toBase))
    (pullback.snd toBase (genericPointMap R K)) (by
      rw [← Category.assoc, toImage_comp_closureModelι]
      exact pullback.condition)

/-- **The closure model has the same generic fibre as `Z`**: the base change of the closed
immersion `closureModelι` along `Spec K ⟶ Spec R` is an isomorphism.  Indeed the generic fibre
factors through its scheme-theoretic image, and `closureModelι` is a monomorphism. -/
instance isIso_genericFiberMap_closureModelι :
    IsIso (genericFiberMap (K := K) (closureModelι (K := K) toBase) toBase) := by
  refine ⟨genericFiberToClosureModel (K := K) toBase, ?_, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, genericFiberToClosureModel, pullback.lift_fst, Category.id_comp,
        ← cancel_mono (closureModelι (K := K) toBase), Category.assoc,
        toImage_comp_closureModelι, genericFiberMap_fst]
    · rw [Category.assoc, genericFiberToClosureModel, pullback.lift_snd, Category.id_comp,
        genericFiberMap_snd]
  · apply pullback.hom_ext
    · rw [Category.assoc, genericFiberMap_fst, ← Category.assoc,
        genericFiberToClosureModel, pullback.lift_fst, toImage_comp_closureModelι,
        Category.id_comp]
    · rw [Category.assoc, genericFiberMap_snd, genericFiberToClosureModel, pullback.lift_snd,
        Category.id_comp]

/-- The generic fibre of the closure model, identified with the generic fibre of `Z` as a scheme
over `Spec K`. -/
def closureModelGenericFiberIso :
    genericFiber R K (closureModelι (K := K) toBase ≫ toBase) ≅ genericFiber R K toBase :=
  Over.isoMk (asIso (genericFiberMap (K := K) (closureModelι (K := K) toBase) toBase))
    (genericFiberMap_snd _ _)

/-! ### The closure model of a flat scheme, and finiteness properties -/

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- If `Z` is flat over `R` then its generic fibre is scheme-theoretically dominant in `Z`
(Mathlib's `IsSchemeTheoreticallyDominant.pullbackFst`), so the `π`-power-torsion ideal sheaf
vanishes. -/
theorem piTorsionIdeal_eq_bot_of_flat [Flat toBase] : piTorsionIdeal (K := K) toBase = ⊥ :=
  Scheme.Hom.ker_eq_bot _

/-- If `Z` is already flat over `R`, the closed immersion of the closure model is an
isomorphism: `Z` is its own closure model. -/
instance isIso_closureModelι_of_flat [Flat toBase] : IsIso (closureModelι (K := K) toBase) :=
  (Scheme.isIso_subschemeι_iff_eq_bot _).mpr (piTorsionIdeal_eq_bot_of_flat toBase)

/-- The closure model is quasi-compact over the base whenever `Z` is. -/
instance quasiCompact_closureModel [QuasiCompact toBase] :
    QuasiCompact (closureModelι (K := K) toBase ≫ toBase) := inferInstance

/-- The closure model is of locally finite presentation over the base whenever `Z` is: it is a
closed subscheme of a scheme of finite type over the Noetherian ring `R`, hence of finite type,
hence of finite presentation. -/
instance locallyOfFinitePresentation_closureModel [LocallyOfFinitePresentation toBase] :
    LocallyOfFinitePresentation (closureModelι (K := K) toBase ≫ toBase) := inferInstance

/-- The closure model is proper over the base whenever `Z` is. -/
instance isProper_closureModel [_root_.AlgebraicGeometry.IsProper toBase] :
    _root_.AlgebraicGeometry.IsProper (closureModelι (K := K) toBase ≫ toBase) := inferInstance

end ClosureModel

/-! ### The generic fibre of a composite -/

section GenericFiberComp

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The generic fibre map of a composite is, up to the reassociation isomorphism of pullbacks,
the composite of the generic fibre maps. -/
theorem genericFiberMap_comp {A B X : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ X)
    (p : X ⟶ Spec (.of R)) :
    genericFiberMap (K := K) (a ≫ b) p =
      (pullback.congrHom (Category.assoc a b p) rfl).hom ≫
        genericFiberMap (K := K) a (b ≫ p) ≫ genericFiberMap (K := K) b p := by
  apply pullback.hom_ext
  · simp [pullback.congrHom, pullback.map, pullback.lift_fst_assoc, genericFiberMap_fst]
  · simp [pullback.congrHom, pullback.map, pullback.lift_snd, genericFiberMap_snd]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- If both factors of a composite induce isomorphisms on generic fibres, so does the
composite. -/
theorem isIso_genericFiberMap_comp {A B X : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ X)
    (p : X ⟶ Spec (.of R)) (ha : IsIso (genericFiberMap (K := K) a (b ≫ p)))
    (hb : IsIso (genericFiberMap (K := K) b p)) :
    IsIso (genericFiberMap (K := K) (a ≫ b) p) := by
  rw [genericFiberMap_comp]
  have := ha
  have := hb
  infer_instance

namespace Model

variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)} {M N : Model R K C toK}

/-- The base-change map on generic fibres attached to a morphism over the base, composed with the
first projection. -/
@[reassoc]
theorem baseChangeHom_comp_fst (h : M.total ⟶ N.total) (ob : h ≫ N.toBase = M.toBase) :
    Model.baseChangeHom (R := R) (K := K) h ob ≫
        pullback.fst N.toBase (genericPointMap R K) =
      pullback.fst M.toBase (genericPointMap R K) ≫ h :=
  pullback.lift_fst _ _ _

/-- The base-change map on generic fibres attached to a morphism over the base, composed with the
second projection. -/
@[reassoc]
theorem baseChangeHom_comp_snd (h : M.total ⟶ N.total) (ob : h ≫ N.toBase = M.toBase) :
    Model.baseChangeHom (R := R) (K := K) h ob ≫
        pullback.snd N.toBase (genericPointMap R K) =
      pullback.snd M.toBase (genericPointMap R K) :=
  pullback.lift_snd _ _ _

end Model

/-- The reassociation isomorphism of pullbacks is compatible with the first projections. -/
theorem congrHom_hom_comp_fst {X Y S : Scheme.{u}} {f₁ f₂ : X ⟶ S} {g₁ g₂ : Y ⟶ S}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.fst f₂ g₂ = pullback.fst f₁ g₁ := by
  simp [pullback.congrHom, pullback.map, pullback.lift_fst]

/-- The reassociation isomorphism of pullbacks is compatible with the second projections. -/
theorem congrHom_hom_comp_snd {X Y S : Scheme.{u}} {f₁ f₂ : X ⟶ S} {g₁ g₂ : Y ⟶ S}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ := by
  simp [pullback.congrHom, pullback.map, pullback.lift_snd]

variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)} {M N : Model R K C toK}

/-- The generic fibre of `M` is the fibre product of `M.total` with the generic fibre of `N` over
`N.total`, for any morphism `M.total ⟶ N.total` over the base. -/
theorem isPullback_baseChangeHom (h : M.total ⟶ N.total) (ob : h ≫ N.toBase = M.toBase) :
    IsPullback (Model.baseChangeHom (R := R) (K := K) h ob)
      (pullback.fst M.toBase (genericPointMap R K))
      (pullback.fst N.toBase (genericPointMap R K)) h := by
  refine (isPullback_genericFiberMap (K := K) h N.toBase).flip.of_iso
    (pullback.congrHom ob rfl) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id]
    apply pullback.hom_ext
    · rw [genericFiberMap_fst, Category.assoc, Model.baseChangeHom_comp_fst,
        ← Category.assoc, congrHom_hom_comp_fst]
    · rw [genericFiberMap_snd, Category.assoc, Model.baseChangeHom_comp_snd,
        congrHom_hom_comp_snd]
  · rw [Iso.refl_hom, Category.comp_id, congrHom_hom_comp_fst]
  · rw [Iso.refl_hom, Category.comp_id, Iso.refl_hom, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, Iso.refl_hom, Category.id_comp]

/-- In a pullback square whose right-hand map is an isomorphism, the left-hand projection is an
isomorphism. -/
theorem isIso_fst_of_isPullback {W X Y Z : Scheme.{u}} {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (H : IsPullback fst snd f g) [IsIso g] : IsIso fst := by
  refine ⟨H.lift (𝟙 X) (f ≫ inv g) (by simp), ?_, H.lift_fst _ _ _⟩
  apply H.hom_ext
  · rw [Category.assoc, H.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, H.lift_snd, Category.id_comp, ← Category.assoc, H.w,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end GenericFiberComp

/-! ### Application: a common model dominating two modifications -/

section CommonModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

namespace ModelModification

/-- The total-space morphism underlying a modification of models is proper. -/
instance isProper_modification_hom {M P : Model R K C toK} (f : ModelModification M P) :
    _root_.AlgebraicGeometry.IsProper f.hom.hom := f.proper

variable {M N P : Model R K C toK} (f : ModelModification M P) (g : ModelModification N P)

/-- The structure map of the fibre product of two modifications, spelled out; this is
`ModelModification.commonToBase f g` by definition. -/
theorem fst_comp_toBase_eq_commonToBase :
    pullback.fst f.hom.hom g.hom.hom ≫ M.toBase = commonToBase f g := rfl

/-- The two structure maps of the fibre product of two modifications agree. -/
theorem fst_comp_toBase_eq_snd_comp_toBase :
    pullback.fst f.hom.hom g.hom.hom ≫ M.toBase =
      pullback.snd f.hom.hom g.hom.hom ≫ N.toBase :=
  commonToBase_eq_snd f g

/-- **The generic fibre of the fibre product of two modifications.**  The first projection of the
fibre product of two modifications to a common target is an isomorphism on generic fibres: the
generic fibre of a fibre product is the fibre product of the generic fibres (pasting the two
pullback squares), and the generic fibre of `g` is an isomorphism because `g` is a modification. -/
theorem isIso_genericFiberMap_pullbackFst :
    IsIso (genericFiberMap (K := K) (pullback.fst f.hom.hom g.hom.hom) M.toBase) := by
  have H1 := (isPullback_genericFiberMap (K := K)
    (pullback.fst f.hom.hom g.hom.hom) M.toBase).flip
  have HB := H1.paste_vert (IsPullback.of_hasPullback f.hom.hom g.hom.hom)
  rw [← Model.baseChangeHom_comp_fst f.hom.hom f.hom.over_base] at HB
  have Hsq := IsPullback.of_bot' HB (isPullback_baseChangeHom g.hom.hom g.hom.over_base)
  have := g.genericIsIso
  exact isIso_fst_of_isPullback Hsq

/-- The closure model of the fibre product of two modifications of models: the scheme-theoretic
closure of the generic fibre inside `ModelModification.commonTotal f g`. -/
abbrev commonClosure : Scheme.{u} :=
  closureModel (K := K) (pullback.fst f.hom.hom g.hom.hom ≫ M.toBase)

/-- The projection of the closure model of the fibre product onto the total space of `M`. -/
abbrev closureToFirst : commonClosure f g ⟶ M.total :=
  closureModelι (K := K) (pullback.fst f.hom.hom g.hom.hom ≫ M.toBase) ≫
    pullback.fst f.hom.hom g.hom.hom

/-- The projection of the closure model of the fibre product onto the total space of `N`. -/
abbrev closureToSecond : commonClosure f g ⟶ N.total :=
  closureModelι (K := K) (pullback.fst f.hom.hom g.hom.hom ≫ M.toBase) ≫
    pullback.snd f.hom.hom g.hom.hom

/-- The two projections of the closure model induce the same structure map to the base. -/
theorem closureToSecond_comp_toBase :
    closureToSecond f g ≫ N.toBase = closureToFirst f g ≫ M.toBase := by
  rw [Category.assoc, Category.assoc, ← fst_comp_toBase_eq_snd_comp_toBase]

/-- The closure model of the fibre product is flat over the base DVR. -/
theorem flat_closureToFirst_comp : Flat (closureToFirst f g ≫ M.toBase) := by
  have h := flat_closureModel (K := K) (pullback.fst f.hom.hom g.hom.hom ≫ M.toBase)
  rwa [← Category.assoc] at h

/-- The generic fibre of the closure model of the fibre product agrees with that of `M`: both the
closed immersion and the first projection are isomorphisms on generic fibres. -/
theorem isIso_genericFiberMap_closureToFirst :
    IsIso (genericFiberMap (K := K) (closureToFirst f g) M.toBase) :=
  isIso_genericFiberMap_comp _ _ _
    (isIso_genericFiberMap_closureModelι (K := K)
      (pullback.fst f.hom.hom g.hom.hom ≫ M.toBase)) (isIso_genericFiberMap_pullbackFst f g)

/-- The generic-fibre identification of the closure model of the fibre product, obtained from the
one of `M` through the first projection. -/
def commonGenericFiberIso :
    genericFiber R K (closureToFirst f g ≫ M.toBase) ≅ Over.mk toK :=
  (Over.isoMk (@asIso _ _ _ _ (genericFiberMap (K := K) (closureToFirst f g) M.toBase)
        (isIso_genericFiberMap_closureToFirst f g)) (genericFiberMap_snd _ _) :
      genericFiber R K (closureToFirst f g ≫ M.toBase) ≅ genericFiber R K M.toBase) ≪≫
    M.genericFiberIso

/- `commonModel` is `@[reducible]` so that `(commonModel f g).total` and `(commonModel f g).toBase`
unfold during unification: the statements below mention `Model.baseChangeHom (M := commonModel f g)`
and `Model.Hom`s out of `commonModel f g`, whose types only definitionally agree with the expected
pullbacks, which otherwise blocks `rw` and `simp`. -/
/-- **The common model**: the closure model of the fibre product of two modifications of models of
the same curve is again a model of that curve.  Flatness -- the property that fails for the naive
fibre product -- holds because the closure model is by construction torsion free over `R`, and the
generic-fibre identification comes from `M` through the first projection. -/
@[reducible]
def commonModel : Model R K C toK where
  total := commonClosure f g
  toBase := closureToFirst f g ≫ M.toBase
  flat := flat_closureToFirst_comp f g
  locallyOfFinitePresentation := inferInstance
  quasiCompact := inferInstance
  genericFiberIso := commonGenericFiberIso f g

/-- The base-change map on generic fibres attached to the projection onto `M` is the generic fibre
map of that projection. -/
theorem baseChangeHom_closureToFirst :
    Model.baseChangeHom (R := R) (K := K) (M := commonModel f g) (N := M)
        (closureToFirst f g) rfl =
      genericFiberMap (K := K) (closureToFirst f g) M.toBase := rfl

/-- The common model dominates `M`: the first projection is a morphism of models. -/
def commonModelHomFst : commonModel f g ⟶ M where
  hom := closureToFirst f g
  over_base := rfl
  genericFiber := rfl

/-- The common model dominates `M` as a modification of models. -/
def commonModificationFst : ModelModification (commonModel f g) M where
  hom := commonModelHomFst f g
  proper := by
    change _root_.AlgebraicGeometry.IsProper (closureToFirst f g)
    infer_instance
  genericIsIso := by
    change IsIso (Model.baseChangeHom (R := R) (K := K) (M := commonModel f g) (N := M)
      (closureToFirst f g) rfl)
    rw [baseChangeHom_closureToFirst]
    exact isIso_genericFiberMap_closureToFirst f g

/-- The two projections of the closure model agree after composing to `P.total`. -/
theorem closureToSecond_comp_hom :
    closureToSecond f g ≫ g.hom.hom = closureToFirst f g ≫ f.hom.hom := by
  rw [Category.assoc, Category.assoc, ← pullback.condition]

/-- The identity expressing that the two generic-fibre identifications of the closure model, one
through `M` and one through `N`, agree over `P`. -/
theorem baseChangeHom_closureToSecond_comp :
    Model.baseChangeHom (R := R) (K := K) (M := commonModel f g) (N := N)
          (closureToSecond f g) (closureToSecond_comp_toBase f g) ≫
        Model.baseChangeHom (R := R) (K := K) g.hom.hom g.hom.over_base =
      genericFiberMap (K := K) (closureToFirst f g) M.toBase ≫
        Model.baseChangeHom (R := R) (K := K) f.hom.hom f.hom.over_base := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Model.baseChangeHom_comp_fst,
      Model.baseChangeHom_comp_fst_assoc, genericFiberMap_fst_assoc]
    rw [pullback.condition]
  · simp only [Category.assoc, Model.baseChangeHom_comp_snd]
    rw [genericFiberMap_snd]

/-- The generic fibre of the closure model agrees with that of `N` as well. -/
theorem isIso_baseChangeHom_closureToSecond :
    IsIso (Model.baseChangeHom (R := R) (K := K) (M := commonModel f g) (N := N)
      (closureToSecond f g) (closureToSecond_comp_toBase f g)) := by
  have hf := f.genericIsIso
  have hg := g.genericIsIso
  have hF := isIso_genericFiberMap_closureToFirst f g
  have hcomp : IsIso (Model.baseChangeHom (R := R) (K := K) (M := commonModel f g) (N := N)
      (closureToSecond f g) (closureToSecond_comp_toBase f g) ≫
        Model.baseChangeHom (R := R) (K := K) g.hom.hom g.hom.over_base) := by
    rw [baseChangeHom_closureToSecond_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Model.baseChangeHom (R := R) (K := K) g.hom.hom
    g.hom.over_base)

/-- The common model dominates `N`: the second projection is a morphism of models. -/
def commonModelHomSnd : commonModel f g ⟶ N where
  hom := closureToSecond f g
  over_base := closureToSecond_comp_toBase f g
  genericFiber := by
    have hcomp := baseChangeHom_closureToSecond_comp f g
    have hf : Model.baseChangeHom (R := R) (K := K) f.hom.hom f.hom.over_base ≫
        P.genericFiberIso.hom.left = M.genericFiberIso.hom.left := f.hom.genericFiber
    have hg : Model.baseChangeHom (R := R) (K := K) g.hom.hom g.hom.over_base ≫
        P.genericFiberIso.hom.left = N.genericFiberIso.hom.left := g.hom.genericFiber
    have hM : (commonModel f g).genericFiberIso.hom.left =
        genericFiberMap (K := K) (closureToFirst f g) M.toBase ≫
          M.genericFiberIso.hom.left := rfl
    rw [hM, ← hf, ← hg, ← Category.assoc, hcomp, Category.assoc]

/-- The common model dominates `N` as a modification of models. -/
def commonModificationSnd : ModelModification (commonModel f g) N where
  hom := commonModelHomSnd f g
  proper := by
    change _root_.AlgebraicGeometry.IsProper (closureToSecond f g)
    infer_instance
  genericIsIso := isIso_baseChangeHom_closureToSecond f g

/-- The common model is proper over the base whenever `M` is. -/
instance isProper_commonModel [M.IsProper] : (commonModel f g).IsProper := by
  change _root_.AlgebraicGeometry.IsProper (closureToFirst f g ≫ M.toBase)
  have : _root_.AlgebraicGeometry.IsProper M.toBase := ‹M.IsProper›
  infer_instance

end ModelModification

end CommonModel

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
