/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ModelNormalization

/-!
# Normalization over the generic fibre

`Curves/StableReduction/ModelNormalization.lean` builds the normalization `Model.normalize` of a
model `M` of a curve `C` over a discrete valuation ring `R`, but leaves the identification of the
generic fibres as an explicit hypothesis
`hgen : IsIso (genericFiberMap (Normalization.toCurve M.total) M.toBase)`.
This file discharges that hypothesis when the generic fibre is normal.

## Normality of a scheme

Mathlib has no predicate "the scheme `X` is normal", so we use

* `IsNormalScheme X`: the sections `Γ(X, U)` over every nonempty affine open `U` are integrally
  closed (in their fraction ring).  This is invariant under isomorphisms
  (`IsNormalScheme.of_iso`) and, along an open immersion `j`, controls the sections of the target
  over the affine opens contained in the range of `j`
  (`IsNormalScheme.isIntegrallyClosed_of_le_opensRange`).

## Normalization is an isomorphism over the normal locus

* `Normalization.isIso_app_toCurve`: on a nonempty affine open `U` with `Γ(X, U)` integrally
  closed the normalization morphism induces an isomorphism on sections.  Indeed, by Mathlib's
  `Scheme.Hom.fromNormalization_app` the map on sections is (up to the isomorphism
  `Scheme.Hom.normalizationObjIso`) the inclusion of `Γ(X, U)` into its integral closure in the
  function field, and that inclusion is bijective exactly when `Γ(X, U)` is integrally closed.
* `Normalization.isIso_morphismRestrict_toCurve_of_normal`: consequently the normalization
  morphism restricted to an open `V` all of whose affine opens have integrally closed sections is
  an isomorphism, and `Normalization.isIso_toCurve_of_isNormalScheme`: the normalization of a
  normal integral scheme is an isomorphism.

## Normalization and the generic fibre

The generic fibre `Z_K = Z ×_{Spec R} Spec K` of `Z = M.total` sits inside `Z` as an open
subscheme (`Spec K → Spec R` is an open immersion for a discrete valuation ring), and
`genericFiberMap (Normalization.toCurve Z) M.toBase` is the base change of the normalization
morphism along that open immersion (`isPullback_genericFiberMap`).  Two consequences:

* `Model.isIso_genericFiberMap_iff_isIso_fromNormalization`: the generic-fibre map is an
  isomorphism if and only if the *relative* normalization of `Z_K` in the function-field point is
  an isomorphism.  This is normalization commuting with the (smooth, indeed open) base change
  `Z_K → Z`, i.e. Mathlib's `Scheme.Hom.normalizationPullback`, recorded here as
  `Model.genericFiberNormalizationIso`.
* `Model.isIso_genericFiberMap_toCurve_iff_isNormalScheme`: the generic-fibre map is an
  isomorphism **if and only if** the curve `C` is normal, and in particular
  `Model.isIso_genericFiberMap_toCurve_of_isNormalScheme`: normality of `C` discharges the
  hypothesis of `Model.normalize`.

What is *not* proved is that the relative normalization of `Z_K` appearing in
`Model.isIso_genericFiberMap_iff_isIso_fromNormalization` is the absolute normalization
`Curves.Normalization.scheme Z_K` of the generic fibre: that identification needs
`Spec (functionField Z) ×_Z Z_K ≅ Spec (functionField Z_K)`, i.e. that a nonempty open subscheme
of an integral scheme has the same function field, which is not available in Mathlib.  The
characterisation by normality above is proved directly instead, so nothing below depends on it.

## Assembling

* `Model.normalize'`, `Model.normalizeModification'`: the normalization of a model with normal
  generic fibre is again a model, and a proper modification of the original model; the only
  remaining hypothesis is the finiteness `[IsFinite (Normalization.toCurve M.total)]` of the
  normalization morphism.
* `Model.isFinite_toCurve_of_charZero`, `Model.normalize_charZero` and
  `Model.normalizeModification_charZero`: in
  characteristic zero (more precisely, when `Spec R` is locally of finite type over a field of
  characteristic zero) the finiteness hypothesis is automatic by
  `Curves.Normalization.isFinite_toCurve`, so a model of a normal curve always has a
  normalization, as a proper modification.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

/-! ### Bijectivity of the inclusion into an integral closure -/

namespace Normalization

/-- A ring is integrally closed exactly when it exhausts its integral closure in its fraction
field; this is the surjectivity half, packaged with the (always valid) injectivity. -/
theorem bijective_algebraMap_integralClosure (A F : Type u) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] [hic : IsIntegrallyClosed A] :
    Function.Bijective (algebraMap A (integralClosure A F)) := by
  refine ⟨algebraMap_integralClosure_injective A F, fun x ↦ ?_⟩
  have hx : (x : F) ∈ (⊥ : Subalgebra A F) := by
    rw [← IsIntegrallyClosed.integralClosure_eq_bot A F]
    exact x.2
  obtain ⟨y, hy⟩ := Algebra.mem_bot.mp hx
  exact ⟨y, Subtype.ext hy⟩

/-- The previous statement transported along an isomorphism of the ambient algebra: this is how it
will be applied, the ambient algebra being the sections of the function-field point rather than
the function field itself. -/
theorem bijective_algebraMap_integralClosure_of_algEquiv (A F L : Type u) [CommRing A]
    [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F] [hic : IsIntegrallyClosed A]
    [CommRing L] [Algebra A L] (e : F ≃ₐ[A] L) :
    Function.Bijective (algebraMap A (integralClosure A L)) := by
  have h := bijective_algebraMap_integralClosure A F
  have he : (algebraMap A (integralClosure A L)) =
      (integralClosureAlgEquiv e).toRingEquiv.toRingHom.comp
        (algebraMap A (integralClosure A F)) := by
    refine RingHom.ext fun a ↦ ?_
    exact ((integralClosureAlgEquiv e).commutes a).symm
  rw [he]
  exact (integralClosureAlgEquiv e).bijective.comp h

end Normalization

/-! ### Normal schemes -/

/-- A scheme is *normal* if its sections over every nonempty affine open form an integrally closed
ring.  Mathlib has no such predicate, and this is the form in which normality is used below. -/
def IsNormalScheme (X : Scheme.{u}) : Prop :=
  ∀ U : X.affineOpens, Nonempty U.1 → IsIntegrallyClosed Γ(X, U.1)

/-- Integral closedness of sections transfers along an open immersion, from an open of the source
to its image. -/
theorem isIntegrallyClosed_sections_image {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (W : Y.Opens) (h : IsIntegrallyClosed Γ(Y, W)) : IsIntegrallyClosed Γ(Z, j ''ᵁ W) :=
  IsIntegrallyClosed.of_equiv (h := h) (j.appIso W).symm.commRingCatIsoToRingEquiv

/-- Integral closedness of sections transfers along an open immersion, from the image of an open
of the source back to that open. -/
theorem isIntegrallyClosed_sections_of_image {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (W : Y.Opens) (h : IsIntegrallyClosed Γ(Z, j ''ᵁ W)) : IsIntegrallyClosed Γ(Y, W) :=
  IsIntegrallyClosed.of_equiv (h := h) (j.appIso W).commRingCatIsoToRingEquiv

/-- If `Y` is normal and `j : Y ⟶ Z` is an open immersion, then the sections of `Z` over any
nonempty affine open contained in the range of `j` are integrally closed. -/
theorem IsNormalScheme.isIntegrallyClosed_of_le_opensRange {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    [IsOpenImmersion j] (hY : IsNormalScheme Y) (U : Z.affineOpens)
    (hU : U.1 ≤ j.opensRange) (hne : Nonempty U.1) : IsIntegrallyClosed Γ(Z, U.1) := by
  obtain ⟨x⟩ := hne
  obtain ⟨y, hy⟩ := hU x.2
  have hpre : IsAffineOpen (j ⁻¹ᵁ U.1) := U.2.preimage_of_isOpenImmersion j hU
  have hmem : j.base y ∈ U.1 := by rw [hy]; exact x.2
  have himg : j ''ᵁ (j ⁻¹ᵁ U.1) = U.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]
  have h1 := isIntegrallyClosed_sections_image j (j ⁻¹ᵁ U.1) (hY ⟨_, hpre⟩ ⟨⟨y, hmem⟩⟩)
  rwa [himg] at h1

/-- Normality of a scheme is invariant under isomorphisms. -/
theorem IsNormalScheme.of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (h : IsNormalScheme Y) :
    IsNormalScheme X := by
  intro U hne
  have hi : IsAffineOpen (e.hom ''ᵁ U.1) := U.2.image_of_isOpenImmersion e.hom
  have hne' : Nonempty (e.hom ''ᵁ U.1) := by
    obtain ⟨x⟩ := hne
    exact ⟨⟨e.hom.base x.1, ⟨x.1, x.2, rfl⟩⟩⟩
  exact isIntegrallyClosed_sections_of_image e.hom U.1 (h ⟨_, hi⟩ hne')

/-- Converse of `IsNormalScheme.isIntegrallyClosed_of_le_opensRange`: if the sections of `Z` over
every nonempty affine open contained in the range of an open immersion `j : Y ⟶ Z` are integrally
closed, then `Y` is normal. -/
theorem isNormalScheme_of_le_opensRange {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (h : ∀ U : Z.affineOpens, U.1 ≤ j.opensRange → Nonempty U.1 →
      IsIntegrallyClosed Γ(Z, U.1)) : IsNormalScheme Y := by
  intro W hne
  have hi : IsAffineOpen (j ''ᵁ W.1) := W.2.image_of_isOpenImmersion j
  have hle : j ''ᵁ W.1 ≤ j.opensRange := by
    intro z hz
    obtain ⟨w, -, rfl⟩ := hz
    exact ⟨w, rfl⟩
  have hne' : Nonempty (j ''ᵁ W.1) := by
    obtain ⟨w⟩ := hne
    exact ⟨⟨j.base w.1, ⟨w.1, w.2, rfl⟩⟩⟩
  exact isIntegrallyClosed_sections_of_image j W.1 (h ⟨_, hi⟩ hle hne')

/-! ### Normalization over the normal locus -/

namespace Normalization

variable (X : Scheme.{u}) [IsIntegral X]

/-- **The normalization is an isomorphism on sections over an integrally closed affine open.**
By `Scheme.Hom.fromNormalization_app` the map on sections is, up to the isomorphism
`Scheme.Hom.normalizationObjIso`, the inclusion of `Γ(X, U)` into its integral closure inside the
sections of the function-field point, and that inclusion is bijective by
`bijective_algebraMap_integralClosure_of_algEquiv`. -/
theorem isIso_app_toCurve (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [hic : IsIntegrallyClosed Γ(X, U)] : IsIso ((toCurve X).app U) := by
  let _ := ((genericPointMap X).app U).hom.toAlgebra
  have _ : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have hbij : Function.Bijective (algebraMap Γ(X, U)
      (integralClosure Γ(X, U) Γ(Spec X.functionField, genericPointMap X ⁻¹ᵁ U))) :=
    bijective_algebraMap_integralClosure_of_algEquiv Γ(X, U) X.functionField _
      (functionFieldAlgEquiv X U)
  have hiso : IsIso (CommRingCat.ofHom (algebraMap Γ(X, U)
      (integralClosure Γ(X, U) Γ(Spec X.functionField, genericPointMap X ⁻¹ᵁ U)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  change IsIso ((genericPointMap X).fromNormalization.app U)
  rw [Scheme.Hom.fromNormalization_app _ hU]
  infer_instance

/-- The normalization morphism restricted to a nonempty affine open with integrally closed
sections is an isomorphism. -/
theorem isIso_morphismRestrict_toCurve (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [hic : IsIntegrallyClosed Γ(X, U)] : IsIso (toCurve X ∣_ U) :=
  (isIso_morphismRestrict_iff_isIso_app _ hU).mpr (isIso_app_toCurve X U hU)

/-- **The normalization is an isomorphism over a normal open.**  If every nonempty affine open of
`X` contained in `V` has integrally closed sections, the normalization morphism restricted to `V`
is an isomorphism; being an isomorphism is Zariski-local at the target, and the affine opens
contained in `V` form a basis of `V`. -/
theorem isIso_morphismRestrict_toCurve_of_normal (V : X.Opens)
    (h : ∀ U : X.affineOpens, U.1 ≤ V → Nonempty U.1 → IsIntegrallyClosed Γ(X, U.1)) :
    IsIso (toCurve X ∣_ V) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms _)
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show (V.ι.base x : X) ∈ (V : Set X) from x.2) V.2
  refine ⟨V.ι ⁻¹ᵁ U, hxU, ?_⟩
  refine (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms _)
    (morphismRestrictRestrict (toCurve X) V (V.ι ⁻¹ᵁ U))).mpr ?_
  have hUV' : U ≤ V := hUV
  have himg : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUV']
  rw [himg]
  have hne : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : IsIntegrallyClosed Γ(X, U) := h ⟨U, hU⟩ hUV' hne
  exact isIso_morphismRestrict_toCurve X U hU

/-- **The normalization of a normal integral scheme is an isomorphism.** -/
theorem isIso_toCurve_of_isNormalScheme (h : IsNormalScheme X) : IsIso (toCurve X) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms _)
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  refine ⟨U, hxU, ?_⟩
  have hne : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : IsIntegrallyClosed Γ(X, U) := h ⟨U, hU⟩ hne
  exact isIso_morphismRestrict_toCurve X U hU

/-- **Converse of `isIso_app_toCurve`.**  If the normalization morphism is an isomorphism on the
sections over a nonempty affine open, then those sections are integrally closed: the sections of
the normalization always are, by `Normalization.isIntegrallyClosed_sections`. -/
theorem isIntegrallyClosed_of_isIso_app_toCurve (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIso ((toCurve X).app U)] : IsIntegrallyClosed Γ(X, U) :=
  IsIntegrallyClosed.of_equiv (h := isIntegrallyClosed_sections X U hU)
    (asIso ((toCurve X).app U)).symm.commRingCatIsoToRingEquiv

/-- **Converse of `isIso_morphismRestrict_toCurve_of_normal`.**  If the normalization morphism
restricted to an open `V` is an isomorphism, the sections over every nonempty affine open
contained in `V` are integrally closed. -/
theorem isIntegrallyClosed_of_isIso_morphismRestrict_toCurve (V : X.Opens)
    (h : IsIso (toCurve X ∣_ V)) (U : X.affineOpens) (hUV : U.1 ≤ V) (hne : Nonempty U.1) :
    IsIntegrallyClosed Γ(X, U.1) := by
  have himg : V.ι ''ᵁ (V.ι ⁻¹ᵁ U.1) = U.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUV]
  have h1 : IsIso (toCurve X ∣_ V ∣_ (V.ι ⁻¹ᵁ U.1)) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms _) h _
  have h2 : IsIso (toCurve X ∣_ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U.1))) :=
    (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms _)
      (morphismRestrictRestrict (toCurve X) V (V.ι ⁻¹ᵁ U.1))).mp h1
  rw [himg] at h2
  have h3 : IsIso ((toCurve X).app U.1) := (isIso_morphismRestrict_iff_isIso_app _ U.2).mp h2
  have hne' : Nonempty U.1 := hne
  exact isIntegrallyClosed_of_isIso_app_toCurve X U.1 U.2

end Normalization

/-! ### Isomorphy of a base change along an open immersion -/

/-- A base change of `f` along an open immersion `iY` is an isomorphism if and only if the
restriction of `f` to the range of `iY` is one: both are, up to isomorphism of arrows, the
pullback of `f` along `iY`. -/
theorem isIso_iff_isIso_morphismRestrict_of_isPullback {N Z Y N' : Scheme.{u}} {f : N ⟶ Z}
    {iY : Y ⟶ Z} [IsOpenImmersion iY] {iX : N' ⟶ N} {f' : N' ⟶ Y}
    (h : IsPullback iX f' f iY) : IsIso f' ↔ IsIso (f ∣_ iY.opensRange) := by
  set e := IsPullback.isoIsPullback _ _ h (IsPullback.of_hasPullback f iY) with he
  have hsnd : e.hom ≫ pullback.snd f iY = f' := by simp [he]
  have h2 : IsIso f' ↔ IsIso (pullback.snd f iY) := by
    refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
    · rw [show pullback.snd f iY = e.inv ≫ f' by rw [← hsnd, Iso.inv_hom_id_assoc]]
      infer_instance
    · rw [← hsnd]
      infer_instance
  refine h2.trans ?_
  have h3 : IsIso (pullback.snd f iY) ↔ IsIso (f ∣_ iY.opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms _)
      (morphismRestrictOpensRange f iY)).symm
  exact h3

namespace StableReduction

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

namespace Model

variable (M : Model R K C toK) [IsIntegral M.total]

/-- **Normalization commutes with passing to the generic fibre.**  The generic fibre of the
normalization of `M.total` is the relative normalization of the generic fibre `Z_K` in the
function-field point of `M.total` restricted to `Z_K`.  This is Mathlib's
`Scheme.Hom.normalizationPullback` for the base change along the open (hence smooth) immersion
`Z_K ⟶ M.total`. -/
def genericFiberNormalizationIso :
    (pullback.snd (Normalization.genericPointMap M.total)
        (pullback.fst M.toBase (genericPointMap R K))).normalization ≅
      pullback (Normalization.toCurve M.total) (pullback.fst M.toBase (genericPointMap R K)) :=
  asIso ((Normalization.genericPointMap M.total).normalizationPullback
    (pullback.fst M.toBase (genericPointMap R K)))

@[reassoc (attr := simp)]
theorem genericFiberNormalizationIso_hom_snd :
    (genericFiberNormalizationIso M).hom ≫
        pullback.snd (Normalization.toCurve M.total)
          (pullback.fst M.toBase (genericPointMap R K)) =
      (pullback.snd (Normalization.genericPointMap M.total)
        (pullback.fst M.toBase (genericPointMap R K))).fromNormalization :=
  Scheme.Hom.normalizationPullback_snd _ _

/-- **The generic-fibre hypothesis of `Model.normalize` is the normality of the generic fibre.**
The map induced by the normalization morphism on generic fibres is an isomorphism if and only if
the relative normalization of the generic fibre in the function-field point is an isomorphism. -/
theorem isIso_genericFiberMap_iff_isIso_fromNormalization :
    IsIso (genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase) ↔
      IsIso (pullback.snd (Normalization.genericPointMap M.total)
        (pullback.fst M.toBase (genericPointMap R K))).fromNormalization := by
  rw [isIso_iff_isIso_morphismRestrict_of_isPullback
    (isPullback_genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase)]
  have h2 : IsIso (pullback.snd (Normalization.toCurve M.total)
        (pullback.fst M.toBase (genericPointMap R K))) ↔
      IsIso (Normalization.toCurve M.total ∣_
        (pullback.fst M.toBase (genericPointMap R K)).opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms _)
      (morphismRestrictOpensRange (Normalization.toCurve M.total) _)).symm
  refine h2.symm.trans ?_
  rw [← genericFiberNormalizationIso_hom_snd M]
  exact (MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme)
    (genericFiberNormalizationIso M).hom _).symm

/-- **The generic-fibre map of the normalization is an isomorphism over the normal locus.**  If
every nonempty affine open of `M.total` contained in the generic fibre has integrally closed
sections, the normalization morphism induces an isomorphism on generic fibres. -/
theorem isIso_genericFiberMap_toCurve
    (h : ∀ U : M.total.affineOpens,
      U.1 ≤ (pullback.fst M.toBase (genericPointMap R K)).opensRange → Nonempty U.1 →
        IsIntegrallyClosed Γ(M.total, U.1)) :
    IsIso (genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase) :=
  (isIso_iff_isIso_morphismRestrict_of_isPullback
      (isPullback_genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase)).mpr
    (Normalization.isIso_morphismRestrict_toCurve_of_normal M.total _ h)

/-- **Normality of the curve is exactly the generic-fibre hypothesis of `Model.normalize`.**  The
normalization morphism of `M.total` induces an isomorphism on generic fibres if and only if the
curve `C` modelled by `M` is normal.  The generic fibre of `M` is an open subscheme of `M.total`
isomorphic to `C`, and over an open subscheme being the normalization is measured by integral
closedness of the sections. -/
theorem isIso_genericFiberMap_toCurve_iff_isNormalScheme :
    IsIso (genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase) ↔
      IsNormalScheme C := by
  have e : (pullback M.toBase (genericPointMap R K) : Scheme.{u}) ≅ C :=
    (Over.forget (Spec (CommRingCat.of K))).mapIso M.genericFiberIso
  rw [isIso_iff_isIso_morphismRestrict_of_isPullback
    (isPullback_genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase)]
  refine ⟨fun h ↦ IsNormalScheme.of_iso e.symm ?_, fun hC ↦ ?_⟩
  · exact isNormalScheme_of_le_opensRange (pullback.fst M.toBase (genericPointMap R K))
      fun U hU hne ↦ Normalization.isIntegrallyClosed_of_isIso_morphismRestrict_toCurve
        M.total _ h U hU hne
  · exact Normalization.isIso_morphismRestrict_toCurve_of_normal M.total _
      fun U hU hne ↦ (IsNormalScheme.of_iso e hC).isIntegrallyClosed_of_le_opensRange _ U hU hne

/-- **A normal curve has a normalization-invariant generic fibre.**  If the curve `C` modelled by
`M` is normal, the normalization morphism of `M.total` induces an isomorphism on generic
fibres. -/
theorem isIso_genericFiberMap_toCurve_of_isNormalScheme (hC : IsNormalScheme C) :
    IsIso (genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase) :=
  (isIso_genericFiberMap_toCurve_iff_isNormalScheme M).mpr hC

variable [IsFinite (Normalization.toCurve M.total)]

/-- **The normalization of a model with normal generic fibre.**  Compared with `Model.normalize`,
the generic-fibre hypothesis is replaced by the normality of the curve `C`. -/
def normalize' (hC : IsNormalScheme C) : Model R K C toK :=
  M.normalize (isIso_genericFiberMap_toCurve_of_isNormalScheme M hC)

/-- **Normalization is a proper modification.**  Compared with `Model.normalizeModification`, the
generic-fibre hypothesis is replaced by the normality of the curve `C`. -/
def normalizeModification' (hC : IsNormalScheme C) :
    ModelModification (M.normalize' hC) M :=
  M.normalizeModification (isIso_genericFiberMap_toCurve_of_isNormalScheme M hC)

end Model

/-! ### The characteristic-zero case -/

namespace Model

variable (M : Model R K C toK) [IsIntegral M.total]

/-- **Finiteness of the normalization of a model in characteristic zero.**  If the base `Spec R`
is locally of finite type over a field `k` of characteristic zero, then so is `M.total` (a model
is locally of finite presentation over `R`), and `Curves.Normalization.isFinite_toCurve` applies:
the normalization morphism of `M.total` is finite. -/
theorem isFinite_toCurve_of_charZero (k : Type u) [Field k] [CharZero k]
    (g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] :
    IsFinite (Normalization.toCurve M.total) :=
  Normalization.isFinite_toCurve M.total k (M.toBase ≫ g)

/-- **The normalization of a model of a normal curve, in characteristic zero.**  If `Spec R` is
locally of finite type over a field of characteristic zero and the curve `C` is normal, then the
normalization of `M.total` is again a model of `C`: no hypothesis on the normalization morphism is
needed, its finiteness being automatic. -/
def normalize_charZero (k : Type u) [Field k] [CharZero k]
    (g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (hC : IsNormalScheme C) : Model R K C toK :=
  have := isFinite_toCurve_of_charZero M k g
  M.normalize' hC

/-- **Normalization is a proper modification, in characteristic zero.**  Under the hypotheses of
`Model.normalize_charZero` the normalization morphism is a proper modification of models. -/
def normalizeModification_charZero (k : Type u) [Field k] [CharZero k]
    (g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (hC : IsNormalScheme C) :
    ModelModification (M.normalize_charZero k g hC) M :=
  have := isFinite_toCurve_of_charZero M k g
  M.normalizeModification' hC

/-- The total space of the characteristic-zero normalization is the normalization of `M.total`. -/
theorem normalize_charZero_total (k : Type u) [Field k] [CharZero k]
    (g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (hC : IsNormalScheme C) :
    (M.normalize_charZero k g hC).total = Normalization.scheme M.total := rfl

end Model

end StableReduction

end

end GromovWitten.AlgebraicGeometry.Curves
