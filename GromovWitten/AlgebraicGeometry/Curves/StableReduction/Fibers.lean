/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.DVRExtension

/-!
# Generic and special fibres over a discrete valuation ring

The generic fibre is always base change along `Spec K ⟶ Spec R`, where `K` is the specified
fraction field.  The special fibre is base change along the residue field of the maximal ideal.
This file also exposes the immersions into the total space and comparison data with
`Scheme.Hom.fiber`.
-/

open CategoryTheory Limits
open AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- A fraction field of a DVR is obtained by inverting any uniformizer. -/
lemma isLocalizationAway_of_isFractionRing_dvr {π : R} (hπ : Irreducible π) :
    IsLocalization.Away π K := by
  change IsLocalization (Submonoid.powers π) K
  refine (IsLocalization.iff_of_le_of_exists_dvd (S := K)
    (M := Submonoid.powers π) (nonZeroDivisors R) ?_ ?_).mpr inferInstance
  · rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hπ.ne_zero)
  · intro x hx
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    obtain ⟨n, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
    refine ⟨π ^ n, ⟨n, rfl⟩, (a⁻¹ : Rˣ), ?_⟩
    rw [ha, mul_assoc, mul_comm (π ^ n) ((a⁻¹ : Rˣ) : R), ← mul_assoc]
    simp

/-- The canonical map from the generic point into the spectrum of a DVR. -/
def genericPointMap : Spec (.of K) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

instance genericPointMap_isOpenImmersion : IsOpenImmersion (genericPointMap R K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let _ : IsLocalization.Away π K := isLocalizationAway_of_isFractionRing_dvr R K hπ
  exact IsOpenImmersion.of_isLocalization π

/-- The closed point of the spectrum of a DVR. -/
abbrev dvrSpecialPoint : Spec (.of R) := IsLocalRing.closedPoint R

/-- A residue field attached to the maximal ideal of a DVR. -/
abbrev specialResidueField : Type u := (IsLocalRing.maximalIdeal R).ResidueField

/-- The canonical map from the special point into the spectrum of a DVR. -/
def specialPointMap : Spec (.of (specialResidueField R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (specialResidueField R)))

instance specialPointMap_isClosedImmersion : IsClosedImmersion (specialPointMap R) :=
  IsClosedImmersion.spec_of_surjective _
    (Ideal.algebraMap_residueField_surjective (IsLocalRing.maximalIdeal R))

/-- The generic point of the spectrum of a DVR. -/
abbrev dvrGenericPoint : Spec (.of R) := (⊥ : PrimeSpectrum R)

/-- The residue field at the generic point, identified with the specified fraction field. -/
noncomputable def genericResidueFieldIso :
    (Spec (.of R)).residueField (dvrGenericPoint R) ≅ .of K :=
  Scheme.Spec.residueFieldIso (.of R) (dvrGenericPoint R) ≪≫
    (IsLocalization.algEquiv (nonZeroDivisors R)
      ((⊥ : Ideal R).ResidueField) K).toRingEquiv.toCommRingCatIso

/-- The scheme induced by the generic residue-field identification. -/
noncomputable def genericResidueSpecIso :
    Spec (.of K) ≅ Spec ((Spec (.of R)).residueField (dvrGenericPoint R)) :=
  Scheme.Spec.mapIso (genericResidueFieldIso R K).op

/-- The intrinsic residue field at the closed point, identified with the conventional
quotient by the maximal ideal. -/
noncomputable def specialResidueFieldIso :
    (Spec (.of R)).residueField (dvrSpecialPoint R) ≅ .of (specialResidueField R) :=
  Scheme.Spec.residueFieldIso (.of R) (dvrSpecialPoint R)

/-- The scheme induced by the special residue-field identification. -/
noncomputable def specialResidueSpecIso :
    Spec (.of (specialResidueField R)) ≅
      Spec ((Spec (.of R)).residueField (dvrSpecialPoint R)) :=
  Scheme.Spec.mapIso (specialResidueFieldIso R).op

@[reassoc]
lemma genericResidueSpecIso_hom_fromSpecResidueField :
    (genericResidueSpecIso R K).hom ≫
        (Spec (.of R)).fromSpecResidueField (dvrGenericPoint R) =
      genericPointMap R K := by
  change Spec.map (genericResidueFieldIso R K).hom ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [genericResidueFieldIso, ← Spec.map_comp]
  rw [AlgebraicGeometry.Spec.map_inj]
  ext r
  simp only [PrimeSpectrum.asIdeal_bot, Iso.trans_hom, RingEquiv.toCommRingCatIso_hom,
    AlgEquiv.toRingEquiv_toRingHom, Category.assoc, Iso.inv_hom_id_assoc,
    CommRingCat.hom_comp, ConcreteCategory.hom_ofHom, RingHom.coe_comp, RingHom.coe_coe,
    Function.comp_apply, AlgEquiv.commutes]

@[reassoc]
lemma specialResidueSpecIso_hom_fromSpecResidueField :
    (specialResidueSpecIso R).hom ≫
        (Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R) =
      specialPointMap R := by
  change Spec.map (specialResidueFieldIso R).hom ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap R (specialResidueField R)))
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [specialResidueFieldIso, ← Spec.map_comp]
  rw [AlgebraicGeometry.Spec.map_inj]
  change CommRingCat.ofHom (algebraMap R (specialResidueField R)) ≫
    (specialResidueFieldIso R).inv ≫ (specialResidueFieldIso R).hom = _
  simp

/-- Base change of `X` to the specified fraction field. -/
abbrev genericFiber {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) : Over (Spec (.of K)) :=
  Over.mk (pullback.snd toBase (genericPointMap R K))

/-- The immersion of the generic fibre into the total space. -/
def genericFiberι {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (genericFiber R K toBase).left ⟶ X := pullback.fst _ _

instance genericFiberι_isOpenImmersion {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    IsOpenImmersion (genericFiberι R K toBase) := by
  dsimp only [genericFiberι, genericFiber]
  infer_instance

/-- Base change of `X` to the residue field at the closed point. -/
def specialFiber {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    Over (Spec (.of (specialResidueField R))) :=
  Over.mk (pullback.snd toBase (specialPointMap R))

/-- The immersion of the special fibre into the total space. -/
def specialFiberι {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (specialFiber R toBase).left ⟶ X := pullback.fst _ _

instance specialFiberι_isClosedImmersion {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    IsClosedImmersion (specialFiberι R toBase) := by
  dsimp only [specialFiberι, specialFiber]
  infer_instance

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc (attr := simp)]
lemma genericFiberι_toBase {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    genericFiberι R K toBase ≫ toBase =
      (genericFiber R K toBase).hom ≫ genericPointMap R K :=
  pullback.condition

@[reassoc (attr := simp)]
lemma specialFiberι_toBase {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    specialFiberι R toBase ≫ toBase =
      (specialFiber R toBase).hom ≫ specialPointMap R :=
  pullback.condition

/-- The chosen generic fibre is a pullback over the intrinsic generic residue field. -/
lemma genericFiber_isPullback {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    IsPullback (genericFiberι R K toBase)
      ((genericFiber R K toBase).hom ≫ (genericResidueSpecIso R K).hom)
      toBase ((Spec (.of R)).fromSpecResidueField (dvrGenericPoint R)) := by
  apply (IsPullback.of_hasPullback toBase (genericPointMap R K)).of_iso
    (Iso.refl _) (Iso.refl _) (genericResidueSpecIso R K) (Iso.refl _)
  · simp [genericFiberι]
  · change pullback.snd _ _ ≫ _ = 𝟙 _ ≫ pullback.snd _ _ ≫ _
    simp
  · simp
  · simpa using (genericResidueSpecIso_hom_fromSpecResidueField R K).symm

/-- The chosen special fibre is a pullback over the intrinsic closed-point residue field. -/
lemma specialFiber_isPullback {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    IsPullback (specialFiberι R toBase)
      ((specialFiber R toBase).hom ≫ (specialResidueSpecIso R).hom)
      toBase ((Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R)) := by
  apply (IsPullback.of_hasPullback toBase (specialPointMap R)).of_iso
    (Iso.refl _) (Iso.refl _) (specialResidueSpecIso R) (Iso.refl _)
  · simp [specialFiberι]
  · change pullback.snd _ _ ≫ _ = 𝟙 _ ≫ pullback.snd _ _ ≫ _
    simp
  · simp
  · simpa using (specialResidueSpecIso_hom_fromSpecResidueField R).symm

/-- Comparison between the chosen generic fibre and `Scheme.Hom.fiber` at the generic point. -/
noncomputable def genericFiberIsoFiber {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (genericFiber R K toBase).left ≅ toBase.fiber (dvrGenericPoint R) :=
  (genericFiber_isPullback R K toBase).isoIsPullback X
    (Spec ((Spec (.of R)).residueField (dvrGenericPoint R)))
    (IsPullback.of_hasPullback toBase
      ((Spec (.of R)).fromSpecResidueField (dvrGenericPoint R)))

/-- Comparison between the chosen special fibre and `Scheme.Hom.fiber` at the closed point. -/
noncomputable def specialFiberIsoFiber {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (specialFiber R toBase).left ≅ toBase.fiber (dvrSpecialPoint R) :=
  (specialFiber_isPullback R toBase).isoIsPullback X
    (Spec ((Spec (.of R)).residueField (dvrSpecialPoint R)))
    (IsPullback.of_hasPullback toBase
      ((Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R)))

@[reassoc (attr := simp)]
lemma genericFiberIsoFiber_hom_fiberι {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (genericFiberIsoFiber R K toBase).hom ≫ toBase.fiberι (dvrGenericPoint R) =
      genericFiberι R K toBase :=
  (genericFiber_isPullback R K toBase).isoIsPullback_hom_fst X
    (Spec ((Spec (.of R)).residueField (dvrGenericPoint R)))
    (IsPullback.of_hasPullback toBase
      ((Spec (.of R)).fromSpecResidueField (dvrGenericPoint R)))

@[reassoc (attr := simp)]
lemma genericFiberIsoFiber_hom_fiberToSpecResidueField
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (genericFiberIsoFiber R K toBase).hom ≫
        toBase.fiberToSpecResidueField (dvrGenericPoint R) =
      (genericFiber R K toBase).hom ≫ (genericResidueSpecIso R K).hom :=
  (genericFiber_isPullback R K toBase).isoIsPullback_hom_snd X
    (Spec ((Spec (.of R)).residueField (dvrGenericPoint R)))
    (IsPullback.of_hasPullback toBase
      ((Spec (.of R)).fromSpecResidueField (dvrGenericPoint R)))

@[reassoc (attr := simp)]
lemma specialFiberIsoFiber_hom_fiberι {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (specialFiberIsoFiber R toBase).hom ≫ toBase.fiberι (dvrSpecialPoint R) =
      specialFiberι R toBase :=
  (specialFiber_isPullback R toBase).isoIsPullback_hom_fst X
    (Spec ((Spec (.of R)).residueField (dvrSpecialPoint R)))
    (IsPullback.of_hasPullback toBase
      ((Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R)))

@[reassoc (attr := simp)]
lemma specialFiberIsoFiber_hom_fiberToSpecResidueField
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (specialFiberIsoFiber R toBase).hom ≫
        toBase.fiberToSpecResidueField (dvrSpecialPoint R) =
      (specialFiber R toBase).hom ≫ (specialResidueSpecIso R).hom :=
  (specialFiber_isPullback R toBase).isoIsPullback_hom_snd X
    (Spec ((Spec (.of R)).residueField (dvrSpecialPoint R)))
    (IsPullback.of_hasPullback toBase
      ((Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R)))

/-- Generic fibre as functorial base change along the generic point. -/
abbrev genericFiberFunctor :
    Over (Spec (.of R)) ⥤ Over (Spec (.of K)) :=
  Over.pullback (genericPointMap R K)

/-- Special fibre as functorial base change along the closed point. -/
abbrev specialFiberFunctor :
    Over (Spec (.of R)) ⥤ Over (Spec (.of (specialResidueField R))) :=
  Over.pullback (specialPointMap R)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[simp]
lemma genericFiberFunctor_obj (X : Over (Spec (.of R))) :
    (genericFiberFunctor R K).obj X = genericFiber R K X.hom := rfl

@[simp]
lemma specialFiberFunctor_obj (X : Over (Spec (.of R))) :
    (specialFiberFunctor R).obj X = specialFiber R X.hom := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc (attr := simp)]
lemma genericFiberFunctor_map_fiberι
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    ((genericFiberFunctor R K).map f).left ≫ genericFiberι R K Y.hom =
      genericFiberι R K X.hom ≫ f.left := by
  dsimp [genericFiberFunctor, genericFiberι]
  apply pullback.lift_fst

@[reassoc (attr := simp)]
lemma specialFiberFunctor_map_fiberι
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    ((specialFiberFunctor R).map f).left ≫ specialFiberι R Y.hom =
      specialFiberι R X.hom ≫ f.left := by
  dsimp [specialFiberFunctor, specialFiberι]
  apply pullback.lift_fst

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc (attr := simp)]
lemma genericFiberFunctor_map_hom
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    ((genericFiberFunctor R K).map f).left ≫
        ((genericFiberFunctor R K).obj Y).hom =
      ((genericFiberFunctor R K).obj X).hom :=
  Over.w _

@[reassoc (attr := simp)]
lemma specialFiberFunctor_map_hom
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    ((specialFiberFunctor R).map f).left ≫
        ((specialFiberFunctor R).obj Y).hom =
      ((specialFiberFunctor R).obj X).hom :=
  Over.w _

/-- Intrinsic fibres as functorial base change to the generic residue field. -/
abbrev intrinsicGenericFiberFunctor :
    Over (Spec (.of R)) ⥤
      Over (Spec ((Spec (.of R)).residueField (dvrGenericPoint R))) :=
  Over.pullback ((Spec (.of R)).fromSpecResidueField (dvrGenericPoint R))

/-- Intrinsic fibres as functorial base change to the closed-point residue field. -/
abbrev intrinsicSpecialFiberFunctor :
    Over (Spec (.of R)) ⥤
      Over (Spec ((Spec (.of R)).residueField (dvrSpecialPoint R))) :=
  Over.pullback ((Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R))

omit [IsDiscreteValuationRing R] in
@[reassoc (attr := simp)]
lemma intrinsicGenericFiberFunctor_map_fiberι
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    ((intrinsicGenericFiberFunctor R).map f).left ≫
        Y.hom.fiberι (dvrGenericPoint R) =
      X.hom.fiberι (dvrGenericPoint R) ≫ f.left := by
  dsimp [intrinsicGenericFiberFunctor, Scheme.Hom.fiberι]
  apply pullback.lift_fst

@[reassoc (attr := simp)]
lemma intrinsicSpecialFiberFunctor_map_fiberι
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    ((intrinsicSpecialFiberFunctor R).map f).left ≫
        Y.hom.fiberι (dvrSpecialPoint R) =
      X.hom.fiberι (dvrSpecialPoint R) ≫ f.left := by
  dsimp [intrinsicSpecialFiberFunctor, Scheme.Hom.fiberι]
  apply pullback.lift_fst

/-- The chosen generic-fibre functor, transported to the intrinsic generic residue field. -/
abbrev genericFiberToIntrinsicFunctor :
    Over (Spec (.of R)) ⥤
      Over (Spec ((Spec (.of R)).residueField (dvrGenericPoint R))) :=
  genericFiberFunctor R K ⋙ Over.map (genericResidueSpecIso R K).hom

/-- The chosen special-fibre functor, transported to the intrinsic closed-point residue field. -/
abbrev specialFiberToIntrinsicFunctor :
    Over (Spec (.of R)) ⥤
      Over (Spec ((Spec (.of R)).residueField (dvrSpecialPoint R))) :=
  specialFiberFunctor R ⋙ Over.map (specialResidueSpecIso R).hom

/-- Objectwise comparison between the chosen and intrinsic generic-fibre functors. -/
noncomputable def genericFiberIntrinsicComparisonIso
    (X : Over (Spec (.of R))) :
    (genericFiberToIntrinsicFunctor R K).obj X ≅
      (intrinsicGenericFiberFunctor R).obj X :=
  Over.isoMk (genericFiberIsoFiber R K X.hom)
    (genericFiberIsoFiber_hom_fiberToSpecResidueField R K X.hom)

/-- Objectwise comparison between the chosen and intrinsic special-fibre functors. -/
noncomputable def specialFiberIntrinsicComparisonIso
    (X : Over (Spec (.of R))) :
    (specialFiberToIntrinsicFunctor R).obj X ≅
      (intrinsicSpecialFiberFunctor R).obj X :=
  Over.isoMk (specialFiberIsoFiber R X.hom)
    (specialFiberIsoFiber_hom_fiberToSpecResidueField R X.hom)

@[reassoc (attr := simp)]
lemma genericFiberIntrinsicComparisonIso_hom_fiberι
    (X : Over (Spec (.of R))) :
    (genericFiberIntrinsicComparisonIso R K X).hom.left ≫
        X.hom.fiberι (dvrGenericPoint R) = genericFiberι R K X.hom := by
  change (genericFiberIsoFiber R K X.hom).hom ≫
    X.hom.fiberι (dvrGenericPoint R) = genericFiberι R K X.hom
  exact genericFiberIsoFiber_hom_fiberι R K X.hom

@[reassoc (attr := simp)]
lemma genericFiberIntrinsicComparisonIso_hom_hom
    (X : Over (Spec (.of R))) :
    (genericFiberIntrinsicComparisonIso R K X).hom.left ≫
        ((intrinsicGenericFiberFunctor R).obj X).hom =
      ((genericFiberToIntrinsicFunctor R K).obj X).hom := by
  change (genericFiberIsoFiber R K X.hom).hom ≫
      X.hom.fiberToSpecResidueField (dvrGenericPoint R) =
    (genericFiber R K X.hom).hom ≫ (genericResidueSpecIso R K).hom
  exact genericFiberIsoFiber_hom_fiberToSpecResidueField R K X.hom

@[reassoc (attr := simp)]
lemma specialFiberIntrinsicComparisonIso_hom_fiberι
    (X : Over (Spec (.of R))) :
    (specialFiberIntrinsicComparisonIso R X).hom.left ≫
        X.hom.fiberι (dvrSpecialPoint R) = specialFiberι R X.hom := by
  change (specialFiberIsoFiber R X.hom).hom ≫
    X.hom.fiberι (dvrSpecialPoint R) = specialFiberι R X.hom
  exact specialFiberIsoFiber_hom_fiberι R X.hom

@[reassoc (attr := simp)]
lemma specialFiberIntrinsicComparisonIso_hom_hom
    (X : Over (Spec (.of R))) :
    (specialFiberIntrinsicComparisonIso R X).hom.left ≫
        ((intrinsicSpecialFiberFunctor R).obj X).hom =
      ((specialFiberToIntrinsicFunctor R).obj X).hom := by
  change (specialFiberIsoFiber R X.hom).hom ≫
      X.hom.fiberToSpecResidueField (dvrSpecialPoint R) =
    (specialFiber R X.hom).hom ≫ (specialResidueSpecIso R).hom
  exact specialFiberIsoFiber_hom_fiberToSpecResidueField R X.hom

/-- The chosen generic fibre agrees naturally with the intrinsic generic fibre after transport
along the residue-field spectrum isomorphism. -/
noncomputable def genericFiberIntrinsicComparisonNatIso :
    genericFiberToIntrinsicFunctor R K ≅ intrinsicGenericFiberFunctor R :=
  NatIso.ofComponents (genericFiberIntrinsicComparisonIso R K) (fun {X Y} f ↦ by
    ext
    apply pullback.hom_ext
    · change ((genericFiberFunctor R K).map f).left ≫
          ((genericFiberIntrinsicComparisonIso R K Y).hom.left ≫
            Y.hom.fiberι (dvrGenericPoint R)) =
        (genericFiberIntrinsicComparisonIso R K X).hom.left ≫
          (((intrinsicGenericFiberFunctor R).map f).left ≫
            Y.hom.fiberι (dvrGenericPoint R))
      rw [genericFiberIntrinsicComparisonIso_hom_fiberι,
        intrinsicGenericFiberFunctor_map_fiberι,
        genericFiberFunctor_map_fiberι]
      exact (genericFiberIntrinsicComparisonIso_hom_fiberι_assoc R K X f.left).symm
    · change ((genericFiberFunctor R K).map f).left ≫
          ((genericFiberIntrinsicComparisonIso R K Y).hom.left ≫
            ((intrinsicGenericFiberFunctor R).obj Y).hom) =
        (genericFiberIntrinsicComparisonIso R K X).hom.left ≫
          (((intrinsicGenericFiberFunctor R).map f).left ≫
            ((intrinsicGenericFiberFunctor R).obj Y).hom)
      rw [genericFiberIntrinsicComparisonIso_hom_hom, Over.w,
        genericFiberIntrinsicComparisonIso_hom_hom]
      exact Over.w ((genericFiberToIntrinsicFunctor R K).map f))

/-- The chosen special fibre agrees naturally with the intrinsic special fibre after transport
along the residue-field spectrum isomorphism. -/
noncomputable def specialFiberIntrinsicComparisonNatIso :
    specialFiberToIntrinsicFunctor R ≅ intrinsicSpecialFiberFunctor R :=
  NatIso.ofComponents (specialFiberIntrinsicComparisonIso R) (fun {X Y} f ↦ by
    ext
    apply pullback.hom_ext
    · change ((specialFiberFunctor R).map f).left ≫
          ((specialFiberIntrinsicComparisonIso R Y).hom.left ≫
            Y.hom.fiberι (dvrSpecialPoint R)) =
        (specialFiberIntrinsicComparisonIso R X).hom.left ≫
          (((intrinsicSpecialFiberFunctor R).map f).left ≫
            Y.hom.fiberι (dvrSpecialPoint R))
      rw [specialFiberIntrinsicComparisonIso_hom_fiberι,
        intrinsicSpecialFiberFunctor_map_fiberι,
        specialFiberFunctor_map_fiberι]
      exact (specialFiberIntrinsicComparisonIso_hom_fiberι_assoc R X f.left).symm
    · change ((specialFiberFunctor R).map f).left ≫
          ((specialFiberIntrinsicComparisonIso R Y).hom.left ≫
            ((intrinsicSpecialFiberFunctor R).obj Y).hom) =
        (specialFiberIntrinsicComparisonIso R X).hom.left ≫
          (((intrinsicSpecialFiberFunctor R).map f).left ≫
            ((intrinsicSpecialFiberFunctor R).obj Y).hom)
      rw [specialFiberIntrinsicComparisonIso_hom_hom, Over.w,
        specialFiberIntrinsicComparisonIso_hom_hom]
      exact Over.w ((specialFiberToIntrinsicFunctor R).map f))

namespace FiniteDVRExtension

variable (E : FiniteDVRExtension R K)

/-- The map of spectra from the selected extension DVR to the original DVR. -/
def baseSpecMap : Spec (.of E.localRing) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R E.localRing))

/-- The selected extension-DVR map is affine. -/
instance baseSpecMap_isAffine : IsAffineHom (baseSpecMap R K E) := by
  infer_instance

/-- In particular, the selected extension-DVR map is quasi-compact. -/
instance baseSpecMap_quasiCompact : QuasiCompact (baseSpecMap R K E) := by
  infer_instance

/-- The selected extension-DVR map is flat. -/
instance baseSpecMap_flat : Flat (baseSpecMap R K E) := by
  rw [baseSpecMap, Flat.SpecMap_iff]
  change (algebraMap R E.localRing).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The selected extension-DVR map is surjective: algebraically, the local flat extension is
faithfully flat. -/
instance baseSpecMap_surjective : Surjective (baseSpecMap R K E) := by
  have hff : (algebraMap R E.localRing).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  exact (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R E.localRing))).mpr hff |>.2

/-- Pullback along the faithfully flat quasi-compact extension-DVR map is faithful. -/
instance baseSpecPullback_faithful : (Over.pullback (baseSpecMap R K E)).Faithful := by
  infer_instance

/-- Pullback along the faithfully flat quasi-compact extension-DVR map reflects
isomorphisms. -/
instance baseSpecPullback_reflectsIsomorphisms :
    (Over.pullback (baseSpecMap R K E)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    have htop : IsIso ((Over.pullback (baseSpecMap R K E)).map f).left := by
      change IsIso ((Over.forget (Spec (.of E.localRing))).map
        ((Over.pullback (baseSpecMap R K E)).map f))
      infer_instance
    have hsquare :
        IsPullback ((Over.pullback (baseSpecMap R K E)).map f).left
          (pullback.fst X.hom (baseSpecMap R K E))
          (pullback.fst Y.hom (baseSpecMap R K E)) f.left := by
      have hfst :
          ((Over.pullback (baseSpecMap R K E)).map f).left ≫
              pullback.fst Y.hom (baseSpecMap R K E) =
            pullback.fst X.hom (baseSpecMap R K E) ≫ f.left := by
        change pullback.lift
            (pullback.fst X.hom (baseSpecMap R K E) ≫ f.left)
            (pullback.snd X.hom (baseSpecMap R K E)) _ ≫
              pullback.fst Y.hom (baseSpecMap R K E) = _
        exact pullback.lift_fst _ _ _
      have hsnd :
          ((Over.pullback (baseSpecMap R K E)).map f).left ≫
              pullback.snd Y.hom (baseSpecMap R K E) =
            pullback.snd X.hom (baseSpecMap R K E) := by
        change pullback.lift
            (pullback.fst X.hom (baseSpecMap R K E) ≫ f.left)
            (pullback.snd X.hom (baseSpecMap R K E)) _ ≫
              pullback.snd Y.hom (baseSpecMap R K E) = _
        exact pullback.lift_snd _ _ _
      refine (IsPullback.of_bot ?_ hfst.symm
        (IsPullback.of_hasPullback Y.hom (baseSpecMap R K E))).flip
      simpa only [hsnd, f.w] using
        IsPullback.of_hasPullback X.hom (baseSpecMap R K E)
    have hf : MorphismProperty.isomorphisms Scheme f.left :=
      MorphismProperty.of_isPullback_of_descendsAlong
        (P := MorphismProperty.isomorphisms Scheme)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        hsquare ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ htop
    exact @isIso_of_reflects_iso _ _ _ _ _ _ f
      (Over.forget (Spec (.of R))) hf inferInstance

/-- The map of spectra associated to the finite extension of fraction fields. -/
def extensionSpecMap : Spec (.of E.extensionField) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K E.extensionField))

/-- The map associated to the finite extension field is finite. -/
instance extensionSpecMap_finite : IsFinite (extensionSpecMap R K E) := by
  rw [extensionSpecMap, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- A nonzero extension field is faithfully flat over its base field. -/
instance extensionField_faithfullyFlat :
    Module.FaithfullyFlat K E.extensionField := by
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Hence the map of extension-field spectra is flat. -/
instance extensionSpecMap_flat : Flat (extensionSpecMap R K E) := by
  rw [extensionSpecMap, Flat.SpecMap_iff]
  change (algebraMap K E.extensionField).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The map of spectra of a field extension is surjective. -/
instance extensionSpecMap_surjective : Surjective (extensionSpecMap R K E) := by
  have hff : (algebraMap K E.extensionField).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  exact (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap K E.extensionField))).mpr hff |>.2

/-- A compatible extension morphism induces the contravariant map of selected local spectra. -/
def Hom.localSpecMap {E F : FiniteDVRExtension R K} (f : E ⟶ F) :
    Spec (.of F.localRing) ⟶ Spec (.of E.localRing) :=
  Spec.map (CommRingCat.ofHom f.localRingHom.toRingHom)

/-- A compatible extension morphism induces the contravariant map of fraction-field spectra. -/
def Hom.fieldSpecMap {E F : FiniteDVRExtension R K} (f : E ⟶ F) :
    Spec (.of F.extensionField) ⟶ Spec (.of E.extensionField) :=
  Spec.map (CommRingCat.ofHom f.fieldHom.toRingHom)

@[simp]
lemma Hom.localSpecMap_id (E : FiniteDVRExtension R K) :
    (𝟙 E : E ⟶ E).localSpecMap = 𝟙 (Spec (.of E.localRing)) := by
  simp [Hom.localSpecMap, ← Spec.map_id]

@[simp]
lemma Hom.fieldSpecMap_id (E : FiniteDVRExtension R K) :
    (𝟙 E : E ⟶ E).fieldSpecMap = 𝟙 (Spec (.of E.extensionField)) := by
  simp [Hom.fieldSpecMap, ← Spec.map_id]

@[simp]
lemma Hom.localSpecMap_comp {E F G : FiniteDVRExtension R K}
    (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).localSpecMap = g.localSpecMap ≫ f.localSpecMap := by
  simp only [Hom.localSpecMap, ← Spec.map_comp]
  rw [Spec.map_inj]
  ext
  rfl

@[simp]
lemma Hom.fieldSpecMap_comp {E F G : FiniteDVRExtension R K}
    (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).fieldSpecMap = g.fieldSpecMap ≫ f.fieldSpecMap := by
  simp only [Hom.fieldSpecMap, ← Spec.map_comp]
  rw [Spec.map_inj]
  ext
  rfl

@[reassoc]
lemma Hom.localSpecMap_baseSpecMap {E F : FiniteDVRExtension R K} (f : E ⟶ F) :
    f.localSpecMap ≫ baseSpecMap R K E = baseSpecMap R K F := by
  simp only [Hom.localSpecMap, baseSpecMap, ← Spec.map_comp]
  rw [Spec.map_inj]
  ext x
  exact f.localRingHom.commutes x

@[reassoc]
lemma Hom.fieldSpecMap_extensionSpecMap {E F : FiniteDVRExtension R K} (f : E ⟶ F) :
    f.fieldSpecMap ≫ extensionSpecMap R K E = extensionSpecMap R K F := by
  simp only [Hom.fieldSpecMap, extensionSpecMap, ← Spec.map_comp]
  rw [Spec.map_inj]
  ext x
  exact f.fieldHom.commutes x

/-- The maps of local and fraction-field spectra induced by a compatible extension morphism
commute with their generic-point maps. -/
@[reassoc]
lemma Hom.genericPointMap_localSpecMap {E F : FiniteDVRExtension R K} (f : E ⟶ F) :
    genericPointMap F.localRing F.extensionField ≫ f.localSpecMap =
      f.fieldSpecMap ≫ genericPointMap E.localRing E.extensionField := by
  simp only [genericPointMap, Hom.localSpecMap, Hom.fieldSpecMap, ← Spec.map_comp]
  rw [Spec.map_inj]
  change CommRingCat.ofHom
      ((algebraMap F.localRing F.extensionField).comp f.localRingHom.toRingHom) =
    CommRingCat.ofHom
      (f.fieldHom.toRingHom.comp (algebraMap E.localRing E.extensionField))
  exact congrArg CommRingCat.ofHom f.fraction_commutes_ringHom

/-- The generic-point square associated to a finite DVR extension commutes. -/
@[reassoc]
lemma genericPointMap_baseSpecMap :
    genericPointMap E.localRing E.extensionField ≫ baseSpecMap R K E =
      extensionSpecMap R K E ≫ genericPointMap R K := by
  simp only [genericPointMap, baseSpecMap, extensionSpecMap, ← Spec.map_comp]
  rw [AlgebraicGeometry.Spec.map_inj]
  ext x
  change algebraMap E.localRing E.extensionField (algebraMap R E.localRing x) =
    algebraMap K E.extensionField (algebraMap R K x)
  rw [← IsScalarTower.algebraMap_apply R E.localRing E.extensionField,
    ← IsScalarTower.algebraMap_apply R K E.extensionField]

/-- Contravariant functor sending a finite DVR extension to its selected local spectrum over the
base DVR. -/
def localSpecFunctor :
    (FiniteDVRExtension R K)ᵒᵖ ⥤ Over (Spec (.of R)) where
  obj E := Over.mk (baseSpecMap R K E.unop)
  map f := Over.homMk f.unop.localSpecMap
    (f.unop.localSpecMap_baseSpecMap R K)
  map_id E := by
    ext
    exact Hom.localSpecMap_id R K E.unop
  map_comp f g := by
    ext
    exact Hom.localSpecMap_comp R K g.unop f.unop

/-- Contravariant functor sending a finite DVR extension to its extension-field spectrum over the
original fraction field. -/
def fieldSpecFunctor :
    (FiniteDVRExtension R K)ᵒᵖ ⥤ Over (Spec (.of K)) where
  obj E := Over.mk (extensionSpecMap R K E.unop)
  map f := Over.homMk f.unop.fieldSpecMap
    (f.unop.fieldSpecMap_extensionSpecMap R K)
  map_id E := by
    ext
    exact Hom.fieldSpecMap_id R K E.unop
  map_comp f g := by
    ext
    exact Hom.fieldSpecMap_comp R K g.unop f.unop

@[simp]
lemma localSpecFunctor_obj_left (E : FiniteDVRExtension R K) :
    ((localSpecFunctor R K).obj (Opposite.op E)).left = Spec (.of E.localRing) := rfl

@[simp]
lemma localSpecFunctor_obj_hom (E : FiniteDVRExtension R K) :
    ((localSpecFunctor R K).obj (Opposite.op E)).hom = baseSpecMap R K E := rfl

@[simp]
lemma localSpecFunctor_map_left {E F : FiniteDVRExtension R K} (f : E ⟶ F) :
    ((localSpecFunctor R K).map f.op).left = f.localSpecMap := rfl

@[simp]
lemma fieldSpecFunctor_obj_left (E : FiniteDVRExtension R K) :
    ((fieldSpecFunctor R K).obj (Opposite.op E)).left = Spec (.of E.extensionField) := rfl

@[simp]
lemma fieldSpecFunctor_obj_hom (E : FiniteDVRExtension R K) :
    ((fieldSpecFunctor R K).obj (Opposite.op E)).hom = extensionSpecMap R K E := rfl

@[simp]
lemma fieldSpecFunctor_map_left {E F : FiniteDVRExtension R K} (f : E ⟶ F) :
    ((fieldSpecFunctor R K).map f.op).left = f.fieldSpecMap := rfl

/-- The contravariant selected-local-spectrum functor remembers every compatible extension
morphism. -/
instance localSpecFunctor_faithful :
    (localSpecFunctor R K).Faithful where
  map_injective {X Y} f g h := by
    apply Quiver.Hom.unop_inj
    apply Hom.ext_localRingHom
    apply AlgHom.coe_ringHom_injective
    have hs := congrArg Over.Hom.left h
    change f.unop.localSpecMap = g.unop.localSpecMap at hs
    rw [Hom.localSpecMap, Hom.localSpecMap, AlgebraicGeometry.Spec.map_inj] at hs
    exact congrArg CommRingCat.Hom.hom hs

/-- The contravariant extension-field-spectrum functor remembers every compatible extension
morphism. -/
instance fieldSpecFunctor_faithful :
    (fieldSpecFunctor R K).Faithful where
  map_injective {X Y} f g h := by
    apply Quiver.Hom.unop_inj
    apply Hom.ext_fieldHom
    apply AlgHom.coe_ringHom_injective
    have hs := congrArg Over.Hom.left h
    change f.unop.fieldSpecMap = g.unop.fieldSpecMap at hs
    rw [Hom.fieldSpecMap, Hom.fieldSpecMap, AlgebraicGeometry.Spec.map_inj] at hs
    exact congrArg CommRingCat.Hom.hom hs

/-- The generic-point inclusions form a natural transformation from extension-field spectra,
viewed over the base DVR, to the selected local spectra. -/
def genericPointNatTrans :
    fieldSpecFunctor R K ⋙ Over.map (genericPointMap R K) ⟶ localSpecFunctor R K where
  app E := Over.homMk
    (genericPointMap E.unop.localRing E.unop.extensionField)
    (genericPointMap_baseSpecMap R K E.unop)
  naturality E F f := by
    ext
    exact (f.unop.genericPointMap_localSpecMap R K).symm

@[simp]
lemma genericPointNatTrans_app_left (E : FiniteDVRExtension R K) :
    ((genericPointNatTrans R K).app (Opposite.op E)).left =
      genericPointMap E.localRing E.extensionField := rfl

end FiniteDVRExtension

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
