/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ModelBlowup
import GromovWitten.AlgebraicGeometry.Curves.NormalizationFinite

/-!
# Normalization of a model

Given a model `M` of a curve over a discrete valuation ring `R`, this file constructs its
normalization `Model.normalize`, obtained by normalizing the total space `M.total` in its own
function field, and proves it is again a model: flatness follows from the fact that the affine
charts of the normalization are integrally closed subrings of the function field, hence domains,
and every domain receiving an injective ring map from the flat, hence torsion-free, chart rings of
`M.total` is itself torsion-free (equivalently flat, since `R` is a discrete valuation ring, hence
Bezout).  Finite presentation and quasi-compactness are derived from an explicit finiteness
hypothesis on the normalization morphism, and the generic-fibre identification is taken as an
explicit hypothesis (documented gap: proving that the generic point of `M.total` maps to the
generic point of `R`, which is what would let one derive this from properties of `M` alone, needs
a going-down argument that is not yet available in the repository).
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

open GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

/-! ### Two generic facts about flatness over a Bezout domain -/

namespace RingHom.Flat

variable {R A : Type u} [CommRing R] [IsDomain R] [IsBezout R] [CommRing A]

omit [IsDomain R] [IsBezout R] in
/-- The zero ring is flat over any ring. -/
theorem of_subsingleton [Subsingleton A] (φ : R →+* A) : φ.Flat := by
  let _ := φ.toAlgebra
  change Module.Flat R A
  let _ : Module.Free R A := Module.Free.of_subsingleton R A
  infer_instance

omit [IsBezout R] in
/-- Over a Bezout domain, a flat ring map into a domain is injective: a flat module has no
torsion, and a nonzero scalar killing an element of a domain forces that element (or the scalar's
image) to vanish. -/
theorem injective_of_isDomain [IsDomain A] {φ : R →+* A} (hφ : φ.Flat) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hane
  have hz : φ a ∈ nonZeroDivisors A :=
    ReesTorsion.mem_nonZeroDivisors_of_flat hφ (mem_nonZeroDivisors_iff_ne_zero.mpr hane)
  exact mem_nonZeroDivisors_iff_ne_zero.mp hz ha

/-- Over a Bezout domain, an injective ring map into a domain is flat: the torsion submodule of
the target, viewed as a module over the source, vanishes because a nonzerodivisor of the source
has nonzero (hence, in a domain, nonzerodivisor) image. -/
theorem of_injective_of_isDomain [IsDomain A] {φ : R →+* A} (hφ : Function.Injective φ) :
    φ.Flat := by
  let _ := φ.toAlgebra
  change Module.Flat R A
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro x hx
  obtain ⟨⟨r, hr⟩, hrx⟩ := (Submodule.mem_torsion_iff x).mp hx
  rw [Submodule.mem_bot]
  rw [Submonoid.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hrx
  have hrne : φ r ≠ 0 := fun h ↦
    mem_nonZeroDivisors_iff_ne_zero.mp hr (hφ (h.trans φ.map_zero.symm))
  exact (mul_eq_zero.mp hrx).resolve_left hrne

end RingHom.Flat

/-! ### Normalization of a model -/

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

namespace Model

variable (M : Model R K C toK)

section Flatness

variable [IsIntegral M.total]

/-- The algebra map from the sections of `M.total` on a nonempty affine open to the integral
closure computing the corresponding chart of the normalization is injective.  It factors, through
an algebra isomorphism relating the sections of the function-field point to the function field
itself, through the (always injective) inclusion of a domain into the integral closure of itself
inside its own fraction field. -/
theorem injective_normalize_algebraMap (U : M.total.affineOpens) [Nonempty U.1] :
    letI := ((Normalization.genericPointMap M.total).app U.1).hom.toAlgebra
    Function.Injective
      (algebraMap Γ(M.total, U.1)
        (integralClosure Γ(M.total, U.1)
          Γ(Spec M.total.functionField, Normalization.genericPointMap M.total ⁻¹ᵁ U.1))) := by
  let _ := ((Normalization.genericPointMap M.total).app U.1).hom.toAlgebra
  have hfrac : IsFractionRing Γ(M.total, U.1) M.total.functionField :=
    functionField_isFractionRing_of_isAffineOpen M.total U.1 U.2
  have h0 : Function.Injective
      (algebraMap Γ(M.total, U.1) (integralClosure Γ(M.total, U.1) M.total.functionField)) :=
    Normalization.algebraMap_integralClosure_injective _ _
  set e := Normalization.integralClosureAlgEquiv
    (Normalization.functionFieldAlgEquiv M.total U.1) with he
  have h1 : Function.Injective e := e.injective
  intro a b hab
  apply h0
  apply h1
  rw [e.commutes, e.commutes, hab]

/-- The Mathlib normalization diagram's chart ring map unfolds to the classical algebra map into
the integral closure inside the function field. -/
theorem normalizationDiagramMap_app_hom (U : M.total.affineOpens) :
    letI := ((Normalization.genericPointMap M.total).app U.1).hom.toAlgebra
    ((Normalization.genericPointMap M.total).normalizationDiagramMap.app
        (Opposite.op U.1)).hom =
      algebraMap Γ(M.total, U.1)
        (integralClosure Γ(M.total, U.1)
          Γ(Spec M.total.functionField, Normalization.genericPointMap M.total ⁻¹ᵁ U.1)) := rfl

/-- The chart-level ring map of the normalization of `M.total` over an affine open `U` of
`M.total`, composed with the structure map on `U`, is flat over `R`.  On a nonempty chart this is
the composite of the injective, flat structure map of `M` (hence injective by
`RingHom.Flat.injective_of_isDomain`) with the injective inclusion into the integral closure
(`injective_normalize_algebraMap`), which is flat by `RingHom.Flat.of_injective_of_isDomain`
since the integral closure is a domain.  An empty chart is handled separately, since its sections
(and hence the whole chart of the normalization) form the zero ring. -/
theorem flat_normalize_chartMap (U : M.total.affineOpens) :
    letI := ((Normalization.genericPointMap M.total).app U.1).hom.toAlgebra
    ((algebraMap Γ(M.total, U.1)
        (integralClosure Γ(M.total, U.1)
          Γ(Spec M.total.functionField, Normalization.genericPointMap M.total ⁻¹ᵁ U.1))).comp
      (affineStructureMap M U)).Flat := by
  let _ := ((Normalization.genericPointMap M.total).app U.1).hom.toAlgebra
  rcases (U.1 : Set M.total).eq_empty_or_nonempty with hU | hU
  · have hUbot : U.1 = ⊥ := SetLike.ext' hU
    have hsub : Subsingleton Γ(M.total, U.1) := hUbot ▸ inferInstance
    have := Module.subsingleton Γ(M.total, U.1)
      (integralClosure Γ(M.total, U.1)
        Γ(Spec M.total.functionField, Normalization.genericPointMap M.total ⁻¹ᵁ U.1))
    exact RingHom.Flat.of_subsingleton _
  · have hUinst : Nonempty U.1 := hU.to_subtype
    have htop : Normalization.genericPointMap M.total ⁻¹ᵁ U.1 = ⊤ :=
      Normalization.preimage_genericPointMap_eq_top M.total U.1
    have hneB : Nonempty (Normalization.genericPointMap M.total ⁻¹ᵁ U.1 :
        (Spec M.total.functionField).Opens) :=
      ⟨⟨Classical.arbitrary _, by rw [htop]; trivial⟩⟩
    have hdom : IsDomain
        (integralClosure Γ(M.total, U.1)
          Γ(Spec M.total.functionField, Normalization.genericPointMap M.total ⁻¹ᵁ U.1)) :=
      inferInstance
    have hinjA : Function.Injective (affineStructureMap M U) :=
      RingHom.Flat.injective_of_isDomain (flat_affineStructureMap M U)
    exact RingHom.Flat.of_injective_of_isDomain
      ((injective_normalize_algebraMap M U).comp hinjA)

set_option backward.isDefEq.respectTransparency false in
/-- **Flatness of the normalization of a model.**  The normalization of `M.total`, viewed over
`R` through `M.toBase`, is flat: this is checked chart by chart on the affine open cover of the
normalization furnished by Mathlib's relative-normalization machinery, using
`flat_normalize_chartMap` together with the chart identity `Scheme.Hom.ι_fromNormalization` and
the model's own structure-map factorization `fromSpec_comp_toBase`. -/
theorem flat_normalizeToBase : Flat (Normalization.toCurve M.total ≫ M.toBase) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover
    (Normalization.genericPointMap M.total).normalizationOpenCover fun U ↦ ?_
  rw [← Category.assoc, Scheme.Hom.ι_fromNormalization, Category.assoc, fromSpec_comp_toBase,
    ← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_comp,
    CommRingCat.hom_ofHom]
  exact flat_normalize_chartMap M U

end Flatness

section Finite

variable [IsIntegral M.total] [IsFinite (Normalization.toCurve M.total)]

/-- Under the hypothesis that the normalization morphism is finite (proved unconditionally in
characteristic zero in `NormalizationFinite.lean`, and stated here as an explicit hypothesis so
that this file does not depend on the characteristic), the normalization of `M.total` is again
locally of finite presentation over `R`: `M.toBase` is locally of finite presentation, the finite
morphism `Normalization.toCurve M.total` is locally of finite type, so the composite is locally of
finite type over the Noetherian base `Spec R`, hence locally of finite presentation by Mathlib's
Noetherian-base finite-type-equals-finite-presentation instance. -/
instance locallyOfFinitePresentation_normalizeToBase :
    LocallyOfFinitePresentation (Normalization.toCurve M.total ≫ M.toBase) :=
  inferInstance

/-- Under the same finiteness hypothesis, the normalization of `M.total` is quasi-compact over
`R`: a finite morphism is affine, hence quasi-compact, and `M.toBase` is already quasi-compact. -/
instance quasiCompact_normalizeToBase :
    QuasiCompact (Normalization.toCurve M.total ≫ M.toBase) :=
  inferInstance

/-- The normalization morphism of a model is proper: finite morphisms are proper. -/
instance isProper_toCurve : _root_.AlgebraicGeometry.IsProper (Normalization.toCurve M.total) :=
  inferInstance

end Finite

section GenericFiber

variable [IsIntegral M.total]

/-- **The normalization of a model.**  Given that the normalization morphism is finite (so that
finite presentation and quasi-compactness transfer, see `Finite` above) and that the induced map
on generic fibres is already an isomorphism (a hypothesis recording that the generic fibre of `M`
is already normal at every point in its smooth/normal locus; establishing this from `M` alone
would need a going-down argument -- that the generic point of `M.total` maps to the generic point
of `Spec R` -- that is not yet available in this repository), the normalization of `M.total` is
again a model of the same curve. -/
def normalize [IsFinite (Normalization.toCurve M.total)]
    (hgen : IsIso (genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase)) :
    Model R K C toK where
  total := Normalization.scheme M.total
  toBase := Normalization.toCurve M.total ≫ M.toBase
  flat := flat_normalizeToBase M
  locallyOfFinitePresentation := locallyOfFinitePresentation_normalizeToBase M
  quasiCompact := quasiCompact_normalizeToBase M
  genericFiberIso :=
    haveI := hgen
    Over.isoMk (f := genericFiber R K (Normalization.toCurve M.total ≫ M.toBase))
      (g := genericFiber R K M.toBase)
      (asIso (genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase))
      (by simp) ≪≫ M.genericFiberIso

/-- The identity on generic fibres carried by the isomorphism data of `normalize`. -/
theorem genericFiberMap_comp_normalize_genericFiberIso_hom_left
    [IsFinite (Normalization.toCurve M.total)]
    (hgen : IsIso (genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase)) :
    genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase ≫
        M.genericFiberIso.hom.left = (M.normalize hgen).genericFiberIso.hom.left := by
  have := hgen
  simp [normalize]

/-- The normalization morphism as a morphism of models. -/
def normalizeHom [IsFinite (Normalization.toCurve M.total)]
    (hgen : IsIso (genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase)) :
    M.normalize hgen ⟶ M where
  hom := Normalization.toCurve M.total
  over_base := rfl
  genericFiber := genericFiberMap_comp_normalize_genericFiberIso_hom_left M hgen

/-- **Normalization is a proper modification.**  The normalization morphism of a model, under the
finiteness and generic-fibre hypotheses above, is a proper modification from the normalized model
to `M`. -/
def normalizeModification [IsFinite (Normalization.toCurve M.total)]
    (hgen : IsIso (genericFiberMap (K := K) (Normalization.toCurve M.total) M.toBase)) :
    ModelModification (M.normalize hgen) M where
  hom := normalizeHom M hgen
  proper := isProper_toCurve M
  genericIsIso := hgen

end GenericFiber

end Model

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
