/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeBaseChange
import GromovWitten.AlgebraicGeometry.Curves.Nodal

/-!
# Fibrewise nodal certificate for the explicit local node

This file connects the geometric-fibre calculation for `R[x,y]/(xy-πⁿ)` to the shared
scheme-level nodal-family predicate.  The chart is flat, locally of finite presentation, and
geometrically pure of relative dimension one.  After every field-valued coefficient extension its
fibre is either smooth of relative dimension one or is explicitly isomorphic over the field to the
standard node `xy = 0`; consequently the structural morphism is at worst nodal and this property
is available through the repository-wide arbitrary-base-change interface.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u

noncomputable section

/-- Exponent-zero node algebras do not depend on the displayed parameter. -/
def exponentZeroEquiv (R : Type u) [CommRing R] (π ρ : R) :
    Ring R π 0 ≃ₐ[R] Ring R ρ 0 :=
  Ideal.quotientEquivAlgOfEq R (by
    unfold relationIdeal
    congr 2
    simp only [equation, pow_zero])

/-- All positive-exponent zero-parameter presentations define the same standard node. -/
def positiveZeroParameterEquiv (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Ring R 0 n ≃ₐ[R] Ring R 0 1 :=
  Ideal.quotientEquivAlgOfEq R (by
    unfold relationIdeal
    congr 2
    simp only [equation, zero_pow hn, zero_pow one_ne_zero])

/-- Scheme-level positive-exponent zero-parameter comparison, over the coefficient field. -/
noncomputable def positiveZeroParameterOverIso
    (F : Type u) [Field F] (n : ℕ) (hn : n ≠ 0) :
    Over.mk (toBaseSpec F 0 n) ≅
      Over.mk (GromovWitten.AlgebraicGeometry.Curves.standardNodeToSpec F) := by
  let e : Ring F 0 n ≃ₐ[F] Ring F 0 1 := positiveZeroParameterEquiv F n hn
  let E : Spec (.of (Ring F 0 n)) ≅ Spec (.of (Ring F 0 1)) :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op.symm
  refine Over.isoMk E ?_
  change E.hom ≫ toBaseSpec F 0 1 = toBaseSpec F 0 n
  dsimp only [E]
  simp only [Functor.mapIso_hom, Iso.symm_hom, Scheme.Spec_map]
  rw [toBaseSpec, toBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact RingHom.ext fun r ↦ e.symm.commutes r

/-- At exponent zero the node equation is `xy = 1`, so the structural morphism is smooth of
relative dimension one for every displayed parameter. -/
theorem toBaseSpec_smoothOfRelativeDimension_one_zero
    (R : Type u) [CommRing R] (π : R) :
    SmoothOfRelativeDimension 1 (toBaseSpec R π 0) := by
  rw [toBaseSpec]
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr
  have h := ring_standardSmoothOfRelativeDimension_one_of_isUnit R 1 0 isUnit_one
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (exponentZeroEquiv R π 1).symm

/-- Every coefficient base change of an exponent-zero node is smooth of relative dimension
one. -/
theorem baseChangedNodeToBaseSpec_smoothOfRelativeDimension_one_zero
    (R : Type u) [CommRing R] (T : Type u) [CommRing T] [Algebra R T] (π : R) :
    SmoothOfRelativeDimension 1 (baseChangedNodeToBaseSpec R T π 0) := by
  change SmoothOfRelativeDimension 1
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π 0))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
  exact (_root_.AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π 0))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    (toBaseSpec_smoothOfRelativeDimension_one_zero R π)

/-- A theorem-backed certificate for the exact geometric fibres of this explicit chart.

For every field-valued coefficient extension, the base-changed chart is either smooth of
relative dimension one, or the exponent is positive, the parameter vanishes, and the chart is
explicitly isomorphic over the field to the standard node `xy = 0`. -/
structure ExplicitNodalFiberCertificate
    (R : Type u) [CommRing R] (π : R) (n : ℕ) : Prop where
  flat : Flat (toBaseSpec R π n)
  locallyOfFinitePresentation : LocallyOfFinitePresentation (toBaseSpec R π n)
  geometricPureRelativeDimension :
    GromovWitten.AlgebraicGeometry.Curves.GeometricPureRelativeDimension 1
      (toBaseSpec R π n)
  geometricFiberShape : ∀ (F : Type u) [Field F] [Algebra R F],
    SmoothOfRelativeDimension 1 (baseChangedNodeToBaseSpec R F π n) ∨
      (n ≠ 0 ∧ algebraMap R F π = 0 ∧
        Nonempty (Over.mk (baseChangedNodeToBaseSpec R F π n) ≅
          Over.mk (toBaseSpec F 0 n)))

/-- Every explicit local-node chart has the fibrewise nodal certificate. -/
theorem explicitNodalFiberCertificate
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    ExplicitNodalFiberCertificate R π n where
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance
  geometricPureRelativeDimension := toBaseSpec_geometricPureRelativeDimension_one R π n
  geometricFiberShape := by
    intro F _ _
    by_cases hn : n = 0
    · left
      subst n
      exact baseChangedNodeToBaseSpec_smoothOfRelativeDimension_one_zero R F π
    · by_cases hπ : algebraMap R F π = 0
      · right
        exact ⟨hn, hπ, ⟨specialFiberOverIso R F π n hπ⟩⟩
      · left
        change SmoothOfRelativeDimension 1
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
            (Spec.map (CommRingCat.ofHom (algebraMap R F))))
        exact genericFiberProjection_smoothOfRelativeDimension_one R F π n hπ

/-- The explicit local-node chart instantiates the shared geometric at-worst-nodal family
predicate.  This quantifies over arbitrary field-valued pullback squares, rather than only the
chosen affine fibre product. -/
theorem toBaseSpec_atWorstNodal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.AtWorstNodal (toBaseSpec R π n) where
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance
  geometricPureRelativeDimension := toBaseSpec_geometricPureRelativeDimension_one R π n
  geometricFibers := by
    intro F _ y Z fst snd hsquare
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    algebraize [φ.hom]
    have hchosen : GromovWitten.AlgebraicGeometry.Curves.IsNodalCurveOverField
        (baseChangedNodeToBaseSpec R F π n) := by
      rcases (explicitNodalFiberCertificate R π n).geometricFiberShape F with hsm | hnode
      · let _ : SmoothOfRelativeDimension 1 (baseChangedNodeToBaseSpec R F π n) := hsm
        exact GromovWitten.AlgebraicGeometry.Curves.IsNodalCurveOverField.of_smooth _
          (SmoothOfRelativeDimension.smooth 1 _)
      · obtain ⟨hn, -, ⟨e⟩⟩ := hnode
        exact
          GromovWitten.AlgebraicGeometry.Curves.IsNodalCurveOverField.of_overIso_standardNode _
            (e.trans (positiveZeroParameterOverIso F n hn))
    have htransport :=
      GromovWitten.AlgebraicGeometry.Curves.IsNodalCurveOverField.precomp_iso
        hsquare.isoPullback (baseChangedNodeToBaseSpec R F π n) hchosen
    change GromovWitten.AlgebraicGeometry.Curves.IsNodalCurveOverField
      (hsquare.isoPullback.hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
          (Spec.map φ)) at htransport
    have heq : hsquare.isoPullback.hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
          (Spec.map φ) = snd := hsquare.isoPullback_hom_snd
    rw [heq] at htransport
    exact htransport

instance toBaseSpec_instAtWorstNodal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.AtWorstNodal (toBaseSpec R π n) :=
  toBaseSpec_atWorstNodal R π n

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
