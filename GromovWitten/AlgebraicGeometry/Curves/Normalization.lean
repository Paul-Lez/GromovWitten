/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Normalization of an integral curve or scheme

For an integral scheme `X`, its function-field point is a dominant morphism to `X`.  Applying
Mathlib's relative-normalization construction to this morphism gives the actual normalization of
`X`: affine charts are spectra of the integral closures of their coordinate rings in the function
field.  This file exposes that specialization together with integrality, dominance, surjectivity,
factorization, and uniqueness.

Finiteness of this morphism needs an additional finiteness theorem for integral closures; it is
proved in `GromovWitten/AlgebraicGeometry/Curves/NormalizationFinite.lean` for integral schemes
that are locally of finite type over a field of characteristic zero.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

namespace Normalization

variable (X : Scheme.{u}) [IsIntegral X]

/-- The function-field point of an integral scheme: the canonical morphism from the spectrum of
the stalk at the generic point, i.e. of the function field. -/
abbrev genericPointMap : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- The normalization of `X`, obtained by normalizing it in its function field. -/
abbrev scheme : Scheme.{u} :=
  (genericPointMap X).normalization

/-- The normalization morphism. -/
abbrev toCurve : scheme X ⟶ X :=
  (genericPointMap X).fromNormalization

/-- The lifted function-field point of the normalization. -/
abbrev genericLift : Spec X.functionField ⟶ scheme X :=
  (genericPointMap X).toNormalization

instance toCurve_isIntegral : IsIntegralHom (toCurve X) := inferInstance
instance genericLift_isDominant : IsDominant (genericLift X) := inferInstance
instance scheme_isIntegral : IsIntegral (scheme X) := inferInstance

instance genericPointMap_isDominant : IsDominant (genericPointMap X) := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (genericPointMap X).base := by
    change genericPoint X ∈ Set.range (X.fromSpecStalk (genericPoint X)).base
    rw [Scheme.range_fromSpecStalk]
    exact specializes_rfl
  refine Set.eq_univ_of_univ_subset ?_
  have := closure_mono (Set.singleton_subset_iff.mpr hmem)
  rwa [genericPoint_spec X] at this

@[simp]
theorem genericLift_toCurve : genericLift X ≫ toCurve X = genericPointMap X :=
  Scheme.Hom.toNormalization_fromNormalization _

instance toCurve_isDominant : IsDominant (toCurve X) := by
  let _ : IsDominant (genericLift X ≫ toCurve X) := by
    rw [genericLift_toCurve]
    infer_instance
  exact IsDominant.of_comp (genericLift X) (toCurve X)

/-- The integral normalization morphism is surjective: its closed image contains the dense
function-field point. -/
instance toCurve_surjective : Surjective (toCurve X) :=
  surjective_of_isDominant_of_isClosed_range (toCurve X)
    (toCurve X).isClosedMap.isClosed_range

variable {X}
variable {T : Scheme.{u}}
    (a : Spec X.functionField ⟶ T)
    (b : T ⟶ X) [IsIntegralHom b]

/-- Every integral factorization of the function-field point receives a canonical morphism from
the normalization. -/
def desc (h : genericPointMap X = a ≫ b) : scheme X ⟶ T :=
  (genericPointMap X).normalizationDesc a b h

instance desc_isIntegral (h : genericPointMap X = a ≫ b) :
    IsIntegralHom (desc a b h) := by
  change IsIntegralHom ((genericPointMap X).normalizationDesc a b h)
  infer_instance

@[simp]
theorem genericLift_desc (h : genericPointMap X = a ≫ b) :
    genericLift X ≫ desc a b h = a := by
  exact Scheme.Hom.toNormalization_normalizationDesc _ _ _ _

@[simp]
theorem desc_toCurve (h : genericPointMap X = a ≫ b) :
    desc a b h ≫ b = toCurve X := by
  exact Scheme.Hom.normalizationDesc_comp _ _ _ _

/-- Uniqueness in the normalization universal property. -/
theorem hom_ext (f₁ f₂ : scheme X ⟶ T)
    (hgeneric : genericLift X ≫ f₁ = genericLift X ≫ f₂)
    (hf₁ : f₁ ≫ b = toCurve X) (hf₂ : f₂ ≫ b = toCurve X) : f₁ = f₂ := by
  exact Scheme.Hom.normalization.hom_ext
    (genericPointMap X) f₁ f₂ b hgeneric hf₁ hf₂

end Normalization

end

end GromovWitten.AlgebraicGeometry.Curves
