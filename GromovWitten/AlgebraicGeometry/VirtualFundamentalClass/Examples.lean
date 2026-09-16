/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Basic
import GromovWitten.AlgebraicGeometry.Cones.Stack
import GromovWitten.AlgebraicGeometry.Stacks.Scheme

/-!
# Constructed virtual-class examples

This module contains only examples whose data and comparison theorem are constructed in Lean.
It deliberately does not use records with fields such as `formula : virtualClass = ...`: such a
record is a specification of a future example, not an implementation of one.

The first executable acceptance test is the proper smooth point `Spec(k)`.  Its cycle grading is
the actual closure-dimension grading, its rational-equivalence generators and divisors are
canonical, its normal cone is computed from the Rees algebra of the identity ideal, its affine
cotangent presentation and derived obstruction theory have genuine zero terms, its global
resolution is that same affine presentation viewed as a cochain complex, its rank-zero Gysin map
is identity transport, and its resolved-cone class is proved equal to the ordinary fundamental
class.  The Rees cone is also mapped by an actual closed immersion into `Spec Sym(I/I²)`, and
the dual cotangent quotient is proved contractible.  The represented Rees cone and affine normal
sheaf are globally equivalent to the total stack of the constructed rank-zero obstruction
target, compatibly with the canonical Rees immersion.  Upgrading this total-stack comparison to
all additive and contraction data of a `ConeStack.Iso` remains to be constructed.
-/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Examples

open CategoryTheory IntersectionTheory
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u

noncomputable section

variable (k : Type u) [Field k]

/-- The proper point regarded as an actual Deligne--Mumford stack. -/
noncomputable def properPointStack : DeligneMumfordStack.{u} :=
  FppfStack.ofSchemeDeligneMumfordStack
    (_root_.AlgebraicGeometry.Spec (.of k))

/-- The represented point stack is separated because its scheme diagonal is a closed
immersion, hence proper. -/
theorem properPointStack_separated :
    DiagonalHasProperty (properPointStack k).toStack
      (@_root_.AlgebraicGeometry.IsProper : MorphismProperty
        _root_.AlgebraicGeometry.Scheme.{u}) :=
  FppfStack.ofScheme_diagonal_proper _

/-- The represented point stack has a constructed pure dimension-zero atlas presentation. -/
theorem properPointStack_pureDimension :
    PureStackDimension (properPointStack k).toAlgebraicStack 0 :=
  FppfStack.ofSchemeAlgebraicStack_specField_pureDimension k

/-- The identity embedding's Rees normal cone is canonically the point. -/
noncomputable def properPointNormalConeIso :
    ProperPoint.identityNormalCone k ≅
      _root_.AlgebraicGeometry.Spec (.of k) :=
  ProperPoint.identityNormalConeIso k

/-- The obstruction target of the identity theory on the point, constructed as the actual
rank-zero vector-bundle stack `[0/0]`. -/
noncomputable def properPointObstructionTarget :
    CanonicalVectorBundleStack (properPointStack k).toStack :=
  zeroVectorBundleStack (properPointStack k).toAlgebraicStack

/-- The obstruction target has the rank computed from its actual zero-matrix presentation. -/
@[simp] theorem properPointObstructionTarget_stackRank :
    (properPointObstructionTarget k).stackRank = 0 :=
  rfl

/-- The total stack of the zero obstruction target is definitionally the represented point. -/
@[simp] theorem properPointObstructionTarget_total :
    (properPointObstructionTarget k).total = (properPointStack k).toStack :=
  rfl

/-- The point's intrinsic normal sheaf as an actual global abelian cone stack.  Its fibres are
the contractible zero cone over the represented point. -/
noncomputable def properPointIntrinsicNormalSheaf :
    CanonicalAbelianConeStack (properPointStack k).toStack :=
  zeroAbelianConeStack (properPointStack k).toStack canonicalFppfScalarRings

/-- The intrinsic normal cone of the smooth point is the whole zero normal sheaf, included by
the constructed identity cone morphism. -/
noncomputable def properPointIntrinsicNormalCone :
    ClosedConeSubstack (properPointIntrinsicNormalSheaf k).toConeStack where
  cone := (properPointIntrinsicNormalSheaf k).toConeStack
  inclusion := ConeStack.Hom.id _
  inclusion_closed := by
    apply StackHom.id_hasRepresentableProperty

/-- The map induced by the identity perfect obstruction theory is the identity map from the
zero intrinsic normal sheaf to the rank-zero vector-bundle target. -/
noncomputable def properPointNormalMap :
    ConeStack.Hom (properPointIntrinsicNormalSheaf k).toConeStack
      (properPointObstructionTarget k).toConeStack :=
  ConeStack.Hom.id _

/-- The induced normal-sheaf map is a closed immersion because it is the identity. -/
theorem properPointNormalMap_closed :
    (properPointNormalMap k).toStackHom.ClosedImmersion := by
  apply StackHom.id_hasRepresentableProperty

/-- The intrinsic normal sheaf and obstruction target agree as cone stacks, including their
vertices, scalar contractions, and additive structures. -/
noncomputable def properPointNormalSheafTargetIso :
    ConeStack.Iso (properPointIntrinsicNormalSheaf k).toConeStack
      (properPointObstructionTarget k).toConeStack :=
  ConeStack.Iso.refl _

/-- The point's intrinsic normal cone is its obstruction cone, as an isomorphism of cone stacks
rather than merely an equivalence of total stacks. -/
noncomputable def properPointIntrinsicConeTargetIso :
    ConeStack.Iso (properPointIntrinsicNormalCone k).cone
      (properPointObstructionTarget k).toConeStack :=
  ConeStack.Iso.refl _

/-- The represented affine normal sheaf is globally equivalent to the total stack of the
constructed rank-zero obstruction target.  This equivalence is induced by the actual scheme
isomorphism `Spec Sym(0) ≅ Spec(k)`. -/
noncomputable def properPointNormalSheafStackEquivalence :
    StackEquivalenceData
      (FppfStack.ofScheme (ProperPoint.identityNormalSheaf k))
      (properPointObstructionTarget k).total :=
  FppfStack.stackEquivalenceOfSchemeIso (ProperPoint.identityNormalSheafIso k)

/-- The represented Rees normal cone is globally equivalent to the same obstruction target,
using its computed scheme isomorphism with `Spec(k)`. -/
noncomputable def properPointNormalConeStackEquivalence :
    StackEquivalenceData
      (FppfStack.ofScheme (ProperPoint.identityNormalCone k))
      (properPointObstructionTarget k).total :=
  FppfStack.stackEquivalenceOfSchemeIso (ProperPoint.identityNormalConeIso k)

/-- The global equivalence of the Rees cone with the obstruction target factors through the
canonical closed immersion into the affine normal sheaf. -/
noncomputable def properPointConeTargetCompatibility : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (FppfStack.mapOfSchemeHom (ProperPoint.identityConeToNormalSheaf k))
      (properPointNormalSheafStackEquivalence k).hom)
    (properPointNormalConeStackEquivalence k).hom := by
  dsimp [properPointNormalSheafStackEquivalence,
    properPointNormalConeStackEquivalence, FppfStack.stackEquivalenceOfSchemeIso]
  exact (FppfStack.mapOfSchemeHom_comp_iso _ _).trans
    (by
      rw [ProperPoint.identityConeToNormalSheaf_comp_normalSheafIso]
      exact StackIso2.refl _)

/-- The concrete affine cotangent presentation used by the point example. -/
noncomputable def properPointCotangentComplex : LinearTwoTermComplex k :=
  ProperPoint.identityCotangentComplex k

/-- The same affine presentation as an honest cochain complex in degrees `-1` and `0`. -/
noncomputable def properPointCotangentCochainComplex :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  ProperPoint.identityPresentationCochainComplex k

/-- Its derived localization is proved zero from the actual termwise computation. -/
noncomputable def properPointDerivedCotangentIsoZero :
    ProperPoint.derivedCotangentObject k ≅
      (0 : DerivedCategory (ModuleCat.{u} k)) :=
  ProperPoint.derivedCotangentObjectIsoZero k

/-- The actual dual two-term presentation whose quotient models `h¹/h⁰(Lᵛ)`. -/
noncomputable def properPointDualCotangentComplex : LinearTwoTermComplex k :=
  ProperPoint.identityObstructionDualComplex k

/-- The dual POT acts as the identity on the concrete quotient groupoid. -/
theorem properPoint_dualPOT_quotientFunctor :
    (ProperPoint.identityObstructionTheoryDualMap k).quotientFunctor =
      Functor.id (ProperPoint.identityObstructionDualComplex k).quotient :=
  ProperPoint.identityObstructionTheoryDualMap_quotientFunctor k

/-- The Rees normal cone maps by a constructed closed immersion into the affine normal sheaf. -/
theorem properPoint_coneToNormalSheaf_closed :
    (@_root_.AlgebraicGeometry.IsClosedImmersion : MorphismProperty
      _root_.AlgebraicGeometry.Scheme.{u})
      (ProperPoint.identityConeToNormalSheaf k) :=
  ProperPoint.identityConeToNormalSheaf_closedImmersion k

/-- The point's derived obstruction theory is constructed as the identity of its zero
cotangent object. -/
noncomputable def properPointObstructionTheory :=
  ProperPoint.identityObstructionTheory k

/-- The identity theory is genuinely perfect: its source has the displayed finite-free zero
resolution and its amplitude is proved from the computed derived isomorphism to zero. -/
theorem properPointObstructionTheory_isPerfect :
    ProperPoint.IsPerfectComplex k (properPointObstructionTheory k).E ∧
      DerivedObstructionTheory.HasAmplitudeNegOneZero
        (properPointObstructionTheory k).E :=
  ProperPoint.identityObstructionTheory_isPerfect k

/-- The point's global two-term resolution uses the actual affine cotangent cochain complex. -/
noncomputable def properPointGlobalResolution :=
  ProperPoint.zeroGlobalResolution k

/-- The identity chain map on that resolution localizes to the point's obstruction-theory
morphism. -/
theorem properPoint_resolution_realizes_obstructionTheory :
    DerivedCategory.Q.map (ProperPoint.identityObstructionTheoryResolutionMap k) =
      (ProperPoint.zeroGlobalResolution k).comparison.hom ≫
        (properPointObstructionTheory k).φ :=
  ProperPoint.identityObstructionTheoryResolutionMap_realizes k

/-- The ranks of that resolution compute virtual dimension zero. -/
theorem properPoint_resolution_virtualRank :
    (ProperPoint.zeroGlobalResolution k).virtualRank = 0 :=
  ProperPoint.zeroGlobalResolution_virtualRank k

/-- The two ranks used by the resolved cone are definitionally the ranks of the actual global
resolution terms; their vanishing is subsequently proved, not entered as independent data. -/
theorem properPoint_resolvedRanks_are_resolutionRanks :
    ProperPoint.resolutionRankF₀ k =
        Module.finrank k ((ProperPoint.zeroGlobalResolution k).complex.X 0) ∧
      ProperPoint.resolutionRankF₁ k =
        Module.finrank k ((ProperPoint.zeroGlobalResolution k).complex.X (-1)) :=
  ProperPoint.resolvedCone_ranks_eq_zeroGlobalResolution k

/-- The constructed rational Chow group of `Spec(k)` is canonically `ℚ`. -/
def properPointChowEquiv :
    (PointChow.grading k).group 0 ≃ₗ[ℚ] ℚ :=
  PointChow.chowEquivRat k

/-- The ordinary fundamental class of `Spec(k)` has degree one. -/
@[simp]
theorem properPoint_fundamentalClass_degree_one :
    properPointChowEquiv k
      (ProperPoint.fundamentalClass k) = 1 :=
  PointChow.fundamentalClass_degree_one k

/-- For the actual Rees normal cone of the identity embedding, the constructed rank-zero
resolved-cone formula gives the ordinary fundamental class. -/
theorem properPoint_virtual_eq_fundamental :
    ProperPoint.virtualClass k =
      ProperPoint.fundamentalClass k :=
  ProperPoint.virtualClass_eq_fundamentalClass k

/-- The cone immersion used in the resolved Chow formula factors through the actual affine
normal sheaf. -/
theorem properPoint_resolvedCone_factors_through_normalSheaf :
    (ProperPoint.resolvedCone k).inclusion =
      ProperPoint.identityConeToNormalSheaf k ≫
        (ProperPoint.identityNormalSheafIso k).hom :=
  ProperPoint.resolvedCone_inclusion_factors_through_normalSheaf k

/-- The point's displayed resolved cone is the actual categorical pullback along the rank-zero
bundle atlas. -/
theorem properPoint_resolvedCone_isPullback :
    IsPullback (ProperPoint.identityNormalConeIso k).hom
      (𝟙 (ProperPoint.identityNormalCone k))
      (ProperPoint.identityNormalSheafIso k).inv
      (ProperPoint.identityConeToNormalSheaf k) :=
  ProperPoint.identityResolvedCone_isPullback k

/-- Consequently the point's virtual degree is one. -/
@[simp]
theorem properPoint_virtual_degree_one :
    properPointChowEquiv k
      (ProperPoint.virtualClass k) = 1 :=
  ProperPoint.virtualClass_degree_one k

/-- The scheme in this example is proper over its ground point. -/
theorem properPoint_isProper :
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty
      _root_.AlgebraicGeometry.Scheme.{u})
      (𝟙 (_root_.AlgebraicGeometry.Spec (.of k))) :=
  ProperPoint.proper_over_self k

end

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Examples
