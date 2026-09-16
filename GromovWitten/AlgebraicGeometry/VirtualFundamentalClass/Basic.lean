/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.Affine
import GromovWitten.AlgebraicGeometry.CotangentComplex.AffinePresentation
import GromovWitten.AlgebraicGeometry.IntersectionTheory.Gysin
import GromovWitten.AlgebraicGeometry.ObstructionTheory.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The proper-point resolved cone formula

This file constructs the grading-sensitive Behrend--Fantechi calculation for the proper smooth
point.  Its normal cone is the actual Rees cone of the identity ideal, both terms of its global
two-term resolution are proved zero, and the zero-section Gysin operation is therefore literal
grading transport.

There is deliberately no general resolved-cone input record here.  The former record accepted
vector-bundle homotopy invariance as a field, which allowed the central geometric theorem to be
provided by a caller rather than proved.
-/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass

open CategoryTheory
open CategoryTheory.Limits
open IntersectionTheory
open scoped ZeroObject

universe u v

namespace ProperPoint

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k]

private noncomputable abbrev pointScheme : Scheme.{u} :=
  _root_.AlgebraicGeometry.Spec (.of k)

/-- The defining ideal of the identity closed immersion of the affine point. -/
abbrev identityIdeal : Ideal k := ⊥

/-- The actual Rees normal cone of the identity embedding `Spec(k) → Spec(k)`. -/
noncomputable abbrev identityNormalCone : Scheme.{u} :=
  AffineNormalCone.scheme k (identityIdeal k)

/-- The coefficientwise Rees-algebra calculation identifies the identity normal cone with the
point. -/
noncomputable def identityNormalConeIso :
    identityNormalCone k ≅ pointScheme k :=
  AffineNormalCone.schemeBotIso k

noncomputable instance identityNormalConeUnique : Unique (identityNormalCone k) :=
  (identityNormalConeIso k).schemeIsoToHomeo.toEquiv.unique

noncomputable instance identityNormalConeIsIntegral :
    _root_.AlgebraicGeometry.IsIntegral (identityNormalCone k) :=
  _root_.AlgebraicGeometry.IsIntegral.of_isIso (identityNormalConeIso k).inv

noncomputable instance identityNormalConeIsReduced :
    _root_.AlgebraicGeometry.IsReduced (identityNormalCone k) :=
  _root_.AlgebraicGeometry.isReduced_of_isOpenImmersion
    (identityNormalConeIso k).hom

noncomputable instance identityNormalConeIsLocallyNoetherian :
    _root_.AlgebraicGeometry.IsLocallyNoetherian (identityNormalCone k) :=
  _root_.AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion
    (identityNormalConeIso k).hom

/-- The zero-variable affine presentation of the identity algebra `k → k`. -/
noncomputable def identityAffinePresentation : Algebra.Extension k k :=
  Algebra.Extension.self k k

/-- Its defining ideal is the zero ideal used by the Rees normal cone above. -/
theorem identityAffinePresentation_ker :
    (identityAffinePresentation k).ker = identityIdeal k := by
  ext x
  simp [identityAffinePresentation, identityIdeal, Algebra.Extension.self]

/-- The actual two-term affine cotangent presentation of the identity algebra. -/
noncomputable def identityCotangentComplex : LinearTwoTermComplex k :=
  CotangentComplex.AffinePresentation.twoTerm k k (identityAffinePresentation k)

noncomputable instance identityCotangentDegreeZeroSubsingleton :
    Subsingleton (identityCotangentComplex k).degreeZero := by
  change Subsingleton (identityAffinePresentation k).Cotangent
  change Subsingleton (identityAffinePresentation k).ker.Cotangent
  rw [identityAffinePresentation_ker k]
  exact AffineNormalCone.conormalModuleBotSubsingleton k

noncomputable instance identityCotangentDegreeOneSubsingleton :
    Subsingleton (identityCotangentComplex k).degreeOne := by
  change Subsingleton
    (TensorProduct (identityAffinePresentation k).Ring k
      (KaehlerDifferential (identityAffinePresentation k).Ring k))
  have hsurj : Function.Surjective
      (algebraMap k (identityAffinePresentation k).Ring) := by
    intro x
    exact ⟨x, by rfl⟩
  let _ : Subsingleton
      (KaehlerDifferential (identityAffinePresentation k).Ring k) :=
    KaehlerDifferential.subsingleton_of_surjective
      (identityAffinePresentation k).Ring k hsurj
  infer_instance

/-- Thus the displayed cotangent differential is the unique map between zero modules. -/
theorem identityCotangentComplex_differential_eq_zero :
    (identityCotangentComplex k).differential = 0 := by
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- The actual dual two-term complex underlying the obstruction target
`h¹/h⁰(Lₓᵛ)`.  Its terms are the dual ambient tangent and dual conormal modules, in that
order. -/
noncomputable def identityObstructionDualComplex : LinearTwoTermComplex k :=
  (identityCotangentComplex k).dual

/-- Dualizing the identity POT is represented by the identity chain map of the actual dual
cotangent presentation. -/
noncomputable def identityObstructionTheoryDualMap :
    LinearTwoTermComplex.Hom (identityObstructionDualComplex k)
      (identityObstructionDualComplex k) :=
  LinearTwoTermComplex.Hom.id _

/-- Hence the induced morphism on the concrete `h¹/h⁰` quotient groupoid is the identity
functor, not a separately supplied normal-map action. -/
@[simp]
theorem identityObstructionTheoryDualMap_quotientFunctor :
    (identityObstructionTheoryDualMap k).quotientFunctor =
      Functor.id (identityObstructionDualComplex k).quotient :=
  LinearTwoTermComplex.Hom.quotientFunctor_id _

noncomputable instance identityObstructionDualDegreeZeroSubsingleton :
    Subsingleton (identityObstructionDualComplex k).degreeZero := by
  change Subsingleton (Module.Dual k (identityCotangentComplex k).degreeOne)
  exact LinearTwoTermComplex.dual_subsingleton

noncomputable instance identityObstructionDualDegreeOneSubsingleton :
    Subsingleton (identityObstructionDualComplex k).degreeOne := by
  change Subsingleton (Module.Dual k (identityCotangentComplex k).degreeZero)
  exact LinearTwoTermComplex.dual_subsingleton

/-- The displayed dual differential is the unique map between its actual zero dual modules. -/
theorem identityObstructionDualComplex_differential_eq_zero :
    (identityObstructionDualComplex k).differential = 0 := by
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- The quotient groupoid of the actual dual cotangent presentation has a unique object. -/
noncomputable instance identityObstructionQuotientUnique :
    Unique (identityObstructionDualComplex k).quotient where
  default := TwoTermQuotient.vertex _
  uniq x := by
    rcases x with ⟨x⟩
    congr
    exact Subsingleton.elim x 0

/-- It also has a unique arrow between every pair of objects, retaining and then computing the
automorphism group rather than truncating the quotient to a set. -/
noncomputable instance identityObstructionQuotientHomSubsingleton
    (x y : (identityObstructionDualComplex k).quotient) :
    Subsingleton (x ⟶ y) where
  allEq f g := by
    apply TwoTermQuotient.Hom.ext
    exact Subsingleton.elim _ _

/-- Sections of the affine normal sheaf over its affine base.  By the symmetric-algebra
construction these are its genuine functor-of-points objects over the identity base point. -/
abbrev identityNormalSheafSections : Type u :=
  AffineCone.Section (k ⧸ identityIdeal k)
    (AffineNormalCone.conormalModule k (identityIdeal k))

/-- The geometric section objects of `Spec Sym(I/I²)` agree with the objects of the actual
dual-complex quotient in the identity case.  Both sides are proved unique from their respective
constructions; the equivalence therefore makes no selectable object-level choices. -/
noncomputable def identityNormalSheafSectionsEquivObstructionQuotient :
    identityNormalSheafSections k ≃
      (identityObstructionDualComplex k).quotient :=
  Equiv.ofUnique _ _

/-- The affine normal sheaf of the identity embedding, constructed as
`Spec Sym(I/I²)`. -/
noncomputable abbrev identityNormalSheaf : Scheme.{u} :=
  AffineNormalCone.normalSheaf k (identityIdeal k)

/-- Since the actual conormal module is zero, the normal sheaf is canonically the point. -/
noncomputable def identityNormalSheafIso :
    identityNormalSheaf k ≅ pointScheme k :=
  AffineNormalCone.normalSheafBotIso k

/-- The identity normal cone maps into its actual affine normal sheaf through the canonical
Rees coordinate map `Sym(I/I²) → gr_I(k)`. -/
noncomputable def identityConeToNormalSheaf :
    identityNormalCone k ⟶ identityNormalSheaf k :=
  AffineNormalCone.coneToNormalSheaf k (identityIdeal k)

noncomputable instance identityConeToNormalSheaf_isIso :
    IsIso (identityConeToNormalSheaf k) := by
  rw [identityConeToNormalSheaf,
    ← AffineNormalCone.schemeBotIsoNormalSheaf_hom]
  infer_instance

/-- In the smooth identity case, the normal-cone map is therefore a closed immersion for a
constructed reason: it is an isomorphism. -/
theorem identityConeToNormalSheaf_closedImmersion :
    (@_root_.AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})
      (identityConeToNormalSheaf k) := by
  infer_instance

/-- Returning from the normal sheaf to the base recovers the canonical Rees-cone
identification.  This is the point-specific cone-image compatibility used below. -/
@[simp]
theorem identityConeToNormalSheaf_comp_normalSheafIso :
    identityConeToNormalSheaf k ≫ (identityNormalSheafIso k).hom =
      (identityNormalConeIso k).hom := by
  exact
    AffineNormalCone.schemeBotIsoNormalSheaf_hom_comp_normalSheafBotIso_hom k

/-- The affine two-term cotangent presentation, now regarded as an actual cochain complex in
degrees `-1` and `0`. -/
noncomputable def identityPresentationCochainComplex :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  CotangentComplex.AffinePresentation.cochainComplex k k
    (identityAffinePresentation k)

/-- Every term of the actual affine cotangent presentation is a zero module.  This statement is
proved from the two concrete module computations above, not by replacing the presentation with
the categorical zero complex. -/
theorem identityPresentationCochainComplex_term_isZero (i : ℤ) :
    IsZero ((identityPresentationCochainComplex k).X i) := by
  by_cases hiNeg : i = -1
  · subst i
    change IsZero (ModuleCat.of k (identityCotangentComplex k).degreeZero)
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  · by_cases hiZero : i = 0
    · subst i
      change IsZero (ModuleCat.of k (identityCotangentComplex k).degreeOne)
      exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
    · exact (identityCotangentComplex k).toCochainComplex_X_isZero i hiNeg hiZero

/-- The genuine affine cotangent presentation is isomorphic, as a complex, to the categorical
zero complex.  Compatibility with the differentials follows from termwise zero-ness. -/
noncomputable def identityPresentationCochainComplexIsoZero :
    identityPresentationCochainComplex k ≅
      (0 : CochainComplex (ModuleCat.{u} k) ℤ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (identityPresentationCochainComplex_term_isZero k i).iso
      ((HomologicalComplex.eval (ModuleCat.{u} k) (ComplexShape.up ℤ) i).map_isZero
        (isZero_zero (CochainComplex (ModuleCat.{u} k) ℤ))))
    (by
      intro i j _
      exact (identityPresentationCochainComplex_term_isZero k i).eq_of_src _ _)

/-- The derived cotangent object is the localization of the actual affine two-term
presentation.  It is not an independently declared zero object. -/
noncomputable def derivedCotangentObject :
    DerivedCategory (ModuleCat.{u} k) :=
  CotangentComplex.AffinePresentation.derivedObject k k
    (identityAffinePresentation k)

/-- The preceding termwise calculation proves that the derived cotangent object is zero. -/
noncomputable def derivedCotangentObjectIsoZero :
    derivedCotangentObject k ≅ (0 : DerivedCategory (ModuleCat.{u} k)) :=
  (DerivedCategory.Q.mapIso (identityPresentationCochainComplexIsoZero k)) ≪≫
    DerivedCategory.Q.mapZeroObject

/-- The identity of the zero cotangent object is the canonical obstruction theory of the smooth
point; its cohomological conditions are proved by functoriality, not supplied separately. -/
noncomputable def identityObstructionTheory :
    DerivedObstructionTheory.ObstructionTheory (derivedCotangentObject k) :=
  DerivedObstructionTheory.ObstructionTheory.id (derivedCotangentObject k)

@[simp]
theorem identityObstructionTheory_source :
    (identityObstructionTheory k).E = derivedCotangentObject k := rfl

@[simp]
theorem identityObstructionTheory_map :
    (identityObstructionTheory k).φ = 𝟙 (derivedCotangentObject k) := rfl

/-- The actual finite-free condition on modules used in the point's global resolution. -/
def IsFiniteFreeModule (M : ModuleCat.{u} k) : Prop :=
  Module.Finite k M ∧ Module.Free k M

theorem isFiniteFreeModule_of_isZero (M : ModuleCat.{u} k) (hM : IsZero M) :
    IsFiniteFreeModule k M := by
  let _ : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  constructor
  · exact Module.finite_of_rank_eq_zero (rank_subsingleton' k M)
  · infer_instance

/-- Every term of the categorical zero cochain complex is a zero module. -/
theorem zeroCochainComplex_term_isZero (i : ℤ) :
    IsZero ((0 : CochainComplex (ModuleCat.{u} k) ℤ).X i) :=
  (HomologicalComplex.eval (ModuleCat.{u} k) (ComplexShape.up ℤ) i).map_isZero
    (isZero_zero (CochainComplex (ModuleCat.{u} k) ℤ))

/-- A global two-term resolution over the field `k`, with the mathematical finite/free
conditions fixed rather than supplied as an arbitrary predicate. -/
structure FiniteFreeTwoTermResolution
    (E : DerivedCategory (ModuleCat.{u} k)) where
  complex : CochainComplex (ModuleCat.{u} k) ℤ
  zero_outside : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (complex.X i)
  negative_finiteFree : IsFiniteFreeModule k (complex.X (-1))
  zero_finiteFree : IsFiniteFreeModule k (complex.X 0)
  comparison : DerivedCategory.Q.obj complex ≅ E

namespace FiniteFreeTwoTermResolution

/-- Virtual rank is the difference of the actual vector-space dimensions of the displayed
finite free terms. -/
noncomputable def virtualRank {E : DerivedCategory (ModuleCat.{u} k)}
    (F : FiniteFreeTwoTermResolution k E) : ℤ :=
  (Module.finrank k (F.complex.X 0) : ℤ) -
    Module.finrank k (F.complex.X (-1))

end FiniteFreeTwoTermResolution

/-- A genuine global two-term resolution of the point obstruction complex.  Its complex is the
actual cochain realization of the affine cotangent presentation, and its derived comparison is
the identity because `derivedCotangentObject` was defined from precisely this complex. -/
noncomputable def zeroGlobalResolution :
    FiniteFreeTwoTermResolution k (derivedCotangentObject k) where
  complex := identityPresentationCochainComplex k
  zero_outside := fun i _ _ ↦ identityPresentationCochainComplex_term_isZero k i
  negative_finiteFree := isFiniteFreeModule_of_isZero k _
    (identityPresentationCochainComplex_term_isZero k (-1))
  zero_finiteFree := isFiniteFreeModule_of_isZero k _
    (identityPresentationCochainComplex_term_isZero k 0)
  comparison := Iso.refl _

/-- For the module-category example, perfectness means possession of an actual global
two-term resolution by finite free modules.  This is a fixed mathematical predicate, not a
caller-selectable proposition. -/
def IsPerfectComplex (E : DerivedCategory (ModuleCat.{u} k)) : Prop :=
  Nonempty (FiniteFreeTwoTermResolution k E)

/-- The point cotangent object is perfect because the concrete zero complex constructed above
is a global finite-free two-term resolution of it. -/
theorem derivedCotangentObject_isPerfect :
    IsPerfectComplex k (derivedCotangentObject k) :=
  ⟨zeroGlobalResolution k⟩

/-- The computed zero cotangent object has cohomological amplitude contained in `[-1,0]`. -/
theorem derivedCotangentObject_hasAmplitudeNegOneZero :
    DerivedObstructionTheory.HasAmplitudeNegOneZero (derivedCotangentObject k) := by
  intro i _hi
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) i
  exact (H.map_isZero (isZero_zero _)).of_iso
    (H.mapIso (derivedCotangentObjectIsoZero k))

/-- Non-arbitrary perfectness evidence for the identity obstruction theory: its source has the
displayed finite-free resolution and the required intrinsic amplitude. -/
theorem identityObstructionTheory_isPerfect :
    IsPerfectComplex k (identityObstructionTheory k).E ∧
      DerivedObstructionTheory.HasAmplitudeNegOneZero
        (identityObstructionTheory k).E :=
  ⟨derivedCotangentObject_isPerfect k,
    derivedCotangentObject_hasAmplitudeNegOneZero k⟩

/-- The chain map representing the point obstruction theory with respect to its actual global
resolution.  Both source and target are the affine cotangent cochain complex itself. -/
noncomputable def identityObstructionTheoryResolutionMap :
    (zeroGlobalResolution k).complex ⟶ identityPresentationCochainComplex k :=
  𝟙 _

/-- Localizing the displayed chain map gives exactly the obstruction-theory morphism after the
global resolution comparison.  Thus the POT and resolution are joined by an equality of derived
morphisms, rather than merely by agreeing ranks. -/
theorem identityObstructionTheoryResolutionMap_realizes :
    DerivedCategory.Q.map (identityObstructionTheoryResolutionMap k) =
      (zeroGlobalResolution k).comparison.hom ≫ (identityObstructionTheory k).φ := by
  dsimp [identityObstructionTheoryResolutionMap, zeroGlobalResolution,
    identityObstructionTheory, DerivedObstructionTheory.ObstructionTheory.id,
    derivedCotangentObject]
  exact (DerivedCategory.Q :
    CochainComplex (ModuleCat.{u} k) ℤ ⥤
      DerivedCategory (ModuleCat.{u} k)).map_id
    (identityPresentationCochainComplex k)

theorem zeroGlobalResolution_term_rank (i : ℤ) :
    Module.finrank k ((zeroGlobalResolution k).complex.X i) = 0 := by
  change Module.finrank k ((identityPresentationCochainComplex k).X i) = 0
  let _ : Subsingleton ((identityPresentationCochainComplex k).X i) :=
    ModuleCat.subsingleton_of_isZero
      (identityPresentationCochainComplex_term_isZero k i)
  exact Module.finrank_zero_of_subsingleton

/-- The constructed zero resolution has virtual rank zero. -/
theorem zeroGlobalResolution_virtualRank :
    (zeroGlobalResolution k).virtualRank = 0 := by
  change (Module.finrank k ((identityPresentationCochainComplex k).X 0) : ℤ) -
      (Module.finrank k ((identityPresentationCochainComplex k).X (-1)) : ℤ) = 0
  let _ : Subsingleton ((identityPresentationCochainComplex k).X 0) :=
    ModuleCat.subsingleton_of_isZero
      (identityPresentationCochainComplex_term_isZero k 0)
  let _ : Subsingleton ((identityPresentationCochainComplex k).X (-1)) :=
    ModuleCat.subsingleton_of_isZero
      (identityPresentationCochainComplex_term_isZero k (-1))
  rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
  norm_num

/-- The `F₀` rank used by the resolved-cone formula is computed from degree `0` of the actual
global resolution. -/
noncomputable def resolutionRankF₀ : ℕ :=
  Module.finrank k ((zeroGlobalResolution k).complex.X 0)

/-- The `F₁` rank used by the resolved-cone formula is computed from degree `-1` of the actual
global resolution. -/
noncomputable def resolutionRankF₁ : ℕ :=
  Module.finrank k ((zeroGlobalResolution k).complex.X (-1))

@[simp]
theorem resolutionRankF₀_eq_zero : resolutionRankF₀ k = 0 :=
  zeroGlobalResolution_term_rank k 0

@[simp]
theorem resolutionRankF₁_eq_zero : resolutionRankF₁ k = 0 :=
  zeroGlobalResolution_term_rank k (-1)

/-- Zero-section Gysin for the point's actual degree-`-1` resolution term.  That term has proved
rank zero, so this is direct transport of the grading rather than an assumed vector-bundle
homotopy-invariance equivalence. -/
noncomputable def resolutionZeroBundleGysin (i : ℤ) :
    (PointChow.grading k).group (i + resolutionRankF₁ k) →ₗ[ℚ]
      (PointChow.grading k).group i :=
  RationalChowGrading.cast (by
    rw [resolutionRankF₁_eq_zero]
    omega)

@[simp]
theorem resolutionZeroBundle_zeroGysin (i : ℤ)
    (z : (PointChow.grading k).group (i + resolutionRankF₁ k)) :
    resolutionZeroBundleGysin k i z =
      RationalChowGrading.cast (by
        rw [resolutionRankF₁_eq_zero]
        omega) z := by
  rfl

/-- The ordinary fundamental class of the point in its constructed rational Chow group. -/
noncomputable def fundamentalClass : (PointChow.grading k).group 0 :=
  (PointChow.rationalEquivalence k 0).quotientMap (PointChow.fundamentalCycle k)

/-- The resolved cone for the smooth point is the actual Rees normal cone, embedded into the
rank-zero bundle by its computed isomorphism with the base point. -/
noncomputable def resolvedCone : IntegralClosedSubscheme (pointScheme k) where
  scheme := identityNormalCone k
  inclusion := (identityNormalConeIso k).hom

/-- The generic point of the Rees cone has the dimension dictated by the degree-zero term of the
actual global resolution. -/
theorem resolvedCone_dimension (z : (resolvedCone k).scheme) (_hz : IsMax z) :
    DimensionFunction.specField k ((resolvedCone k).inclusion.base z) =
      (resolutionRankF₀ k : ℤ) := by
  rw [resolutionRankF₀_eq_zero]
  exact DimensionFunction.specField_apply k ((identityNormalConeIso k).hom.base z)

/-- The closed cone immersion used by the Chow calculation is exactly the actual normal-cone
map into `Spec Sym(I/I²)`, followed by the proved rank-zero normal-sheaf identification. -/
theorem resolvedCone_inclusion_factors_through_normalSheaf :
    (resolvedCone k).inclusion =
      identityConeToNormalSheaf k ≫ (identityNormalSheafIso k).hom := by
  exact (identityConeToNormalSheaf_comp_normalSheafIso k).symm

/-- The actual Rees cone is the categorical pullback of its normal-sheaf immersion along the
rank-zero bundle atlas `Spec(k) → Spec Sym(I/I²)`.  This is the resolved-cone square in the
identity example, with its universal property proved from the two vertical isomorphisms. -/
theorem identityResolvedCone_isPullback :
    IsPullback (identityNormalConeIso k).hom
      (𝟙 (identityNormalCone k))
      (identityNormalSheafIso k).inv
      (identityConeToNormalSheaf k) := by
  apply IsPullback.of_vert_isIso
  exact ⟨by
    calc
      (identityNormalConeIso k).hom ≫ (identityNormalSheafIso k).inv =
          (identityConeToNormalSheaf k ≫
            (identityNormalSheafIso k).hom) ≫
              (identityNormalSheafIso k).inv := by
        rw [identityConeToNormalSheaf_comp_normalSheafIso]
      _ = identityConeToNormalSheaf k := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

/-- The two numerical ranks in the resolved cone are those of the constructed global derived
resolution, rather than unrelated example constants. -/
theorem resolvedCone_ranks_eq_zeroGlobalResolution :
    resolutionRankF₀ k =
        Module.finrank k ((zeroGlobalResolution k).complex.X 0) ∧
      resolutionRankF₁ k =
        Module.finrank k ((zeroGlobalResolution k).complex.X (-1)) := by
  exact ⟨rfl, rfl⟩

/-- Virtual rank computed from the two actual resolution terms. -/
noncomputable def resolvedConeVirtualRank : ℤ :=
  (resolutionRankF₀ k : ℤ) - (resolutionRankF₁ k : ℤ)

/-- Consequently the resolved formula and global resolution compute the same virtual rank. -/
theorem resolvedCone_virtualRank_eq_zeroGlobalResolution :
    resolvedConeVirtualRank k =
      (zeroGlobalResolution k).virtualRank := by
  rfl

@[simp]
theorem resolvedCone_rankF₀_eq_zero : resolutionRankF₀ k = 0 := by
  exact resolutionRankF₀_eq_zero k

@[simp]
theorem resolvedCone_rankF₁_eq_zero : resolutionRankF₁ k = 0 := by
  exact resolutionRankF₁_eq_zero k

@[simp]
theorem resolvedCone_virtualRank_eq_zero : resolvedConeVirtualRank k = 0 := by
  exact (resolvedCone_virtualRank_eq_zeroGlobalResolution k).trans
    (zeroGlobalResolution_virtualRank k)

/-- The fundamental cycle of the actual Rees cone, pushed along its computed closed immersion. -/
noncomputable def resolvedConeCycle :
    cyclesOfDimension (pointScheme k) (DimensionFunction.specField k)
      (resolutionRankF₀ k : ℤ) := by
  let c : AlgebraicCycle (pointScheme k) ℚ :=
    (resolvedCone k).pushforward (DimensionFunction.specField k)
      (resolvedCone k).scheme.fundamentalCycle
  refine ⟨c, ?_⟩
  intro x hx
  have hsupport : c.support ⊆
      {y : pointScheme k |
        DimensionFunction.specField k y = (resolutionRankF₀ k : ℤ)} := by
    unfold c IntegralClosedSubscheme.pushforward
    unfold _root_.AlgebraicGeometry.AlgebraicCycle.map
    apply Function.locallyFinsupp.support_map_subset_of_forall_mem
      (s := {z : (resolvedCone k).scheme | IsMax z})
    · intro z hz
      by_contra hzmax
      exact hz (by
        rw [(resolvedCone k).scheme.fundamentalCycle_apply_of_not_isMax z hzmax])
    · intro z hz _
      exact resolvedCone_dimension k z hz
  by_contra hzero
  exact hx (hsupport (by simpa [Function.mem_support] using hzero))

/-- The constructed cone cycle for the point is its ordinary fundamental cycle. -/
theorem resolvedConeCycle_eq :
    (resolvedConeCycle k :
        _root_.AlgebraicGeometry.AlgebraicCycle (pointScheme k) ℚ) =
      (PointChow.fundamentalCycle k :
        _root_.AlgebraicGeometry.AlgebraicCycle (pointScheme k) ℚ) := by
  change _root_.AlgebraicGeometry.AlgebraicCycle.map
      (identityNormalConeIso k).hom
        (fun z ↦ DimensionFunction.specField k ((identityNormalConeIso k).hom.base z))
        (DimensionFunction.specField k)
        (identityNormalCone k).fundamentalCycle =
    (PointChow.fundamentalCycle k : AlgebraicCycle (pointScheme k) ℚ)
  ext y
  have hy : (identityNormalConeIso k).hom.base
      (default : identityNormalCone k) = y := Subsingleton.elim _ _
  simp only [_root_.AlgebraicGeometry.AlgebraicCycle.map,
    Function.locallyFinsupp.map_apply, finsum_unique]
  have hxmax : IsMax (default : identityNormalCone k) := by
    intro x _
    exact (Subsingleton.elim x default).le
  have hdegree : (identityNormalConeIso k).hom.residueDegree
      (default : identityNormalCone k) = 1 := by
    let φ := (identityNormalConeIso k).hom.residueFieldMap
      (default : identityNormalCone k)
    let _ : Algebra
        ((pointScheme k).residueField ((identityNormalConeIso k).hom.base default))
        ((identityNormalCone k).residueField default) := φ.hom.toAlgebra
    change Module.finrank
      ((pointScheme k).residueField ((identityNormalConeIso k).hom.base default))
      ((identityNormalCone k).residueField default) = 1
    apply Module.finrank_of_bijective_algebraMap
    change Function.Bijective φ
    exact ConcreteCategory.bijective_of_isIso φ
  have hsource : (identityNormalCone k).fundamentalCycle
      (default : identityNormalCone k) = 1 :=
    (identityNormalCone k).fundamentalCycle_apply_of_isMax_of_isReduced default hxmax
  have htarget : (PointChow.fundamentalCycle k : AlgebraicCycle (pointScheme k) ℚ)
      ((identityNormalConeIso k).hom.base default) = 1 := by
    rw [show (identityNormalConeIso k).hom.base default =
      (default : pointScheme k) from Subsingleton.elim _ _]
    exact PointChow.fundamentalCycle_apply k
  subst y
  simp [_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff, hdegree, hsource, htarget]

/-- Chow class of the actual pushed-forward Rees-cone cycle. -/
noncomputable def resolvedConeClass :
    (PointChow.grading k).group (resolutionRankF₀ k : ℤ) :=
  (PointChow.grading k (resolutionRankF₀ k : ℤ)).quotientMap
    (resolvedConeCycle k)

/-- Consequently the cone class used by the resolved formula is the quotient of the ordinary
fundamental cycle, rather than an independently supplied Chow class. -/
theorem resolvedConeClass_eq :
    RationalChowGrading.cast
        (congrArg (fun n : ℕ ↦ (n : ℤ)) (resolvedCone_rankF₀_eq_zero k))
        (resolvedConeClass k) =
      fundamentalClass k := by
  rw [resolvedConeClass, RationalChowGrading.cast_quotientMap]
  unfold fundamentalClass
  apply congrArg (PointChow.rationalEquivalence k 0).quotientMap
  apply Subtype.ext
  rw [RationalChowGrading.coe_cyclesCast]
  exact resolvedConeCycle_eq k

theorem resolvedConeVirtualRank_add_rankF₁ :
    resolvedConeVirtualRank k + (resolutionRankF₁ k : ℤ) =
      (resolutionRankF₀ k : ℤ) := by
  simp [resolvedConeVirtualRank]

/-- The cone class reindexed to the source degree of the constructed rank-zero Gysin map. -/
noncomputable def resolvedConeClassAtGysinDegree :
    (PointChow.grading k).group
      (resolvedConeVirtualRank k + resolutionRankF₁ k) :=
  RationalChowGrading.cast (resolvedConeVirtualRank_add_rankF₁ k).symm
    (resolvedConeClass k)

/-- The resolved-cone formula before transporting its proved-zero virtual rank to degree zero. -/
noncomputable def resolvedConeVirtualClass :
    (PointChow.grading k).group (resolvedConeVirtualRank k) :=
  resolutionZeroBundleGysin k (resolvedConeVirtualRank k)
    (resolvedConeClassAtGysinDegree k)

/-- The virtual class of the smooth point, evaluated through the concrete resolved-cone
pipeline. -/
noncomputable def virtualClass : (PointChow.grading k).group 0 :=
  RationalChowGrading.cast (resolvedCone_virtualRank_eq_zero k)
    (resolvedConeVirtualClass k)

/-- On the proper smooth point, the rank-zero virtual class is the ordinary fundamental class. -/
theorem virtualClass_eq_fundamentalClass :
    virtualClass k = fundamentalClass k := by
  simp only [virtualClass, resolvedConeVirtualClass,
    resolvedConeClassAtGysinDegree]
  rw [resolutionZeroBundle_zeroGysin]
  rw [RationalChowGrading.cast_cast, RationalChowGrading.cast_cast]
  rw [resolvedConeClass_eq]

/-- The point scheme is proper over itself; this is the concrete proper example used by the
virtual/fundamental comparison. -/
theorem proper_over_self :
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u})
      (𝟙 (pointScheme k)) := by
  infer_instance

/-- The virtual class of the proper point has degree one. -/
@[simp]
theorem virtualClass_degree_one :
    PointChow.chowEquivRat k (virtualClass k) = 1 := by
  rw [virtualClass_eq_fundamentalClass]
  exact PointChow.fundamentalClass_degree_one k

end ProperPoint

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
