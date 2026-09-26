/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.IndependenceAcyclic
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.OverField
import GromovWitten.AlgebraicGeometry.Cones.NormalConeRegular

/-!
# The lci formula `[X]^vir = [X]`

Behrend--Fantechi, Proposition 5.? (the local complete intersection case): if `X = Spec (R ⧸ I)`
is cut out inside a smooth (or merely regular-sequence) presentation by a quasi-regular ideal
`I`, then the *identity* obstruction theory `φ = id : L ⟶ L`, `L = conormalComplex k R I`, has
virtual class equal to the ordinary fundamental class of `X`.  Geometrically: quasi-regularity of
`I` forces the normal cone `C` of `X` to equal the normal sheaf `N = Spec Sym(I/I²)`
(`Cones/NormalConeRegular.lean`), so the resolved cone `C(E) ⊆ E₁ = N` of
`VirtualFundamentalClass/ResolvedCone.lean` is *all* of `E₁`, exactly as in the rank-zero case of
`Construction.lean` but now for a possibly nonzero obstruction bundle.

The smooth case (`X` smooth over `k`) will follow once "smooth ⇒ quasi-regular" is available
(tracked as issue #64 in the survey `vfc_formulas.md`; not attempted here).

## Main declarations

* `lciHom`: the identity obstruction theory on `conormalComplex k R I`.
* `bundleAugmentation`: the augmentation `gr_I(R) ⊗ Sym(E⁰) →ₐ[R⧸I] gr_I(R)` killing the
  positive-degree part of `Sym(E⁰)`.
* `productMap_comp_augmentation`: composing `productMap lciHom` with `bundleAugmentation` agrees
  with `AffineNormalCone.normalSheafCoordinateMap R I` (the comparison map used to state
  quasi-regularity, `Cones/NormalConeRegular.lean`).
* `ideal_eq_bot_of_injective`, `isIso_toBundle_of_injective`: quasi-regularity of `I` forces
  `C(E) = E₁`.
* `flatPullbackBundle_fundamental_eq_resolvedConeCycle_of_injective`: the flat pullback of the
  fundamental cycle of `X` to `E₁` is the resolved-cone cycle.
* `virtualClass_eq_fundamental_of_injective`, `lci_formula`: the virtual class of the identity
  obstruction theory is the class of the fundamental cycle of `X`.

## What is left as an explicit hypothesis

The ambient machinery of `Construction.lean` already carries the two explicit hypotheses `hhom`
(homogeneity of principal divisors) and `hinj` (injectivity of `π^*`, Fulton's homotopy-invariance
Thm 3.3(a), not proved in this development).  Beyond those, `lci_formula` also takes an explicit
purity hypothesis `hpureX` on the chosen `DimensionFunction` of `X` (every generic point of `X`
has the expected dimension), matching how `Construction.lean` itself only proves purity of the
resolved cone from purity of the base.  `Module.Free`/`Module.Finite` of `I.Cotangent` over
`R ⧸ I` are also explicit hypotheses, as they already are throughout `Construction.lean`.
-/

universe u

-- Matches `Construction.lean`/`ResolvedCone.lean`: the coordinate ring of `C ×_X E₀` needs one
-- more level of pending instance search than the default to synthesise `CommRing`.
set_option maxSynthPendingDepth 5

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.VirtualClass

open IntersectionTheory hiding Scheme AlgebraicCycle
open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable (k : Type u) [CommRing k] {R : Type u} [CommRing R] [Algebra k R] (I : Ideal R)

/-! ## The identity obstruction theory -/

/-- **The lci obstruction theory**: the identity chain map on the conormal complex
`L = conormalComplex k R I`.  Its resolved cone realises Behrend--Fantechi's comparison of the
normal cone with the normal sheaf. -/
noncomputable abbrev lciHom :
    LinearTwoTermComplex.Hom (conormalComplex k R I) (conormalComplex k R I) :=
  LinearTwoTermComplex.Hom.id (conormalComplex k R I)

/-! ## Step 1: the augmented product map is the normal-sheaf comparison map -/

/-- The augmentation `gr_I(R) ⊗ Sym(E⁰) →ₐ[R⧸I] gr_I(R)` killing the positive-degree part of
`Sym(E⁰)`: the vertex of the bundle `E₀`. -/
noncomputable def bundleAugmentation :
    ResolvedCone.productRing (lciHom k I) →ₐ[R ⧸ I]
      AffineNormalCone.associatedGradedRing R I :=
  Algebra.TensorProduct.lift (AlgHom.id (R ⧸ I) (AffineNormalCone.associatedGradedRing R I))
    ((Algebra.ofId (R ⧸ I) (AffineNormalCone.associatedGradedRing R I)).comp
      (SymmetricAlgebra.lift (0 : (conormalComplex k R I).degreeOne →ₗ[R ⧸ I] R ⧸ I)))
    (fun _ _ => Commute.all _ _)

/-- **Step 1.** Composing `productMap lciHom` with the augmentation `bundleAugmentation` agrees
with the canonical normal-sheaf comparison map `AffineNormalCone.normalSheafCoordinateMap R I`,
under the identification `bundleRing lciHom = Sym(I/I²) = normalSheafCoordinateRing R I`. -/
theorem productMap_comp_augmentation (w : ResolvedCone.bundleRing (lciHom k I)) :
    bundleAugmentation k I (ResolvedCone.productMap (lciHom k I) w) =
      AffineNormalCone.normalSheafCoordinateMap R I w := by
  induction w using SymmetricAlgebra.induction with
  | algebraMap r =>
      rw [AlgHom.commutes, AlgHom.commutes, AffineNormalCone.normalSheafCoordinateMap_base]
      rfl
  | ι x =>
      rw [ResolvedCone.productMap_ι, AffineNormalCone.normalSheafCoordinateMap_ι, map_add,
        show (lciHom k I).degreeZero x = x from rfl]
      have h1 : bundleAugmentation k I
          (AffineNormalCone.conormalToAssociatedGraded R I x ⊗ₜ[R ⧸ I] (1 : _)) =
            AffineNormalCone.conormalToAssociatedGraded R I x := by
        rw [bundleAugmentation, Algebra.TensorProduct.lift_tmul]
        simp
      have h2 : bundleAugmentation k I
          ((1 : AffineNormalCone.associatedGradedRing R I) ⊗ₜ[R ⧸ I]
            SymmetricAlgebra.ι (R ⧸ I) (conormalComplex k R I).degreeOne
              ((conormalComplex k R I).differential x)) = 0 := by
        rw [bundleAugmentation, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
          SymmetricAlgebra.lift_ι_apply]
        simp
      rw [h1, h2, add_zero]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-! ## Steps 2-3: `C(E) = E₁` -/

/-- **Step 2, first half.** If the normal-sheaf comparison map is injective then so is
`productMap lciHom`. -/
theorem productMap_injective_of_normalSheafCoordinateMap_injective
    (hinj : Function.Injective (AffineNormalCone.normalSheafCoordinateMap R I)) :
    Function.Injective (ResolvedCone.productMap (lciHom k I)) := by
  intro a b hab
  apply hinj
  rw [← productMap_comp_augmentation, ← productMap_comp_augmentation, hab]

/-- **Step 2.** Quasi-regularity of `I` (injectivity of the normal-sheaf comparison map) forces
the ideal of the resolved cone to vanish: `C(E) = E₁`. -/
theorem ideal_eq_bot_of_injective
    (hinj : Function.Injective (AffineNormalCone.normalSheafCoordinateMap R I)) :
    ResolvedCone.ideal (lciHom k I) = ⊥ := by
  have hpi := productMap_injective_of_normalSheafCoordinateMap_injective k I hinj
  rw [eq_bot_iff]
  intro a ha
  have h0 : ResolvedCone.productMap (lciHom k I) a = 0 := ha
  rw [Ideal.mem_bot]
  exact hpi (by rw [h0, map_zero])

/-- In the quasi-regular case the quotient map defining the resolved cone is bijective. -/
theorem quotientMk_ideal_bijective_of_injective
    (hinj : Function.Injective (AffineNormalCone.normalSheafCoordinateMap R I)) :
    Function.Bijective (Ideal.Quotient.mk (ResolvedCone.ideal (lciHom k I))) := by
  refine ⟨?_, Ideal.Quotient.mk_surjective⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ideal_eq_bot_of_injective k I hinj] at ha
  exact ha

/-- **Step 3.** In the quasi-regular case the closed immersion `C(E) ↪ E₁` is an isomorphism:
the resolved cone is the whole bundle `E₁`. -/
theorem isIso_toBundle_of_injective
    (hinj : Function.Injective (AffineNormalCone.normalSheafCoordinateMap R I)) :
    IsIso (ResolvedCone.toBundle (lciHom k I)) := by
  have hiso : IsIso (CommRingCat.ofHom
      (Ideal.Quotient.mk (ResolvedCone.ideal (lciHom k I)))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (quotientMk_ideal_bijective_of_injective k I hinj)
  exact inferInstanceAs (IsIso (Spec.map _))

variable [IsNoetherianRing R] [Module.Free (R ⧸ I) I.Cotangent] [Module.Finite (R ⧸ I) I.Cotangent]

/-! ## Steps 4-5: the flat pullback of the fundamental cycle of `X` is the resolved-cone cycle -/

/-- **Steps 4-5.** The flat pullback of the fundamental cycle of `X = Spec (R ⧸ I)` along the
projection of the bundle `E₁` is the resolved-cone cycle.  Quasi-regularity of `I` identifies
`C(E) ≅ E₁` (`isIso_toBundle_of_injective`), so the fundamental cycle of `C(E)` transports, along
this isomorphism, to the fundamental cycle of `E₁` (`map_fundamentalCycle_of_isIso`); on the
other hand the fundamental cycle of `E₁` is, unconditionally, the flat pullback of the
fundamental cycle of `X` (`pullbackBundle_fundamentalCycle`).  No purity hypothesis on `E₁`
itself is needed: it is automatically supplied by the membership proof of
`cyclesOfDimension.flatPullbackBundle`, which already shows that the flat pullback of a
dimension-`vd` graded cycle is graded in dimension `vd + a`. -/
theorem flatPullbackBundle_fundamental_eq_resolvedConeCycle_of_injective
    (hinj : Function.Injective (AffineNormalCone.normalSheafCoordinateMap R I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (lciHom k I)))
    (hpureX : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p →
      dimX p = virtualDimension (lciHom k I)) :
    cyclesOfDimension.flatPullbackBundle (trivialization (lciHom k I)) dimX dimE
        (virtualDimension (lciHom k I)) (cyclesOfDimension.fundamental hpureX) =
      resolvedConeCycle (lciHom k I) dimE := by
  have hiso : IsIso (ResolvedCone.toBundle (lciHom k I)) := isIso_toBundle_of_injective k I hinj
  set z := cyclesOfDimension.flatPullbackBundle (trivialization (lciHom k I)) dimX dimE
    (virtualDimension (lciHom k I)) (cyclesOfDimension.fundamental hpureX) with hz
  have hzcoe : (z : AlgebraicCycle (ResolvedCone.bundleSpace (lciHom k I)) ℚ) =
      (ResolvedCone.bundleSpace (lciHom k I)).fundamentalCycle := by
    rw [hz, flatPullbackBundle_coe]
    exact pullbackBundle_fundamentalCycle (trivialization (lciHom k I))
  have hmap : AlgebraicCycle.map (ResolvedCone.toBundle (lciHom k I))
      (coneDimension (lciHom k I) dimE) dimE
      (ResolvedCone.scheme (lciHom k I)).fundamentalCycle =
      (ResolvedCone.bundleSpace (lciHom k I)).fundamentalCycle :=
    map_fundamentalCycle_of_isIso (asIso (ResolvedCone.toBundle (lciHom k I)))
      (coneDimension (lciHom k I) dimE) dimE
  rw [resolvedConeCycle, hmap, ← hzcoe, cyclesOfDimension.project_coe]

/-! ## Step 6: the virtual class is the fundamental class -/

/-- **Step 6.** In the setting of `Construction.lean` (with its explicit hypotheses `hhom`,
`hinj`, dimension functions and rational-equivalence systems), the virtual class of the identity
obstruction theory on `X = Spec (R ⧸ I)` is the class of the fundamental cycle of `X`, provided
`I` is quasi-regular (injectivity of the normal-sheaf comparison map) and the chosen dimension
function `dimX` of `X` is pure of the expected dimension `hpureX`. -/
theorem virtualClass_eq_fundamental_of_injective
    (hinj : Function.Injective (AffineNormalCone.normalSheafCoordinateMap R I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (lciHom k I)))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (virtualDimension (lciHom k I)))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace (lciHom k I)) dimE
      (coneDegree (lciHom k I)))
    (hpureX : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p →
      dimX p = virtualDimension (lciHom k I))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace (lciHom k I)) dimE)
    (hinj' : Function.Injective (bundlePullback (lciHom k I) dimX dimE RX RE)) :
    virtualClass (lciHom k I) dimX dimE RX RE hhom hinj' =
      RX.quotientMap (cyclesOfDimension.fundamental hpureX) := by
  symm
  refine eq_virtualClass_of_pullback_eq (lciHom k I) dimX dimE RX RE hhom hinj' _ ?_
  rw [bundlePullback, VectorBundle.chowPullbackBundle_quotientMap,
    flatPullbackBundle_fundamental_eq_resolvedConeCycle_of_injective k I hinj dimX dimE hpureX]
  rfl

/-! ## Step 7-8: packaging with quasi-regular generators -/

/-- **The lci formula** (Behrend--Fantechi, Prop. 5.?): if `I` is generated by a finite
quasi-regular sequence (`x`), the virtual fundamental class of the identity ("lci") obstruction
theory `φ = id : conormalComplex k R I ⟶ conormalComplex k R I` on `X = Spec (R ⧸ I)` is the
class of the fundamental cycle of `X`.

The two hypotheses `hhom`/`hinj'` inherited from `Construction.lean` are not discharged here (see
that file's module docstring); the purity hypothesis `hpureX` records that the chosen dimension
function of `X` takes the expected value `vd = rk Ω - rk I/I²` on every generic point of `X` —
this is the "`dim X = rank Ω - rank I/I²`" bookkeeping mentioned in the survey, left explicit
rather than derived.  The smooth case (`X` smooth over `k`, so that `I` is automatically
quasi-regular) is issue #64 and is not attempted here: it needs "smooth ⇒ quasi-regular", which
would come from Mathlib's `IsStandardSmooth.subsingleton_h1Cotangent`/freeness of `Ω` wired
through `AffineNormalCone.QuasiregularGenerators`, and is not present in this development. -/
theorem lci_formula (x : AffineNormalCone.QuasiregularGenerators R I)
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (lciHom k I)))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (virtualDimension (lciHom k I)))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace (lciHom k I)) dimE
      (coneDegree (lciHom k I)))
    (hpureX : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p →
      dimX p = virtualDimension (lciHom k I))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace (lciHom k I)) dimE)
    (hinj' : Function.Injective (bundlePullback (lciHom k I) dimX dimE RX RE)) :
    virtualClass (lciHom k I) dimX dimE RX RE hhom hinj' =
      RX.quotientMap (cyclesOfDimension.fundamental hpureX) :=
  virtualClass_eq_fundamental_of_injective k I x.normalSheafCoordinateMap_injective dimX dimE RX
    RE hpureX hhom hinj'

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.VirtualClass

/-! ## Step 7: the unconditional lci formula over an infinite field -/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.OverField

open IntersectionTheory hiding Scheme AlgebraicCycle
open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable (k : Type u) [Field k] [Infinite k] {R : Type u} [CommRing R] [Algebra k R]
  [Algebra.FiniteType k R] [IsNoetherianRing R] (I : Ideal R) [Nontrivial (R ⧸ I)]
  [Module.Free (R ⧸ I) I.Cotangent] [Module.Finite (R ⧸ I) I.Cotangent]

/-- **Step 7.** The unconditional form of `VirtualClass.virtualClass_eq_fundamental_of_injective`:
over an infinite field `k`, with `R` finitely generated over `k` and `X = Spec (R ⧸ I)` nonempty,
the hypotheses `hhom`/`hinj'` of `Construction.lean` are automatic (`OverField.lean`), so only
quasi-regularity of `I` and purity of the chosen dimension function of `X` remain. -/
theorem virtualClass_eq_fundamental_of_injective
    (hinj : Function.Injective (AffineNormalCone.normalSheafCoordinateMap R I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (VirtualClass.lciHom k I)))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (VirtualClass.virtualDimension (VirtualClass.lciHom k I)))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace (VirtualClass.lciHom k I)) dimE
      (VirtualClass.coneDegree (VirtualClass.lciHom k I)))
    (hpureX : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p →
      dimX p = VirtualClass.virtualDimension (VirtualClass.lciHom k I)) :
    virtualClass (VirtualClass.lciHom k I) dimX dimE RX RE =
      RX.quotientMap (cyclesOfDimension.fundamental hpureX) := by
  symm
  refine eq_virtualClass_of_pullback_eq (VirtualClass.lciHom k I) dimX dimE RX RE _ ?_
  rw [VirtualClass.bundlePullback, VectorBundle.chowPullbackBundle_quotientMap,
    VirtualClass.flatPullbackBundle_fundamental_eq_resolvedConeCycle_of_injective k I hinj dimX
      dimE hpureX]
  rfl

/-- **The unconditional lci formula.**  Over an infinite field `k`, with `R` finitely generated
over `k`, `X = Spec (R ⧸ I)` nonempty and `I` generated by a finite quasi-regular sequence `x`,
the virtual fundamental class of the identity ("lci") obstruction theory on `X` is the class of
the fundamental cycle of `X`, with no hypothesis beyond quasi-regularity and purity of the
chosen dimension function of `X`. -/
theorem lci_formula (x : AffineNormalCone.QuasiregularGenerators R I)
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (VirtualClass.lciHom k I)))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (VirtualClass.virtualDimension (VirtualClass.lciHom k I)))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace (VirtualClass.lciHom k I)) dimE
      (VirtualClass.coneDegree (VirtualClass.lciHom k I)))
    (hpureX : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p →
      dimX p = VirtualClass.virtualDimension (VirtualClass.lciHom k I)) :
    virtualClass (VirtualClass.lciHom k I) dimX dimE RX RE =
      RX.quotientMap (cyclesOfDimension.fundamental hpureX) :=
  virtualClass_eq_fundamental_of_injective k I x.normalSheafCoordinateMap_injective dimX dimE RX
    RE hpureX

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.OverField
