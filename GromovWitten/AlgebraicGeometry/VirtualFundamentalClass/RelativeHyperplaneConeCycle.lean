/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneConeIdentity
import GromovWitten.AlgebraicGeometry.IntersectionTheory.CycleGluing

/-!
# The cycle of the resolved cone of a hyperplane base change

`VirtualFundamentalClass/RelativeHyperplaneConeIdentity.lean` proves the ideal identity of issue
#75: for a relative obstruction datum `φ : E ⟶ L_{X/Y}` over `Y = 𝔸^{Option τ'}`, for the
hyperplane `Y' = 𝔸^{τ'} = {y₀ = 0} ⊆ Y` and for `X' = X ×_Y Y'`, the resolved cone of the
base-changed datum `ψ = reindexHom I φ` is the scheme-theoretic intersection of the resolved cone
of `φ` with the divisor `y₀ = 0` of the bundle `E₁`, provided `y₀` is a non-zero-divisor on every
`R ⧸ Iⁿ` (`RegularOnPowers`) and the resolved cone is transversal to the hyperplane
(`ResolvedConeTransversal`).

This file upgrades that identity to a statement about *cycles*.  The resolved cone of `ψ` lives in
the smaller bundle `E₁ ×_X X'`, so the comparison needs the pushforward of cycles along the closed
immersion `E₁ ×_X X' ↪ E₁`, which on coordinate rings is the scalar extension
`Sym_{Base I}(E⁰) → Sym_{Base J}(Base J ⊗ E⁰)`.  The main theorem
`map_relConeCycle_reindexHom` says that the pushforward of the resolved-cone cycle of `ψ` is the
cycle of the hyperplane section of the resolved cone of `φ`.

## Main definitions

* `hyperplaneBundleImmersion I M`: the closed immersion `Spec Sym_{Base J}(Base J ⊗ M) ↪
  Spec Sym_{Base I}(M)` of the bundle over the hyperplane section into the bundle.
* `quotientComapEquiv g hg K`: for a surjective ring homomorphism `g : A →+* B`, the isomorphism
  `A ⧸ comap g K ≃+* B ⧸ K`.

## Main results

The general cycle-theoretic input, for arbitrary schemes:

* `map_project_of_isClosedImmersion`: the pushforward along a closed immersion commutes with the
  projection onto the dimension-`d` part.  (The other cycle lemmas used below are already available:
  `VirtualClass.map_fundamentalCycle_of_isIso`, `VirtualClass.map_congr_hom` and
  `VirtualClass.map_comp_closedImmersion` of `VirtualFundamentalClass/Independence.lean`.)
* `map_quotientCycle_of_surjective`: **for a surjective ring homomorphism `g : A →+* B` and an
  ideal `K` of `B`, the pushforward of the cycle of `Spec (B ⧸ K)` along the closed immersion
  `Spec B ↪ Spec A` is the cycle of the closed subscheme of `Spec A` cut out by `comap g K`.**
* `properPushforward_quotientCycle_of_surjective`,
  `closedImmersionPushforward_quotientCycle_of_surjective`: the same identity for the proper
  pushforward on dimension-`d` cycles and on rational Chow groups.

The consequences for the hyperplane base change:

* `isNoetherianRing_symmetricAlgebra_reindex`: the coordinate ring of the bundle over the
  hyperplane section is Noetherian whenever that of the bundle is.
* `isSMulRegular_quotient_ideal'_symHyperplaneCoord`: under `RegularOnPowers I y₀` and for a free
  bundle `E₀`, the equation `y₀` is a non-zero-divisor on the coordinate ring of the resolved cone,
  i.e. **the divisor `y₀ = 0` meets the resolved cone properly**.
* `coneDegree_absHom_reindexHom`: the resolved-cone cycle of the base-changed datum lives in
  degree one less than that of `φ`.
* `map_quotientCycle_ideal'_reindexHom`, **`map_relConeCycle_reindexHom`**: the pushforward of the
  cycle of the resolved cone of `reindexHom I φ` into the bundle `E₁` over `X` is the cycle of the
  scheme-theoretic intersection of the resolved cone of `φ` with the divisor `y₀ = 0`.
* `map_relConeCycle_reindexHom_comap`: the unconditional form of the pushforward, with the preimage
  of `ideal' (reindexHom I φ)` on the right-hand side; `map_relConeCycle_reindexHom_of_flat`: the
  form in which transversality is replaced by flatness of the cokernel.
* `map_resolvedConeCycleAt_absHom_reindexHom`: the same statement for the resolved-cone cycle of
  the associated absolute obstruction datum.
* `properPushforward_relConeCycle_reindexHom`,
  `closedImmersionPushforward_relConeClass_reindexHom`: the same identity inside the group of
  dimension-`d` cycles, and on rational Chow groups.

Non-vacuity of the hypotheses of `RelativeHyperplaneConeIdentity.lean`:

* `isLeftRegular_mvPolynomial_X`, `surjective_algebraMap_symmetricAlgebra_of_subsingleton`,
  `surjective_algebraMap_tensorProduct`, `surjective_algebraMap_associatedGradedRing_bot`: the
  ring-theoretic inputs.
* `resolvedConeTransversal_of_eq_bot`, `regularOnPowers_of_eq_bot`: **for `I = ⊥` — that is, for
  `X = 𝔸^{σ ⊔ Option τ'}` the whole affine space, whose hyperplane section
  `X' = 𝔸^{σ ⊔ τ'}` is nonempty — and for an obstruction complex with vanishing degree-one term,
  both hypotheses of the resolved-cone identity are theorems**, the coordinate-ring map of the
  resolved cone being surjective (`surjective_relProductMap_of_eq_bot`).  Hence
  `ideal'_reindexHom_of_eq_bot` and `map_relConeCycle_reindexHom_of_eq_bot`: the ideal identity and
  the cycle comparison hold unconditionally in that case.

## What the Gysin comparison still needs

The expected statement `relativeVirtualClass (reindexHom I φ) = i^! (relativeVirtualClass φ)` for
the regular embedding `i : Y' ↪ Y` of the hyperplane cannot be *stated* with the present Chow-level
API, let alone proved: `IntersectionTheory/PrincipalGysin.lean` constructs the Gysin operation of a
principal Cartier divisor only on cycles (`PrincipalGysin.map`, `PrincipalGysin.gradedMap`), and its
module docstring records that the descent of that operation to rational equivalence is not
available.  Concretely, three inputs are missing.

1. A `RationalEquivalenceSystem.DescendingMap` for `PrincipalGysin.map`, i.e. the statement that
   the divisor operation carries rationally trivial cycles to rationally trivial cycles (the local
   order identity, with its tame-symbol correction, named in `PrincipalGysin.lean`).
2. The multiplicity identity comparing the *scheme-theoretic* intersection cycle computed here with
   the divisor operation: for `f : A` a non-zero-divisor on `A ⧸ K`,
   `HomotopyInvariance.quotientCycle (K ⊔ Ideal.span {f}) dim d` should be the pushforward along
   `Spec (A ⧸ (f)) ↪ Spec A` of `PrincipalGysin.map f dim (HomotopyInvariance.quotientCycle K dim
   (d + 1))`.  This is the length identity `ord_W(f) = length ((A ⧸ K)_W ⧸ f)` of Fulton A.3; the
   properness hypothesis it needs is proved here for the case at hand
   (`isSMulRegular_quotient_ideal'_symHyperplaneCoord`), and the pushforward step is
   `map_quotientCycle_of_surjective`.
3. The compatibility of the divisor operation on the bundle `E₁` with the zero-section Gysin map
   `VectorBundle.zeroSectionGysin'` used to define `RelativeAbsolute.relativeVirtualClass`.

Everything above item 2 that lives on cycles of `E₁` is proved in this file:
`closedImmersionPushforward_relConeClass_reindexHom` is the identity of Chow classes on `E₁` that
the comparison of relative virtual classes will consume.
-/

universe u

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneCone

/-! ## Pushforward of cycles along closed immersions -/

section Pushforward

open CategoryTheory
open _root_.AlgebraicGeometry (IsClosedImmersion)
open IntersectionTheory hiding Scheme AlgebraicCycle

variable {X Y : _root_.AlgebraicGeometry.Scheme.{u}}

/-- **Pushforward along a closed immersion commutes with the projection onto the dimension-`d`
part**, because the two certified gradings agree along a closed immersion. -/
theorem map_project_of_isClosedImmersion (f : X ⟶ Y) [IsClosedImmersion f]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (d : ℤ)
    (c : _root_.AlgebraicGeometry.AlgebraicCycle X ℚ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY
        (cyclesOfDimension.project (dimension := dimX) (i := d) c) =
      (cyclesOfDimension.project (dimension := dimY) (i := d)
        (_root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY c) :
          _root_.AlgebraicGeometry.AlgebraicCycle Y ℚ) := by
  have hdim : (dimX : X → ℤ) = fun x => (dimY : Y → ℤ) (f.base x) :=
    funext fun x => DimensionFunction.apply_eq_of_isClosedImmersion dimX dimY f x
  apply Function.locallyFinsuppWithin.ext
  intro y
  by_cases hy : y ∈ Set.range f.base
  · obtain ⟨x, rfl⟩ := hy
    have hL : _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY
        (cyclesOfDimension.project (dimension := dimX) (i := d) c :
          _root_.AlgebraicGeometry.AlgebraicCycle X ℚ) (f.base x) =
        (cyclesOfDimension.project (dimension := dimX) (i := d) c :
          _root_.AlgebraicGeometry.AlgebraicCycle X ℚ) x := by
      rw [hdim]
      exact AlgebraicCycle.map_closedImmersion_apply_image f (dimY : Y → ℤ) _ x
    have hR : _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY c (f.base x) = c x := by
      rw [hdim]
      exact AlgebraicCycle.map_closedImmersion_apply_image f (dimY : Y → ℤ) c x
    rw [hL, cyclesOfDimension.project_apply, cyclesOfDimension.project_apply, hR,
      DimensionFunction.apply_eq_of_isClosedImmersion dimX dimY f x]
  · have hL : _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY
        (cyclesOfDimension.project (dimension := dimX) (i := d) c :
          _root_.AlgebraicGeometry.AlgebraicCycle X ℚ) y = 0 := by
      rw [hdim]
      exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range f (dimY : Y → ℤ) _ y hy
    have hR : _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY c y = 0 := by
      rw [hdim]
      exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range f (dimY : Y → ℤ) c y hy
    rw [hL, cyclesOfDimension.project_apply, hR, ite_self]

end Pushforward

/-! ## The cycle of a closed subscheme under a surjection of rings -/

section QuotientCycle

open CategoryTheory
open _root_.AlgebraicGeometry (Spec IsClosedImmersion isIso_SpecMap_iff)
open IntersectionTheory hiding Scheme AlgebraicCycle
open HomotopyInvariance (quotientImmersion quotientCycle)

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The kernel of `A → B → B ⧸ K` is the preimage of `K`. -/
theorem ker_mk_comp (g : A →+* B) (K : Ideal B) :
    RingHom.ker ((Ideal.Quotient.mk K).comp g) = Ideal.comap g K := by
  refine Ideal.ext fun a => ?_
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]

/-- **For a surjective ring homomorphism `g : A →+* B` and an ideal `K` of `B`, the quotient of `A`
by the preimage of `K` is the quotient of `B` by `K`.**  Geometrically: a closed subscheme of a
closed subscheme of `Spec A` is a closed subscheme of `Spec A`. -/
noncomputable def quotientComapEquiv (g : A →+* B) (hg : Function.Surjective g) (K : Ideal B) :
    (A ⧸ Ideal.comap g K) ≃+* (B ⧸ K) :=
  (Ideal.quotEquivOfEq (ker_mk_comp g K).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk K).comp g)
      (Ideal.Quotient.mk_surjective.comp hg))

@[simp]
theorem quotientComapEquiv_mk (g : A →+* B) (hg : Function.Surjective g) (K : Ideal B) (a : A) :
    quotientComapEquiv g hg K (Ideal.Quotient.mk (Ideal.comap g K) a) =
      Ideal.Quotient.mk K (g a) := by
  rw [quotientComapEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- The defining formula for the cycle of a closed subscheme of an affine scheme. -/
theorem quotientCycle_eq (J : Ideal A) (dim : DimensionFunction (Spec (CommRingCat.of A)))
    (d : ℤ) :
    (quotientCycle J dim d :
        _root_.AlgebraicGeometry.AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) =
      (cyclesOfDimension.project (dimension := dim) (i := d)
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (quotientImmersion J)
          (DimensionFunction.comapClosedImmersion (quotientImmersion J) dim) dim
          (Spec (CommRingCat.of (A ⧸ J))).fundamentalCycle) :
        _root_.AlgebraicGeometry.AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) :=
  rfl

/-- **The cycle of a closed subscheme pushes forward along a surjection of rings.**  If
`g : A →+* B` is surjective, so that `Spec B ↪ Spec A` is a closed immersion, the pushforward of
the cycle of the closed subscheme `Spec (B ⧸ K) ⊆ Spec B` is the cycle of the closed subscheme of
`Spec A` cut out by the preimage of `K`.

The proof compares the two closed immersions `Spec (B ⧸ K) ↪ Spec B ↪ Spec A` and
`Spec (A ⧸ comap g K) ↪ Spec A` through the isomorphism `quotientComapEquiv`. -/
theorem map_quotientCycle_of_surjective (g : A →+* B) (hg : Function.Surjective g) (K : Ideal B)
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (dimB : DimensionFunction (Spec (CommRingCat.of B))) (d : ℤ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map (Spec.map (CommRingCat.ofHom g)) dimB dimA
        (quotientCycle K dimB d :
          _root_.AlgebraicGeometry.AlgebraicCycle (Spec (CommRingCat.of B)) ℚ) =
      (quotientCycle (Ideal.comap g K) dimA d :
        _root_.AlgebraicGeometry.AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) := by
  have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ hg
  have hquot : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (quotientComapEquiv g hg K).toRingHom)) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
      (quotientComapEquiv g hg K).surjective
  have hiso : IsIso (Spec.map (CommRingCat.ofHom (quotientComapEquiv g hg K).toRingHom)) := by
    rw [isIso_SpecMap_iff]
    exact (quotientComapEquiv g hg K).bijective
  have hring : (Ideal.Quotient.mk K).comp g =
      (quotientComapEquiv g hg K).toRingHom.comp (Ideal.Quotient.mk (Ideal.comap g K)) :=
    RingHom.ext fun a => (quotientComapEquiv_mk g hg K a).symm
  have h1 : Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk K).comp g)) =
      quotientImmersion K ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  have h2 : Spec.map (CommRingCat.ofHom ((quotientComapEquiv g hg K).toRingHom.comp
        (Ideal.Quotient.mk (Ideal.comap g K)))) =
      Spec.map (CommRingCat.ofHom (quotientComapEquiv g hg K).toRingHom) ≫
        quotientImmersion (Ideal.comap g K) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  have hsq : quotientImmersion K ≫ Spec.map (CommRingCat.ofHom g) =
      Spec.map (CommRingCat.ofHom (quotientComapEquiv g hg K).toRingHom) ≫
        quotientImmersion (Ideal.comap g K) := by
    rw [← h1, ← h2, hring]
  have hfc : _root_.AlgebraicGeometry.AlgebraicCycle.map
      (Spec.map (CommRingCat.ofHom (quotientComapEquiv g hg K).toRingHom))
      (DimensionFunction.comapClosedImmersion (quotientImmersion K) dimB)
      (DimensionFunction.comapClosedImmersion (quotientImmersion (Ideal.comap g K)) dimA)
      (Spec (CommRingCat.of (B ⧸ K))).fundamentalCycle =
      (Spec (CommRingCat.of (A ⧸ Ideal.comap g K))).fundamentalCycle :=
    VirtualClass.map_fundamentalCycle_of_isIso
      (asIso (Spec.map (CommRingCat.ofHom (quotientComapEquiv g hg K).toRingHom))) _ _
  rw [quotientCycle_eq, quotientCycle_eq, map_project_of_isClosedImmersion,
    ← VirtualClass.map_comp_closedImmersion (f := quotientImmersion K)
      (g := Spec.map (CommRingCat.ofHom g)) (dY := dimB),
    VirtualClass.map_congr_hom hsq,
    VirtualClass.map_comp_closedImmersion
      (f := Spec.map (CommRingCat.ofHom (quotientComapEquiv g hg K).toRingHom))
      (g := quotientImmersion (Ideal.comap g K))
      (dY := DimensionFunction.comapClosedImmersion (quotientImmersion (Ideal.comap g K)) dimA),
    hfc]

/-- **The graded form of `map_quotientCycle_of_surjective`**: the same identity for the proper
pushforward on dimension-`d` cycles.  The closed-immersion instance is implied by `hg`; it appears
as an instance argument only so that the statement may mention
`cyclesOfDimension.properPushforward`. -/
theorem properPushforward_quotientCycle_of_surjective (g : A →+* B) (hg : Function.Surjective g)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))] (K : Ideal B)
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (dimB : DimensionFunction (Spec (CommRingCat.of B))) (d : ℤ) :
    cyclesOfDimension.properPushforward (dimension := dimB) (dimensionY := dimA) (i := d)
        (Spec.map (CommRingCat.ofHom g)) (quotientCycle K dimB d) =
      quotientCycle (Ideal.comap g K) dimA d :=
  Subtype.ext (map_quotientCycle_of_surjective g hg K dimA dimB d)

/-- **The Chow-level form of `map_quotientCycle_of_surjective`**: the class of a closed subscheme of
`Spec B` pushes forward to the class of the closed subscheme of `Spec A` cut out by the preimage of
its ideal. -/
theorem closedImmersionPushforward_quotientCycle_of_surjective (g : A →+* B)
    (hg : Function.Surjective g) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (K : Ideal B) (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (dimB : DimensionFunction (Spec (CommRingCat.of B))) (d : ℤ)
    (RA : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimA d)
    (RB : RationalEquivalenceSystem (Spec (CommRingCat.of B)) dimB d) :
    RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward RB
        (Spec.map (CommRingCat.ofHom g)) RA (RB.quotientMap (quotientCycle K dimB d)) =
      RA.quotientMap (quotientCycle (Ideal.comap g K) dimA d) :=
  congrArg RA.quotientMap (properPushforward_quotientCycle_of_surjective g hg K dimA dimB d)

end QuotientCycle


/-! ## The resolved cone meets the hyperplane properly -/

section ProperIntersection

open RelativeVirtualClassBaseChange RelativeHyperplaneReindex RelativeAbsolute
open GromovWitten.AlgebraicGeometry.NormalConeAction (Base)
open scoped TensorProduct

-- Tensor products of the associated graded ring with a symmetric algebra need a deeper instance
-- search, exactly as in `RelativeAbsolute.lean`.
set_option maxSynthPendingDepth 5

variable {k : Type u} [CommRing k] {σ τ' : Type u}
variable (I : Ideal (MvPolynomial (σ ⊕ Option τ') k))
variable {E : LinearTwoTermComplex (Base I)}
variable (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))

/-- **The equation of the hyperplane is a non-zero-divisor on the coordinate ring of the resolved
cone**, as soon as it is one on all the powers of `I` and the bundle `E₀` is free.  Geometrically:
no irreducible component of the resolved cone `C(E)` is contained in the divisor `y₀ = 0` of the
bundle `E₁`, i.e. the divisor meets the resolved cone properly.  This is the hypothesis under which
the cycle of the scheme-theoretic intersection computed by `map_relConeCycle_reindexHom` is
expected to agree with the divisor-Gysin image of the cycle of `C(E)`. -/
theorem isSMulRegular_quotient_ideal'_symHyperplaneCoord
    (h : RegularOnPowers I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))
    [Module.Free (Base I) E.degreeOne] :
    IsSMulRegular (SymmetricAlgebra (Base I) E.degreeZero ⧸ ideal' φ)
      (Ideal.Quotient.mk (ideal' φ) (symHyperplaneCoord I E)) := by
  rw [isSMulRegular_quotient_iff]
  intro a ha
  have hreg := isLeftRegular_relProductMap_symHyperplaneCoord I φ h
  have hmem : relProductMap φ (symHyperplaneCoord I E * a) = 0 := mem_ideal'_iff.1 ha
  rw [map_mul] at hmem
  have hmem' : (relProductMap φ).toRingHom (symHyperplaneCoord I E) * relProductMap φ a = 0 :=
    hmem
  refine mem_ideal'_iff.2 (hreg ?_)
  simpa only [mul_zero] using hmem'

end ProperIntersection

/-! ## The cycle of the resolved cone of the hyperplane base change -/

section HyperplaneCycle

open CategoryTheory
open _root_.AlgebraicGeometry (Spec IsClosedImmersion)
open RelativeVirtualClassBaseChange RelativeHyperplaneReindex RelativeAbsolute
open GromovWitten.AlgebraicGeometry.NormalConeAction (Base)
open GradedCone.SymmetricFunctoriality
open IntersectionTheory hiding Scheme AlgebraicCycle
open HomotopyInvariance (quotientCycle)
open scoped TensorProduct

-- Tensor products of the associated graded ring with a symmetric algebra need a deeper instance
-- search, exactly as in `RelativeAbsolute.lean`.
set_option maxSynthPendingDepth 5

variable {k : Type u} [CommRing k] {σ τ' : Type u}
variable (I : Ideal (MvPolynomial (σ ⊕ Option τ') k))

/-- **The closed immersion of the bundle over the hyperplane section into the bundle**: on
coordinate rings it is the scalar extension along `Base I → Base (reindexIdeal I)`, which is
surjective with kernel the equation `y₀` of the hyperplane. -/
noncomputable abbrev hyperplaneBundleImmersion (M : Type u) [AddCommGroup M]
    [Module (Base I) M] :
    Spec (CommRingCat.of (SymmetricAlgebra (Base (reindexIdeal I))
        (Base (reindexIdeal I) ⊗[Base I] M))) ⟶
      Spec (CommRingCat.of (SymmetricAlgebra (Base I) M)) :=
  Spec.map (CommRingCat.ofHom
    (scalarExtensionMap (Base I) (Base (reindexIdeal I)) M).toRingHom)

/-- The bundle over the hyperplane section is a closed subscheme of the bundle. -/
instance hyperplaneBundleImmersion_isClosedImmersion (M : Type u) [AddCommGroup M]
    [Module (Base I) M] : IsClosedImmersion (hyperplaneBundleImmersion I M) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (surjective_scalarExtensionMap_base I M)

/-- **The coordinate ring of the bundle over the hyperplane section is Noetherian** as soon as the
coordinate ring of the bundle is, being a quotient of it by the equation of the hyperplane. -/
theorem isNoetherianRing_symmetricAlgebra_reindex (M : Type u) [AddCommGroup M]
    [Module (Base I) M] [IsNoetherianRing (SymmetricAlgebra (Base I) M)] :
    IsNoetherianRing (SymmetricAlgebra (Base (reindexIdeal I))
      (Base (reindexIdeal I) ⊗[Base I] M)) :=
  isNoetherianRing_of_surjective (SymmetricAlgebra (Base I) M) _
    (scalarExtensionMap (Base I) (Base (reindexIdeal I)) M).toRingHom
    (surjective_scalarExtensionMap_base I M)

variable {E : LinearTwoTermComplex (Base I)}
variable (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))
variable [Fintype σ] [Fintype τ'] [IsNoetherianRing k]
variable [Module.Free (Base I) E.degreeZero] [Module.Finite (Base I) E.degreeZero]
variable [Module.Free (Base (reindexIdeal I)) (Base (reindexIdeal I) ⊗[Base I] E.degreeZero)]
variable [Module.Finite (Base (reindexIdeal I)) (Base (reindexIdeal I) ⊗[Base I] E.degreeZero)]

omit [IsNoetherianRing k] in
/-- **The resolved cone of the base-changed datum has expected codimension one in the resolved
cone of `φ`**: the degree in which the resolved-cone cycle of `reindexHom I φ` lives is one less
than the degree for `φ`.  The virtual dimensions differ by one
(`RelativeHyperplaneReindex.virtualDimension_absHom_reindexHom`) and the two bundles have the same
rank, the base change of a finite free module having the same rank. -/
theorem coneDegree_absHom_reindexHom [Nontrivial (Base I)]
    [Nontrivial (Base (reindexIdeal I))] [Module.Free (Base I) E.degreeOne]
    [Module.Finite (Base I) E.degreeOne] :
    VirtualClass.coneDegree (absHom (reindexHom I φ)) + 1 =
      VirtualClass.coneDegree (absHom φ) := by
  have hv := virtualDimension_absHom_reindexHom I φ
  have hb : (VirtualClass.bundleRank (absHom (reindexHom I φ)) : ℤ) =
      (VirtualClass.bundleRank (absHom φ) : ℤ) := by
    rw [VirtualClass.bundleRank_eq_finrank, VirtualClass.bundleRank_eq_finrank]
    exact_mod_cast Module.finrank_baseChange (R := Base (reindexIdeal I)) (S := Base I)
      (M' := E.degreeZero)
  have h1 : VirtualClass.coneDegree (absHom (reindexHom I φ)) =
      VirtualClass.virtualDimension (absHom (reindexHom I φ)) +
        (VirtualClass.bundleRank (absHom (reindexHom I φ)) : ℤ) := rfl
  have h2 : VirtualClass.coneDegree (absHom φ) =
      VirtualClass.virtualDimension (absHom φ) + (VirtualClass.bundleRank (absHom φ) : ℤ) := rfl
  rw [h1, h2, hb, ← hv]
  ring

/-- **The pushforward of the resolved-cone cycle of the base-changed datum, unconditionally**: with
no hypothesis on `y₀`, the cycle of the resolved cone of `reindexHom I φ` pushes forward to the
cycle of the closed subscheme of the bundle `E₁` cut out by the preimage of
`ideal' (reindexHom I φ)` under the scalar extension.  The hypotheses of
`map_relConeCycle_reindexHom` are exactly what identifies that preimage with `ideal' φ ⊔ (y₀)`,
by `comap_ideal'_reindexHom`. -/
theorem map_relConeCycle_reindexHom_comap
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ)))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace (absHom (reindexHom I φ)))) (d : ℤ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map (hyperplaneBundleImmersion I E.degreeZero)
        dimE' dimE (relConeCycle (reindexHom I φ) dimE' d) =
      (quotientCycle (Ideal.comap
          (scalarExtensionMap (Base I) (Base (reindexIdeal I)) E.degreeZero).toRingHom
          (ideal' (reindexHom I φ))) dimE d :
        _root_.AlgebraicGeometry.AlgebraicCycle (ResolvedCone.bundleSpace (absHom φ)) ℚ) :=
  map_quotientCycle_of_surjective
    (scalarExtensionMap (Base I) (Base (reindexIdeal I)) E.degreeZero).toRingHom
    (surjective_scalarExtensionMap_base I E.degreeZero) (ideal' (reindexHom I φ)) dimE dimE' d

/-- **The cycle of the resolved cone of the base-changed datum, pushed forward into the bundle `E₁`
over `X`, is the cycle of the hyperplane section of the resolved cone of `φ`.**  This is the
cycle-level form of `comap_ideal'_reindexHom`: the ideal of the resolved cone of `reindexHom I φ`
pulls back to `ideal' φ ⊔ (y₀)`, and `map_quotientCycle_of_surjective` turns that identity of
ideals into an identity of cycles on `E₁`. -/
theorem map_quotientCycle_ideal'_reindexHom
    (h : RegularOnPowers I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))
    (htrans : ResolvedConeTransversal I φ)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ)))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace (absHom (reindexHom I φ)))) (d : ℤ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map (hyperplaneBundleImmersion I E.degreeZero)
        dimE' dimE (quotientCycle (ideal' (reindexHom I φ)) dimE' d) =
      (quotientCycle (ideal' φ ⊔ symHyperplaneSpan I E.degreeZero) dimE d :
        _root_.AlgebraicGeometry.AlgebraicCycle (ResolvedCone.bundleSpace (absHom φ)) ℚ) := by
  have hcomap : Ideal.comap
      (scalarExtensionMap (Base I) (Base (reindexIdeal I)) E.degreeZero).toRingHom
      (ideal' (reindexHom I φ)) = ideal' φ ⊔ symHyperplaneSpan I E.degreeZero :=
    comap_ideal'_reindexHom I φ h htrans
  rw [← hcomap]
  exact map_quotientCycle_of_surjective
    (scalarExtensionMap (Base I) (Base (reindexIdeal I)) E.degreeZero).toRingHom
    (surjective_scalarExtensionMap_base I E.degreeZero) (ideal' (reindexHom I φ)) dimE dimE' d

/-- **The cycle-level comparison of resolved cones along a hyperplane.**  Under
`RegularOnPowers I y₀` and transversality of the resolved cone to the hyperplane, the resolved-cone
cycle `[C(E')] ∈ Z_d(E₁ ×_X X')` of the base-changed datum `reindexHom I φ` pushes forward, along
the closed immersion `E₁ ×_X X' ↪ E₁`, to the cycle of the scheme-theoretic intersection of the
resolved cone `C(E)` of `φ` with the divisor `y₀ = 0` of `E₁`. -/
theorem map_relConeCycle_reindexHom
    (h : RegularOnPowers I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))
    (htrans : ResolvedConeTransversal I φ)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ)))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace (absHom (reindexHom I φ)))) (d : ℤ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map (hyperplaneBundleImmersion I E.degreeZero)
        dimE' dimE (relConeCycle (reindexHom I φ) dimE' d) =
      (quotientCycle (ideal' φ ⊔ symHyperplaneSpan I E.degreeZero) dimE d :
        _root_.AlgebraicGeometry.AlgebraicCycle (ResolvedCone.bundleSpace (absHom φ)) ℚ) :=
  map_quotientCycle_ideal'_reindexHom I φ h htrans dimE dimE' d

/-- **The cycle-level comparison of resolved cones along a hyperplane, in the flat case**: if the
cokernel of the coordinate-ring map of the resolved cone is flat over the coordinate ring of `X`,
transversality is automatic (`resolvedConeTransversal_of_flat`), so `RegularOnPowers I y₀` alone
gives the cycle identity. -/
theorem map_relConeCycle_reindexHom_of_flat
    (h : RegularOnPowers I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))
    [Module.Flat (Base I) (relProductRing φ ⧸ LinearMap.range (relProductMap φ).toLinearMap)]
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ)))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace (absHom (reindexHom I φ)))) (d : ℤ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map (hyperplaneBundleImmersion I E.degreeZero)
        dimE' dimE (relConeCycle (reindexHom I φ) dimE' d) =
      (quotientCycle (ideal' φ ⊔ symHyperplaneSpan I E.degreeZero) dimE d :
        _root_.AlgebraicGeometry.AlgebraicCycle (ResolvedCone.bundleSpace (absHom φ)) ℚ) :=
  map_relConeCycle_reindexHom I φ h (resolvedConeTransversal_of_flat I φ h.isSMulRegular)
    dimE dimE' d

/-- **The cycle-level comparison of resolved cones along a hyperplane, for the associated absolute
obstruction data.**  By `RelativeAbsolute.resolvedConeCycleAt_absHom` the resolved-cone cycle of
`absHom (reindexHom I φ)` is the cycle of the resolved cone of the relative datum, so
`map_relConeCycle_reindexHom` applies. -/
theorem map_resolvedConeCycleAt_absHom_reindexHom
    (h : RegularOnPowers I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))
    (htrans : ResolvedConeTransversal I φ)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ)))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace (absHom (reindexHom I φ)))) (d : ℤ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map (hyperplaneBundleImmersion I E.degreeZero)
        dimE' dimE
        (VirtualClass.resolvedConeCycleAt (absHom (reindexHom I φ)) dimE' d) =
      (quotientCycle (ideal' φ ⊔ symHyperplaneSpan I E.degreeZero) dimE d :
        _root_.AlgebraicGeometry.AlgebraicCycle (ResolvedCone.bundleSpace (absHom φ)) ℚ) := by
  rw [resolvedConeCycleAt_absHom (reindexHom I φ) dimE' d]
  exact map_relConeCycle_reindexHom I φ h htrans dimE dimE' d

/-- **The graded form of the cycle comparison**: the same statement inside the group of
dimension-`d` cycles of the bundle `E₁`, for the proper pushforward along the closed immersion
`E₁ ×_X X' ↪ E₁`. -/
theorem properPushforward_relConeCycle_reindexHom
    (h : RegularOnPowers I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))
    (htrans : ResolvedConeTransversal I φ)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ)))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace (absHom (reindexHom I φ)))) (d : ℤ) :
    cyclesOfDimension.properPushforward (dimension := dimE') (dimensionY := dimE) (i := d)
        (hyperplaneBundleImmersion I E.degreeZero)
        (relConeCycle (reindexHom I φ) dimE' d) =
      quotientCycle (ideal' φ ⊔ symHyperplaneSpan I E.degreeZero) dimE d :=
  Subtype.ext (map_relConeCycle_reindexHom I φ h htrans dimE dimE' d)

/-- **The Chow-level comparison of the resolved-cone classes along a hyperplane**: the pushforward
to `A_d(E₁)` of the class of the resolved cone of the base-changed datum is the class of the
hyperplane section of the resolved cone of `φ`.  This is the cycle input for the comparison of the
relative virtual classes; what is still missing for the latter is the divisor-Gysin identity
recorded in the module docstring. -/
theorem closedImmersionPushforward_relConeClass_reindexHom
    (h : RegularOnPowers I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))
    (htrans : ResolvedConeTransversal I φ)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ)))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace (absHom (reindexHom I φ)))) (d : ℤ)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace (absHom φ)) dimE d)
    (RE' : RationalEquivalenceSystem
      (ResolvedCone.bundleSpace (absHom (reindexHom I φ))) dimE' d) :
    RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward RE'
        (hyperplaneBundleImmersion I E.degreeZero) RE
        (RE'.quotientMap (relConeCycle (reindexHom I φ) dimE' d)) =
      RE.quotientMap (quotientCycle (ideal' φ ⊔ symHyperplaneSpan I E.degreeZero) dimE d) :=
  congrArg RE.quotientMap (properPushforward_relConeCycle_reindexHom I φ h htrans dimE dimE' d)

end HyperplaneCycle


/-! ## Non-vacuity: an affine space with vanishing `E⁻¹` -/

section Generators

open AffineNormalCone
open scoped TensorProduct

/-- A coordinate of a polynomial ring is a non-zero-divisor: multiplication by `X s` shifts
coefficients. -/
theorem isLeftRegular_mvPolynomial_X {k : Type u} [CommRing k] {ι : Type u} (s : ι) :
    IsLeftRegular (MvPolynomial.X s : MvPolynomial ι k) := by
  intro p q hpq
  have hpq' : MvPolynomial.X s * p = MvPolynomial.X s * q := hpq
  refine MvPolynomial.ext p q fun m => ?_
  have h := congrArg (MvPolynomial.coeff (Finsupp.single s 1 + m)) hpq'
  rwa [MvPolynomial.coeff_X_mul, MvPolynomial.coeff_X_mul] at h

/-- The symmetric algebra of a trivial module is generated by the scalars. -/
theorem surjective_algebraMap_symmetricAlgebra_of_subsingleton (S : Type u) [CommRing S]
    (M : Type u) [AddCommGroup M] [Module S M] [Subsingleton M] :
    Function.Surjective (algebraMap S (SymmetricAlgebra S M)) := by
  intro z
  induction z using SymmetricAlgebra.induction with
  | algebraMap a => exact ⟨a, rfl⟩
  | ι x =>
      refine ⟨0, ?_⟩
      rw [map_zero, Subsingleton.elim x 0, map_zero]
  | mul a b ha hb =>
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      exact ⟨p * q, by rw [map_mul, hp, hq]⟩
  | add a b ha hb =>
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      exact ⟨p + q, by rw [map_add, hp, hq]⟩

/-- A tensor product of two algebras generated by the scalars is generated by the scalars. -/
theorem surjective_algebraMap_tensorProduct {S A B : Type u} [CommRing S] [CommRing A]
    [CommRing B] [Algebra S A] [Algebra S B] (hA : Function.Surjective (algebraMap S A))
    (hB : Function.Surjective (algebraMap S B)) :
    Function.Surjective (algebraMap S (A ⊗[S] B)) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
      obtain ⟨p, rfl⟩ := hA a
      obtain ⟨q, rfl⟩ := hB b
      refine ⟨q * p, ?_⟩
      have hb : algebraMap S B q = q • (1 : B) := by rw [Algebra.smul_def, mul_one]
      have ha : q • algebraMap S A p = algebraMap S A q * algebraMap S A p :=
        Algebra.smul_def q _
      rw [Algebra.TensorProduct.algebraMap_apply, map_mul, hb, ← TensorProduct.smul_tmul, ha]
  | add x y hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, by rw [map_add, hp, hq]⟩

/-- **The associated graded ring of the zero ideal is generated by degree zero**: it is the base
ring itself, by `AffineNormalCone.associatedGradedRingBotEquiv`. -/
theorem surjective_algebraMap_associatedGradedRing_bot (R : Type u) [CommRing R] :
    Function.Surjective
      (algebraMap (R ⧸ (⊥ : Ideal R)) (associatedGradedRing R (⊥ : Ideal R))) := by
  intro z
  refine ⟨Ideal.Quotient.mk ⊥ (associatedGradedRingBotEquiv R z), ?_⟩
  apply (associatedGradedRingBotEquiv R).injective
  have h : algebraMap (R ⧸ (⊥ : Ideal R)) (associatedGradedRing R (⊥ : Ideal R))
        (Ideal.Quotient.mk ⊥ (associatedGradedRingBotEquiv R z)) =
      associatedGradedBaseRingHom R ⊥
        (Ideal.Quotient.mk ⊥ (associatedGradedRingBotEquiv R z)) := rfl
  rw [h, associatedGradedRingBotEquiv_base_mk]

end Generators

section AffineSpaceExample

open CategoryTheory
open _root_.AlgebraicGeometry (Spec)
open RelativeVirtualClassBaseChange RelativeHyperplaneReindex RelativeAbsolute
open GromovWitten.AlgebraicGeometry.NormalConeAction (Base)
open GradedCone.SymmetricFunctoriality
open IntersectionTheory hiding Scheme AlgebraicCycle
open HomotopyInvariance (quotientCycle)
open scoped TensorProduct

-- Tensor products of the associated graded ring with a symmetric algebra need a deeper instance
-- search, exactly as in `RelativeAbsolute.lean`.
set_option maxSynthPendingDepth 5

variable {k : Type u} [CommRing k] {σ τ' : Type u}
variable (I : Ideal (MvPolynomial (σ ⊕ Option τ') k))
variable {E : LinearTwoTermComplex (Base I)} [Subsingleton E.degreeOne]
variable (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))

/-- **Over the full affine space and with vanishing `E⁻¹` the resolved cone is all of
`C ×_X E₀`**: the coordinate-ring map `Sym(E⁰) → gr_I(R) ⊗ Sym(E⁻¹)` is surjective, both factors of
its target being generated by the scalars. -/
theorem surjective_relProductMap_of_eq_bot (hI : I = ⊥) :
    Function.Surjective (relProductMap φ) := by
  subst hI
  intro z
  obtain ⟨a, rfl⟩ := surjective_algebraMap_tensorProduct
    (surjective_algebraMap_associatedGradedRing_bot (MvPolynomial (σ ⊕ Option τ') k))
    (surjective_algebraMap_symmetricAlgebra_of_subsingleton _ E.degreeOne) z
  exact ⟨algebraMap _ _ a, (relProductMap φ).commutes a⟩

/-- **A positive example of transversality**: over the full affine space `X = 𝔸^{σ ⊔ Option τ'}`
(the ideal `I = ⊥`) and for an obstruction complex with vanishing degree-one term, the resolved cone
is transversal to the hyperplane `y₀ = 0`.  The hyperplane section `X' = 𝔸^{σ ⊔ τ'}` is nonempty
here, so this is not the degenerate case covered by `resolvedConeTransversal_of_isUnit`. -/
theorem resolvedConeTransversal_of_eq_bot (hI : I = ⊥) : ResolvedConeTransversal I φ :=
  resolvedConeTransversal_of_surjective I φ (surjective_relProductMap_of_eq_bot I φ hI)

omit [Subsingleton E.degreeOne] in
/-- The equation of the hyperplane is regular on all powers of the zero ideal. -/
theorem regularOnPowers_of_eq_bot (hI : I = ⊥) :
    RegularOnPowers I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')) := by
  subst hI
  exact regularOnPowers_bot (isLeftRegular_mvPolynomial_X _)

variable [Fintype σ]

/-- **The resolved-cone ideal identity holds unconditionally over the full affine space** with
vanishing `E⁻¹`: both hypotheses of `ideal'_reindexHom` are theorems there. -/
theorem ideal'_reindexHom_of_eq_bot (hI : I = ⊥) :
    ideal' (reindexHom I φ) =
      Ideal.map (scalarExtensionMap (Base I) (Base (reindexIdeal I)) E.degreeZero) (ideal' φ) :=
  ideal'_reindexHom I φ (regularOnPowers_of_eq_bot I hI)
    (resolvedConeTransversal_of_eq_bot I φ hI)

variable [Fintype τ'] [IsNoetherianRing k]
variable [Module.Free (Base I) E.degreeZero] [Module.Finite (Base I) E.degreeZero]
variable [Module.Free (Base (reindexIdeal I)) (Base (reindexIdeal I) ⊗[Base I] E.degreeZero)]
variable [Module.Finite (Base (reindexIdeal I)) (Base (reindexIdeal I) ⊗[Base I] E.degreeZero)]

/-- **The cycle-level comparison holds unconditionally over the full affine space** with vanishing
`E⁻¹`: the resolved-cone cycle of the base-changed datum pushes forward to the cycle of the
hyperplane section of the resolved cone. -/
theorem map_relConeCycle_reindexHom_of_eq_bot (hI : I = ⊥)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ)))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace (absHom (reindexHom I φ)))) (d : ℤ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map (hyperplaneBundleImmersion I E.degreeZero)
        dimE' dimE (relConeCycle (reindexHom I φ) dimE' d) =
      (quotientCycle (ideal' φ ⊔ symHyperplaneSpan I E.degreeZero) dimE d :
        _root_.AlgebraicGeometry.AlgebraicCycle (ResolvedCone.bundleSpace (absHom φ)) ℚ) :=
  map_relConeCycle_reindexHom I φ (regularOnPowers_of_eq_bot I hI)
    (resolvedConeTransversal_of_eq_bot I φ hI) dimE dimE' d

end AffineSpaceExample

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneCone
