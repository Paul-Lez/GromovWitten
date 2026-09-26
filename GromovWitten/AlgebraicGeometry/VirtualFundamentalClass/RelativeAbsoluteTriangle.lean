/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeAbsoluteObstruction
import GromovWitten.AlgebraicGeometry.Cones.DualShortExact
import Mathlib.Algebra.Module.PUnit

/-!
# The affine morphism of triangles between the relative and the absolute obstruction theory

Fix `k`, finite index sets `σ`, `τ`, `R = MvPolynomial (σ ⊕ τ) k`, `I : Ideal R` and
`X = Spec (R ⧸ I) → Y = 𝔸^τ_k`, as in `VirtualFundamentalClass/RelativeAbsolute.lean`.  Since
`Y` is smooth, its cotangent complex `L_Y` is concentrated in degree one, and the Jacobi–Zariski
triangle `L_Y ⊗ 𝒪_X → L_X → L_{X/Y}` of the tower `k → k[x_τ] → R ⧸ I` becomes, in the two-term
model of `Cones/Picard.lean`, a genuine *short exact sequence* of two-term complexes

`0 → [0 → (τ → R ⧸ I)] → conormalComplex k R I → relConormalComplex I → 0`,

both in degree zero (the conormal module is untouched) and in degree one (the coordinate
splitting `Tangent I ≅ (σ → R ⧸ I) ⊕ (τ → R ⧸ I)` of `sigmaPart`/`tauPart`/`sigmaLift`/`tauLift`
of `VirtualFundamentalClass/RelativeAbsolute.lean`).  This is the affine-model specialisation of
the chain-level Jacobi–Zariski triangle `PicardCriteria.jzLeftComplex`/`jzMidComplex`/
`jzRightComplex` of `Cones/IntrinsicPullbackSequence.lean`: it is built directly here for the
concrete tower `k → k[x_τ] → R ⧸ I` rather than identified with the abstract presentation
complexes of that file (see "What is not done" below).

Given a relative datum `φ : E ⟶ relConormalComplex I`, the same splitting exhibits
`absComplex φ` (`RelativeAbsolute.absComplex`) as an extension of `E` by the pulled-back base
complex, and the two short exact sequences fit into a commuting square whose vertical maps are
`absHom φ` and the identity of the base complex — the affine model of Behrend–Fantechi's
Definition 7.1 "compatible square" of obstruction theories.

## Main definitions

* `baseComplex I`: the trivial two-term complex `[0 → (τ → R ⧸ I)]`, i.e. `E_Y ⊗ 𝒪_X = L_Y ⊗
  𝒪_X` for the smooth base `Y = 𝔸^τ`.
* `baseInclusion I`, `conormalToRel I`: the two maps of the bottom row `0 → baseComplex I →
  conormalComplex k R I → relConormalComplex I → 0`.
* `absBaseInclusion φ`, `absProjection φ`: the two maps of the top row `0 → baseComplex I →
  absComplex φ → E → 0`.
* `CompatibleSquare φ`: the Prop package of BF Def 7.1 — the two rows are short exact and the
  two squares built from `absHom φ` and the identity of `baseComplex I` commute.

## Main results

* `shortExact_relAbs I`, `shortExact_absComplex φ`: the bottom and top rows are short exact.
* `compatibleSquare φ : CompatibleSquare φ`: every relative datum gives a compatible square.
* `isObstructionTheory_absHom_iff_and_id`: **the "two out of three" property.**  Since the base
  leg `Hom.id (baseComplex I)` is automatically an obstruction theory (`𝔸^τ` is smooth), the
  absolute datum `absHom φ` is an obstruction theory for `X` exactly when the relative datum `φ`
  is one for `X/Y` — restating `RelativeAbsolute.isObstructionTheory_absHom_iff`.
* `shortExactPicard_absComplex φ B`: **the intrinsic pullback sequence of the compatible
  square.**  Dualising the top row over a test algebra `B` gives the exact sequence of Picard
  groupoids `h¹/h⁰(Eᵛ)(B) → h¹/h⁰((absComplex φ)ᵛ)(B) → h¹/h⁰(E_Yᵛ)(B)`, matching
  `PicardCriteria.shortExactPicard_dual_jz` of `Cones/IntrinsicPullbackSequence.lean`.
* `shortExactPicard_relConormal I B`: the analogous sequence for the bottom row.

## What is not done

The bottom row is built directly from the coordinate splitting of `RelativeAbsolute.lean`
rather than identified with the abstract Jacobi–Zariski triangle
`PicardCriteria.jzLeftComplex`/`jzMidComplex`/`jzRightComplex` of
`Cones/IntrinsicPullbackSequence.lean` for chosen presentations of the tower
`k → k[x_τ] → R ⧸ I`; such an identification would need an
explicit comparison of `Algebra.Generators` for that tower with the coordinate presentation used
here and is not attempted.  Base change of the square along `k → k'` and the product of two
squares (`ObstructionTheory/BaseChangeObstruction.lean`, `ObstructionTheory/ExternalSum.lean`)
are also not attempted.
-/

universe u

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeAbsolute

open scoped TensorProduct
open NormalConeAction ConeQuotient NormalSheafPicard
open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {k : Type u} [CommRing k] {σ τ : Type u}
variable (I : Ideal (MvPolynomial (σ ⊕ τ) k))

/-! ## The trivial complex `E_Y ⊗ 𝒪_X = [0 → (τ → R ⧸ I)]` -/

/-- **The pullback to `X` of the (concentrated in degree one) cotangent complex of the smooth
base `Y = 𝔸^τ`.**  Since `Y` is smooth its cotangent complex is `L_Y = (τ → k)` placed in degree
one with zero differential; this is its pullback along `X → Y`. -/
noncomputable abbrev baseComplex : LinearTwoTermComplex (Base I) where
  degreeZero := PUnit
  degreeOne := τ → Base I
  differential := 0

/-! ## The bottom row: `0 → baseComplex I → conormalComplex k R I → relConormalComplex I → 0` -/

section BottomRow

/-- **The inclusion of `E_Y ⊗ 𝒪_X` into `L_X`.**  Zero in degree zero, and the inclusion of the
`τ`-coordinates `tauLift I` in degree one. -/
noncomputable abbrev baseInclusion [Fintype τ] :
    LinearTwoTermComplex.Hom (baseComplex I)
      (conormalComplex k (MvPolynomial (σ ⊕ τ) k) I) where
  degreeZero := 0
  degreeOne := tauLift I
  comm _ := by simp

/-- **The projection `L_X ⟶ L_{X/Y}`.**  The identity in degree zero (the conormal module is
untouched by the relative/absolute passage) and `sigmaPart I` in degree one. -/
noncomputable abbrev conormalToRel :
    LinearTwoTermComplex.Hom (conormalComplex k (MvPolynomial (σ ⊕ τ) k) I)
      (relConormalComplex I) where
  degreeZero := LinearMap.id
  degreeOne := sigmaPart I
  comm _ := rfl

variable [Fintype τ]

/-- **The Jacobi–Zariski triangle of the tower `k → k[x_τ] → R ⧸ I`, as a short exact sequence.**
The `σ`- and `τ`-coordinate splitting of a tangent vector of the ambient affine space makes
`0 → E_Y ⊗ 𝒪_X → L_X → L_{X/Y} → 0` degreewise short exact. -/
theorem shortExact_relAbs [Finite σ] :
    PicardCriteria.ShortExact (baseInclusion I) (conormalToRel I) := by
  have _ : Fintype σ := Fintype.ofFinite σ
  exact
    { injective_degreeZero := fun a b _ => Subsingleton.elim a b
      injective_degreeOne := fun a b hab => by
        have h := congrArg (tauPart I) hab
        rwa [tauPart_tauLift, tauPart_tauLift] at h
      surjective_degreeZero := Function.surjective_id
      surjective_degreeOne := fun a => ⟨sigmaLift I a, sigmaPart_sigmaLift I a⟩
      exact_degreeZero := by rw [LinearMap.ker_id, LinearMap.range_zero]
      exact_degreeOne := by
        refine Submodule.ext fun v => ?_
        rw [LinearMap.mem_ker, LinearMap.mem_range]
        constructor
        · intro hv
          refine ⟨tauPart I v, ?_⟩
          have h := sigmaLift_sigmaPart_add_tauLift_tauPart I v
          rwa [hv, map_zero, zero_add] at h
        · rintro ⟨w, rfl⟩
          exact sigmaPart_tauLift I w }

/-- The bottom row is degreewise split: the retraction is `0` in degree zero (the target `PUnit`
is a subsingleton) and `tauPart I` in degree one. -/
theorem isDegreewiseSplit_baseInclusion :
    PicardCriteria.ShortExact.IsDegreewiseSplit (baseInclusion I) :=
  ⟨⟨0, fun x => Subsingleton.elim _ x⟩, ⟨tauPart I, fun w => tauPart_tauLift I w⟩⟩

end BottomRow

/-! ## The top row: `0 → baseComplex I → absComplex φ → E → 0` -/

section TopRow

variable {E : LinearTwoTermComplex (Base I)}
  (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))

/-- **The inclusion of `E_Y ⊗ 𝒪_X` into the absolute complex `absComplex φ`.**  Zero in degree
zero (`(absComplex φ).degreeZero = E.degreeZero`) and the inclusion of the `τ`-summand in degree
one. -/
noncomputable abbrev absBaseInclusion :
    LinearTwoTermComplex.Hom (baseComplex I) (absComplex φ) where
  degreeZero := 0
  degreeOne := LinearMap.inr (Base I) E.degreeOne (τ → Base I)
  comm _ := by simp

/-- **The projection `absComplex φ ⟶ E`**, forgetting the `τ`-summand adjoined in degree zero of
the absolute complex: the identity in degree zero and the first projection in degree one. -/
noncomputable abbrev absProjection : LinearTwoTermComplex.Hom (absComplex φ) E where
  degreeZero := LinearMap.id
  degreeOne := LinearMap.fst (Base I) E.degreeOne (τ → Base I)
  comm _ := rfl

/-- **`absComplex φ` is `E` with the `τ`-summand adjoined in degree zero**, exhibited as a short
exact sequence `0 → E_Y ⊗ 𝒪_X → absComplex φ → E → 0`. -/
theorem shortExact_absComplex :
    PicardCriteria.ShortExact (absBaseInclusion I φ) (absProjection I φ) where
  injective_degreeZero a b _ := Subsingleton.elim a b
  injective_degreeOne := LinearMap.inr_injective
  surjective_degreeZero := Function.surjective_id
  surjective_degreeOne := fun u => ⟨(u, 0), rfl⟩
  exact_degreeZero := by rw [LinearMap.ker_id, LinearMap.range_zero]
  exact_degreeOne := LinearMap.ker_fst (Base I) E.degreeOne (τ → Base I)

/-- The top row is degreewise split: the retraction is `0` in degree zero and `LinearMap.snd` in
degree one. -/
theorem isDegreewiseSplit_absBaseInclusion :
    PicardCriteria.ShortExact.IsDegreewiseSplit (absBaseInclusion I φ) :=
  ⟨⟨0, fun x => Subsingleton.elim _ x⟩,
    ⟨LinearMap.snd (Base I) E.degreeOne (τ → Base I), fun _ => rfl⟩⟩

/-! ### The two commuting squares -/

variable [Fintype σ] [Fintype τ]

/-- **The left square commutes in degree zero.**  Both composites are the zero map. -/
theorem absHom_comp_absBaseInclusion_degreeZero :
    (absHom φ).degreeZero.comp (absBaseInclusion I φ).degreeZero =
      (baseInclusion I).degreeZero := by
  ext x
  simp

/-- **The left square commutes in degree one.**  Translating the tautological `τ`-directions
through `absHom φ` reproduces `tauLift I`. -/
theorem absHom_comp_absBaseInclusion_degreeOne :
    (absHom φ).degreeOne.comp (absBaseInclusion I φ).degreeOne = (baseInclusion I).degreeOne := by
  ext w
  change absHomOne φ (0, w) = tauLift I w
  rw [absHomOne_apply, map_zero, map_zero, zero_add]

/-- **The right square commutes in degree zero.**  Both composites are `φ.degreeZero`. -/
theorem φ_comp_absProjection_degreeZero :
    φ.degreeZero.comp (absProjection I φ).degreeZero =
      (conormalToRel I).degreeZero.comp (absHom φ).degreeZero := by
  ext x
  simp

/-- **The right square commutes in degree one.**  Projecting `absHom φ` to the `σ`-coordinates
reproduces `φ.degreeOne`. -/
theorem φ_comp_absProjection_degreeOne :
    φ.degreeOne.comp (absProjection I φ).degreeOne =
      (conormalToRel I).degreeOne.comp (absHom φ).degreeOne := by
  refine LinearMap.ext fun p => ?_
  obtain ⟨u, w⟩ := p
  change φ.degreeOne u = sigmaPart I (absHomOne φ (u, w))
  rw [absHomOne_apply, map_add, sigmaPart_sigmaLift, sigmaPart_tauLift, add_zero]

/-! ## The compatible square -/

/-- **A compatible square** (Behrend–Fantechi, Def. 7.1, affine model): the relative datum `φ`,
its absolute counterpart `absHom φ`, and the (necessarily trivial, since `𝔸^τ` is smooth) datum
`Hom.id (baseComplex I) : baseComplex I ⟶ baseComplex I` for the base fit into a square of short
exact rows, both of whose squares commute. -/
structure CompatibleSquare : Prop where
  /-- The top row `0 → baseComplex I → absComplex φ → E → 0` is short exact. -/
  shortExact_top : PicardCriteria.ShortExact (absBaseInclusion I φ) (absProjection I φ)
  /-- The bottom row `0 → baseComplex I → conormalComplex k R I → relConormalComplex I → 0` is
  short exact. -/
  shortExact_bottom : PicardCriteria.ShortExact (baseInclusion I) (conormalToRel I)
  /-- The left square commutes in degree zero. -/
  leftSquare_degreeZero : (absHom φ).degreeZero.comp (absBaseInclusion I φ).degreeZero =
      (baseInclusion I).degreeZero
  /-- The left square commutes in degree one. -/
  leftSquare_degreeOne : (absHom φ).degreeOne.comp (absBaseInclusion I φ).degreeOne =
      (baseInclusion I).degreeOne
  /-- The right square commutes in degree zero. -/
  rightSquare_degreeZero : φ.degreeZero.comp (absProjection I φ).degreeZero =
      (conormalToRel I).degreeZero.comp (absHom φ).degreeZero
  /-- The right square commutes in degree one. -/
  rightSquare_degreeOne : φ.degreeOne.comp (absProjection I φ).degreeOne =
      (conormalToRel I).degreeOne.comp (absHom φ).degreeOne

/-- **Every relative datum gives a compatible square.** -/
theorem compatibleSquare : CompatibleSquare I φ where
  shortExact_top := shortExact_absComplex I φ
  shortExact_bottom := shortExact_relAbs I
  leftSquare_degreeZero := absHom_comp_absBaseInclusion_degreeZero I φ
  leftSquare_degreeOne := absHom_comp_absBaseInclusion_degreeOne I φ
  rightSquare_degreeZero := φ_comp_absProjection_degreeZero I φ
  rightSquare_degreeOne := φ_comp_absProjection_degreeOne I φ

/-! ## Compatibility of the obstruction-theory conditions -/

/-- **The "two out of three" property of the compatible square.**  The base leg
`Hom.id (baseComplex I)` is automatically an obstruction theory (`𝔸^τ` is smooth), so the
absolute datum `absHom φ` is an obstruction theory exactly when the relative datum `φ` is one:
this restates `isObstructionTheory_absHom_iff` with the trivial base leg made explicit. -/
theorem isObstructionTheory_absHom_iff_and_id :
    PicardCriteria.IsObstructionTheory (absHom φ) ↔
      PicardCriteria.IsObstructionTheory φ ∧
        PicardCriteria.IsObstructionTheory (LinearTwoTermComplex.Hom.id (baseComplex I)) :=
  ⟨fun h => ⟨(isObstructionTheory_absHom_iff φ).mp h,
      PicardCriteria.IsObstructionTheory.id (baseComplex I)⟩,
    fun h => (isObstructionTheory_absHom_iff φ).mpr h.1⟩

/-! ## The intrinsic pullback sequence of Picard groupoids -/

variable (B : Type u) [CommRing B] [Algebra (Base I) B]

omit [Fintype σ] [Fintype τ] in
/-- **The intrinsic pullback sequence of the compatible square.**  Dualising the top row
`0 → baseComplex I → absComplex φ → E → 0` over a test algebra `B` gives the exact sequence of
Picard groupoids `h¹/h⁰(Eᵛ)(B) → h¹/h⁰((absComplex φ)ᵛ)(B) → h¹/h⁰(E_Yᵛ)(B)`, matching the
intrinsic pullback sequence `PicardCriteria.shortExactPicard_dual_jz` of
`Cones/IntrinsicPullbackSequence.lean`. -/
theorem shortExactPicard_absComplex :
    PicardCriteria.ShortExactPicard
      (PicardCriteria.dualHom (absProjection I φ) B)
      (PicardCriteria.dualHom (absBaseInclusion I φ) B) :=
  (shortExact_absComplex I φ).shortExactPicard_dualHom (isDegreewiseSplit_absBaseInclusion I φ) B

end TopRow

/-- **The intrinsic pullback sequence of the bottom row.**  The analogue of
`shortExactPicard_absComplex` for `0 → baseComplex I → conormalComplex k R I →
relConormalComplex I → 0`: `h¹/h⁰(L_{X/Y}ᵛ)(B) → h¹/h⁰(L_Xᵛ)(B) → h¹/h⁰(E_Yᵛ)(B)`. -/
theorem shortExactPicard_relConormal [Finite σ] [Fintype τ] (B : Type u) [CommRing B]
    [Algebra (Base I) B] :
    PicardCriteria.ShortExactPicard
      (PicardCriteria.dualHom (conormalToRel I) B)
      (PicardCriteria.dualHom (baseInclusion I) B) :=
  (shortExact_relAbs I).shortExactPicard_dualHom (isDegreewiseSplit_baseInclusion I) B

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeAbsolute
