/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.DualShortExact
import GromovWitten.AlgebraicGeometry.Cones.PerfectTwoTerm
import GromovWitten.AlgebraicGeometry.CotangentComplex.AffinePresentation
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# The intrinsic pullback sequence of a tower of affine algebras

Behrend–Fantechi attach to a morphism `f : X → Y` over a base the *intrinsic pullback sequence*
`h¹/h⁰(L_{X/Y}ᵛ) → 𝔑_{X} → 𝔑_{Y} ×_Y X`, induced by the Jacobi–Zariski triangle
`L_{Y} ⊗ 𝒪_X → L_X → L_{X/Y}`.  This file constructs that sequence in the affine model of a
tower `R → S → T` of commutative rings (`X = Spec T`, `Y = Spec S`, base `Spec R`), presented by
`Q : Algebra.Generators S T` and `P : Algebra.Generators R S`, with `Q.comp P` presenting
`T` over `R`.

## Main results

* `PicardCriteria.jzLeftComplex`, `jzMidComplex`, `jzRightComplex`: the three two-term
  presentation complexes `T ⊗_S [I/I² → Ω_{R[X]}]`, `[J/J² → Ω_{R[X,Y]}]` and
  `[K/K² → Ω_{S[Y]}]`, together with the chain maps `jzToComp` and `jzOfComp` between them —
  the chain-level Jacobi–Zariski triangle.  The commutation squares are Mathlib's
  `Algebra.Generators.H1Cotangent.map_comp_cotangentComplex_baseChange` and
  `Algebra.Extension.CotangentSpace.map_comp_cotangentComplex`.
* Degreewise exactness, all unconditional and transported from Mathlib's Jacobi–Zariski
  sequence: `ker_jzOfComp_degreeZero`, `ker_jzOfComp_degreeOne` (exactness in the middle),
  `surjective_jzOfComp_degreeZero`, `surjective_jzOfComp_degreeOne` (surjectivity on the right)
  and `injective_jzToComp_degreeOne` (injectivity on the left in degree `0`, where the sequence
  is even split by `Algebra.Generators.CotangentSpace.compEquiv`).
* `PicardCriteria.shortExact_jz`: the Jacobi–Zariski sequence is a `ShortExact` sequence of
  two-term complexes as soon as the one remaining map `T ⊗_S I/I² → J/J²` is injective — the
  only hypothesis, and the exact point where the triangle degenerates into a short exact
  sequence.  From it the six-term cohomology sequence follows (`jzDelta`, `jz_injective_h0`,
  `jz_exact_h0_middle`, `jz_exact_h0_right`, `jz_exact_h1_left`, `jz_exact_h1_middle`,
  `jz_surjective_h1`).
* `PicardCriteria.isDegreewiseSplit_jz`: the sequence is degreewise split when the relative
  conormal module `K/K²` is projective — the local complete intersection hypothesis; the
  degree-`0` part is split unconditionally because `Ω` of a presentation is free
  (`projective_jzRightComplex_degreeOne`).
* `PicardCriteria.shortExact_dual_jz`, `shortExactPicard_dual_jz`, `essSurj_dual_jz`: **the
  intrinsic pullback sequence.**  Over every test algebra `B`, the dual sequence
  `h¹/h⁰(L_{T/S}ᵛ)(B) → 𝔑_{T/R}(B) → (𝔑_{S/R} ×_{Spec S} Spec T)(B)` is short exact in the sense
  of Layer 4: the second functor is essentially surjective, its fibres on hom-sets are torsors
  under `h⁰(L_{T/S}ᵛ)(B)`, and its fibres on isomorphism classes are the orbits of the
  translation action of the relative Picard groupoid.
* `PicardCriteria.dualJzLeftEquivalence`: the last term is the intrinsic normal sheaf of `S`
  over `R`, evaluated at `B` viewed as an `S`-algebra — the base-change adjunction
  `bijective_dualBaseChangeMap` identifies `(𝔑_{S/R} ×_{Spec S} Spec T)(B)` with `𝔑_{S/R}(B)`.
  Through `NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafQuotientEquivPresentation`
  that term is the affine intrinsic normal sheaf of `S/R` whenever `S` is presented as a
  quotient.

## What is assumed

Two hypotheses are carried explicitly, and nothing else: injectivity of `T ⊗_S I/I² → J/J²`
(the degeneration of the Jacobi–Zariski triangle into a short exact sequence; it holds for
instance for a flat tower and is what the missing `Tor`-vanishing input of Mathlib's
`H1Cotangent.exact_liftBaseChange_map_of_flat` would give in general), and projectivity of the
relative conormal module `K/K²` (the local complete intersection condition, needed for the
degreewise splitting which makes `Hom(-, B)` exact).  Neither is derived here from a
lci hypothesis on the ring map, and the comparison with the *derived* Jacobi–Zariski triangle of
`CotangentComplex/Full.lean` (`jzH1Map`, `jzDelta`, `jzOmegaMap`) is not formalized: the present
sequence is the chain-level one for chosen presentations.
-/

open CategoryTheory TensorProduct

universe u

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

open LinearTwoTermComplex CotangentComplex

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι σ : Type u} (Q : Algebra.Generators.{u} S T ι) (P : Algebra.Generators.{u} R S σ)

/-! ## The three two-term complexes of the Jacobi–Zariski triangle -/

/-- The base change to `T` of the presentation complex of `S` over `R`: the two-term complex
`[T ⊗ I/I² → T ⊗ Ω_{R[X]}]`.  Its dual is the fibre product `𝔑_{S/R} ×_{Spec S} Spec T`. -/
noncomputable def jzLeftComplex (T : Type u) [CommRing T] [Algebra S T]
    (P : Algebra.Generators.{u} R S σ) : LinearTwoTermComplex T where
  degreeZero := T ⊗[S] P.toExtension.Cotangent
  degreeOne := T ⊗[S] P.toExtension.CotangentSpace
  differential := LinearMap.baseChange T P.toExtension.cotangentComplex

/-- The presentation complex of `T` over `R`, for the composed presentation.  Its dual is the
intrinsic normal sheaf `𝔑_{T/R}`. -/
noncomputable abbrev jzMidComplex : LinearTwoTermComplex T :=
  AffinePresentation.twoTerm R T (Q.comp P).toExtension

/-- The presentation complex of `T` over `S`.  Its dual is the relative term
`h¹/h⁰(L_{T/S}ᵛ)` of the intrinsic pullback sequence. -/
noncomputable abbrev jzRightComplex : LinearTwoTermComplex T :=
  AffinePresentation.twoTerm S T Q.toExtension

/-- The first map of the Jacobi–Zariski sequence of two-term complexes: the base change of the
presentation complex of `S/R` maps to the presentation complex of `T/R`. -/
noncomputable def jzToComp : Hom (jzLeftComplex T P) (jzMidComplex Q P) where
  degreeZero :=
    (Algebra.Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T
  degreeOne :=
    (Algebra.Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T
  comm x :=
    congrArg (fun m : (T ⊗[S] P.toExtension.Cotangent) →ₗ[T]
        (Q.comp P).toExtension.CotangentSpace => m x)
      (Algebra.Generators.H1Cotangent.map_comp_cotangentComplex_baseChange Q P)

/-- The second map of the Jacobi–Zariski sequence of two-term complexes: the presentation
complex of `T/R` maps to the presentation complex of `T/S`. -/
noncomputable def jzOfComp : Hom (jzMidComplex Q P) (jzRightComplex Q) where
  degreeZero := Algebra.Extension.Cotangent.map (Q.ofComp P).toExtensionHom
  degreeOne := Algebra.Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom
  comm x :=
    congrArg (fun m : (Q.comp P).toExtension.Cotangent →ₗ[T] Q.toExtension.CotangentSpace => m x)
      (Algebra.Extension.CotangentSpace.map_comp_cotangentComplex
        (Q.ofComp P).toExtensionHom)

@[simp]
theorem jzToComp_degreeZero :
    (jzToComp Q P).degreeZero =
      (Algebra.Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T :=
  rfl

@[simp]
theorem jzToComp_degreeOne :
    (jzToComp Q P).degreeOne =
      (Algebra.Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T :=
  rfl

@[simp]
theorem jzOfComp_degreeZero :
    (jzOfComp Q P).degreeZero = Algebra.Extension.Cotangent.map (Q.ofComp P).toExtensionHom :=
  rfl

@[simp]
theorem jzOfComp_degreeOne :
    (jzOfComp Q P).degreeOne =
      Algebra.Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom :=
  rfl

/-! ## Degreewise exactness -/

/-- **Exactness in degree `-1`**: the conormal sequence `T ⊗ I/I² → J/J² → K/K²` of the
Jacobi–Zariski triangle is exact in the middle (Mathlib's `Cotangent.exact`). -/
theorem ker_jzOfComp_degreeZero :
    LinearMap.ker (jzOfComp Q P).degreeZero = LinearMap.range (jzToComp Q P).degreeZero :=
  ((Algebra.Generators.Cotangent.exact Q P).linearMap_ker_eq).trans rfl

/-- **Exactness in degree `0`**: the sequence of ambient differentials
`T ⊗ Ω_{R[X]} → Ω_{R[X,Y]} → Ω_{S[Y]}` is exact in the middle (Mathlib's
`CotangentSpace.exact`). -/
theorem ker_jzOfComp_degreeOne :
    LinearMap.ker (jzOfComp Q P).degreeOne = LinearMap.range (jzToComp Q P).degreeOne :=
  ((Algebra.Generators.CotangentSpace.exact Q P).linearMap_ker_eq).trans rfl

/-- The map on conormal modules is surjective. -/
theorem surjective_jzOfComp_degreeZero :
    Function.Surjective (jzOfComp Q P).degreeZero :=
  Algebra.Generators.Cotangent.surjective_map_ofComp Q P

/-- The map on ambient differentials is surjective. -/
theorem surjective_jzOfComp_degreeOne :
    Function.Surjective (jzOfComp Q P).degreeOne :=
  Algebra.Generators.CotangentSpace.map_ofComp_surjective Q P

/-- The map on ambient differentials is injective: in degree `0` the Jacobi–Zariski sequence is
even split short exact, by `Algebra.Generators.CotangentSpace.compEquiv`. -/
theorem injective_jzToComp_degreeOne :
    Function.Injective (jzToComp Q P).degreeOne :=
  Algebra.Generators.CotangentSpace.map_toComp_injective Q P

/-- **The Jacobi–Zariski sequence of two-term complexes is short exact** as soon as the map on
conormal modules `T ⊗_S I/I² → J/J²` is injective.  Everything else — surjectivity on both
ends, exactness in the middle in both degrees, and injectivity in degree `0` — is unconditional
and comes from Mathlib's Jacobi–Zariski sequence.  The remaining injectivity is the only place
where a hypothesis on the tower `R → S → T` is needed; it holds for instance when `T` is flat
over `S`, and it is exactly the condition under which the triangle degenerates into a short
exact sequence of presentation complexes. -/
theorem shortExact_jz (hinj : Function.Injective (jzToComp Q P).degreeZero) :
    ShortExact (jzToComp Q P) (jzOfComp Q P) where
  injective_degreeZero := hinj
  injective_degreeOne := injective_jzToComp_degreeOne Q P
  surjective_degreeZero := surjective_jzOfComp_degreeZero Q P
  surjective_degreeOne := surjective_jzOfComp_degreeOne Q P
  exact_degreeZero := ker_jzOfComp_degreeZero Q P
  exact_degreeOne := ker_jzOfComp_degreeOne Q P

/-! ## The six-term Jacobi–Zariski sequence on `h⁰` and `h¹` -/

section SixTerm

variable (hinj : Function.Injective (jzToComp Q P).degreeZero)

include hinj

/-- The connecting homomorphism `h⁰(L_{T/S}) → h¹(T ⊗ L_{S/R})` of the Jacobi–Zariski sequence
of two-term complexes. -/
noncomputable def jzDelta : h0 (jzRightComplex Q) →ₗ[T] h1 (jzLeftComplex T P) :=
  (shortExact_jz Q P hinj).delta

/-- `h⁰` of the first map is injective. -/
theorem jz_injective_h0 :
    Function.Injective (jzToComp Q P).kernelMap :=
  (shortExact_jz Q P hinj).injective_kernelMap

/-- Exactness of the Jacobi–Zariski sequence at `h⁰(L_{T/R})`. -/
theorem jz_exact_h0_middle :
    LinearMap.ker (jzOfComp Q P).kernelMap = LinearMap.range (jzToComp Q P).kernelMap :=
  (shortExact_jz Q P hinj).exact_h0_middle

/-- Exactness of the Jacobi–Zariski sequence at `h⁰(L_{T/S})`, where the connecting map
starts. -/
theorem jz_exact_h0_right :
    LinearMap.ker (jzDelta Q P hinj) = LinearMap.range (jzOfComp Q P).kernelMap :=
  (shortExact_jz Q P hinj).exact_h0_right

/-- Exactness of the Jacobi–Zariski sequence at `h¹(T ⊗ L_{S/R})`. -/
theorem jz_exact_h1_left :
    LinearMap.ker (jzToComp Q P).cokernelMap = LinearMap.range (jzDelta Q P hinj) :=
  (shortExact_jz Q P hinj).exact_h1_left

/-- Exactness of the Jacobi–Zariski sequence at `h¹(L_{T/R})`. -/
theorem jz_exact_h1_middle :
    LinearMap.ker (jzOfComp Q P).cokernelMap = LinearMap.range (jzToComp Q P).cokernelMap :=
  (shortExact_jz Q P hinj).exact_h1_middle

/-- The Jacobi–Zariski sequence ends in a surjection onto `h¹(L_{T/S})`. -/
theorem jz_surjective_h1 :
    Function.Surjective (jzOfComp Q P).cokernelMap :=
  (shortExact_jz Q P hinj).surjective_cokernelMap

end SixTerm

/-! ## The dual sequence of Picard groupoids -/

/-- The degree-one term of a presentation complex is free on the generators, hence projective. -/
theorem projective_jzRightComplex_degreeOne :
    Module.Projective T (jzRightComplex Q).degreeOne := by
  have hfree : Module.Free T Q.toExtension.CotangentSpace :=
    Module.Free.of_basis Q.cotangentSpaceBasis
  change Module.Projective T Q.toExtension.CotangentSpace
  infer_instance

/-- **The Jacobi–Zariski sequence is degreewise split** when the relative conormal module
`K/K²` is projective — for instance when `T = S/K` with `K` generated by a regular sequence,
that is when the morphism is a local complete intersection.  The degree-zero part is split
unconditionally (`Algebra.Generators.CotangentSpace.compEquiv`). -/
theorem isDegreewiseSplit_jz (hinj : Function.Injective (jzToComp Q P).degreeZero)
    (hproj : Module.Projective T Q.toExtension.Cotangent) :
    ShortExact.IsDegreewiseSplit (jzToComp Q P) := by
  have h0 : Module.Projective T (jzRightComplex Q).degreeZero := hproj
  have h1 : Module.Projective T (jzRightComplex Q).degreeOne :=
    projective_jzRightComplex_degreeOne Q
  exact (shortExact_jz Q P hinj).isDegreewiseSplit_of_projective

variable (B : Type u) [CommRing B] [Algebra T B]

/-- **The intrinsic pullback sequence.**  Dualising the Jacobi–Zariski sequence of presentation
complexes gives, over every test algebra `B`, a short exact sequence of two-term complexes of
`B`-points

`h¹/h⁰(L_{T/S}ᵛ)(B) → 𝔑_{T/R}(B) → (𝔑_{S/R} ×_{Spec S} Spec T)(B)`. -/
theorem shortExact_dual_jz (hinj : Function.Injective (jzToComp Q P).degreeZero)
    (hproj : Module.Projective T Q.toExtension.Cotangent) :
    ShortExact (dualHom (jzOfComp Q P) B) (dualHom (jzToComp Q P) B) :=
  (shortExact_jz Q P hinj).shortExact_dualHom (isDegreewiseSplit_jz Q P hinj hproj) B

/-- **The Picard-groupoid form of the intrinsic pullback sequence.**  The functor
`𝔑_{T/R}(B) → (𝔑_{S/R} ×_{Spec S} Spec T)(B)` is essentially surjective, its fibres on hom-sets
are torsors under `h⁰(L_{T/S}ᵛ)(B)` and its fibres on isomorphism classes are the orbits of the
translation action of the relative Picard groupoid `h¹/h⁰(L_{T/S}ᵛ)(B)`. -/
theorem shortExactPicard_dual_jz (hinj : Function.Injective (jzToComp Q P).degreeZero)
    (hproj : Module.Projective T Q.toExtension.Cotangent) :
    ShortExactPicard (dualHom (jzOfComp Q P) B) (dualHom (jzToComp Q P) B) :=
  (shortExact_dual_jz Q P B hinj hproj).shortExactPicard

/-- The restriction functor `𝔑_{T/R}(B) → (𝔑_{S/R} ×_{Spec S} Spec T)(B)` of the intrinsic
pullback sequence is essentially surjective. -/
theorem essSurj_dual_jz (hinj : Function.Injective (jzToComp Q P).degreeZero)
    (hproj : Module.Projective T Q.toExtension.Cotangent) :
    (dualHom (jzToComp Q P) B).quotientFunctor.EssSurj :=
  (shortExact_dual_jz Q P B hinj hproj).essSurj_quotientFunctor

/-! ## The last term is the intrinsic normal sheaf of `S` over `R` -/

section BaseChangeIdentification

/-- Restriction of a `B₀`-valued functional on a base-changed module along `m ↦ 1 ⊗ m`, as a
`B₀`-linear map.  This is the base-change adjunction for modules of functionals. -/
def dualBaseChangeMap (A₀ A₁ B₀ : Type u) [CommRing A₀] [CommRing A₁] [CommRing B₀]
    [Algebra A₀ A₁] [Algebra A₁ B₀] [Algebra A₀ B₀] [IsScalarTower A₀ A₁ B₀]
    (M : Type u) [AddCommGroup M] [Module A₀ M] :
    ((A₁ ⊗[A₀] M) →ₗ[A₁] B₀) →ₗ[B₀] (M →ₗ[A₀] B₀) where
  toFun l := (l.restrictScalars A₀).comp (TensorProduct.mk A₀ A₁ M 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem dualBaseChangeMap_apply (A₀ A₁ B₀ : Type u) [CommRing A₀] [CommRing A₁] [CommRing B₀]
    [Algebra A₀ A₁] [Algebra A₁ B₀] [Algebra A₀ B₀] [IsScalarTower A₀ A₁ B₀]
    (M : Type u) [AddCommGroup M] [Module A₀ M] (l : (A₁ ⊗[A₀] M) →ₗ[A₁] B₀) (x : M) :
    dualBaseChangeMap A₀ A₁ B₀ M l x = l (1 ⊗ₜ[A₀] x) :=
  rfl

/-- **Base-change adjunction.**  Restricting an `A₁`-linear functional on `A₁ ⊗[A₀] M` along
`m ↦ 1 ⊗ m` is a bijection onto the `A₀`-linear functionals on `M`. -/
theorem bijective_dualBaseChangeMap (A₀ A₁ B₀ : Type u) [CommRing A₀] [CommRing A₁]
    [CommRing B₀] [Algebra A₀ A₁] [Algebra A₁ B₀] [Algebra A₀ B₀] [IsScalarTower A₀ A₁ B₀]
    (M : Type u) [AddCommGroup M] [Module A₀ M] :
    Function.Bijective (dualBaseChangeMap A₀ A₁ B₀ M) := by
  have hfun : ⇑(dualBaseChangeMap A₀ A₁ B₀ M) =
      ⇑(LinearMap.liftBaseChangeEquiv (R := A₀) (M := M) (N := B₀) A₁).symm := by
    funext l
    exact LinearMap.ext fun x => rfl
  rw [hfun]
  exact (LinearMap.liftBaseChangeEquiv (R := A₀) (M := M) (N := B₀) A₁).symm.bijective

variable (B : Type u) [CommRing B] [Algebra T B] [Algebra S B] [IsScalarTower S T B]

/-- The comparison of the `B`-points of the dual of the base-changed presentation complex with
the `B`-points of the dual of the presentation complex of `S` over `R`. -/
noncomputable def dualJzLeftHom :
    Hom (dualPoints (jzLeftComplex T P) B)
      (dualPoints (AffinePresentation.twoTerm R S P.toExtension) B) where
  degreeZero := dualBaseChangeMap S T B P.toExtension.CotangentSpace
  degreeOne := dualBaseChangeMap S T B P.toExtension.Cotangent
  comm _ := LinearMap.ext fun _ => rfl

omit [Algebra R T] [IsScalarTower R S T] in
/-- **The last term of the intrinsic pullback sequence is the intrinsic normal sheaf of `S`
over `R`.**  The comparison is a quasi-isomorphism, by the base-change adjunction. -/
theorem isQuasiIsomorphism_dualJzLeftHom :
    (dualJzLeftHom (T := T) P B).IsQuasiIsomorphism :=
  isQuasiIsomorphism_of_bijective _
    (bijective_dualBaseChangeMap S T B P.toExtension.CotangentSpace)
    (bijective_dualBaseChangeMap S T B P.toExtension.Cotangent)

/-- **`(𝔑_{S/R} ×_{Spec S} Spec T)(B) ≌ 𝔑_{S/R}(B)`**: the fibre of the last term of the
intrinsic pullback sequence over a test algebra `B` is the fibre of the intrinsic normal sheaf
of `S` over `R` at `B`, viewed as an `S`-algebra through `T`. -/
noncomputable def dualJzLeftEquivalence :
    (dualPoints (jzLeftComplex T P) B).quotient ≌
      (dualPoints (AffinePresentation.twoTerm R S P.toExtension) B).quotient :=
  (isQuasiIsomorphism_dualJzLeftHom (T := T) P B).quotientEquivalence

end BaseChangeIdentification

end PicardCriteria

end GromovWitten.AlgebraicGeometry
