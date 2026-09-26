/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.NormalSheafPicard
import GromovWitten.AlgebraicGeometry.Cones.NormalConeAction
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The smooth formula `[N_{U/M}/T_M|_U] ≃ B T_U` in the affine model

For a formally smooth affine embedding `U = Spec S ↪ M = Spec P` with `P = k[x_i]`, this file
proves the affine, functor-of-points form of Behrend–Fantechi's "smooth case" description of the
intrinsic normal cone/sheaf: over every test algebra `B` the quotient groupoid
`[N_{U/M}/T_M|_U](B)` has exactly one isomorphism class, and the automorphism group of every
object is `Hom_S(Ω_{S/k}, B)`, the group of `k`-derivations of `S` valued in `B`.  By the already
proved comparison `C_{U/M} = N_{U/M}`
(`NormalConeAction.isEquivalence_quotientFunctor_of_bijective`) the same statements hold for the
intrinsic normal cone.

## Main results

* `SmoothIntrinsicNormalSheaf.isConnected_of_retraction`,
  `SmoothIntrinsicNormalSheaf.autEquiv_of_retraction`: the general algebraic input. If a linear
  map `d : N →ₗ[C] F` has a retraction `ρ` (`ρ ∘ d = id`), the quotient groupoid
  `[Spec Sym N / Spec Sym F]` attached to `ConeQuotient.bundleTranslationAction d` has a single
  isomorphism class over every test algebra `B`, and the automorphism group of every object is
  `h¹(dualComplexOf d) →ₗ[C] B`.
* `SmoothIntrinsicNormalSheaf.conormalRetraction`: for `U ⊆ M` formally smooth, the splitting of
  the conormal sequence `Algebra.Extension.formallySmooth_iff_split_injection` supplies exactly
  such a retraction of the conormal map `I/I² → (R/I) ⊗ Ω[R⁄k]`.
* `SmoothIntrinsicNormalSheaf.smoothNormalSheaf_isConnected`,
  `SmoothIntrinsicNormalSheaf.smoothNormalSheafAutEquiv`: the affine intrinsic normal sheaf
  `[N_{U/M}/T_M|_U](B)` is connected, with automorphism group `h¹(conormalComplex) →ₗ[R/I] B`.
* `SmoothIntrinsicNormalSheaf.h1ConormalComplexEquivKaehler`: `h¹` of the conormal complex is
  linearly identified with the actual Kähler differentials `Ω[(R/I)⁄k]`, so the automorphism
  group above is literally `Hom_{R/I}(Ω_{(R/I)/k}, B) ≃ Derivation k (R/I) B`
  (`smoothNormalSheafAutEquivDerivation`).
* `SmoothIntrinsicNormalSheaf.smoothIntrinsicNormalConeEquivalence`,
  `SmoothIntrinsicNormalSheaf.smoothIntrinsicNormalCone_isConnected`,
  `SmoothIntrinsicNormalSheaf.smoothIntrinsicNormalCone_autEquivDerivation`: transporting all of
  the above from the normal sheaf to the normal cone along the (already proved, unconditional)
  equivalence `NormalConeAction.isEquivalence_quotientFunctor_of_bijective`, given
  bijectivity of the normal-sheaf coordinate map (in particular given injectivity, since
  surjectivity always holds).

What is *not* proved here: naturality of the above equivalences in the test algebra `B`
(the individual ingredients — `NormalSheafPicard.toDualPoints_naturality`,
`ConeQuotient.quotientFunctor_comp_mapQuotient` — are already natural, but they are not
assembled here into a single natural equivalence of prestacks), and the stack-level (global)
gluing of the smooth formula, which needs the still-inactive `IntrinsicNormalCone/*.lean`
machinery.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

namespace SmoothIntrinsicNormalSheaf

universe u

/-! ## The general algebraic input: a retraction collapses the quotient groupoid -/

section Retraction

variable {C : Type u} [CommRing C] {N F : Type u} [AddCommGroup N] [Module C N]
  [AddCommGroup F] [Module C F] (d : N →ₗ[C] F) (ρ : F →ₗ[C] N)
  (hρ : ρ.comp d = LinearMap.id) (B : Type u) [CommRing B] [Algebra C B]

include ρ hρ in
/-- **A retraction of `d` makes precomposition with `d` on `B`-points surjective.**  If
`ρ ∘ d = id` then every `B`-linear functional on `N` extends to one on `F`, namely through `ρ`. -/
theorem precomp_surjective_of_retraction :
    Function.Surjective (PicardCriteria.precomp d B) := by
  intro l
  refine ⟨l.comp ρ, LinearMap.ext fun x => ?_⟩
  have hx : ρ (d x) = x := by
    have h := LinearMap.congr_fun hρ x
    simpa using h
  simp [PicardCriteria.precomp_apply, hx]

include ρ hρ in
/-- **The isomorphism class of every `B`-point is the same.**  This is the vanishing of the
cokernel of precomposition with `d`, i.e. of `h¹` of the complex of `B`-points of the dual of
`[N → F]`. -/
theorem isoClass_const_of_retraction
    (x y : ConeQuotient.QuotientGroupoid (ConeQuotient.bundleTranslationAction d) B) :
    NormalSheafPicard.isoClass d B x = NormalSheafPicard.isoClass d B y := by
  have htop :
      LinearMap.range (PicardCriteria.dualPoints (NormalSheafPicard.dualComplexOf d) B).differential
        = ⊤ := by
    rw [NormalSheafPicard.dualPoints_dualComplexOf_differential]
    exact LinearMap.range_eq_top.mpr (precomp_surjective_of_retraction d ρ hρ B)
  have h :=
    (PicardCriteria.h1mk_eq_iff
        (E := PicardCriteria.dualPoints (NormalSheafPicard.dualComplexOf d) B)
        (SymmetricAlgebra.lift.symm x.point) (SymmetricAlgebra.lift.symm y.point)).mpr
      (by rw [htop]; exact Submodule.mem_top)
  simpa only [NormalSheafPicard.isoClass_def] using h

include ρ hρ in
/-- **Collapse of the quotient groupoid.**  If `d` has a retraction, every two `B`-points of the
quotient groupoid `[Spec Sym N / Spec Sym F]` of `ConeQuotient.bundleTranslationAction d` are
isomorphic. -/
theorem isConnected_of_retraction
    (x y : ConeQuotient.QuotientGroupoid (ConeQuotient.bundleTranslationAction d) B) :
    Nonempty (x ≅ y) :=
  (NormalSheafPicard.isoClass_eq_iff d B x y).mp (isoClass_const_of_retraction d ρ hρ B x y)

/-- **Automorphisms are `Hom(h¹(d), B)`.**  If `d` has a retraction, the automorphism group of
every `B`-point of the quotient groupoid is `h¹` of the dual complex `[N → F]`, applied to `B`:
the cokernel of `d`, viewed through `B`-linear functionals. -/
noncomputable def autEquiv_of_retraction
    (x : ConeQuotient.QuotientGroupoid (ConeQuotient.bundleTranslationAction d) B) :
    (x ⟶ x) ≃ (PicardCriteria.h1 (NormalSheafPicard.dualComplexOf d) →ₗ[C] B) :=
  (NormalSheafPicard.autEquivH0 d B x).trans
    (PicardCriteria.dualH0Equiv (NormalSheafPicard.dualComplexOf d) B).toEquiv

end Retraction

/-! ## The affine local embedding: the retraction from formal smoothness -/

section Smooth

variable {A : Type u} [CommRing A] {σ : Type u} (I : Ideal (MvPolynomial σ A))

/-- The presentation `R → R/I` of `S = R/I` over `k = A`, for `R = A[x_i]` the polynomial
ambient ring: the affine local embedding `U = Spec S ↪ M = Spec R`. -/
noncomputable abbrev presentation : Algebra.Extension.{u} A (NormalConeAction.Base I) :=
  NormalSheafPicard.AffineIntrinsicNormalSheaf.quotientExtension A (MvPolynomial σ A) I

/-- The conormal map, read pointwise through the presentation comparison of
`NormalSheafPicard.AffineIntrinsicNormalSheaf`. -/
theorem conormalMap_eq (x : I.Cotangent) :
    AffineNormalCone.conormalMap A (MvPolynomial σ A) I x =
      (presentation I).cotangentComplex
        (NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalCotangentEquiv
          A (MvPolynomial σ A) I x) :=
  (NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalComplexHom A (MvPolynomial σ A) I).comm x

/-- The conormal map and the presentation cotangent differential have the same image, since
they differ by the bijective comparison `conormalCotangentEquiv`. -/
theorem range_conormalMap_eq_range_cotangentComplex :
    LinearMap.range (AffineNormalCone.conormalMap A (MvPolynomial σ A) I) =
      LinearMap.range (presentation I).cotangentComplex := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalCotangentEquiv
      A (MvPolynomial σ A) I x, (conormalMap_eq I x).symm⟩
  · rintro _ ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := (NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalCotangentEquiv
      A (MvPolynomial σ A) I).surjective w
    exact ⟨x, conormalMap_eq I x⟩

/-- **`h¹` of the conormal complex is the Kähler differentials of `S = R/I` over `k`.**  This
uses exactness of the presentation cotangent complex
(`Algebra.Extension.exact_cotangentComplex_toKaehler`) and surjectivity of the map to Kähler
differentials (`Algebra.Extension.toKaehler_surjective`), transported to the conormal map
through `range_conormalMap_eq_range_cotangentComplex`. -/
noncomputable def h1ConormalComplexEquivKaehler :
    PicardCriteria.h1 (NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalComplex
        A (MvPolynomial σ A) I) ≃ₗ[NormalConeAction.Base I]
      Ω[NormalConeAction.Base I⁄A] :=
  (Submodule.quotEquivOfEq _ _
        (range_conormalMap_eq_range_cotangentComplex I |>.trans
          (LinearMap.exact_iff.mp
            (presentation I).exact_cotangentComplex_toKaehler).symm)).trans
    (LinearMap.quotKerEquivOfSurjective _ (presentation I).toKaehler_surjective)

variable [Algebra.FormallySmooth A (NormalConeAction.Base I)]

/-- **The splitting of the conormal sequence coming from formal smoothness.**  Mathlib's
criterion for formal smoothness of a quotient of a formally smooth ambient ring is exactly the
existence of a retraction of the conormal map on the level of the presentation cotangent
complex. -/
theorem exists_split :
    ∃ l : (presentation I).CotangentSpace →ₗ[NormalConeAction.Base I] (presentation I).Cotangent,
      l.comp (presentation I).cotangentComplex = LinearMap.id :=
  (Algebra.Extension.formallySmooth_iff_split_injection (P := presentation I)).mp ‹_›

/-- **The retraction of the conormal map.**  Transporting the splitting of
`exists_split` through the identification `conormalCotangentEquiv` of the degree-zero terms of
the conormal complex and of the presentation complex. -/
noncomputable def conormalRetraction :
    NormalConeAction.Tangent I →ₗ[NormalConeAction.Base I] I.Cotangent :=
  (NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalCotangentEquiv
      A (MvPolynomial σ A) I).symm.toLinearMap ∘ₗ (exists_split I).choose

/-- The retraction of `conormalRetraction` really does retract the conormal map. -/
theorem conormalRetraction_apply_conormalMap (x : I.Cotangent) :
    conormalRetraction I (AffineNormalCone.conormalMap A (MvPolynomial σ A) I x) = x := by
  have hspec :=
    LinearMap.congr_fun (exists_split I).choose_spec
      (NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalCotangentEquiv
        A (MvPolynomial σ A) I x)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hspec
  unfold conormalRetraction
  rw [LinearMap.comp_apply, conormalMap_eq I x, hspec]
  exact (NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalCotangentEquiv
    A (MvPolynomial σ A) I).symm_apply_apply x

/-- The retraction property as a linear-map equation. -/
theorem conormalRetraction_comp :
    (conormalRetraction I).comp (AffineNormalCone.conormalMap A (MvPolynomial σ A) I) =
      LinearMap.id :=
  LinearMap.ext (conormalRetraction_apply_conormalMap I)

/-! ### The affine intrinsic normal sheaf of a smooth local embedding -/

/-- **Collapse of the affine intrinsic normal sheaf, smooth case.**  Every two `B`-points of
`[N_{U/M}/T_M|_U]` are isomorphic. -/
theorem smoothNormalSheaf_isConnected
    (B : Type u) [CommRing B] [Algebra (NormalConeAction.Base I) B]
    (x y : ConeQuotient.QuotientGroupoid
      (AffineNormalCone.normalSheafTangentAction A (MvPolynomial σ A) I) B) :
    Nonempty (x ≅ y) :=
  isConnected_of_retraction (AffineNormalCone.conormalMap A (MvPolynomial σ A) I)
    (conormalRetraction I) (conormalRetraction_comp I) B x y

/-- **Automorphisms in the affine intrinsic normal sheaf, smooth case.**  The automorphism group
of every `B`-point of `[N_{U/M}/T_M|_U]` is `h¹(conormalComplex) →ₗ[R/I] B`. -/
noncomputable def smoothNormalSheafAutEquiv
    (B : Type u) [CommRing B] [Algebra (NormalConeAction.Base I) B]
    (x : ConeQuotient.QuotientGroupoid
      (AffineNormalCone.normalSheafTangentAction A (MvPolynomial σ A) I) B) :
    (x ⟶ x) ≃
      (PicardCriteria.h1 (NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalComplex
        A (MvPolynomial σ A) I) →ₗ[NormalConeAction.Base I] B) :=
  autEquiv_of_retraction (AffineNormalCone.conormalMap A (MvPolynomial σ A) I) B x

/-- **Automorphisms in the affine intrinsic normal sheaf, in terms of derivations.**  The
automorphism group of every `B`-point of `[N_{U/M}/T_M|_U]` is `Hom_S(Ω_{S/k}, B)`, i.e. the
group of `k`-derivations of `S = R/I` valued in `B`.  This needs `B` to also be an `A`-algebra
compatibly with its `R/I`-algebra structure, since a `k`-derivation of `S` valued in `B` is only
meaningful relative to a fixed map `k → B`. -/
noncomputable def smoothNormalSheafAutEquivDerivation
    (B : Type u) [CommRing B] [Algebra (NormalConeAction.Base I) B] [Algebra A B]
    [IsScalarTower A (NormalConeAction.Base I) B]
    (x : ConeQuotient.QuotientGroupoid
      (AffineNormalCone.normalSheafTangentAction A (MvPolynomial σ A) I) B) :
    (x ⟶ x) ≃ Derivation A (NormalConeAction.Base I) B :=
  (smoothNormalSheafAutEquiv I B x).trans
    (((h1ConormalComplexEquivKaehler I).arrowCongr
        (LinearEquiv.refl (NormalConeAction.Base I) B)).trans
      (KaehlerDifferential.linearMapEquivDerivation A (NormalConeAction.Base I))).toEquiv

end Smooth

/-! ## Transport to the intrinsic normal cone -/

section Cone

variable {A : Type u} [CommRing A] {σ : Type u} (I : Ideal (MvPolynomial σ A))

/-- **Item 1: the closed immersion `C_{U/M} ↪ N_{U/M}` is an isomorphism.**  Injectivity of the
normal-sheaf coordinate map, combined with its (unconditional) surjectivity, gives
bijectivity. -/
theorem normalSheafCoordinateMap_bijective_of_injective
    (hinj : Function.Injective
      (AffineNormalCone.normalSheafCoordinateMap (MvPolynomial σ A) I)) :
    Function.Bijective (AffineNormalCone.normalSheafCoordinateMap (MvPolynomial σ A) I) :=
  ⟨hinj, AffineNormalCone.normalSheafCoordinateMap_surjective _ _⟩

/-- **Item 1/3: the intrinsic normal cone equals the intrinsic normal sheaf, as quotient
groupoids.**  This is `NormalConeAction.isEquivalence_quotientFunctor_of_bijective`, specialised
to bijectivity coming from injectivity of the normal-sheaf coordinate map. -/
noncomputable def smoothIntrinsicNormalConeEquivalence
    (hinj : Function.Injective
      (AffineNormalCone.normalSheafCoordinateMap (MvPolynomial σ A) I))
    (B : Type u) [CommRing B] [Algebra (NormalConeAction.Base I) B] :
    ConeQuotient.QuotientGroupoid (NormalConeAction.normalConeAction I) B ≌
      ConeQuotient.QuotientGroupoid
        (AffineNormalCone.normalSheafTangentAction A (MvPolynomial σ A) I) B :=
  haveI := NormalConeAction.isEquivalence_quotientFunctor_of_bijective I
    (normalSheafCoordinateMap_bijective_of_injective I hinj) B
  (ConeQuotient.quotientFunctor (NormalConeAction.isEquivariant_nsToGrAlg I) B).asEquivalence

variable [Algebra.FormallySmooth A (NormalConeAction.Base I)]
  (hinj : Function.Injective (AffineNormalCone.normalSheafCoordinateMap (MvPolynomial σ A) I))

include hinj in
/-- **Item 3: collapse of the intrinsic normal cone, smooth case.**  Every two `B`-points of
`[C_{U/M}/T_M|_U]` are isomorphic, transported from `smoothNormalSheaf_isConnected` along the
equivalence `smoothIntrinsicNormalConeEquivalence`. -/
theorem smoothIntrinsicNormalCone_isConnected
    (B : Type u) [CommRing B] [Algebra (NormalConeAction.Base I) B]
    (c c' : ConeQuotient.QuotientGroupoid (NormalConeAction.normalConeAction I) B) :
    Nonempty (c ≅ c') := by
  obtain ⟨iso⟩ := smoothNormalSheaf_isConnected I B
    ((smoothIntrinsicNormalConeEquivalence I hinj B).functor.obj c)
    ((smoothIntrinsicNormalConeEquivalence I hinj B).functor.obj c')
  exact ⟨(smoothIntrinsicNormalConeEquivalence I hinj B).fullyFaithfulFunctor.preimageIso iso⟩

include hinj in
/-- **Item 3: automorphisms in the intrinsic normal cone, smooth case, in terms of derivations.**
The automorphism group of every `B`-point of `[C_{U/M}/T_M|_U]` is `Hom_S(Ω_{S/k}, B)`,
transported from `smoothNormalSheafAutEquivDerivation` along
`smoothIntrinsicNormalConeEquivalence`. -/
noncomputable def smoothIntrinsicNormalCone_autEquivDerivation
    (B : Type u) [CommRing B] [Algebra (NormalConeAction.Base I) B] [Algebra A B]
    [IsScalarTower A (NormalConeAction.Base I) B]
    (c : ConeQuotient.QuotientGroupoid (NormalConeAction.normalConeAction I) B) :
    (c ⟶ c) ≃ Derivation A (NormalConeAction.Base I) B :=
  ((smoothIntrinsicNormalConeEquivalence I hinj B).fullyFaithfulFunctor.homEquiv).trans
    (smoothNormalSheafAutEquivDerivation I B
      ((smoothIntrinsicNormalConeEquivalence I hinj B).functor.obj c))

end Cone

end SmoothIntrinsicNormalSheaf

end GromovWitten.AlgebraicGeometry
