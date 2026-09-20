/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyKey
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjective
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackChow
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalizationExact
import GromovWitten.AlgebraicGeometry.IntersectionTheory.SupportedCycles

/-!
# Affine homotopy surjectivity with control of the supports

`IntersectionTheory/BundleHomotopy.lean` proves Fulton's Proposition 1.9 for a trivialised affine
vector bundle `π : Spec (MvPolynomial ι R) → Spec R`: every cycle on the total space which is
concentrated in dimension `j` is `π^*` of a cycle in dimension `j - r` modulo the span of
principal divisors.  The Noetherian induction which globalises that statement to an arbitrary
scheme needs the refinement in which all supports are tracked: if the given cycle is supported
over the closed subscheme `V(I) ⊆ Spec R`, then the cycle upstairs can be chosen supported in
`V(I)` and the relation can be chosen inside `supportedRelations … (V(I · MvPolynomial ι R))`.

The proof restricts everything to the closed subscheme `Spec (MvPolynomial ι (R ⧸ I))` (the
restriction of the bundle over `Spec (R ⧸ I)`), applies the affine surjectivity there, and pushes
the answer forward; both pushforwards land in cycles and relations supported in the image of the
closed immersion, which is exactly the required closed subset.

Main declarations:

* `totalRationalRelations_map_closedImmersion_supported`: the closed-immersion pushforward of the
  span of principal divisors lands in the relations supported in the image of the immersion;
* `VectorBundle.hasUniversalDimensionFormula_quotient`: the universal dimension formula passes to
  a quotient ring;
* `VectorBundle.ker_quotBundleHom_refl`, `VectorBundle.range_quotBundleImmersion_base_refl`: the
  kernel and the image of the restriction of the trivial bundle to `V(I)`, for an arbitrary ideal
  `I` (`BundlePullbackChow.lean` computes them only for a prime ideal);
* `VectorBundle.pullbackBundle_map_quotImmersion_of_ker`: the compatibility `π^* ∘ V_* =
  (E_V)_* ∘ π_V^*` of `BundlePullbackChow.lean`, with the primality hypothesis on the ideal
  replaced by the explicit kernel computation;
* `VectorBundle.exists_pullback_supported`: the affine surjectivity with supports, in the form
  consumed by the global Noetherian induction.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Pushing relations forward along a closed immersion -/

/-- The pushforward along a closed immersion of a principal divisor is a principal divisor
supported in the image of the immersion: the integral closed subscheme of the generator is
composed with the immersion, so its image lies in the image of the immersion. -/
theorem totalRationalRelations_map_closedImmersion_supported {W X : Scheme.{u}} (f : W ⟶ X)
    [_root_.AlgebraicGeometry.IsClosedImmersion f] (dimensionW : DimensionFunction W)
    (dimensionX : DimensionFunction X) :
    Submodule.map (AlgebraicCycle.mapLinear f dimensionW dimensionX)
        (totalRationalRelations W dimensionW) ≤
      supportedRelations X dimensionX (Set.range f.base) := by
  rw [totalRationalRelations, Submodule.map_span]
  refine Submodule.span_le.2 ?_
  rintro d ⟨c, ⟨g, rfl⟩, rfl⟩
  have hsup : (g.closedImage f).SupportedIn (Set.range f.base) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨g.subspace.inclusion.base y, rfl⟩
  have hd := divisor_mem_supportedRelations dimensionX hsup
  rw [← g.map_divisor_closedImmersion f dimensionW dimensionX] at hd
  exact hd

namespace VectorBundle

/-! ## The universal dimension formula for a quotient ring -/

/-- The universal dimension formula passes to every quotient of the base ring: a prime quotient of
`MvPolynomial ι (R ⧸ I)` is a prime quotient of `MvPolynomial ι R`, through the surjection
reducing the coefficients modulo `I`. -/
theorem hasUniversalDimensionFormula_quotient {R : Type u} [CommRing R]
    (h : HasUniversalDimensionFormula R) (I : Ideal R) :
    HasUniversalDimensionFormula (R ⧸ I) := by
  intro ι' _ P hP
  have hPp : P.IsPrime := hP
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk P).comp
        (MvPolynomial.map (Ideal.Quotient.mk I) : MvPolynomial ι' R →+* _)) :=
    Ideal.Quotient.mk_surjective.comp
      (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  have hker : RingHom.ker ((Ideal.Quotient.mk P).comp
      (MvPolynomial.map (Ideal.Quotient.mk I) : MvPolynomial ι' R →+* _)) =
      P.comap (MvPolynomial.map (Ideal.Quotient.mk I)) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  have _ : (RingHom.ker ((Ideal.Quotient.mk P).comp
      (MvPolynomial.map (Ideal.Quotient.mk I) : MvPolynomial ι' R →+* _))).IsPrime := by
    rw [hker]
    exact hPp.comap _
  exact SectionGysinIdentity.hasDimensionFormula_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective hsurj) (h ι' _ inferInstance)

/-! ## The restriction of the trivial bundle to an arbitrary closed subscheme -/

section Restriction

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {ι : Type u}
  (e : A ≃ₐ[R] MvPolynomial ι R) (I : Ideal R)

/-- The kernel of the restriction map of the *tautologically* trivialised bundle is the extended
ideal, for an arbitrary ideal `I`.  `BundlePullbackChow.ker_quotBundleHom` proves this for a prime
ideal and an arbitrary trivialisation; here no primality is needed because the trivialisation is
the identity and the kernel of a coefficientwise reduction of polynomials is computed by
`MvPolynomial.ker_map`. -/
theorem ker_quotBundleHom_refl :
    RingHom.ker (quotBundleHom (AlgEquiv.refl : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R) I) =
      Ideal.map (algebraMap R (MvPolynomial ι R)) I := by
  have h : quotBundleHom (AlgEquiv.refl : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R) I =
      (MvPolynomial.map (Ideal.Quotient.mk I) : MvPolynomial ι R →+* MvPolynomial ι (R ⧸ I)) :=
    RingHom.ext fun _ ↦ rfl
  rw [h, MvPolynomial.ker_map, Ideal.mk_ker, MvPolynomial.algebraMap_eq]

/-- Contracting an extended ideal of the restricted bundle along the restriction map gives the
extension of the contracted ideal.  This is `BundlePullbackChow.comap_quotBundleHom_map_algebraMap`
with the primality of the ideal replaced by the explicit computation of the kernel. -/
theorem comap_quotBundleHom_map_algebraMap_of_ker
    (hker : RingHom.ker (quotBundleHom e I) = Ideal.map (algebraMap R A) I)
    (P : Ideal (R ⧸ I)) :
    Ideal.comap (quotBundleHom e I)
        (Ideal.map (algebraMap (R ⧸ I) (MvPolynomial ι (R ⧸ I))) P) =
      Ideal.map (algebraMap R A) (Ideal.comap (Ideal.Quotient.mk I) P) := by
  have hPQ : Ideal.map (Ideal.Quotient.mk I) (Ideal.comap (Ideal.Quotient.mk I) P) = P :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P
  have hcomp : (quotBundleHom e I).comp (algebraMap R A) =
      (algebraMap (R ⧸ I) (MvPolynomial ι (R ⧸ I))).comp (Ideal.Quotient.mk I) :=
    RingHom.ext fun r ↦ quotBundleHom_algebraMap e I r
  have hmapK : Ideal.map (quotBundleHom e I)
      (Ideal.map (algebraMap R A) (Ideal.comap (Ideal.Quotient.mk I) P)) =
      Ideal.map (algebraMap (R ⧸ I) (MvPolynomial ι (R ⧸ I))) P := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hPQ]
  have hpQ : I ≤ Ideal.comap (Ideal.Quotient.mk I) P := by
    intro x hx
    change Ideal.Quotient.mk I x ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact P.zero_mem
  rw [← hmapK, Ideal.comap_map_of_surjective _ (quotBundleHom_surjective e I),
    ← RingHom.ker_eq_comap_bot, hker, sup_eq_left]
  exact Ideal.map_mono hpQ

/-- The generic point of the fibre over a point of the closed subscheme, computed in the restricted
bundle, maps to the generic point of the fibre over its image.  This is
`BundlePullbackChow.quotBundleImmersion_base_bundlePoint` without the primality hypothesis. -/
theorem quotBundleImmersion_base_bundlePoint_of_ker
    (hker : RingHom.ker (quotBundleHom e I) = Ideal.map (algebraMap R A) I)
    (x : ↥(Spec (CommRingCat.of (R ⧸ I)))) :
    (quotBundleImmersion e I).base (bundlePoint (quotTrivialization ι I) x) =
      bundlePoint e ((quotImmersion I).base x) :=
  PrimeSpectrum.ext
    (comap_quotBundleHom_map_algebraMap_of_ker e I hker (x : PrimeSpectrum (R ⧸ I)).asIdeal)

/-- The flat pullback of a cycle pushed forward from the closed subscheme vanishes away from the
image of the generic points of the fibres of the restricted bundle.  This is
`BundlePullbackChow.pullbackBundle_map_quotImmersion_apply_eq_zero` without primality. -/
theorem pullbackBundle_map_quotImmersion_apply_eq_zero_of_ker
    (hker : RingHom.ker (quotBundleHom e I) = Ideal.map (algebraMap R A) I)
    (wX : ↥(Spec (CommRingCat.of R)) → ℤ)
    (c : AlgebraicCycle (Spec (CommRingCat.of (R ⧸ I))) ℚ)
    {y : ↥(Spec (CommRingCat.of A))}
    (hy : ∀ x, y ≠ (quotBundleImmersion e I).base (bundlePoint (quotTrivialization ι I) x)) :
    AlgebraicCycle.pullbackBundle e
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (quotImmersion I)
          (fun z ↦ wX ((quotImmersion I).base z)) wX c) y = 0 := by
  by_cases hmem : y ∈ Set.range (bundlePoint e)
  · obtain ⟨w, rfl⟩ := hmem
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint]
    refine AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ ?_
    rintro ⟨x, rfl⟩
    exact hy x (quotBundleImmersion_base_bundlePoint_of_ker e I hker x).symm
  · exact AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e _ hmem

/-- The flat pullback along a trivialised affine bundle commutes with the pushforward along the
closed immersion of `Spec (R ⧸ I)`: `π^* ∘ V_* = (E_V)_* ∘ π_V^*`.  This is
`BundlePullbackChow.pullbackBundle_map_quotImmersion` with the primality of `I` replaced by the
explicit computation of the kernel of the restriction map. -/
theorem pullbackBundle_map_quotImmersion_of_ker
    (hker : RingHom.ker (quotBundleHom e I) = Ideal.map (algebraMap R A) I)
    (wX : ↥(Spec (CommRingCat.of R)) → ℤ) (wE : ↥(Spec (CommRingCat.of A)) → ℤ)
    (c : AlgebraicCycle (Spec (CommRingCat.of (R ⧸ I))) ℚ) :
    AlgebraicCycle.pullbackBundle e
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (quotImmersion I)
          (fun z ↦ wX ((quotImmersion I).base z)) wX c) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (quotBundleImmersion e I)
        (fun z ↦ wE ((quotBundleImmersion e I).base z)) wE
        (AlgebraicCycle.pullbackBundle (quotTrivialization ι I) c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  dsimp only
  by_cases hy : y ∈ Set.range (quotBundleImmersion e I).base
  · obtain ⟨z, rfl⟩ := hy
    rw [AlgebraicCycle.map_closedImmersion_apply_image (quotBundleImmersion e I) wE
      (AlgebraicCycle.pullbackBundle (quotTrivialization ι I) c) z]
    by_cases hz : z ∈ Set.range (bundlePoint (quotTrivialization ι I))
    · obtain ⟨x, rfl⟩ := hz
      rw [quotBundleImmersion_base_bundlePoint_of_ker e I hker x,
        AlgebraicCycle.pullbackBundle_apply_bundlePoint e _ ((quotImmersion I).base x),
        AlgebraicCycle.map_closedImmersion_apply_image (quotImmersion I) wX c x,
        AlgebraicCycle.pullbackBundle_apply_bundlePoint (quotTrivialization ι I) c x]
    · rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem _ c hz]
      refine pullbackBundle_map_quotImmersion_apply_eq_zero_of_ker e I hker wX c ?_
      intro x hx
      exact hz ⟨x, ((quotBundleImmersion e I).isClosedEmbedding.injective hx).symm⟩
  · rw [AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range
      (quotBundleImmersion e I) wE _ y hy]
    exact pullbackBundle_map_quotImmersion_apply_eq_zero_of_ker e I hker wX c
      fun x hx ↦ hy ⟨_, hx.symm⟩

end Restriction

/-! ## The images of the two closed immersions -/

section Images

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The image of the closed immersion `Spec (R ⧸ I) → Spec R` is the zero locus of `I`. -/
theorem range_quotImmersion_base :
    Set.range (quotImmersion I).base = PrimeSpectrum.zeroLocus (I : Set R) := by
  have h : Set.range (quotImmersion I).base =
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := rfl
  rw [h, _root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

variable {ι : Type u}

/-- The image of the closed immersion of the restricted bundle into the total space of the trivial
bundle is the zero locus of the extended ideal. -/
theorem range_quotBundleImmersion_base_refl :
    Set.range (quotBundleImmersion (AlgEquiv.refl : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R) I).base
      = PrimeSpectrum.zeroLocus
          (I.map (MvPolynomial.C : R →+* MvPolynomial ι R) : Set (MvPolynomial ι R)) := by
  have h : Set.range
      (quotBundleImmersion (AlgEquiv.refl : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R) I).base =
      Set.range (PrimeSpectrum.comap
        (quotBundleHom (AlgEquiv.refl : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R) I)) := rfl
  rw [h, _root_.range_comap_of_surjective _ _ (quotBundleHom_surjective _ I),
    ker_quotBundleHom_refl I, MvPolynomial.algebraMap_eq]

end Images

/-! ## Surjectivity with supports -/

section Supported

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [Finite ι] (e : A ≃ₐ[R] MvPolynomial ι R) (I : Ideal R)

/-- Fulton's Proposition 1.9 for a trivialised affine vector bundle, with supports tracked, in the
form where the restriction of the bundle to the closed subscheme `Spec (R ⧸ I)` is described by an
explicit kernel computation: a cycle on the total space which is concentrated in dimension `j` and
supported in the restricted bundle is the flat pullback of a cycle supported in `Spec (R ⧸ I)` and
concentrated in dimension `j - r`, modulo relations supported in the restricted bundle. -/
theorem exists_pullback_supported_of_ker
    (hker : RingHom.ker (quotBundleHom e I) = Ideal.map (algebraMap R A) I)
    (hdimQ : HasUniversalDimensionFormula (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of A)))
    (j : ℤ) (z : AlgebraicCycle (Spec (CommRingCat.of A)) ℚ)
    (hz : ∀ q, dimE q ≠ j → (z : _ → ℚ) q = 0)
    (hsupp : z.SupportedIn (Set.range (quotBundleImmersion e I).base)) :
    ∃ w : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ,
      (∀ x, dimX x ≠ j - (Nat.card ι : ℤ) → (w : _ → ℚ) x = 0) ∧
      w.SupportedIn (Set.range (quotImmersion I).base) ∧
      z - AlgebraicCycle.pullbackBundle e w ∈
        supportedRelations (Spec (CommRingCat.of A)) dimE
          (Set.range (quotBundleImmersion e I).base) := by
  have hzero : ∀ q, q ∉ Set.range (quotBundleImmersion e I).base → (z : _ → ℚ) q = 0 := by
    intro q hq
    by_contra hcon
    exact hq (hsupp q hcon)
  have hhom : PrincipalDivisorsHomogeneous
      (Spec (CommRingCat.of (MvPolynomial ι (R ⧸ I))))
      (DimensionFunction.comapClosedImmersion (quotBundleImmersion e I) dimE) :=
    principalDivisorsHomogeneous_of_hasUniversalDimensionFormula (quotTrivialization ι I) _ hdimQ
  have hconc : ∀ q, (DimensionFunction.comapClosedImmersion (quotBundleImmersion e I) dimE) q ≠ j →
      ((AlgebraicCycle.pullbackClosed (quotBundleImmersion e I) z :
        AlgebraicCycle (Spec (CommRingCat.of (MvPolynomial ι (R ⧸ I)))) ℚ) : _ → ℚ) q = 0 :=
    fun q hq ↦ hz _ hq
  obtain ⟨w', hw'dim, hw'rel⟩ := (mem_pullbackRange_iff _ _ _ _ _).1
    (bundleSurjective_of_card rankOneKey (Nat.card ι) (R ⧸ I) (MvPolynomial ι (R ⧸ I)) ι
      (quotTrivialization ι I) (DimensionFunction.comapClosedImmersion (quotImmersion I) dimX)
      (DimensionFunction.comapClosedImmersion (quotBundleImmersion e I) dimE) rfl hhom j
      (AlgebraicCycle.pullbackClosed (quotBundleImmersion e I) z) hconc)
  refine ⟨_root_.AlgebraicGeometry.AlgebraicCycle.map (quotImmersion I)
    (fun x ↦ (dimX : _ → ℤ) ((quotImmersion I).base x)) dimX w', ?_, ?_, ?_⟩
  · intro x hx
    by_cases hmem : x ∈ Set.range (quotImmersion I).base
    · obtain ⟨y, rfl⟩ := hmem
      rw [AlgebraicCycle.map_closedImmersion_apply_image (quotImmersion I) (dimX : _ → ℤ) w' y]
      exact hw'dim y hx
    · exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ hmem
  · intro x hx
    by_contra hmem
    exact hx (AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ hmem)
  · have hsub : _root_.AlgebraicGeometry.AlgebraicCycle.map (quotBundleImmersion e I)
        (fun q ↦ (dimE : _ → ℤ) ((quotBundleImmersion e I).base q)) (dimE : _ → ℤ)
        (AlgebraicCycle.pullbackClosed (quotBundleImmersion e I) z -
          AlgebraicCycle.pullbackBundle (quotTrivialization ι I) w') =
        _root_.AlgebraicGeometry.AlgebraicCycle.map (quotBundleImmersion e I)
          (fun q ↦ (dimE : _ → ℤ) ((quotBundleImmersion e I).base q)) (dimE : _ → ℤ)
          (AlgebraicCycle.pullbackClosed (quotBundleImmersion e I) z) -
        _root_.AlgebraicGeometry.AlgebraicCycle.map (quotBundleImmersion e I)
          (fun q ↦ (dimE : _ → ℤ) ((quotBundleImmersion e I).base q)) (dimE : _ → ℤ)
          (AlgebraicCycle.pullbackBundle (quotTrivialization ι I) w') :=
      (AlgebraicCycle.mapLinear (quotBundleImmersion e I)
        (fun q ↦ (dimE : _ → ℤ) ((quotBundleImmersion e I).base q)) (dimE : _ → ℤ)).map_sub _ _
    have hzmap := AlgebraicCycle.map_pullbackClosed (quotBundleImmersion e I)
      (dimE : _ → ℤ) z hzero
    have key : z - AlgebraicCycle.pullbackBundle e
          (_root_.AlgebraicGeometry.AlgebraicCycle.map (quotImmersion I)
            (fun x ↦ (dimX : _ → ℤ) ((quotImmersion I).base x)) dimX w') =
        _root_.AlgebraicGeometry.AlgebraicCycle.map (quotBundleImmersion e I)
          (fun q ↦ (dimE : _ → ℤ) ((quotBundleImmersion e I).base q)) (dimE : _ → ℤ)
          (AlgebraicCycle.pullbackClosed (quotBundleImmersion e I) z -
            AlgebraicCycle.pullbackBundle (quotTrivialization ι I) w') := by
      rw [hsub, hzmap, pullbackBundle_map_quotImmersion_of_ker e I hker (dimX : _ → ℤ)
        (dimE : _ → ℤ) w']
    rw [key]
    refine totalRationalRelations_map_closedImmersion_supported (quotBundleImmersion e I)
      (DimensionFunction.comapClosedImmersion (quotBundleImmersion e I) dimE) dimE ?_
    exact ⟨_, hw'rel, rfl⟩

end Supported

section Main

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {ι : Type u} [Finite ι]

/-- **Fulton, *Intersection Theory*, Proposition 1.9, affine case with supports.**  Let `I` be an
ideal of a Noetherian ring `R` with the universal dimension formula, and let `z` be a cycle on the
total space `Spec (MvPolynomial ι R)` of the trivial bundle of rank `#ι`, concentrated in dimension
`j` and supported over the closed subset `V(I)`.  Then `z` is the flat pullback of a cycle `w`
concentrated in dimension `j - #ι` and supported in `V(I)`, modulo a rational relation which is
itself supported over `V(I)`.  This is the input of the Noetherian induction which globalises the
homotopy property to an arbitrary scheme. -/
theorem exists_pullback_supported (hdim : HasUniversalDimensionFormula R)
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι R))))
    (I : Ideal R) (j : ℤ) (z : AlgebraicCycle (Spec (CommRingCat.of (MvPolynomial ι R))) ℚ)
    (hz : ∀ q, dimE q ≠ j → (z : _ → ℚ) q = 0)
    (hsupp : z.SupportedIn
      (PrimeSpectrum.zeroLocus (I.map (MvPolynomial.C : R →+* MvPolynomial ι R) : Set _))) :
    ∃ w : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ,
      (∀ x, dimX x ≠ j - (Nat.card ι : ℤ) → (w : _ → ℚ) x = 0) ∧
      w.SupportedIn (PrimeSpectrum.zeroLocus (I : Set R)) ∧
      z - AlgebraicCycle.pullbackBundle
          (AlgEquiv.refl : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R) w ∈
        supportedRelations (Spec (CommRingCat.of (MvPolynomial ι R))) dimE
          (PrimeSpectrum.zeroLocus (I.map (MvPolynomial.C : R →+* MvPolynomial ι R) : Set _)) := by
  have hrangeE := range_quotBundleImmersion_base_refl (ι := ι) I
  have hrangeX := range_quotImmersion_base I
  obtain ⟨w, hwdim, hwsupp, hwrel⟩ :=
    exists_pullback_supported_of_ker (AlgEquiv.refl : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R) I
      (ker_quotBundleHom_refl I) (hasUniversalDimensionFormula_quotient hdim I) dimX dimE j z hz
      (by rw [hrangeE]; exact hsupp)
  refine ⟨w, hwdim, ?_, ?_⟩
  · rw [← hrangeX]
    exact hwsupp
  · rw [← hrangeE]
    exact hwrel

end Main

end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
