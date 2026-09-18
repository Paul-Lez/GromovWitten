/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackDescent

/-!
# Descent of the affine-bundle flat pullback to rational Chow groups

`ChernClasses.lean` builds the flat pullback `cyclesOfDimension.flatPullbackBundle` of
dimension-graded rational cycles along an affine vector bundle `E = Spec A → Spec R = X`, and
`BundlePullbackDescent.lean` proves the principal-divisor comparison `π^* div(f) = div(π^* f)`
for the generators whose integral closed subscheme is the *whole* base.  This file supplies the
missing presentation of a general generator and concludes the descent, producing the flat
pullback on rational Chow groups.

## The restriction of a trivialized bundle over a closed subscheme of the base

For a prime `p` of `R` the closed subscheme `Spec (R ⧸ p)` carries the restricted bundle
`Spec (MvPolynomial ι (R ⧸ p))`, a trivialized affine vector bundle of the same rank:

* `VectorBundle.quotBundleHom`: the surjection `A → MvPolynomial ι (R ⧸ p)` obtained by reducing
  the coefficients of a polynomial modulo `p`, with `VectorBundle.quotBundleHom_surjective`,
  `VectorBundle.quotBundleHom_algebraMap` (the base-change square commutes) and
  `VectorBundle.ker_quotBundleHom` (its kernel is the extended ideal `p · A`).
* `VectorBundle.comap_quotBundleHom_map_algebraMap`: the contraction of an extended prime of the
  restricted bundle is the extended contraction.  This is the ideal-theoretic heart of the file.
* `VectorBundle.quotImmersion`, `VectorBundle.quotBundleImmersion`: the two closed immersions
  `Spec (R ⧸ p) → Spec R` and `Spec (MvPolynomial ι (R ⧸ p)) → Spec A`.
* `VectorBundle.quotBundleImmersion_base_bundlePoint`: the generic point of the preimage of a
  point of `Spec (R ⧸ p)` maps to the generic point of the preimage of its image, that is
  `E_V ↪ E` identifies `E_V` with the preimage of `V`.

## Compatibility of the bundle pullback with closed-immersion pushforward

* `VectorBundle.pullbackBundle_map_quotImmersion`: `π^* ∘ V_* = (E_V)_* ∘ π_V^*` on cycles, for
  arbitrary weights.  Both pushforwards are along closed immersions, so all multiplicities are
  one, and the computation is the point-set bijection above.

## The descent

* `VectorBundle.pullbackBundle_divisor_mem_totalRationalRelations`: the flat pullback of *every*
  principal-divisor generator of the base is a rational-equivalence relation on the total space.
  An arbitrary integral closed subscheme of `Spec R` is presented as `Spec (R ⧸ p)` by
  `IsClosedImmersion.Spec_iff`, the principal divisor is transported along that isomorphism by
  `map_isIso_principalCycle`, and `VectorBundle.pullbackBundle_principalCycle` is applied to the
  Noetherian domain `R ⧸ p`.
* `VectorBundle.totalRationalRelations_pullbackBundle`: consequently the flat pullback carries
  the canonical span of principal divisors into the canonical span on the total space.
* `VectorBundle.ofBundle` and `VectorBundle.chowPullbackBundle`: the resulting `DescendingMap`
  and the induced map of rational Chow groups `A_i(Spec R) →ₗ[ℚ] A_{i+r}(E)`, with
  `VectorBundle.chowPullbackBundle_quotientMap` identifying it on cycle classes.
* `VectorBundle.chowEquivOfAlgEquiv_comp_chowPullbackBundle`: the Chow pullback is invariant
  under isomorphism of bundles, hence independent of the chosen trivialization.

The base `Spec R` is *not* assumed irreducible or reduced: only `R` Noetherian and `ι` finite.
Every generator lives on an integral closed subscheme, which is handled by the presentation
above.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Two invariance lemmas for the residue-degree pushforward -/

/-- The residue-degree pushforward with the pulled-back weight depends only on the morphism, not
on the quasi-compactness instance used to form it.  This allows a closed immersion to be replaced
by an equal composite inside a pushforward. -/
theorem AlgebraicCycle.map_congr_hom {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [_root_.AlgebraicGeometry.QuasiCompact f] [_root_.AlgebraicGeometry.QuasiCompact f']
    (hff : f = f') (wy : Y → ℤ) (c : AlgebraicCycle X ℚ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f (fun x ↦ wy (f.base x)) wy c =
      _root_.AlgebraicGeometry.AlgebraicCycle.map f' (fun x ↦ wy (f'.base x)) wy c := by
  subst hff
  rfl

/-- The residue-degree pushforward along an isomorphism of integral locally Noetherian schemes
carries a principal cycle to the principal cycle of the transported rational function.  Pushing
forward along an isomorphism is flat pullback along its inverse, and flat pullback along a
dominant open immersion preserves principal divisors. -/
theorem map_isIso_principalCycle {X Y : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral X] [_root_.AlgebraicGeometry.IsIntegral Y]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
    (ε : X ≅ Y) (dY : DimensionFunction Y) (f : X.functionField) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map ε.hom
        (fun x ↦ (dY : Y → ℤ) (ε.hom.base x)) (dY : Y → ℤ) (X.principalCycle f) =
      Y.principalCycle (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap ε.inv f) := by
  rw [principalCycle_pullbackOpen ε.inv f]
  exact (AlgebraicCycle.pullbackOpen_eq_map_of_isIso ε.symm dY
    (DimensionFunction.comapClosedImmersion ε.hom dY) (X.principalCycle f)).symm

namespace VectorBundle

/-! ## The restriction of a trivialized affine bundle to a closed subscheme of the base -/

/-- The tautological trivialization of the restriction of a rank-`ι` affine vector bundle over
the closed subscheme `Spec (R ⧸ p)` of the base: the restricted bundle *is* the polynomial
algebra `MvPolynomial ι (R ⧸ p)`. -/
noncomputable abbrev quotTrivialization (ι : Type u) {R : Type u} [CommRing R] (p : Ideal R) :
    MvPolynomial ι (R ⧸ p) ≃ₐ[R ⧸ p] MvPolynomial ι (R ⧸ p) :=
  AlgEquiv.refl

section Restriction

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R) (p : Ideal R)

/-- The surjection of the coordinate algebra of a trivialized affine vector bundle onto the
coordinate algebra of its restriction over the closed subscheme `Spec (R ⧸ p)`: trivialize, then
reduce the coefficients of the resulting polynomial modulo `p`. -/
noncomputable def quotBundleHom : A →+* MvPolynomial ι (R ⧸ p) :=
  (MvPolynomial.map (Ideal.Quotient.mk p)).comp
    (e.toRingEquiv : A ≃+* MvPolynomial ι R).toRingHom

/-- The coordinate algebra of the restricted bundle is a quotient of the coordinate algebra of
the bundle. -/
theorem quotBundleHom_surjective : Function.Surjective (quotBundleHom e p) :=
  (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp
    (e.toRingEquiv : A ≃+* MvPolynomial ι R).surjective

/-- The base-change square commutes: restricting the bundle over `Spec (R ⧸ p)` is compatible
with the two structure maps. -/
theorem quotBundleHom_algebraMap (r : R) :
    quotBundleHom e p (algebraMap R A r) =
      algebraMap (R ⧸ p) (MvPolynomial ι (R ⧸ p)) (Ideal.Quotient.mk p r) := by
  change MvPolynomial.map (Ideal.Quotient.mk p) (e (algebraMap R A r)) = _
  rw [e.commutes, MvPolynomial.algebraMap_eq, MvPolynomial.map_C, MvPolynomial.algebraMap_eq]

/-- The kernel of the restriction map is the extended ideal `p · A`: the kernel of the reduction
of coefficients is the extension of `p` to the polynomial algebra. -/
theorem ker_quotBundleHom [hp : p.IsPrime] :
    RingHom.ker (quotBundleHom e p) = Ideal.map (algebraMap R A) p := by
  rw [quotBundleHom, ← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker]
  exact (map_algebraMap_eq_comap e ⟨p, hp⟩).symm

/-- Contracting an extended ideal of the restricted bundle along the restriction map gives the
extension of the contracted ideal.  This is the statement that the restricted bundle is exactly
the preimage of the closed subscheme `Spec (R ⧸ p)`, at the level of the points carrying the
flat pullback of a cycle. -/
theorem comap_quotBundleHom_map_algebraMap [p.IsPrime] (P : Ideal (R ⧸ p)) :
    Ideal.comap (quotBundleHom e p)
        (Ideal.map (algebraMap (R ⧸ p) (MvPolynomial ι (R ⧸ p))) P) =
      Ideal.map (algebraMap R A) (Ideal.comap (Ideal.Quotient.mk p) P) := by
  have hPQ : Ideal.map (Ideal.Quotient.mk p) (Ideal.comap (Ideal.Quotient.mk p) P) = P :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P
  have hcomp : (quotBundleHom e p).comp (algebraMap R A) =
      (algebraMap (R ⧸ p) (MvPolynomial ι (R ⧸ p))).comp (Ideal.Quotient.mk p) :=
    RingHom.ext fun r ↦ quotBundleHom_algebraMap e p r
  have hmapK : Ideal.map (quotBundleHom e p)
      (Ideal.map (algebraMap R A) (Ideal.comap (Ideal.Quotient.mk p) P)) =
      Ideal.map (algebraMap (R ⧸ p) (MvPolynomial ι (R ⧸ p))) P := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hPQ]
  have hpQ : p ≤ Ideal.comap (Ideal.Quotient.mk p) P := by
    intro x hx
    change Ideal.Quotient.mk p x ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact P.zero_mem
  rw [← hmapK, Ideal.comap_map_of_surjective _ (quotBundleHom_surjective e p),
    ← RingHom.ker_eq_comap_bot, ker_quotBundleHom e p, sup_eq_left]
  exact Ideal.map_mono hpQ

/-- The closed immersion of the closed subscheme `Spec (R ⧸ p)` into the affine base. -/
noncomputable abbrev quotImmersion :
    Spec (CommRingCat.of (R ⧸ p)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))

/-- The quotient by a prime is a closed subscheme of the affine base. -/
instance isClosedImmersion_quotImmersion :
    _root_.AlgebraicGeometry.IsClosedImmersion (quotImmersion p) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The closed immersion of the restricted bundle into the total space of the bundle. -/
noncomputable abbrev quotBundleImmersion :
    Spec (CommRingCat.of (MvPolynomial ι (R ⧸ p))) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (quotBundleHom e p))

/-- The restriction of the bundle is a closed subscheme of the total space, because the
restriction of coordinate algebras is surjective. -/
instance isClosedImmersion_quotBundleImmersion :
    _root_.AlgebraicGeometry.IsClosedImmersion (quotBundleImmersion e p) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ (quotBundleHom_surjective e p)

/-- The generic point of the preimage of a point of the closed subscheme, computed inside the
restricted bundle, is the generic point of the preimage of its image, computed inside the whole
bundle.  This identifies the restricted bundle with the preimage of the closed subscheme on the
points which carry a flat pullback. -/
theorem quotBundleImmersion_base_bundlePoint [p.IsPrime]
    (x : ↥(Spec (CommRingCat.of (R ⧸ p)))) :
    (quotBundleImmersion e p).base (bundlePoint (quotTrivialization ι p) x) =
      bundlePoint e ((quotImmersion p).base x) :=
  PrimeSpectrum.ext
    (comap_quotBundleHom_map_algebraMap e p (x : PrimeSpectrum (R ⧸ p)).asIdeal)

/-! ## Compatibility of the bundle pullback with closed-immersion pushforward -/

/-- The flat pullback of a cycle pushed forward from the closed subscheme `Spec (R ⧸ p)` vanishes
at every point of the total space which is not the image of a generic point of a fibre of the
restricted bundle. -/
theorem pullbackBundle_map_quotImmersion_apply_eq_zero [p.IsPrime]
    (wX : ↥(Spec (CommRingCat.of R)) → ℤ)
    (c : AlgebraicCycle (Spec (CommRingCat.of (R ⧸ p))) ℚ)
    {y : ↥(Spec (CommRingCat.of A))}
    (hy : ∀ x, y ≠ (quotBundleImmersion e p).base (bundlePoint (quotTrivialization ι p) x)) :
    AlgebraicCycle.pullbackBundle e
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (quotImmersion p)
          (fun z ↦ wX ((quotImmersion p).base z)) wX c) y = 0 := by
  by_cases hmem : y ∈ Set.range (bundlePoint e)
  · obtain ⟨w, rfl⟩ := hmem
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint]
    refine AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ ?_
    rintro ⟨x, rfl⟩
    exact hy x (quotBundleImmersion_base_bundlePoint e p x).symm
  · exact AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e _ hmem

/-- The flat pullback along an affine vector bundle commutes with the pushforward along the
closed immersion of `Spec (R ⧸ p)`: `π^* ∘ V_* = (E_V)_* ∘ π_V^*`.  Both pushforwards use the
pulled-back weight, so every multiplicity is one and the identity is the point-set bijection
between the generic points of the fibres of the restricted bundle and the generic points of the
fibres over the closed subscheme. -/
theorem pullbackBundle_map_quotImmersion [p.IsPrime]
    (wX : ↥(Spec (CommRingCat.of R)) → ℤ) (wE : ↥(Spec (CommRingCat.of A)) → ℤ)
    (c : AlgebraicCycle (Spec (CommRingCat.of (R ⧸ p))) ℚ) :
    AlgebraicCycle.pullbackBundle e
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (quotImmersion p)
          (fun z ↦ wX ((quotImmersion p).base z)) wX c) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (quotBundleImmersion e p)
        (fun z ↦ wE ((quotBundleImmersion e p).base z)) wE
        (AlgebraicCycle.pullbackBundle (quotTrivialization ι p) c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  dsimp only
  by_cases hy : y ∈ Set.range (quotBundleImmersion e p).base
  · obtain ⟨z, rfl⟩ := hy
    rw [AlgebraicCycle.map_closedImmersion_apply_image (quotBundleImmersion e p) wE
      (AlgebraicCycle.pullbackBundle (quotTrivialization ι p) c) z]
    by_cases hz : z ∈ Set.range (bundlePoint (quotTrivialization ι p))
    · obtain ⟨x, rfl⟩ := hz
      rw [quotBundleImmersion_base_bundlePoint e p x,
        AlgebraicCycle.pullbackBundle_apply_bundlePoint e _ ((quotImmersion p).base x),
        AlgebraicCycle.map_closedImmersion_apply_image (quotImmersion p) wX c x,
        AlgebraicCycle.pullbackBundle_apply_bundlePoint (quotTrivialization ι p) c x]
    · rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem _ c hz]
      refine pullbackBundle_map_quotImmersion_apply_eq_zero e p wX c ?_
      intro x hx
      exact hz ⟨x, ((quotBundleImmersion e p).isClosedEmbedding.injective hx).symm⟩
  · rw [AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range
      (quotBundleImmersion e p) wE _ y hy]
    exact pullbackBundle_map_quotImmersion_apply_eq_zero e p wX c fun x hx ↦ hy ⟨_, hx.symm⟩

end Restriction

/-! ## Descent of the flat pullback to rational Chow groups -/

section Descent

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [Finite ι] (e : A ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A)))

/-- The flat pullback along an affine vector bundle of the principal divisor of a rational
function on an arbitrary integral closed subscheme of the base is a rational-equivalence relation
on the total space.  The integral closed subscheme is presented as `Spec (R ⧸ p)` for a prime `p`
(`IsClosedImmersion.Spec_iff`), its restricted bundle is `Spec (MvPolynomial ι (R ⧸ p))`, and the
comparison `π^* div(f) = div(π^* f)` over the Noetherian domain `R ⧸ p` is
`VectorBundle.pullbackBundle_principalCycle`. -/
theorem pullbackBundle_divisor_mem_totalRationalRelations
    (g : RationalFunctionGenerator (Spec (CommRingCat.of R))) :
    AlgebraicCycle.pullbackBundle e (g.divisor dimX) ∈
      totalRationalRelations (Spec (CommRingCat.of A)) dimE := by
  obtain ⟨p, ε, hfac⟩ :=
    _root_.AlgebraicGeometry.IsClosedImmersion.Spec_iff.1 g.subspace.isClosedImmersion
  have hint : _root_.AlgebraicGeometry.IsIntegral (Spec (CommRingCat.of (R ⧸ p))) :=
    _root_.AlgebraicGeometry.IsIntegral.of_isIso ε.hom
  have hdom : IsDomain (R ⧸ p) :=
    (_root_.AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of (R ⧸ p))).1 hint
  have hp : p.IsPrime := (Ideal.Quotient.isDomain_iff_prime p).1 hdom
  have hdominant :
      _root_.AlgebraicGeometry.IsDominant
        (GradedCone.projection (R ⧸ p) (MvPolynomial ι (R ⧸ p))) :=
    isDominant_projection (quotTrivialization ι p)
  -- the rational function transported to the presentation `Spec (R ⧸ p)`
  set f' : (Spec (CommRingCat.of (R ⧸ p))).functionFieldˣ :=
    Units.map (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap ε.inv).toMonoidHom
      g.function with hf'
  -- the presentation of the generator's divisor
  have h1 : g.divisor dimX =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (ε.hom ≫ quotImmersion p)
        (fun x ↦ (dimX : _ → ℤ) ((ε.hom ≫ quotImmersion p).base x)) (dimX : _ → ℤ)
        (g.subspace.scheme.principalCycle (g.function : _)) :=
    AlgebraicCycle.map_congr_hom hfac (dimX : _ → ℤ) _
  have h2 := AlgebraicCycle.map_comp_of_isClosedImmersion ε.hom (quotImmersion p)
    ((DimensionFunction.comapClosedImmersion (quotImmersion p) dimX : _ → ℤ))
    (dimX : _ → ℤ) (g.subspace.scheme.principalCycle (g.function : _))
  have h3 := map_isIso_principalCycle ε
    (DimensionFunction.comapClosedImmersion (quotImmersion p) dimX)
    (g.function : g.subspace.scheme.functionField)
  rw [h3] at h2
  have h4 : g.divisor dimX =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (quotImmersion p)
        (fun z ↦ (dimX : _ → ℤ) ((quotImmersion p).base z)) (dimX : _ → ℤ)
        ((Spec (CommRingCat.of (R ⧸ p))).principalCycle (f' : _)) := h1.trans h2.symm
  -- the comparison on the restricted bundle
  have h5 := pullbackBundle_map_quotImmersion e p (dimX : _ → ℤ) (dimE : _ → ℤ)
    ((Spec (CommRingCat.of (R ⧸ p))).principalCycle (f' : _))
  have h6 := pullbackBundle_principalCycle (quotTrivialization ι p) (f' : _)
  rw [h6] at h5
  -- the resulting generator on the total space
  refine Submodule.subset_span
    ⟨⟨{ scheme := Spec (CommRingCat.of (MvPolynomial ι (R ⧸ p)))
        inclusion := quotBundleImmersion e p },
      Units.map (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
        (GradedCone.projection (R ⧸ p) (MvPolynomial ι (R ⧸ p)))).toMonoidHom f'⟩, ?_⟩
  rw [h4, h5]
  rfl

/-- The flat pullback along an affine vector bundle carries the canonical span of principal
divisors on the base into the canonical span on the total space. -/
theorem totalRationalRelations_pullbackBundle :
    Submodule.map (AlgebraicCycle.pullbackBundleLinear e)
        (totalRationalRelations (Spec (CommRingCat.of R)) dimX) ≤
      totalRationalRelations (Spec (CommRingCat.of A)) dimE := by
  rw [totalRationalRelations, Submodule.map_span, Submodule.span_le]
  rintro z ⟨c, ⟨g, rfl⟩, rfl⟩
  exact pullbackBundle_divisor_mem_totalRationalRelations e dimX dimE g

variable (i : ℤ)

/-- The dimension-graded flat pullback along a rank-`r` affine vector bundle, together with its
proved preservation of the canonical rational-equivalence subspaces.  The grading shift `i ↦ i+r`
is the proved polynomial Krull-dimension formula of `ChernClasses.lean`. -/
noncomputable def ofBundle
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
    (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ))) :
    RX.DescendingMap RE where
  onCycles := cyclesOfDimension.flatPullbackBundle e dimX dimE i
  maps_relations := by
    cases RX
    cases RE
    intro z hz
    change AlgebraicCycle.pullbackBundle e z.1 ∈
      totalRationalRelations (Spec (CommRingCat.of A)) dimE
    exact totalRationalRelations_pullbackBundle e dimX dimE ⟨z.1, hz, rfl⟩

/-- Flat pullback along an affine vector bundle of rank `r` on dimension-graded rational Chow
groups, `A_i(Spec R) →ₗ[ℚ] A_{i+r}(E)`.  This is the descent of
`cyclesOfDimension.flatPullbackBundle` through rational equivalence. -/
noncomputable def chowPullbackBundle
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
    (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ))) :
    RX.ChowGroup →ₗ[ℚ] RE.ChowGroup :=
  RationalEquivalenceSystem.DescendingMap.inducedMap RX (ofBundle e dimX dimE i RX RE)

/-- The Chow-group flat pullback along an affine vector bundle is induced by the actual flat
pullback of dimension-graded cycles. -/
@[simp]
theorem chowPullbackBundle_quotientMap
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
    (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ)))
    (z : cyclesOfDimension (Spec (CommRingCat.of R)) dimX i) :
    chowPullbackBundle e dimX dimE i RX RE (RX.quotientMap z) =
      RE.quotientMap (cyclesOfDimension.flatPullbackBundle e dimX dimE i z) :=
  rfl

end Descent

/-! ## Invariance of the Chow pullback under isomorphism of bundles -/

section BundleIso

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {A A' : Type u}
  [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A'] {ι : Type u} [Finite ι]
  (φ : A ≃ₐ[R] A') (e : A ≃ₐ[R] MvPolynomial ι R) (e' : A' ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A)))
  (dimE' : DimensionFunction (Spec (CommRingCat.of A'))) (i : ℤ)
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
  (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ)))
  (RE' : RationalEquivalenceSystem (Spec (CommRingCat.of A')) dimE' (i + (Nat.card ι : ℤ)))

/-- The Chow-group flat pullback along an affine vector bundle is invariant under isomorphism of
bundles: composing with the isomorphism of rational Chow groups induced by an isomorphism of
coordinate algebras turns one bundle pullback into the other.  In particular the pullback does
not depend on the chosen trivialization. -/
theorem chowEquivOfAlgEquiv_comp_chowPullbackBundle :
    (chowEquivOfAlgEquiv φ RE RE').toLinearMap.comp
        (chowPullbackBundle e dimX dimE i RX RE) =
      chowPullbackBundle e' dimX dimE' i RX RE' := by
  apply LinearMap.ext
  rintro ⟨z⟩
  exact congrArg (fun w ↦ RE'.quotientMap w)
    (cyclesOfDimension.flatPullbackOpen_flatPullbackBundle φ e e' dimX dimE dimE' i z)

end BundleIso

end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
