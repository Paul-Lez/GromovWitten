/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ResolvedCone
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyKey

/-!
# The virtual fundamental class of an obstruction theory, in the affine model

Let `X = Spec (R ⧸ I)` be the affine closed subscheme of `Spec R` cut out by `I` (with `R` a
Noetherian `k`-algebra), let `L = conormalComplex k R I` be the conormal complex and let
`φ : E ⟶ L` be a chain map of two-term complexes whose degree-zero term `E⁻¹` is finite free.
`VirtualFundamentalClass/ResolvedCone.lean` builds the resolved cone `C(E) ⊆ E₁` as a closed
subscheme of the vector bundle `E₁ = Spec Sym(E⁻¹)` of rank `a = rk E⁻¹`.  This file turns it
into the Behrend--Fantechi virtual fundamental class `[X]^vir = 0^!_{E₁}[C(E)] ∈ A_{vd}(X)`,
where `vd = rk E⁰ - rk E⁻¹` is the expected dimension.

## The construction

* `bundleRank φ = a`, `virtualDimension φ = vd` and `coneDegree φ = vd + a`; the trivialisation
  `trivialization φ : Sym(E⁻¹) ≃ₐ MvPolynomial _ (R ⧸ I)` of `E₁` is
  `VectorBundle.symTrivialization` for the chosen basis of `E⁻¹`.
* `resolvedConeCycle φ dimE : Z_{vd+a}(E₁)` is the dimension-`(vd+a)` part of the pushforward
  along the closed immersion `C(E) ↪ E₁` of the fundamental cycle of `C(E)`, and
  `resolvedConeClass φ dimE RE` is its rational-equivalence class.
  `resolvedConeCycle_eq_properPushforward_fundamental` shows that under purity — every generic
  point of `C(E)` has dimension `vd + a`, the conclusion of
  `VirtualFundamentalClass/ResolvedConeDimension.lean` — no truncation takes place: the cycle is
  the graded fundamental cycle of `C(E)` pushed forward.
* `exists_virtualClass` produces a class on `X` pulling back to `resolvedConeClass`, from the
  surjectivity of the flat pullback (Fulton, Prop. 1.9) proved in
  `IntersectionTheory/BundleHomotopy.lean` and `IntersectionTheory/BundleHomotopyKey.lean`.
* `virtualClassQuot` is the resulting canonical class in `A_{vd}(X) ⧸ ker π^*`, with no
  injectivity hypothesis at all.
* `virtualClass hhom hinj : A_{vd}(X)` is the virtual fundamental class itself, characterised by
  `pullback_virtualClass` and `virtualClass_unique`.

## The two explicit hypotheses

`virtualClass` carries exactly two hypotheses beyond the geometric data, and neither is proved
here:

* `hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE`, homogeneity of
  principal divisors on `E₁`, the hypothesis under which the localisation sequence of
  `IntersectionTheory/LocalizationExact.lean` and the surjectivity of `π^*` are proved;
* `hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)`, injectivity of `π^*`.  This is
  the remaining half of homotopy invariance (Fulton, Thm. 3.3(a)); its proof needs Chern classes
  of vector bundles, which are not available in this development.

Purity is a hypothesis only of `resolvedConeCycle_eq_properPushforward_fundamental`; the class
itself is defined without it.

## The expected dimension and the proper point

`virtualDimension_eq` records that the expected dimension is `rk E⁰ - rk E⁻¹`, which is
`PicardCriteria.virtualRank E` (`virtualDimension_eq_virtualRank`) and is therefore a
chain-homotopy invariant of a perfect obstruction theory
(`virtualDimension_eq_of_homotopyEquivalence`).

The last part of the file checks the construction against the proper point.  If `E⁻¹ = 0` then
`algebraMap_bundleRing_surjective` and the vertex of the normal cone give
`ideal_eq_bot : ResolvedCone.ideal φ = ⊥`, so `C(E) = E₁ = X` and `isIso_toBundle` says that
`C(E) ↪ E₁` is an isomorphism.  If moreover `E⁰ = 0` and `X` is a reduced point, then
`virtualClass_eq_fundamental` identifies the virtual class with the class of the fundamental
cycle of `X`, and `virtualClass_point` specialises this to `R` a field with `I = ⊥`.
-/

universe u

-- The coordinate ring of `C ×_X E₀` is a tensor product whose left factor is itself a quotient
-- of a Rees algebra; synthesising `CommSemiring`/`CommRing` for it needs one more level of
-- pending instance problems than the default.
set_option maxSynthPendingDepth 5

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.VirtualClass

open IntersectionTheory hiding Scheme AlgebraicCycle
open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]

/-! ## Ranks, the expected dimension and the trivialisation of `E₁` -/

/-- The rank `a = rk E⁻¹` of the vector bundle `E₁ = Spec Sym(E⁻¹)`, read off from the basis of
`E⁻¹` chosen to trivialise it. -/
noncomputable abbrev bundleRank
    (_φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) : ℕ :=
  Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero)

/-- The virtual dimension `vd = rk E⁰ - rk E⁻¹` of the obstruction theory. -/
noncomputable abbrev virtualDimension
    (_φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) : ℤ :=
  (Module.finrank (R ⧸ I) E.degreeOne : ℤ) - (Module.finrank (R ⧸ I) E.degreeZero : ℤ)

/-- The degree `vd + a` in which the resolved-cone cycle lives inside `E₁`. -/
noncomputable abbrev coneDegree
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) : ℤ :=
  virtualDimension φ + (bundleRank φ : ℤ)

/-- The chosen trivialisation `Sym(E⁻¹) ≃ MvPolynomial _ (R ⧸ I)` of the vector bundle `E₁`. -/
noncomputable abbrev trivialization
    (_φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    SymmetricAlgebra (R ⧸ I) E.degreeZero ≃ₐ[R ⧸ I]
      MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero) (R ⧸ I) :=
  VectorBundle.symTrivialization (R ⧸ I) E.degreeZero

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The virtual dimension of the obstruction theory is the virtual rank of the complex `E`. -/
theorem virtualDimension_eq_virtualRank
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    virtualDimension φ = PicardCriteria.virtualRank E :=
  rfl

omit [IsNoetherianRing R] in
/-- The rank of `E₁` is the rank of the module `E⁻¹`. -/
theorem bundleRank_eq_finrank [Nontrivial (R ⧸ I)]
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    bundleRank φ = Module.finrank (R ⧸ I) E.degreeZero :=
  VectorBundle.card_chooseBasisIndex (R ⧸ I) E.degreeZero

omit [IsNoetherianRing R] in
/-- The resolved-cone cycle lives in dimension `rk E⁰`: the expected dimension `vd` of `X` plus
the rank `a` of the bundle `E₁`. -/
theorem coneDegree_eq_finrank [Nontrivial (R ⧸ I)]
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    coneDegree φ = (Module.finrank (R ⧸ I) E.degreeOne : ℤ) := by
  rw [coneDegree, bundleRank_eq_finrank φ, virtualDimension]
  ring

/-! ## Noetherian hypotheses -/

/-- The symmetric algebra of a finite free module over a Noetherian ring is Noetherian: it is a
polynomial ring in finitely many variables. -/
instance isNoetherianRing_symmetricAlgebra (S : Type u) [CommRing S] [IsNoetherianRing S]
    (M : Type u) [AddCommGroup M] [Module S M] [Module.Free S M] [Module.Finite S M] :
    IsNoetherianRing (SymmetricAlgebra S M) :=
  isNoetherianRing_of_ringEquiv (MvPolynomial (Module.Free.ChooseBasisIndex S M) S)
    (VectorBundle.symTrivialization S M).symm.toRingEquiv

/-! ## The resolved-cone cycle and class -/

variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-- The certified dimension grading of the resolved cone `C(E)`, pulled back along the closed
immersion `C(E) ↪ E₁`.  Closed immersions preserve heights, so no choice is involved. -/
noncomputable abbrev coneDimension
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) :
    DimensionFunction (ResolvedCone.scheme φ) :=
  DimensionFunction.comapClosedImmersion (ResolvedCone.toBundle φ) dimE

/-- **The resolved-cone cycle** `[C(E)] ∈ Z_{vd+a}(E₁)`: the dimension-`(vd+a)` part of the
pushforward along the closed immersion `C(E) ↪ E₁` of the fundamental cycle of `C(E)`. -/
noncomputable def resolvedConeCycle (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) :
    cyclesOfDimension (ResolvedCone.bundleSpace φ) dimE (coneDegree φ) :=
  cyclesOfDimension.project
    (AlgebraicCycle.map (ResolvedCone.toBundle φ) (coneDimension φ dimE) dimE
      (ResolvedCone.scheme φ).fundamentalCycle)

/-- **Purity implies that the resolved-cone cycle is the graded fundamental cycle.**

The hypothesis `hpure` — every generic point of `C(E)` has dimension `vd + a` — is the conclusion
of the purity theorem of `VirtualFundamentalClass/ResolvedConeDimension.lean`; it is an explicit
hypothesis here so that the two files stay independent. -/
theorem resolvedConeCycle_eq_properPushforward_fundamental
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (hpure : ∀ x : ResolvedCone.scheme φ, IsMax x → coneDimension φ dimE x = coneDegree φ) :
    resolvedConeCycle φ dimE =
      cyclesOfDimension.properPushforward (ResolvedCone.toBundle φ)
        (cyclesOfDimension.fundamental hpure) := by
  have h := cyclesOfDimension.project_coe
    (cyclesOfDimension.properPushforward (dimension := coneDimension φ dimE)
      (dimensionY := dimE) (ResolvedCone.toBundle φ) (cyclesOfDimension.fundamental hpure))
  exact h

/-! ## The virtual class -/

variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
  (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX (virtualDimension φ))
  (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (coneDegree φ))

/-- The flat pullback `π^* : A_{vd}(X) → A_{vd+a}(E₁)` along the projection of the vector bundle
`E₁ = Spec Sym(E⁻¹)`, in the chosen trivialisation. -/
noncomputable abbrev bundlePullback : RX.ChowGroup →ₗ[ℚ] RE.ChowGroup :=
  VectorBundle.chowPullbackBundle (trivialization φ) dimX dimE (virtualDimension φ) RX RE

/-- **The resolved-cone class** `[C(E)] ∈ A_{vd+a}(E₁)`. -/
noncomputable def resolvedConeClass : RE.ChowGroup :=
  RE.quotientMap (resolvedConeCycle φ dimE)

/-- **Existence of the virtual class.**  The resolved-cone class is a flat pullback from the
base, because `π^*` is surjective (Fulton, Prop. 1.9, proved in
`IntersectionTheory/BundleHomotopy.lean` and `IntersectionTheory/BundleHomotopyKey.lean`).  The
hypothesis `hhom` is exactly the one carried by
`VectorBundle.chowPullbackBundle_surjective'`. -/
theorem exists_virtualClass
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE) :
    ∃ α : RX.ChowGroup, bundlePullback φ dimX dimE RX RE α = resolvedConeClass φ dimE RE :=
  VectorBundle.chowPullbackBundle_surjective' (trivialization φ) dimX dimE (virtualDimension φ)
    RX RE hhom (resolvedConeClass φ dimE RE)

/-- **The canonical virtual class**, an element of `A_{vd}(X) ⧸ ker π^*`.  This is the virtual
class without any injectivity hypothesis: it is the unique preimage of the resolved-cone class
under the isomorphism `A_{vd}(X) ⧸ ker π^* ≃ A_{vd+a}(E₁)` of
`VectorBundle.chowQuotientEquiv'`. -/
noncomputable def virtualClassQuot
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE) :
    RX.ChowGroup ⧸ LinearMap.ker (bundlePullback φ dimX dimE RX RE) :=
  (VectorBundle.chowQuotientEquiv' (trivialization φ) dimX dimE (virtualDimension φ)
    RX RE hhom).symm (resolvedConeClass φ dimE RE)

/-- The canonical virtual class is characterised by mapping to the resolved-cone class. -/
@[simp]
theorem chowQuotientEquiv_virtualClassQuot
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE) :
    VectorBundle.chowQuotientEquiv' (trivialization φ) dimX dimE (virtualDimension φ) RX RE hhom
        (virtualClassQuot φ dimX dimE RX RE hhom) =
      resolvedConeClass φ dimE RE :=
  (VectorBundle.chowQuotientEquiv' (trivialization φ) dimX dimE (virtualDimension φ)
    RX RE hhom).apply_symm_apply _

/-- **The virtual fundamental class** `[X]^vir ∈ A_{vd}(X)` of the obstruction theory `φ`:
the Gysin pullback `0^!_{E₁}[C(E)]` of the resolved-cone class along the zero section of `E₁`.

Two inputs are explicit hypotheses and are documented as such: `hhom` (homogeneity of principal
divisors on `E₁`, the hypothesis of the localisation sequence) and `hinj` (injectivity of `π^*`,
the remaining half of homotopy invariance; see `VectorBundle.zeroSectionGysin'`). -/
noncomputable def virtualClass
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) : RX.ChowGroup :=
  VectorBundle.zeroSectionGysin' (trivialization φ) dimX dimE (virtualDimension φ)
    RX RE hhom hinj (resolvedConeClass φ dimE RE)

/-- **The defining property of the virtual class**: it pulls back to the resolved-cone class. -/
@[simp]
theorem pullback_virtualClass
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) :
    bundlePullback φ dimX dimE RX RE (virtualClass φ dimX dimE RX RE hhom hinj) =
      resolvedConeClass φ dimE RE :=
  VectorBundle.pullback_zeroSectionGysin' (trivialization φ) dimX dimE (virtualDimension φ)
    RX RE hhom hinj (resolvedConeClass φ dimE RE)

/-- **Uniqueness of the virtual class**: any class pulling back to the resolved-cone class is
the virtual class. -/
theorem eq_virtualClass_of_pullback_eq
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) (α : RX.ChowGroup)
    (hα : bundlePullback φ dimX dimE RX RE α = resolvedConeClass φ dimE RE) :
    α = virtualClass φ dimX dimE RX RE hhom hinj :=
  hinj (by rw [hα, pullback_virtualClass])

/-- The virtual class is the unique class with the defining property. -/
theorem virtualClass_unique
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) :
    ∃! α : RX.ChowGroup, bundlePullback φ dimX dimE RX RE α = resolvedConeClass φ dimE RE :=
  ⟨virtualClass φ dimX dimE RX RE hhom hinj, pullback_virtualClass φ dimX dimE RX RE hhom hinj,
    fun α hα => eq_virtualClass_of_pullback_eq φ dimX dimE RX RE hhom hinj α hα⟩

/-! ## The expected dimension -/

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- **The expected dimension.**  The virtual class is by construction an element of
`RX.ChowGroup` for a rational-equivalence system `RX` in degree `virtualDimension φ`, and the
virtual dimension is `rk E⁰ - rk E⁻¹`. -/
theorem virtualDimension_eq :
    virtualDimension φ =
      (Module.finrank (R ⧸ I) E.degreeOne : ℤ) - (Module.finrank (R ⧸ I) E.degreeZero : ℤ) :=
  rfl

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The expected dimension depends only on the chain-homotopy class of a perfect obstruction
theory: it is `PicardCriteria.virtualRank`, which is a homotopy invariant. -/
theorem virtualDimension_eq_of_homotopyEquivalence [Nontrivial (R ⧸ I)]
    {E' : LinearTwoTermComplex (R ⧸ I)}
    (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k R I))
    (hE : PicardCriteria.IsPerfectTwoTerm E) (hE' : PicardCriteria.IsPerfectTwoTerm E')
    (h : LinearTwoTermComplex.HomotopyEquivalence E E') :
    virtualDimension φ = virtualDimension φ' :=
  hE.virtualRank_eq hE' h

/-! ## The rank-zero case: `C(E) = E₁ = X` -/

/-- The chosen basis index of a subsingleton free module over a nontrivial ring is empty. -/
instance isEmpty_chooseBasisIndex_of_subsingleton {S M : Type u} [CommRing S] [Nontrivial S]
    [AddCommGroup M] [Module S M] [Module.Free S M] [Subsingleton M] :
    IsEmpty (Module.Free.ChooseBasisIndex S M) :=
  ⟨fun i => (Module.Free.chooseBasis S M).ne_zero i (Subsingleton.elim _ _)⟩

/-- If an `S`-algebra is isomorphic to `S` then its structure map is surjective. -/
theorem algebraMap_surjective_of_algEquiv {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
    (e : A ≃ₐ[S] S) : Function.Surjective (algebraMap S A) := by
  intro a
  refine ⟨e a, e.injective ?_⟩
  simp

/-- The augmentation `gr_J(A) → A ⧸ J` of the associated graded ring, as a map of
`A ⧸ J`-algebras: the vertex of the normal cone. -/
noncomputable def coneAugmentation (A : Type u) [CommRing A] (J : Ideal A) :
    AffineNormalCone.associatedGradedRing A J →ₐ[A ⧸ J] A ⧸ J :=
  { AffineNormalCone.associatedGradedAugmentation A J with
    commutes' := AffineNormalCone.associatedGradedAugmentation_base A J }

/-- The augmentation of the coordinate ring of `C ×_X E₀`: the vertex of the normal cone
together with the zero section of `E₀`. -/
noncomputable def productAugmentation : ResolvedCone.productRing φ →ₐ[R ⧸ I] R ⧸ I :=
  Algebra.TensorProduct.lift (coneAugmentation R I)
    (SymmetricAlgebra.lift (0 : E.degreeOne →ₗ[R ⧸ I] R ⧸ I)) fun _ _ => Commute.all _ _

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The augmentation retracts the structure map of the coordinate ring of `C ×_X E₀`. -/
theorem productAugmentation_algebraMap (s : R ⧸ I) :
    productAugmentation φ (algebraMap (R ⧸ I) (ResolvedCone.productRing φ) s) = s :=
  (productAugmentation φ).commutes s

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The coordinate ring of `C ×_X E₀` contains the coordinate ring of the base: the normal cone
has a vertex. -/
theorem algebraMap_productRing_injective :
    Function.Injective (algebraMap (R ⧸ I) (ResolvedCone.productRing φ)) :=
  Function.LeftInverse.injective (productAugmentation_algebraMap φ)

variable [hbase : Nontrivial (R ⧸ I)] [Subsingleton E.degreeZero]

/-- In rank zero the coordinate ring of `E₁` is the coordinate ring of the base. -/
noncomputable def bundleRingEquiv : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] R ⧸ I :=
  (trivialization φ).trans (MvPolynomial.isEmptyAlgEquiv (R ⧸ I) _)

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- In rank zero every element of the coordinate ring of `E₁` is a constant. -/
theorem algebraMap_bundleRing_surjective :
    Function.Surjective (algebraMap (R ⧸ I) (ResolvedCone.bundleRing φ)) :=
  algebraMap_surjective_of_algEquiv (bundleRingEquiv φ)

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- **In rank zero the resolved cone is the whole of `E₁`.**  If `E⁻¹ = 0` then `E₁ = X` and the
morphism `C ×_X E₀ → E₁` is the structure map of the base, which is injective because the normal
cone has a vertex; so the ideal of the resolved cone vanishes. -/
theorem ideal_eq_bot : ResolvedCone.ideal φ = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨s, rfl⟩ := algebraMap_bundleRing_surjective φ a
  have h1 : ResolvedCone.productMap φ (algebraMap (R ⧸ I) (ResolvedCone.bundleRing φ) s) = 0 := ha
  rw [AlgHom.commutes] at h1
  have h2 : s = 0 := by
    refine algebraMap_productRing_injective φ ?_
    rw [h1, map_zero]
  rw [h2, map_zero]
  exact Ideal.zero_mem _

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- In rank zero the quotient map defining the resolved cone is bijective. -/
theorem quotientMk_ideal_bijective :
    Function.Bijective (Ideal.Quotient.mk (ResolvedCone.ideal φ)) := by
  refine ⟨?_, Ideal.Quotient.mk_surjective⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ideal_eq_bot φ] at ha
  exact ha

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- **In rank zero the closed immersion `C(E) ↪ E₁` is an isomorphism.** -/
theorem isIso_toBundle : IsIso (ResolvedCone.toBundle φ) := by
  have hiso : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (ResolvedCone.ideal φ))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (quotientMk_ideal_bijective φ)
  exact inferInstanceAs (IsIso (Spec.map _))

/-! ## Consistency with the proper point -/

/-- A certified dimension grading of a one-point scheme is identically zero. -/
theorem dimensionFunction_eq_zero_of_subsingleton {X : Scheme.{u}} [Subsingleton X]
    (d : DimensionFunction X) (x : X) : d x = 0 := by
  have h : Order.height x = 0 := by
    rw [Order.height_eq_zero]
    intro y _
    exact (Subsingleton.elim x y).le
  rw [d.height_eq x] at h
  have hnat : Int.toNat (d x) = 0 := by exact_mod_cast h
  have hnn := d.nonnegative x
  omega

/-- Every point of a one-point scheme is maximal for the specialisation order. -/
theorem isMax_of_subsingleton {X : Scheme.{u}} [Subsingleton X] (x : X) : IsMax x :=
  fun y _ => (Subsingleton.elim y x).le

/-- The isomorphism between the coordinate ring of the resolved cone and the coordinate ring of
`E₁` in the rank-zero case. -/
noncomputable def ringEquivBundleRing :
    ResolvedCone.ring φ ≃+* ResolvedCone.bundleRing φ :=
  (RingEquiv.ofBijective (Ideal.Quotient.mk (ResolvedCone.ideal φ))
    (quotientMk_ideal_bijective φ)).symm

/-- In rank zero the resolved cone has the coordinate ring of the base. -/
noncomputable def ringEquivBase : ResolvedCone.ring φ ≃+* R ⧸ I :=
  (ringEquivBundleRing φ).trans (bundleRingEquiv φ).toRingEquiv

variable [Subsingleton E.degreeOne]

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
include hbase in
/-- A zero obstruction theory has virtual dimension zero. -/
theorem virtualDimension_eq_zero : virtualDimension φ = 0 := by
  rw [virtualDimension_eq, Module.finrank_zero_of_subsingleton,
    Module.finrank_zero_of_subsingleton]
  norm_num

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] [Subsingleton E.degreeOne] in
include hbase in
/-- A zero obstruction theory has a rank-zero bundle `E₁`. -/
theorem bundleRank_eq_zero : bundleRank φ = 0 := by
  rw [bundleRank, Nat.card_eq_zero]
  exact Or.inl inferInstance

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
include hbase in
/-- A zero obstruction theory puts the resolved-cone cycle in dimension zero. -/
theorem coneDegree_eq_zero : coneDegree φ = 0 := by
  rw [coneDegree, virtualDimension_eq_zero, bundleRank_eq_zero]
  norm_num

variable [Subsingleton (PrimeSpectrum (R ⧸ I))] [_root_.IsReduced (R ⧸ I)]

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] [Subsingleton E.degreeOne]
  [_root_.IsReduced (R ⧸ I)] in
/-- In the rank-zero case over a one-point base, the total space `E₁` is again a single point. -/
theorem subsingleton_bundleSpace : Subsingleton ↥(ResolvedCone.bundleSpace φ) :=
  have _h : Subsingleton (PrimeSpectrum (ResolvedCone.bundleRing φ)) :=
    (PrimeSpectrum.comapEquiv (bundleRingEquiv φ).toRingEquiv).toEquiv.subsingleton
  inferInstanceAs (Subsingleton (PrimeSpectrum (ResolvedCone.bundleRing φ)))

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] [Subsingleton E.degreeOne]
  [_root_.IsReduced (R ⧸ I)] in
/-- In the rank-zero case over a one-point base, the resolved cone is again a single point. -/
theorem subsingleton_coneScheme : Subsingleton ↥(ResolvedCone.scheme φ) :=
  have _h : Subsingleton (PrimeSpectrum (ResolvedCone.ring φ)) :=
    (PrimeSpectrum.comapEquiv (ringEquivBase φ)).toEquiv.subsingleton
  inferInstanceAs (Subsingleton (PrimeSpectrum (ResolvedCone.ring φ)))

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] [Subsingleton E.degreeOne]
  [Subsingleton (PrimeSpectrum (R ⧸ I))] [_root_.IsReduced (R ⧸ I)] in
/-- In the rank-zero case over a one-point base, the resolved cone is nonempty. -/
theorem nonempty_coneScheme : Nonempty ↥(ResolvedCone.scheme φ) :=
  have _h : Nontrivial (ResolvedCone.ring φ) := (ringEquivBase φ).toEquiv.nontrivial
  inferInstanceAs (Nonempty (PrimeSpectrum (ResolvedCone.ring φ)))

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] [Subsingleton E.degreeOne]
  [Subsingleton (PrimeSpectrum (R ⧸ I))] in
/-- In the rank-zero case over a reduced one-point base, the resolved cone is reduced. -/
theorem isReduced_coneScheme : _root_.AlgebraicGeometry.IsReduced (ResolvedCone.scheme φ) :=
  have _h : _root_.IsReduced (ResolvedCone.ring φ) :=
    isReduced_of_injective (ringEquivBase φ) (ringEquivBase φ).injective
  inferInstance


omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] [_root_.IsReduced (R ⧸ I)] in
/-- Over a one-point base every point has the expected dimension, so the fundamental cycle of the
base is a cycle of dimension `vd`. -/
theorem pure_base (x : ↥(Spec (CommRingCat.of (R ⧸ I)))) (_hx : IsMax x) :
    dimX x = virtualDimension φ := by
  have _hX : Subsingleton ↥(Spec (CommRingCat.of (R ⧸ I))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (R ⧸ I)))
  rw [dimensionFunction_eq_zero_of_subsingleton, virtualDimension_eq_zero]

/-- **Consistency with the proper point, at the level of cycles.**  For the zero obstruction
theory on a reduced point the resolved-cone cycle is the flat pullback of the fundamental cycle
of the base. -/
theorem flatPullbackBundle_fundamental_eq_resolvedConeCycle :
    cyclesOfDimension.flatPullbackBundle (trivialization φ) dimX dimE (virtualDimension φ)
        (cyclesOfDimension.fundamental (pure_base φ dimX)) = resolvedConeCycle φ dimE := by
  have _hE1 : Subsingleton ↥(ResolvedCone.bundleSpace φ) := subsingleton_bundleSpace φ
  have _hC : Subsingleton ↥(ResolvedCone.scheme φ) := subsingleton_coneScheme φ
  have _hCred : _root_.AlgebraicGeometry.IsReduced (ResolvedCone.scheme φ) :=
    isReduced_coneScheme φ
  have _hX : Subsingleton ↥(Spec (CommRingCat.of (R ⧸ I))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (R ⧸ I)))
  obtain ⟨x⟩ : Nonempty ↥(Spec (CommRingCat.of (R ⧸ I))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (R ⧸ I)))
  obtain ⟨y⟩ : Nonempty ↥(ResolvedCone.scheme φ) := nonempty_coneScheme φ
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  dsimp only
  have hqx : q = VectorBundle.bundlePoint (trivialization φ) x := Subsingleton.elim _ _
  have hqy : q = (ResolvedCone.toBundle φ).base y := Subsingleton.elim _ _
  have hdim : dimE q = coneDegree φ := by
    rw [dimensionFunction_eq_zero_of_subsingleton, coneDegree_eq_zero]
  have hlhs : (AlgebraicCycle.pullbackBundle (trivialization φ)
      ((cyclesOfDimension.fundamental (pure_base φ dimX) :
        cyclesOfDimension (Spec (CommRingCat.of (R ⧸ I))) dimX (virtualDimension φ)) :
        AlgebraicCycle (Spec (CommRingCat.of (R ⧸ I))) ℚ)) q = 1 := by
    rw [hqx, AlgebraicCycle.pullbackBundle_apply_bundlePoint]
    exact cyclesOfDimension.fundamental_apply_of_isMax_of_isReduced _ x (isMax_of_subsingleton x)
  have hmap : (AlgebraicCycle.map (ResolvedCone.toBundle φ) (coneDimension φ dimE) dimE
      (ResolvedCone.scheme φ).fundamentalCycle) ((ResolvedCone.toBundle φ).base y) =
      (ResolvedCone.scheme φ).fundamentalCycle y :=
    AlgebraicCycle.map_closedImmersion_apply_image (ResolvedCone.toBundle φ) _ _ y
  have hrhs : ((resolvedConeCycle φ dimE :
      cyclesOfDimension (ResolvedCone.bundleSpace φ) dimE (coneDegree φ)) :
      AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ) q = 1 := by
    change (if dimE q = coneDegree φ then
      (AlgebraicCycle.map (ResolvedCone.toBundle φ) (coneDimension φ dimE) dimE
        (ResolvedCone.scheme φ).fundamentalCycle) q else 0) = 1
    rw [if_pos hdim, hqy, hmap]
    exact (ResolvedCone.scheme φ).fundamentalCycle_apply_of_isMax_of_isReduced y
      (isMax_of_subsingleton y)
  exact hlhs.trans hrhs.symm

/-- **Consistency with the proper point.**  For the zero obstruction theory on a reduced point
`X = Spec (R ⧸ I)` — the resolved cone is `C(E) = E₁ = X`, the bundle `E₁` has rank zero and the
expected dimension is zero — the virtual class is the class of the fundamental cycle of `X`. -/
theorem virtualClass_eq_fundamental
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) :
    virtualClass φ dimX dimE RX RE hhom hinj =
      RX.quotientMap (cyclesOfDimension.fundamental (pure_base φ dimX)) := by
  symm
  refine eq_virtualClass_of_pullback_eq φ dimX dimE RX RE hhom hinj _ ?_
  rw [bundlePullback, VectorBundle.chowPullbackBundle_quotientMap,
    flatPullbackBundle_fundamental_eq_resolvedConeCycle]
  rfl

/-! ## The hypotheses of the proper-point statement are satisfied by a reduced point -/

section ReducedPoint

variable (F : Type u) [Field F]

/-- The quotient of a field by the zero ideal is reduced. -/
instance isReduced_quotient_bot : _root_.IsReduced (F ⧸ (⊥ : Ideal F)) :=
  isReduced_of_injective (RingEquiv.quotientBot F) (RingEquiv.quotientBot F).injective

/-- The spectrum of the quotient of a field by the zero ideal is a single point. -/
instance subsingleton_primeSpectrum_quotient_bot :
    Subsingleton (PrimeSpectrum (F ⧸ (⊥ : Ideal F))) :=
  (PrimeSpectrum.comapEquiv (RingEquiv.quotientBot F)).toEquiv.subsingleton

variable {k : Type u} [CommRing k] [Algebra k F]
  {E : LinearTwoTermComplex (F ⧸ (⊥ : Ideal F))}
  [Module.Free (F ⧸ (⊥ : Ideal F)) E.degreeZero]
  [Module.Finite (F ⧸ (⊥ : Ideal F)) E.degreeZero]
  [Subsingleton E.degreeZero] [Subsingleton E.degreeOne]
  (φ : LinearTwoTermComplex.Hom E (conormalComplex k F (⊥ : Ideal F)))
  (dimX : DimensionFunction (Spec (CommRingCat.of (F ⧸ (⊥ : Ideal F)))))
  (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (F ⧸ (⊥ : Ideal F)))) dimX
    (virtualDimension φ))
  (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (coneDegree φ))

/-- **The virtual class of a reduced point.**  Take `R = F` a field, `I = ⊥`, so that
`X = Spec (F ⧸ ⊥)` is a reduced point, and let `φ` be a zero obstruction theory (both terms of
`E` vanish).  Then `E₁ = C(E) = X` is a rank-zero bundle, the expected dimension is `0`, and the
virtual fundamental class is the class of the fundamental cycle of the point. -/
theorem virtualClass_point
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) :
    virtualClass φ dimX dimE RX RE hhom hinj =
      RX.quotientMap (cyclesOfDimension.fundamental (pure_base φ dimX)) :=
  virtualClass_eq_fundamental φ dimX dimE RX RE hhom hinj

end ReducedPoint

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.VirtualClass
