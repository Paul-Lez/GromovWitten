/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.SemilocalNormOrder
import GromovWitten.AlgebraicGeometry.IntersectionTheory.NormPushforward
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClassGeneral
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Proper pushforward of a principal divisor, equidimensional case

Let `f : X ⟶ Y` be a proper morphism, `W ⊆ X` an integral closed subscheme with generic point
`w`, and `φ` a nonzero rational function on `W`.  Let `f(W) ⊆ Y` be the image of `W` (the
scheme-theoretic image of `W → X → Y`, an integral closed subscheme of `Y` with generic point
`f(w)`).  This file proves Fulton, *Intersection Theory*, Prop. 1.4 (b) / Stacks, Chow
Homology, Lemma 42.20.3, in the case `dim f(W) = dim W`:

`f_* div(φ) = div(Nm_{K(W)/K(f(W))} φ)`,

for the residue-degree pushforward `AlgebraicGeometry.AlgebraicCycle.map` with certified dimension
functions, and deduces that the proper pushforward of such a divisor is a rational equivalence.
(The cases `dim f(W) < dim W` are not treated here.)

## Main results

* `IntegralClosedSubscheme.properImage`, `IntegralClosedSubscheme.toProperImage`,
  `IntegralClosedSubscheme.genericPointImage_properImage`: the image `f(W)` and the dominant
  (proper if `f` is) morphism `W ⟶ f(W)`; `RationalFunctionGenerator.normImage`: the generator
  `(f(W), Nm φ)`.
* `ProperPushforwardDivisor.finite_preimage_singleton_of_antichain`: a fibre of a quasi-compact
  morphism from a locally Noetherian scheme in which no point specialises to another is finite.
* `ProperPushforwardDivisor.ordFrac_norm_eq_finsum_fibre`: for a finite injective extension of
  domains `A₀ ⊆ B₀` and a prime `p` of `A₀` with one-dimensional local ring,
  `ord_p (Nm b) = ∑_{Q ∩ A₀ = p} [κ(Q) : κ(p)] · ord_Q b` (the semilocal norm formula of
  `GromovWitten.Algebra.SemilocalNormOrder` applied to `(A₀)_p ⊆ (A₀ ∖ p)⁻¹ B₀`).
* `ProperPushforwardDivisor.exists_affine_finite_of_finite_fiber` (Zariski's main theorem): a
  proper morphism with finite fibre over `η` is finite over an affine neighbourhood of `η`;
  `ProperPushforwardDivisor.fibrePrime_bijective`, `residueDegree_eq_fibreDegree` and
  `ord_algebraMap_eq_ord_localization` identify the points over `η`, their residue degrees and
  their orders of vanishing with primes of the finite ring extension.
* `ProperPushforwardDivisor.map_principalCycle_eq_principalCycle_norm`: `h_* div(g) = div(Nm g)`
  for a proper dominant morphism `h` of integral locally Noetherian schemes and weight functions
  compatible with coheight one.
* `ProperPushforwardDivisor.finite_functionField_of_dim_eq` (P2.1): `K(W) / K(f(W))` is finite
  when `dim f(w) = dim w`.
* `ProperPushforwardDivisor.dim_eq_of_mem_fiber`, `ProperPushforwardDivisor.finite_fiber_of_dim_eq`
  (P2.2): over a point `ξ` with `dim ξ + 1 = dim w`, the specialisations of `w` form a finite set
  of points of dimension `dim ξ`.
* `ProperPushforwardDivisor.exists_affine_finite_over` (P2.3): `W → f(W)` is finite over an affine
  neighbourhood of every codimension-one point of `f(W)`.
* `ProperPushforwardDivisor.map_divisor_of_dim_eq_of_covByDimension`,
  `ProperPushforwardDivisor.map_divisor_of_dim_eq`,
  `ProperPushforwardDivisor.properPushforward_divisor_of_dim_eq` (Theorem P2): for `X`, `Y`
  locally of finite type over a field (or, more generally, dimension functions dropping by one
  along covering relations) and `dim f(w) = dim w`, `f_* div(φ) = div(Nm φ)`.
* `ProperPushforwardDivisor.properPushforward_divisor_mem_relations_of_dim_eq`: the pushforward of
  such a divisor lies in the rational equivalence relations of `Y`.

## Proof outline

Write `h : W ⟶ f(W)`.  Pushforward along `W → X → Y` factors as pushforward along `h` followed by
the closed immersion `f(W) → Y` (`AlgebraicCycle.map_comp_of_between`), so it suffices to prove
`h_* div(φ) = div(Nm φ)` on `f(W)`.  At a point `η` of `f(W)` of codimension `≠ 1` both sides
vanish for dimension reasons.  At a point `η` of codimension one, every point over `η` has
codimension one in `W`, the fibre is finite (its points are pairwise incomparable), and Zariski's
main theorem gives affine opens `VA ∋ η`, `VB = h⁻¹ VA` with `Γ(f(W), VA) → Γ(W, VB)` finite.
Writing `φ = b₁ / b₂` with `bᵢ ∈ Γ(W, VB)`, the coefficient identity at `η` is the semilocal norm
formula for `Γ(f(W), VA)_p ⊆ (Γ(f(W), VA) ∖ p)⁻¹ Γ(W, VB)`, transported through the
identifications of points, stalks and residue fields.

The hypothesis `f ≫ sY = sX` of the blueprint is not needed: certified dimension functions are
intrinsic (`dimensionFunction_eq`), and only `LocallyOfFiniteType` of the structure morphisms is
used (to get `CovByDimension`).
-/

-- Concrete `Spec R` / section-ring / residue-field carriers only unify with the generic scheme
-- instances at default transparency; this option is what Mathlib's own affine-scheme API uses.
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Order

open scoped WithZero

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## The image of an integral closed subscheme under a quasi-compact morphism -/

namespace IntegralClosedSubscheme

variable {X Y : Scheme.{u}} (Z : IntegralClosedSubscheme X) (f : X ⟶ Y)
  [QuasiCompact f]

/-- The scheme-theoretic image of an integral closed subscheme under a quasi-compact morphism is
integral: reduced because the source is, irreducible because the source is and the morphism to
the image is dominant. -/
instance isIntegral_image_inclusion_comp : IsIntegral (Z.inclusion ≫ f).image :=
  have _h1 := _root_.AlgebraicGeometry.Scheme.isReduced_image (Z.inclusion ≫ f)
  have _h2 := _root_.AlgebraicGeometry.Scheme.irreducibleSpace_image (Z.inclusion ≫ f)
  isIntegral_of_irreducibleSpace_of_isReduced _

variable [IsLocallyNoetherian Y]

/-- **The image `f(Z)`** of an integral closed subscheme `Z ⊆ X` under a quasi-compact morphism
`f : X ⟶ Y` to a locally Noetherian scheme: the scheme-theoretic image of `Z → X → Y`, as an
integral closed subscheme of `Y`.  Its generic point is the image under `f` of the generic point
of `Z` (`genericPointImage_properImage`). -/
noncomputable def properImage : IntegralClosedSubscheme Y where
  scheme := (Z.inclusion ≫ f).image
  inclusion := (Z.inclusion ≫ f).imageι
  isLocallyNoetherian := _root_.AlgebraicGeometry.Scheme.isLocallyNoetherian_image _

/-- The morphism from `Z` onto its image `f(Z)`. -/
noncomputable def toProperImage : Z.scheme ⟶ (Z.properImage f).scheme :=
  (Z.inclusion ≫ f).toImage

/-- `Z → f(Z) → Y` is `Z → X → Y`. -/
@[reassoc (attr := simp)]
theorem toProperImage_inclusion :
    Z.toProperImage f ≫ (Z.properImage f).inclusion = Z.inclusion ≫ f :=
  Scheme.Hom.toImage_imageι _

/-- `Z → f(Z)` is dominant. -/
instance isDominant_toProperImage : IsDominant (Z.toProperImage f) :=
  inferInstanceAs (IsDominant (Z.inclusion ≫ f).toImage)

/-- `Z → f(Z)` is quasi-compact. -/
instance quasiCompact_toProperImage : QuasiCompact (Z.toProperImage f) :=
  inferInstanceAs (QuasiCompact (Z.inclusion ≫ f).toImage)

/-- `Z → f(Z)` is proper when `f` is: `Z → f(Z) → Y` is proper and `f(Z) → Y` is separated. -/
instance isProper_toProperImage [IsProper f] : IsProper (Z.toProperImage f) := by
  have : IsProper (Z.toProperImage f ≫ (Z.properImage f).inclusion) := by
    rw [toProperImage_inclusion]
    infer_instance
  exact IsProper.of_comp _ (Z.properImage f).inclusion

/-- The generic point of `f(Z)` is the image of the generic point of `Z`. -/
theorem genericPointImage_properImage :
    (Z.properImage f).genericPointImage = f.base Z.genericPointImage := by
  change (Z.properImage f).inclusion.base (genericPoint (Z.properImage f).scheme) =
    f.base (Z.inclusion.base (genericPoint Z.scheme))
  rw [← _root_.AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant (Z.toProperImage f),
    ← Scheme.Hom.comp_apply, toProperImage_inclusion, Scheme.Hom.comp_apply]

/-- The function field of `Z` is an algebra over the function field of its image `f(Z)`, through
the dominant morphism `Z → f(Z)`. -/
noncomputable instance functionFieldAlgebra :
    Algebra (Z.properImage f).scheme.functionField Z.scheme.functionField :=
  (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (Z.toProperImage f)).toAlgebra

end IntegralClosedSubscheme

namespace RationalFunctionGenerator

variable {X Y : Scheme.{u}} (g : RationalFunctionGenerator X) (f : X ⟶ Y) [QuasiCompact f]
  [IsLocallyNoetherian Y]

/-- **The norm generator** `(f(W), Nm_{K(W)/K(f(W))} φ)` attached to a generator `(W, φ)` of `X`
and a quasi-compact morphism `f : X ⟶ Y`: the image subscheme `f(W)` together with the norm of
`φ` along the function field extension `K(W) / K(f(W))`.  (When this extension is not finite,
`Algebra.norm` is `1` by convention; in the equidimensional proper case it is finite, this is
proved independently in `finite_functionField_of_dim_eq`.) -/
noncomputable def normImage : RationalFunctionGenerator Y where
  subspace := g.subspace.properImage f
  function := Units.map
    (Algebra.norm (g.subspace.properImage f).scheme.functionField :
      g.subspace.scheme.functionField →* _) g.function

end RationalFunctionGenerator

namespace ProperPushforwardDivisor

/-! ## Dimension functions along specialisations -/

/-- A proper specialisation strictly lowers a certified dimension. -/
theorem dim_lt_of_specializes {X : Scheme.{u}} (dim : DimensionFunction X) {x y : X}
    (h : x ⤳ y) (hne : x ≠ y) : dim y < dim x := by
  have hlt : y < x := lt_of_le_not_ge (HomogeneityLocal.le_iff_specializes.2 h)
    fun hyx ↦ hne (h.antisymm (HomogeneityLocal.le_iff_specializes.1 hyx)).eq
  have hfin : height y < ⊤ := by rw [dim.height_eq y]; exact ENat.natCast_lt_top _
  have hh : height y < height x := height_strictMono hlt hfin
  rw [dim.height_eq, dim.height_eq] at hh
  have hn : Int.toNat (dim y) < Int.toNat (dim x) := by exact_mod_cast hh
  have h1 := dim.nonnegative y
  have h2 := dim.nonnegative x
  omega

/-! ## Finiteness of fibres consisting of pairwise incomparable points -/

attribute [local instance] specializationOrder in
/-- A maximal point for the specialisation order is a generic point of an irreducible component
(a copy of the private lemma of `ChowGroup.lean`). -/
private lemma isMax_mem_genericPoints''
    {T : Type*} [TopologicalSpace T] [T0Space T] [QuasiSober T]
    {x : T} (hx : IsMax x) : x ∈ genericPoints T := by
  rw [genericPoints, irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, ?_⟩
  intro s hs hxs
  let y : T := hs.2.genericPoint
  have hy : IsGenericPoint y s := hs.2.isGenericPoint_genericPoint_closure.trans
    hs.1.closure_eq
  have hxy : x ≤ y := by
    change y ⤳ x
    rw [specializes_iff_closure_subset, hy.def]
    exact hxs
  have hyx : y ≤ x := hx hxy
  have heq : x = y := le_antisymm hxy hyx
  simpa only [heq] using hy.def.symm.le

attribute [local instance] specializationOrder in
/-- **Fibres made of pairwise incomparable points are finite.**  Let `h : V ⟶ V'` be a
quasi-compact morphism from a locally Noetherian scheme and `η` a point of `V'` such that no point
of the fibre `h⁻¹{η}` is a proper specialisation of another one.  Then the fibre is finite: over
an affine open neighbourhood `V₀` of `η` the preimage `h⁻¹V₀` is a Noetherian space, and every
point of the fibre is a generic point of an irreducible component of the closed subset
`h⁻¹(closure {η}) ∩ h⁻¹V₀`. -/
theorem finite_preimage_singleton_of_antichain {V V' : Scheme.{u}} [IsLocallyNoetherian V]
    (h : V ⟶ V') [QuasiCompact h] (η : V')
    (hanti : ∀ x x' : V, h.base x = η → h.base x' = η → x ⤳ x' → x = x') :
    (h.base ⁻¹' {η}).Finite := by
  obtain ⟨V₀, hV₀, hηV₀, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := V') (x := η) (U := ⊤) trivial
  let U : V.Opens := h ⁻¹ᵁ V₀
  have hUc : IsCompact (U : Set V) :=
    QuasiCompact.isCompact_preimage (f := h) _ V₀.isOpen hV₀.isCompact
  have _ : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  have _ : IsNoetherian U.toScheme := ⟨⟩
  let C : Set U := {u | h.base u.1 ∈ closure ({η} : Set V')}
  have hC : IsClosed C := isClosed_closure.preimage (h.continuous.comp continuous_subtype_val)
  have _ : QuasiSober C := hC.isClosedEmbedding_subtypeVal.quasiSober
  have hgen : (genericPoints C).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  refine ((hgen.image fun c : C ↦ c.1).image (fun u : U ↦ (u : V))).subset ?_
  intro x hx
  have hxη : h.base x = η := hx
  have hxU : x ∈ U := by
    change h.base x ∈ V₀
    rw [hxη]
    exact hηV₀
  have hxC : (⟨x, hxU⟩ : U) ∈ C := by
    change h.base x ∈ closure ({η} : Set V')
    rw [hxη]
    exact subset_closure rfl
  refine ⟨⟨x, hxU⟩, ⟨⟨⟨x, hxU⟩, hxC⟩, isMax_mem_genericPoints'' fun c hc ↦ ?_, rfl⟩, rfl⟩
  have hcx : (c.1.1 : V) ⤳ x := by
    change c ⤳ ⟨⟨x, hxU⟩, hxC⟩ at hc
    have h1 : c.1 ⤳ ⟨x, hxU⟩ := by simpa only [subtype_specializes_iff] using hc
    exact h1.map U.ι.continuous
  have hcη : h.base (c.1.1 : V) = η := by
    have h1 : h.base (c.1.1 : V) ⤳ η := by
      rw [← hxη]
      exact hcx.map h.continuous
    have h2 : η ⤳ h.base (c.1.1 : V) := specializes_iff_mem_closure.mpr c.2
    exact (h1.antisymm h2).eq
  have hceq : (c.1.1 : V) = x := hanti _ _ hcη hxη hcx
  have hc' : c = ⟨⟨x, hxU⟩, hxC⟩ := Subtype.ext (Subtype.ext hceq)
  rw [hc']
  exact specializes_rfl

/-! ## Algebra: the fibre of a finite extension over a prime -/

section RingFibre

open NormPushforward

variable {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀] [Module.Finite A₀ B₀]
  (p : Ideal A₀) [p.IsPrime]

/-- A maximal ideal of the semilocal ring `locB B₀ p` lies over `p` (for `B₀` finite over `A₀`;
`NormPushforward.comap_fibrePoint` is the same statement under a freeness assumption). -/
theorem comap_fibrePoint_of_finite (Q : MaximalSpectrum (locB B₀ p)) :
    (fibrePoint p Q).asIdeal.comap (algebraMap A₀ B₀) = p := by
  have hQ : Q.asIdeal.IsPrime := Q.isMaximal.isPrime
  have hcomp : (fibrePoint p Q).asIdeal.comap (algebraMap A₀ B₀) =
      (Q.asIdeal.comap (algebraMap (locA p) (locB B₀ p))).comap (algebraMap A₀ (locA p)) := by
    rw [fibrePoint_asIdeal, Ideal.comap_comap, Ideal.comap_comap,
      ← IsScalarTower.algebraMap_eq A₀ B₀ (locB B₀ p),
      ← IsScalarTower.algebraMap_eq A₀ (locA p) (locB B₀ p)]
  have hmax : (Q.asIdeal.comap (algebraMap (locA p) (locB B₀ p))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := locA p) Q.asIdeal
  rw [hcomp, IsLocalRing.eq_maximalIdeal hmax]
  exact IsLocalization.AtPrime.under_maximalIdeal (locA p) p

/-- Every prime of `B₀` over `p` is `fibrePoint p Q` for a maximal ideal `Q` of `locB B₀ p` (for
`B₀` finite over `A₀`; compare `NormPushforward.exists_fibrePoint`). -/
theorem exists_fibrePoint_of_finite (q : PrimeSpectrum B₀)
    (hq : q.asIdeal.comap (algebraMap A₀ B₀) = p) : ∃ Q, fibrePoint p Q = q := by
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid B₀ p.primeCompl : Set B₀)
      (q.asIdeal : Set B₀) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hmem
    exact hs (hq ▸ hmem)
  have hJ : (q.asIdeal.map (algebraMap B₀ (locB B₀ p))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Algebra.algebraMapSubmonoid B₀ p.primeCompl)
      (locB B₀ p) q.asIdeal q.isPrime hdisj
  have hunder : (q.asIdeal.map (algebraMap B₀ (locB B₀ p))).comap (algebraMap B₀ (locB B₀ p))
      = q.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid B₀ p.primeCompl)
      (locB B₀ p) q.isPrime hdisj
  have hPm : ((q.asIdeal.map (algebraMap B₀ (locB B₀ p))).comap
      (algebraMap (locA p) (locB B₀ p))).comap (algebraMap A₀ (locA p)) = p := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A₀ (locA p) (locB B₀ p),
      IsScalarTower.algebraMap_eq A₀ B₀ (locB B₀ p), ← Ideal.comap_comap, hunder, hq]
  have hJmax : (q.asIdeal.map (algebraMap B₀ (locB B₀ p))).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := locA p) _
      (by rw [eq_maximalIdeal_of_comap_eq p _ hPm]; exact IsLocalRing.maximalIdeal.isMaximal _)
  exact ⟨⟨q.asIdeal.map (algebraMap B₀ (locB B₀ p)), hJmax⟩, PrimeSpectrum.ext hunder⟩

/-- The residue degree `[κ(Q) : κ(p)]` of a prime `Q` of `B₀` lying over `p`, through the map of
residue fields `Ideal.ResidueField.map`. -/
noncomputable def fibreDegree (Q : PrimeSpectrum B₀)
    (hQ : Q.asIdeal.comap (algebraMap A₀ B₀) = p) : ℕ :=
  letI := (Ideal.ResidueField.map p Q.asIdeal (algebraMap A₀ B₀) hQ.symm).toAlgebra
  Module.finrank p.ResidueField Q.asIdeal.ResidueField

/-- **Matching the residue degrees** for a finite (not necessarily free) extension: the residue
degree of `fibrePoint p Q` over `p` equals `[κ(Q) : κ(locA p)]` (copy of
`NormPushforward.finrank_residueField_fibrePoint` without the freeness assumption). -/
theorem fibreDegree_fibrePoint (Q : MaximalSpectrum (locB B₀ p)) :
    fibreDegree p (fibrePoint p Q) (comap_fibrePoint_of_finite p Q) =
      Module.finrank (IsLocalRing.ResidueField (locA p)) Q.asIdeal.ResidueField := by
  have _ : Q.asIdeal.IsPrime := Q.isMaximal.isPrime
  have _ : IsScalarTower A₀ (locA p) (Localization.AtPrime Q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq (algebraMap_locQ p Q)
  refine finrank_congr_ringHom_left _ (RingEquiv.refl p.ResidueField)
    (IsLocalRing.ResidueField.mapAlgEquiv (locQAlgEquiv p Q)).toRingEquiv ?_
  have key : ((IsLocalRing.ResidueField.mapAlgEquiv
        (locQAlgEquiv p Q)).toRingEquiv : _ →+* _).comp
      (Ideal.ResidueField.map p (fibrePoint p Q).asIdeal (algebraMap A₀ B₀)
        (comap_fibrePoint_of_finite p Q).symm) =
      algebraMap (IsLocalRing.ResidueField (locA p)) Q.asIdeal.ResidueField := by
    refine Ideal.ResidueField.ringHom_ext (R := A₀) (RingHom.ext fun a => ?_)
    have h1 : algebraMap A₀ Q.asIdeal.ResidueField a =
        algebraMap B₀ Q.asIdeal.ResidueField (algebraMap A₀ B₀ a) :=
      IsScalarTower.algebraMap_apply A₀ B₀ _ a
    have h2 : algebraMap A₀ Q.asIdeal.ResidueField a =
        algebraMap (IsLocalRing.ResidueField (locA p)) Q.asIdeal.ResidueField
          (algebraMap A₀ p.ResidueField a) :=
      IsScalarTower.algebraMap_apply A₀ (IsLocalRing.ResidueField (locA p)) _ a
    simp only [RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap p (fibrePoint p Q).asIdeal (algebraMap A₀ B₀)
      (comap_fibrePoint_of_finite p Q).symm a]
    change (IsLocalRing.ResidueField.mapAlgEquiv (locQAlgEquiv p Q))
      (algebraMap B₀ (fibrePoint p Q).asIdeal.ResidueField (algebraMap A₀ B₀ a)) = _
    rw [AlgEquiv.commutes, ← h1, h2]
  exact fun c => RingHom.congr_fun key c

end RingFibre

section RingFinite

open scoped nonZeroDivisors

/-- A finite injective extension of domains `A₀ ⊆ B₀` induces a finite extension of fraction
fields `K ⊆ L`. -/
theorem finite_of_isFractionRing {A₀ B₀ K L : Type*} [CommRing A₀] [CommRing B₀] [IsDomain A₀]
    [IsDomain B₀] [Algebra A₀ B₀] [Module.Finite A₀ B₀]
    (hinj : Function.Injective (algebraMap A₀ B₀)) [Field K] [Field L] [Algebra A₀ K]
    [IsFractionRing A₀ K] [Algebra B₀ L] [IsFractionRing B₀ L] [Algebra K L] [Algebra A₀ L]
    [IsScalarTower A₀ K L] [IsScalarTower A₀ B₀ L] : Module.Finite K L := by
  have _ : FaithfulSMul A₀ B₀ := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact Module.Finite.of_isLocalization A₀ B₀ A₀⁰

end RingFinite
section RingNorm

open NormPushforward

/-- Over a finite index type, the `toNat` of a sum of finite products `aᵢ · oᵢ` in `ℕ∞` is the
sum of the products `aᵢ · (oᵢ).toNat`. -/
theorem toNat_finsum_natCast_mul {ι : Type*} [Finite ι] (a : ι → ℕ) (o : ι → ℕ∞)
    (ho : ∀ i, o i ≠ ⊤) : (∑ᶠ i, (a i : ℕ∞) * o i).toNat = ∑ᶠ i, a i * (o i).toNat := by
  have := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have h : ∀ i, (a i : ℕ∞) * o i = ((a i * (o i).toNat : ℕ) : ℕ∞) := fun i => by
    rw [Nat.cast_mul, ENat.natCast_toNat (ho i)]
  simp_rw [h]
  rw [← Nat.cast_sum, ENat.toNat_natCast]

variable {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀] [IsDomain A₀] [IsDomain B₀]
  [IsNoetherianRing A₀] [Algebra A₀ B₀] [Module.Finite A₀ B₀] (p : Ideal A₀) [p.IsPrime]
  {K L : Type u} [Field K] [Field L] [Algebra A₀ K] [IsFractionRing A₀ K] [Algebra B₀ L]
  [IsFractionRing B₀ L] [Algebra K L] [Algebra A₀ L] [IsScalarTower A₀ K L]
  [IsScalarTower A₀ B₀ L]
  (A' : Type u) [CommRing A'] [IsDomain A'] [Algebra A₀ A'] [IsLocalization.AtPrime A' p]
  [Algebra A' K] [IsScalarTower A₀ A' K] [IsFractionRing A' K]
  [IsNoetherianRing A'] [Ring.KrullDimLE 1 A']

/-- **The norm formula over a prime of the base, fibre form.**  Let `A₀ ⊆ B₀` be a finite
injective extension of domains with `A₀` Noetherian, `p` a prime of `A₀` whose local ring has
dimension `≤ 1`, `K`, `L` fraction fields of `A₀`, `B₀` with compatible structure maps, and `A'`
any localization of `A₀` at `p` mapping compatibly to `K`.  For `b ∈ B₀` nonzero,
`ord_{A'} (Nm_{L/K} b) = ∑_{Q ∩ A₀ = p} [κ(Q) : κ(p)] · ord_{(B₀)_Q} b`.  This is the semilocal
norm formula applied to `(A₀)_p ⊆ (A₀ ∖ p)⁻¹ B₀`, whose maximal ideals are the primes over `p`. -/
theorem ordFrac_norm_eq_finsum_fibre (hinj : Function.Injective (algebraMap A₀ B₀)) (b : B₀)
    (hb : b ≠ 0) :
    Ring.ordFrac A' (Algebra.norm K (algebraMap B₀ L b)) =
      ((Multiplicative.ofAdd ((∑ᶠ Q : {Q : PrimeSpectrum B₀ //
          Q.asIdeal.comap (algebraMap A₀ B₀) = p},
        fibreDegree p Q.1 Q.2 * (Ring.ord (Localization.AtPrime Q.1.asIdeal)
            (algebraMap B₀ (Localization.AtPrime Q.1.asIdeal) b)).toNat : ℕ) : ℤ) :
        Multiplicative ℤ) : ℤᵐ⁰) := by
  classical
  let e : locA p ≃ₐ[A₀] A' := IsLocalization.algEquiv p.primeCompl _ _
  let algAK : Algebra (locA p) K := ((algebraMap A' K).comp (e : locA p →+* A')).toAlgebra
  have towerA : IsScalarTower A₀ (locA p) K := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A₀ K a = algebraMap A' K (e (algebraMap A₀ (locA p) a))
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have fracA : IsFractionRing (locA p) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl _ _
  have hle := algebraMapSubmonoid_le_nonZeroDivisors p hinj
  have domB : IsDomain (locB B₀ p) := IsLocalization.isDomain_localization hle
  have hunit : ∀ y : Algebra.algebraMapSubmonoid B₀ p.primeCompl,
      IsUnit (algebraMap B₀ L y) := fun y =>
    IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hle y.2))
  let algBL : Algebra (locB B₀ p) L := (IsLocalization.lift hunit).toAlgebra
  have towerB : IsScalarTower B₀ (locB B₀ p) L :=
    IsScalarTower.of_algebraMap_eq fun c => (IsLocalization.lift_eq hunit c).symm
  have fracB : IsFractionRing (locB B₀ p) L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid B₀ p.primeCompl) _ _
  let algAL : Algebra (locA p) L := ((algebraMap K L).comp (algebraMap (locA p) K)).toAlgebra
  have towerAKL : IsScalarTower (locA p) K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have towerAL : IsScalarTower A₀ (locA p) L := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A₀ L a =
      algebraMap K L (algebraMap (locA p) K (algebraMap A₀ (locA p) a))
    rw [← IsScalarTower.algebraMap_apply A₀ (locA p) K, ← IsScalarTower.algebraMap_apply A₀ K L]
  have towerABL : IsScalarTower (locA p) (locB B₀ p) L := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    apply IsLocalization.ringHom_ext p.primeCompl
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply A₀ (locA p) L,
      ← IsScalarTower.algebraMap_apply A₀ (locA p) (locB B₀ p),
      IsScalarTower.algebraMap_apply A₀ B₀ (locB B₀ p),
      ← IsScalarTower.algebraMap_apply B₀ (locB B₀ p) L,
      ← IsScalarTower.algebraMap_apply A₀ B₀ L]
  have faithful : FaithfulSMul (locA p) (locB B₀ p) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    have h1 : algebraMap (locA p) L x = algebraMap (locA p) L y := by
      rw [IsScalarTower.algebraMap_apply (locA p) (locB B₀ p) L, hxy,
        ← IsScalarTower.algebraMap_apply]
    exact IsFractionRing.injective (locA p) K ((algebraMap K L).injective h1)
  have kdim : Ring.KrullDimLE 1 (locA p) := by
    rw [Ring.krullDimLE_iff, ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    exact Ring.krullDimLE_iff.mp ‹_›
  have hb' : algebraMap B₀ (locB B₀ p) b ≠ 0 := fun h =>
    hb (IsLocalization.injective (locB B₀ p) hle (by rw [h, map_zero]))
  have hordM : ∀ M : MaximalSpectrum (locB B₀ p), Ring.ord (Localization.AtPrime M.asIdeal)
        (algebraMap (locB B₀ p) (Localization.AtPrime M.asIdeal)
          (algebraMap B₀ (locB B₀ p) b)) =
      Ring.ord (Localization.AtPrime (fibrePoint p M).asIdeal)
        (algebraMap B₀ (Localization.AtPrime (fibrePoint p M).asIdeal) b) := by
    intro M
    have _ : M.asIdeal.IsPrime := M.isMaximal.isPrime
    have _ : IsLocalization.AtPrime (Localization.AtPrime M.asIdeal) (fibrePoint p M).asIdeal :=
      IsLocalization.isLocalization_atPrime_localization_atPrime
        (Algebra.algebraMapSubmonoid B₀ p.primeCompl) M.asIdeal
    rw [← IsScalarTower.algebraMap_apply B₀ (locB B₀ p) (Localization.AtPrime M.asIdeal)]
    exact VectorBundle.SectionGysinIdentity.ring_ord_atPrime (fibrePoint p M).asIdeal
      (Localization.AtPrime M.asIdeal) b
  have _ : Finite (MaximalSpectrum (locB B₀ p)) :=
    GromovWitten.Algebra.finite_maximalSpectrum_of_finite_over_local (locA p)
  have hconv : (∑ᶠ M : MaximalSpectrum (locB B₀ p),
      (Module.finrank (IsLocalRing.ResidueField (locA p)) M.asIdeal.ResidueField : ℕ∞) *
        Ring.ord (Localization.AtPrime M.asIdeal)
          (algebraMap (locB B₀ p) (Localization.AtPrime M.asIdeal)
            (algebraMap B₀ (locB B₀ p) b))).toNat =
      ∑ᶠ M : MaximalSpectrum (locB B₀ p),
        Module.finrank (IsLocalRing.ResidueField (locA p)) M.asIdeal.ResidueField *
          (Ring.ord (Localization.AtPrime M.asIdeal)
            (algebraMap (locB B₀ p) (Localization.AtPrime M.asIdeal)
              (algebraMap B₀ (locB B₀ p) b))).toNat :=
    toNat_finsum_natCast_mul _ _ fun M =>
      GromovWitten.Algebra.semilocal_ord_localization_ne_top (locA p) K L hb' M
  have key := GromovWitten.Algebra.semilocal_finsum_ord_eq_ordFrac_norm (A := locA p)
    (B := locB B₀ p) (K := K) (L := L) hb'
  rw [← IsScalarTower.algebraMap_apply, hconv] at key
  have hord : Ring.ordFrac A' (Algebra.norm K (algebraMap B₀ L b)) =
      Ring.ordFrac (locA p) (Algebra.norm K (algebraMap B₀ L b)) :=
    ordFrac_ringEquiv e.toRingEquiv (RingEquiv.refl K) (fun _ => rfl) _
  rw [hord, key]
  have hsum : (∑ᶠ M : MaximalSpectrum (locB B₀ p),
      Module.finrank (IsLocalRing.ResidueField (locA p)) M.asIdeal.ResidueField *
        (Ring.ord (Localization.AtPrime M.asIdeal)
          (algebraMap (locB B₀ p) (Localization.AtPrime M.asIdeal)
            (algebraMap B₀ (locB B₀ p) b))).toNat) =
      ∑ᶠ Q : {Q : PrimeSpectrum B₀ // Q.asIdeal.comap (algebraMap A₀ B₀) = p},
        fibreDegree p Q.1 Q.2 * (Ring.ord (Localization.AtPrime Q.1.asIdeal)
            (algebraMap B₀ (Localization.AtPrime Q.1.asIdeal) b)).toNat := by
    refine finsum_eq_of_bijective (fun M : MaximalSpectrum (locB B₀ p) =>
        (⟨fibrePoint p M, comap_fibrePoint_of_finite p M⟩ :
          {Q : PrimeSpectrum B₀ // Q.asIdeal.comap (algebraMap A₀ B₀) = p}))
      ⟨fun _ _ h => fibrePoint_injective p (congrArg Subtype.val h),
        fun Q => (exists_fibrePoint_of_finite p Q.1 Q.2).imp fun _ h => Subtype.ext h⟩ ?_
    intro M
    change _ = fibreDegree p (fibrePoint p M) (comap_fibrePoint_of_finite p M) * _
    rw [fibreDegree_fibrePoint, hordM]
  rw [hsum]

end RingNorm

/-! ## Geometry: local finiteness over a point with finite fibre -/

section LocalFinite

/-- **Local finiteness (Zariski's main theorem).**  If `h : V ⟶ V'` is proper and the fibre over
`η` is finite, there are affine opens `VA ∋ η` of `V'` and `VB = h⁻¹ VA` of `V` such that the ring
map `Γ(V', VA) → Γ(V, VB)` is finite. -/
theorem exists_affine_finite_of_finite_fiber {V V' : Scheme.{u}} (h : V ⟶ V') [IsProper h]
    (η : V') (hfin : (h.base ⁻¹' {η}).Finite) :
    ∃ (VA : V'.Opens) (VB : V.Opens) (e : VB ≤ h ⁻¹ᵁ VA), IsAffineOpen VA ∧ IsAffineOpen VB ∧
      η ∈ VA ∧ h ⁻¹ᵁ VA ≤ VB ∧ (h.appLE VA VB e).hom.Finite := by
  obtain ⟨V₁, hηV₁, hfinite⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton h η hfin
  obtain ⟨W, hW, hηW, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := V₁.toScheme) (x := ⟨η, hηV₁⟩) (U := ⊤) trivial
  have hVB := image_morphismRestrict_preimage h V₁ W
  refine ⟨V₁.ι ''ᵁ W, (h ⁻¹ᵁ V₁).ι ''ᵁ ((h ∣_ V₁) ⁻¹ᵁ W), hVB.le,
    hW.image_of_isOpenImmersion V₁.ι,
    (hW.preimage (h ∣_ V₁)).image_of_isOpenImmersion _, ⟨⟨η, hηV₁⟩, hηW, rfl⟩, hVB.ge, ?_⟩
  have := IsFinite.finite_app (h ∣_ V₁) W hW
  rwa [morphismRestrict_app'] at this

/-- The stalk maps of `h` send germs of sections over `VA` to germs of their images under
`h.appLE VA VB e`. -/
theorem stalkMap_germ_appLE {V V' : Scheme.{u}} (h : V ⟶ V') {VA : V'.Opens} {VB : V.Opens}
    (e : VB ≤ h ⁻¹ᵁ VA) (x : V) (hx : x ∈ VB) (a : Γ(V', VA)) :
    h.stalkMap x (V'.presheaf.germ VA (h.base x) (e hx) a) =
      V.presheaf.germ VB x hx (h.appLE VA VB e a) := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
    TopCat.Presheaf.germ_res_apply]

/-- An open immersion has residue degree one at every point. -/
theorem residueDegree_eq_one_of_isOpenImmersion {P V : Scheme.{u}} (i : P ⟶ V)
    [IsOpenImmersion i] (x : P) : i.residueDegree x = 1 := by
  unfold Scheme.Hom.residueDegree
  let _ := (i.residueFieldMap x).hom.toAlgebra
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  exact (asIso (i.residueFieldMap x)).commRingCatIsoToRingEquiv.bijective

/-- **Residue degrees along a commutative square of open immersions.**  If `ψ ≫ j = i ≫ h` with
`i`, `j` open immersions, then the residue degree of `h` at `i x` is the residue degree of `ψ`
at `x`. -/
theorem residueDegree_eq_of_comm {P Q V V' : Scheme.{u}} (ψ : P ⟶ Q) (h : V ⟶ V') (i : P ⟶ V)
    (j : Q ⟶ V') [IsOpenImmersion i] [IsOpenImmersion j] (w : ψ ≫ j = i ≫ h) (x : P) :
    h.residueDegree (i.base x) = ψ.residueDegree x := by
  have h1 := residueDegree_comp ψ j x
  have h2 := residueDegree_comp i h x
  rw [residueDegree_eq_one_of_isOpenImmersion j, one_mul] at h1
  rw [residueDegree_eq_one_of_isOpenImmersion i, mul_one] at h2
  rw [← h1, ← h2, w]

end LocalFinite
section FibrePrimes

variable {V V' : Scheme.{u}} (h : V ⟶ V') {η : V'} {VA : V'.Opens} {VB : V.Opens}
  (e : VB ≤ h ⁻¹ᵁ VA) (hA : IsAffineOpen VA) (hB : IsAffineOpen VB) (hηA : η ∈ VA)
  (hpre : h ⁻¹ᵁ VA ≤ VB)

include hηA hpre in
/-- A point over `η ∈ VA` lies in `VB ⊇ h⁻¹ VA`. -/
theorem mem_of_mem_fibre {x : V} (hx : h.base x = η) : x ∈ VB :=
  hpre (show h.base x ∈ VA by rw [hx]; exact hηA)

/-- The prime of `Γ(V, VB)` of a point over `η` lies over the prime of `Γ(V', VA)` of `η`. -/
theorem comap_primeIdealOf_fibre {x : V} (hx : h.base x = η) :
    (hB.primeIdealOf ⟨x, mem_of_mem_fibre h hηA hpre hx⟩).asIdeal.comap
        (h.appLE VA VB e).hom = (hA.primeIdealOf ⟨η, hηA⟩).asIdeal := by
  have h1 := congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE (f := h)
    VA hA VB hB e (mem_of_mem_fibre h hηA hpre hx))
  have h2 : (⟨h.base x, e (mem_of_mem_fibre h hηA hpre hx)⟩ : VA) = ⟨η, hηA⟩ := Subtype.ext hx
  rw [h2] at h1
  exact h1

/-- **The fibre over `η` as primes over `p`.**  A point `x` of `V` over `η` gives the prime of
`Γ(V, VB)` corresponding to `x`, which lies over the prime `p` of `Γ(V', VA)` corresponding to
`η`. -/
noncomputable def fibrePrime (x : ↥(h.base ⁻¹' {η})) :
    {Q : PrimeSpectrum Γ(V, VB) //
      Q.asIdeal.comap (h.appLE VA VB e).hom = (hA.primeIdealOf ⟨η, hηA⟩).asIdeal} :=
  ⟨hB.primeIdealOf ⟨x.1, mem_of_mem_fibre h hηA hpre x.2⟩,
    comap_primeIdealOf_fibre h e hA hB hηA hpre x.2⟩

/-- **Points over `η` correspond bijectively to primes of `Γ(V, VB)` over the prime of `η`**
(for affine opens `VA ∋ η` and `VB ⊇ h⁻¹ VA` with `VB ≤ h⁻¹ VA`). -/
theorem fibrePrime_bijective : Function.Bijective (fibrePrime h e hA hB hηA hpre) := by
  refine ⟨fun x y hxy => ?_, fun Q => ?_⟩
  · have h1 := congrArg (fun P => hB.fromSpec.base P) (congrArg Subtype.val hxy)
    simp only [fibrePrime, IsAffineOpen.fromSpec_primeIdealOf] at h1
    exact Subtype.ext h1
  · have hy : h.base (hB.fromSpec.base Q.1) = η := by
      have h1 := congrArg (fun m => m.base Q.1) (IsAffineOpen.SpecMap_appLE_fromSpec h hA hB e)
      simp only [Scheme.Hom.comp_apply] at h1
      rw [← h1]
      have hQ' : (Spec.map (h.appLE VA VB e)).base Q.1 = hA.primeIdealOf ⟨η, hηA⟩ :=
        PrimeSpectrum.ext Q.2
      rw [hQ', hA.fromSpec_primeIdealOf]
    refine ⟨⟨hB.fromSpec.base Q.1, hy⟩, Subtype.ext ?_⟩
    apply hB.fromSpec.isOpenEmbedding.injective
    exact hB.fromSpec_primeIdealOf ⟨_, mem_of_mem_fibre h hηA hpre hy⟩

/-- **Residue degrees over `η` are residue degrees of primes.**  The residue degree of `h` at a
point `x` over `η` is the degree `[κ(Q) : κ(p)]` of the corresponding prime `Q` of `Γ(V, VB)` over
the prime `p` of `η`. -/
theorem residueDegree_eq_fibreDegree (x : ↥(h.base ⁻¹' {η})) :
    h.residueDegree x.1 =
      (letI := (h.appLE VA VB e).hom.toAlgebra;
        fibreDegree (hA.primeIdealOf ⟨η, hηA⟩).asIdeal (fibrePrime h e hA hB hηA hpre x).1
          (fibrePrime h e hA hB hηA hpre x).2) := by
  let _ := (h.appLE VA VB e).hom.toAlgebra
  have h1 := residueDegree_eq_of_comm (Spec.map (h.appLE VA VB e)) h hB.fromSpec hA.fromSpec
    (IsAffineOpen.SpecMap_appLE_fromSpec h hA hB e) (fibrePrime h e hA hB hηA hpre x).1
  have hx : hB.fromSpec.base (fibrePrime h e hA hB hηA hpre x).1 = x.1 :=
    hB.fromSpec_primeIdealOf _
  rw [hx] at h1
  rw [h1, NormPushforward.residueDegree_specMap' Γ(V', VA) Γ(V, VB) (h.appLE VA VB e)
    (fibrePrime h e hA hB hηA hpre x).1 _ (fibrePrime h e hA hB hηA hpre x).2.symm]
  rfl

end FibrePrimes

/-! ## Geometry: the coefficient identity over an affine finite chart -/

section AffineLocal

variable {V V' : Scheme.{u}} [IsIntegral V] [IsIntegral V'] [IsLocallyNoetherian V]
  [IsLocallyNoetherian V'] (h : V ⟶ V') [IsDominant h]
  [Algebra V'.functionField V.functionField]
  (halg : algebraMap V'.functionField V.functionField = Scheme.dominantFunctionFieldMap h)

/-- A finite index type turns the cast of a natural-number `finsum` into a `finsum` of casts. -/
theorem cast_finsum_of_finite {ι : Type*} [Finite ι] (f : ι → ℕ) :
    ((∑ᶠ i, f i : ℕ) : ℚ) = ∑ᶠ i, (f i : ℚ) := by
  have := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  push_cast
  rfl

omit [IsLocallyNoetherian V] [IsLocallyNoetherian V'] in
include halg in
/-- The function-field map of `h` is compatible with the ring map `h.appLE VA VB e` on sections
over nonempty opens. -/
theorem algebraMap_functionField_appLE {VA : V'.Opens} {VB : V.Opens} (e : VB ≤ h ⁻¹ᵁ VA)
    [Nonempty VA] [Nonempty VB] (a : Γ(V', VA)) :
    algebraMap V'.functionField V.functionField (algebraMap Γ(V', VA) V'.functionField a) =
      algebraMap Γ(V, VB) V.functionField (h.appLE VA VB e a) := by
  obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty VB›
  have h1 := Scheme.dominantFunctionFieldMap_algebraMap h x
    (V'.presheaf.germ VA (h.base x) (e hx) a)
  rw [stalkMap_germ_appLE h e x hx a, Scheme.algebraMap_germ_eq_germToFunctionField,
    Scheme.algebraMap_germ_eq_germToFunctionField] at h1
  rw [halg]
  exact h1

omit [IsIntegral V'] [IsLocallyNoetherian V'] in
/-- The order of vanishing at a point `x` of coheight one of a nonzero section `b` over an affine
open `VB ∋ x` is the order of `b` in the localization of `Γ(V, VB)` at the prime of `x`. -/
theorem ord_algebraMap_eq_ord_localization {VB : V.Opens} (hB : IsAffineOpen VB) [Nonempty VB]
    (b : Γ(V, VB)) (hb : b ≠ 0) (x : V) (hx : x ∈ VB) (hx1 : coheight x = 1) :
    V.ord (algebraMap Γ(V, VB) V.functionField b) x =
      ((Ring.ord (Localization.AtPrime (hB.primeIdealOf ⟨x, hx⟩).asIdeal)
        (algebraMap Γ(V, VB) (Localization.AtPrime (hB.primeIdealOf ⟨x, hx⟩).asIdeal)
          b)).toNat : ℤ) := by
  let _ := TopCat.Presheaf.algebra_section_stalk V.presheaf (⟨x, hx⟩ : VB)
  have _ := hB.isLocalization_stalk ⟨x, hx⟩
  have _ : Ring.KrullDimLE 1 (V.presheaf.stalk x) := krullDimLE_of_coheight_le hx1.le
  have hgerm : V.presheaf.germ VB x hx b ≠ 0 := fun h0 =>
    hb (germ_injective_of_isIntegral V x hx (by rw [h0, map_zero]))
  have hord := VectorBundle.SectionGysinIdentity.ring_ord_atPrime
    (hB.primeIdealOf ⟨x, hx⟩).asIdeal (V.presheaf.stalk x) b
  change Ring.ord (V.presheaf.stalk x) (V.presheaf.germ VB x hx b) = _ at hord
  have hfin : Ring.ord (V.presheaf.stalk x) (V.presheaf.germ VB x hx b) ≠ ⊤ :=
    Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hgerm)
  have hg : algebraMap Γ(V, VB) V.functionField b =
      algebraMap (V.presheaf.stalk x) V.functionField (V.presheaf.germ VB x hx b) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField V hx b).symm
  have hg0 : algebraMap Γ(V, VB) V.functionField b ≠ 0 := by
    rw [hg]
    exact fun h0 => hgerm (IsFractionRing.injective _ V.functionField (by rw [h0, map_zero]))
  rw [Scheme.ord_eq_iff hx1 hg0, ← hord]
  change Ring.ordFrac (V.presheaf.stalk x) (algebraMap Γ(V, VB) V.functionField b) = _
  rw [hg, Ring.ordFrac_eq_ord _ hgerm,
    Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hgerm)
      (ENat.natCast_toNat hfin).symm]
omit [IsLocallyNoetherian V] [IsLocallyNoetherian V'] in
include halg in
/-- If `h` is finite over an affine chart `VA` of `V'` (i.e. `Γ(V', VA) → Γ(V, VB)` is finite for
`VB = h⁻¹ VA`), then the function field extension `K(V) / K(V')` is finite. -/
theorem finite_functionField_of_affine {VA : V'.Opens} {VB : V.Opens} (e : VB ≤ h ⁻¹ᵁ VA)
    (hA : IsAffineOpen VA) (hB : IsAffineOpen VB) [Nonempty VA] [Nonempty VB]
    (hfin : (h.appLE VA VB e).hom.Finite) : Module.Finite V'.functionField V.functionField := by
  let φ := h.appLE VA VB e
  let _ : Algebra Γ(V', VA) Γ(V, VB) := φ.hom.toAlgebra
  have _ : Module.Finite Γ(V', VA) Γ(V, VB) := hfin
  have _ := functionField_isFractionRing_of_isAffineOpen V' VA hA
  have _ := functionField_isFractionRing_of_isAffineOpen V VB hB
  have hcompat := algebraMap_functionField_appLE h halg e
  let _ : Algebra Γ(V', VA) V.functionField :=
    ((algebraMap Γ(V, VB) V.functionField).comp φ.hom).toAlgebra
  have _ : IsScalarTower Γ(V', VA) Γ(V, VB) V.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower Γ(V', VA) V'.functionField V.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (hcompat a).symm
  have hinj : Function.Injective (algebraMap Γ(V', VA) Γ(V, VB)) := by
    intro a a' haa
    apply IsFractionRing.injective Γ(V', VA) V'.functionField
    apply (algebraMap V'.functionField V.functionField).injective
    rw [hcompat, hcompat]
    exact congrArg _ haa
  exact finite_of_isFractionRing hinj
include halg in
/-- **The coefficient identity over an affine finite chart.**  Let `h : V ⟶ V'` be a dominant
morphism of integral locally Noetherian schemes, `η` a point of coheight one of `V'` over which
every point has coheight one, and `VA ∋ η`, `VB = h⁻¹ VA` affine opens with `Γ(V', VA) → Γ(V, VB)`
finite.  For a nonzero section `b` over `VB`,
`∑_{h x = η} ord_x(b) · [κ(x) : κ(η)] = ord_η (Nm_{K(V)/K(V')} b)`. -/
theorem finsum_fibre_ord_eq_ord_norm_of_affine {η : V'} (hη : coheight η = 1)
    (hfib : (h.base ⁻¹' {η}).Finite) (hcod : ∀ x : V, h.base x = η → coheight x = 1)
    {VA : V'.Opens} {VB : V.Opens} (e : VB ≤ h ⁻¹ᵁ VA) (hA : IsAffineOpen VA)
    (hB : IsAffineOpen VB) (hηA : η ∈ VA) (hpre : h ⁻¹ᵁ VA ≤ VB)
    (hfin : (h.appLE VA VB e).hom.Finite) [Nonempty VB] (b : Γ(V, VB)) (hb : b ≠ 0) :
    (∑ᶠ x ∈ h.base ⁻¹' {η}, (V.ord (algebraMap Γ(V, VB) V.functionField b) x : ℚ) *
        (h.residueDegree x : ℚ)) =
      (V'.ord (Algebra.norm V'.functionField (algebraMap Γ(V, VB) V.functionField b)) η : ℚ) := by
  classical
  have _ : Nonempty VA := ⟨⟨η, hηA⟩⟩
  let φ := h.appLE VA VB e
  let _ : Algebra Γ(V', VA) Γ(V, VB) := φ.hom.toAlgebra
  have _ : Module.Finite Γ(V', VA) Γ(V, VB) := hfin
  have _ : IsNoetherianRing Γ(V', VA) := IsLocallyNoetherian.component_noetherian ⟨VA, hA⟩
  have _ := functionField_isFractionRing_of_isAffineOpen V' VA hA
  have _ := functionField_isFractionRing_of_isAffineOpen V VB hB
  have hcompat := algebraMap_functionField_appLE h halg e
  let _ : Algebra Γ(V', VA) V.functionField :=
    ((algebraMap Γ(V, VB) V.functionField).comp φ.hom).toAlgebra
  have _ : IsScalarTower Γ(V', VA) Γ(V, VB) V.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower Γ(V', VA) V'.functionField V.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (hcompat a).symm
  have hinj : Function.Injective (algebraMap Γ(V', VA) Γ(V, VB)) := by
    intro a a' haa
    apply IsFractionRing.injective Γ(V', VA) V'.functionField
    apply (algebraMap V'.functionField V.functionField).injective
    rw [hcompat, hcompat]
    exact congrArg _ haa
  let p := (hA.primeIdealOf ⟨η, hηA⟩).asIdeal
  let _ := TopCat.Presheaf.algebra_section_stalk V'.presheaf (⟨η, hηA⟩ : VA)
  have _ := hA.isLocalization_stalk ⟨η, hηA⟩
  have _ := functionField_isScalarTower V' VA ⟨η, hηA⟩
  have _ : Ring.KrullDimLE 1 (V'.presheaf.stalk η) := krullDimLE_of_coheight_le hη.le
  -- the fibre over `η` is indexed by the primes of `Γ(V, VB)` over `p`
  have hF := fibrePrime_bijective h e hA hB hηA hpre
  have _ : Finite {Q : PrimeSpectrum Γ(V, VB) //
      Q.asIdeal.comap (algebraMap Γ(V', VA) Γ(V, VB)) = p} := by
    have _ : Finite ↥(h.base ⁻¹' {η}) := hfib.to_subtype
    exact Finite.of_surjective _ hF.2
  have key := ordFrac_norm_eq_finsum_fibre p (K := V'.functionField) (L := V.functionField)
    (V'.presheaf.stalk η) hinj b hb
  have hNne : Algebra.norm V'.functionField (algebraMap Γ(V, VB) V.functionField b) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at key
    exact WithZero.zero_ne_coe key
  have hRHS := (Scheme.ord_eq_iff hη hNne).mpr key
  rw [hRHS, Int.cast_natCast]
  rw [cast_finsum_of_finite,
    ← finsum_subtype_eq_finsum_cond (fun x => x ∈ h.base ⁻¹' {η})]
  refine finsum_eq_of_bijective _ hF fun x => ?_
  rw [residueDegree_eq_fibreDegree h e hA hB hηA hpre x,
    ord_algebraMap_eq_ord_localization hB b hb x.1 (mem_of_mem_fibre h hηA hpre x.2)
      (hcod x.1 x.2)]
  push_cast
  exact mul_comm _ _

end AffineLocal

/-! ## Geometry: the integral case -/

/-- The norm of a nonzero element of a field extension is nonzero (it is `1` by convention when
the extension is infinite). -/
theorem norm_ne_zero_of_ne_zero {K L : Type*} [Field K] [Field L] [Algebra K L] {y : L}
    (hy : y ≠ 0) : Algebra.norm K y ≠ 0 := by
  by_cases hfin : Module.Finite K L
  · exact Algebra.norm_ne_zero_iff.mpr hy
  · rw [Algebra.norm_eq_one_of_not_module_finite hfin]
    exact one_ne_zero

section Core

variable {V V' : Scheme.{u}} [IsIntegral V] [IsIntegral V'] [IsLocallyNoetherian V]
  [IsLocallyNoetherian V'] (h : V ⟶ V') [IsProper h] [IsDominant h]
  [Algebra V'.functionField V.functionField]
  (halg : algebraMap V'.functionField V.functionField = Scheme.dominantFunctionFieldMap h)

omit [IsLocallyNoetherian V] [IsIntegral V'] [IsLocallyNoetherian V'] in
/-- In an integral scheme, two points of coheight one which specialise one to the other are
equal. -/
theorem eq_of_specializes_of_coheight_eq_one {x x' : V} (hx : coheight x = 1)
    (hx' : coheight x' = 1) (hxx' : x ⤳ x') : x = x' := by
  have c1 := (HomogeneityLocal.coheight_eq_one_iff_covBy
    (HomogeneityLocal.isTop_genericPoint V)).1 hx
  have c2 := (HomogeneityLocal.coheight_eq_one_iff_covBy
    (HomogeneityLocal.isTop_genericPoint V)).1 hx'
  by_contra hne
  have hlt : x' < x := lt_of_le_not_ge (HomogeneityLocal.le_iff_specializes.2 hxx')
    fun hle => hne (hxx'.antisymm (HomogeneityLocal.le_iff_specializes.1 hle)).eq
  exact c2.2 hlt c1.1

include halg in
/-- **The coefficient identity at a point of coheight one.**  Let `h : V ⟶ V'` be a proper
dominant morphism of integral locally Noetherian schemes and `η ∈ V'` a point of coheight one over
which every point of `V` has coheight one.  Then for every nonzero rational function `g` on `V`,
`∑_{h x = η} ord_x(g) · [κ(x) : κ(η)] = ord_η (Nm_{K(V)/K(V')} g)`. -/
theorem finsum_fibre_ord_eq_ord_norm {η : V'} (hη : coheight η = 1)
    (hcod : ∀ x : V, h.base x = η → coheight x = 1) (g : V.functionField) (hg : g ≠ 0) :
    (∑ᶠ x ∈ h.base ⁻¹' {η}, (V.ord g x : ℚ) * (h.residueDegree x : ℚ)) =
      (V'.ord (Algebra.norm V'.functionField g) η : ℚ) := by
  have hfib := finite_preimage_singleton_of_antichain h η fun x x' hx hx' hxx' =>
    eq_of_specializes_of_coheight_eq_one (hcod x hx) (hcod x' hx') hxx'
  obtain ⟨VA, VB, e, hA, hB, hηA, hpre, hfin⟩ := exists_affine_finite_of_finite_fiber h η hfib
  have hgenB : genericPoint V ∈ VB := hpre (by
    change h.base (genericPoint V) ∈ VA
    rw [Scheme.map_genericPoint_of_isDominant]
    exact ((genericPoint_spec V').mem_open_set_iff VA.isOpen).mpr ⟨η, trivial, hηA⟩)
  have _ : Nonempty VB := ⟨⟨_, hgenB⟩⟩
  have _ := functionField_isFractionRing_of_isAffineOpen V VB hB
  obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective (A := Γ(V, VB)) g
  have hb₂' : b₂ ≠ 0 := nonZeroDivisors.ne_zero hb₂
  have hb₁' : b₁ ≠ 0 := by
    rintro rfl
    simp at hg
  have hB₁ := finsum_fibre_ord_eq_ord_norm_of_affine h halg hη hfib hcod e hA hB hηA hpre hfin
    b₁ hb₁'
  have hB₂ := finsum_fibre_ord_eq_ord_norm_of_affine h halg hη hfib hcod e hA hB hηA hpre hfin
    b₂ hb₂'
  have hβ₂ : algebraMap Γ(V, VB) V.functionField b₂ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb₂
  have hord : ∀ x, V.ord (algebraMap Γ(V, VB) V.functionField b₁ /
      algebraMap Γ(V, VB) V.functionField b₂) x =
        V.ord (algebraMap Γ(V, VB) V.functionField b₁) x -
          V.ord (algebraMap Γ(V, VB) V.functionField b₂) x := by
    intro x
    have h1 := Scheme.ord_mul (x := x) hg hβ₂
    rw [div_mul_cancel₀ _ hβ₂] at h1
    omega
  have hN₂ := norm_ne_zero_of_ne_zero (K := V'.functionField) hβ₂
  have hNq := norm_ne_zero_of_ne_zero (K := V'.functionField) hg
  have hordN : V'.ord (Algebra.norm V'.functionField (algebraMap Γ(V, VB) V.functionField b₁ /
      algebraMap Γ(V, VB) V.functionField b₂)) η =
        V'.ord (Algebra.norm V'.functionField (algebraMap Γ(V, VB) V.functionField b₁)) η -
          V'.ord (Algebra.norm V'.functionField (algebraMap Γ(V, VB) V.functionField b₂)) η := by
    have h1 := Scheme.ord_mul (x := η) hNq hN₂
    rw [← map_mul, div_mul_cancel₀ _ hβ₂] at h1
    omega
  calc (∑ᶠ x ∈ h.base ⁻¹' {η}, (V.ord (algebraMap Γ(V, VB) V.functionField b₁ /
        algebraMap Γ(V, VB) V.functionField b₂) x : ℚ) * (h.residueDegree x : ℚ))
      = ∑ᶠ x ∈ h.base ⁻¹' {η},
          ((V.ord (algebraMap Γ(V, VB) V.functionField b₁) x : ℚ) * (h.residueDegree x : ℚ) -
            (V.ord (algebraMap Γ(V, VB) V.functionField b₂) x : ℚ) *
              (h.residueDegree x : ℚ)) := by
        refine finsum_mem_congr rfl fun x _ => ?_
        rw [hord]
        push_cast
        ring
    _ = _ := by
        rw [finsum_mem_sub_distrib _ _ hfib, hB₁, hB₂, hordN]
        push_cast
        ring

include halg in
/-- **Pushforward of a principal divisor along a proper dominant morphism of integral schemes.**
Let `h : V ⟶ V'` be proper and dominant between integral locally Noetherian schemes, and let
`wV`, `wV'` be weight functions such that (i) every point over a point of coheight one has
coheight one, and (ii) at a point `x` of coheight one, the weights of `x` and `h x` agree exactly
when `h x` has coheight one.  Then `h_* div(g) = div(Nm g)` for every nonzero rational
function `g` on `V`. -/
theorem map_principalCycle_eq_principalCycle_norm (wV : V → ℤ) (wV' : V' → ℤ)
    (hcod : ∀ x : V, coheight (h.base x) = 1 → coheight x = 1)
    (hw : ∀ x : V, coheight x = 1 → (wV x = wV' (h.base x) ↔ coheight (h.base x) = 1))
    (g : V.functionField) (hg : g ≠ 0) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map h wV wV' (V.principalCycle g) =
      V'.principalCycle (Algebra.norm V'.functionField g) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext η
  unfold _root_.AlgebraicGeometry.AlgebraicCycle.map
  change (∑ᶠ x ∈ h.base ⁻¹' {η}, V.principalCycle g x *
    ((_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff h wV wV' x : ℕ) : ℚ)) =
      (V'.ord (Algebra.norm V'.functionField g) η : ℚ)
  by_cases hη : coheight η = 1
  · rw [← finsum_fibre_ord_eq_ord_norm h halg hη (fun x hx => hcod x (hx ▸ hη)) g hg]
    refine finsum_mem_congr rfl fun x hx => ?_
    have hx' : h.base x = η := hx
    have hx1 : coheight x = 1 := hcod x (hx' ▸ hη)
    have hmc : _root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff h wV wV' x =
        h.residueDegree x := if_pos ((hw x hx1).2 (hx' ▸ hη))
    rw [Scheme.principalCycle_apply, hmc]
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hη, Int.cast_zero]
    apply finsum_mem_of_eqOn_zero
    intro x hx
    have hx' : h.base x = η := hx
    by_cases hx1 : coheight x = 1
    · have hmc : _root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff h wV wV' x = 0 :=
        if_neg fun hww => hη (hx' ▸ (hw x hx1).1 hww)
      simp [hmc]
    · simp [Scheme.principalCycle_apply, Scheme.ord_eq_zero_of_coheight_neq_one hx1]

end Core

/-! ## Dimension functions are unique -/

/-- Two certified dimension functions on the same scheme agree: both are the (finite) height. -/
theorem dimensionFunction_eq {X : Scheme.{u}} (d e : DimensionFunction X) : d = e := by
  refine DimensionFunction.ext fun x ↦ ?_
  have h : (Int.toNat (d x) : ℕ∞) = (Int.toNat (e x) : ℕ∞) := by
    rw [← d.height_eq, ← e.height_eq]
  have h' : Int.toNat (d x) = Int.toNat (e x) := by exact_mod_cast h
  have := d.nonnegative x
  have := e.nonnegative x
  omega

/-- Every certified dimension function on a scheme locally of finite type over a field drops by
exactly one along the covering relation of the specialisation order. -/
theorem covByDimension_of_locallyOfFiniteType {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX] (dim : DimensionFunction X) :
    HomogeneityLocal.CovByDimension dim := by
  rw [dimensionFunction_eq dim (FiniteTypeDimension.dimensionFunction sX)]
  exact covByDimension_finiteTypeDimension sX

/-- Residue-degree pushforward only depends on the morphism, not on the proof of its
quasi-compactness. -/
theorem map_congr_hom {X Y : Scheme.{u}} {f f' : X ⟶ Y} (e : f = f') [QuasiCompact f]
    [QuasiCompact f'] (wx : X → ℤ) (wy : Y → ℤ) (c : AlgebraicCycle X ℚ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f wx wy c =
      _root_.AlgebraicGeometry.AlgebraicCycle.map f' wx wy c := by
  subst e
  rfl

/-! ## Dimension bookkeeping on integral closed subschemes -/

/-- A point of an integral closed subscheme has coheight one exactly when its dimension is one
less than that of the generic point (for a dimension function dropping by one along covering
relations). -/
theorem coheight_eq_one_iff_dim_eq {X : Scheme.{u}} (Z : IntegralClosedSubscheme X)
    (dim : DimensionFunction X) (hcov : HomogeneityLocal.CovByDimension dim) (q : Z.scheme) :
    coheight q = 1 ↔ dim Z.genericPointImage = dim (Z.inclusion.base q) + 1 := by
  rw [HomogeneityLocal.coheight_eq_one_iff_covBy (HomogeneityLocal.isTop_genericPoint _)]
  constructor
  · intro hc
    exact (hcov _ _ (HomogeneityLocal.covBy_map_of_isClosedImmersion Z.inclusion hc)).symm
  · intro hd
    exact HomogeneityLocal.covBy_of_covBy_map Z.inclusion Z.inclusion.isClosedEmbedding.isInducing
      (covBy_of_dim_eq_add_one dim (Z.genericPointImage_specializes q) hd)
/-! ## The main theorem -/

section Main

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
  (dimX : DimensionFunction X) (dimY : DimensionFunction Y)

omit [IsLocallyNoetherian Y] in
/-- **Points over a codimension-one point (P2.2, dimension part).**  Let `w` be the generic point
of an integral closed subscheme `W` with `dim f(w) = dim w`, and `ξ` a point with
`dim ξ + 1 = dim w`.  Every specialisation `x` of `w` lying over `ξ` has `dim x = dim ξ`. -/
theorem dim_eq_of_mem_fiber (W : IntegralClosedSubscheme X)
    (hdim : dimY (f.base W.genericPointImage) = dimX W.genericPointImage) {ξ : Y}
    (hξ : dimY ξ + 1 = dimX W.genericPointImage) {x : X} (hwx : W.genericPointImage ⤳ x)
    (hfx : f.base x = ξ) : dimX x = dimY ξ := by
  have hle := DimensionFunction.apply_le_of_isProper dimX dimY f x
  rw [hfx] at hle
  have hne : W.genericPointImage ≠ x := by
    rintro rfl
    rw [hfx] at hdim
    omega
  have hlt := dim_lt_of_specializes dimX hwx hne
  omega

omit [IsLocallyNoetherian Y] in
/-- **Finiteness of the fibre over a codimension-one point (P2.2).**  Under the hypotheses of
`dim_eq_of_mem_fiber`, only finitely many specialisations of `w` lie over `ξ`: they are pairwise
incomparable (they all have the same dimension), and they are the points of the fibre of the
quasi-compact morphism `W → X → Y` over `ξ`. -/
theorem finite_fiber_of_dim_eq (W : IntegralClosedSubscheme X)
    (hdim : dimY (f.base W.genericPointImage) = dimX W.genericPointImage) {ξ : Y}
    (hξ : dimY ξ + 1 = dimX W.genericPointImage) :
    {x : X | W.genericPointImage ⤳ x ∧ f.base x = ξ}.Finite := by
  have hfin := finite_preimage_singleton_of_antichain (W.inclusion ≫ f) ξ
    fun q q' hq hq' hqq' => by
      have e1 := dim_eq_of_mem_fiber f dimX dimY W hdim hξ
        (W.genericPointImage_specializes q) hq
      have e2 := dim_eq_of_mem_fiber f dimX dimY W hdim hξ
        (W.genericPointImage_specializes q') hq'
      by_contra hne
      have hne' : W.inclusion.base q ≠ W.inclusion.base q' :=
        fun e => hne (W.inclusion.isClosedEmbedding.injective e)
      have := dim_lt_of_specializes dimX (hqq'.map W.inclusion.continuous) hne'
      omega
  refine (hfin.image W.inclusion.base).subset ?_
  rintro x ⟨hwx, hfx⟩
  obtain ⟨q, rfl⟩ := W.mem_range_of_specializes hwx
  exact ⟨q, hfx, rfl⟩

/-- **Finiteness of the function field extension (P2.1).**  If `dim f(w) = dim w` for the generic
point `w` of `W`, then `K(W)` is a finite extension of `K(f(W))`.  (The fibre of `W → f(W)` over
the generic point of `f(W)` is the generic point of `W` alone, so Zariski's main theorem makes
`W → f(W)` finite over an affine neighbourhood of the generic point.)

Note: this theorem is not used by the main proof chain (`map_divisor_of_dim_eq` and its
supporting lemmas); the finiteness needed there is instead supplied through the affine chart
obtained from Zariski's Main Theorem. It is recorded here as an independent deliverable. -/
theorem finite_functionField_of_dim_eq (W : IntegralClosedSubscheme X)
    (hdim : dimY (f.base W.genericPointImage) = dimX W.genericPointImage) :
    Module.Finite (W.properImage f).scheme.functionField W.scheme.functionField := by
  let hW := W.toProperImage f
  let ι' := (W.properImage f).inclusion
  have hpt : ∀ x : W.scheme, ι'.base (hW.base x) = f.base (W.inclusion.base x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      IntegralClosedSubscheme.toProperImage_inclusion]
  have hgen := W.genericPointImage_properImage f
  have hfib : (hW.base ⁻¹' {genericPoint (W.properImage f).scheme}).Finite := by
    refine (Set.finite_singleton (genericPoint W.scheme)).subset fun x hx => ?_
    have hx' : f.base (W.inclusion.base x) = f.base W.genericPointImage := by
      rw [← hpt, ← hgen]
      exact congrArg ι'.base hx
    have hle := DimensionFunction.apply_le_of_isProper dimX dimY f (W.inclusion.base x)
    by_contra hne
    have hne' : W.genericPointImage ≠ W.inclusion.base x :=
      fun e => hne (W.inclusion.isClosedEmbedding.injective e).symm
    have := dim_lt_of_specializes dimX (W.genericPointImage_specializes x) hne'
    rw [hx'] at hle
    omega
  obtain ⟨VA, VB, e, hA, hB, hηA, hpre, hfin⟩ := exists_affine_finite_of_finite_fiber hW _ hfib
  have _ : Nonempty VA := ⟨⟨_, hηA⟩⟩
  have hgenB : genericPoint W.scheme ∈ VB := hpre (by
    change hW.base (genericPoint W.scheme) ∈ VA
    rw [Scheme.map_genericPoint_of_isDominant]
    exact hηA)
  have _ : Nonempty VB := ⟨⟨_, hgenB⟩⟩
  exact finite_functionField_of_affine hW rfl e hA hB hfin
/-- The morphism `W → f(W)` followed by the inclusion of `f(W)` is `W → X → Y`, pointwise. -/
theorem inclusion_toProperImage_apply (W : IntegralClosedSubscheme X) (x : W.scheme) :
    (W.properImage f).inclusion.base ((W.toProperImage f).base x) =
      f.base (W.inclusion.base x) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    IntegralClosedSubscheme.toProperImage_inclusion]

/-- **Codimension one over codimension one.**  If `dim f(w) = dim w` and both dimension functions
drop by one along covering relations, every point of `W` lying over a point of coheight one of
`f(W)` has coheight one in `W`. -/
theorem coheight_eq_one_of_coheight_toProperImage (hcovX : HomogeneityLocal.CovByDimension dimX)
    (hcovY : HomogeneityLocal.CovByDimension dimY) (W : IntegralClosedSubscheme X)
    (hdim : dimY (f.base W.genericPointImage) = dimX W.genericPointImage) (x : W.scheme)
    (hx : coheight ((W.toProperImage f).base x) = 1) : coheight x = 1 := by
  have h2 := (coheight_eq_one_iff_dim_eq (W.properImage f) dimY hcovY _).1 hx
  rw [inclusion_toProperImage_apply, W.genericPointImage_properImage f] at h2
  have hle := DimensionFunction.apply_le_of_isProper dimX dimY f (W.inclusion.base x)
  have hne : W.genericPointImage ≠ W.inclusion.base x := by
    intro heq
    rw [← heq] at h2
    omega
  have hlt := dim_lt_of_specializes dimX (W.genericPointImage_specializes x) hne
  rw [coheight_eq_one_iff_dim_eq W dimX hcovX]
  omega

/-- **Local finiteness of `W → f(W)` over codimension-one points (P2.3).**  If `dim f(w) = dim w`
and both dimension functions drop by one along covering relations, then over every point `η` of
coheight one of `f(W)` the fibre of `W → f(W)` is finite, and there are affine opens `VA ∋ η` of
`f(W)` and `VB = (W → f(W))⁻¹ VA` of `W` such that `Γ(f(W), VA) → Γ(W, VB)` is finite.  Points
over `η` then correspond to the primes of `Γ(W, VB)` over the prime of `η`
(`fibrePrime_bijective`), with residue degrees `residueDegree_eq_fibreDegree` and orders of
vanishing `ord_algebraMap_eq_ord_localization`. -/
theorem exists_affine_finite_over (hcovX : HomogeneityLocal.CovByDimension dimX)
    (hcovY : HomogeneityLocal.CovByDimension dimY) (W : IntegralClosedSubscheme X)
    (hdim : dimY (f.base W.genericPointImage) = dimX W.genericPointImage)
    {η : (W.properImage f).scheme} (hη : coheight η = 1) :
    ((W.toProperImage f).base ⁻¹' {η}).Finite ∧
      ∃ (VA : (W.properImage f).scheme.Opens) (VB : W.scheme.Opens)
        (e : VB ≤ W.toProperImage f ⁻¹ᵁ VA), IsAffineOpen VA ∧ IsAffineOpen VB ∧ η ∈ VA ∧
          W.toProperImage f ⁻¹ᵁ VA ≤ VB ∧ ((W.toProperImage f).appLE VA VB e).hom.Finite := by
  have hfib := finite_preimage_singleton_of_antichain (W.toProperImage f) η
    fun x x' hx hx' hxx' => eq_of_specializes_of_coheight_eq_one
      (coheight_eq_one_of_coheight_toProperImage f dimX dimY hcovX hcovY W hdim x (hx ▸ hη))
      (coheight_eq_one_of_coheight_toProperImage f dimX dimY hcovX hcovY W hdim x' (hx' ▸ hη))
      hxx'
  exact ⟨hfib, exists_affine_finite_of_finite_fiber _ η hfib⟩

/-- **Pushforward of a principal divisor, equidimensional case, `CovByDimension` form.**  Let
`f : X ⟶ Y` be proper, `(W, φ)` a generator of `X` such that `dim f(w) = dim w` for the generic
point `w` of `W`, and assume both dimension functions drop by exactly one along covering
relations.  Then `f_* div(φ) = div(Nm φ)` on the image `f(W)`. -/
theorem map_divisor_of_dim_eq_of_covByDimension (hcovX : HomogeneityLocal.CovByDimension dimX)
    (hcovY : HomogeneityLocal.CovByDimension dimY) (g : RationalFunctionGenerator X)
    (hdim : dimY (f.base g.subspace.genericPointImage) = dimX g.subspace.genericPointImage) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY (g.divisor dimX) =
      (g.normImage f).divisor dimY := by
  let hW := g.subspace.toProperImage f
  let ι' := (g.subspace.properImage f).inclusion
  have hD1 := coheight_eq_one_iff_dim_eq g.subspace dimX hcovX
  have hD2 := coheight_eq_one_iff_dim_eq (g.subspace.properImage f) dimY hcovY
  rw [g.subspace.genericPointImage_properImage f] at hD2
  have hcod := coheight_eq_one_of_coheight_toProperImage f dimX dimY hcovX hcovY g.subspace hdim
  have hw : ∀ x : g.subspace.scheme, coheight x = 1 →
      ((fun z => dimX (g.subspace.inclusion.base z)) x = (fun z => dimY (ι'.base z)) (hW.base x) ↔
        coheight (hW.base x) = 1) := by
    intro x hx
    have h1 := (hD1 x).1 hx
    rw [hD2, inclusion_toProperImage_apply]
    change dimX (g.subspace.inclusion.base x) =
      dimY (f.base (g.subspace.inclusion.base x)) ↔ _
    omega
  have hcore := map_principalCycle_eq_principalCycle_norm hW rfl
    (fun z => dimX (g.subspace.inclusion.base z)) (fun z => dimY (ι'.base z)) hcod hw
    (g.function : g.subspace.scheme.functionField) g.function.ne_zero
  change _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY
      (_root_.AlgebraicGeometry.AlgebraicCycle.map g.subspace.inclusion
        (fun z => dimX (g.subspace.inclusion.base z)) dimX
        (g.subspace.scheme.principalCycle (g.function : g.subspace.scheme.functionField))) =
    _root_.AlgebraicGeometry.AlgebraicCycle.map ι' (fun z => dimY (ι'.base z)) dimY
      ((g.subspace.properImage f).scheme.principalCycle
        (Algebra.norm (g.subspace.properImage f).scheme.functionField
          (g.function : g.subspace.scheme.functionField)))
  rw [AlgebraicCycle.map_comp_of_between g.subspace.inclusion f _ dimX dimY (fun _ _ => rfl),
    ← hcore, AlgebraicCycle.map_comp_of_between hW ι' _ _ dimY (fun _ hx => hx)]
  exact map_congr_hom (IntegralClosedSubscheme.toProperImage_inclusion g.subspace f).symm _ _ _

variable {k : Type u} [Field k] (sX : X ⟶ Spec (CommRingCat.of k))
  (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]

include sX sY in
/-- **Pushforward of a principal divisor, equidimensional case** (Fulton, Prop. 1.4 (b);
Stacks, Lemma 42.20.3, case `dim f(W) = dim W`).  Let `X`, `Y` be locally of finite type over a
field `k`, `f : X ⟶ Y` proper and `(W, φ)` a generator of `X` (an integral closed subscheme with
a rational function) such that `dim f(w) = dim w` for the generic point `w` of `W`.  Then the
residue-degree pushforward of `div(φ)` is the divisor of the norm of `φ` along `K(W) / K(f(W))`,
on the image `f(W)`. -/
theorem map_divisor_of_dim_eq (g : RationalFunctionGenerator X)
    (hdim : dimY (f.base g.subspace.genericPointImage) = dimX g.subspace.genericPointImage) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY (g.divisor dimX) =
      (g.normImage f).divisor dimY :=
  map_divisor_of_dim_eq_of_covByDimension f dimX dimY
    (covByDimension_of_locallyOfFiniteType sX dimX)
    (covByDimension_of_locallyOfFiniteType sY dimY) g hdim

include sX sY in
/-- **Theorem P2** in the graded form: under the hypotheses of `map_divisor_of_dim_eq`, the
proper pushforward of the dimension-`i` cycle `div(φ)` is `div(Nm φ)`. -/
theorem properPushforward_divisor_of_dim_eq (g : RationalFunctionGenerator X)
    (hdim : dimY (f.base g.subspace.genericPointImage) = dimX g.subspace.genericPointImage)
    {i : ℤ} (hg : g.divisor dimX ∈ cyclesOfDimension X dimX i) :
    ((cyclesOfDimension.properPushforward (dimension := dimX) (dimensionY := dimY) (i := i) f
        ⟨g.divisor dimX, hg⟩ : cyclesOfDimension Y dimY i) : AlgebraicCycle Y ℚ) =
      (g.normImage f).divisor dimY :=
  map_divisor_of_dim_eq f dimX dimY sX sY g hdim

end Main

/-- **Corollary of Theorem P2.**  For `X`, `Y` locally of finite type over a field, `f : X ⟶ Y`
proper and a generator `g` of `X` whose generic point keeps its dimension under `f`, the proper
pushforward of the dimension-`i` cycle `div(g)` is a rational equivalence on `Y`. -/
theorem properPushforward_divisor_mem_relations_of_dim_eq {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (g : RationalFunctionGenerator X)
    (hdim : dimY (f.base g.subspace.genericPointImage) = dimX g.subspace.genericPointImage)
    {i : ℤ} (hg : g.divisor dimX ∈ cyclesOfDimension X dimX i) :
    cyclesOfDimension.properPushforward (dimension := dimX) (dimensionY := dimY) (i := i) f
        ⟨g.divisor dimX, hg⟩ ∈
      (RationalEquivalenceSystem.canonical : RationalEquivalenceSystem Y dimY i).relations := by
  have _ := LocallyOfFiniteType.isLocallyNoetherian sY
  change ((cyclesOfDimension.properPushforward (dimension := dimX) (dimensionY := dimY) (i := i)
    f ⟨g.divisor dimX, hg⟩ : cyclesOfDimension Y dimY i) : AlgebraicCycle Y ℚ) ∈
      totalRationalRelations Y dimY
  rw [properPushforward_divisor_of_dim_eq f dimX dimY sX sY g hdim hg]
  exact Submodule.subset_span (Set.mem_range_self _)

end ProperPushforwardDivisor

end GromovWitten.AlgebraicGeometry.IntersectionTheory
