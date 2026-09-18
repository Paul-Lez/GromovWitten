/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChernClasses

/-!
# Orders of vanishing along an affine vector bundle, and the principal-divisor comparison

`ChernClasses.lean` constructs the flat pullback `cyclesOfDimension.flatPullbackBundle` of
dimension-graded rational cycles along an affine vector bundle `E = Spec A → Spec R = X`, with
the dimension shift proved, but leaves its descent to rational equivalence open.  The recorded
obstruction was the order-of-vanishing comparison for the flat local extension
`𝒪_{Z,z} → 𝒪_{Z ×_X E, π⁻¹ z}`, whose maximal ideal is the extended one but whose residue
extension is purely transcendental, so that the etale comparison
`Ring.ord_algebraMap_of_flat_formallyUnramified_local` of `ChowGroup.lean` does not apply.

This file removes that obstruction and proves the principal-divisor comparison in the case
`Z = X`.

## The length order of a flat local extension with extended maximal ideal

* `Ring.ord_algebraMap_of_flat_local_of_map_maximalIdeal`: for a flat local extension `R → S`
  with `m_R · S = m_S`, the length order is preserved.  Only `IsLocalRing.length_baseChange` is
  used; no unramifiedness, hence arbitrary residue extensions are allowed.
* `Ring.ordMonoidWithZeroHom_algebraMap_of_flat_local_of_map_maximalIdeal` and
  `Ring.ordFrac_algebraMap_of_flat_local_of_map_maximalIdeal`: the multiplicative and fractional
  versions, for Noetherian one-dimensional domains.
* `VectorBundle.flat_localizationAtPrime_map_C`,
  `VectorBundle.map_maximalIdeal_localizationAtPrime_map_C`,
  `VectorBundle.isLocalHom_algebraMap_localizationAtPrime_map_C` and
  `VectorBundle.ord_algebraMap_localizationAtPrime_map_C`: the instance for the localisation of
  `R[ι]` at the extension `m · R[ι]` of the maximal ideal of a local ring `R`.

## Order of vanishing along a flat morphism of schemes

* `AlgebraicGeometry.Scheme.flatLocalFunctionFieldMap`: the map of function fields induced at a
  point by a morphism with flat stalk map.
* `AlgebraicGeometry.Scheme.ord_flatLocalFunctionFieldMap`: such a morphism preserves the
  scheme-theoretic order of vanishing at corresponding codimension-one points as soon as the
  stalk map extends the maximal ideal.  This is the unramifiedness-free analogue of
  `AlgebraicGeometry.Scheme.ord_etaleLocalFunctionFieldMap`.
* `AlgebraicGeometry.Scheme.flatLocalFunctionFieldMap_eq_dominantFunctionFieldMap`: for a
  dominant morphism the pointwise map is the canonical function-field pullback.
* `AlgebraicGeometry.Scheme.ord_dominantFunctionFieldMap_of_base_eq_genericPoint`: at a point
  lying over the generic point of the target the pulled-back function is a unit of the local
  ring, so its order vanishes.

## The projection of an affine vector bundle

* `VectorBundle.flat_projection`, `VectorBundle.flat_stalkMap_projection`,
  `VectorBundle.isDominant_projection`: the projection is flat and dominant.
* `VectorBundle.map_maximalIdeal_stalkMap_projection`: at a prime of the total space which is
  the extension of its contraction, the stalk map of the projection carries the maximal ideal
  onto the maximal ideal.
* `VectorBundle.height_bundlePrime`, `VectorBundle.coheight_bundlePoint`: the generic point of
  the preimage of a point has the same codimension as that point.  (Flatness gives going down,
  and the extended prime is the zero ideal of the fibre.)
* `VectorBundle.ord_bundlePoint`, `VectorBundle.ord_dominantFunctionFieldMap_bundlePoint`: the
  order of vanishing is preserved at the generic point of the preimage of every
  codimension-one point.

## The principal-divisor comparison

* `VectorBundle.pullbackBundle_principalCycle`: for `R` a Noetherian domain, the flat pullback
  of the principal divisor of a rational function of the base is the principal divisor of the
  canonically pulled-back rational function, `π^* div(f) = div(π^* f)`.
* `VectorBundle.pullbackBundle_principalCycle_mem_totalRationalRelations`: consequently such a
  pullback is a rational-equivalence relation on the total space.

## What is still missing

The descent of `flatPullbackBundle` to rational equivalence needs the same comparison for every
principal-divisor generator, that is for an arbitrary `IntegralClosedSubscheme` `Z ⊆ Spec R`
rather than for `Z = Spec R`.  What is missing for that is purely a presentation statement: the
identification of `Z.scheme` with `Spec (R ⧸ p)` (the source of a closed immersion into an affine
scheme is affine, and its coordinate ring is a quotient of `R`), of its bundle base change with
`Spec (MvPolynomial ι (R ⧸ p))`, and the resulting compatibility of
`AlgebraicCycle.pullbackBundle` with pushforward along the two closed immersions.  The
order-theoretic input is complete: `pullbackBundle_principalCycle` applies verbatim to the base
ring `R ⧸ p`.
-/

open CategoryTheory AlgebraicGeometry Order Topology TopologicalSpace

universe u

/-! ## The length order along a flat local extension with extended maximal ideal -/

/-- A flat local extension whose maximal ideal is the extension of the maximal ideal of the
base preserves the length-based order of every ring element.  Flat base change identifies the
quotient by `a` with the quotient by its image, and the hypothesis `h` identifies the extended
maximal ideal with the target maximal ideal; the remaining residue-field quotient has length
one.  No unramifiedness is required, so the residue extension may be transcendental. -/
theorem Ring.ord_algebraMap_of_flat_local_of_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (h : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S)
    (a : R) :
    Ring.ord S (algebraMap R S a) = Ring.ord R a := by
  unfold Ring.ord
  have hmap : (Ideal.span {a}).map (algebraMap R S) =
      Ideal.span {algebraMap R S a} := by
    rw [Ideal.map_span]
    congr 1
    simp
  rw [← hmap]
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
    (Ideal.span {a})).toLinearEquiv.length_eq]
  rw [IsLocalRing.length_baseChange]
  rw [h]
  have hresidue : Module.length S (S ⧸ IsLocalRing.maximalIdeal S) = 1 := by
    rw [Module.length_eq_one_iff]
    rw [isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (S := S ⧸ IsLocalRing.maximalIdeal S) Ideal.Quotient.mk_surjective]
    let _ := Ideal.Quotient.field (IsLocalRing.maximalIdeal S)
    exact instIsSimpleModule _
  rw [hresidue, mul_one]

/-- The zero-preserving multiplicative order has the same compatibility with a flat local
extension of Noetherian one-dimensional domains whose maximal ideal is extended. -/
theorem Ring.ordMonoidWithZeroHom_algebraMap_of_flat_local_of_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (h : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S)
    (a : R) :
    Ring.ordMonoidWithZeroHom S (algebraMap R S a) =
      Ring.ordMonoidWithZeroHom R a := by
  by_cases ha : a = 0
  · subst a
    simp
  let _ : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hmap : algebraMap R S a ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R S).ne ha
  rw [Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero hmap),
    Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero ha),
    Ring.ord_algebraMap_of_flat_local_of_map_maximalIdeal h]

/-- Passing to fraction fields, a flat local extension of Noetherian one-dimensional domains
whose maximal ideal is extended preserves the fractional order.  The two scalar-tower hypotheses
state that the displayed map of fraction fields extends the given local-ring map. -/
theorem Ring.ordFrac_algebraMap_of_flat_local_of_map_maximalIdeal
    {R S K L : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    [IsLocalRing R] [IsLocalRing S] [Field K] [Field L]
    [Algebra R S] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (h : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S)
    (q : K) :
    Ring.ordFrac S (algebraMap K L q) = Ring.ordFrac R q := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) q
  by_cases ha : a = 0
  · subst a
    simp
  have hb0 : b ≠ 0 := by
    simpa [mem_nonZeroDivisors_iff_ne_zero] using hb
  let _ : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hma : algebraMap R S a ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R S).ne ha
  have hmb : algebraMap R S b ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R S).ne hb0
  simp only [map_div₀]
  rw [show algebraMap K L (algebraMap R K a) =
      algebraMap S L (algebraMap R S a) by
        rw [← IsScalarTower.algebraMap_apply R K L,
          ← IsScalarTower.algebraMap_apply R S L],
    show algebraMap K L (algebraMap R K b) =
      algebraMap S L (algebraMap R S b) by
        rw [← IsScalarTower.algebraMap_apply R K L,
          ← IsScalarTower.algebraMap_apply R S L]]
  rw [Ring.ordFrac_eq_ord S hma, Ring.ordFrac_eq_ord S hmb,
    Ring.ordFrac_eq_ord R ha, Ring.ordFrac_eq_ord R hb0,
    Ring.ordMonoidWithZeroHom_algebraMap_of_flat_local_of_map_maximalIdeal h,
    Ring.ordMonoidWithZeroHom_algebraMap_of_flat_local_of_map_maximalIdeal h]

/-! ## Order of vanishing along a flat morphism with extended maximal ideal -/

namespace AlgebraicGeometry.Scheme

/-- A flat morphism of integral schemes induces a map of the function fields at any source
point: the stalk map is a flat local homomorphism, hence faithfully flat, hence injective, and
therefore extends to the fraction fields. -/
noncomputable def flatLocalFunctionFieldMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (x : X) (hf : (f.stalkMap x).hom.Flat) :
    Y.functionField →+* X.functionField := by
  let j : Y.presheaf.stalk (f.base x) →+* X.presheaf.stalk x := (f.stalkMap x).hom
  letI : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := j.toAlgebra
  let _ : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x))
      (X.presheaf.stalk x)) := by
    change IsLocalHom j
    infer_instance
  let _ : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := hf
  let _ : Module.FaithfullyFlat (Y.presheaf.stalk (f.base x))
      (X.presheaf.stalk x) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hj : Function.Injective j := by
    change Function.Injective (algebraMap (Y.presheaf.stalk (f.base x))
      (X.presheaf.stalk x))
    exact FaithfulSMul.algebraMap_injective _ _
  exact IsFractionRing.lift
    (A := Y.presheaf.stalk (f.base x)) (K := Y.functionField)
    (L := X.functionField)
    (g := (algebraMap (X.presheaf.stalk x) X.functionField).comp j)
    ((IsFractionRing.injective (X.presheaf.stalk x) X.functionField).comp hj)

@[simp]
lemma flatLocalFunctionFieldMap_algebraMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (x : X) (hf : (f.stalkMap x).hom.Flat)
    (a : Y.presheaf.stalk (f.base x)) :
    flatLocalFunctionFieldMap f x hf
        (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom a) := by
  simp [flatLocalFunctionFieldMap]

/-- Pullback along a flat morphism whose stalk map extends the maximal ideal preserves the
scheme-theoretic order of vanishing at corresponding codimension-one points.  Unlike the etale
case of `ChowGroup.lean` no unramifiedness is assumed, so this applies to the projection of an
affine vector bundle, whose residue extensions are purely transcendental. -/
lemma ord_flatLocalFunctionFieldMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (x : X) (hf : (f.stalkMap x).hom.Flat)
    (hm : Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hx : coheight x = 1) (hy : coheight (f.base x) = 1)
    (q : Y.functionField) :
    X.ord (flatLocalFunctionFieldMap f x hf q) x = Y.ord q (f.base x) := by
  let R := Y.presheaf.stalk (f.base x)
  let S := X.presheaf.stalk x
  let _ : IsDomain R := by dsimp [R]; infer_instance
  let _ : IsDomain S := by dsimp [S]; infer_instance
  let _ : IsNoetherianRing R := by dsimp [R]; infer_instance
  let _ : IsNoetherianRing S := by dsimp [S]; infer_instance
  let _ : IsLocalRing R := by dsimp [R]; infer_instance
  let _ : IsLocalRing S := by dsimp [S]; infer_instance
  let j : R →+* S := (f.stalkMap x).hom
  let _ : Algebra R S := j.toAlgebra
  let _ : IsLocalHom (algebraMap R S) := by
    change IsLocalHom j
    infer_instance
  let _ : Module.Flat R S := hf
  let _ : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hy.le
  let _ : Ring.KrullDimLE 1 S := krullDimLE_of_coheight_le hx.le
  let _ : Algebra Y.functionField X.functionField :=
    (flatLocalFunctionFieldMap f x hf).toAlgebra
  let _ : Algebra R X.functionField := RingHom.toAlgebra
    ((algebraMap S X.functionField).comp j)
  let _ : IsScalarTower R S X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R Y.functionField X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    exact (flatLocalFunctionFieldMap_algebraMap f x hf a).symm
  rw [X.ord_eq_ordHom_of_coheight_eq_one hx,
    Y.ord_eq_ordHom_of_coheight_eq_one hy]
  change Multiplicative.toAdd
      ((Ring.ordFrac S (algebraMap Y.functionField X.functionField q)).unzeroD 1) =
    Multiplicative.toAdd ((Ring.ordFrac R q).unzeroD 1)
  rw [Ring.ordFrac_algebraMap_of_flat_local_of_map_maximalIdeal
    (R := R) (S := S) (K := Y.functionField) (L := X.functionField) hm]

/-- For a dominant morphism the pointwise flat function-field map is the canonical
function-field pullback, so it does not depend on the chosen point. -/
lemma flatLocalFunctionFieldMap_eq_dominantFunctionFieldMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) (hf : (f.stalkMap x).hom.Flat) :
    flatLocalFunctionFieldMap f x hf = dominantFunctionFieldMap f := by
  apply IsFractionRing.ringHom_ext (A := Y.presheaf.stalk (f.base x))
  intro a
  rw [flatLocalFunctionFieldMap_algebraMap, dominantFunctionFieldMap_algebraMap]

/-- At the generic point every element of the function field comes from the local ring: the
function field *is* that local ring, the specialization map being the identity. -/
lemma algebraMap_stalk_surjective_of_eq_genericPoint {Y : Scheme.{u}} [IrreducibleSpace Y]
    {y : Y} (h : y = genericPoint Y) :
    Function.Surjective (algebraMap (Y.presheaf.stalk y) Y.functionField) := by
  subst h
  intro z
  refine ⟨z, ?_⟩
  change (Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial)).hom z = z
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The order of vanishing of the image of a unit of the local ring is zero. -/
lemma ord_algebraMap_of_isUnit {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {x : X} {u : X.presheaf.stalk x} (hu : IsUnit u) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField u) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · rw [X.ord_eq_ordHom_of_coheight_eq_one hx]
    have _ : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    change Multiplicative.toAdd
      ((Ring.ordFrac (X.presheaf.stalk x)
        (algebraMap (X.presheaf.stalk x) X.functionField u)).unzeroD 1) = 0
    rw [Ring.ordFrac_of_isUnit hu]
    simp
  · exact X.ord_eq_zero_of_coheight_neq_one hx _

/-- At a point lying over the generic point of the target, every rational function pulled back
from the target is a unit of the local ring, so its order of vanishing is zero.  This is the
vanishing of the pulled-back divisor away from the generic points of the preimages. -/
lemma ord_dominantFunctionFieldMap_of_base_eq_genericPoint
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f] {x : X} (h : f.base x = genericPoint Y)
    (q : Y.functionField) :
    X.ord (dominantFunctionFieldMap f q) x = 0 := by
  obtain ⟨b, rfl⟩ := algebraMap_stalk_surjective_of_eq_genericPoint h q
  rw [dominantFunctionFieldMap_algebraMap]
  by_cases hb : b = 0
  · subst hb
    simp
  · have hinj : Function.Injective
        (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField) :=
      IsFractionRing.injective _ _
    have hne : algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField b ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb
    obtain ⟨c, hc⟩ := algebraMap_stalk_surjective_of_eq_genericPoint h
      (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField b)⁻¹
    have hub : IsUnit b :=
      isUnit_iff_exists_inv.2 ⟨c, hinj (by rw [map_mul, hc, map_one, mul_inv_cancel₀ hne])⟩
    exact ord_algebraMap_of_isUnit (hub.map ((f.stalkMap x).hom))

end AlgebraicGeometry.Scheme

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace VectorBundle

/-! ## The localisation of a polynomial algebra at the extended maximal ideal -/

section PolynomialLocalization

variable {R : Type u} [CommRing R] [IsLocalRing R] {ι : Type u}

/-- The extension of the maximal ideal of a local ring to the polynomial algebra is prime. -/
instance isPrime_map_C_maximalIdeal :
    (Ideal.map (MvPolynomial.C (σ := ι)) (IsLocalRing.maximalIdeal R)).IsPrime :=
  isPrime_map_C _

variable (S : Type u) [CommRing S]
  [instAlg : Algebra (MvPolynomial ι R) S] [Algebra R S]
  [instTower : IsScalarTower R (MvPolynomial ι R) S]
  [instLoc : IsLocalization.AtPrime S
    (Ideal.map (MvPolynomial.C (σ := ι)) (IsLocalRing.maximalIdeal R))]

include instAlg instTower instLoc

/-- The localisation of a polynomial algebra over a local ring at the extension of the maximal
ideal is flat over the base: the polynomial algebra is free and localisations are flat. -/
theorem flat_localizationAtPrime_map_C : Module.Flat R S := by
  have h1 : Module.Flat (MvPolynomial ι R) S :=
    IsLocalization.flat S
      (Ideal.map (MvPolynomial.C (σ := ι)) (IsLocalRing.maximalIdeal R)).primeCompl
  exact Module.Flat.trans R (MvPolynomial ι R) S

/-- The maximal ideal of the localisation of a polynomial algebra over a local ring at the
extension of the maximal ideal is the extension of the maximal ideal of the base. -/
theorem map_maximalIdeal_localizationAtPrime_map_C [IsLocalRing S] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S := by
  rw [IsScalarTower.algebraMap_eq R (MvPolynomial ι R) S, ← Ideal.map_map]
  rw [show (algebraMap R (MvPolynomial ι R) : R →+* MvPolynomial ι R) =
      (MvPolynomial.C (σ := ι)) from rfl]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal
    (Ideal.map (MvPolynomial.C (σ := ι)) (IsLocalRing.maximalIdeal R)) S

/-- The structure map of the localisation of a polynomial algebra at the extension of the
maximal ideal is a local ring homomorphism. -/
theorem isLocalHom_algebraMap_localizationAtPrime_map_C [IsLocalRing S] :
    IsLocalHom (algebraMap R S) :=
  ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 2 0).mp
    (le_of_eq (map_maximalIdeal_localizationAtPrime_map_C (ι := ι) S))

/-- The length-based order of vanishing is preserved by the extension of a local ring to the
localisation of its polynomial algebra at the extended maximal ideal.  This is the local
statement underlying the equality `π^* div(f) = div(π^* f)` on an affine vector bundle. -/
theorem ord_algebraMap_localizationAtPrime_map_C [IsLocalRing S] (a : R) :
    Ring.ord S (algebraMap R S a) = Ring.ord R a := by
  let _ : Module.Flat R S := flat_localizationAtPrime_map_C (ι := ι) S
  let _ : IsLocalHom (algebraMap R S) :=
    isLocalHom_algebraMap_localizationAtPrime_map_C (ι := ι) S
  exact Ring.ord_algebraMap_of_flat_local_of_map_maximalIdeal
    (map_maximalIdeal_localizationAtPrime_map_C (ι := ι) S) a

end PolynomialLocalization

/-! ## The stalk map of the projection at the generic point of a fibre -/

section StalkMap

/-- Transport of the extended-maximal-ideal condition along surjective maps of local rings. -/
theorem map_maximalIdeal_comp_of_surjective
    {R₁ R₂ S₁ S₂ : Type u} [CommRing R₁] [CommRing R₂] [CommRing S₁] [CommRing S₂]
    [IsLocalRing R₁] [IsLocalRing R₂] [IsLocalRing S₁] [IsLocalRing S₂]
    (u : R₁ →+* R₂) (hu : Function.Surjective u) (g : R₂ →+* S₁)
    (v : S₁ →+* S₂) (hv : Function.Surjective v)
    (hg : Ideal.map g (IsLocalRing.maximalIdeal R₂) = IsLocalRing.maximalIdeal S₁) :
    Ideal.map ((v.comp g).comp u) (IsLocalRing.maximalIdeal R₁) =
      IsLocalRing.maximalIdeal S₂ := by
  rw [← Ideal.map_map, ← Ideal.map_map,
    IsLocalRing.map_maximalIdeal_of_surjective u hu, hg,
    IsLocalRing.map_maximalIdeal_of_surjective v hv]

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- If a prime `q` of `A` is the extension of its contraction `p`, then the localised
homomorphism `R_p → A_q` carries the maximal ideal onto the maximal ideal.  This is the
ideal-theoretic form of the statement that `q` is the generic point of the fibre over `p`. -/
theorem map_maximalIdeal_localRingHom (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R A)) (hq : q = Ideal.map (algebraMap R A) p) :
    Ideal.map (Localization.localRingHom p q (algebraMap R A) hpq)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  have hcomp : (Localization.localRingHom p q (algebraMap R A) hpq).comp
      (algebraMap R (Localization.AtPrime p)) =
      (algebraMap A (Localization.AtPrime q)).comp (algebraMap R A) := by
    ext r
    simp
  calc Ideal.map (Localization.localRingHom p q (algebraMap R A) hpq)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      = Ideal.map (Localization.localRingHom p q (algebraMap R A) hpq)
          (Ideal.map (algebraMap R (Localization.AtPrime p)) p) := by
        rw [Localization.AtPrime.map_eq_maximalIdeal]
    _ = Ideal.map ((Localization.localRingHom p q (algebraMap R A) hpq).comp
          (algebraMap R (Localization.AtPrime p))) p := Ideal.map_map _ _
    _ = Ideal.map ((algebraMap A (Localization.AtPrime q)).comp (algebraMap R A)) p := by
        rw [hcomp]
    _ = Ideal.map (algebraMap A (Localization.AtPrime q))
          (Ideal.map (algebraMap R A) p) := (Ideal.map_map _ _).symm
    _ = Ideal.map (algebraMap A (Localization.AtPrime q)) q := by rw [← hq]
    _ = IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
        Localization.AtPrime.map_eq_maximalIdeal

/-- The stalk map of the projection of an affine bundle at a prime which is the extension of
its contraction carries the maximal ideal of the base stalk onto the maximal ideal.  This is
the hypothesis of `AlgebraicGeometry.Scheme.ord_flatLocalFunctionFieldMap` for the projection;
no unramifiedness is available here, the fibre being a polynomial ring. -/
theorem map_maximalIdeal_stalkMap_projection (q : ↥(Spec (CommRingCat.of A)))
    (hq : (q : PrimeSpectrum A).asIdeal =
      Ideal.map (algebraMap R A)
        (show PrimeSpectrum R from (GradedCone.projection R A).base q).asIdeal) :
    Ideal.map ((GradedCone.projection R A).stalkMap q).hom
        (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk
          ((GradedCone.projection R A).base q))) =
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk q) := by
  have hprimeq : (q : PrimeSpectrum A).asIdeal.IsPrime := (q : PrimeSpectrum A).isPrime
  have hprimep :
      (show PrimeSpectrum R from (GradedCone.projection R A).base q).asIdeal.IsPrime :=
    (show PrimeSpectrum R from (GradedCone.projection R A).base q).isPrime
  have hiso := Scheme.localRingHom_comp_stalkIso
    (CommRingCat.ofHom (algebraMap R A)) (q : PrimeSpectrum A)
  have hu : Function.Surjective (Spec.stalkIso (CommRingCat.of R)
      (show PrimeSpectrum R from (GradedCone.projection R A).base q)).hom.hom :=
    (Spec.stalkIso (CommRingCat.of R)
      (show PrimeSpectrum R from
        (GradedCone.projection R A).base q)).commRingCatIsoToRingEquiv.surjective
  have hv : Function.Surjective
      (Spec.stalkIso (CommRingCat.of A) (q : PrimeSpectrum A)).inv.hom :=
    (Spec.stalkIso (CommRingCat.of A)
      (q : PrimeSpectrum A)).symm.commRingCatIsoToRingEquiv.surjective
  have key := map_maximalIdeal_comp_of_surjective
    (Spec.stalkIso (CommRingCat.of R)
      (show PrimeSpectrum R from (GradedCone.projection R A).base q)).hom.hom hu
    (Localization.localRingHom
      (show PrimeSpectrum R from (GradedCone.projection R A).base q).asIdeal
      (q : PrimeSpectrum A).asIdeal (algebraMap R A) rfl)
    (Spec.stalkIso (CommRingCat.of A) (q : PrimeSpectrum A)).inv.hom hv
    (map_maximalIdeal_localRingHom _ _ rfl hq)
  have hcomp : ((GradedCone.projection R A).stalkMap q).hom =
      (((Spec.stalkIso (CommRingCat.of A) (q : PrimeSpectrum A)).inv.hom).comp
        (Localization.localRingHom
          (show PrimeSpectrum R from (GradedCone.projection R A).base q).asIdeal
          (q : PrimeSpectrum A).asIdeal (algebraMap R A) rfl)).comp
        ((Spec.stalkIso (CommRingCat.of R)
          (show PrimeSpectrum R from
            (GradedCone.projection R A).base q)).hom.hom) :=
    congrArg CommRingCat.Hom.hom hiso.symm
  rw [hcomp]
  exact key

end StalkMap

/-! ## Flatness and codimension along the projection of a trivialized bundle -/

section BundleProjection

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R)

include e in
/-- The coordinate algebra of a trivialized affine vector bundle is a flat module over the
base: it is isomorphic to a free polynomial algebra. -/
theorem flat_of_trivialization : Module.Flat R A :=
  Module.Flat.of_linearEquiv e.toLinearEquiv

include e in
/-- The projection of a trivialized affine vector bundle is a flat morphism of schemes. -/
theorem flat_projection : AlgebraicGeometry.Flat (GradedCone.projection R A) := by
  have h : Module.Flat R A := flat_of_trivialization e
  change AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  rw [AlgebraicGeometry.Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.2 h

include e in
/-- Every stalk map of the projection of a trivialized affine vector bundle is flat. -/
theorem flat_stalkMap_projection (q : ↥(Spec (CommRingCat.of A))) :
    ((GradedCone.projection R A).stalkMap q).hom.Flat :=
  have := flat_projection e
  AlgebraicGeometry.Flat.stalkMap _ q

/-- The codimension of a point of `Spec R` measured in the specialization order used by
`AlgebraicGeometry.Scheme.ord` is the height of the corresponding prime ideal. -/
theorem coheight_eq_ideal_height (R : Type u) [CommRing R] (x : PrimeSpectrum R) :
    Order.coheight (show ↥(Spec (CommRingCat.of R)) from x) = x.asIdeal.height := by
  rw [PrimeSpectrum.height_eq_orderHeight]
  exact (Order.coheight_orderIso (specOrderIso R)
    (show ↥(Spec (CommRingCat.of R)) from x)).symm

include e in
/-- The height of the extension of a prime to the coordinate algebra of a trivialized affine
vector bundle equals the height of the prime.  Flatness supplies going down, and the extended
prime becomes the zero ideal of the fibre, of height zero. -/
theorem height_bundlePrime [IsNoetherianRing R] [Finite ι] (p : PrimeSpectrum R) :
    (bundlePrime e p).asIdeal.height = p.asIdeal.height := by
  have _ : Module.Flat R A := flat_of_trivialization e
  have _ : IsNoetherianRing A :=
    isNoetherianRing_of_ringEquiv (MvPolynomial ι R) e.symm.toRingEquiv
  have hlies : (bundlePrime e p).asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg PrimeSpectrum.asIdeal (comap_bundlePrime e p)).symm⟩
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    p.asIdeal (bundlePrime e p).asIdeal
  have hbot : Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R A) p.asIdeal))
      (bundlePrime e p).asIdeal = ⊥ := Ideal.map_quotient_self _
  have hprime : (Ideal.map (algebraMap R A) p.asIdeal).IsPrime := isPrime_map_algebraMap e p
  have hnt : Nontrivial (A ⧸ Ideal.map (algebraMap R A) p.asIdeal) := inferInstance
  rw [hbot, Ideal.height_bot, add_zero] at key
  exact key

include e in
/-- The codimension of the generic point of the preimage of a point of the base equals the
codimension of that point: the fibres of an affine vector bundle are irreducible of constant
dimension. -/
theorem coheight_bundlePoint [IsNoetherianRing R] [Finite ι]
    (x : ↥(Spec (CommRingCat.of R))) :
    Order.coheight (bundlePoint e x) = Order.coheight x := by
  rw [show (bundlePoint e x) =
      (show ↥(Spec (CommRingCat.of A)) from bundlePrime e (x : PrimeSpectrum R)) from rfl,
    coheight_eq_ideal_height A (bundlePrime e (x : PrimeSpectrum R)),
    coheight_eq_ideal_height R (x : PrimeSpectrum R)]
  exact height_bundlePrime e (x : PrimeSpectrum R)

include e in
/-- The coordinate algebra of a trivialized affine vector bundle over a domain is a domain. -/
theorem isDomain_of_trivialization [IsDomain R] : IsDomain A :=
  MulEquiv.isDomain (MvPolynomial ι R) e.toRingEquiv.toMulEquiv

include e in
/-- The coordinate algebra of a trivialized affine vector bundle of finite rank over a
Noetherian ring is Noetherian. -/
theorem isNoetherianRing_of_trivialization [IsNoetherianRing R] [Finite ι] :
    IsNoetherianRing A :=
  isNoetherianRing_of_ringEquiv (MvPolynomial ι R) e.symm.toRingEquiv

include e in
/-- The order of vanishing of a rational function of the base is preserved by pullback along
the projection of an affine vector bundle, at the generic point of the preimage of any
codimension-one point.  This is the local comparison `π^* div(f) = div(π^* f)` at the points of
the preimage which carry the pullback cycle. -/
theorem ord_bundlePoint [IsDomain R] [IsNoetherianRing R] [Finite ι]
    [IsDomain A] [IsNoetherianRing A]
    (x : ↥(Spec (CommRingCat.of R))) (hx : Order.coheight x = 1)
    (q : (Spec (CommRingCat.of R)).functionField) :
    (Spec (CommRingCat.of A)).ord
        (AlgebraicGeometry.Scheme.flatLocalFunctionFieldMap (GradedCone.projection R A)
          (bundlePoint e x) (flat_stalkMap_projection e (bundlePoint e x)) q)
        (bundlePoint e x) =
      (Spec (CommRingCat.of R)).ord q x := by
  have hq : (bundlePoint e x : PrimeSpectrum A).asIdeal =
      Ideal.map (algebraMap R A)
        (show PrimeSpectrum R from
          (GradedCone.projection R A).base (bundlePoint e x)).asIdeal :=
    congrArg (fun y : PrimeSpectrum R => Ideal.map (algebraMap R A) y.asIdeal)
      (projection_base_bundlePoint e x).symm
  have hy : Order.coheight ((GradedCone.projection R A).base (bundlePoint e x)) = 1 :=
    (congrArg (fun y : ↥(Spec (CommRingCat.of R)) => Order.coheight y)
      (projection_base_bundlePoint e x)).trans hx
  have hx' : Order.coheight (bundlePoint e x) = 1 := (coheight_bundlePoint e x).trans hx
  have key := AlgebraicGeometry.Scheme.ord_flatLocalFunctionFieldMap
    (GradedCone.projection R A) (bundlePoint e x)
    (flat_stalkMap_projection e (bundlePoint e x))
    (map_maximalIdeal_stalkMap_projection (bundlePoint e x) hq) hx' hy q
  rwa [projection_base_bundlePoint] at key

include e in
/-- The structure map of a trivialized affine vector bundle is injective. -/
theorem injective_algebraMap_of_trivialization : Function.Injective (algebraMap R A) := by
  intro a b hab
  have h := congrArg e hab
  rw [e.commutes, e.commutes, MvPolynomial.algebraMap_eq] at h
  exact MvPolynomial.C_injective ι R h

include e in
/-- The projection of a trivialized affine vector bundle is dominant. -/
theorem isDominant_projection : IsDominant (GradedCone.projection R A) := by
  refine ⟨?_⟩
  have hker : RingHom.ker (algebraMap R A) ≤ nilradical R := by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap R A)).1
      (injective_algebraMap_of_trivialization e)]
    exact bot_le
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R A)).2 hker

include e in
/-- The order of vanishing of a rational function of the base agrees with the order of its
canonical pullback along the projection of an affine vector bundle at the generic point of the
preimage of any point.  This is the comparison `π^* div(f) = div(π^* f)` at all the points
carrying the pullback cycle. -/
theorem ord_dominantFunctionFieldMap_bundlePoint [IsDomain R] [IsNoetherianRing R] [Finite ι]
    [IsDomain A] [IsNoetherianRing A] [IsDominant (GradedCone.projection R A)]
    (x : ↥(Spec (CommRingCat.of R))) (hx : Order.coheight x = 1)
    (q : (Spec (CommRingCat.of R)).functionField) :
    (Spec (CommRingCat.of A)).ord
        (AlgebraicGeometry.Scheme.dominantFunctionFieldMap (GradedCone.projection R A) q)
        (bundlePoint e x) =
      (Spec (CommRingCat.of R)).ord q x := by
  rw [← AlgebraicGeometry.Scheme.flatLocalFunctionFieldMap_eq_dominantFunctionFieldMap
    (GradedCone.projection R A) (bundlePoint e x)
    (flat_stalkMap_projection e (bundlePoint e x))]
  exact ord_bundlePoint e x hx q

include e in
/-- The flat pullback of a principal divisor along an affine vector bundle over an integral
Noetherian affine base is the principal divisor of the canonically pulled-back rational
function.  This is the comparison `π^* div(f) = div(π^* f)`, at the generic points of the
preimages by `ord_dominantFunctionFieldMap_bundlePoint`, and elsewhere because a point of
codimension one which is not such a generic point lies over the generic point of the base, where
the pulled-back function is a unit. -/
theorem pullbackBundle_principalCycle [IsDomain R] [IsNoetherianRing R] [Finite ι]
    [IsDomain A] [IsNoetherianRing A] [IsDominant (GradedCone.projection R A)]
    (q : (Spec (CommRingCat.of R)).functionField) :
    AlgebraicCycle.pullbackBundle e ((Spec (CommRingCat.of R)).principalCycle q) =
      (Spec (CommRingCat.of A)).principalCycle
        (AlgebraicGeometry.Scheme.dominantFunctionFieldMap (GradedCone.projection R A) q) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  dsimp only
  by_cases hy : y = bundlePoint e ((GradedCone.projection R A).base y)
  · have hL := AlgebraicCycle.pullbackBundle_apply_bundlePoint e
      ((Spec (CommRingCat.of R)).principalCycle q) ((GradedCone.projection R A).base y)
    rw [← hy] at hL
    rw [hL]
    by_cases hc : Order.coheight ((GradedCone.projection R A).base y) = 1
    · conv_rhs => rw [hy]
      simp only [AlgebraicGeometry.Scheme.principalCycle_apply]
      rw [ord_dominantFunctionFieldMap_bundlePoint e
        ((GradedCone.projection R A).base y) hc q]
    · have hcy : Order.coheight y ≠ 1 := by
        rw [hy, coheight_bundlePoint e]
        exact hc
      simp only [AlgebraicGeometry.Scheme.principalCycle_apply,
        AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hc,
        AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hcy]
  · have hnot : y ∉ Set.range (bundlePoint e) := by
      rintro ⟨x, rfl⟩
      exact hy (by rw [projection_base_bundlePoint])
    rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e _ hnot]
    by_cases hcy : Order.coheight y = 1
    · have hh : (show PrimeSpectrum A from y).asIdeal.height = 1 := by
        rw [← coheight_eq_ideal_height A (y : PrimeSpectrum A)]
        exact hcy
      have hle : (bundlePrime e
          (show PrimeSpectrum R from (GradedCone.projection R A).base y)).asIdeal ≤
          (show PrimeSpectrum A from y).asIdeal := Ideal.map_comap_le
      have hne : (bundlePrime e
          (show PrimeSpectrum R from (GradedCone.projection R A).base y)).asIdeal ≠
          (show PrimeSpectrum A from y).asIdeal := fun hcon => hy (PrimeSpectrum.ext hcon).symm
      have hst := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
      rw [hh] at hst
      have h0 : (bundlePrime e
          (show PrimeSpectrum R from
            (GradedCone.projection R A).base y)).asIdeal.height = 0 :=
        Order.lt_one_iff.1 hst
      rw [height_bundlePrime e] at h0
      have hgen : (GradedCone.projection R A).base y =
          genericPoint (Spec (CommRingCat.of R)) := by
        rw [genericPoint_eq_bot_of_affine]
        exact PrimeSpectrum.ext (Ideal.height_eq_zero_iff_eq_bot.1 h0)
      simp only [AlgebraicGeometry.Scheme.principalCycle_apply,
        AlgebraicGeometry.Scheme.ord_dominantFunctionFieldMap_of_base_eq_genericPoint
          (GradedCone.projection R A) hgen q]
      simp
    · simp only [AlgebraicGeometry.Scheme.principalCycle_apply,
        AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hcy]
      simp

include e in
/-- The flat pullback of the principal divisor of a rational function of the base is a
rational-equivalence relation on the total space, being the principal divisor of the
pulled-back function.  This is the descent of the flat pullback on all the principal-divisor
generators whose integral closed subscheme is the whole base. -/
theorem pullbackBundle_principalCycle_mem_totalRationalRelations
    [IsDomain R] [IsNoetherianRing R] [Finite ι]
    [IsDomain A] [IsNoetherianRing A] [IsDominant (GradedCone.projection R A)]
    (dimE : DimensionFunction (Spec (CommRingCat.of A)))
    (q : (Spec (CommRingCat.of R)).functionFieldˣ) :
    AlgebraicCycle.pullbackBundle e ((Spec (CommRingCat.of R)).principalCycle
        (q : (Spec (CommRingCat.of R)).functionField)) ∈
      totalRationalRelations (Spec (CommRingCat.of A)) dimE := by
  rw [pullbackBundle_principalCycle e]
  exact principalCycle_mem_totalRationalRelations (Spec (CommRingCat.of A)) dimE
    (Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap
      (GradedCone.projection R A)).toMonoidHom q)

end BundleProjection




end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
