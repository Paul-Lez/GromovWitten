/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjective

/-!
# Base change for flat pullbacks along trivialised affine vector bundles

Pure intersection theory, in the affine setting of
`IntersectionTheory/BundleHomotopyKey.lean`: `R` is a Noetherian ring, `A` an `R`-algebra with a
trivialisation `e : A ≃ₐ[R] MvPolynomial ι R` for a finite index type `ι`, and
`VectorBundle.chowPullbackBundle e` is the flat pullback `A_i(Spec R) → A_{i+r}(Spec A)` on
dimension-graded rational Chow groups.  This file proves the three compatibilities of that
pullback which are needed to compare virtual classes along a base change by a polynomial ring.

## Contents

* Degree transport: `cyclesDegreeCongr`, `chowDegreeCongr`, `chowDegreeCongr_quotientMap`.  The
  degree of a `RationalEquivalenceSystem` occurs in the *type* of its Chow group, so an identity
  which changes the shape of the degree (such as `i + r₂ + r₁ = i + r`) must be transported.
* Transitivity along a tower: `chowPullbackBundle_tower`, the Chow-group form of the cycle-level
  `VectorBundle.pullbackBundle_tower`.
* Commutation with a closed immersion: for an ideal `K` of `A` and a finite `τ`, the closed
  immersions `baseImm K : Spec (A ⧸ K) ⟶ Spec A` and
  `bundleImm K : Spec (MvPolynomial τ (A ⧸ K)) ⟶ Spec (MvPolynomial τ A)` satisfy
  `pullbackBundle_map_baseImm` (cycles), `flatPullbackBundle_properPushforward` (graded cycles)
  and `chowPullbackBundle_closedImmersionPushforward` (Chow groups).  Every closed immersion of
  affine schemes is of this form, so this is the general base-change square for a closed
  immersion and a trivial bundle.
* Commutation of the zero-section Gysin isomorphism with polynomial base change:
  `zeroSectionGysin'_chowPullbackBundle`, for the square of bundles
  `Spec (MvPolynomial τ A) → Spec A` over `Spec (MvPolynomial τ R) → Spec R`.  The trivialisation
  `polyTrivialization e : MvPolynomial τ A ≃ₐ[MvPolynomial τ R] MvPolynomial ι (MvPolynomial τ R)`
  of the base-changed bundle is constructed here.

## Hypotheses

The Gysin statement carries the homogeneity and injectivity hypotheses `hhom`, `hinj` of
`VectorBundle.zeroSectionGysin'` for both bundles; these are the inputs of the Gysin isomorphism
itself and are not assumptions specific to this file.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace VectorBundle

namespace PullbackBaseChange

/-! ## Transport of dimension-graded cycles and Chow groups along an equality of degrees -/

section Degree

variable {X : Scheme.{u}} {dimension : DimensionFunction X} {j j' : ℤ}

/-- Transport of dimension-graded rational cycles along an equality of degrees.  The underlying
algebraic cycle is unchanged. -/
def cyclesDegreeCongr (h : j = j') :
    cyclesOfDimension X dimension j ≃ₗ[ℚ] cyclesOfDimension X dimension j' :=
  LinearEquiv.ofEq _ _ (by rw [h])

@[simp]
theorem cyclesDegreeCongr_coe (h : j = j') (z : cyclesOfDimension X dimension j) :
    ((cyclesDegreeCongr h z : cyclesOfDimension X dimension j') : AlgebraicCycle X ℚ) =
      (z : AlgebraicCycle X ℚ) :=
  rfl

/-- Transport of dimension-graded rational Chow groups along an equality of degrees. -/
noncomputable def chowDegreeCongr (h : j = j')
    (RJ : RationalEquivalenceSystem X dimension j)
    (RJ' : RationalEquivalenceSystem X dimension j') :
    RJ.ChowGroup ≃ₗ[ℚ] RJ'.ChowGroup := by
  subst h
  cases RJ
  cases RJ'
  exact LinearEquiv.refl ℚ _

@[simp]
theorem chowDegreeCongr_quotientMap (h : j = j')
    (RJ : RationalEquivalenceSystem X dimension j)
    (RJ' : RationalEquivalenceSystem X dimension j')
    (z : cyclesOfDimension X dimension j) :
    chowDegreeCongr h RJ RJ' (RJ.quotientMap z) = RJ'.quotientMap (cyclesDegreeCongr h z) := by
  subst h
  cases RJ
  cases RJ'
  rfl

end Degree

/-! ## Transitivity of the Chow-group bundle pullback along a tower -/

section Tower

variable {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
  [IsNoetherianRing R] [IsNoetherianRing R']
  [Algebra R R'] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
  {ι ι₁ ι₂ : Type u} [Finite ι] [Finite ι₁] [Finite ι₂]
  (e : A ≃ₐ[R] MvPolynomial ι R) (e₁ : A ≃ₐ[R'] MvPolynomial ι₁ R')
  (e₂ : R' ≃ₐ[R] MvPolynomial ι₂ R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimR' : DimensionFunction (Spec (CommRingCat.of R')))
  (dimA : DimensionFunction (Spec (CommRingCat.of A))) (i : ℤ)

/-- **Transitivity of the flat pullback along a tower of trivialised affine vector bundles** on
dimension-graded rational Chow groups: pulling back from `Spec R` to `Spec A` in one step agrees
with pulling back to `Spec R'` and then to `Spec A`.  The degree bookkeeping
`i + r₂ + r₁ = i + r` is the hypothesis `hdeg`, and the resulting change of the Chow group's
type is absorbed by `chowDegreeCongr`. -/
theorem chowPullbackBundle_tower
    (hdeg : i + (Nat.card ι₂ : ℤ) + (Nat.card ι₁ : ℤ) = i + (Nat.card ι : ℤ))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
    (RR' : RationalEquivalenceSystem (Spec (CommRingCat.of R')) dimR' (i + (Nat.card ι₂ : ℤ)))
    (RA : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimA (i + (Nat.card ι : ℤ)))
    (RA₁ : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimA
      (i + (Nat.card ι₂ : ℤ) + (Nat.card ι₁ : ℤ))) :
    chowPullbackBundle e dimX dimA i RX RA =
      ((chowDegreeCongr hdeg RA₁ RA).toLinearMap.comp
          (chowPullbackBundle e₁ dimR' dimA (i + (Nat.card ι₂ : ℤ)) RR' RA₁)).comp
        (chowPullbackBundle e₂ dimX dimR' i RX RR') := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change RA.quotientMap (cyclesOfDimension.flatPullbackBundle e dimX dimA i z) =
    chowDegreeCongr hdeg RA₁ RA (RA₁.quotientMap
      (cyclesOfDimension.flatPullbackBundle e₁ dimR' dimA (i + (Nat.card ι₂ : ℤ))
        (cyclesOfDimension.flatPullbackBundle e₂ dimX dimR' i z)))
  rw [chowDegreeCongr_quotientMap]
  refine congrArg _ (Subtype.ext ?_)
  change AlgebraicCycle.pullbackBundle e (z : AlgebraicCycle _ ℚ) =
    AlgebraicCycle.pullbackBundle e₁
      (AlgebraicCycle.pullbackBundle e₂ (z : AlgebraicCycle _ ℚ))
  exact pullbackBundle_tower e e₁ e₂ _

end Tower

/-! ## The bundle pullback commutes with a closed immersion of the base -/

section ClosedImmersion

variable {A : Type u} [CommRing A] (K : Ideal A) {τ : Type u}

/-- The closed immersion of the closed subscheme `Spec (A ⧸ K)` into `Spec A`. -/
noncomputable abbrev baseImm : Spec (CommRingCat.of (A ⧸ K)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))

/-- The induced closed immersion of the trivial rank-`τ` bundles over `Spec (A ⧸ K)` and
`Spec A`. -/
noncomputable abbrev bundleImm :
    Spec (CommRingCat.of (MvPolynomial τ (A ⧸ K))) ⟶
      Spec (CommRingCat.of (MvPolynomial τ A)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := τ) (Ideal.Quotient.mk K)))

instance isClosedImmersion_baseImm :
    _root_.AlgebraicGeometry.IsClosedImmersion (baseImm K) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance isClosedImmersion_bundleImm :
    _root_.AlgebraicGeometry.IsClosedImmersion (bundleImm K (τ := τ)) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)

/-- The trivialisation of the trivial rank-`τ` bundle over `Spec A`. -/
noncomputable abbrev trivialBundle (A : Type u) [CommRing A] (τ : Type u) :
    MvPolynomial τ A ≃ₐ[A] MvPolynomial τ A :=
  AlgEquiv.refl

/-- Contracting an extended ideal of the restricted bundle along the restriction map gives the
extension of the contracted ideal: the trivial bundle over the closed subscheme is exactly the
preimage of the closed subscheme, on the points which carry a flat pullback. -/
theorem comap_map_map_algebraMap (Q : Ideal (A ⧸ K)) :
    Ideal.comap (MvPolynomial.map (σ := τ) (Ideal.Quotient.mk K))
        (Ideal.map (algebraMap (A ⧸ K) (MvPolynomial τ (A ⧸ K))) Q) =
      Ideal.map (algebraMap A (MvPolynomial τ A)) (Ideal.comap (Ideal.Quotient.mk K) Q) := by
  have hQ : Ideal.map (Ideal.Quotient.mk K) (Ideal.comap (Ideal.Quotient.mk K) Q) = Q :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q
  have hcomp : (MvPolynomial.map (σ := τ) (Ideal.Quotient.mk K)).comp
      (algebraMap A (MvPolynomial τ A)) =
      (algebraMap (A ⧸ K) (MvPolynomial τ (A ⧸ K))).comp (Ideal.Quotient.mk K) :=
    RingHom.ext fun a ↦ by
      simp [MvPolynomial.algebraMap_eq]
  have hmapK : Ideal.map (MvPolynomial.map (σ := τ) (Ideal.Quotient.mk K))
      (Ideal.map (algebraMap A (MvPolynomial τ A)) (Ideal.comap (Ideal.Quotient.mk K) Q)) =
      Ideal.map (algebraMap (A ⧸ K) (MvPolynomial τ (A ⧸ K))) Q := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hQ]
  have hKQ : K ≤ Ideal.comap (Ideal.Quotient.mk K) Q := by
    intro x hx
    change Ideal.Quotient.mk K x ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact Q.zero_mem
  rw [← hmapK, Ideal.comap_map_of_surjective
      (MvPolynomial.map (σ := τ) (Ideal.Quotient.mk K))
      (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective),
    ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, Ideal.mk_ker, sup_eq_left,
    MvPolynomial.algebraMap_eq]
  exact Ideal.map_mono hKQ

/-- The generic point of the fibre over a point of the closed subscheme, computed in the
restricted bundle, maps to the generic point of the fibre over its image. -/
theorem bundleImm_base_bundlePoint (x : ↥(Spec (CommRingCat.of (A ⧸ K)))) :
    (bundleImm K (τ := τ)).base (bundlePoint (trivialBundle (A ⧸ K) τ) x) =
      bundlePoint (trivialBundle A τ) ((baseImm K).base x) :=
  PrimeSpectrum.ext (comap_map_map_algebraMap K (x : PrimeSpectrum (A ⧸ K)).asIdeal)

/-- The flat pullback of a cycle pushed forward from the closed subscheme vanishes away from the
generic points of the fibres of the restricted bundle. -/
theorem pullbackBundle_map_baseImm_apply_eq_zero
    (wA : ↥(Spec (CommRingCat.of A)) → ℤ)
    (c : AlgebraicCycle (Spec (CommRingCat.of (A ⧸ K))) ℚ)
    {y : ↥(Spec (CommRingCat.of (MvPolynomial τ A)))}
    (hy : ∀ x, y ≠ (bundleImm K (τ := τ)).base (bundlePoint (trivialBundle (A ⧸ K) τ) x)) :
    AlgebraicCycle.pullbackBundle (trivialBundle A τ)
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (baseImm K)
          (fun z ↦ wA ((baseImm K).base z)) wA c) y = 0 := by
  by_cases hmem : y ∈ Set.range (bundlePoint (trivialBundle A τ))
  · obtain ⟨w, rfl⟩ := hmem
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint]
    refine AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ ?_
    rintro ⟨x, rfl⟩
    exact hy x (bundleImm_base_bundlePoint K x).symm
  · exact AlgebraicCycle.pullbackBundle_eq_zero_of_notMem _ _ hmem

/-- **The flat pullback along a trivial bundle commutes with the pushforward along a closed
immersion of the base.**  Both pushforwards use the pulled-back weight, so every multiplicity is
one and the identity is the bijection between the generic points of the fibres of the restricted
bundle and the generic points of the fibres over the closed subscheme. -/
theorem pullbackBundle_map_baseImm
    (wA : ↥(Spec (CommRingCat.of A)) → ℤ)
    (wA' : ↥(Spec (CommRingCat.of (MvPolynomial τ A))) → ℤ)
    (c : AlgebraicCycle (Spec (CommRingCat.of (A ⧸ K))) ℚ) :
    AlgebraicCycle.pullbackBundle (trivialBundle A τ)
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (baseImm K)
          (fun z ↦ wA ((baseImm K).base z)) wA c) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (bundleImm K)
        (fun z ↦ wA' ((bundleImm K (τ := τ)).base z)) wA'
        (AlgebraicCycle.pullbackBundle (trivialBundle (A ⧸ K) τ) c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  dsimp only
  by_cases hy : y ∈ Set.range (bundleImm K (τ := τ)).base
  · obtain ⟨z, rfl⟩ := hy
    rw [AlgebraicCycle.map_closedImmersion_apply_image (bundleImm K) wA'
      (AlgebraicCycle.pullbackBundle (trivialBundle (A ⧸ K) τ) c) z]
    by_cases hz : z ∈ Set.range (bundlePoint (trivialBundle (A ⧸ K) τ))
    · obtain ⟨x, rfl⟩ := hz
      rw [bundleImm_base_bundlePoint K x,
        AlgebraicCycle.pullbackBundle_apply_bundlePoint (trivialBundle A τ) _
          ((baseImm K).base x),
        AlgebraicCycle.map_closedImmersion_apply_image (baseImm K) wA c x,
        AlgebraicCycle.pullbackBundle_apply_bundlePoint (trivialBundle (A ⧸ K) τ) c x]
    · rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem _ c hz]
      refine pullbackBundle_map_baseImm_apply_eq_zero K wA c ?_
      intro x hx
      exact hz ⟨x, ((bundleImm K (τ := τ)).isClosedEmbedding.injective hx).symm⟩
  · rw [AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range (bundleImm K) wA' _ y hy]
    exact pullbackBundle_map_baseImm_apply_eq_zero K wA c fun x hx ↦ hy ⟨_, hx.symm⟩

variable [Finite τ] [IsNoetherianRing A]

/-- The fundamental-cycle form of `pullbackBundle_map_baseImm`.  The hypothesis `hfc` is the
statement that the fundamental cycle of the total space of the restricted bundle is the flat
pullback of the fundamental cycle of the closed subscheme; it is proved for Noetherian rings in
`VirtualFundamentalClass/IndependenceAcyclic.lean`, which is a later file, and is therefore taken
as an explicit hypothesis here. -/
theorem pullbackBundle_map_baseImm_fundamentalCycle
    (wA : ↥(Spec (CommRingCat.of A)) → ℤ)
    (wA' : ↥(Spec (CommRingCat.of (MvPolynomial τ A))) → ℤ)
    (hfc : AlgebraicCycle.pullbackBundle (trivialBundle (A ⧸ K) τ)
        (Spec (CommRingCat.of (A ⧸ K))).fundamentalCycle =
      (Spec (CommRingCat.of (MvPolynomial τ (A ⧸ K)))).fundamentalCycle) :
    AlgebraicCycle.pullbackBundle (trivialBundle A τ)
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (baseImm K)
          (fun z ↦ wA ((baseImm K).base z)) wA
          (Spec (CommRingCat.of (A ⧸ K))).fundamentalCycle) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (bundleImm K)
        (fun z ↦ wA' ((bundleImm K (τ := τ)).base z)) wA'
        (Spec (CommRingCat.of (MvPolynomial τ (A ⧸ K)))).fundamentalCycle := by
  rw [← hfc]
  exact pullbackBundle_map_baseImm K wA wA' _

variable (dimA : DimensionFunction (Spec (CommRingCat.of A)))
  (dimA' : DimensionFunction (Spec (CommRingCat.of (MvPolynomial τ A)))) (i : ℤ)

/-- The graded form of `pullbackBundle_map_baseImm`: the flat pullback of dimension-graded cycles
along the trivial bundle commutes with the closed-immersion pushforward. -/
theorem flatPullbackBundle_properPushforward
    (z : cyclesOfDimension (Spec (CommRingCat.of (A ⧸ K)))
      (dimA.comapClosedImmersion (baseImm K)) i) :
    cyclesOfDimension.flatPullbackBundle (trivialBundle A τ) dimA dimA' i
        (cyclesOfDimension.properPushforward (baseImm K) z) =
      cyclesOfDimension.properPushforward (bundleImm K)
        (cyclesOfDimension.flatPullbackBundle (trivialBundle (A ⧸ K) τ)
          (dimA.comapClosedImmersion (baseImm K))
          (dimA'.comapClosedImmersion (bundleImm K)) i z) := by
  refine Subtype.ext ?_
  change AlgebraicCycle.pullbackBundle (trivialBundle A τ)
      (_root_.AlgebraicGeometry.AlgebraicCycle.map (baseImm K)
        (fun z ↦ (dimA : _ → ℤ) ((baseImm K).base z)) (dimA : _ → ℤ)
        (z : AlgebraicCycle _ ℚ)) =
    _root_.AlgebraicGeometry.AlgebraicCycle.map (bundleImm K)
      (fun w ↦ (dimA' : _ → ℤ) ((bundleImm K (τ := τ)).base w)) (dimA' : _ → ℤ)
      (AlgebraicCycle.pullbackBundle (trivialBundle (A ⧸ K) τ) (z : AlgebraicCycle _ ℚ))
  exact pullbackBundle_map_baseImm K (dimA : _ → ℤ) (dimA' : _ → ℤ) _

/-- **The base-change square for a closed immersion and a trivial bundle on rational Chow
groups**: `π^* ∘ ι_* = ι'_* ∘ π'^*`. -/
theorem chowPullbackBundle_closedImmersionPushforward
    (RC : RationalEquivalenceSystem (Spec (CommRingCat.of (A ⧸ K)))
      (dimA.comapClosedImmersion (baseImm K)) i)
    (RA : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimA i)
    (RC' : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial τ (A ⧸ K))))
      (dimA'.comapClosedImmersion (bundleImm K)) (i + (Nat.card τ : ℤ)))
    (RA' : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial τ A))) dimA'
      (i + (Nat.card τ : ℤ))) :
    (chowPullbackBundle (trivialBundle A τ) dimA dimA' i RA RA').comp
        (RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward RC (baseImm K) RA) =
      (RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward
          RC' (bundleImm K) RA').comp
        (chowPullbackBundle (trivialBundle (A ⧸ K) τ) (dimA.comapClosedImmersion (baseImm K))
          (dimA'.comapClosedImmersion (bundleImm K)) i RC RC') := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change RA'.quotientMap (cyclesOfDimension.flatPullbackBundle (trivialBundle A τ) dimA dimA' i
      (cyclesOfDimension.properPushforward (baseImm K) z)) =
    RA'.quotientMap (cyclesOfDimension.properPushforward (bundleImm K)
      (cyclesOfDimension.flatPullbackBundle (trivialBundle (A ⧸ K) τ)
        (dimA.comapClosedImmersion (baseImm K))
        (dimA'.comapClosedImmersion (bundleImm K)) i z))
  exact congrArg _ (flatPullbackBundle_properPushforward K dimA dimA' i z)

end ClosedImmersion

/-! ## The zero-section Gysin isomorphism commutes with polynomial base change -/

section PolyBaseChange

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The polynomial ring over an algebra is an algebra over the polynomial ring over the base, in
a way compatible with the base. -/
theorem isScalarTower_mvPolynomial {σ : Type u} :
    IsScalarTower R (MvPolynomial σ R) (MvPolynomial σ A) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    change MvPolynomial.C (algebraMap R A r) =
      MvPolynomial.map (algebraMap R A) (MvPolynomial.C r)
    rw [MvPolynomial.map_C]

attribute [local instance] isScalarTower_mvPolynomial

variable {ι : Type u} (τ : Type u) (e : A ≃ₐ[R] MvPolynomial ι R)

/-- The trivialisation of the bundle `Spec (MvPolynomial τ A) ⟶ Spec (MvPolynomial τ R)` obtained
by base change from a trivialisation `e` of `Spec A ⟶ Spec R` along the polynomial extension
`R ⟶ MvPolynomial τ R`. -/
noncomputable def polyTrivialization :
    MvPolynomial τ A ≃ₐ[MvPolynomial τ R] MvPolynomial ι (MvPolynomial τ R) :=
  AlgEquiv.ofRingEquiv
    (f := ((MvPolynomial.mapAlgEquiv τ e).trans
      (MvPolynomial.commAlgEquiv R τ ι)).toRingEquiv)
    (by
      have key : (((MvPolynomial.mapAlgEquiv τ e).trans
            (MvPolynomial.commAlgEquiv R τ ι)).toAlgHom.toRingHom).comp
          (algebraMap (MvPolynomial τ R) (MvPolynomial τ A)) =
          algebraMap (MvPolynomial τ R) (MvPolynomial ι (MvPolynomial τ R)) := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp [MvPolynomial.algebraMap_eq]
        · intro t
          simp [MvPolynomial.algebraMap_eq]
      intro x
      exact RingHom.congr_fun key x)

/-- The trivialisation of `Spec (MvPolynomial τ A)` as a bundle over `Spec R` itself, obtained by
composing the base change with the trivialisation `e`. -/
noncomputable def totalTrivialization :
    MvPolynomial τ A ≃ₐ[R] MvPolynomial (τ ⊕ ι) R :=
  (MvPolynomial.mapAlgEquiv τ e).trans (MvPolynomial.sumAlgEquiv R τ ι).symm

/-- **The flat pullback of cycles along a trivialised affine vector bundle commutes with
polynomial base change**: the two ways of going from `Spec R` to `Spec (MvPolynomial τ A)` — first
along the bundle and then along the base change, or first along the base change and then along the
base-changed bundle — agree. -/
theorem pullbackBundle_polyBaseChange (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    AlgebraicCycle.pullbackBundle (trivialBundle A τ) (AlgebraicCycle.pullbackBundle e c) =
      AlgebraicCycle.pullbackBundle (polyTrivialization τ e)
        (AlgebraicCycle.pullbackBundle (trivialBundle R τ) c) :=
  (pullbackBundle_tower (totalTrivialization τ e) (trivialBundle A τ) e c).symm.trans
    (pullbackBundle_tower (totalTrivialization τ e) (polyTrivialization τ e)
      (trivialBundle R τ) c)

variable [Finite ι] [Finite τ] [IsNoetherianRing R] [IsNoetherianRing A]
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A)))
  (dimX' : DimensionFunction (Spec (CommRingCat.of (MvPolynomial τ R))))
  (dimE' : DimensionFunction (Spec (CommRingCat.of (MvPolynomial τ A)))) (i : ℤ)

/-- The Chow-group form of `pullbackBundle_polyBaseChange`.  The two composites land in Chow
groups of the same scheme in the two degrees `i + r + t` and `i + t + r`, which are transported
into one another by `chowDegreeCongr`. -/
theorem chowPullbackBundle_polyBaseChange
    (hdeg : i + (Nat.card ι : ℤ) + (Nat.card τ : ℤ) = i + (Nat.card τ : ℤ) + (Nat.card ι : ℤ))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
    (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ)))
    (RX' : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial τ R))) dimX'
      (i + (Nat.card τ : ℤ)))
    (RE₁ : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial τ A))) dimE'
      (i + (Nat.card ι : ℤ) + (Nat.card τ : ℤ)))
    (RE₂ : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial τ A))) dimE'
      (i + (Nat.card τ : ℤ) + (Nat.card ι : ℤ)))
    (α : RX.ChowGroup) :
    chowDegreeCongr hdeg RE₁ RE₂
        (chowPullbackBundle (trivialBundle A τ) dimE dimE' (i + (Nat.card ι : ℤ)) RE RE₁
          (chowPullbackBundle e dimX dimE i RX RE α)) =
      chowPullbackBundle (polyTrivialization τ e) dimX' dimE' (i + (Nat.card τ : ℤ)) RX' RE₂
        (chowPullbackBundle (trivialBundle R τ) dimX dimX' i RX RX' α) := by
  induction α using Quotient.inductionOn with
  | h z =>
    change chowDegreeCongr hdeg RE₁ RE₂ (RE₁.quotientMap
        (cyclesOfDimension.flatPullbackBundle (trivialBundle A τ) dimE dimE'
          (i + (Nat.card ι : ℤ)) (cyclesOfDimension.flatPullbackBundle e dimX dimE i z))) =
      RE₂.quotientMap (cyclesOfDimension.flatPullbackBundle (polyTrivialization τ e) dimX' dimE'
        (i + (Nat.card τ : ℤ))
        (cyclesOfDimension.flatPullbackBundle (trivialBundle R τ) dimX dimX' i z))
    rw [chowDegreeCongr_quotientMap]
    refine congrArg _ (Subtype.ext ?_)
    change AlgebraicCycle.pullbackBundle (trivialBundle A τ)
        (AlgebraicCycle.pullbackBundle e (z : AlgebraicCycle _ ℚ)) =
      AlgebraicCycle.pullbackBundle (polyTrivialization τ e)
        (AlgebraicCycle.pullbackBundle (trivialBundle R τ) (z : AlgebraicCycle _ ℚ))
    exact pullbackBundle_polyBaseChange τ e _

/-- **The zero-section Gysin isomorphism commutes with polynomial base change.**  For the square
of bundles `Spec (MvPolynomial τ A) ⟶ Spec A` over `Spec (MvPolynomial τ R) ⟶ Spec R`, pulling a
class back to the base-changed total space and applying the Gysin isomorphism of the base-changed
bundle gives the same answer as applying the Gysin isomorphism of the original bundle and then
pulling back along the base change. -/
theorem zeroSectionGysin'_chowPullbackBundle
    (hdeg : i + (Nat.card ι : ℤ) + (Nat.card τ : ℤ) = i + (Nat.card τ : ℤ) + (Nat.card ι : ℤ))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
    (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ)))
    (RX' : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial τ R))) dimX'
      (i + (Nat.card τ : ℤ)))
    (RE₁ : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial τ A))) dimE'
      (i + (Nat.card ι : ℤ) + (Nat.card τ : ℤ)))
    (RE₂ : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial τ A))) dimE'
      (i + (Nat.card τ : ℤ) + (Nat.card ι : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE)
    (hinj : Function.Injective (chowPullbackBundle e dimX dimE i RX RE))
    (hhom' : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of (MvPolynomial τ A))) dimE')
    (hinj' : Function.Injective (chowPullbackBundle (polyTrivialization τ e) dimX' dimE'
      (i + (Nat.card τ : ℤ)) RX' RE₂))
    (β : RE.ChowGroup) :
    zeroSectionGysin' (polyTrivialization τ e) dimX' dimE' (i + (Nat.card τ : ℤ)) RX' RE₂
        hhom' hinj'
        (chowDegreeCongr hdeg RE₁ RE₂
          (chowPullbackBundle (trivialBundle A τ) dimE dimE' (i + (Nat.card ι : ℤ)) RE RE₁ β)) =
      chowPullbackBundle (trivialBundle R τ) dimX dimX' i RX RX'
        (zeroSectionGysin' e dimX dimE i RX RE hhom hinj β) := by
  obtain ⟨α, rfl⟩ : ∃ α, chowPullbackBundle e dimX dimE i RX RE α = β :=
    ⟨zeroSectionGysin' e dimX dimE i RX RE hhom hinj β,
      pullback_zeroSectionGysin' e dimX dimE i RX RE hhom hinj β⟩
  rw [zeroSectionGysin'_pullback, chowPullbackBundle_polyBaseChange τ e dimX dimE dimX' dimE' i
    hdeg RX RE RX' RE₁ RE₂ α, zeroSectionGysin'_pullback]

end PolyBaseChange

end PullbackBaseChange

end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
