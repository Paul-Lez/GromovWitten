/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ConeGluing
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.LocalisationCone
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Independence
import GromovWitten.AlgebraicGeometry.Cones.RefinementNormalSheaf

/-!
# The overlap hypothesis of `LocalConeData` from local embeddings

`VirtualFundamentalClass/ConeGluing.lean` glues a global cone out of local affine obstruction
models `φ j` on the charts of a bundle `𝓔 : BundleData X ι`.  Its input `LocalConeData 𝓔 φ`
carries one geometric hypothesis, `LocalConeData.compat`: over every affine open `W` of the
overlap of two charts `i`, `j` the two resolved-cone ideals extend to the *same* ideal of
`𝓔.algebra.ring W`.  Stated like that the hypothesis is an ad-hoc equality of ideals.

This file shows that it is a *consequence* of the data one actually has in the geometric
situation, namely of local embeddings of `W` into the two affine models.  The input is packaged
in two steps.

* `LocalEmbeddingCore 𝓔 φ` carries, besides the chart identifications `chartBase`,
  `chartBundle`, `chartBundle_algebraMap` of `LocalConeData`, for every chart `j` and every
  affine open `W ≤ 𝓔.chart j`:
  - a flat, formally étale `R j`-algebra `chartRing j W h` together with a ring isomorphism
    `chartBaseExt j W h : (R' ⧸ (I j)·R') ≃+* Γ(X, W.1)` compatible with `chartBase j` and the
    restriction map `res X h` (field `chartBaseExt_algebraMap`) — that is, `W` is presented as a
    flat formally étale neighbourhood inside the affine model of the chart `j`;
  - a ring isomorphism `chartBundleExt j W h` of the bundle algebra `𝓔.algebra.ring W` with the
    bundle ring of the *base-changed* obstruction datum
    `LocalisationCone.baseChangeHom (I j) (chartRing j W h) (φ j)`, compatible with the
    transition map `𝓔.algebra.map h` and the canonical base-change map `baseChangeBundleHom`
    (field `chartBundleExt_map`).
* `CompatibleLocalEmbeddingData 𝓔 φ` extends it with the comparison of two charts over the same
  `W`: an isomorphism `transition i j W hi hj` of the two base-changed bundle rings which is
  compatible with the two identifications of `𝓔.algebra.ring W` (`transition_chartBundleExt`).  Its
  `transition_comparison` is an `OverlapComparison`: either a direct intrinsic
  obstruction-theory/refinement comparison, or two such comparisons into a common refinement.

## Main results

* `ideal_map_baseChangeBundleHom` — the resolved-cone ideal of a flat formally étale base change
  is the extension of the resolved-cone ideal.  This is
  `LocalisationCone.ideal_map_bundleRingEquiv` rewritten along the canonical ring map
  `baseChangeBundleHom`, and it is what makes the reduction below work.
* `CompatibleLocalEmbeddingData.map_chartIdeal_eq` — over `W` the extended chart ideal of chart `i`
  is the transport of the resolved-cone ideal of the base-changed datum.  Only
  `LocalEmbeddingCore` data enters.
* `CompatibleLocalEmbeddingData.compat` — **the overlap hypothesis of `LocalConeData` is a
  theorem**.
  `CompatibleLocalEmbeddingData.toLocalConeData` packages the whole input as a `LocalConeData 𝓔 φ`.
* `IntrinsicComparison.ideal_map` — the resolved-cone ideal compatibility theorem.  It is proved
  from the intrinsic comparison of the product maps, using that the comparison is an isomorphism;
  no ideal equality is stored in local embedding data.
* `RefinementComparison.ideal_map` and `CommonRefinementComparison.ideal_map` — the corresponding
  kernel arguments when the cone transport is only split-injective and when two local models share
  a common refinement.
* `LocalEmbeddingCore.toCompatibleLocalEmbeddingDataOfAffine` — sanity check: for the round-17
  affine
  bundle datum `GlobalConeAffine.bundleData φ`, whose chart index type is `PUnit`, the
  comparison data of `CompatibleLocalEmbeddingData` can always be taken to be the identity, so every
  `LocalEmbeddingCore` is already a `CompatibleLocalEmbeddingData`.

## What is an explicit hypothesis and what is proved

The comparison is stated over the quotient-ring isomorphism induced by the two presentations of
`Γ(X, W)`.  A direct comparison records semilinear transport of both terms of the obstruction
complexes and ambient/refinement transport of the resolved-cone factor.  A refinement comparison
allows the target conormal map and cone map to be noninvertible, provided the cone map has the
geometric retraction supplied by the common ambient chart.  In either case the product-ring map is
constructed from the cone and degree-one transports, and the ideal equality is derived from the
kernel description.  Thus the overlap theorem is conditional on compatible local embedding data;
`LocalEmbeddingCore` by itself does not assert that every pair of presentations admits a common
refinement comparison.
-/

universe u

-- As in `ResolvedCone.lean` and `ConeGluing.lean`: the ring instances of the tensor products
-- occurring in `ResolvedCone.ideal` need one more level of pending instance problems.
set_option maxSynthPendingDepth 5

-- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
-- type of affine opens; as in `ConeGluing.lean` the unifier is told not to respect transparency.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

open IntersectionTheory hiding Scheme AlgebraicCycle
open VectorBundleTotalSpace RelativeSpec
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open VirtualFundamentalClass
open GlobalBlowup (res)

namespace VirtualClass.ConeGluing

noncomputable section

/-! ## The normal-sheaf transport supplied by a polynomial refinement -/

section NormalSheafRefinement

variable {R : Type u} [CommRing R] (τ : Type u) (I : Ideal R)

/-- The polynomial refinement equivalence on the canonical normal-sheaf coordinate rings.

It is obtained by transporting the normal-sheaf product equivalence through the quotient
presentation `normalSheafRingEquiv`; no comparison of resolved-cone ideals is part of this
definition.  The source polynomial variables become the classes of the new ambient variables. -/
def normalSheafCoordinateRefinementEquiv :
    MvPolynomial τ (AffineNormalCone.normalSheafCoordinateRing R I) ≃+*
      AffineNormalCone.normalSheafCoordinateRing (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I) :=
  (MvPolynomial.mapEquiv τ
      (AffineNormalCone.normalSheafRingEquiv R I).toRingEquiv).symm.trans
    ((ConeRefinement.nsProdEquiv τ I).trans
      ((AffineNormalCone.normalSheafRingEquiv (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I)).toRingEquiv))

@[simp]
theorem normalSheafCoordinateRefinementEquiv_apply (w :
    MvPolynomial τ (AffineNormalCone.normalSheafCoordinateRing R I)) :
    normalSheafCoordinateRefinementEquiv τ I w =
      (AffineNormalCone.normalSheafRingEquiv (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I))
        (ConeRefinement.nsProdEquiv τ I
          ((MvPolynomial.mapEquiv τ
            (AffineNormalCone.normalSheafRingEquiv R I).toRingEquiv).symm w)) :=
  rfl

def normalSheafCoordinateRefinementHom :
    MvPolynomial τ (AffineNormalCone.normalSheafCoordinateRing R I) →+*
      AffineNormalCone.normalSheafCoordinateRing (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I) :=
  (normalSheafCoordinateRefinementEquiv τ I).toRingHom

def coneRefinementHom :
    MvPolynomial τ (AffineNormalCone.associatedGradedRing R I) →+*
      AffineNormalCone.associatedGradedRing (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I) :=
  (ConeRefinement.prodEquiv (τ := τ) (I := I)).toRingHom

/-- The cone-ring inclusion for the ambient polynomial refinement.  It is the constant-polynomial
inclusion followed by the product equivalence, so its source is the old cone ring rather than the
polynomial presentation of that ring. -/
def coneRefinementMap :
    AffineNormalCone.associatedGradedRing R I →+*
      AffineNormalCone.associatedGradedRing (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I) :=
  (ConeRefinement.prodEquiv (τ := τ) (I := I)).toRingHom.comp
    (MvPolynomial.C : AffineNormalCone.associatedGradedRing R I →+*
      MvPolynomial τ (AffineNormalCone.associatedGradedRing R I))

@[simp]
theorem coneRefinementMap_apply (c : AffineNormalCone.associatedGradedRing R I) :
    coneRefinementMap τ I c = ConeRefinement.grIncl τ I c := by
  change (ConeRefinement.prodEquiv (τ := τ) (I := I)) (MvPolynomial.C c) = _
  rw [ConeRefinement.prodEquiv_apply, ConeRefinement.prodMap_C]

/-- Evaluation at the added ambient variables retracts the cone inclusion. -/
def coneRefinementRetraction :
    AffineNormalCone.associatedGradedRing (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I) →+*
      AffineNormalCone.associatedGradedRing R I :=
  (MvPolynomial.constantCoeff :
      MvPolynomial τ (AffineNormalCone.associatedGradedRing R I) →+*
        AffineNormalCone.associatedGradedRing R I).comp
    (ConeRefinement.prodEquiv (τ := τ) (I := I)).symm.toRingHom

theorem coneRefinementRetraction_leftInverse :
    Function.LeftInverse (coneRefinementRetraction τ I) (coneRefinementMap τ I) := by
  intro c
  change MvPolynomial.constantCoeff
      ((ConeRefinement.prodEquiv (τ := τ) (I := I)).symm
        ((ConeRefinement.prodEquiv (τ := τ) (I := I)) (MvPolynomial.C c))) = c
  rw [(ConeRefinement.prodEquiv (τ := τ) (I := I)).symm_apply_apply,
    MvPolynomial.constantCoeff_C]

theorem coneRefinementMap_injective : Function.Injective (coneRefinementMap τ I) :=
  (coneRefinementRetraction_leftInverse τ I).injective

/-- The quotient map induced by the constant-coefficient section of the polynomial refinement. -/
def coneRefinementQuotientMap :
    R ⧸ I →+* (MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I :=
  Ideal.quotientMap (ConeRefinement.polyExt τ I)
    (MvPolynomial.C : R →+* MvPolynomial τ R) (by
      intro r hr
      exact ConeRefinement.C_mem_polyExt hr)

def coneRefinementQuotientRetraction :
    (MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I →+* R ⧸ I :=
  Ideal.quotientMap I (MvPolynomial.constantCoeff : MvPolynomial τ R →+* R) (by
    intro p hp
    exact hp)

theorem coneRefinementQuotientRetraction_leftInverse :
    Function.LeftInverse (coneRefinementQuotientRetraction τ I)
      (coneRefinementQuotientMap τ I) := by
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [coneRefinementQuotientRetraction, coneRefinementQuotientMap]

theorem coneRefinementQuotientMap_surjective :
    Function.Surjective (coneRefinementQuotientMap τ I) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨Ideal.Quotient.mk I (MvPolynomial.constantCoeff p), ?_⟩
  simp only [coneRefinementQuotientMap, Ideal.quotientMap_mk]
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  rw [ConeRefinement.mem_polyExt_iff, map_sub, MvPolynomial.constantCoeff_C,
    sub_self]
  exact Ideal.zero_mem _

noncomputable def coneRefinementQuotientEquiv :
    R ⧸ I ≃+* (MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I :=
  RingEquiv.ofBijective (coneRefinementQuotientMap τ I) ⟨
    (coneRefinementQuotientRetraction_leftInverse τ I).injective,
    coneRefinementQuotientMap_surjective τ I⟩

theorem coneRefinementQuotientEquiv_apply (x : R ⧸ I) :
    coneRefinementQuotientEquiv τ I x = coneRefinementQuotientMap τ I x :=
  rfl

/-- The canonical cone map commutes with the normal-sheaf refinement transport.  This is the
generator-level comparison used when a polynomial ambient variable is added: constants are sent
through `nsIncl`, while each new variable is sent to its degree-one normal-cone class. -/
theorem normalSheafCoordinateRefinementEquiv_comp_coordinateMap :
    (AffineNormalCone.normalSheafCoordinateMap (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I)).comp
        (normalSheafCoordinateRefinementHom τ I) =
      (coneRefinementHom τ I).comp
        (MvPolynomial.map
          (AffineNormalCone.normalSheafCoordinateMap R I)) := by
  have hcoord (A : Type u) [CommRing A] (J : Ideal A) :
      (AffineNormalCone.normalSheafCoordinateMap A J).comp
          (AffineNormalCone.normalSheafRingEquiv A J).toRingEquiv.toRingHom =
        (AffineNormalCone.nsToGr A J).toRingHom :=
    AffineNormalCone.normalSheafCoordinateMap_comp_equiv A J
  have hns := ConeRefinement.nsToGr_comp_nsProdMap (τ := τ) (I := I)
  apply MvPolynomial.ringHom_ext
  · intro w
    simp only [normalSheafCoordinateRefinementHom, coneRefinementHom,
      RingHom.comp_apply]
    change AffineNormalCone.normalSheafCoordinateMap (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I)
        (normalSheafCoordinateRefinementEquiv τ I (MvPolynomial.C w)) =
      (ConeRefinement.prodEquiv (τ := τ) (I := I))
        (MvPolynomial.map (AffineNormalCone.normalSheafCoordinateMap R I)
          (MvPolynomial.C w))
    rw [normalSheafCoordinateRefinementEquiv_apply, MvPolynomial.mapEquiv_symm,
      MvPolynomial.mapEquiv_apply, MvPolynomial.map_C, MvPolynomial.map_C]
    change AffineNormalCone.normalSheafCoordinateMap (MvPolynomial τ R)
      (ConeRefinement.polyExt τ I)
      ((AffineNormalCone.normalSheafRingEquiv (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I))
        (ConeRefinement.nsProdEquiv τ I
          (MvPolynomial.C ((AffineNormalCone.normalSheafRingEquiv R I).symm w)))) = _
    calc
      AffineNormalCone.normalSheafCoordinateMap (MvPolynomial τ R)
          (ConeRefinement.polyExt τ I)
          ((AffineNormalCone.normalSheafRingEquiv (MvPolynomial τ R)
            (ConeRefinement.polyExt τ I))
            (ConeRefinement.nsProdEquiv τ I
              (MvPolynomial.C ((AffineNormalCone.normalSheafRingEquiv R I).symm w)))) =
          AffineNormalCone.nsToGr (MvPolynomial τ R)
            (ConeRefinement.polyExt τ I)
            (ConeRefinement.nsProdEquiv τ I
              (MvPolynomial.C ((AffineNormalCone.normalSheafRingEquiv R I).symm w))) :=
        DFunLike.congr_fun (hcoord (MvPolynomial τ R) (ConeRefinement.polyExt τ I)) _
      _ = AffineNormalCone.nsToGr (MvPolynomial τ R)
          (ConeRefinement.polyExt τ I)
          (ConeRefinement.nsProdMap τ I
            (MvPolynomial.C ((AffineNormalCone.normalSheafRingEquiv R I).symm w))) := by
        rw [ConeRefinement.nsProdEquiv_apply]
      _ = ConeRefinement.prodMap τ I
          (MvPolynomial.map (AffineNormalCone.nsToGr R I).toRingHom
            (MvPolynomial.C ((AffineNormalCone.normalSheafRingEquiv R I).symm w))) :=
        DFunLike.congr_fun hns _
      _ = (ConeRefinement.prodEquiv (τ := τ) (I := I))
          (MvPolynomial.C (AffineNormalCone.normalSheafCoordinateMap R I w)) := by
        have hc := DFunLike.congr_fun
          (hcoord R I) ((AffineNormalCone.normalSheafRingEquiv R I).symm w)
        change AffineNormalCone.normalSheafCoordinateMap R I
            ((AffineNormalCone.normalSheafRingEquiv R I)
              ((AffineNormalCone.normalSheafRingEquiv R I).symm w)) =
          AffineNormalCone.nsToGr R I
            ((AffineNormalCone.normalSheafRingEquiv R I).symm w) at hc
        rw [(AffineNormalCone.normalSheafRingEquiv R I).apply_symm_apply] at hc
        rw [MvPolynomial.map_C]
        change (ConeRefinement.prodMap τ I)
            (MvPolynomial.C
              (AffineNormalCone.nsToGr R I
                ((AffineNormalCone.normalSheafRingEquiv R I).symm w))) = _
        rw [← hc]
        rfl
  · intro t
    simp only [normalSheafCoordinateRefinementHom, coneRefinementHom,
      RingHom.comp_apply]
    change AffineNormalCone.normalSheafCoordinateMap (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I)
        (normalSheafCoordinateRefinementEquiv τ I (MvPolynomial.X t)) =
      (ConeRefinement.prodEquiv (τ := τ) (I := I))
        (MvPolynomial.map (AffineNormalCone.normalSheafCoordinateMap R I)
          (MvPolynomial.X t))
    rw [normalSheafCoordinateRefinementEquiv_apply, MvPolynomial.mapEquiv_symm,
      MvPolynomial.mapEquiv_apply, MvPolynomial.map_X, MvPolynomial.map_X]
    calc
      AffineNormalCone.normalSheafCoordinateMap (MvPolynomial τ R)
          (ConeRefinement.polyExt τ I)
          ((AffineNormalCone.normalSheafRingEquiv (MvPolynomial τ R)
            (ConeRefinement.polyExt τ I))
            (ConeRefinement.nsProdEquiv τ I (MvPolynomial.X t))) =
          AffineNormalCone.nsToGr (MvPolynomial τ R)
            (ConeRefinement.polyExt τ I)
            (ConeRefinement.nsProdEquiv τ I (MvPolynomial.X t)) :=
        DFunLike.congr_fun (hcoord (MvPolynomial τ R) (ConeRefinement.polyExt τ I)) _
      _ = AffineNormalCone.nsToGr (MvPolynomial τ R)
          (ConeRefinement.polyExt τ I)
          (ConeRefinement.nsProdMap τ I (MvPolynomial.X t)) := by
        rw [ConeRefinement.nsProdEquiv_apply]
      _ = ConeRefinement.prodMap τ I
          (MvPolynomial.map (AffineNormalCone.nsToGr R I).toRingHom
            (MvPolynomial.X t)) := DFunLike.congr_fun hns _
      _ = (ConeRefinement.prodEquiv (τ := τ) (I := I))
          (MvPolynomial.X t) := by
        rw [MvPolynomial.map_X]
        rfl

/-- A generator check for the cone component of an overlap comparison.  Once the transported
normal-sheaf equivalence is known on the old conormal generators, its cone square determines the
transport of `conormalToAssociatedGraded`; this is the form consumed by an intrinsic comparison. -/
theorem normalSheafCoordinateRefinementEquiv_conormal_generator
    (q : I.Cotangent → (ConeRefinement.polyExt τ I).Cotangent)
    (hgen : ∀ x : I.Cotangent,
      normalSheafCoordinateRefinementEquiv τ I
          (MvPolynomial.C
            (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent x)) =
        SymmetricAlgebra.ι ((MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I)
          (ConeRefinement.polyExt τ I).Cotangent (q x))
    (x : I.Cotangent) :
    ConeRefinement.prodEquiv (τ := τ) (I := I)
        (MvPolynomial.C (AffineNormalCone.conormalToAssociatedGraded R I x)) =
      AffineNormalCone.conormalToAssociatedGraded (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I) (q x) := by
  have hsquare := DFunLike.congr_fun
    (normalSheafCoordinateRefinementEquiv_comp_coordinateMap τ I)
    (MvPolynomial.C (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent x))
  simp only [normalSheafCoordinateRefinementHom, coneRefinementHom,
    RingHom.comp_apply] at hsquare
  change AffineNormalCone.normalSheafCoordinateMap (MvPolynomial τ R)
      (ConeRefinement.polyExt τ I)
      (normalSheafCoordinateRefinementEquiv τ I
        (MvPolynomial.C (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent x))) =
    (ConeRefinement.prodEquiv (τ := τ) (I := I))
      (MvPolynomial.map (AffineNormalCone.normalSheafCoordinateMap R I)
        (MvPolynomial.C (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent x))) at hsquare
  rw [MvPolynomial.map_C,
    AffineNormalCone.normalSheafCoordinateMap_ι, hgen x,
    AffineNormalCone.normalSheafCoordinateMap_ι] at hsquare
  exact hsquare.symm

/-- The cone inclusion for a polynomial ambient refinement carries the old conormal generator to
the generator selected by the corresponding conormal transport.  This is the concrete
conormal-map equation consumed by a `RefinementComparison` leg. -/
theorem coneRefinementMap_conormal_generator
    (q : I.Cotangent → (ConeRefinement.polyExt τ I).Cotangent)
    (hgen : ∀ x : I.Cotangent,
      normalSheafCoordinateRefinementEquiv τ I
          (MvPolynomial.C
            (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent x)) =
        SymmetricAlgebra.ι ((MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I)
          (ConeRefinement.polyExt τ I).Cotangent (q x))
    (x : I.Cotangent) :
    coneRefinementMap τ I (AffineNormalCone.conormalToAssociatedGraded R I x) =
      AffineNormalCone.conormalToAssociatedGraded (MvPolynomial τ R)
        (ConeRefinement.polyExt τ I) (q x) := by
  change (ConeRefinement.prodEquiv (τ := τ) (I := I))
      (MvPolynomial.C (AffineNormalCone.conormalToAssociatedGraded R I x)) = _
  exact normalSheafCoordinateRefinementEquiv_conormal_generator τ I q hgen x

end NormalSheafRefinement

/-! ## A congruence lemma for `Ideal.map` -/

/-- Two ring homomorphisms (of possibly different bundled types) with the same underlying
function extend an ideal to the same ideal. -/
theorem ideal_map_congr_hom {A B : Type u} [Semiring A] [Semiring B] {F G : Type*}
    [FunLike F A B] [RingHomClass F A B] [FunLike G A B] [RingHomClass G A B] (f : F) (g : G)
    (h : ∀ a, f a = g a) (J : Ideal A) : J.map f = J.map g := by
  have himg : (f : A → B) '' (J : Set A) = (g : A → B) '' (J : Set A) :=
    Set.image_congr fun a _ => h a
  change Ideal.span _ = Ideal.span _
  rw [himg]

/-- Two ring homomorphisms (of possibly different bundled types) with the same underlying
function contract an ideal to the same ideal. -/
theorem ideal_comap_congr_hom {A B : Type u} [Semiring A] [Semiring B] {F G : Type*}
    [FunLike F A B] [RingHomClass F A B] [FunLike G A B] [RingHomClass G A B] (f : F) (g : G)
    (h : ∀ a, f a = g a) (J : Ideal B) : J.comap f = J.comap g := by
  ext a
  simp only [Ideal.mem_comap, h a]

/-! ## The canonical map to the base-changed bundle ring -/

section BaseChange

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R)
variable (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra k R'] [IsScalarTower k R R']
variable [Module.Flat R R'] [Algebra.FormallyEtale R R']
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-- The canonical ring map from the bundle ring `Sym(E⁻¹)` of an affine obstruction datum to the
bundle ring of its base change along a flat formally étale extension `R → R'`.  It is the
inclusion `b ↦ 1 ⊗ b` of the right factor, read through
`LocalisationCone.bundleRingEquiv`. -/
def baseChangeBundleHom :
    ResolvedCone.bundleRing φ →+*
      ResolvedCone.bundleRing (LocalisationCone.baseChangeHom I R' φ) :=
  (LocalisationCone.bundleRingEquiv I R' φ).symm.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight :
      ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
        LocalisationCone.baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ).toRingHom

@[simp]
theorem baseChangeBundleHom_apply (a : ResolvedCone.bundleRing φ) :
    baseChangeBundleHom I R' φ a =
      (LocalisationCone.bundleRingEquiv I R' φ).symm
        ((1 : LocalisationCone.baseExt I R') ⊗ₜ[R ⧸ I] a) :=
  rfl

/-- **The resolved-cone ideal of a flat formally étale base change is the extension of the
resolved-cone ideal.**  This is `LocalisationCone.ideal_map_bundleRingEquiv` transported along
the canonical map `baseChangeBundleHom`. -/
theorem ideal_map_baseChangeBundleHom :
    Ideal.map (baseChangeBundleHom I R' φ) (ResolvedCone.ideal φ) =
      ResolvedCone.ideal (LocalisationCone.baseChangeHom I R' φ) := by
  have key : Ideal.map (Algebra.TensorProduct.includeRight :
        ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
          LocalisationCone.baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ).toRingHom
        (ResolvedCone.ideal φ) =
      Ideal.map (LocalisationCone.bundleRingEquiv I R' φ).toRingEquiv.toRingHom
        (ResolvedCone.ideal (LocalisationCone.baseChangeHom I R' φ)) := by
    refine Eq.trans (ideal_map_congr_hom _ (Algebra.TensorProduct.includeRight :
      ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
        LocalisationCone.baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ)
      (fun _ => rfl) _) ?_
    refine Eq.trans (LocalisationCone.ideal_map_bundleRingEquiv I R' φ).symm ?_
    exact ideal_map_congr_hom _ _ (fun _ => rfl) _
  have hcomp : (LocalisationCone.bundleRingEquiv I R' φ).symm.toRingEquiv.toRingHom.comp
      (LocalisationCone.bundleRingEquiv I R' φ).toRingEquiv.toRingHom = RingHom.id _ :=
    RingHom.ext fun x => (LocalisationCone.bundleRingEquiv I R' φ).symm_apply_apply x
  change Ideal.map ((LocalisationCone.bundleRingEquiv I R' φ).symm.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight :
      ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
        LocalisationCone.baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ).toRingHom)
    (ResolvedCone.ideal φ) = _
  rw [← Ideal.map_map, key, Ideal.map_map, hcomp, Ideal.map_id]

end BaseChange

/-! ## Comparing two obstruction data over the same ring -/

section ChainIso

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E E' : LinearTwoTermComplex (R ⧸ I)}

/-- **The same-ring special case of the intrinsic comparison below.  If two affine obstruction
data `φ`, `φ'` over the same ring are related by a chain map `ψ` which is bijective in both
degrees and compatible with the maps to the conormal complex, then the induced isomorphism
`VirtualClass.bundleEquiv` of bundle rings carries the resolved-cone ideal of `φ` to the ideal of
`φ'`.  This is round 15's
`VirtualClass.ideal_map_bundleEquiv`, restated for the `RingEquiv` underlying
`VirtualClass.bundleEquiv`. -/
theorem ideal_map_bundleEquiv_of_chainIso
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k R I))
    (ψ : LinearTwoTermComplex.Hom E E') (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) :
    Ideal.map (VirtualFundamentalClass.VirtualClass.bundleEquiv φ φ' ψ hψ0).toRingEquiv.toRingHom
        (ResolvedCone.ideal φ) = ResolvedCone.ideal φ' := by
  refine Eq.trans (ideal_map_congr_hom _ _ (fun _ => rfl) _) ?_
  exact VirtualFundamentalClass.VirtualClass.ideal_map_bundleEquiv φ φ' ψ hψ0 hψ1 hcomp

end ChainIso

/-! ## Intrinsic comparison across a change of chart ring -/

/-- A semilinear isomorphism of two-term complexes.  The two complexes may be defined over
different rings; `e` identifies those rings and the additive equivalences in the two degrees are
required to respect the scalar actions and the differential.  This is the transport supplied by
an obstruction-theory refinement on an overlap. -/
structure SemilinearIso {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (E : LinearTwoTermComplex A) (F : LinearTwoTermComplex B) where
  degreeZero : E.degreeZero ≃+ F.degreeZero
  degreeOne : E.degreeOne ≃+ F.degreeOne
  map_smul_degreeZero (a : A) (x : E.degreeZero) :
    degreeZero (a • x) = e a • degreeZero x
  map_smul_degreeOne (a : A) (x : E.degreeOne) :
    degreeOne (a • x) = e a • degreeOne x
  comm (x : E.degreeZero) : degreeOne (E.differential x) = F.differential (degreeZero x)

namespace SemilinearIso

/-- The identity semilinear comparison. -/
def refl {A : Type u} [CommRing A] (E : LinearTwoTermComplex A) :
    SemilinearIso (RingEquiv.refl A) E E where
  degreeZero := AddEquiv.refl _
  degreeOne := AddEquiv.refl _
  map_smul_degreeZero _ _ := rfl
  map_smul_degreeOne _ _ := rfl
  comm _ := rfl

end SemilinearIso

/-- A semilinear map of two-term complexes.  Unlike `SemilinearIso`, its degree maps need not be
bijective; this is the target transport used by a smooth ambient refinement. -/
structure SemilinearHom {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (E : LinearTwoTermComplex A) (F : LinearTwoTermComplex B) where
  degreeZero : E.degreeZero →+ F.degreeZero
  degreeOne : E.degreeOne →+ F.degreeOne
  map_smul_degreeZero (a : A) (x : E.degreeZero) :
    degreeZero (a • x) = e a • degreeZero x
  map_smul_degreeOne (a : A) (x : E.degreeOne) :
    degreeOne (a • x) = e a • degreeOne x
  comm (x : E.degreeZero) : degreeOne (E.differential x) = F.differential (degreeZero x)

/-! ### Ring transports from semilinear module transports -/

namespace SemilinearTransport

namespace Symmetric

variable {R S M N : Type u} [CommRing R] [CommRing S]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]

noncomputable def map (e : R →+* S) (f : M →+ N)
    (hf : ∀ r x, f (r • x) = e r • f x) :
    SymmetricAlgebra R M →+* SymmetricAlgebra S N := by
  letI : Algebra R (SymmetricAlgebra S N) :=
    ((algebraMap S (SymmetricAlgebra S N)).comp e).toAlgebra
  let l : M →ₗ[R] SymmetricAlgebra S N :=
    { toFun := fun x => SymmetricAlgebra.ι S N (f x)
      map_add' := by intro x y; simp
      map_smul' := by
        intro r x
        rw [hf, map_smul]
        simp only [RingHom.id_apply, Algebra.smul_def]
        rfl }
  exact (SymmetricAlgebra.lift l).toRingHom

@[simp]
theorem map_ι (e : R →+* S) (f : M →+ N)
    (hf : ∀ r x, f (r • x) = e r • f x) (x : M) :
    map e f hf (SymmetricAlgebra.ι R M x) = SymmetricAlgebra.ι S N (f x) := by
  let : Algebra R (SymmetricAlgebra S N) :=
    ((algebraMap S (SymmetricAlgebra S N)).comp e).toAlgebra
  unfold map
  exact SymmetricAlgebra.lift_ι_apply _ _

@[simp]
theorem map_algebraMap (e : R →+* S) (f : M →+ N)
    (hf : ∀ r x, f (r • x) = e r • f x) (r : R) :
    map e f hf (algebraMap R (SymmetricAlgebra R M) r) =
      algebraMap S (SymmetricAlgebra S N) (e r) := by
  let : Algebra R (SymmetricAlgebra S N) :=
    ((algebraMap S (SymmetricAlgebra S N)).comp e).toAlgebra
  unfold map
  exact AlgHom.commutes _ _

theorem symm_smul (e : R ≃+* S) (f : M ≃+ N)
    (hf : ∀ r x, f (r • x) = e r • f x) (s : S) (y : N) :
    f.symm (s • y) = e.symm s • f.symm y := by
  apply f.injective
  rw [f.apply_symm_apply, hf, e.apply_symm_apply, f.apply_symm_apply]

noncomputable def equiv (e : R ≃+* S) (f : M ≃+ N)
    (hf : ∀ r x, f (r • x) = e r • f x) :
    SymmetricAlgebra R M ≃+* SymmetricAlgebra S N := by
  let g := map e.toRingHom f.toAddMonoidHom hf
  let h := map e.symm.toRingHom f.symm.toAddMonoidHom (symm_smul e f hf)
  have hleft : ∀ a, h (g a) = a := by
    intro a
    induction a using SymmetricAlgebra.induction with
    | algebraMap r => simp [g, h]
    | ι x => simp [g, h]
    | add a b ha hb => simp only [map_add, ha, hb]
    | mul a b ha hb => simp only [map_mul, ha, hb]
  have hright : ∀ b, g (h b) = b := by
    intro b
    induction b using SymmetricAlgebra.induction with
    | algebraMap s => simp [g, h]
    | ι y => simp [g, h]
    | add a b ha hb => simp only [map_add, ha, hb]
    | mul a b ha hb => simp only [map_mul, ha, hb]
  exact { g with invFun := h, left_inv := hleft, right_inv := hright }

@[simp]
theorem equiv_ι (e : R ≃+* S) (f : M ≃+ N)
    (hf : ∀ r x, f (r • x) = e r • f x) (x : M) :
    equiv e f hf (SymmetricAlgebra.ι R M x) = SymmetricAlgebra.ι S N (f x) :=
  map_ι _ _ hf _

@[simp]
theorem equiv_algebraMap (e : R ≃+* S) (f : M ≃+ N)
    (hf : ∀ r x, f (r • x) = e r • f x) (r : R) :
    equiv e f hf (algebraMap R (SymmetricAlgebra R M) r) =
      algebraMap S (SymmetricAlgebra S N) (e r) :=
  map_algebraMap _ _ hf _

end Symmetric

namespace Tensor

variable {R S A B C D : Type u} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra S C] [Algebra S D]

noncomputable def map (e : R →+* S) (f : A →+* C) (g : B →+* D)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S C (e r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap S D (e r)) :
    A ⊗[R] B →+* C ⊗[S] D := by
  letI : Algebra R (C ⊗[S] D) :=
    ((algebraMap S (C ⊗[S] D)).comp e).toAlgebra
  let α : A →ₐ[R] C ⊗[S] D :=
    { (Algebra.TensorProduct.includeLeftRingHom.comp f) with
      commutes' := by
        intro r
        change (Algebra.TensorProduct.includeLeftRingHom (f (algebraMap R A r))) = _
        rw [hf]
        exact (Algebra.TensorProduct.includeLeft : C →ₐ[S] C ⊗[S] D).commutes (e r) }
  let β : B →ₐ[R] C ⊗[S] D :=
    { ((Algebra.TensorProduct.includeRight : D →ₐ[S] C ⊗[S] D).toRingHom.comp g) with
      commutes' := by
        intro r
        change (Algebra.TensorProduct.includeRight (g (algebraMap R B r))) = _
        rw [hg]
        exact (Algebra.TensorProduct.includeRight : D →ₐ[S] C ⊗[S] D).commutes (e r) }
  exact (Algebra.TensorProduct.lift α β (fun _ _ => Commute.all _ _)).toRingHom

@[simp]
theorem map_tmul (e : R →+* S) (f : A →+* C) (g : B →+* D)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S C (e r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap S D (e r)) (a : A) (b : B) :
    map e f g hf hg (a ⊗ₜ[R] b) = f a ⊗ₜ[S] g b := by
  let : Algebra R (C ⊗[S] D) :=
    ((algebraMap S (C ⊗[S] D)).comp e).toAlgebra
  simp [map, Algebra.TensorProduct.lift_tmul]

theorem symm_algebraMap (e : R ≃+* S) (f : A ≃+* C)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S C (e r)) (s : S) :
    f.symm (algebraMap S C s) = algebraMap R A (e.symm s) := by
  apply f.injective
  rw [f.apply_symm_apply, hf, e.apply_symm_apply]

noncomputable def equiv (e : R ≃+* S) (f : A ≃+* C) (g : B ≃+* D)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S C (e r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap S D (e r)) :
    A ⊗[R] B ≃+* C ⊗[S] D := by
  let p := map e.toRingHom f.toRingHom g.toRingHom hf hg
  let q := map e.symm.toRingHom f.symm.toRingHom g.symm.toRingHom
    (symm_algebraMap e f hf) (symm_algebraMap e g hg)
  have hleft : ∀ a, q (p a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [p, q]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hright : ∀ a, p (q a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [p, q]
    | add a b ha hb => simp only [map_add, ha, hb]
  exact { p with invFun := q, left_inv := hleft, right_inv := hright }

@[simp]
theorem equiv_tmul (e : R ≃+* S) (f : A ≃+* C) (g : B ≃+* D)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S C (e r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap S D (e r)) (a : A) (b : B) :
    equiv e f g hf hg (a ⊗ₜ[R] b) = f a ⊗ₜ[S] g b :=
  map_tmul _ _ _ hf hg _ _

theorem retract_algebraMap (e : R ≃+* S) (f : A →+* C) (r : C →+* A)
    (hf : ∀ a, f (algebraMap R A a) = algebraMap S C (e a))
    (hr : Function.LeftInverse r f) (s : S) :
    r (algebraMap S C s) = algebraMap R A (e.symm s) := by
  calc
    r (algebraMap S C s) = r (algebraMap S C (e (e.symm s))) := by
      rw [e.apply_symm_apply]
    _ = r (f (algebraMap R A (e.symm s))) := by rw [hf]
    _ = algebraMap R A (e.symm s) := hr _

theorem map_leftInverse (e : R ≃+* S) (f : A →+* C) (r : C →+* A) (g : B ≃+* D)
    (hf : ∀ a, f (algebraMap R A a) = algebraMap S C (e a))
    (hg : ∀ a, g (algebraMap R B a) = algebraMap S D (e a))
    (hr : Function.LeftInverse r f) :
    Function.LeftInverse
      (map e.symm.toRingHom r g.symm.toRingHom
        (retract_algebraMap e f r hf hr) (symm_algebraMap e g hg))
      (map e.toRingHom f g.toRingHom hf hg) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [hr a]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem map_injective_of_retract (e : R ≃+* S)
    (f : A →+* C) (r : C →+* A) (g : B ≃+* D)
    (hf : ∀ a, f (algebraMap R A a) = algebraMap S C (e a))
    (hg : ∀ a, g (algebraMap R B a) = algebraMap S D (e a))
    (hr : Function.LeftInverse r f) :
    Function.Injective (map e.toRingHom f g.toRingHom hf hg) :=
  (map_leftInverse e f r g hf hg hr).injective

end Tensor

end SemilinearTransport

/-- The intrinsic comparison used on an overlap.  The fields `source` and `target` transport the
two-term obstruction datum and its conormal target along the quotient-ring isomorphism.  The
fields `bundle_generator` and the theorem `IntrinsicComparison.product_map` say that the
ambient/refinement comparison induces the displayed bundle and product-ring maps.  The latter is
constructed from `cone`, `cone_algebraMap`, and the semilinear degree-one transport; in particular,
`product_map` is a comparison of the defining maps of the resolved cones, rather than an equality
of their kernels supplied as input. -/
structure IntrinsicComparison
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] {I : Ideal R} {J : Ideal S}
    {E : LinearTwoTermComplex (R ⧸ I)} {E' : LinearTwoTermComplex (S ⧸ J)}
    (e : (R ⧸ I) ≃+* (S ⧸ J))
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k S J))
    (τ : ResolvedCone.bundleRing φ ≃+* ResolvedCone.bundleRing φ') where
  /-- Semilinear transport of the obstruction complex. -/
  source : SemilinearIso e E E'
  /-- Semilinear transport of the conormal complex. -/
  target : SemilinearIso e (conormalComplex k R I) (conormalComplex k S J)
  /-- The affine obstruction maps commute with the semilinear transport. -/
  map_degreeZero (x : E.degreeZero) :
    target.degreeZero (φ.degreeZero x) = φ'.degreeZero (source.degreeZero x)
  /-- The degree-one part of the obstruction-theory square also commutes. -/
  map_degreeOne (x : E.degreeOne) :
    target.degreeOne (φ.degreeOne x) = φ'.degreeOne (source.degreeOne x)
  /-- The bundle-ring comparison is induced on symmetric generators by the source transport. -/
  bundle_generator (x : E.degreeZero) :
    τ (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x) =
      SymmetricAlgebra.ι (S ⧸ J) E'.degreeZero (source.degreeZero x)
  /-- The ambient/refinement comparison of the associated graded normal cones. -/
  cone :
    AffineNormalCone.associatedGradedRing R I ≃+*
      AffineNormalCone.associatedGradedRing S J
  /-- The cone transport is over the quotient-ring equivalence.  This is the scalar compatibility
  needed to construct the product transport from the two factors. -/
  cone_algebraMap (a : R ⧸ I) :
    cone (algebraMap (R ⧸ I) (AffineNormalCone.associatedGradedRing R I) a) =
      algebraMap (S ⧸ J) (AffineNormalCone.associatedGradedRing S J) (e a)
  /-- The ambient comparison carries the canonical conormal generators to one another. -/
  cone_conormal (z : (conormalComplex k R I).degreeZero) :
    cone (AffineNormalCone.conormalToAssociatedGraded R I z) =
      AffineNormalCone.conormalToAssociatedGraded S J (target.degreeZero z)
  bundle_algebraMap (a : R ⧸ I) :
    τ (algebraMap (R ⧸ I) (ResolvedCone.bundleRing φ) a) =
      algebraMap (S ⧸ J) (ResolvedCone.bundleRing φ') (e a)

namespace IntrinsicComparison

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] {I : Ideal R} {J : Ideal S}
  {E : LinearTwoTermComplex (R ⧸ I)} {E' : LinearTwoTermComplex (S ⧸ J)}
  {e : (R ⧸ I) ≃+* (S ⧸ J)}
  {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}
  {φ' : LinearTwoTermComplex.Hom E' (conormalComplex k S J)}
  {τ : ResolvedCone.bundleRing φ ≃+* ResolvedCone.bundleRing φ'}

/-- The degree-one symmetric-algebra transport forced by the semilinear obstruction comparison. -/
noncomputable def degreeOneSymmetric (C : IntrinsicComparison e φ φ' τ) :
    SymmetricAlgebra (R ⧸ I) E.degreeOne ≃+*
      SymmetricAlgebra (S ⧸ J) E'.degreeOne :=
  SemilinearTransport.Symmetric.equiv e C.source.degreeOne
    C.source.map_smul_degreeOne

/-- The product-ring transport is constructed as the tensor product of the intrinsic cone
transport and the degree-one symmetric-algebra transport.  No product-ring isomorphism is stored
in `IntrinsicComparison`; its scalar compatibility and generator formulas are consequences of the
two factors. -/
noncomputable def product (C : IntrinsicComparison e φ φ' τ) :
    ResolvedCone.productRing φ ≃+* ResolvedCone.productRing φ' :=
  SemilinearTransport.Tensor.equiv e C.cone (C.degreeOneSymmetric)
    C.cone_algebraMap (fun a => by
      exact SemilinearTransport.Symmetric.equiv_algebraMap e C.source.degreeOne
        C.source.map_smul_degreeOne a)

theorem product_algebraMap (C : IntrinsicComparison e φ φ' τ) (a : R ⧸ I) :
    C.product (algebraMap (R ⧸ I) (ResolvedCone.productRing φ) a) =
      algebraMap (S ⧸ J) (ResolvedCone.productRing φ') (e a) := by
  simp [product, Algebra.TensorProduct.algebraMap_apply,
    SemilinearTransport.Tensor.equiv_tmul, C.cone_algebraMap]

theorem product_cone (C : IntrinsicComparison e φ φ' τ)
    (c : AffineNormalCone.associatedGradedRing R I) :
    C.product (c ⊗ₜ[R ⧸ I] (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne)) =
      C.cone c ⊗ₜ[S ⧸ J] (1 : SymmetricAlgebra (S ⧸ J) E'.degreeOne) := by
  rw [product, SemilinearTransport.Tensor.equiv_tmul, map_one]

theorem product_bundle_generator (C : IntrinsicComparison e φ φ' τ)
    (y : E.degreeOne) :
    C.product ((1 : AffineNormalCone.associatedGradedRing R I) ⊗ₜ[R ⧸ I]
        SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y) =
      (1 : AffineNormalCone.associatedGradedRing S J) ⊗ₜ[S ⧸ J]
        SymmetricAlgebra.ι (S ⧸ J) E'.degreeOne (C.source.degreeOne y) := by
  rw [product, SemilinearTransport.Tensor.equiv_tmul, map_one,
    degreeOneSymmetric, SemilinearTransport.Symmetric.equiv_ι]

private theorem product_map_on_generator
    (C : IntrinsicComparison e φ φ' τ) (x : E.degreeZero) :
    C.product (ResolvedCone.productMap φ
        (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x)) =
      ResolvedCone.productMap φ'
        (τ (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x)) := by
  rw [ResolvedCone.productMap_ι, C.product.map_add, C.product_cone,
    C.product_bundle_generator, C.bundle_generator, ResolvedCone.productMap_ι,
    C.cone_conormal, C.map_degreeZero, C.source.comm]

theorem product_map (C : IntrinsicComparison e φ φ' τ)
    (a : ResolvedCone.bundleRing φ) :
    C.product (ResolvedCone.productMap φ a) =
      ResolvedCone.productMap φ' (τ a) := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap a =>
      rw [(ResolvedCone.productMap φ).commutes, C.product_algebraMap,
        C.bundle_algebraMap, (ResolvedCone.productMap φ').commutes]
  | ι x => exact C.product_map_on_generator x
  | mul a b ha hb =>
      calc
        C.product (ResolvedCone.productMap φ (a * b)) =
            C.product (ResolvedCone.productMap φ a * ResolvedCone.productMap φ b) :=
          congrArg C.product ((ResolvedCone.productMap φ).map_mul a b)
        _ = ResolvedCone.productMap φ' (τ a) * ResolvedCone.productMap φ' (τ b) := by
          rw [C.product.map_mul, ha, hb]
        _ = ResolvedCone.productMap φ' (τ a * τ b) :=
          ((ResolvedCone.productMap φ').map_mul (τ a) (τ b)).symm
        _ = ResolvedCone.productMap φ' (τ (a * b)) :=
          congrArg (ResolvedCone.productMap φ') (τ.map_mul a b).symm
  | add a b ha hb =>
      calc
        C.product (ResolvedCone.productMap φ (a + b)) =
            C.product (ResolvedCone.productMap φ a + ResolvedCone.productMap φ b) :=
          congrArg C.product ((ResolvedCone.productMap φ).map_add a b)
        _ = ResolvedCone.productMap φ' (τ a) + ResolvedCone.productMap φ' (τ b) := by
          rw [C.product.map_add, ha, hb]
        _ = ResolvedCone.productMap φ' (τ a + τ b) :=
          ((ResolvedCone.productMap φ').map_add (τ a) (τ b)).symm
        _ = ResolvedCone.productMap φ' (τ (a + b)) :=
          congrArg (ResolvedCone.productMap φ') (τ.map_add a b).symm

/-- The intrinsic comparison transports the resolved-cone ideal.  This is a consequence of the
kernel description `ResolvedCone.ideal = ker productMap`, not an input field. -/
theorem ideal_map (C : IntrinsicComparison e φ φ' τ) :
    Ideal.map τ.toRingHom (ResolvedCone.ideal φ) = ResolvedCone.ideal φ' := by
  have hcomap : Ideal.comap τ.toRingHom (ResolvedCone.ideal φ') =
      ResolvedCone.ideal φ := by
    ext a
    rw [Ideal.mem_comap, ResolvedCone.mem_ideal_iff, ResolvedCone.mem_ideal_iff]
    constructor
    · intro ha
      have ha' : ResolvedCone.productMap φ' (τ a) = 0 := ha
      apply C.product.injective
      calc
        C.product (ResolvedCone.productMap φ a) =
            ResolvedCone.productMap φ' (τ a) := IntrinsicComparison.product_map C a
        _ = 0 := ha'
        _ = C.product 0 := (map_zero C.product).symm
    · intro ha
      change ResolvedCone.productMap φ' (τ a) = 0
      calc
        ResolvedCone.productMap φ' (τ a) = C.product (ResolvedCone.productMap φ a) :=
          (IntrinsicComparison.product_map C a).symm
        _ = C.product 0 := by rw [ha]
        _ = 0 := map_zero C.product
  rw [← hcomap]
  exact Ideal.map_comap_of_surjective _ τ.surjective _

end IntrinsicComparison

/-! ## Refinement comparisons with injective cone transport

An ambient smooth refinement can add polynomial cone coordinates while leaving the obstruction
bundle unchanged.  Its cone transport is therefore generally only a split-injective ring map, and
the target conormal complex is only reached by a semilinear chain map.  The following comparison
keeps this genuine refinement shape; the strict `IntrinsicComparison` above is the special case in
which the target map and cone map are equivalences. -/

structure RefinementComparison
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] {I : Ideal R} {J : Ideal S}
    {E : LinearTwoTermComplex (R ⧸ I)} {E' : LinearTwoTermComplex (S ⧸ J)}
    (e : (R ⧸ I) ≃+* (S ⧸ J))
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k S J))
    (τ : ResolvedCone.bundleRing φ ≃+* ResolvedCone.bundleRing φ') where
  /-- The obstruction complexes are transported isomorphically; only the conormal target changes
  by refinement. -/
  source : SemilinearIso e E E'
  target : SemilinearHom e (conormalComplex k R I) (conormalComplex k S J)
  map_degreeZero (x : E.degreeZero) :
    target.degreeZero (φ.degreeZero x) = φ'.degreeZero (source.degreeZero x)
  /-- The degree-one part of the obstruction-theory square also commutes. -/
  map_degreeOne (x : E.degreeOne) :
    target.degreeOne (φ.degreeOne x) = φ'.degreeOne (source.degreeOne x)
  bundle_generator (x : E.degreeZero) :
    τ (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x) =
      SymmetricAlgebra.ι (S ⧸ J) E'.degreeZero (source.degreeZero x)
  bundle_algebraMap (a : R ⧸ I) :
    τ (algebraMap (R ⧸ I) (ResolvedCone.bundleRing φ) a) =
      algebraMap (S ⧸ J) (ResolvedCone.bundleRing φ') (e a)
  /-- The cone map supplied by the ambient refinement. -/
  cone : AffineNormalCone.associatedGradedRing R I →+*
    AffineNormalCone.associatedGradedRing S J
  cone_algebraMap (a : R ⧸ I) :
    cone (algebraMap (R ⧸ I) (AffineNormalCone.associatedGradedRing R I) a) =
      algebraMap (S ⧸ J) (AffineNormalCone.associatedGradedRing S J) (e a)
  /-- The refinement cone map has the explicit retraction supplied by the common ambient chart. -/
  cone_retraction : AffineNormalCone.associatedGradedRing S J →+*
    AffineNormalCone.associatedGradedRing R I
  cone_leftInverse : Function.LeftInverse cone_retraction cone
  cone_conormal (z : (conormalComplex k R I).degreeZero) :
    cone (AffineNormalCone.conormalToAssociatedGraded R I z) =
      AffineNormalCone.conormalToAssociatedGraded S J (target.degreeZero z)

namespace RefinementComparison

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] {I : Ideal R} {J : Ideal S}
  {E : LinearTwoTermComplex (R ⧸ I)} {E' : LinearTwoTermComplex (S ⧸ J)}
  {e : (R ⧸ I) ≃+* (S ⧸ J)}
  {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}
  {φ' : LinearTwoTermComplex.Hom E' (conormalComplex k S J)}
  {τ : ResolvedCone.bundleRing φ ≃+* ResolvedCone.bundleRing φ'}

noncomputable def degreeOneSymmetric (C : RefinementComparison e φ φ' τ) :
    SymmetricAlgebra (R ⧸ I) E.degreeOne ≃+*
      SymmetricAlgebra (S ⧸ J) E'.degreeOne :=
  SemilinearTransport.Symmetric.equiv e C.source.degreeOne
    C.source.map_smul_degreeOne

/-- The target product map is constructed from the refinement cone map and the symmetric transport
of the degree-one obstruction term. -/
noncomputable def product (C : RefinementComparison e φ φ' τ) :
    ResolvedCone.productRing φ →+* ResolvedCone.productRing φ' :=
  SemilinearTransport.Tensor.map e.toRingHom C.cone C.degreeOneSymmetric
    C.cone_algebraMap (fun a => by
      exact SemilinearTransport.Symmetric.equiv_algebraMap e C.source.degreeOne
        C.source.map_smul_degreeOne a)

theorem product_injective (C : RefinementComparison e φ φ' τ) :
    Function.Injective C.product := by
  exact SemilinearTransport.Tensor.map_injective_of_retract e C.cone C.cone_retraction
    C.degreeOneSymmetric C.cone_algebraMap
    (fun a => SemilinearTransport.Symmetric.equiv_algebraMap e C.source.degreeOne
      C.source.map_smul_degreeOne a) C.cone_leftInverse

theorem product_algebraMap (C : RefinementComparison e φ φ' τ) (a : R ⧸ I) :
    C.product (algebraMap (R ⧸ I) (ResolvedCone.productRing φ) a) =
      algebraMap (S ⧸ J) (ResolvedCone.productRing φ') (e a) := by
  simp [product, Algebra.TensorProduct.algebraMap_apply,
    SemilinearTransport.Tensor.map_tmul, C.cone_algebraMap]

theorem product_cone (C : RefinementComparison e φ φ' τ)
    (c : AffineNormalCone.associatedGradedRing R I) :
    C.product (c ⊗ₜ[R ⧸ I] (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne)) =
      C.cone c ⊗ₜ[S ⧸ J] (1 : SymmetricAlgebra (S ⧸ J) E'.degreeOne) := by
  rw [product, SemilinearTransport.Tensor.map_tmul, map_one]

theorem product_bundle_generator (C : RefinementComparison e φ φ' τ)
    (y : E.degreeOne) :
    C.product ((1 : AffineNormalCone.associatedGradedRing R I) ⊗ₜ[R ⧸ I]
        SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y) =
      (1 : AffineNormalCone.associatedGradedRing S J) ⊗ₜ[S ⧸ J]
        SymmetricAlgebra.ι (S ⧸ J) E'.degreeOne (C.source.degreeOne y) := by
  rw [product, SemilinearTransport.Tensor.map_tmul, map_one,
    degreeOneSymmetric]
  exact congrArg (fun z =>
      (1 : AffineNormalCone.associatedGradedRing S J) ⊗ₜ[S ⧸ J] z)
    (SemilinearTransport.Symmetric.equiv_ι e C.source.degreeOne
      C.source.map_smul_degreeOne y)

private theorem product_map_on_generator
    (C : RefinementComparison e φ φ' τ) (x : E.degreeZero) :
    C.product (ResolvedCone.productMap φ
        (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x)) =
      ResolvedCone.productMap φ'
        (τ (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x)) := by
  rw [ResolvedCone.productMap_ι, C.product.map_add, C.product_cone,
    C.product_bundle_generator, C.bundle_generator, ResolvedCone.productMap_ι,
    C.cone_conormal, C.map_degreeZero, C.source.comm]

theorem product_map (C : RefinementComparison e φ φ' τ)
    (a : ResolvedCone.bundleRing φ) :
    C.product (ResolvedCone.productMap φ a) =
      ResolvedCone.productMap φ' (τ a) := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap a =>
      rw [(ResolvedCone.productMap φ).commutes, C.product_algebraMap,
        C.bundle_algebraMap, (ResolvedCone.productMap φ').commutes]
  | ι x => exact C.product_map_on_generator x
  | mul a b ha hb =>
      calc
        C.product (ResolvedCone.productMap φ (a * b)) =
            C.product (ResolvedCone.productMap φ a * ResolvedCone.productMap φ b) :=
          congrArg C.product ((ResolvedCone.productMap φ).map_mul a b)
        _ = ResolvedCone.productMap φ' (τ a) * ResolvedCone.productMap φ' (τ b) := by
          rw [C.product.map_mul, ha, hb]
        _ = ResolvedCone.productMap φ' (τ a * τ b) :=
          ((ResolvedCone.productMap φ').map_mul (τ a) (τ b)).symm
        _ = ResolvedCone.productMap φ' (τ (a * b)) :=
          congrArg (ResolvedCone.productMap φ') (τ.map_mul a b).symm
  | add a b ha hb =>
      calc
        C.product (ResolvedCone.productMap φ (a + b)) =
            C.product (ResolvedCone.productMap φ a + ResolvedCone.productMap φ b) :=
          congrArg C.product ((ResolvedCone.productMap φ).map_add a b)
        _ = ResolvedCone.productMap φ' (τ a) + ResolvedCone.productMap φ' (τ b) := by
          rw [C.product.map_add, ha, hb]
        _ = ResolvedCone.productMap φ' (τ a + τ b) :=
          ((ResolvedCone.productMap φ').map_add (τ a) (τ b)).symm
        _ = ResolvedCone.productMap φ' (τ (a + b)) :=
          congrArg (ResolvedCone.productMap φ') (τ.map_add a b).symm

/-- The injective product transport turns the defining-map comparison into ideal compatibility. -/
theorem ideal_map (C : RefinementComparison e φ φ' τ) :
    Ideal.map τ.toRingHom (ResolvedCone.ideal φ) = ResolvedCone.ideal φ' := by
  have hcomap : Ideal.comap τ.toRingHom (ResolvedCone.ideal φ') =
      ResolvedCone.ideal φ := by
    ext a
    rw [Ideal.mem_comap, ResolvedCone.mem_ideal_iff, ResolvedCone.mem_ideal_iff]
    constructor
    · intro ha
      apply C.product_injective
      calc
        C.product (ResolvedCone.productMap φ a) =
            ResolvedCone.productMap φ' (τ a) := C.product_map a
        _ = 0 := ha
        _ = C.product 0 := (map_zero C.product).symm
    · intro ha
      calc
        ResolvedCone.productMap φ' (τ a) =
            C.product (ResolvedCone.productMap φ a) := (C.product_map a).symm
        _ = C.product 0 := by rw [ha]
        _ = 0 := map_zero C.product
  rw [← hcomap]
  exact Ideal.map_comap_of_surjective _ τ.surjective _

end RefinementComparison

/-! ### Polynomial refinement constructor -/

namespace RefinementComparison

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {τ : Type u} {I : Ideal R}
  {E : LinearTwoTermComplex (R ⧸ I)}
  {E' : LinearTwoTermComplex
    ((MvPolynomial τ R) ⧸ (ConeRefinement.polyExt τ I))}
  {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}
  {φ' : LinearTwoTermComplex.Hom E'
    (conormalComplex k (MvPolynomial τ R) (ConeRefinement.polyExt τ I))}

/-- Build a refinement comparison for the canonical polynomial ambient refinement.  The only
geometric inputs are the semilinear obstruction/conormal chain maps, their quotient-ring scalar
compatibility, and the bundle-generator equations.  The cone map and its retraction are fixed by
`ConeRefinement.prodEquiv`; the conormal square is discharged by
`coneRefinementMap_conormal_generator`. -/
noncomputable def ofPolynomialCone
    (bundleTransport : ResolvedCone.bundleRing φ ≃+* ResolvedCone.bundleRing φ')
    (source : SemilinearIso (coneRefinementQuotientEquiv τ I) E E')
    (target : SemilinearHom (coneRefinementQuotientEquiv τ I)
      (conormalComplex k R I)
      (conormalComplex k (MvPolynomial τ R) (ConeRefinement.polyExt τ I)))
    (h0 : ∀ x : E.degreeZero,
      target.degreeZero (φ.degreeZero x) = φ'.degreeZero (source.degreeZero x))
    (h1 : ∀ x : E.degreeOne,
      target.degreeOne (φ.degreeOne x) = φ'.degreeOne (source.degreeOne x))
    (hgen : ∀ x : I.Cotangent,
      normalSheafCoordinateRefinementEquiv τ I
          (MvPolynomial.C
            (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent x)) =
        SymmetricAlgebra.ι ((MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I)
          (ConeRefinement.polyExt τ I).Cotangent (target.degreeZero x))
    (hbundleGen : ∀ x : E.degreeZero,
      bundleTransport (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x) =
        SymmetricAlgebra.ι ((MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I)
          E'.degreeZero (source.degreeZero x))
    (hbundleAlg : ∀ a : R ⧸ I,
      bundleTransport (algebraMap (R ⧸ I) (ResolvedCone.bundleRing φ) a) =
        algebraMap ((MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I)
          (ResolvedCone.bundleRing φ') (coneRefinementQuotientEquiv τ I a)) :
    RefinementComparison (coneRefinementQuotientEquiv τ I) φ φ' bundleTransport :=
  { source := source
    target := target
    map_degreeZero := h0
    map_degreeOne := h1
    bundle_generator := hbundleGen
    bundle_algebraMap := hbundleAlg
    cone := coneRefinementMap τ I
    cone_algebraMap := by
      intro a
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      calc
        coneRefinementMap τ I
            (algebraMap (R ⧸ I) (AffineNormalCone.associatedGradedRing R I)
              (Ideal.Quotient.mk I r)) =
            coneRefinementMap τ I
              (algebraMap R (AffineNormalCone.associatedGradedRing R I) r) := by
                change coneRefinementMap τ I
                    (algebraMap (R ⧸ I) (AffineNormalCone.associatedGradedRing R I)
                      (algebraMap R (R ⧸ I) r)) = _
                rw [IsScalarTower.algebraMap_apply R (R ⧸ I)
                  (AffineNormalCone.associatedGradedRing R I) r]
        _ = algebraMap (MvPolynomial τ R)
              (AffineNormalCone.associatedGradedRing (MvPolynomial τ R)
                (ConeRefinement.polyExt τ I)) (MvPolynomial.C r) := by
              rw [coneRefinementMap_apply, ConeRefinement.grIncl_algebraMap]
        _ = algebraMap ((MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I)
              (AffineNormalCone.associatedGradedRing (MvPolynomial τ R)
                (ConeRefinement.polyExt τ I))
              (Ideal.Quotient.mk (ConeRefinement.polyExt τ I) (MvPolynomial.C r)) := by
              symm
              exact IsScalarTower.algebraMap_apply (MvPolynomial τ R)
                ((MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I)
                (AffineNormalCone.associatedGradedRing (MvPolynomial τ R)
                  (ConeRefinement.polyExt τ I)) (MvPolynomial.C r)
        _ = algebraMap ((MvPolynomial τ R) ⧸ ConeRefinement.polyExt τ I)
              (AffineNormalCone.associatedGradedRing (MvPolynomial τ R)
                (ConeRefinement.polyExt τ I))
              (coneRefinementQuotientEquiv τ I (Ideal.Quotient.mk I r)) := by
              rw [coneRefinementQuotientEquiv_apply,
                coneRefinementQuotientMap, Ideal.quotientMap_mk]
    cone_retraction := coneRefinementRetraction τ I
    cone_leftInverse := coneRefinementRetraction_leftInverse τ I
    cone_conormal := fun z =>
      coneRefinementMap_conormal_generator τ I target.degreeZero hgen z }

end RefinementComparison

/-! ### Two legs into one common refinement -/

/-- Two local presentations may be compared through a common smooth refinement.  The common
presentation is existential inside this structure, while both legs retain the genuine semilinear
chain-map and split-injective cone data of `RefinementComparison`. -/
structure CommonRefinementComparison
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] {I : Ideal R} {J : Ideal S}
    {E : LinearTwoTermComplex (R ⧸ I)} {E' : LinearTwoTermComplex (S ⧸ J)}
    (e : (R ⧸ I) ≃+* (S ⧸ J))
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k S J))
    (τ : ResolvedCone.bundleRing φ ≃+* ResolvedCone.bundleRing φ') where
  commonRing : Type u
  [commonCommRing : CommRing commonRing]
  [commonAlgebra : Algebra k commonRing]
  commonIdeal : Ideal commonRing
  commonComplex : LinearTwoTermComplex (commonRing ⧸ commonIdeal)
  commonHom : LinearTwoTermComplex.Hom commonComplex
    (conormalComplex k commonRing commonIdeal)
  leftQuotient : (R ⧸ I) ≃+* (commonRing ⧸ commonIdeal)
  rightQuotient : (S ⧸ J) ≃+* (commonRing ⧸ commonIdeal)
  leftBundle : ResolvedCone.bundleRing φ ≃+*
    ResolvedCone.bundleRing commonHom
  rightBundle : ResolvedCone.bundleRing φ' ≃+*
    ResolvedCone.bundleRing commonHom
  left : RefinementComparison leftQuotient φ commonHom leftBundle
  right : RefinementComparison rightQuotient φ' commonHom rightBundle
  /-- The two quotient presentations induce the overlap scalar map used by the outer comparison. -/
  quotient_eq : e = leftQuotient.trans rightQuotient.symm
  transition_eq : τ = leftBundle.trans rightBundle.symm

namespace CommonRefinementComparison

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] {I : Ideal R} {J : Ideal S}
  {E : LinearTwoTermComplex (R ⧸ I)} {E' : LinearTwoTermComplex (S ⧸ J)}
  {e : (R ⧸ I) ≃+* (S ⧸ J)}
  {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}
  {φ' : LinearTwoTermComplex.Hom E' (conormalComplex k S J)}
  {τ : ResolvedCone.bundleRing φ ≃+* ResolvedCone.bundleRing φ'}

/-- The transition between the two local bundle rings transports their ideals because both are
transported to the same common refined kernel. -/
theorem ideal_map (C : CommonRefinementComparison e φ φ' τ) :
    Ideal.map τ.toRingHom (ResolvedCone.ideal φ) = ResolvedCone.ideal φ' := by
  let _ : CommRing C.commonRing := C.commonCommRing
  let _ : Algebra k C.commonRing := C.commonAlgebra
  rw [C.transition_eq]
  change Ideal.map (C.rightBundle.symm.toRingHom.comp C.leftBundle.toRingHom)
    (ResolvedCone.ideal φ) = ResolvedCone.ideal φ'
  rw [← Ideal.map_map, C.left.ideal_map]
  rw [← C.right.ideal_map, Ideal.map_map]
  have hcomp : C.rightBundle.symm.toRingHom.comp C.rightBundle.toRingHom =
      RingHom.id _ := RingHom.ext fun x => C.rightBundle.symm_apply_apply x
  rw [hcomp, Ideal.map_id]

end CommonRefinementComparison

/-- An overlap comparison is either a direct intrinsic comparison or two refinement legs into one
common presentation. -/
inductive OverlapComparison
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] {I : Ideal R} {J : Ideal S}
    {E : LinearTwoTermComplex (R ⧸ I)} {E' : LinearTwoTermComplex (S ⧸ J)}
    (e : (R ⧸ I) ≃+* (S ⧸ J))
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k S J))
    (τ : ResolvedCone.bundleRing φ ≃+* ResolvedCone.bundleRing φ') : Type (u + 2)
  | direct (comparison : IntrinsicComparison e φ φ' τ)
  | common (comparison : CommonRefinementComparison e φ φ' τ)

namespace OverlapComparison

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] {I : Ideal R} {J : Ideal S}
  {E : LinearTwoTermComplex (R ⧸ I)} {E' : LinearTwoTermComplex (S ⧸ J)}
  {e : (R ⧸ I) ≃+* (S ⧸ J)}
  {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}
  {φ' : LinearTwoTermComplex.Hom E' (conormalComplex k S J)}
  {τ : ResolvedCone.bundleRing φ ≃+* ResolvedCone.bundleRing φ'}

theorem ideal_map (C : OverlapComparison e φ φ' τ) :
    Ideal.map τ.toRingHom (ResolvedCone.ideal φ) = ResolvedCone.ideal φ' := by
  cases C with
  | direct C => exact C.ideal_map
  | common C => exact C.ideal_map

end OverlapComparison

/-! ### Constructed same-ring comparison

For a chain isomorphism over one quotient ring all the algebra maps in an intrinsic comparison are
canonical.  This constructor is useful both as the strict special case and as the algebraic core
of a comparison obtained after stabilization: the bundle and product equivalences are built from
the two linear equivalences, and their generator formulas are proved by the symmetric-algebra and
tensor-product APIs. -/

namespace IntrinsicComparison

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E E' : LinearTwoTermComplex (R ⧸ I)}
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k R I))
variable (ψ : LinearTwoTermComplex.Hom E E')

/-- Construct an intrinsic comparison from a bijective chain map.  The only compatibility with the
conormal target needed by the resolved-cone map is the degree-zero square; the degree-one term is
transported by the differential compatibility of the chain map. -/
noncomputable def ofChainIso (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero)
    (hcomp1 : φ'.degreeOne.comp ψ.degreeOne = φ.degreeOne) :
    IntrinsicComparison (RingEquiv.refl (R ⧸ I)) φ φ'
      (VirtualFundamentalClass.VirtualClass.bundleEquiv φ φ' ψ hψ0).toRingEquiv := by
  let ψ₀ := VirtualFundamentalClass.VirtualClass.zeroEquiv ψ hψ0
  let ψ₁ := VirtualFundamentalClass.VirtualClass.oneEquiv ψ hψ1
  let τ := VirtualFundamentalClass.VirtualClass.bundleEquiv φ φ' ψ hψ0
  exact
    { source :=
        { degreeZero := ψ₀.toAddEquiv
          degreeOne := ψ₁.toAddEquiv
          map_smul_degreeZero := by
            intro a x
            exact ψ.degreeZero.map_smul a x
          map_smul_degreeOne := by
            intro a x
            exact ψ.degreeOne.map_smul a x
          comm := by
            intro x
            exact ψ.comm x }
      target := SemilinearIso.refl _
      map_degreeZero := by
        intro x
        have hx := congrArg
          (fun f : E.degreeZero →ₗ[R ⧸ I]
            (conormalComplex k R I).degreeZero => f x) hcomp
        exact hx.symm
      map_degreeOne := by
        intro x
        have hx := congrArg
          (fun f : E.degreeOne →ₗ[R ⧸ I]
            (conormalComplex k R I).degreeOne => f x) hcomp1
        exact hx.symm
      bundle_generator := by
        intro x
        exact VirtualFundamentalClass.VirtualClass.bundleEquiv_ι φ φ' ψ hψ0 x
      cone := RingEquiv.refl _
      cone_algebraMap := by intro; rfl
      cone_conormal := by intro; rfl
      bundle_algebraMap := by
        intro a
        exact τ.commutes a
      }

end IntrinsicComparison

/-! ## Stabilized intrinsic comparisons

The strict comparison above is enough when the two ambient presentations have the same number of
coordinates.  A smooth refinement can instead add an acyclic direct summand to either obstruction
complex.  The following interface records that situation without taking an equality of resolved-
cone ideals as input: the comparison of the stabilized complexes constructs the bundle and product
equivalences through `VirtualClass.bundleEquiv` and `VirtualClass.productEquiv`, and the ideal of
the unstabilized cone is recovered by contraction along the acyclic inclusion.
-/

/-- A comparison after adding possibly different acyclic summands.  The field
`base_transport_comm` says that the induced equivalence of the stabilized bundles restricts to the
displayed transport on the original bundle rings.  This is a geometric refinement condition on
the coordinate rings; the compatibility of the defining product maps is constructed by
`VirtualClass.productEquiv_comp_productMap` from `comparison`, rather than supplied here. -/
structure StabilizedComparison
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
    {E E' : LinearTwoTermComplex (R ⧸ I)}
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k R I))
    (F F' : Type u) [AddCommGroup F] [Module (R ⧸ I) F]
    [AddCommGroup F'] [Module (R ⧸ I) F']
    [Module.Free (R ⧸ I) F] [Module.Free (R ⧸ I) F'] where
  /-- Chain comparison of the stabilized obstruction complexes. -/
  comparison : LinearTwoTermComplex.Hom
    (E.sum (VirtualFundamentalClass.VirtualClass.acyclicComplex (R ⧸ I) F))
    (E'.sum (VirtualFundamentalClass.VirtualClass.acyclicComplex (R ⧸ I) F'))
  bijective_degreeZero : Function.Bijective comparison.degreeZero
  bijective_degreeOne : Function.Bijective comparison.degreeOne
  /-- Compatibility with the maps to the conormal complex. -/
  compatibility :
    (VirtualFundamentalClass.VirtualClass.sumAcyclic φ' F').degreeZero.comp
        comparison.degreeZero =
      (VirtualFundamentalClass.VirtualClass.sumAcyclic φ F).degreeZero
  /-- Transport on the original bundle rings, obtained from the common refinement. -/
  base_transport : ResolvedCone.bundleRing φ ≃+* ResolvedCone.bundleRing φ'
  /-- The stabilized bundle equivalence restricts to `base_transport`. -/
  base_transport_comm (a : ResolvedCone.bundleRing φ) :
    VirtualFundamentalClass.VirtualClass.bundleEquiv
        (VirtualFundamentalClass.VirtualClass.sumAcyclic φ F)
        (VirtualFundamentalClass.VirtualClass.sumAcyclic φ' F') comparison
        bijective_degreeZero
        (VirtualFundamentalClass.VirtualClass.bundleInl φ F a) =
      VirtualFundamentalClass.VirtualClass.bundleInl φ' F'
        (base_transport a)

namespace StabilizedComparison

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E E' : LinearTwoTermComplex (R ⧸ I)}
variable {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}
variable {φ' : LinearTwoTermComplex.Hom E' (conormalComplex k R I)}
variable {F F' : Type u} [AddCommGroup F] [Module (R ⧸ I) F]
variable [AddCommGroup F'] [Module (R ⧸ I) F']
variable [Module.Free (R ⧸ I) F] [Module.Free (R ⧸ I) F']

/-- A stabilized refinement transports the ideal of the original resolved cone.  The proof first
uses the chain comparison to transport the stabilized product-map kernel, then contracts along the
acyclic summand using `mem_ideal_sumAcyclic_iff`. -/
theorem ideal_map (C : StabilizedComparison φ φ' F F') :
    Ideal.map C.base_transport.toRingHom (ResolvedCone.ideal φ) =
      ResolvedCone.ideal φ' := by
  have hmem : ∀ a : ResolvedCone.bundleRing φ,
      a ∈ ResolvedCone.ideal φ ↔
        C.base_transport a ∈ ResolvedCone.ideal φ' := by
    intro a
    calc
      a ∈ ResolvedCone.ideal φ ↔
          VirtualFundamentalClass.VirtualClass.bundleInl φ F a ∈
            ResolvedCone.ideal
              (VirtualFundamentalClass.VirtualClass.sumAcyclic φ F) :=
        VirtualFundamentalClass.VirtualClass.mem_ideal_sumAcyclic_iff φ F a
      _ ↔ VirtualFundamentalClass.VirtualClass.bundleEquiv
            (VirtualFundamentalClass.VirtualClass.sumAcyclic φ F)
            (VirtualFundamentalClass.VirtualClass.sumAcyclic φ' F') C.comparison
            C.bijective_degreeZero
            (VirtualFundamentalClass.VirtualClass.bundleInl φ F a) ∈
          ResolvedCone.ideal
            (VirtualFundamentalClass.VirtualClass.sumAcyclic φ' F') :=
        VirtualFundamentalClass.VirtualClass.mem_ideal_iff_bundleEquiv
          (VirtualFundamentalClass.VirtualClass.sumAcyclic φ F)
          (VirtualFundamentalClass.VirtualClass.sumAcyclic φ' F') C.comparison
          C.bijective_degreeZero C.bijective_degreeOne C.compatibility
          (VirtualFundamentalClass.VirtualClass.bundleInl φ F a)
      _ ↔ VirtualFundamentalClass.VirtualClass.bundleInl φ' F'
            (C.base_transport a) ∈
          ResolvedCone.ideal
            (VirtualFundamentalClass.VirtualClass.sumAcyclic φ' F') := by
        rw [C.base_transport_comm a]
      _ ↔ C.base_transport a ∈ ResolvedCone.ideal φ' :=
        (VirtualFundamentalClass.VirtualClass.mem_ideal_sumAcyclic_iff φ' F'
          (C.base_transport a)).symm
  have hcomap : Ideal.comap C.base_transport.toRingHom
      (ResolvedCone.ideal φ') = ResolvedCone.ideal φ := by
    ext a
    rw [Ideal.mem_comap]
    exact (hmem a).symm
  rw [← hcomap]
  exact Ideal.map_comap_of_surjective _ C.base_transport.surjective _

end StabilizedComparison

/-! ## Local embedding data -/

/-- The *local embeddings* underlying a `LocalConeData`: besides the chart identifications of
`LocalConeData`, every affine open `W` of a chart `j` is presented as a flat, formally étale
neighbourhood `chartRing j W h` inside the affine model `R j` of that chart, compatibly with the
bundle algebra.  This is the input from which the overlap hypothesis of `LocalConeData` is
derived in `CompatibleLocalEmbeddingData.compat`. -/
structure LocalEmbeddingCore {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u}
    (𝓔 : BundleData X ι) {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
    {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
    (φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))) where
  /-- The identification of the sections over a chart with the affine model of the base. -/
  chartBase : ∀ j, Γ(X, (𝓔.chart j).1) ≃+* (R j ⧸ I j)
  /-- The identification of the bundle algebra over a chart with `Sym(E⁻¹)`. -/
  chartBundle : ∀ j, 𝓔.algebra.ring (𝓔.chart j) ≃+* ResolvedCone.bundleRing (φ j)
  /-- `chartBundle` is a map of algebras over the base, via `chartBase`. -/
  chartBundle_algebraMap : ∀ (j : 𝓔.J) (r : Γ(X, (𝓔.chart j).1)),
    chartBundle j (algebraMap Γ(X, (𝓔.chart j).1) (𝓔.algebra.ring (𝓔.chart j)) r) =
      algebraMap (R j ⧸ I j) (ResolvedCone.bundleRing (φ j)) (chartBase j r)
  /-- **(a)** The flat formally étale `R j`-algebra presenting an affine open `W` of the chart
  `j` inside the affine model of that chart. -/
  chartRing : ∀ (j : 𝓔.J) (W : X.affineOpens), W ≤ 𝓔.chart j → Type u
  [commRingChartRing : ∀ j W h, CommRing (chartRing j W h)]
  [algebraChartRing : ∀ j W h, Algebra (R j) (chartRing j W h)]
  [algebraBaseChartRing : ∀ j W h, Algebra k (chartRing j W h)]
  [isScalarTowerChartRing : ∀ j W h, IsScalarTower k (R j) (chartRing j W h)]
  [flatChartRing : ∀ j W h, Module.Flat (R j) (chartRing j W h)]
  [formallyEtaleChartRing : ∀ j W h, Algebra.FormallyEtale (R j) (chartRing j W h)]
  /-- The sections over `W` are the quotient of `chartRing j W h` by the extension of `I j`. -/
  chartBaseExt : ∀ (j : 𝓔.J) (W : X.affineOpens) (h : W ≤ 𝓔.chart j),
    LocalisationCone.baseExt (I j) (chartRing j W h) ≃+* Γ(X, W.1)
  /-- `chartBaseExt` is compatible with `chartBase` and the restriction map of `X`. -/
  chartBaseExt_algebraMap : ∀ (j : 𝓔.J) (W : X.affineOpens) (h : W ≤ 𝓔.chart j)
      (a : Γ(X, (𝓔.chart j).1)),
    chartBaseExt j W h (algebraMap (R j ⧸ I j)
        (LocalisationCone.baseExt (I j) (chartRing j W h)) (chartBase j a)) = res X h a
  /-- **(b)** The identification of the bundle algebra over `W` with the bundle ring of the
  base-changed obstruction datum of the chart `j`. -/
  chartBundleExt : ∀ (j : 𝓔.J) (W : X.affineOpens) (h : W ≤ 𝓔.chart j),
    𝓔.algebra.ring W ≃+*
      ResolvedCone.bundleRing (LocalisationCone.baseChangeHom (I j) (chartRing j W h) (φ j))
  /-- The identification `chartBundleExt` intertwines the transition map `𝓔.algebra.map h` of
  the bundle algebra with the canonical base-change map of bundle rings. -/
  chartBundleExt_map : ∀ (j : 𝓔.J) (W : X.affineOpens) (h : W ≤ 𝓔.chart j)
      (a : 𝓔.algebra.ring (𝓔.chart j)),
    chartBundleExt j W h (𝓔.algebra.map h a) =
      baseChangeBundleHom (I j) (chartRing j W h) (φ j) (chartBundle j a)

attribute [instance] LocalEmbeddingCore.commRingChartRing LocalEmbeddingCore.algebraChartRing
  LocalEmbeddingCore.algebraBaseChartRing LocalEmbeddingCore.isScalarTowerChartRing
  LocalEmbeddingCore.flatChartRing LocalEmbeddingCore.formallyEtaleChartRing

/-- Local embedding data: `LocalEmbeddingCore` together with a direct or common-refinement
comparison, over every affine open `W` of the overlap of two charts, of the two base-changed
obstruction data.  The comparison is semilinear over the quotient-ring isomorphism induced by the
two presentations of `Γ(X, W)`.  Its ambient/refinement component compares the defining product
maps of the resolved cones, so ideal compatibility is proved below. -/
structure CompatibleLocalEmbeddingData {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u}
    (𝓔 : BundleData X ι) {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
    {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
    (φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j)))
    extends LocalEmbeddingCore 𝓔 φ where
  /-- **(c)** The comparison isomorphism of the two base-changed bundle rings over an affine
  open of the overlap of two charts. -/
  transition : ∀ (i j : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i) (hj : W ≤ 𝓔.chart j),
    ResolvedCone.bundleRing (LocalisationCone.baseChangeHom (I i) (chartRing i W hi) (φ i)) ≃+*
      ResolvedCone.bundleRing (LocalisationCone.baseChangeHom (I j) (chartRing j W hj) (φ j))
  /-- The comparison isomorphism is compatible with the two identifications of the bundle
  algebra over `W`. -/
  transition_chartBundleExt : ∀ (i j : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i)
      (hj : W ≤ 𝓔.chart j) (a : 𝓔.algebra.ring W),
    transition i j W hi hj (chartBundleExt i W hi a) = chartBundleExt j W hj a
  /-- The obstruction-theory/refinement comparison on an overlap.  It may be direct, or may give
  two semilinear refinement legs into a common presentation.  In either case the ideal transport
  is derived from the defining product-map kernels. -/
  transition_comparison : ∀ (i j : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i)
      (hj : W ≤ 𝓔.chart j),
    OverlapComparison
      ((chartBaseExt i W hi).trans (chartBaseExt j W hj).symm)
      (LocalisationCone.baseChangeHom (I i) (chartRing i W hi) (φ i))
      (LocalisationCone.baseChangeHom (I j) (chartRing j W hj) (φ j))
      (transition i j W hi hj)

namespace CompatibleLocalEmbeddingData

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} {𝓔 : BundleData X ι}
variable {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
variable {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
variable {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
variable (𝓛 : CompatibleLocalEmbeddingData 𝓔 φ)

/-- The resolved-cone ideal of the chart `j`, pulled back to the bundle algebra of that chart.
It is the ideal called `LocalConeData.chartIdeal` in `ConeGluing.lean`. -/
def chartIdeal (j : 𝓔.J) : Ideal (𝓔.algebra.ring (𝓔.chart j)) :=
  (ResolvedCone.ideal (φ j)).comap (𝓛.chartBundle j).toRingHom

/-- The chart ideal is the transport of the resolved-cone ideal along `chartBundle`. -/
theorem chartIdeal_eq_map (j : 𝓔.J) :
    𝓛.chartIdeal j = Ideal.map (𝓛.chartBundle j).symm.toRingHom (ResolvedCone.ideal (φ j)) := by
  have h1 : Ideal.map (𝓛.chartBundle j).symm (ResolvedCone.ideal (φ j)) =
      Ideal.comap (𝓛.chartBundle j) (ResolvedCone.ideal (φ j)) :=
    Ideal.map_symm (𝓛.chartBundle j)
  change Ideal.comap (𝓛.chartBundle j).toRingHom (ResolvedCone.ideal (φ j)) = _
  rw [ideal_comap_congr_hom (𝓛.chartBundle j).toRingHom (𝓛.chartBundle j) (fun _ => rfl), ← h1]
  exact ideal_map_congr_hom _ _ (fun _ => rfl) _

/-- Over an affine open `W` of the chart `i`, the extension of the chart ideal of `i` is the
transport, along the identification `chartBundleExt i W hi`, of the resolved-cone ideal of the
base-changed obstruction datum.  This uses only the `LocalEmbeddingCore` fields. -/
theorem map_chartIdeal_eq (i : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i) :
    (𝓛.chartIdeal i).map (𝓔.algebra.map hi) =
      Ideal.map (𝓛.chartBundleExt i W hi).symm.toRingHom
        (ResolvedCone.ideal
          (LocalisationCone.baseChangeHom (I i) (𝓛.chartRing i W hi) (φ i))) := by
  have hmap : ((𝓔.algebra.map hi).comp (𝓛.chartBundle i).symm.toRingHom) =
      (𝓛.chartBundleExt i W hi).symm.toRingHom.comp
        (baseChangeBundleHom (I i) (𝓛.chartRing i W hi) (φ i)) := by
    refine RingHom.ext fun b => ?_
    have hb := 𝓛.chartBundleExt_map i W hi ((𝓛.chartBundle i).symm b)
    rw [(𝓛.chartBundle i).apply_symm_apply] at hb
    change 𝓔.algebra.map hi ((𝓛.chartBundle i).symm b) =
      (𝓛.chartBundleExt i W hi).symm
        (baseChangeBundleHom (I i) (𝓛.chartRing i W hi) (φ i) b)
    rw [← hb, (𝓛.chartBundleExt i W hi).symm_apply_apply]
  rw [𝓛.chartIdeal_eq_map i, Ideal.map_map, hmap, ← Ideal.map_map,
    ideal_map_baseChangeBundleHom]

/-- The two identifications of the bundle algebra over an affine open of an overlap differ by
the comparison isomorphism. -/
theorem symm_chartBundleExt_comp_transition (i j : 𝓔.J) (W : X.affineOpens)
    (hi : W ≤ 𝓔.chart i) (hj : W ≤ 𝓔.chart j) :
    (𝓛.chartBundleExt j W hj).symm.toRingHom.comp (𝓛.transition i j W hi hj).toRingHom =
      (𝓛.chartBundleExt i W hi).symm.toRingHom := by
  refine RingHom.ext fun b => ?_
  have hb := 𝓛.transition_chartBundleExt i j W hi hj ((𝓛.chartBundleExt i W hi).symm b)
  rw [(𝓛.chartBundleExt i W hi).apply_symm_apply] at hb
  change (𝓛.chartBundleExt j W hj).symm (𝓛.transition i j W hi hj b) =
    (𝓛.chartBundleExt i W hi).symm b
  rw [hb, (𝓛.chartBundleExt j W hj).symm_apply_apply]

/-- **The overlap hypothesis of `LocalConeData` is a theorem for local embedding data.**  Over
every affine open `W` of the overlap of two charts the two resolved-cone ideals extend to the
same ideal of the bundle algebra `𝓔.algebra.ring W`. -/
theorem compat : ∀ (i j : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i) (hj : W ≤ 𝓔.chart j),
    (𝓛.chartIdeal i).map (𝓔.algebra.map hi) = (𝓛.chartIdeal j).map (𝓔.algebra.map hj) := by
  intro i j W hi hj
  rw [𝓛.map_chartIdeal_eq i W hi, 𝓛.map_chartIdeal_eq j W hj,
    ← (𝓛.transition_comparison i j W hi hj).ideal_map, Ideal.map_map,
    𝓛.symm_chartBundleExt_comp_transition]

/-- **Local embedding data gives local cone data.**  The overlap hypothesis
`LocalConeData.compat` is discharged by `CompatibleLocalEmbeddingData.compat`. -/
def toLocalConeData : LocalConeData 𝓔 φ where
  chartBase := 𝓛.chartBase
  chartBundle := 𝓛.chartBundle
  chartBundle_algebraMap := 𝓛.chartBundle_algebraMap
  compat := 𝓛.compat

@[simp]
theorem toLocalConeData_chartBundle (j : 𝓔.J) :
    𝓛.toLocalConeData.chartBundle j = 𝓛.chartBundle j :=
  rfl

@[simp]
theorem toLocalConeData_chartBase (j : 𝓔.J) : 𝓛.toLocalConeData.chartBase j = 𝓛.chartBase j :=
  rfl

/-- The chart ideal of the associated `LocalConeData` is the chart ideal. -/
theorem toLocalConeData_chartIdeal (j : 𝓔.J) :
    𝓛.toLocalConeData.chartIdeal j = 𝓛.chartIdeal j :=
  rfl

end CompatibleLocalEmbeddingData

/-! ## The single-chart case

For the round-17 affine bundle datum `GlobalConeAffine.bundleData φ` the chart index type is
`PUnit` and the single chart is `⊤`.  Two charts `i`, `j` and two proofs `hi`, `hj` are then
definitionally equal (structure eta for `PUnit`, proof irrelevance), so the comparison data of
`CompatibleLocalEmbeddingData` can be taken to be the identity: every `LocalEmbeddingCore` over that
bundle datum is already a `CompatibleLocalEmbeddingData`. -/

section Affine

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
  {E : LinearTwoTermComplex (R ⧸ I)} [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero]
  {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}

/-- **Sanity check for the single-chart case**: over the affine bundle datum of round 17 the
comparison data (c) of `CompatibleLocalEmbeddingData` is trivial, so any choice of local embeddings
(a), (b) already constitutes local embedding data. -/
def LocalEmbeddingCore.toCompatibleLocalEmbeddingDataOfAffine
    (𝓒 : LocalEmbeddingCore (k := k) (GlobalConeAffine.bundleData φ)
      (R := fun _ ↦ R) (I := fun _ ↦ I) (E := fun _ ↦ E) (fun _ ↦ φ)) :
    CompatibleLocalEmbeddingData (k := k) (GlobalConeAffine.bundleData φ)
      (R := fun _ ↦ R) (I := fun _ ↦ I) (E := fun _ ↦ E) (fun _ ↦ φ) where
  toLocalEmbeddingCore := 𝓒
  transition _ _ _ _ _ := RingEquiv.refl _
  transition_chartBundleExt _ _ _ _ _ _ := rfl
  transition_comparison i j W hi hj := by
    cases i
    cases j
    have hbase :
        (𝓒.chartBaseExt PUnit.unit W hi).trans
            (𝓒.chartBaseExt PUnit.unit W hj).symm =
          RingEquiv.refl _ := by
      ext x
      simp
    rw [hbase]
    refine OverlapComparison.direct
      { source := SemilinearIso.refl _
        target := SemilinearIso.refl _
        map_degreeZero := by intro; rfl
        map_degreeOne := by intro; rfl
        bundle_generator := by intro; rfl
        cone := RingEquiv.refl _
        cone_algebraMap := by intro; rfl
        cone_conormal := by intro; rfl
        bundle_algebraMap := by intro; rfl
        }

end Affine

end

end VirtualClass.ConeGluing

end GromovWitten.AlgebraicGeometry
