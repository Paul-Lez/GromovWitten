/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5, Claude Opus 5
-/

import GromovWitten.AlgebraicGeometry.Cones.PicardBaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of the conormal complex of a polynomial presentation along a field extension

For `k` a field, `k'` a `k`-algebra, `R = MvPolynomial σ k`, `R' = MvPolynomial σ k'`
(the base change `R' ≅ k' ⊗[k] R`, via Mathlib's `MvPolynomial.algebraMvPolynomial` /
`Algebra.IsPushout`), `I : Ideal R` and `J := I.map (MvPolynomial.map (algebraMap k k'))` the
extended ideal, this file identifies the degreewise base change
`(conormalComplex k R I).baseChange (R' ⧸ J)` of the conormal complex of `I` with the conormal
complex `conormalComplex k' R' J` of the base-changed presentation, and deduces the base-change
invariance of the affine intrinsic normal sheaf.

## Main declarations

* `cotangentDegreeZero`: the `(R' ⧸ J)`-linear comparison
  `(R' ⧸ J) ⊗[R ⧸ I] I/I² → J/J²` in degree zero, and `cotangentDegreeZero_bijective`.
  Bijectivity is obtained from Mathlib's flat base change of the cotangent space of an ideal
  (`Ideal.tensorCotangentEquiv`, available because `R'` is a flat `R`-module, `flat_polyR'`)
  transported along the right unit law `R' ⊗[R] R ≃ R'` (`cotangentBaseChangeEquiv`), together
  with the additive surjection `quotTensorHom : R' ⊗[R] I/I² →+ (R' ⧸ J) ⊗[R ⧸ I] I/I²`
  reducing the left factor modulo `J`.
* `kaehlerDegreeOne`: the `(R' ⧸ J)`-linear comparison
  `(R' ⧸ J) ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] Ω[R⁄k]) → (R' ⧸ J) ⊗[R'] Ω[R'⁄k']` in degree one, and
  `kaehlerDegreeOne_bijective`.  Both sides are free `(R' ⧸ J)`-modules with bases indexed by
  the variables (`kaehlerBasisLeft`, `kaehlerBasisRight`, from
  `KaehlerDifferential.mvPolynomialBasis` and `Module.Basis.baseChange`), and the comparison
  matches the bases (`kaehlerDegreeOne_kaehlerBasisLeft`), hence is the basis-matching
  equivalence `kaehlerDegreeOneEquiv`.
* `conormalBaseChange_comm`: the two comparisons commute with the conormal differentials, so they
  assemble into the chain map `conormalBaseChangeHom` with inverse `conormalBaseChangeInv`.
* `conormalBaseChange : HomotopyEquivalence ((conormalComplex k R I).baseChange (R' ⧸ J))
  (conormalComplex k' R' J)`: an isomorphism of two-term complexes (so the homotopies are zero).
* `normalSheafBaseChangeEquiv'`: **the affine intrinsic normal sheaf is invariant under base
  change of the ground field**.  Instantiating
  `NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafBaseChangeEquiv`
  (`Cones/PicardBaseChange.lean`) with `conormalBaseChange` discharges its `compare` hypothesis:
  for every test algebra `B`, `[N_{U'/M'}/T_{M'}|_{U'}](B) ≌ [N_{U/M}/T_M|_U](B)`.

Supporting infrastructure: `cotangentRidHom`/`cotangentRidInv`/`cotangentRidEquiv` transport
`Ideal.Cotangent` along the right unit law `ridEquiv : R' ⊗[R] R ≃ₐ[R'] R'`; `isPushout`
(`Algebra.IsPushout k k' R R'`) and `flat_polyR'` (`Module.Flat R R'`) record that `R'` is the
flat base change of `R`.
-/

open CategoryTheory
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

namespace ConormalBaseChange

open PicardCriteria LinearTwoTermComplex NormalSheafPicard
open NormalSheafPicard.AffineIntrinsicNormalSheaf

universe u

variable (σ : Type u) (k : Type u) [Field k] (k' : Type u) [CommRing k'] [Algebra k k']

-- Bring Mathlib's (non-global, to avoid a diamond) `Algebra (MvPolynomial σ k)
-- (MvPolynomial σ k')` instance into scope: the algebra structure on the base-changed
-- polynomial ring `R'` over `R`, with `algebraMap R R' = MvPolynomial.map (algebraMap k k')`.
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (I : Ideal (MvPolynomial σ k))

/-- The ring map `R → R'` induced by `k → k'`. -/
noncomputable abbrev polyMap : MvPolynomial σ k →+* MvPolynomial σ k' :=
  MvPolynomial.map (algebraMap k k')

/-- The extended ideal `J = I · R'` of the base-changed polynomial ring `R' = MvPolynomial σ k'`,
under the ring map `polyMap σ k k' : R → R'`. -/
noncomputable abbrev extendedIdeal : Ideal (MvPolynomial σ k') :=
  I.map (polyMap σ k k')

theorem le_comap_polyMap :
    I ≤ (extendedIdeal σ k k' I).comap (polyMap σ k k') :=
  Ideal.le_comap_map

/-- `R` acts on `R' ⧸ J` through `polyMap σ k k' : R → R'` followed by the quotient map. -/
noncomputable local instance algebraQuot :
    Algebra (MvPolynomial σ k) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) :=
  ((Ideal.Quotient.mk (extendedIdeal σ k k' I)).comp
    (polyMap σ k k')).toAlgebra

theorem algebraMap_algebraQuot :
    algebraMap (MvPolynomial σ k) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) =
      (Ideal.Quotient.mk (extendedIdeal σ k k' I)).comp (polyMap σ k k') :=
  rfl

/-- The ring map `R ⧸ I → R' ⧸ J` induced by `polyMap σ k k'`. -/
noncomputable abbrev quotMap :
    MvPolynomial σ k ⧸ I →+* MvPolynomial σ k' ⧸ extendedIdeal σ k k' I :=
  Ideal.quotientMap (extendedIdeal σ k k' I) (polyMap σ k k') (le_comap_polyMap σ k k' I)

/-- `R' ⧸ J` is an algebra over `R ⧸ I`, via `quotMap σ k k'`. -/
noncomputable local instance algebraQuotQuot :
    Algebra (MvPolynomial σ k ⧸ I) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) :=
  (quotMap σ k k' I).toAlgebra

theorem algebraMap_algebraQuotQuot :
    algebraMap (MvPolynomial σ k ⧸ I) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) =
      quotMap σ k k' I :=
  rfl

/-- The two ways of mapping `R → R' ⧸ J` (directly, or through `R ⧸ I`) agree. -/
theorem algebraMap_comp_eq :
    algebraMap (MvPolynomial σ k) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) =
      (algebraMap (MvPolynomial σ k ⧸ I) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)).comp
        (algebraMap (MvPolynomial σ k) (MvPolynomial σ k ⧸ I)) := by
  rw [algebraMap_algebraQuot σ k k', algebraMap_algebraQuotQuot σ k k']
  exact (Ideal.quotientMap_comp_mk (le_comap_polyMap σ k k' I)).symm

/-- The scalar tower `R → R ⧸ I → R' ⧸ J` agrees with `R → R' ⧸ J` directly. -/
noncomputable local instance isScalarTower_quotQuot :
    IsScalarTower (MvPolynomial σ k) (MvPolynomial σ k ⧸ I)
      (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) :=
  IsScalarTower.of_algebraMap_eq' (algebraMap_comp_eq σ k k' I)

/-- `R'` is the pushout `k' ⊗[k] R`, via Mathlib's polynomial-ring pushout instance. -/
noncomputable local instance isPushout :
    Algebra.IsPushout k k' (MvPolynomial σ k) (MvPolynomial σ k') :=
  inferInstance

/-- `R'` is a flat `R`-module: it is the base change, along the flat map `k → k'`
(every module over the field `k` is flat), of the `R`-flat module `R ⊗[k] k'`. -/
noncomputable local instance flat_polyR' :
    Module.Flat (MvPolynomial σ k) (MvPolynomial σ k') :=
  Module.Flat.of_linearEquiv
    (R := MvPolynomial σ k) (M := MvPolynomial σ k ⊗[k] k') (N := MvPolynomial σ k')
    (Algebra.IsPushout.equiv k (MvPolynomial σ k) k' (MvPolynomial σ k')).symm.toLinearEquiv

section DegreeZero

/-- The ring isomorphism `R' ⊗[R] R ≃ₐ[R'] R'` given by the right unit law. -/
noncomputable abbrev ridEquiv :
    MvPolynomial σ k' ⊗[MvPolynomial σ k] MvPolynomial σ k ≃ₐ[MvPolynomial σ k']
      MvPolynomial σ k' :=
  Algebra.TensorProduct.rid (MvPolynomial σ k) (MvPolynomial σ k') (MvPolynomial σ k')

theorem ridEquiv_comp_includeRight :
    (ridEquiv σ k k').toRingHom.comp
        (Algebra.TensorProduct.includeRight.toRingHom :
          MvPolynomial σ k →+* MvPolynomial σ k' ⊗[MvPolynomial σ k] MvPolynomial σ k) =
      polyMap σ k k' := by
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply]
  change ridEquiv σ k k' (Algebra.TensorProduct.includeRight x) = _
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.rid_tmul]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_def, mul_one]

/-- The image, under the right-unit ring isomorphism, of the ideal of `R' ⊗[R] R` extended
from `I` along `includeRight`, is the extended ideal `J` of `R'`. -/
theorem map_ridEquiv_map_includeRight :
    (I.map (Algebra.TensorProduct.includeRight.toRingHom :
        MvPolynomial σ k →+* MvPolynomial σ k' ⊗[MvPolynomial σ k] MvPolynomial σ k)).map
      (ridEquiv σ k k').toRingHom =
      extendedIdeal σ k k' I := by
  rw [Ideal.map_map, ridEquiv_comp_includeRight σ k k']

/-- The ideal `I` extended along `includeRight` to `R' ⊗[R] R`. -/
noncomputable abbrev includedIdeal :
    Ideal (MvPolynomial σ k' ⊗[MvPolynomial σ k] MvPolynomial σ k) :=
  I.map (Algebra.TensorProduct.includeRight.toRingHom :
    MvPolynomial σ k →+* MvPolynomial σ k' ⊗[MvPolynomial σ k] MvPolynomial σ k)

theorem includedIdeal_le_comap_ridEquiv :
    includedIdeal σ k k' I ≤
      (extendedIdeal σ k k' I).comap
        (ridEquiv σ k k').toRingHom :=
  Ideal.map_le_iff_le_comap.mp (le_of_eq (map_ridEquiv_map_includeRight σ k k' I))

/-- The extended ideal `J`, mapped back along `(ridEquiv σ k k').symm`, is the ideal
`I.map includeRight` of `R' ⊗[R] R`. -/
theorem extendedIdeal_map_ridEquiv_symm :
    (extendedIdeal σ k k' I).map
        (ridEquiv σ k k').symm.toRingHom =
      includedIdeal σ k k' I := by
  rw [← map_ridEquiv_map_includeRight σ k k' I, Ideal.map_map]
  rw [show (ridEquiv σ k k').symm.toRingHom.comp
      (ridEquiv σ k k').toRingHom = RingHom.id _ from
        RingHom.ext fun x => (ridEquiv σ k k').symm_apply_apply x]
  exact Ideal.map_id _

theorem extendedIdeal_le_comap_ridEquiv_symm :
    extendedIdeal σ k k' I ≤
      (includedIdeal σ k k' I).comap
        (ridEquiv σ k k').symm.toRingHom :=
  Ideal.map_le_iff_le_comap.mp (le_of_eq (extendedIdeal_map_ridEquiv_symm σ k k' I))

/-- The `R'`-linear comparison `(I.map includeRight).Cotangent → J.Cotangent`, transporting the
cotangent module along the ring isomorphism `ridEquiv σ k k'`. -/
noncomputable def cotangentRidHom :
    (includedIdeal σ k k' I).Cotangent →ₗ[MvPolynomial σ k']
      (extendedIdeal σ k k' I).Cotangent :=
  Ideal.mapCotangent (includedIdeal σ k k' I)
    (extendedIdeal σ k k' I)
    (ridEquiv σ k k').toAlgHom (includedIdeal_le_comap_ridEquiv σ k k' I)

/-- The inverse `R'`-linear comparison `J.Cotangent → (I.map includeRight).Cotangent`. -/
noncomputable def cotangentRidInv :
    (extendedIdeal σ k k' I).Cotangent →ₗ[MvPolynomial σ k']
      (includedIdeal σ k k' I).Cotangent :=
  Ideal.mapCotangent (extendedIdeal σ k k' I)
    (includedIdeal σ k k' I)
    (ridEquiv σ k k').symm.toAlgHom (extendedIdeal_le_comap_ridEquiv_symm σ k k' I)

theorem cotangentRidInv_cotangentRidHom :
    (cotangentRidInv σ k k' I).comp
        (cotangentRidHom σ k k' I) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (includedIdeal σ k k' I) x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have key : cotangentRidInv σ k k' I
      (cotangentRidHom σ k k' I
        (Ideal.toCotangent (includedIdeal σ k k' I) x)) =
      Ideal.toCotangent (includedIdeal σ k k' I)
        ⟨(ridEquiv σ k k').symm
          ((ridEquiv σ k k') x), by
            rw [(ridEquiv σ k k').symm_apply_apply]; exact x.2⟩ := rfl
  rw [key]
  exact congrArg (Ideal.toCotangent (includedIdeal σ k k' I))
    (Subtype.ext ((ridEquiv σ k k').symm_apply_apply x))

theorem cotangentRidHom_cotangentRidInv :
    (cotangentRidHom σ k k' I).comp
        (cotangentRidInv σ k k' I) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (extendedIdeal σ k k' I) x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have key : cotangentRidHom σ k k' I
      (cotangentRidInv σ k k' I
        (Ideal.toCotangent (extendedIdeal σ k k' I) x)) =
      Ideal.toCotangent (extendedIdeal σ k k' I)
        ⟨(ridEquiv σ k k')
          ((ridEquiv σ k k').symm x), by
            rw [(ridEquiv σ k k').apply_symm_apply]; exact x.2⟩ := rfl
  rw [key]
  exact congrArg (Ideal.toCotangent (extendedIdeal σ k k' I))
    (Subtype.ext ((ridEquiv σ k k').apply_symm_apply x))

end DegreeZero

section DegreeOne

/-- The `R`-linear comparison `Ω[R⁄k] → (R'⧸J) ⊗[R'] Ω[R'⁄k']`, sending `ω` to
`1 ⊗ (KaehlerDifferential.map k k' R R' ω)`. -/
noncomputable def kaehlerAux :
    Ω[MvPolynomial σ k⁄k] →ₗ[MvPolynomial σ k]
      (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k']
        Ω[MvPolynomial σ k'⁄k'] :=
  ((TensorProduct.mk (MvPolynomial σ k') (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
      Ω[MvPolynomial σ k'⁄k'] 1).restrictScalars (MvPolynomial σ k)).comp
    (KaehlerDifferential.map k k' (MvPolynomial σ k) (MvPolynomial σ k'))

theorem kaehlerAux_apply (ω : Ω[MvPolynomial σ k⁄k]) :
    kaehlerAux σ k k' I ω =
      (1 : MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗ₜ
        KaehlerDifferential.map k k' (MvPolynomial σ k) (MvPolynomial σ k') ω :=
  rfl

/-- The `(R ⧸ I)`-linear comparison `(R ⧸ I) ⊗[R] Ω[R⁄k] → (R' ⧸ J) ⊗[R'] Ω[R'⁄k']`. -/
noncomputable def kaehlerDegreeOneAux :
    (MvPolynomial σ k ⧸ I) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k] →ₗ[MvPolynomial σ k ⧸ I]
      (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k']
        Ω[MvPolynomial σ k'⁄k'] :=
  LinearMap.liftBaseChange (MvPolynomial σ k ⧸ I) (kaehlerAux σ k k' I)

/-- **The degree-one comparison of the conormal complexes**: the `(R' ⧸ J)`-linear map
`(R' ⧸ J) ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] Ω[R⁄k]) → (R' ⧸ J) ⊗[R'] Ω[R'⁄k']`.  It is bijective, see
`kaehlerDegreeOne_bijective`. -/
noncomputable def kaehlerDegreeOne :
    (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k ⧸ I]
        ((MvPolynomial σ k ⧸ I) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k])
      →ₗ[MvPolynomial σ k' ⧸ extendedIdeal σ k k' I]
      (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k']
        Ω[MvPolynomial σ k'⁄k'] :=
  LinearMap.liftBaseChange (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
    (kaehlerDegreeOneAux σ k k' I)

end DegreeOne

section DegreeZeroComparison

/-- `I ≤ J.comap (algebraMap R R')`: `algebraMap R R'` agrees with `polyMap σ k k'`. -/
theorem le_comap_algebraMap :
    I ≤ (extendedIdeal σ k k' I).comap
      (algebraMap (MvPolynomial σ k) (MvPolynomial σ k')) :=
  le_comap_polyMap σ k k' I

/-- The `R`-linear comparison `I.Cotangent → J.Cotangent`, via `mapCotangent` along the algebra
map `R → R'`. -/
noncomputable def cotangentQuotHomAux :
    I.Cotangent →ₗ[MvPolynomial σ k] (extendedIdeal σ k k' I).Cotangent :=
  Ideal.mapCotangent I (extendedIdeal σ k k' I)
    (Algebra.ofId (MvPolynomial σ k) (MvPolynomial σ k')) (le_comap_algebraMap σ k k' I)

/-- `R` acts on `J.Cotangent` through `R → R ⧸ I → R' ⧸ J`. -/
noncomputable local instance moduleR_extendedCotangent :
    Module (MvPolynomial σ k) (extendedIdeal σ k k' I).Cotangent :=
  Module.compHom _
    (algebraMap (MvPolynomial σ k) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I))

/-- `R ⧸ I` acts on `J.Cotangent` through `R ⧸ I → R' ⧸ J`. -/
noncomputable local instance moduleQuotI_extendedCotangent :
    Module (MvPolynomial σ k ⧸ I) (extendedIdeal σ k k' I).Cotangent :=
  Module.compHom _
    (algebraMap (MvPolynomial σ k ⧸ I) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I))

theorem isScalarTower_extendedCotangent :
    IsScalarTower (MvPolynomial σ k) (MvPolynomial σ k ⧸ I)
      (extendedIdeal σ k k' I).Cotangent where
  smul_assoc r c m := by
    change algebraMap (MvPolynomial σ k ⧸ I)
        (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) (r • c) • m =
      algebraMap (MvPolynomial σ k) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) r •
        (algebraMap (MvPolynomial σ k ⧸ I)
          (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) c • m)
    rw [Algebra.smul_def r c, map_mul, mul_smul,
      show algebraMap (MvPolynomial σ k ⧸ I)
          (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
          (algebraMap (MvPolynomial σ k) (MvPolynomial σ k ⧸ I) r) =
        algebraMap (MvPolynomial σ k) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) r from
        (RingHom.congr_fun (algebraMap_comp_eq σ k k' I) r).symm]

attribute [local instance] isScalarTower_extendedCotangent

noncomputable local instance isScalarTower_quotI_extendedCotangent :
    IsScalarTower (MvPolynomial σ k ⧸ I) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
      (extendedIdeal σ k k' I).Cotangent :=
  IsScalarTower.of_compHom (MvPolynomial σ k ⧸ I) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
    (extendedIdeal σ k k' I).Cotangent

/-- The `(R ⧸ I)`-linear comparison `I.Cotangent → J.Cotangent`. -/
noncomputable def cotangentQuotHom :
    I.Cotangent →ₗ[MvPolynomial σ k ⧸ I]
      (extendedIdeal σ k k' I).Cotangent :=
  (cotangentQuotHomAux σ k k' I).extendScalarsOfSurjective
    (S := MvPolynomial σ k ⧸ I) Ideal.Quotient.mk_surjective

/-- **The degree-zero comparison of the conormal complexes**: the `(R' ⧸ J)`-linear map
`(R' ⧸ J) ⊗[R ⧸ I] I.Cotangent → J.Cotangent`.  It is bijective, see
`cotangentDegreeZero_bijective`. -/
noncomputable def cotangentDegreeZero :
    (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k ⧸ I]
        I.Cotangent →ₗ[MvPolynomial σ k' ⧸ extendedIdeal σ k k' I]
      (extendedIdeal σ k k' I).Cotangent :=
  LinearMap.liftBaseChange (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
    (cotangentQuotHom σ k k' I)

end DegreeZeroComparison

section DegreeOneBijective

/-- The `(R' ⧸ J)`-basis of the degree-one term `(R' ⧸ J) ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] Ω[R⁄k])` of the
base-changed conormal complex, indexed by the variables. -/
noncomputable def kaehlerBasisLeft :
    Module.Basis σ (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
      ((MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k ⧸ I]
        ((MvPolynomial σ k ⧸ I) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k])) :=
  ((KaehlerDifferential.mvPolynomialBasis k σ).baseChange
      (MvPolynomial σ k ⧸ I)).baseChange (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)

/-- The `(R' ⧸ J)`-basis of the degree-one term `(R' ⧸ J) ⊗[R'] Ω[R'⁄k']` of the conormal complex
of the base-changed presentation, indexed by the variables. -/
noncomputable def kaehlerBasisRight :
    Module.Basis σ (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
      ((MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k']
        Ω[MvPolynomial σ k'⁄k']) :=
  (KaehlerDifferential.mvPolynomialBasis k' σ).baseChange
    (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)

/-- The basis vectors of `kaehlerBasisLeft` are the classes of the differentials of the
variables. -/
theorem kaehlerBasisLeft_apply (i : σ) :
    kaehlerBasisLeft σ k k' I i =
      (1 : MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗ₜ
        ((1 : MvPolynomial σ k ⧸ I) ⊗ₜ
          KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i)) := by
  rw [kaehlerBasisLeft, Module.Basis.baseChange_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]

/-- The basis vectors of `kaehlerBasisRight` are the classes of the differentials of the
variables. -/
theorem kaehlerBasisRight_apply (i : σ) :
    kaehlerBasisRight σ k k' I i =
      (1 : MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗ₜ
        KaehlerDifferential.D k' (MvPolynomial σ k') (MvPolynomial.X i) := by
  rw [kaehlerBasisRight, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]

/-- The degree-one comparison map on an element of the form `t ⊗ (1 ⊗ ω)`. -/
theorem kaehlerDegreeOne_tmul_one_tmul (t : MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
    (ω : Ω[MvPolynomial σ k⁄k]) :
    kaehlerDegreeOne σ k k' I (t ⊗ₜ ((1 : MvPolynomial σ k ⧸ I) ⊗ₜ ω)) =
      t • ((1 : MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗ₜ
        KaehlerDifferential.map k k' (MvPolynomial σ k) (MvPolynomial σ k') ω) := by
  simp only [kaehlerDegreeOne, kaehlerDegreeOneAux, LinearMap.liftBaseChange_tmul, one_smul,
    kaehlerAux_apply]

/-- The structure map `R → R'` fixes the variables. -/
theorem algebraMap_X (i : σ) :
    algebraMap (MvPolynomial σ k) (MvPolynomial σ k') (MvPolynomial.X i) = MvPolynomial.X i := by
  rw [MvPolynomial.algebraMap_def]
  exact MvPolynomial.map_X _ _

/-- **The degree-one comparison map takes the basis to the basis.** -/
theorem kaehlerDegreeOne_kaehlerBasisLeft (i : σ) :
    kaehlerDegreeOne σ k k' I (kaehlerBasisLeft σ k k' I i) = kaehlerBasisRight σ k k' I i := by
  rw [kaehlerBasisLeft_apply, kaehlerDegreeOne_tmul_one_tmul, one_smul,
    KaehlerDifferential.map_D, algebraMap_X, kaehlerBasisRight_apply]

/-- The degree-one comparison, packaged as the `(R' ⧸ J)`-linear equivalence matching the two
bases indexed by the variables. -/
noncomputable def kaehlerDegreeOneEquiv :
    ((MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k ⧸ I]
        ((MvPolynomial σ k ⧸ I) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k]))
      ≃ₗ[MvPolynomial σ k' ⧸ extendedIdeal σ k k' I]
      ((MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k']
        Ω[MvPolynomial σ k'⁄k']) :=
  (kaehlerBasisLeft σ k k' I).equiv (kaehlerBasisRight σ k k' I) (Equiv.refl σ)

/-- The degree-one comparison map is the basis-matching equivalence. -/
theorem kaehlerDegreeOne_eq :
    kaehlerDegreeOne σ k k' I = (kaehlerDegreeOneEquiv σ k k' I).toLinearMap :=
  (kaehlerBasisLeft σ k k' I).ext fun i => by
    rw [kaehlerDegreeOne_kaehlerBasisLeft]
    exact ((kaehlerBasisLeft σ k k' I).equiv_apply i
      (kaehlerBasisRight σ k k' I) (Equiv.refl σ)).symm

/-- **The degree-one comparison map is bijective.** -/
theorem kaehlerDegreeOne_bijective : Function.Bijective (kaehlerDegreeOne σ k k' I) := by
  rw [kaehlerDegreeOne_eq]
  exact (kaehlerDegreeOneEquiv σ k k' I).bijective

end DegreeOneBijective

section DegreeZeroBijective

/-- The image of `x ∈ I` in the extended ideal `J`. -/
theorem polyMap_mem_extendedIdeal (x : I) :
    polyMap σ k k' (x : MvPolynomial σ k) ∈ extendedIdeal σ k k' I :=
  Ideal.mem_map_of_mem _ x.2

/-- The degree-zero comparison map on a generator. -/
theorem cotangentQuotHom_toCotangent (x : I) :
    cotangentQuotHom σ k k' I (Ideal.toCotangent I x) =
      Ideal.toCotangent (extendedIdeal σ k k' I)
        ⟨polyMap σ k k' (x : MvPolynomial σ k), polyMap_mem_extendedIdeal σ k k' I x⟩ :=
  rfl

/-- The degree-zero comparison map on a pure tensor. -/
theorem cotangentDegreeZero_tmul (t : MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) (x : I) :
    cotangentDegreeZero σ k k' I (t ⊗ₜ Ideal.toCotangent I x) =
      t • Ideal.toCotangent (extendedIdeal σ k k' I)
        ⟨polyMap σ k k' (x : MvPolynomial σ k), polyMap_mem_extendedIdeal σ k k' I x⟩ := by
  simp only [cotangentDegreeZero, LinearMap.liftBaseChange_tmul, cotangentQuotHom_toCotangent]

/-- The `R'`-linear isomorphism `(I · (R' ⊗[R] R))/(…)² ≃ J/J²` transporting the cotangent module
along the right unit law `ridEquiv`. -/
noncomputable def cotangentRidEquiv :
    (includedIdeal σ k k' I).Cotangent ≃ₗ[MvPolynomial σ k']
      (extendedIdeal σ k k' I).Cotangent :=
  LinearEquiv.ofLinearMap (cotangentRidHom σ k k' I) (cotangentRidInv σ k k' I)
    (cotangentRidHom_cotangentRidInv σ k k' I) (cotangentRidInv_cotangentRidHom σ k k' I)

/-- **Flat base change of the conormal module**: `R' ⊗[R] I/I² ≃ J/J²`.  This is Mathlib's flat
base change of the cotangent space of an ideal (`Ideal.tensorCotangentEquiv`, applicable because
`R'` is a flat `R`-module) composed with the right unit law `R' ⊗[R] R ≃ R'`. -/
noncomputable def cotangentBaseChangeEquiv :
    MvPolynomial σ k' ⊗[MvPolynomial σ k] I.Cotangent ≃ₗ[MvPolynomial σ k']
      (extendedIdeal σ k k' I).Cotangent :=
  (Ideal.tensorCotangentEquiv (MvPolynomial σ k) (MvPolynomial σ k') I).trans
    (cotangentRidEquiv σ k k' I)

/-- `cotangentBaseChangeEquiv` on a pure tensor. -/
theorem cotangentBaseChangeEquiv_tmul (a : MvPolynomial σ k') (x : I) :
    cotangentBaseChangeEquiv σ k k' I (a ⊗ₜ Ideal.toCotangent I x) =
      a • Ideal.toCotangent (extendedIdeal σ k k' I)
        ⟨polyMap σ k k' (x : MvPolynomial σ k), polyMap_mem_extendedIdeal σ k k' I x⟩ := by
  have hx : (ridEquiv σ k k') ((1 : MvPolynomial σ k') ⊗ₜ[MvPolynomial σ k]
      (x : MvPolynomial σ k)) = polyMap σ k k' (x : MvPolynomial σ k) :=
    RingHom.congr_fun (ridEquiv_comp_includeRight σ k k') (x : MvPolynomial σ k)
  have hmem : (1 : MvPolynomial σ k') ⊗ₜ[MvPolynomial σ k] (x : MvPolynomial σ k) ∈
      includedIdeal σ k k' I := Ideal.mem_map_of_mem _ x.2
  have key : cotangentRidEquiv σ k k' I
      (Ideal.toCotangent (includedIdeal σ k k' I)
        ⟨(1 : MvPolynomial σ k') ⊗ₜ[MvPolynomial σ k] (x : MvPolynomial σ k), hmem⟩) =
      Ideal.toCotangent (extendedIdeal σ k k' I)
        ⟨(ridEquiv σ k k') ((1 : MvPolynomial σ k') ⊗ₜ[MvPolynomial σ k]
            (x : MvPolynomial σ k)),
          includedIdeal_le_comap_ridEquiv σ k k' I hmem⟩ := rfl
  change cotangentRidEquiv σ k k' I
      (Ideal.tensorCotangentEquiv (MvPolynomial σ k) (MvPolynomial σ k') I
        (a ⊗ₜ Ideal.toCotangent I x)) = _
  rw [Ideal.tensorCotangentEquiv_tmul, map_smul]
  exact congrArg (fun z => a • z)
    (key.trans (congrArg (Ideal.toCotangent (extendedIdeal σ k k' I)) (Subtype.ext hx)))

end DegreeZeroBijective

section DegreeZeroSurjection

/-- The additive map `R' → I/I² →+ (R' ⧸ J) ⊗[R ⧸ I] I/I²`, `a ↦ c ↦ [a] ⊗ c`. -/
noncomputable def quotTensorBilin :
    MvPolynomial σ k' →+ I.Cotangent →+
      (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k ⧸ I] I.Cotangent :=
  AddMonoidHom.mk'
    (fun a => (TensorProduct.mk (MvPolynomial σ k ⧸ I)
      (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) I.Cotangent
      (Ideal.Quotient.mk (extendedIdeal σ k k' I) a)).toAddMonoidHom)
    fun a b => by
      refine AddMonoidHom.ext fun c => ?_
      change Ideal.Quotient.mk (extendedIdeal σ k k' I) (a + b) ⊗ₜ c =
        Ideal.Quotient.mk (extendedIdeal σ k k' I) a ⊗ₜ c +
          Ideal.Quotient.mk (extendedIdeal σ k k' I) b ⊗ₜ c
      rw [map_add, TensorProduct.add_tmul]

/-- The comparison of the two base changes of the conormal module, as an additive map: it
reduces the left tensor factor `R'` modulo `J`.  Only additivity is asserted, which is all that
is needed below and avoids having to produce an `R'`-module structure on the target. -/
noncomputable def quotTensorHom :
    MvPolynomial σ k' ⊗[MvPolynomial σ k] I.Cotangent →+
      (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k ⧸ I] I.Cotangent :=
  TensorProduct.liftAddHom (quotTensorBilin σ k k' I) fun r a c => by
    change Ideal.Quotient.mk (extendedIdeal σ k k' I) (r • a) ⊗ₜ c =
      Ideal.Quotient.mk (extendedIdeal σ k k' I) a ⊗ₜ (r • c)
    have h1 : Ideal.Quotient.mk (extendedIdeal σ k k' I) (r • a) =
        algebraMap (MvPolynomial σ k) (MvPolynomial σ k ⧸ I) r •
          Ideal.Quotient.mk (extendedIdeal σ k k' I) a := by
      have hr : algebraMap (MvPolynomial σ k ⧸ I) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
          (algebraMap (MvPolynomial σ k) (MvPolynomial σ k ⧸ I) r) =
          algebraMap (MvPolynomial σ k) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) r :=
        (RingHom.congr_fun (algebraMap_comp_eq σ k k' I) r).symm
      rw [Algebra.smul_def r a, Algebra.smul_def, hr, map_mul]
      rfl
    rw [h1, TensorProduct.smul_tmul, algebraMap_smul]

/-- `quotTensorHom` on a pure tensor. -/
theorem quotTensorHom_tmul (a : MvPolynomial σ k') (c : I.Cotangent) :
    quotTensorHom σ k k' I (a ⊗ₜ c) =
      Ideal.Quotient.mk (extendedIdeal σ k k' I) a ⊗ₜ c :=
  rfl

/-- `quotTensorHom` is surjective: every class in `R' ⧸ J` is the class of an element of `R'`. -/
theorem quotTensorHom_surjective : Function.Surjective (quotTensorHom σ k k' I) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul t c =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
    exact ⟨a ⊗ₜ c, quotTensorHom_tmul σ k k' I a c⟩
  | add z w hz hw =>
    obtain ⟨u, hu⟩ := hz
    obtain ⟨v, hv⟩ := hw
    exact ⟨u + v, by rw [map_add, hu, hv]⟩

/-- **The degree-zero comparison map, precomposed with the reduction of the left factor, is the
flat base change isomorphism of the conormal module.** -/
theorem cotangentDegreeZero_quotTensorHom
    (w : MvPolynomial σ k' ⊗[MvPolynomial σ k] I.Cotangent) :
    cotangentDegreeZero σ k k' I (quotTensorHom σ k k' I w) =
      cotangentBaseChangeEquiv σ k k' I w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a c =>
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I c
    rw [quotTensorHom_tmul, cotangentDegreeZero_tmul, cotangentBaseChangeEquiv_tmul,
      ← algebraMap_smul (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) a]
    rfl
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]

/-- **The degree-zero comparison map is bijective.** -/
theorem cotangentDegreeZero_bijective : Function.Bijective (cotangentDegreeZero σ k k' I) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := quotTensorHom_surjective σ k k' I z
    rw [cotangentDegreeZero_quotTensorHom] at hz
    rw [(cotangentBaseChangeEquiv σ k k' I).map_eq_zero_iff.mp hz, map_zero]
  · intro y
    obtain ⟨w, rfl⟩ := (cotangentBaseChangeEquiv σ k k' I).surjective y
    exact ⟨quotTensorHom σ k k' I w, cotangentDegreeZero_quotTensorHom σ k k' I w⟩

end DegreeZeroSurjection

section Comparison

/-- The structure map `R → R'` is `polyMap`. -/
theorem algebraMap_eq_polyMap (p : MvPolynomial σ k) :
    algebraMap (MvPolynomial σ k) (MvPolynomial σ k') p = polyMap σ k k' p :=
  rfl

/-- **The two comparison maps commute with the conormal differentials.**  Both sides send the
generator `t ⊗ [y]`, for `y ∈ I`, to `t · (1 ⊗ d(polyMap y))`. -/
theorem conormalBaseChange_comm
    (x : (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k ⧸ I] I.Cotangent) :
    kaehlerDegreeOne σ k k' I
        (LinearMap.baseChange (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)
          (AffineNormalCone.conormalMap k (MvPolynomial σ k) I) x) =
      AffineNormalCone.conormalMap k' (MvPolynomial σ k') (extendedIdeal σ k k' I)
        (cotangentDegreeZero σ k k' I x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul t c =>
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective I c
    rw [LinearMap.baseChange_tmul, AffineNormalCone.conormalMap_toCotangent,
      kaehlerDegreeOne_tmul_one_tmul, cotangentDegreeZero_tmul, map_smul,
      AffineNormalCone.conormalMap_toCotangent, KaehlerDifferential.map_D,
      algebraMap_eq_polyMap]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The degree-zero comparison as a `(R' ⧸ J)`-linear equivalence. -/
noncomputable def cotangentDegreeZeroEquiv :
    ((MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) ⊗[MvPolynomial σ k ⧸ I] I.Cotangent)
      ≃ₗ[MvPolynomial σ k' ⧸ extendedIdeal σ k k' I] (extendedIdeal σ k k' I).Cotangent :=
  LinearEquiv.ofBijective (cotangentDegreeZero σ k k' I) (cotangentDegreeZero_bijective σ k k' I)

/-- **The comparison chain map** from the base change of the conormal complex of `I ⊆ R` to the
conormal complex of the extended ideal `J ⊆ R'`. -/
noncomputable def conormalBaseChangeHom :
    LinearTwoTermComplex.Hom
      ((conormalComplex k (MvPolynomial σ k) I).baseChange
        (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I))
      (conormalComplex k' (MvPolynomial σ k') (extendedIdeal σ k k' I)) where
  degreeZero := cotangentDegreeZero σ k k' I
  degreeOne := kaehlerDegreeOne σ k k' I
  comm x := conormalBaseChange_comm σ k k' I x

/-- The inverse comparison chain map. -/
noncomputable def conormalBaseChangeInv :
    LinearTwoTermComplex.Hom
      (conormalComplex k' (MvPolynomial σ k') (extendedIdeal σ k k' I))
      ((conormalComplex k (MvPolynomial σ k) I).baseChange
        (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I)) where
  degreeZero := (cotangentDegreeZeroEquiv σ k k' I).symm.toLinearMap
  degreeOne := (kaehlerDegreeOneEquiv σ k k' I).symm.toLinearMap
  comm y := by
    have hx : cotangentDegreeZero σ k k' I
        ((cotangentDegreeZeroEquiv σ k k' I).symm y) = y :=
      (cotangentDegreeZeroEquiv σ k k' I).apply_symm_apply y
    have hcomm := conormalBaseChange_comm σ k k' I ((cotangentDegreeZeroEquiv σ k k' I).symm y)
    rw [hx, kaehlerDegreeOne_eq] at hcomm
    change (kaehlerDegreeOneEquiv σ k k' I).symm
        (AffineNormalCone.conormalMap k' (MvPolynomial σ k') (extendedIdeal σ k k' I) y) = _
    rw [← hcomm]
    exact (kaehlerDegreeOneEquiv σ k k' I).symm_apply_apply _

/-- **Base change of the conormal complex along a field extension.**  For `k` a field, `k'` a
`k`-algebra, `R = k[x_σ]`, `R' = k'[x_σ]`, `I ⊆ R` an ideal and `J = I · R'` the extended ideal,
the degreewise base change `(conormalComplex k R I).baseChange (R' ⧸ J)` of the conormal complex
of `I` is isomorphic — hence chain-homotopy equivalent, with zero homotopies — to the conormal
complex `conormalComplex k' R' J` of the base-changed presentation.  In degree zero this is flat
base change of the conormal module `I/I²`, in degree one it is the freeness of the module of
differentials of a polynomial ring. -/
noncomputable def conormalBaseChange :
    LinearTwoTermComplex.HomotopyEquivalence
      ((conormalComplex k (MvPolynomial σ k) I).baseChange
        (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I))
      (conormalComplex k' (MvPolynomial σ k') (extendedIdeal σ k k' I)) where
  hom := conormalBaseChangeHom σ k k' I
  inv := conormalBaseChangeInv σ k k' I
  unit :=
    { homotopy := 0
      degreeZero x := by
        refine ((cotangentDegreeZeroEquiv σ k k' I).symm_apply_apply x).trans ?_
        exact (add_eq_of_eq_zero_degreeZero _ _ rfl).symm
      degreeOne x := by
        refine ?_
        have h : (kaehlerDegreeOneEquiv σ k k' I).symm
            (kaehlerDegreeOne σ k k' I x) = x := by
          rw [kaehlerDegreeOne_eq]
          exact (kaehlerDegreeOneEquiv σ k k' I).symm_apply_apply x
        exact h.trans (add_eq_of_eq_zero_degreeOne _ _ (map_zero _)).symm }
  counit :=
    { homotopy := 0
      degreeZero y := by
        refine ((cotangentDegreeZeroEquiv σ k k' I).apply_symm_apply y).symm.trans ?_
        exact (add_eq_of_eq_zero_degreeZero
          (E := conormalComplex k' (MvPolynomial σ k') (extendedIdeal σ k k' I)) _ _ rfl).symm
      degreeOne y := by
        have h : kaehlerDegreeOne σ k k' I
            ((kaehlerDegreeOneEquiv σ k k' I).symm y) = y := by
          rw [kaehlerDegreeOne_eq]
          exact (kaehlerDegreeOneEquiv σ k k' I).apply_symm_apply y
        exact h.symm.trans (add_eq_of_eq_zero_degreeOne
          (E := conormalComplex k' (MvPolynomial σ k') (extendedIdeal σ k k' I)) _ _
          (map_zero _)).symm }

end Comparison

section Application

variable (B : Type u) [CommRing B]
  [Algebra (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) B] [Algebra (MvPolynomial σ k ⧸ I) B]
  [IsScalarTower (MvPolynomial σ k ⧸ I) (MvPolynomial σ k' ⧸ extendedIdeal σ k k' I) B]

/-- **The affine intrinsic normal sheaf is invariant under base change of the ground field.**
For `k` a field, `k'` a `k`-algebra, `R = k[x_σ]`, `I ⊆ R`, `R' = k'[x_σ]` and `J = I · R'`, the
quotient groupoid `[N_{U'/M'} / T_{M'}|_{U'}](B)` of the base-changed presentation is equivalent,
over every test algebra `B` (an `R' ⧸ J`-algebra which is compatibly an `R ⧸ I`-algebra), to
`[N_{U/M} / T_M|_U](B)`.  This discharges the `compare`
hypothesis of `NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafBaseChangeEquiv` with
`conormalBaseChange`. -/
noncomputable def normalSheafBaseChangeEquiv' :
    ConeQuotient.QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k'
        (MvPolynomial σ k') (extendedIdeal σ k k' I)) B ≌
      ConeQuotient.QuotientGroupoid
        (AffineNormalCone.normalSheafTangentAction k (MvPolynomial σ k) I) B :=
  normalSheafBaseChangeEquiv I (extendedIdeal σ k k' I) B (conormalBaseChange σ k k' I)

end Application

end ConormalBaseChange

end GromovWitten.AlgebraicGeometry
