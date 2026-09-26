/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5
-/

import GromovWitten.AlgebraicGeometry.ObstructionTheory.AffineObstructionCone

/-!
# The Picard groupoid of a base-changed two-term complex

For a two-term complex `E : LinearTwoTermComplex R` and an `R`-algebra `R'`,
`LinearTwoTermComplex.baseChange` (`ObstructionTheory/AffineObstructionCone.lean`) builds the
degreewise base-changed complex `E.baseChange R' : LinearTwoTermComplex R'`.  Separately,
`PicardCriteria.dualPoints` (`Cones/CriteriaBundle.lean`) attaches to a two-term complex and a
test algebra the two-term complex of `B`-points of its dual.  This file relates the two
constructions: for `B` an algebra over both `R'` and `R`, compatibly, the Picard groupoid of the
`B`-points of the dual of `E.baseChange R'` is *isomorphic* (not merely equivalent) to the
Picard groupoid of the `B`-points of the dual of `E`.  This fills the gap identified by the
round-19 survey: `LinearTwoTermComplex.baseChange` and `LinearTwoTermComplex.quotient` /
`PicardCriteria.dualPoints` were never previously related by a theorem.

## Main declarations

* `PicardCriteria.dualBaseChangeLinearEquiv`: the `B`-linear equivalence
  `(R' ⊗[R] M →ₗ[R'] B) ≃ₗ[B] (M →ₗ[R] B)` underlying the comparison, for any `R`-module `M`.
* `PicardCriteria.dualPointsBaseChangeHom`: the chain map (in `LinearTwoTermComplex B`)
  `dualPoints (E.baseChange R') B ⟶ dualPoints E B` built from this equivalence in each degree.
* `PicardCriteria.dualPointsBaseChangeHomotopyEquivalence`: it is a chain-homotopy equivalence
  (in fact literally invertible), whence
* `PicardCriteria.dualPointsBaseChangeEquiv : (dualPoints (E.baseChange R') B).quotient ≌
  (dualPoints E B).quotient`, the equivalence of Picard groupoids of goal 1.
* `PicardCriteria.dualPointsBaseChangeHom_naturality`: naturality of the comparison chain map in
  the test algebra `B`, i.e. compatibility with `PicardCriteria.dualPointsMap` reindexing along
  an `R'`-algebra map `B ⟶ B'` (goal 2).
* `NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafBaseChangeEquiv`: specialising
  goal 1 to `E = conormalComplex k R I`, given an explicit identification of
  `(conormalComplex k R I).baseChange (R' ⧸ J)` with `conormalComplex k' R' J` as a hypothesis
  (the comparison itself, i.e. flat base change of the cotangent complex of a presentation, is
  not proved in the repository at the time of writing; see the docstring of that declaration for
  the precise gap).

## Design

Throughout, `B` carries *both* an `R'`-algebra structure and an `R`-algebra structure, related by
`[IsScalarTower R R' B]`: this is the standard way scalar-restriction data is threaded through
this repository (compare `Cones/NormalConeBaseChange.lean`'s `pointEquiv`).  The comparison at
each degree is `Mathlib`'s base-change adjunction `LinearMap.liftBaseChangeEquiv`, repackaged as
a `B`-linear (rather than merely `R'`-linear) equivalence: post-composition with elements of `B`
commutes with the restriction along `x ↦ 1 ⊗ x` on the nose, so no `sorry` or extra hypothesis is
needed to upgrade the linearity.
-/

open CategoryTheory
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

universe u

open LinearTwoTermComplex

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R']

section LinearEquiv

variable (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B] [IsScalarTower R R' B]
  (M : Type u) [AddCommGroup M] [Module R M]

/-- **The base-change linear equivalence of `B`-points.**  `R'`-linear functionals on
`R' ⊗[R] M` valued in `B` correspond to `R`-linear functionals on `M` valued in `B`, by
restricting along `x ↦ 1 ⊗ x` (Mathlib's `LinearMap.liftBaseChangeEquiv`).  This equivalence is
`R'`-linear in Mathlib; here it is repackaged as `B`-linear, since post-composition with `b : B`
commutes with restriction along `1 ⊗ -` for the same reason it commutes with everything else:
both sides are literally `fun l => b * l (1 ⊗ₜ x)` (`LinearMap.smul_apply`). -/
noncomputable def dualBaseChangeLinearEquiv :
    (R' ⊗[R] M →ₗ[R'] B) ≃ₗ[B] (M →ₗ[R] B) where
  toFun l := (LinearMap.liftBaseChangeEquiv R' (M := M) (N := B)).symm l
  invFun g := LinearMap.liftBaseChangeEquiv R' (M := M) (N := B) g
  left_inv l := (LinearMap.liftBaseChangeEquiv R' (M := M) (N := B)).apply_symm_apply l
  right_inv g := (LinearMap.liftBaseChangeEquiv R' (M := M) (N := B)).symm_apply_apply g
  map_add' l l' := by simp
  map_smul' b l := by
    apply LinearMap.ext
    intro x
    simp [LinearMap.liftBaseChangeEquiv_symm_apply]

/-- The forward direction of `dualBaseChangeLinearEquiv` is restriction along `x ↦ 1 ⊗ x`. -/
@[simp]
theorem dualBaseChangeLinearEquiv_apply (l : R' ⊗[R] M →ₗ[R'] B) (x : M) :
    dualBaseChangeLinearEquiv B M l x = l (1 ⊗ₜ[R] x) :=
  rfl

/-- The inverse direction of `dualBaseChangeLinearEquiv` on a pure tensor is scalar extension. -/
@[simp]
theorem dualBaseChangeLinearEquiv_symm_apply_tmul (g : M →ₗ[R] B) (r : R') (x : M) :
    (dualBaseChangeLinearEquiv B M).symm g (r ⊗ₜ[R] x) = r • g x :=
  rfl

end LinearEquiv

section ChainMap

variable (E : LinearTwoTermComplex R) (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B]
  [IsScalarTower R R' B]

/-- **The comparison chain map**, from the complex of `B`-points of the dual of the
base-changed complex to the complex of `B`-points of the dual of `E`, built in each degree from
`dualBaseChangeLinearEquiv`. -/
noncomputable def dualPointsBaseChangeHom :
    Hom (dualPoints (E.baseChange R') B) (dualPoints E B) where
  degreeZero := (dualBaseChangeLinearEquiv B E.degreeOne).toLinearMap
  degreeOne := (dualBaseChangeLinearEquiv B E.degreeZero).toLinearMap
  comm l := by
    apply LinearMap.ext
    intro y
    rfl

/-- Auxiliary form of the commutativity square for `dualPointsBaseChangeInv`, stated entirely
with manifest (unfolded) types so that `TensorProduct.ext'` can unify with its conclusion; see
the docstring of `dualBaseChangeLinearEquiv` for why the analogous statement through the opaque
`PicardCriteria.dualPoints` requires this detour (`exact`/`rfl` see through the definition, but
`apply`-style unification of a bare structure projection does not). -/
theorem dualPointsBaseChangeInv_comm_aux (g : E.degreeOne →ₗ[R] B) :
    (dualBaseChangeLinearEquiv B E.degreeZero).symm.toLinearMap.comp (precomp E.differential B) g
      = (precomp (LinearMap.baseChange R' E.differential) B).comp
          (dualBaseChangeLinearEquiv B E.degreeOne).symm.toLinearMap g := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul r x => rfl
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

/-- **The inverse comparison chain map.** -/
noncomputable def dualPointsBaseChangeInv :
    Hom (dualPoints E B) (dualPoints (E.baseChange R') B) where
  degreeZero := (dualBaseChangeLinearEquiv B E.degreeOne).symm.toLinearMap
  degreeOne := (dualBaseChangeLinearEquiv B E.degreeZero).symm.toLinearMap
  comm g := dualPointsBaseChangeInv_comm_aux E B g

/-- **The comparison is a chain-homotopy equivalence** (in fact, literally an isomorphism of
chain complexes: the trivial homotopies below witness that the two composites are *equal* to
the respective identity chain maps, not merely homotopic to them). -/
noncomputable def dualPointsBaseChangeHomotopyEquivalence :
    HomotopyEquivalence (dualPoints (E.baseChange R') B) (dualPoints E B) where
  hom := dualPointsBaseChangeHom E B
  inv := dualPointsBaseChangeInv E B
  unit :=
    { homotopy := 0
      degreeZero := fun l => by
        simp only [add_zero, LinearMap.zero_apply]
        exact (dualBaseChangeLinearEquiv B E.degreeOne).symm_apply_apply l
      degreeOne := fun l => by
        rw [LinearMap.zero_apply, map_zero, add_zero]
        exact (dualBaseChangeLinearEquiv B E.degreeZero).symm_apply_apply l }
  counit :=
    { homotopy := 0
      degreeZero := fun g => by
        simp only [add_zero, LinearMap.zero_apply]
        exact ((dualBaseChangeLinearEquiv B E.degreeOne).apply_symm_apply g).symm
      degreeOne := fun g => by
        rw [LinearMap.zero_apply, map_zero, add_zero]
        exact ((dualBaseChangeLinearEquiv B E.degreeZero).apply_symm_apply g).symm }

/-- **Goal 1: the Picard groupoid of the `B`-points of the dual of a base-changed two-term
complex is equivalent (in fact, isomorphic) to the Picard groupoid of the `B`-points of the dual
of the original complex.**  Here `R'` is an arbitrary `R`-algebra, and `B` is any algebra over
both `R'` and `R` compatibly (`IsScalarTower R R' B`). -/
noncomputable def dualPointsBaseChangeEquiv :
    (dualPoints (E.baseChange R') B).quotient ≌ (dualPoints E B).quotient :=
  (dualPointsBaseChangeHomotopyEquivalence E B).quotientEquivalence

end ChainMap

section Naturality

variable (E : LinearTwoTermComplex R) (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B]
  [IsScalarTower R R' B] (B' : Type u) [CommRing B'] [Algebra R' B'] [Algebra R B']
  [IsScalarTower R R' B']

/-- Auxiliary manifest-typed form of the naturality square on morphisms; see
`dualPointsBaseChangeInv_comm_aux` for why the detour through manifest types (rather than the
opaque `PicardCriteria.dualPoints`) is needed for `rfl` to apply here. -/
theorem dualPointsBaseChangeHom_naturality_aux (φ : B →ₐ[R'] B')
    (l : R' ⊗[R] E.degreeOne →ₗ[R'] B) :
    dualBaseChangeLinearEquiv B' E.degreeOne (φ.toLinearMap ∘ₗ l) =
      (AlgHom.restrictScalars R φ).toLinearMap ∘ₗ dualBaseChangeLinearEquiv B E.degreeOne l := by
  apply LinearMap.ext
  intro z
  rfl

/-- **Goal 2: naturality of the comparison in the test algebra.**  Reindexing the Picard
groupoid of the `B`-points of the dual of `E.baseChange R'` along an `R'`-algebra map
`φ : B ⟶ B'` and then comparing with `E` is the same functor as comparing with `E` first and
then reindexing along the underlying `R`-algebra map `φ.restrictScalars R`. -/
theorem dualPointsBaseChangeHom_naturality (φ : B →ₐ[R'] B') :
    dualPointsMap (E.baseChange R') B B' φ ⋙ (dualPointsBaseChangeHom E B').quotientFunctor =
      (dualPointsBaseChangeHom E B).quotientFunctor ⋙
        dualPointsMap E B B' (φ.restrictScalars R) := by
  refine CategoryTheory.Functor.ext (fun x => quotient_ext ?_) fun x y a => ?_
  · apply LinearMap.ext
    intro z
    rfl
  · apply TwoTermQuotient.Hom.ext
    simp only [TwoTermQuotient.comp_val, eqToHom_val, Functor.comp_map,
      Hom.quotientFunctor_map_val, dualPointsMap_map_val, zero_add]
    change dualBaseChangeLinearEquiv B' E.degreeOne (φ.toLinearMap ∘ₗ a.val) =
      (AlgHom.restrictScalars R φ).toLinearMap ∘ₗ dualBaseChangeLinearEquiv B E.degreeOne a.val
        + 0
    rw [add_zero]
    exact dualPointsBaseChangeHom_naturality_aux E B B' φ a.val

end Naturality

end PicardCriteria

namespace NormalSheafPicard

namespace AffineIntrinsicNormalSheaf

open PicardCriteria LinearTwoTermComplex ConeQuotient

variable {k : Type u} [CommRing k] {R : Type u} [CommRing R] [Algebra k R] (I : Ideal R)
  {k' : Type u} [CommRing k'] [Algebra k k']
  {R' : Type u} [CommRing R'] [Algebra k' R'] [Algebra R R'] [Algebra k R']
  [IsScalarTower k R R'] [IsScalarTower k k' R'] (J : Ideal R')
  [Algebra (R ⧸ I) (R' ⧸ J)]
  (B : Type u) [CommRing B] [Algebra (R' ⧸ J) B] [Algebra (R ⧸ I) B]
  [IsScalarTower (R ⧸ I) (R' ⧸ J) B]

/-- **Goal 3 (application): the affine intrinsic normal sheaf is invariant under base change of
the presentation, given the comparison of conormal complexes.**

Let `k → k'` be an algebra map (e.g. a field extension), let `R` be a `k`-algebra with ideal `I`
presenting an affine local model `U ↪ M`, and let `R'` be an `R`- and `k'`-algebra (compatibly),
with ideal `J` extending `I` in the sense that there is a induced algebra structure of
`R' ⧸ J` on `R ⧸ I`-algebras (`[Algebra (R ⧸ I) (R' ⧸ J)]`, discharged by an
`IsScalarTower (R ⧸ I) (R' ⧸ J) B` for every test algebra `B`); the intended case is
`R' = k' ⊗[k] R` and `J = I.map (algebraMap R R')`, i.e. `U' = U ×_k k'`.

Given an explicit chain-homotopy equivalence `compare` identifying the degreewise base change
`(conormalComplex k R I).baseChange (R' ⧸ J)` with `conormalComplex k' R' J` — the flat base
change of the presentation cotangent complex, which is *not* proved in this repository at the
time of writing (it needs `Ideal.CotangentBaseChange` together with a base-change comparison
for `Ω[R⁄k]`, i.e. the gap recorded in `VirtualFundamentalClass/NormalConeBaseChange.lean`'s
docstring) — the affine intrinsic normal sheaf of the base-changed presentation is equivalent,
over every test algebra `B`, to the affine intrinsic normal sheaf of the original presentation:
`[N_{U'/M'}/T_{M'}|_{U'}](B) ≌ [N_{U/M}/T_M|_U](B)`. This combines
`PicardCriteria.dualPointsBaseChangeEquiv` (goal 1) with
`PicardCriteria.dualQuotientEquivalence` (dualising a chain homotopy equivalence, already in
`Cones/CriteriaBundle.lean`) and `normalSheafQuotientEquivDualPoints` on both sides. -/
noncomputable def normalSheafBaseChangeEquiv
    (compare : HomotopyEquivalence ((conormalComplex k R I).baseChange (R' ⧸ J))
      (conormalComplex k' R' J)) :
    QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k' R' J) B ≌
      QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B :=
  (normalSheafQuotientEquivDualPoints k' R' J B).trans
    ((PicardCriteria.dualQuotientEquivalence B compare).trans
      ((PicardCriteria.dualPointsBaseChangeEquiv (conormalComplex k R I) B).trans
        (normalSheafQuotientEquivDualPoints k R I B).symm))

end AffineIntrinsicNormalSheaf

end NormalSheafPicard

end GromovWitten.AlgebraicGeometry
