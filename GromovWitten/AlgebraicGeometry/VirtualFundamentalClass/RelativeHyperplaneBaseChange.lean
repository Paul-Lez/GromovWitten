/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneReindex

/-!
# The conormal complex of a coordinate-hyperplane base change is a base change (issue #75)

`RelativeVirtualClassBaseChange.lean`, `RelativeHyperplaneObstruction.lean` and
`RelativeHyperplaneReindex.lean` construct, for a relative obstruction datum
`φ : E ⟶ RelativeAbsolute.relConormalComplex I` of `X = Spec (R ⧸ I) → Y = 𝔸^{Option τ'}`
(`R = k[x_σ, y_{Option τ'}]`), the reindexed base-changed datum
`RelativeHyperplaneReindex.reindexHom I φ : E.baseChange (Base J) ⟶
RelativeAbsolute.relConormalComplex J` of `X' = X ×_Y Y' → Y' = 𝔸^{τ'}` along the coordinate
hyperplane `Y' ↪ Y`, `y₀ = 0` (`J = RelativeHyperplaneReindex.reindexIdeal I`, the ideal of `X'`
inside the smaller ambient ring `R' = k[x_σ, y_{τ'}]`), and prove it is a relative obstruction
theory whenever `φ` is (no regularity hypothesis on `y₀` needed), and moreover (this *does* need
`y₀` a non-zero-divisor on `Base I = R ⧸ I`, i.e. `X'` a Cartier divisor in `X`) that `reindexHom`
reflects the obstruction-theory property.

Both files leave open the identity of resolved-cone ideals
`ResolvedCone.ideal (reindexHom I φ) = (ResolvedCone.ideal φ).map (…)` needed for the Gysin
comparison `relativeVirtualClass_hyperplane = i^! [X/Y]^vir` (issue #75's remaining gap): this is
a Tor-independence statement about the associated graded ring `Gr I` in *every* degree
(`RelativeHyperplaneReindex.surjective_grReindexHom`'s docstring), and is not proved here either;
see "What is not proved" below for the precise mathematical obstacle.

## What is proved

The *degree-one* piece of that Tor-independence statement, i.e. the base-change comparison of the
relative conormal complexes themselves (as opposed to the resolved cone, which additionally sees
the associated graded ring `Gr I` in every degree): under the hypothesis that `y₀` is a
non-zero-divisor on `Base I` (`hreg`), the comparison chain map
`reindexComparisonHom I := RelativeHyperplaneReindex.reindexHom I (LinearTwoTermComplex.Hom.id
(RelativeAbsolute.relConormalComplex I))`,
a chain map `(RelativeAbsolute.relConormalComplex I).baseChange (Base J) ⟶
RelativeAbsolute.relConormalComplex J`,
is **bijective in both degrees** (`bijective_reindexComparisonHom_degreeZero`,
`bijective_reindexComparisonHom_degreeOne`), hence a quasi-isomorphism
(`isQuasiIsomorphism_reindexComparisonHom`). Geometrically: the relative conormal module `J/J²`
of `X'` inside the smaller ambient space `𝔸^σ × Y'` is *literally* the base change along
`Base I → Base J` of the relative conormal module `I/I²` of `X` inside `𝔸^σ × Y`, and likewise for
the free `σ`-direction term; this is the flat/Tor-independent behaviour of the conormal complex
under the regular embedding `Y' ↪ Y`, i.e. the `n = 1` case of the associated-graded-ring
Tor-independence needed for the full resolved-cone comparison.

The proof is a specialisation of `RelativeHyperplaneReindex.reindexHom` to `φ = id`
(`reindexComparisonHom I` unfolds, through the `abbrev`
`RelativeHyperplaneObstruction.hyperplaneComparisonHom`, to the reindexing of the *comparison*
chain map, not of a general obstruction datum), composed with the already-proven bijectivity of
each of its three constituent pieces
(`RelativeHyperplaneReindex.tensorReindexEquiv`,
`RelativeHyperplaneObstruction.injective_hyperplaneComparison_degreeZero` /
`surjective_hyperplaneComparison_degreeZero` / `bijective_hyperplaneComparison_degreeOne`,
`RelativeHyperplaneReindex.hyperplaneCotangentReindexEquiv` /
`RelativeHyperplaneReindex.sigmaReindexEquiv`).

Finally, `reindexHom_eq_comp` shows that `reindexComparisonHom I` really is *the* comparison map
for a general datum `φ`, not just for `φ = id`: `reindexHom I φ` (the reindexed hyperplane base
change of an arbitrary `φ`) equals `reindexComparisonHom I` composed with the plain degreewise
base change `φ.baseChange (Base J)`, mirroring
`RelativeHyperplaneObstruction.hyperplaneHom_eq_comp`.  Combined with the bijectivity above,
`isObstructionTheory_reindexHom_iff_baseChange_reindex` gives a second, direct proof (not going
through the semilinear-isomorphism trick of
`RelativeHyperplaneReindex.isObstructionTheory_reindexHom_iff_baseChange`) that `reindexHom I φ` is
a relative obstruction theory for `X'/Y'` iff `φ.baseChange (Base J)` is, whenever `y₀` is regular.

## What is not proved

The resolved-cone ideal identity itself needs the *same* comparison one degree further up: not
just that `Gr I`'s degree-one piece (`I/I²`) base-changes correctly, but that the whole associated
graded ring `Gr I = ⊕ₙ Iⁿ/Iⁿ⁺¹` does, i.e. that `Iⁿ ∩ I'ⁿ⁺¹ ⊆ Iⁿ⁺¹ + y₀·Iⁿ` for *every* `n`, not
just `n = 1`. Writing out the `n = 1` case elementarily (`I ∩ (y₀) ⊆ I² + y₀I`, which is exactly
`RelativeHyperplaneObstruction.hyperplaneIdeal_sq_le` combined with the regularity hypothesis) and
attempting the same argument for `n = 2` shows that it does *not* close by an elementary induction
on `n` from the `n = 1` case alone: peeling one factor of `y₀` at a time using only
`RelativeHyperplaneObstruction.mem_of_mul_hyperplaneCoord_mem` repeatedly loses exactly one degree
of ideal membership at each step, so the induction needs an independent input at every degree
(equivalently: `y₀` being a non-zero-divisor on `Base I` says `y₀` is a non-zero-divisor on the
*degree-zero* piece `Gr I₀ = Base I` of the associated graded ring, but does not by itself force
`y₀` to be a non-zero-divisor on the *whole* associated graded ring `Gr I`, which is the
classically stronger condition that actually controls `Ass (R ⧸ Iⁿ)` for every `n`). This is a
genuine additional hypothesis in general commutative algebra (related to `y₀` being what is
sometimes called a *superficial* element for `I`), not a formal consequence of `hreg`, and no
argument for it (nor a counterexample) is established here; it is exactly the content flagged as
unproved in `RelativeHyperplaneReindex.lean`'s module docstring ("What remains open").
Consequently `relConeCycle_hyperplaneHom` and the Gysin identification
`relativeVirtualClass (reindexHom I φ) = i^! (relativeVirtualClass φ)` remain out of reach.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneBaseChange

open LinearTwoTermComplex PicardCriteria
open RelativeVirtualClassBaseChange
open GromovWitten.AlgebraicGeometry.NormalConeAction (Base)
open RelativeHyperplaneReindex

variable {k : Type u} [CommRing k] {σ τ' : Type u} [Fintype σ]
variable (I : Ideal (MvPolynomial (σ ⊕ Option τ') k))

/-- **The comparison chain map of the reindexed hyperplane base change**: the special case
`φ = id` of `RelativeHyperplaneReindex.reindexHom`, a chain map from the base change of the
relative conormal complex of `X/Y` to the relative conormal complex of `X'/Y'`
(`J = reindexIdeal I`). -/
noncomputable abbrev reindexComparisonHom :
    Hom ((RelativeAbsolute.relConormalComplex I).baseChange (Base (reindexIdeal I)))
      (RelativeAbsolute.relConormalComplex (reindexIdeal I)) :=
  reindexHom I (Hom.id (RelativeAbsolute.relConormalComplex I))

/-- **The comparison chain map is bijective in degree one**, unconditionally: the base change of
the free module `σ → Base I` is the free module `σ → Base J`. -/
theorem bijective_reindexComparisonHom_degreeOne :
    Function.Bijective (reindexComparisonHom I).degreeOne := by
  have heq : ((reindexComparisonHom I).degreeOne :
      Base (reindexIdeal I) ⊗[Base I] (σ → Base I) → σ → Base (reindexIdeal I)) =
      (sigmaReindexEquiv I : (σ → Base (hyperplaneIdeal I)) → σ → Base (reindexIdeal I)) ∘
        (RelativeHyperplaneObstruction.hyperplaneComparisonHom I).degreeOne ∘
        (tensorReindexEquiv I (σ → Base I)).symm := by
    funext z
    exact reindexHom_degreeOne_apply I (Hom.id (RelativeAbsolute.relConormalComplex I)) z
  rw [heq]
  exact (Function.Bijective.comp (sigmaReindexEquiv I).bijective
    (Function.Bijective.comp
      (RelativeHyperplaneObstruction.bijective_hyperplaneComparison_degreeOne I)
      (tensorReindexEquiv I (σ → Base I)).symm.bijective))

/-- **The comparison chain map is bijective in degree zero**, when `y₀` is a non-zero-divisor on
`Base I`: the base change of the conormal module `I/I²` is the conormal module `J/J²`. -/
theorem bijective_reindexComparisonHom_degreeZero
    (hreg : IsSMulRegular (Base I)
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))) :
    Function.Bijective (reindexComparisonHom I).degreeZero := by
  have heq : ((reindexComparisonHom I).degreeZero :
      Base (reindexIdeal I) ⊗[Base I] I.Cotangent → (reindexIdeal I).Cotangent) =
      (hyperplaneCotangentReindexEquiv I) ∘
        (RelativeHyperplaneObstruction.hyperplaneComparisonHom I).degreeZero ∘
        (tensorReindexEquiv I I.Cotangent).symm := by
    funext z
    exact reindexHom_degreeZero_apply I (Hom.id (RelativeAbsolute.relConormalComplex I)) z
  rw [heq]
  exact (hyperplaneCotangentReindexEquiv I).bijective.comp
    (Function.Bijective.comp
      ⟨RelativeHyperplaneObstruction.injective_hyperplaneComparison_degreeZero I hreg,
        RelativeHyperplaneObstruction.surjective_hyperplaneComparison_degreeZero I⟩
      (tensorReindexEquiv I I.Cotangent).symm.bijective)

/-- **The comparison chain map is a quasi-isomorphism**, when `y₀` is a non-zero-divisor on
`Base I`: the relative conormal complex of `X'/Y'` is the base change of the relative conormal
complex of `X/Y`, bijectively in both degrees, hence in particular as a quasi-isomorphism of
two-term complexes. -/
theorem isQuasiIsomorphism_reindexComparisonHom
    (hreg : IsSMulRegular (Base I)
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))) :
    (reindexComparisonHom I).IsQuasiIsomorphism :=
  RelativeHyperplaneObstruction.isQuasiIsomorphism_of_bijective
    (bijective_reindexComparisonHom_degreeZero I hreg) (bijective_reindexComparisonHom_degreeOne I)

/-- **`reindexHom I φ` factors through `reindexComparisonHom I`**: for a general relative
obstruction datum `φ`, the reindexed hyperplane base change is literally the plain degreewise
base change of `φ` followed by the (bijective, under `hreg`) comparison chain map. This exhibits
`reindexComparisonHom I` as *the* comparison map between the reindexed hyperplane base change and
the naive base change, matching `RelativeHyperplaneObstruction.hyperplaneHom_eq_comp`. -/
theorem reindexHom_eq_comp {E : LinearTwoTermComplex (Base I)}
    (φ : Hom E (RelativeAbsolute.relConormalComplex I)) :
    reindexHom I φ =
      (reindexComparisonHom I).comp (φ.baseChange (Base (reindexIdeal I))) := by
  refine VirtualClass.BaseChangeObstruction.hom_ext (LinearMap.ext fun z => ?_)
    (LinearMap.ext fun z => ?_)
  · have hL := reindexHom_degreeZero_apply I φ z
    have hR := reindexHom_degreeZero_apply I (Hom.id (RelativeAbsolute.relConormalComplex I))
      ((φ.baseChange (Base (reindexIdeal I))).degreeZero z)
    have hnat := tensorReindexEquiv_symm_baseChange I E.degreeZero φ.degreeZero z
    change (reindexHom I φ).degreeZero z =
      (reindexComparisonHom I).degreeZero ((φ.baseChange (Base (reindexIdeal I))).degreeZero z)
    rw [hL, hR, RelativeHyperplaneObstruction.hyperplaneHom_eq_comp]
    change hyperplaneCotangentReindexEquiv I
        ((RelativeHyperplaneObstruction.hyperplaneComparisonHom I).degreeZero
          ((φ.baseChange (Base (hyperplaneIdeal I))).degreeZero
            ((tensorReindexEquiv I E.degreeZero).symm z))) =
      hyperplaneCotangentReindexEquiv I
        ((RelativeHyperplaneObstruction.hyperplaneComparisonHom I).degreeZero
          ((tensorReindexEquiv I I.Cotangent).symm
            ((φ.baseChange (Base (reindexIdeal I))).degreeZero z)))
    congr 1
    congr 1
    exact hnat.symm
  · have hL := reindexHom_degreeOne_apply I φ z
    have hR := reindexHom_degreeOne_apply I (Hom.id (RelativeAbsolute.relConormalComplex I))
      ((φ.baseChange (Base (reindexIdeal I))).degreeOne z)
    have hnat := tensorReindexEquiv_symm_baseChange I E.degreeOne φ.degreeOne z
    change (reindexHom I φ).degreeOne z =
      (reindexComparisonHom I).degreeOne ((φ.baseChange (Base (reindexIdeal I))).degreeOne z)
    rw [hL, hR, RelativeHyperplaneObstruction.hyperplaneHom_eq_comp]
    change sigmaReindexEquiv I
        ((RelativeHyperplaneObstruction.hyperplaneComparisonHom I).degreeOne
          ((φ.baseChange (Base (hyperplaneIdeal I))).degreeOne
            ((tensorReindexEquiv I E.degreeOne).symm z))) =
      sigmaReindexEquiv I
        ((RelativeHyperplaneObstruction.hyperplaneComparisonHom I).degreeOne
          ((tensorReindexEquiv I (σ → Base I)).symm
            ((φ.baseChange (Base (reindexIdeal I))).degreeOne z)))
    congr 1
    congr 1
    exact hnat.symm

/-- **A second, direct proof that `reindexHom` reflects the obstruction-theory property**, not
going through the semilinear-isomorphism argument of
`RelativeHyperplaneReindex.isObstructionTheory_reindexHom_iff_baseChange`: compose
`reindexHom_eq_comp` with the two-out-of-three property of obstruction theories against the
quasi-isomorphism `reindexComparisonHom I`. -/
theorem isObstructionTheory_reindexHom_iff_baseChange_reindex
    (hreg : IsSMulRegular (Base I)
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ'))))
    {E : LinearTwoTermComplex (Base I)}
    (φ : Hom E (RelativeAbsolute.relConormalComplex I)) :
    IsObstructionTheory (reindexHom I φ) ↔
      IsObstructionTheory (φ.baseChange (Base (reindexIdeal I))) := by
  rw [reindexHom_eq_comp]
  refine ⟨fun h => VirtualClass.BaseChangeObstruction.isObstructionTheory_of_comp_quasiIso
    (isQuasiIsomorphism_reindexComparisonHom I hreg) h, fun h =>
    RelativeHyperplaneObstruction.isObstructionTheory_comp
      (RelativeHyperplaneObstruction.isObstructionTheory_of_surjective_of_bijective
        (bijective_reindexComparisonHom_degreeZero I hreg).2
        (bijective_reindexComparisonHom_degreeOne I)) h⟩

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneBaseChange
