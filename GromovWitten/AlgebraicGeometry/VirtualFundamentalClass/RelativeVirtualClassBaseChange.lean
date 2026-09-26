/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeAbsolute
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.DegreeOneSummand
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.BaseChangeInvariance
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.BaseChangeObstruction
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.LocalisationCone

/-!
# The relative virtual class and its base change (issue #75)

Behrend–Fantechi §7 attach to a morphism `X → Y` (`Y` smooth) a *relative* virtual fundamental
class `[X/Y]^vir`, prove it agrees with the virtual class of the associated absolute obstruction
theory, and prove two base-change formulas for it: along a smooth morphism `Y' → Y` (in
particular an open immersion) and along a regular embedding `Y' ↪ Y`.  This file assembles the
affine-model pieces of `RelativeAbsolute.lean`, `DegreeOneSummand.lean`,
`BaseChangeInvariance.lean`, `BaseChangeObstruction.lean` and `LocalisationCone.lean` into the
three statements requested by
issue #75, and proves the affine model of the regular-embedding case for the simplest possible
regular embedding: a coordinate hyperplane `Y' = 𝔸^{τ'} ↪ Y = 𝔸^τ` (`τ = Option τ'`).

## Part 1: the headline statements (thin re-exports)

* `relativeVirtualClass_eq_absoluteVirtualClass` (`RelativeAbsolute.virtualClassAt_absHom`):
  the virtual class of the absolute obstruction theory `absHom φ` attached to a relative
  obstruction theory `φ : E ⟶ relConormalComplex I` of `X = Spec(R/I) → Y = 𝔸^τ` is *the*
  relative virtual class `[X/Y]^vir`.
* `virtualDimension_relativeVirtualClass` (`RelativeAbsolute.virtualDimension_absHom`): the
  dimension shift `vdim(absHom φ) = vdim(φ) + dim Y` between the absolute and the relative
  reading.
* `relativeVirtualClass_baseChange_flat`
  (`BaseChangeInvariance.relativeVirtualClassAt_baseChangeHom`): the flat base-change formula
  `[X ×_Y (Y × 𝔸^ρ)]^vir = π^*[X/Y]^vir` for the smooth projection `Y × 𝔸^ρ → Y`.
* `isObstructionTheory_relative_localisation_iff`
  (`BaseChangeObstruction.LocalisationCone.isObstructionTheory_baseChangeHom_iff`): the
  companion statement for an open (flat formally étale, e.g. a localisation) base change
  `Y' → Y`: `φ` is a relative obstruction theory for `X/Y` iff its base change is one for
  `X ×_Y Y' → Y'`.

## Part 2: base change along a coordinate hyperplane

Fix `τ = Option τ'` and let `y₀` be the coordinate function dual to `Sum.inr none`, so that
`Y' = 𝔸^{τ'} ↪ Y = 𝔸^τ` is the hyperplane `y₀ = 0`.  For `I ⊆ R = k[x_σ, y_τ]` put
`I' = I + (y₀)`, so `X' = Spec(R/I') = X ×_Y Y'`.

The relative conormal complex of `X'/Y` (relative to the *unchanged* base `Y`,
`RelativeAbsolute.relConormalComplex I'`) is *not* the relative conormal complex of `X'/Y'`: its
degree-zero term `I'/I'²` is one dimension too big, by exactly the conormal class of `y₀` (for
instance `I = 0` in `R = k[x, y]`, `I' = (y)`: `I'/I'² ≅ k[x] ≠ 0`, while the base change of `E`'s
degree-zero term along `Base I → Base I'` is `0`, so the naive comparison map could never even
be an obstruction theory).  The correct relative-over-`Y'` datum is obtained by quotienting that
class out:
`hyperplaneCotangent I'` is the module `I'/I'² ⧸ ⟨[y₀]⟩`, and
`hyperplaneConormalComplex I'` is the two-term complex `[hyperplaneCotangent I' → (σ → Base I')]`
(the differential descends because `y₀`'s partial derivatives in the `σ`-directions vanish,
`sigmaPart_hyperplaneCoord`).  `hyperplaneHom φ` is the induced chain map
`E.baseChange (Base I') ⟶ hyperplaneConormalComplex I'`.

**What is proved**: the construction of `hyperplaneConormalComplex I'` (with the differential
well-defined on the quotient, `sigmaPart_hyperplaneCoord`) and of the chain map `hyperplaneHom φ`
itself, degreewise (`hyperplaneBaseChangeZero`, `hyperplaneBaseChangeOne`) *and* the naturality
square `comm` making it a genuine morphism of two-term complexes — the substantial content is
the naturality lemma `sigmaPart_conormalMap_hyperplaneCotangentMapAux` identifying the two ways
of comparing the relative conormal differentials of `I` and of `I'`.  **What is not proved**:
the obstruction-theory transfer (`IsObstructionTheory φ → IsObstructionTheory (hyperplaneHom φ)`
under the hypothesis that `y₀` is a non-zero-divisor on `Base I`) and the resolved-cone ideal
identity `ResolvedCone.ideal (hyperplaneHom φ) = (ResolvedCone.ideal φ).map (…)`.  Both need a
genuine Tor-independence argument (that multiplication by `y₀` stays injective on the finite
free terms of `E`, hence the *non-flat* quotient `Base I → Base I'` still computes the
kernel/cokernel of `E`'s differential correctly) which is not a repackaging of existing lemmas
in this repository; see the docstring of `hyperplaneHom` for the precise statement of the gap.
The final Gysin-map identification `relativeVirtualClassAt (hyperplaneHom φ) = i^! (…)` is
therefore also out of reach here and is not attempted, per the task's own fallback clause.

None of this is Behrend–Fantechi §7's construction at DM-stack level: it is the affine model of
`X = Spec(R/I) ⊆ 𝔸^σ × Y` only, exactly as in `RelativeAbsolute.lean`.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeVirtualClassBaseChange

/-! ## Part 1: the headline statements of issue #75 -/

/-- **The relative virtual class equals the absolute virtual class of the associated absolute
obstruction theory `absHom φ`.**  This is the affine model of Behrend–Fantechi's comparison
between the relative virtual class `[X/Y]^vir` of a relative obstruction theory `φ` for
`X = Spec(R/I) → Y = 𝔸^τ` and the (ordinary) virtual class of the absolute datum `absHom φ`
attached to it by `RelativeAbsolute.absHom`. -/
alias relativeVirtualClass_eq_absoluteVirtualClass := RelativeAbsolute.virtualClassAt_absHom

/-- **The dimension shift between the relative and the absolute reading**: the virtual dimension
of the absolute obstruction theory `absHom φ` exceeds the virtual dimension of the relative
datum `φ` by `dim Y = #τ`. -/
alias virtualDimension_relativeVirtualClass := RelativeAbsolute.virtualDimension_absHom

/-- **Flat base change of the relative virtual class**, `[X ×_Y (Y × 𝔸^ρ)]^vir = π^*[X/Y]^vir`:
Behrend–Fantechi's Proposition 7.2 for the smooth projection `Y × 𝔸^ρ → Y`, read relatively (the
left-hand side is `DegreeOneSummand.relativeVirtualClassAt` of the base-changed datum, in
relative dimension `Nat.card ρ`, and the right-hand side is the flat pullback, along
`X → X ×_Y (Y × 𝔸^ρ) → X` composed appropriately, of the relative virtual class of `φ`). -/
alias relativeVirtualClass_baseChange_flat :=
  BaseChangeInvariance.relativeVirtualClassAt_baseChangeHom

open GromovWitten.AlgebraicGeometry.VirtualClass.BaseChangeObstruction

/-- **Localisation (open, flat formally étale) base change of the relative obstruction-theory
property**: for `Y' → Y` flat formally étale (e.g. a localisation `Y' = Spec (Localization.Away
f)`) and faithfully flat, a relative datum `φ` for `X/Y` is an obstruction theory iff its base
change to `X ×_Y Y' → Y'` is one.  Together with `relativeVirtualClass_eq_absoluteVirtualClass`
this identifies `[X/Y]^vir` with `[X ×_Y Y'/Y']^vir` under the flat pullback along `Y' → Y`
whenever both sides are defined. -/
alias isObstructionTheory_relative_localisation_iff :=
  LocalisationCone.isObstructionTheory_baseChangeHom_iff

/-! ## Part 2: base change along a coordinate hyperplane -/

open GromovWitten.AlgebraicGeometry.NormalConeAction (Base)

variable {k : Type u} [CommRing k] {σ τ' : Type u} [Fintype σ] [Fintype τ']

/-- The coordinate function `y₀` dual to `Sum.inr none`: the equation cutting out the
coordinate hyperplane `Y' = 𝔸^{τ'} ↪ Y = 𝔸^{Option τ'}`. -/
noncomputable abbrev hyperplaneCoord : MvPolynomial (σ ⊕ Option τ') k :=
  MvPolynomial.X (Sum.inr none)

variable (I : Ideal (MvPolynomial (σ ⊕ Option τ') k))

/-- **The ideal `I' = I + (y₀)`** of `X' = X ×_Y Y'` inside the same ambient ring as `X`: the
affine model of the fibre product of the closed subscheme `X = Spec (R/I)` with the coordinate
hyperplane `Y' ↪ Y`. -/
noncomputable abbrev hyperplaneIdeal : Ideal (MvPolynomial (σ ⊕ Option τ') k) :=
  I ⊔ Ideal.span {hyperplaneCoord (k := k) (σ := σ) (τ' := τ')}

omit [Fintype σ] [Fintype τ'] in
/-- `I ≤ I'`. -/
theorem le_hyperplaneIdeal : I ≤ hyperplaneIdeal I := le_sup_left

omit [Fintype σ] [Fintype τ'] in
/-- `y₀` lies in `I'`. -/
theorem hyperplaneCoord_mem : hyperplaneCoord (k := k) (σ := σ) (τ' := τ') ∈ hyperplaneIdeal I :=
  Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

omit [Fintype σ] [Fintype τ'] in
/-- **The `σ`-derivatives of `y₀` all vanish**: `y₀` is a `τ`-coordinate, independent of every
`σ`-coordinate, so its conormal class dies under the relative (`σ`-only) conormal map. -/
theorem sigmaPart_hyperplaneCoord :
    RelativeAbsolute.sigmaPart (hyperplaneIdeal I)
        (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ Option τ') k) (hyperplaneIdeal I)
          (Ideal.toCotangent (hyperplaneIdeal I) ⟨hyperplaneCoord, hyperplaneCoord_mem I⟩)) =
      0 := by
  classical
  funext s
  rw [RelativeAbsolute.sigmaPart_conormalMap_toCotangent]
  simp [hyperplaneCoord, MvPolynomial.pderiv_X]

/-- **The relative conormal module of `X'/Y'`**: the quotient of `I'/I'²` (the conormal module
of `X'` inside the *unchanged* ambient space `𝔸^σ × Y`) by the conormal class of `y₀`.  This is
the affine model of the conormal module of `X'` inside the *smaller* ambient space `𝔸^σ × Y'`
(the class of `y₀` accounts for exactly the one ambient dimension that is lost in passing from
`Y` to the hyperplane `Y'`). -/
noncomputable abbrev hyperplaneCotangent : Type u :=
  (hyperplaneIdeal I).Cotangent ⧸
    (Base (hyperplaneIdeal I) ∙
      Ideal.toCotangent (hyperplaneIdeal I) ⟨hyperplaneCoord, hyperplaneCoord_mem I⟩)

/-- **The relative conormal differential of `X'/Y'`**, `hyperplaneCotangent I' → (σ → Base I')`:
the descent of the relative conormal differential of `X'/Y` to the quotient
`hyperplaneCotangent I`, using that `y₀`'s class dies (`sigmaPart_hyperplaneCoord`). -/
noncomputable def hyperplaneDifferential :
    hyperplaneCotangent I →ₗ[Base (hyperplaneIdeal I)] (σ → Base (hyperplaneIdeal I)) :=
  Submodule.liftQSpanSingleton _
    ((RelativeAbsolute.sigmaPart (hyperplaneIdeal I)).comp
      (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ Option τ') k) (hyperplaneIdeal I)))
    (sigmaPart_hyperplaneCoord I)

omit [Fintype σ] [Fintype τ'] in
@[simp]
theorem hyperplaneDifferential_mk (x : (hyperplaneIdeal I).Cotangent) :
    hyperplaneDifferential I (Submodule.Quotient.mk x) =
      RelativeAbsolute.sigmaPart (hyperplaneIdeal I)
        (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ Option τ') k) (hyperplaneIdeal I) x) :=
  rfl

/-- **The relative conormal complex of `X'/Y'`**, `[hyperplaneCotangent I' → (σ → Base I')]`:
the affine model of the relative cotangent complex `L_{X'/Y'}` of the base-changed scheme
`X' = X ×_Y Y'` over the coordinate hyperplane `Y' = 𝔸^{τ'} ↪ Y = 𝔸^{Option τ'}`. -/
noncomputable abbrev hyperplaneConormalComplex : LinearTwoTermComplex (Base (hyperplaneIdeal I)) :=
  NormalSheafPicard.dualComplexOf (hyperplaneDifferential I)

/-! ### The comparison chain map `hyperplaneHom` -/

/-- **`Base I'` is a `Base I`-algebra**, through the quotient map `Base I → Base I'` induced by
`I ≤ I'`. -/
noncomputable instance algebraHyperplane : Algebra (Base I) (Base (hyperplaneIdeal I)) :=
  RingHom.toAlgebra (Ideal.Quotient.factor (le_hyperplaneIdeal I))

omit [Fintype σ] [Fintype τ'] in
@[simp]
theorem algebraMap_hyperplane_mk (r : MvPolynomial (σ ⊕ Option τ') k) :
    algebraMap (Base I) (Base (hyperplaneIdeal I)) (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (hyperplaneIdeal I) r :=
  rfl

/-- `hyperplaneCotangent I` is a `Base I`-module through `Base I → Base I'`. -/
noncomputable instance moduleHyperplaneCotangent : Module (Base I) (hyperplaneCotangent I) :=
  Module.compHom _ (algebraMap (Base I) (Base (hyperplaneIdeal I)))

omit [Fintype σ] [Fintype τ'] in
theorem mk_smul_hyperplaneCotangent (r : MvPolynomial (σ ⊕ Option τ') k)
    (m : hyperplaneCotangent I) : (Ideal.Quotient.mk I r) • m = r • m :=
  rfl

omit [Fintype σ] [Fintype τ'] in
/-- **The `Base I`- and `Base I'`-actions on `hyperplaneCotangent I` commute.** -/
theorem smul_comm_hyperplaneCotangent (b : Base I) (x : Base (hyperplaneIdeal I))
    (m : hyperplaneCotangent I) : x • b • m = b • x • m := by
  change x • (algebraMap (Base I) (Base (hyperplaneIdeal I)) b) • m =
    (algebraMap (Base I) (Base (hyperplaneIdeal I)) b) • x • m
  rw [← mul_smul, ← mul_smul, mul_comm]

/-- The comparison map `I/I² → I'/I'²`, linear over the *ambient* polynomial ring. -/
noncomputable def hyperplaneCotangentMapAux :
    I.Cotangent →ₗ[MvPolynomial (σ ⊕ Option τ') k] (hyperplaneIdeal I).Cotangent :=
  Ideal.mapCotangent I (hyperplaneIdeal I)
    (AlgHom.id (MvPolynomial (σ ⊕ Option τ') k) (MvPolynomial (σ ⊕ Option τ') k))
    (by rw [Ideal.comap_idₐ]; exact le_hyperplaneIdeal I)

/-- **The comparison map on conormal modules**, `I/I² → hyperplaneCotangent I`, as a
`Base I`-linear map: `Ideal.mapCotangent` composed with the projection onto the quotient
`hyperplaneCotangent I`. -/
noncomputable def hyperplaneCotangentComparison :
    I.Cotangent →ₗ[Base I] hyperplaneCotangent I where
  toFun x := Submodule.Quotient.mk (hyperplaneCotangentMapAux I x)
  map_add' x y := by
    change Submodule.Quotient.mk (hyperplaneCotangentMapAux I (x + y)) =
      Submodule.Quotient.mk (hyperplaneCotangentMapAux I x) +
        Submodule.Quotient.mk (hyperplaneCotangentMapAux I y)
    rw [map_add]; rfl
  map_smul' b x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h : (Ideal.Quotient.mk I r) • x = r • x :=
      IsScalarTower.algebraMap_smul (Base I) r x
    change Submodule.Quotient.mk (hyperplaneCotangentMapAux I ((Ideal.Quotient.mk I r) • x)) =
      (Ideal.Quotient.mk I r) • Submodule.Quotient.mk (hyperplaneCotangentMapAux I x)
    rw [h, map_smul, mk_smul_hyperplaneCotangent]
    rfl

/-- **The comparison map on the `σ`-directions**, `(σ → Base I) → (σ → Base I')`, `Base I`-linear
through the structure map `Base I → Base I'` applied coordinatewise. -/
noncomputable def hyperplaneSigmaMap :
    (σ → Base I) →ₗ[Base I] (σ → Base (hyperplaneIdeal I)) :=
  LinearMap.pi fun s => (Algebra.linearMap (Base I) (Base (hyperplaneIdeal I))).comp
    (LinearMap.proj s)

omit [Fintype σ] [Fintype τ'] in
@[simp]
theorem hyperplaneSigmaMap_apply (f : σ → Base I) (s : σ) :
    hyperplaneSigmaMap I f s = algebraMap (Base I) (Base (hyperplaneIdeal I)) (f s) :=
  rfl

variable {E : LinearTwoTermComplex (Base I)}

/-- The `Base I`-bilinear map underlying the degree-zero component of `hyperplaneHom`. -/
noncomputable def hyperplaneBaseChangeZeroBilin
    (φ : LinearTwoTermComplex.Hom E (RelativeAbsolute.relConormalComplex I)) :
    Base (hyperplaneIdeal I) →ₗ[Base I] E.degreeZero →ₗ[Base I] hyperplaneCotangent I :=
  LinearMap.mk₂ (Base I)
    (fun x e => x • hyperplaneCotangentComparison I (φ.degreeZero e))
    (fun x y e => add_smul x y _)
    (fun b x e => by rw [Algebra.smul_def]; exact mul_smul _ _ _)
    (fun x e e' => by rw [map_add, map_add, smul_add])
    (fun b x e => by rw [map_smul, map_smul]; exact smul_comm_hyperplaneCotangent I b x _)

/-- **The degree-zero component of `hyperplaneHom`**: `Base I' ⊗[Base I] E⁰ → hyperplaneCotangent
I`. -/
noncomputable def hyperplaneBaseChangeZero
    (φ : LinearTwoTermComplex.Hom E (RelativeAbsolute.relConormalComplex I)) :
    Base (hyperplaneIdeal I) ⊗[Base I] E.degreeZero →ₗ[Base (hyperplaneIdeal I)]
      hyperplaneCotangent I where
  toFun := TensorProduct.lift (hyperplaneBaseChangeZeroBilin I φ)
  map_add' x y := map_add _ x y
  map_smul' x z := by
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, RingHom.id_apply, smul_zero]
    | tmul y e =>
      rw [TensorProduct.smul_tmul' x y e, TensorProduct.lift.tmul, TensorProduct.lift.tmul,
        RingHom.id_apply]
      exact mul_smul x y _
    | add z w hz hw =>
      rw [smul_add, map_add, map_add, hz, hw, RingHom.id_apply, smul_add]

/-- **`Base I' ⊗[Base I] (σ → Base I) ≃ (σ → Base I')`**: the base change of the free module
`σ → Base I` is again the free module on `σ`, over `Base I'` — a special case of
`Algebra.TensorProduct.piScalarRight`. -/
noncomputable def hyperplaneSigmaBaseChangeEquiv :
    Base (hyperplaneIdeal I) ⊗[Base I] (σ → Base I) ≃ₗ[Base (hyperplaneIdeal I)]
      (σ → Base (hyperplaneIdeal I)) :=
  letI : DecidableEq σ := Classical.decEq σ
  (Algebra.TensorProduct.piScalarRight (Base I) (Base (hyperplaneIdeal I))
    (Base (hyperplaneIdeal I)) σ).toLinearEquiv

omit [Fintype τ'] in
@[simp]
theorem hyperplaneSigmaBaseChangeEquiv_tmul (b : Base (hyperplaneIdeal I)) (f : σ → Base I) :
    hyperplaneSigmaBaseChangeEquiv I (b ⊗ₜ f) = fun s => f s • b :=
  rfl

/-- **The degree-one component of `hyperplaneHom`**: `Base I' ⊗[Base I] E¹ → (σ → Base I')`, the
base change of `φ`'s degree-one component along `hyperplaneSigmaBaseChangeEquiv`. -/
noncomputable def hyperplaneBaseChangeOne
    (φ : LinearTwoTermComplex.Hom E (RelativeAbsolute.relConormalComplex I)) :
    Base (hyperplaneIdeal I) ⊗[Base I] E.degreeOne →ₗ[Base (hyperplaneIdeal I)]
      (σ → Base (hyperplaneIdeal I)) :=
  (hyperplaneSigmaBaseChangeEquiv I).toLinearMap.comp
    (LinearMap.baseChange (Base (hyperplaneIdeal I)) φ.degreeOne)

omit [Fintype σ] [Fintype τ'] in
/-- **Naturality of `hyperplaneCotangentMapAux` against the relative (`σ`-only) conormal map**:
the comparison map `I/I² → I'/I'²` intertwines the relative conormal differential of `I` with
that of `I'`, through `hyperplaneSigmaMap`. -/
theorem sigmaPart_conormalMap_hyperplaneCotangentMapAux (x : I.Cotangent) :
    RelativeAbsolute.sigmaPart (hyperplaneIdeal I) (AffineNormalCone.conormalMap k
        (MvPolynomial (σ ⊕ Option τ') k) (hyperplaneIdeal I) (hyperplaneCotangentMapAux I x)) =
      hyperplaneSigmaMap I (RelativeAbsolute.sigmaPart I (AffineNormalCone.conormalMap k
        (MvPolynomial (σ ⊕ Option τ') k) I x)) := by
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective I x
  funext s
  rw [hyperplaneCotangentMapAux, Ideal.mapCotangent_toCotangent,
    RelativeAbsolute.sigmaPart_conormalMap_toCotangent, hyperplaneSigmaMap_apply,
    RelativeAbsolute.sigmaPart_conormalMap_toCotangent, algebraMap_hyperplane_mk]
  simp

/-- **`hyperplaneHom φ`: the relative obstruction datum of `X'/Y'` attached to a relative
obstruction datum `φ` of `X/Y`.**  It is obtained from `φ` by base change along the quotient map
`Base I → Base I' = Base I ⧸ (y₀)` (degree zero landing in `hyperplaneCotangent I`, the conormal
module of `X'` inside `𝔸^σ × Y'`, rather than the naive `I'/I'²`; degree one unaffected, only
its ambient bookkeeping changing along `hyperplaneSigmaBaseChangeEquiv`). -/
noncomputable def hyperplaneHom
    (φ : LinearTwoTermComplex.Hom E (RelativeAbsolute.relConormalComplex I)) :
    LinearTwoTermComplex.Hom (E.baseChange (Base (hyperplaneIdeal I)))
      (hyperplaneConormalComplex I) where
  degreeZero := hyperplaneBaseChangeZero I φ
  degreeOne := hyperplaneBaseChangeOne I φ
  comm x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b e =>
      change hyperplaneBaseChangeOne I φ (LinearMap.baseChange _ E.differential (b ⊗ₜ e)) =
        hyperplaneDifferential I (hyperplaneBaseChangeZero I φ (b ⊗ₜ e))
      have hφ := φ.comm e
      simp only [LinearMap.comp_apply] at hφ
      have hZero : hyperplaneBaseChangeZero I φ (b ⊗ₜ[Base I] e) =
          Submodule.Quotient.mk (b • hyperplaneCotangentMapAux I (φ.degreeZero e)) := by
        change TensorProduct.lift (hyperplaneBaseChangeZeroBilin I φ) (b ⊗ₜ[Base I] e) =
          Submodule.Quotient.mk (b • hyperplaneCotangentMapAux I (φ.degreeZero e))
        rw [TensorProduct.lift.tmul, hyperplaneBaseChangeZeroBilin, LinearMap.mk₂_apply,
          hyperplaneCotangentComparison]
        rfl
      rw [LinearMap.baseChange_tmul, hyperplaneBaseChangeOne, LinearMap.comp_apply,
        LinearMap.baseChange_tmul, hφ, hZero, hyperplaneDifferential_mk, map_smul, map_smul,
        sigmaPart_conormalMap_hyperplaneCotangentMapAux]
      funext s
      simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp [map_add, hx, hy]

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeVirtualClassBaseChange
