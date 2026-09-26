/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeVirtualClassBaseChange

/-!
# The obstruction-theory condition transfers along a coordinate hyperplane (issue #75)

`RelativeVirtualClassBaseChange.lean` constructs, for a relative obstruction datum
`φ : E ⟶ relConormalComplex I` of `X = Spec (R ⧸ I) → Y = 𝔸^{Option τ'}` with
`R = k[x_σ, y_{Option τ'}]`, the base-changed datum
`hyperplaneHom φ : E.baseChange (Base I') ⟶ hyperplaneConormalComplex I` of
`X' = X ×_Y Y' → Y' = 𝔸^{τ'}` along the coordinate hyperplane `Y' ↪ Y`, `y₀ = 0`, where
`I' = hyperplaneIdeal I = I + (y₀)` and `hyperplaneCotangent I = (I'/I'²) ⧸ ⟨[y₀]⟩` is the
relative conormal module of `X'` inside `𝔸^σ × Y'`.  This file proves that `hyperplaneHom φ` is a
relative obstruction theory for `X'/Y'` as soon as `φ` is one for `X/Y` — the affine model of the
Behrend–Fantechi base-change statement for a regular embedding `Y' ↪ Y`, in the simplest case of a
coordinate hyperplane.

## Main results

* `isObstructionTheory_comp`: obstruction theories compose (`H⁰` of a composite is a composite of
  bijections, `H⁻¹` of a composite is a composite of surjections).
* `isObstructionTheory_of_surjective_of_bijective`: a chain map of two-term complexes which is
  surjective in degree zero and bijective in degree one is an obstruction theory; if it is
  bijective in both degrees it is even a quasi-isomorphism (`isQuasiIsomorphism_of_bijective`).
* `hyperplaneComparisonHom I`, the `φ = id` case of `hyperplaneHom`, a chain map
  `(relConormalComplex I).baseChange (Base I') ⟶ hyperplaneConormalComplex I`, and
  `hyperplaneHom_eq_comp`: `hyperplaneHom φ` is the composite of the degreewise base change of `φ`
  along `Base I → Base I'` with `hyperplaneComparisonHom I`.
* `surjective_hyperplaneComparison_degreeZero` and `bijective_hyperplaneComparison_degreeOne`:
  the comparison map is surjective in degree zero — modulo the conormal class of `y₀`, every
  conormal class of `I' = I + (y₀)` comes from `I` — and bijective in degree one, because the base
  change of the free module `σ → Base I` is the free module `σ → Base I'`.  Hence
  `isObstructionTheory_hyperplaneComparisonHom`.
* **`isObstructionTheory_hyperplaneHom`**: if `φ` is a relative obstruction theory for `X/Y` then
  `hyperplaneHom φ` is a relative obstruction theory for `X'/Y'`.  *No regularity hypothesis on
  `y₀` is needed*: the degreewise base change of an obstruction theory along an arbitrary algebra
  map is an obstruction theory (`PicardCriteria.IsObstructionTheory.baseChange`, right exactness
  of the tensor product), the comparison map is one by the previous item, and obstruction theories
  compose.
* Under the regularity hypothesis `IsSMulRegular (Base I) [y₀]` (i.e. `y₀` is a non-zero-divisor
  on `R ⧸ I`, so that `X'` is a Cartier divisor in `X`) the comparison map is in addition
  *injective* in degree zero (`injective_hyperplaneComparison_degreeZero`), hence a
  quasi-isomorphism (`isQuasiIsomorphism_hyperplaneComparisonHom`), and
  `hyperplaneCotangentEquiv` is the resulting identification
  `Base I' ⊗[Base I] I/I² ≃ hyperplaneCotangent I`
  — the Tor-independence splitting `I'/I'² ≅ (I/I² ⊗ Base I') ⊕ (y₀)/(y₀)²` of the conormal
  module of the hyperplane section.  It follows that the hyperplane base change *reflects* the
  obstruction-theory property: `isObstructionTheory_hyperplaneHom_iff`.

## The regular-embedding input

The algebraic heart of the last two items is the identity `I ∩ (y₀) = y₀ · I`, equivalently
`Tor₁(R/I, R/(y₀)) = 0`.  It enters as
`exists_smul_of_hyperplaneCotangentComparison_eq_zero`: if the conormal class of `a ∈ I` dies in
`(I'/I'²) ⧸ ⟨[y₀]⟩` then `a - r·y₀ ∈ I'²` for some `r`, so `a = u + t·y₀` with `u ∈ I²` by
`hyperplaneIdeal_sq_le`; since `a` and `u` lie in `I`, regularity of `y₀` forces `t ∈ I`
(`mem_of_mul_hyperplaneCoord_mem`), and therefore the conormal class of `a` is `y₀` times the
conormal class of `t`.  Combined with the surjectivity of `Base I → Base I'` (which makes every
element of `Base I' ⊗[Base I] M` of the form `1 ⊗ x`, `exists_one_tmul`) this is exactly the
injectivity of the degree-zero comparison map.

As in `RelativeAbsolute.lean` and `RelativeVirtualClassBaseChange.lean` everything here is the
affine model `X = Spec (R ⧸ I) ⊆ 𝔸^σ × Y`, not the Deligne–Mumford-stack statement of
Behrend–Fantechi §7.  The resolved-cone ideal identity and the resulting Gysin-map identity
`relativeVirtualClassAt (hyperplaneHom φ) = i^! …` are not treated here.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneObstruction

open LinearTwoTermComplex PicardCriteria

/-! ## Elementary criteria for a chain map to be an obstruction theory -/

section General

variable {R : Type u} [CommRing R] {E F G : LinearTwoTermComplex R}

/-- **Obstruction theories compose.**  `H⁰` of a composite is the composite of the `H⁰`s, which
is a composite of bijections, and `H⁻¹` of a composite is a composite of surjections. -/
theorem isObstructionTheory_comp {ψ : Hom F G} {φ : Hom E F} (hψ : IsObstructionTheory ψ)
    (hφ : IsObstructionTheory φ) : IsObstructionTheory (ψ.comp φ) where
  bijective_cokernelMap := by
    rw [Hom.cokernelMap_comp, LinearMap.coe_comp]
    exact hψ.bijective_cokernelMap.comp hφ.bijective_cokernelMap
  surjective_kernelMap := by
    rw [Hom.kernelMap_comp, LinearMap.coe_comp]
    exact hψ.surjective_kernelMap.comp hφ.surjective_kernelMap

/-- **A chain map which is surjective in degree zero and bijective in degree one is an
obstruction theory.**

Both conditions are elementary diagram chases.  For `H⁰`: the range of the target differential is
the image of the range of the source differential, because degree zero is surjective, whence
injectivity on cokernels; surjectivity on cokernels is immediate from surjectivity in degree one.
For `H⁻¹`: lift an element of `ker` of the target differential to degree zero, and use injectivity
in degree one to see that the lift is again a cycle. -/
theorem isObstructionTheory_of_surjective_of_bijective {φ : Hom E F}
    (h0 : Function.Surjective φ.degreeZero) (h1 : Function.Bijective φ.degreeOne) :
    IsObstructionTheory φ where
  bijective_cokernelMap := by
    refine ⟨LinearMap.ker_eq_bot.1 (Submodule.eq_bot_iff _ |>.2 fun z hz => ?_), fun z => ?_⟩
    · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [LinearMap.mem_ker, Hom.cokernelMap, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨a, ha⟩ := hz
      obtain ⟨e, rfl⟩ := h0 a
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨e, h1.1 ((φ.comm e).trans ha)⟩
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨x, rfl⟩ := h1.2 y
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  surjective_kernelMap := by
    rintro ⟨a, ha⟩
    obtain ⟨e, rfl⟩ := h0 a
    have hcycle : E.differential e = 0 := by
      apply h1.1
      rw [φ.comm e, LinearMap.mem_ker.1 ha, map_zero]
    exact ⟨⟨e, LinearMap.mem_ker.2 hcycle⟩, rfl⟩

/-- **A degreewise bijective chain map is a quasi-isomorphism.** -/
theorem isQuasiIsomorphism_of_bijective {φ : Hom E F} (h0 : Function.Bijective φ.degreeZero)
    (h1 : Function.Bijective φ.degreeOne) : φ.IsQuasiIsomorphism := by
  have h := isObstructionTheory_of_surjective_of_bijective h0.2 h1
  refine ⟨⟨fun x y hxy => ?_, h.surjective_kernelMap⟩, h.bijective_cokernelMap⟩
  exact Subtype.ext (h0.1 (Subtype.ext_iff.1 hxy))

end General


/-! ## The comparison chain map of the hyperplane base change -/

section Hyperplane

open RelativeVirtualClassBaseChange
open GromovWitten.AlgebraicGeometry.NormalConeAction (Base)

variable {k : Type u} [CommRing k] {σ τ' : Type u} [Fintype σ] [Fintype τ']
variable (I : Ideal (MvPolynomial (σ ⊕ Option τ') k))

/-- **The comparison chain map** of the hyperplane base change: the special case `φ = id` of
`RelativeVirtualClassBaseChange.hyperplaneHom`, a chain map
`(relConormalComplex I).baseChange (Base I') ⟶ hyperplaneConormalComplex I` from the base change
of the relative conormal complex of `X/Y` to the relative conormal complex of `X'/Y'`. -/
noncomputable abbrev hyperplaneComparisonHom :
    Hom ((RelativeAbsolute.relConormalComplex I).baseChange (Base (hyperplaneIdeal I)))
      (hyperplaneConormalComplex I) :=
  hyperplaneHom I (Hom.id (RelativeAbsolute.relConormalComplex I))

omit [Fintype τ'] in
@[simp]
theorem hyperplaneComparison_degreeZero_tmul (b : Base (hyperplaneIdeal I)) (x : I.Cotangent) :
    (hyperplaneComparisonHom I).degreeZero (b ⊗ₜ[Base I] x) =
      b • (Submodule.Quotient.mk (hyperplaneCotangentMapAux I x) : hyperplaneCotangent I) :=
  rfl

omit [Fintype τ'] in
theorem hyperplaneComparison_degreeOne_apply
    (x : Base (hyperplaneIdeal I) ⊗[Base I] (σ → Base I)) :
    (hyperplaneComparisonHom I).degreeOne x = hyperplaneSigmaBaseChangeEquiv I x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b f => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [Fintype τ'] in
/-- **`hyperplaneHom φ` factors through the comparison chain map**: it is the composite of the
degreewise base change of `φ` along `Base I → Base I'` with `hyperplaneComparisonHom I`. -/
theorem hyperplaneHom_eq_comp {E : LinearTwoTermComplex (Base I)}
    (φ : Hom E (RelativeAbsolute.relConormalComplex I)) :
    hyperplaneHom I φ =
      (hyperplaneComparisonHom I).comp (φ.baseChange (Base (hyperplaneIdeal I))) := by
  refine VirtualClass.BaseChangeObstruction.hom_ext (LinearMap.ext fun x => ?_)
    (LinearMap.ext fun x => ?_)
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b e => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b e => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [Fintype τ'] in
/-- **The comparison chain map is bijective in degree one**: the base change of the free module
`σ → Base I` is the free module `σ → Base I'`. -/
theorem bijective_hyperplaneComparison_degreeOne :
    Function.Bijective (hyperplaneComparisonHom I).degreeOne := by
  have h : ((hyperplaneComparisonHom I).degreeOne : _ → _) =
      ((hyperplaneSigmaBaseChangeEquiv I : _ → _)) :=
    funext (hyperplaneComparison_degreeOne_apply I)
  have hb := (hyperplaneSigmaBaseChangeEquiv I).bijective
  rwa [← h] at hb

omit [Fintype σ] [Fintype τ'] in
/-- **The conormal class of an element of `(y₀)`** lies in the `Base I'`-submodule of `I'/I'²`
spanned by the conormal class of `y₀`. -/
theorem toCotangent_mem_span (c : MvPolynomial (σ ⊕ Option τ') k)
    (hc : c ∈ Ideal.span {hyperplaneCoord (k := k) (σ := σ) (τ' := τ')})
    (hc' : c ∈ hyperplaneIdeal I) :
    (hyperplaneIdeal I).toCotangent ⟨c, hc'⟩ ∈
      (Base (hyperplaneIdeal I) ∙ (hyperplaneIdeal I).toCotangent
        ⟨hyperplaneCoord, hyperplaneCoord_mem I⟩) := by
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  refine Submodule.mem_span_singleton.2 ⟨Ideal.Quotient.mk (hyperplaneIdeal I) r, ?_⟩
  have hsmul : (Ideal.Quotient.mk (hyperplaneIdeal I) r) •
      (hyperplaneIdeal I).toCotangent ⟨hyperplaneCoord, hyperplaneCoord_mem I⟩ =
      r • (hyperplaneIdeal I).toCotangent ⟨hyperplaneCoord, hyperplaneCoord_mem I⟩ :=
    IsScalarTower.algebraMap_smul (Base (hyperplaneIdeal I)) r _
  rw [hsmul, ← map_smul]
  rfl

omit [Fintype τ'] in
/-- **The comparison chain map is surjective in degree zero**: modulo the conormal class of `y₀`,
every conormal class of `I' = I + (y₀)` comes from a conormal class of `I`. -/
theorem surjective_hyperplaneComparison_degreeZero :
    Function.Surjective (hyperplaneComparisonHom I).degreeZero := by
  intro z
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective (hyperplaneIdeal I) w
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 ha
  refine ⟨1 ⊗ₜ[Base I] I.toCotangent ⟨b, hb⟩, ?_⟩
  rw [hyperplaneComparison_degreeZero_tmul, one_smul, hyperplaneCotangentMapAux,
    Ideal.mapCotangent_toCotangent]
  refine (Submodule.Quotient.eq _).2 ?_
  have hsplit : (hyperplaneIdeal I).toCotangent ⟨b + c, ha⟩ =
      (hyperplaneIdeal I).toCotangent ⟨(AlgHom.id (MvPolynomial (σ ⊕ Option τ') k)
          (MvPolynomial (σ ⊕ Option τ') k)) b, le_hyperplaneIdeal I hb⟩ +
        (hyperplaneIdeal I).toCotangent ⟨c, Ideal.mem_sup_right hc⟩ := by
    rw [← map_add]
    rfl
  rw [hsplit, sub_add_eq_sub_sub, sub_self, zero_sub]
  exact neg_mem (toCotangent_mem_span I c hc (Ideal.mem_sup_right hc))

omit [Fintype τ'] in
/-- **The comparison chain map of the hyperplane base change is an obstruction theory**: it is
surjective in degree zero and bijective in degree one. -/
theorem isObstructionTheory_hyperplaneComparisonHom :
    IsObstructionTheory (hyperplaneComparisonHom I) :=
  isObstructionTheory_of_surjective_of_bijective
    (surjective_hyperplaneComparison_degreeZero I) (bijective_hyperplaneComparison_degreeOne I)


omit [Fintype τ'] in
/-- **The obstruction-theory condition transfers along the hyperplane comparison map.**

If `φ : E ⟶ relConormalComplex I` is a relative obstruction theory for `X = Spec (R/I) → Y = 𝔸^τ`
(`τ = Option τ'`), then `hyperplaneHom φ` is a relative obstruction theory for the base change
`X' = X ×_Y Y' → Y' = 𝔸^{τ'}` along the coordinate hyperplane `y₀ = 0`.

No regularity hypothesis on `y₀` is needed: `hyperplaneHom φ` factors
(`hyperplaneHom_eq_comp`) as the degreewise base change of `φ` along the quotient map
`Base I → Base I'`, which is an obstruction theory for *any* base change
(`PicardCriteria.IsObstructionTheory.baseChange`, right exactness of the mapping cone), followed
by the comparison map `hyperplaneComparisonHom I`, which is an obstruction theory because it is
surjective in degree zero and bijective in degree one; and obstruction theories compose.
Regularity of `y₀` on `Base I` is exactly what upgrades the comparison map from an obstruction
theory to a quasi-isomorphism, see `isQuasiIsomorphism_hyperplaneComparisonHom`. -/
theorem isObstructionTheory_hyperplaneHom {E : LinearTwoTermComplex (Base I)}
    {φ : Hom E (RelativeAbsolute.relConormalComplex I)} (hφ : IsObstructionTheory φ) :
    IsObstructionTheory (hyperplaneHom I φ) := by
  rw [hyperplaneHom_eq_comp]
  exact isObstructionTheory_comp (isObstructionTheory_hyperplaneComparisonHom I)
    (hφ.baseChange (Base (hyperplaneIdeal I)))


/-! ### Regularity of `y₀`: the comparison map is a quasi-isomorphism -/

omit [Fintype σ] [Fintype τ'] in
/-- **Elementwise form of the regularity hypothesis**: if `y₀` is a non-zero-divisor on
`Base I = R ⧸ I` then `r · y₀ ∈ I` forces `r ∈ I`. -/
theorem mem_of_mul_hyperplaneCoord_mem
    (hreg : IsSMulRegular (Base I)
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ'))))
    {r : MvPolynomial (σ ⊕ Option τ') k} (hr : r * hyperplaneCoord ∈ I) : r ∈ I := by
  have h : (Ideal.Quotient.mk I hyperplaneCoord) • (Ideal.Quotient.mk I r) =
      (Ideal.Quotient.mk I hyperplaneCoord) • (0 : Base I) := by
    rw [smul_eq_mul, smul_zero, ← map_mul, mul_comm]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hr
  exact Ideal.Quotient.eq_zero_iff_mem.1 (hreg h)

omit [Fintype σ] [Fintype τ'] in
/-- **`I'² ≤ I² + (y₀)`**: every product of two elements of `I' = I + (y₀)` is a product of two
elements of `I` plus a multiple of `y₀`. -/
theorem hyperplaneIdeal_sq_le :
    hyperplaneIdeal I ^ 2 ≤
      I ^ 2 ⊔ Ideal.span {hyperplaneCoord (k := k) (σ := σ) (τ' := τ')} := by
  rw [pow_two, pow_two]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
  have hexp : (x₁ + x₂) * (y₁ + y₂) = x₁ * y₁ + (x₂ * y₁ + (x₁ * y₂ + x₂ * y₂)) := by ring
  rw [hexp]
  exact Submodule.add_mem_sup (Ideal.mul_mem_mul hx₁ hy₁)
    (add_mem (Ideal.mul_mem_right _ _ hx₂)
      (add_mem (Ideal.mul_mem_left _ _ hy₂) (Ideal.mul_mem_right _ _ hx₂)))

omit [Fintype σ] [Fintype τ'] in
/-- **The kernel of the comparison map on conormal modules is `y₀ · (I/I²)`**, when `y₀` is a
non-zero-divisor on `Base I`.

Indeed if the class of `a ∈ I` dies in `I'/I'² ⧸ ⟨[y₀]⟩` then `a - r·y₀ ∈ I'²` for some `r`, so
`a = u + t·y₀` with `u ∈ I²` by `hyperplaneIdeal_sq_le`; as `a` and `u` lie in `I`, regularity
gives `t ∈ I`, and then the conormal class of `a` is `y₀ ·` the conormal class of `t`. -/
theorem exists_smul_of_hyperplaneCotangentComparison_eq_zero
    (hreg : IsSMulRegular (Base I)
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ'))))
    (x : I.Cotangent)
    (hx : (Submodule.Quotient.mk (hyperplaneCotangentMapAux I x) : hyperplaneCotangent I) = 0) :
    ∃ y : I.Cotangent, x = hyperplaneCoord (k := k) (σ := σ) (τ' := τ') • y := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective I x
  rw [hyperplaneCotangentMapAux, Ideal.mapCotangent_toCotangent,
    Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
  have hsmul : (Ideal.Quotient.mk (hyperplaneIdeal I) r) •
      (hyperplaneIdeal I).toCotangent ⟨hyperplaneCoord, hyperplaneCoord_mem I⟩ =
      (hyperplaneIdeal I).toCotangent
        ⟨r * hyperplaneCoord, Ideal.mul_mem_left _ _ (hyperplaneCoord_mem I)⟩ := by
    have h : (Ideal.Quotient.mk (hyperplaneIdeal I) r) •
        (hyperplaneIdeal I).toCotangent ⟨hyperplaneCoord, hyperplaneCoord_mem I⟩ =
        r • (hyperplaneIdeal I).toCotangent ⟨hyperplaneCoord, hyperplaneCoord_mem I⟩ :=
      IsScalarTower.algebraMap_smul (Base (hyperplaneIdeal I)) r _
    rw [h, ← map_smul]
    rfl
  rw [hsmul] at ht
  have hmem : a - r * hyperplaneCoord ∈ hyperplaneIdeal I ^ 2 := by
    have hzero : (hyperplaneIdeal I).toCotangent
        ⟨a - r * hyperplaneCoord, sub_mem (le_hyperplaneIdeal I ha)
          (Ideal.mul_mem_left _ _ (hyperplaneCoord_mem I))⟩ = 0 := by
      rw [show (⟨a - r * hyperplaneCoord, sub_mem (le_hyperplaneIdeal I ha)
            (Ideal.mul_mem_left _ _ (hyperplaneCoord_mem I))⟩ : hyperplaneIdeal I) =
          ⟨a, le_hyperplaneIdeal I ha⟩ -
            ⟨r * hyperplaneCoord, Ideal.mul_mem_left _ _ (hyperplaneCoord_mem I)⟩ from rfl,
        map_sub]
      exact sub_eq_zero_of_eq ht.symm
    exact (Ideal.toCotangent_eq_zero _ _).1 hzero
  obtain ⟨u, hu, v, hv, hsum⟩ := Submodule.mem_sup.1 (hyperplaneIdeal_sq_le I hmem)
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hv
  have hdecomp : a = u + (w + r) * hyperplaneCoord := by linear_combination -hsum
  have hwr : (w + r) * hyperplaneCoord ∈ I := by
    have h : (w + r) * hyperplaneCoord = a - u := by rw [hdecomp]; ring
    rw [h]
    exact sub_mem ha (Ideal.pow_le_self two_ne_zero hu)
  have hwrI : w + r ∈ I := mem_of_mul_hyperplaneCoord_mem I hreg hwr
  refine ⟨I.toCotangent ⟨w + r, hwrI⟩, ?_⟩
  rw [← map_smul]
  have hu0 : I.toCotangent ⟨u, Ideal.pow_le_self two_ne_zero hu⟩ = 0 :=
    (I.toCotangent_eq_zero _).2 hu
  have hsub : (⟨a, ha⟩ : I) = ⟨u, Ideal.pow_le_self two_ne_zero hu⟩ +
      (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')) • (⟨w + r, hwrI⟩ : I) := by
    apply Subtype.ext
    change a = u + hyperplaneCoord * (w + r)
    rw [hdecomp]
    ring
  rw [hsub, map_add, hu0, zero_add]

omit [Fintype σ] [Fintype τ'] in
/-- **Every element of `Base I' ⊗[Base I] M` is of the form `1 ⊗ x`**, because
`Base I → Base I'` is surjective. -/
theorem exists_one_tmul {M : Type u} [AddCommGroup M] [Module (Base I) M]
    (z : Base (hyperplaneIdeal I) ⊗[Base I] M) : ∃ x : M, z = 1 ⊗ₜ[Base I] x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
  | tmul b x =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨(Ideal.Quotient.mk I r) • x, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, (TensorProduct.tmul_add _ _ _).symm⟩

omit [Fintype τ'] in
/-- **The comparison map is injective in degree zero** when `y₀` is a non-zero-divisor on
`Base I`. -/
theorem injective_hyperplaneComparison_degreeZero
    (hreg : IsSMulRegular (Base I)
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))) :
    Function.Injective (hyperplaneComparisonHom I).degreeZero := by
  refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun z hz => ?_)
  obtain ⟨x, rfl⟩ := exists_one_tmul I z
  rw [hyperplaneComparison_degreeZero_tmul, one_smul] at hz
  obtain ⟨y, rfl⟩ := exists_smul_of_hyperplaneCotangentComparison_eq_zero I hreg x hz
  have hcoe : hyperplaneCoord (k := k) (σ := σ) (τ' := τ') • y =
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ'))) • y :=
    (IsScalarTower.algebraMap_smul (Base I) _ y).symm
  have hzero : (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ'))) •
      (1 : Base (hyperplaneIdeal I)) = 0 := by
    rw [Algebra.smul_def, mul_one, algebraMap_hyperplane_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hyperplaneCoord_mem I)
  rw [hcoe, ← TensorProduct.smul_tmul, hzero, TensorProduct.zero_tmul]

/-- **The splitting of the conormal module of the hyperplane section.**

If `y₀` is a non-zero-divisor on `Base I = R ⧸ I`, the relative conormal module of `X'/Y'`,
namely `hyperplaneCotangent I = (I'/I'²) ⧸ ⟨[y₀]⟩`, is the base change of the relative conormal
module `I/I²` of `X/Y` along `Base I → Base I'`.  Equivalently `I'/I'²` splits as
`(I/I² ⊗ Base I') ⊕ (y₀)/(y₀)²`; the Tor-independence input is `I ∩ (y₀) = y₀ · I`, which is the
content of `exists_smul_of_hyperplaneCotangentComparison_eq_zero`. -/
noncomputable def hyperplaneCotangentEquiv
    (hreg : IsSMulRegular (Base I)
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))) :
    Base (hyperplaneIdeal I) ⊗[Base I] I.Cotangent ≃ₗ[Base (hyperplaneIdeal I)]
      hyperplaneCotangent I :=
  LinearEquiv.ofBijective (hyperplaneComparisonHom I).degreeZero
    ⟨injective_hyperplaneComparison_degreeZero I hreg,
      surjective_hyperplaneComparison_degreeZero I⟩

omit [Fintype τ'] in
/-- **The comparison chain map is a quasi-isomorphism** when `y₀` is a non-zero-divisor on
`Base I`: it is then bijective in both degrees. -/
theorem isQuasiIsomorphism_hyperplaneComparisonHom
    (hreg : IsSMulRegular (Base I)
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')))) :
    (hyperplaneComparisonHom I).IsQuasiIsomorphism :=
  isQuasiIsomorphism_of_bijective
    ⟨injective_hyperplaneComparison_degreeZero I hreg,
      surjective_hyperplaneComparison_degreeZero I⟩
    (bijective_hyperplaneComparison_degreeOne I)

omit [Fintype τ'] in
/-- **Regularity makes the hyperplane base change reflect the obstruction-theory property**: for
`y₀` a non-zero-divisor on `Base I`, `hyperplaneHom φ` is an obstruction theory if and only if the
plain degreewise base change of `φ` along `Base I → Base I'` is one. -/
theorem isObstructionTheory_hyperplaneHom_iff
    (hreg : IsSMulRegular (Base I)
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ'))))
    {E : LinearTwoTermComplex (Base I)}
    (φ : Hom E (RelativeAbsolute.relConormalComplex I)) :
    IsObstructionTheory (hyperplaneHom I φ) ↔
      IsObstructionTheory (φ.baseChange (Base (hyperplaneIdeal I))) := by
  rw [hyperplaneHom_eq_comp]
  refine ⟨fun h => VirtualClass.BaseChangeObstruction.isObstructionTheory_of_comp_quasiIso
    (isQuasiIsomorphism_hyperplaneComparisonHom I hreg) h, fun h =>
    isObstructionTheory_comp (isObstructionTheory_hyperplaneComparisonHom I) h⟩

end Hyperplane

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneObstruction
