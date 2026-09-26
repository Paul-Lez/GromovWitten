/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.Transitivity
import GromovWitten.AlgebraicGeometry.CotangentComplex.TransitivityEtaleGeneral

/-!
# Descent data for the cohomology of the cotangent complex along an étale cover

This file packages the étale base-change isomorphisms of `Transitivity.lean` and
`TransitivityEtaleGeneral.lean` into genuine descent data, at the level of rings: given
`R → S` and a family of étale `S`-algebras `Tⱼ`, we construct the transition isomorphisms
`Hⁱ(L_{Tⱼ/R}) ⊗_{Tⱼ} (Tⱼ ⊗ₛ Tₗ) ≅ Hⁱ(L_{Tⱼ ⊗ₛ Tₗ/R})` for `i ∈ {0, -1}`, prove the cocycle
condition on triple overlaps, and show effectivity: the transition isomorphisms coincide with
the canonical base-change identifications of the module `Hⁱ(L_{S/R})` itself.

Concretely, `H⁰(L_{T/R})` is represented by `Ω[T⁄R]` (`Full.cohomologyZero`) and
`H⁻¹(L_{T/R})` by `Algebra.H1Cotangent R T` (`Full.cohomologyNegOne`); we work with these
concrete presentations throughout, rather than with `Full.cohomology (Full.cotangentComplex R T)
i` directly, to avoid unnecessary `ModuleCat`/`DerivedCategory` bookkeeping.

## Main declarations

* `kaehlerMap_comp`: the composition law for `KaehlerDifferential.map` (fixed base `R`) across a
  tower `A → B → C`, the Kähler-differential analogue of `Transitivity.h1CotangentMap_comp`.
* `bijective_mapBaseChange_of_formallyEtale`, `equivMapBaseChange`: the concrete (non-`Full`-
  wrapped) form of `Transitivity.hZeroBaseChangeIso`: for `S → T` formally étale,
  `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]`.
* `mapBaseChange_comp_tower`, `liftBaseChange_comp_tower`: the composition law for the `H⁰`/`H⁻¹`
  base-change maps through an intermediate ring `S → A → T` (no étale hypothesis needed: a pure
  functoriality statement, proved from `kaehlerMap_comp`/`Transitivity.h1CotangentMap_comp`).
* `hZeroTransition`, `hNegOneTransition`: the transition isomorphisms
  `(A ⊗ₛ B) ⊗_A Hⁱ(L_{A/R}) ≃ Hⁱ(L_{A ⊗ₛ B/R})` for two étale `S`-algebras `A`, `B`.
* `hZeroTransition_cocycle`, `hNegOneTransition_cocycle`: the **cocycle condition** on the triple
  overlap `A ⊗ₛ B ⊗ₛ C` of three étale `S`-algebras.
* `hZeroTransition_eq_canonical`, `hNegOneTransition_eq_canonical`: **effectivity** — the
  transition isomorphism on the overlap `A ⊗ₛ B` agrees with the canonical base-change
  identification of `Hⁱ(L_{S/R})` itself.
* `EtaleDescentDatum`, `cotangentDescentDatum`, `cotangentDescentDatum_eq_canonical`: the same
  data packaged for an indexed family `T : J → Type u` of étale `S`-algebras.

## Design notes

* A single declaration `cotangentDescentDatum i` polymorphic in the cohomological degree
  `i : ℤ` is not used: `H⁰` and `H⁻¹` are represented by genuinely different types (`Ω[T⁄R]`
  versus `Algebra.H1Cotangent R T`), so `EtaleDescentDatum` bundles *both* pieces of data
  (fields `hZero`/`cocycleZero` and `hNegOne`/`cocycleNegOne`) rather than being indexed by `i`.
* `cotangentDescentDatum` is a `def`, not a Lean `instance`: `EtaleDescentDatum` is a plain
  `structure`, and Lean's `instance` mechanism requires a `class`; making it a `class` would be
  poor design here since every argument (`R S J T`) is explicit and would never be found by
  ordinary typeclass search. "Instance" in the task description is used in the informal,
  mathematical sense of "the canonical/distinguished example".
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

open CategoryTheory
open scoped TensorProduct

universe u

namespace AtlasDescent

open Transitivity

/-! ### A composition law for `KaehlerDifferential.map` across a tower of algebras -/

section KaehlerMapComp

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]
variable [Algebra A B] [Algebra B C] [Algebra A C]
variable [IsScalarTower R A B] [IsScalarTower R B C] [IsScalarTower R A C] [IsScalarTower A B C]

/-- Functoriality of `KaehlerDifferential.map` (with fixed base `R`) in the tower `A → B → C`:
the Kähler-differential analogue of `Transitivity.h1CotangentMap_comp`. -/
theorem kaehlerMap_comp :
    KaehlerDifferential.map R R A C =
      (KaehlerDifferential.map R R B C).restrictScalars A ∘ₗ KaehlerDifferential.map R R A B := by
  apply Derivation.liftKaehlerDifferential_unique
  ext x
  simp [KaehlerDifferential.map_D, IsScalarTower.algebraMap_apply A B C]

end KaehlerMapComp

/-! ### `H⁰` base change, restated without reference to `Full.cohomology` -/

section MapBaseChangeBijective

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- `Full.jzBaseChange`'s underlying map is, up to the (iso) identification of `H⁰(L_{T/R})`
with `Ω[T⁄R]`, exactly `KaehlerDifferential.mapBaseChange R S T`: the composite defining
`Full.jzBaseChange`, unfolded. -/
theorem jzBaseChange_hom_eq :
    (Full.jzBaseChange R S T).hom =
      (Full.cohomologyZero R T).toLinearEquiv.symm.toLinearMap.comp
        (KaehlerDifferential.mapBaseChange R S T) := by
  rw [Full.jzBaseChange, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    Iso.toLinearEquiv_symm, Iso.toLinearMap_toLinearEquiv, Iso.symm_hom]

/-- Along a formally étale map `S → T`, `KaehlerDifferential.mapBaseChange` is bijective: the
concrete (non-`Full.cohomology`-wrapped) form of
`Transitivity.bijective_jzBaseChange_of_formallyEtale`. -/
theorem bijective_mapBaseChange_of_formallyEtale [Algebra.FormallyEtale S T] :
    Function.Bijective (KaehlerDifferential.mapBaseChange R S T) := by
  have h := bijective_jzBaseChange_of_formallyEtale R S T
  rw [jzBaseChange_hom_eq] at h
  exact (Function.Bijective.of_comp_iff'
    (Full.cohomologyZero R T).toLinearEquiv.symm.bijective
    (KaehlerDifferential.mapBaseChange R S T)).mp h

/-- The isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `S → T` formally étale (no flatness or
finite-presentation hypothesis needed): the `H⁰` transition isomorphism, concretely. -/
noncomputable def equivMapBaseChange [Algebra.FormallyEtale S T] :
    T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R] :=
  LinearEquiv.ofBijective _ (bijective_mapBaseChange_of_formallyEtale R S T)

end MapBaseChangeBijective

/-! ### Composition law for the base-change maps through an intermediate ring -/

section TowerComp

variable (R S A T : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing T]
variable [Algebra R S] [Algebra R A] [Algebra R T]
variable [Algebra S A] [Algebra A T] [Algebra S T]
variable [IsScalarTower R S A] [IsScalarTower R A T] [IsScalarTower R S T] [IsScalarTower S A T]

/-- The composition law for `H⁰` base change through a tower `S → A → T`: the direct
base-change map `mapBaseChange R S T` agrees with first base-changing to `A` and then to `T`,
after the canonical associativity identification `T ⊗[A] (A ⊗[S] Ω[S⁄R]) ≃ T ⊗[S] Ω[S⁄R]`. No
étale hypothesis is used: this is pure functoriality of `KaehlerDifferential.mapBaseChange`. -/
theorem mapBaseChange_comp_tower :
    KaehlerDifferential.mapBaseChange R S T =
      (KaehlerDifferential.mapBaseChange R A T) ∘ₗ
        (TensorProduct.AlgebraTensorModule.map (LinearMap.id : T →ₗ[T] T)
          (KaehlerDifferential.mapBaseChange R S A)) ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange S A T T Ω[S⁄R]).symm.toLinearMap := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t y =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq,
      KaehlerDifferential.mapBaseChange_tmul, one_smul]
    congr 1
    exact congr($(kaehlerMap_comp R S A T) y)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The composition law for `H⁻¹` base change through a tower `S → A → T`: the analogue of
`mapBaseChange_comp_tower` for `Algebra.H1Cotangent.map`, using
`Transitivity.h1CotangentMap_comp`. No étale hypothesis is used. -/
theorem liftBaseChange_comp_tower :
    (Algebra.H1Cotangent.map R R S T).liftBaseChange T =
      ((Algebra.H1Cotangent.map R R A T).liftBaseChange T) ∘ₗ
        (TensorProduct.AlgebraTensorModule.map (LinearMap.id : T →ₗ[T] T)
          ((Algebra.H1Cotangent.map R R S A).liftBaseChange A)) ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange S A T T
          (Algebra.H1Cotangent R S)).symm.toLinearMap := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t x =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq,
      LinearMap.liftBaseChange_tmul, one_smul]
    congr 1
    exact congr($(h1CotangentMap_comp R S T A) x)
  | add x y hx hy => simp only [map_add, hx, hy]

end TowerComp

/-! ### Transition isomorphisms for a pair of étale `S`-algebras, cocycle and effectivity -/

section Transitions

variable (R S A B C : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra R C]
variable [Algebra S A] [Algebra S B] [Algebra S C]
variable [IsScalarTower R S A] [IsScalarTower R S B] [IsScalarTower R S C]
variable [Algebra.Etale S A] [Algebra.Etale S B] [Algebra.Etale S C]

/-- `A → A ⊗[S] B ⊗[S] C` is étale directly (composing `A → A ⊗[S] B` and
`A ⊗[S] B → A ⊗[S] B ⊗[S] C`, both base changes of étale maps). -/
instance instEtaleTripleDirect : Algebra.Etale A (A ⊗[S] B ⊗[S] C) :=
  Algebra.Etale.comp A (A ⊗[S] B) (A ⊗[S] B ⊗[S] C)

omit [Algebra R C] [Algebra S C] [IsScalarTower R S C] [Algebra.Etale S C] in
/-- `S → A ⊗[S] B` is étale directly (composing `S → A` and `A → A ⊗[S] B`). -/
instance instEtaleOverlap : Algebra.Etale S (A ⊗[S] B) :=
  Algebra.Etale.comp S A (A ⊗[S] B)

omit [Algebra R C] [Algebra S C] [IsScalarTower R S C] [Algebra.Etale S C] in
/-- The `H⁰` transition isomorphism on the overlap `A ⊗[S] B` of two members `A`, `B` of an
étale cover of `S`: `(A ⊗[S] B) ⊗[A] Ω[A⁄R] ≃ₗ[A ⊗[S] B] Ω[(A ⊗[S] B)⁄R]`. -/
noncomputable def hZeroTransition : (A ⊗[S] B) ⊗[A] Ω[A⁄R] ≃ₗ[A ⊗[S] B] Ω[(A ⊗[S] B)⁄R] :=
  equivMapBaseChange R A (A ⊗[S] B)

omit [Algebra R C] [Algebra S C] [IsScalarTower R S C] [Algebra.Etale S C] in
/-- The `H⁻¹` transition isomorphism on the overlap `A ⊗[S] B`. -/
noncomputable def hNegOneTransition :
    (A ⊗[S] B) ⊗[A] Algebra.H1Cotangent R A ≃ₗ[A ⊗[S] B] Algebra.H1Cotangent R (A ⊗[S] B) :=
  tensorH1CotangentOfEtale R A (A ⊗[S] B)

omit [Algebra R B] [Algebra R C] [IsScalarTower R S B] [IsScalarTower R S C]
  [Algebra.Etale S A] in
/-- **Cocycle condition for `H⁰`.** On the triple overlap `A ⊗[S] B ⊗[S] C` of three étale
`S`-algebras, composing the transition isomorphism `A → A ⊗[S] B` with the transition
`A ⊗[S] B → A ⊗[S] B ⊗[S] C` agrees with the direct transition `A → A ⊗[S] B ⊗[S] C`. -/
theorem hZeroTransition_cocycle :
    (equivMapBaseChange R (A ⊗[S] B) (A ⊗[S] B ⊗[S] C)).toLinearMap ∘ₗ
        (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id : (A ⊗[S] B ⊗[S] C) →ₗ[A ⊗[S] B ⊗[S] C] (A ⊗[S] B ⊗[S] C))
          (hZeroTransition R S A B).toLinearMap) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⊗[S] B) (A ⊗[S] B ⊗[S] C)
        (A ⊗[S] B ⊗[S] C) Ω[A⁄R]).symm.toLinearMap
    = (equivMapBaseChange R A (A ⊗[S] B ⊗[S] C)).toLinearMap :=
  (mapBaseChange_comp_tower R A (A ⊗[S] B) (A ⊗[S] B ⊗[S] C)).symm

omit [Algebra R B] [Algebra R C] [IsScalarTower R S B] [IsScalarTower R S C]
  [Algebra.Etale S A] in
/-- **Cocycle condition for `H⁻¹`.** The analogue of `hZeroTransition_cocycle`. -/
theorem hNegOneTransition_cocycle :
    (tensorH1CotangentOfEtale R (A ⊗[S] B) (A ⊗[S] B ⊗[S] C)).toLinearMap ∘ₗ
        (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id : (A ⊗[S] B ⊗[S] C) →ₗ[A ⊗[S] B ⊗[S] C] (A ⊗[S] B ⊗[S] C))
          (hNegOneTransition R S A B).toLinearMap) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⊗[S] B) (A ⊗[S] B ⊗[S] C)
        (A ⊗[S] B ⊗[S] C) (Algebra.H1Cotangent R A)).symm.toLinearMap
    = (tensorH1CotangentOfEtale R A (A ⊗[S] B ⊗[S] C)).toLinearMap :=
  (liftBaseChange_comp_tower R A (A ⊗[S] B) (A ⊗[S] B ⊗[S] C)).symm

omit [Algebra R B] [IsScalarTower R S B] in
/-- **Effectivity for `H⁰`.** The transition isomorphism on the overlap `A ⊗[S] B` agrees with
the canonical base-change identification `(Ω[S⁄R] ⊗[S] A) ⊗_A (A ⊗[S] B) ≃ Ω[S⁄R] ⊗[S] (A ⊗[S]
B)` of the module `Ω[S⁄R] = H⁰(L_{S/R})` itself: the descended module is literally `H⁰(L_{S/R})`
base-changed to each chart, no new data is introduced by the cover. -/
theorem hZeroTransition_eq_canonical :
    (equivMapBaseChange R A (A ⊗[S] B)).toLinearMap ∘ₗ
        (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id : (A ⊗[S] B) →ₗ[A ⊗[S] B] (A ⊗[S] B))
          (equivMapBaseChange R S A).toLinearMap) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S A (A ⊗[S] B) (A ⊗[S] B)
        Ω[S⁄R]).symm.toLinearMap
    = (equivMapBaseChange R S (A ⊗[S] B)).toLinearMap :=
  (mapBaseChange_comp_tower R S A (A ⊗[S] B)).symm

omit [Algebra R B] [IsScalarTower R S B] in
/-- **Effectivity for `H⁻¹`.** The analogue of `hZeroTransition_eq_canonical` for
`Algebra.H1Cotangent R S = H⁻¹(L_{S/R})`. -/
theorem hNegOneTransition_eq_canonical :
    (tensorH1CotangentOfEtale R A (A ⊗[S] B)).toLinearMap ∘ₗ
        (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id : (A ⊗[S] B) →ₗ[A ⊗[S] B] (A ⊗[S] B))
          (tensorH1CotangentOfEtale R S A).toLinearMap) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S A (A ⊗[S] B) (A ⊗[S] B)
        (Algebra.H1Cotangent R S)).symm.toLinearMap
    = (tensorH1CotangentOfEtale R S (A ⊗[S] B)).toLinearMap :=
  (liftBaseChange_comp_tower R S A (A ⊗[S] B)).symm

end Transitions

/-! ### Descent data for an indexed family of étale `S`-algebras -/

section Datum

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (J : Type u) (T : J → Type u) [∀ j, CommRing (T j)] [∀ j, Algebra S (T j)]
variable [∀ j, Algebra R (T j)] [∀ j, IsScalarTower R S (T j)] [∀ j, Algebra.Etale S (T j)]

/-- `S → Tⱼ ⊗[S] Tₗ` is étale directly (composing `S → Tⱼ` and `Tⱼ → Tⱼ ⊗[S] Tₗ`). -/
instance instEtaleOverlapFam (j l : J) : Algebra.Etale S (T j ⊗[S] T l) :=
  Algebra.Etale.comp S (T j) (T j ⊗[S] T l)

/-- `Tⱼ → Tⱼ ⊗[S] Tₗ ⊗[S] Tₘ` is étale directly. -/
instance instEtaleTripleFam (j l m : J) : Algebra.Etale (T j) (T j ⊗[S] T l ⊗[S] T m) :=
  Algebra.Etale.comp (T j) (T j ⊗[S] T l) (T j ⊗[S] T l ⊗[S] T m)

/-- A descent datum for `H⁰`/`H⁻¹` of the cotangent complex along a family `T` of étale
`S`-algebras: transition isomorphisms on pairwise overlaps `Tⱼ ⊗ₛ Tₗ`, satisfying the cocycle
condition on triple overlaps `Tⱼ ⊗ₛ Tₗ ⊗ₛ Tₘ` (see the module docstring for why `H⁰` and `H⁻¹`
are bundled together instead of being indexed by a cohomological degree `i`). -/
structure EtaleDescentDatum where
  /-- The `H⁰` transition isomorphism on the overlap `Tⱼ ⊗ₛ Tₗ`. -/
  hZero : ∀ j l, (T j ⊗[S] T l) ⊗[T j] Ω[T j⁄R] ≃ₗ[T j ⊗[S] T l] Ω[(T j ⊗[S] T l)⁄R]
  /-- The `H⁻¹` transition isomorphism on the overlap `Tⱼ ⊗ₛ Tₗ`. -/
  hNegOne : ∀ j l, (T j ⊗[S] T l) ⊗[T j] Algebra.H1Cotangent R (T j) ≃ₗ[T j ⊗[S] T l]
    Algebra.H1Cotangent R (T j ⊗[S] T l)
  /-- The `H⁰` cocycle condition on the triple overlap `Tⱼ ⊗ₛ Tₗ ⊗ₛ Tₘ`. -/
  cocycleZero : ∀ j l m,
    (equivMapBaseChange R (T j ⊗[S] T l) (T j ⊗[S] T l ⊗[S] T m)).toLinearMap ∘ₗ
        (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id : (T j ⊗[S] T l ⊗[S] T m) →ₗ[T j ⊗[S] T l ⊗[S] T m]
            (T j ⊗[S] T l ⊗[S] T m))
          (hZero j l).toLinearMap) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (T j) (T j ⊗[S] T l)
        (T j ⊗[S] T l ⊗[S] T m) (T j ⊗[S] T l ⊗[S] T m) Ω[T j⁄R]).symm.toLinearMap
    = (equivMapBaseChange R (T j) (T j ⊗[S] T l ⊗[S] T m)).toLinearMap
  /-- The `H⁻¹` cocycle condition on the triple overlap `Tⱼ ⊗ₛ Tₗ ⊗ₛ Tₘ`. -/
  cocycleNegOne : ∀ j l m,
    (tensorH1CotangentOfEtale R (T j ⊗[S] T l) (T j ⊗[S] T l ⊗[S] T m)).toLinearMap ∘ₗ
        (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id : (T j ⊗[S] T l ⊗[S] T m) →ₗ[T j ⊗[S] T l ⊗[S] T m]
            (T j ⊗[S] T l ⊗[S] T m))
          (hNegOne j l).toLinearMap) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (T j) (T j ⊗[S] T l)
        (T j ⊗[S] T l ⊗[S] T m) (T j ⊗[S] T l ⊗[S] T m)
        (Algebra.H1Cotangent R (T j))).symm.toLinearMap
    = (tensorH1CotangentOfEtale R (T j) (T j ⊗[S] T l ⊗[S] T m)).toLinearMap

/-- The canonical descent datum for the cohomology of the cotangent complex along the étale
cover `T`, built from `hZeroTransition`/`hNegOneTransition` and the cocycle conditions
`hZeroTransition_cocycle`/`hNegOneTransition_cocycle` instantiated at each `(T j, T l, T m)`. See
the module docstring for why this is a `def` rather than a Lean `instance`. -/
noncomputable def cotangentDescentDatum : EtaleDescentDatum R S J T where
  hZero j l := hZeroTransition R S (T j) (T l)
  hNegOne j l := hNegOneTransition R S (T j) (T l)
  cocycleZero j l m := hZeroTransition_cocycle R S (T j) (T l) (T m)
  cocycleNegOne j l m := hNegOneTransition_cocycle R S (T j) (T l) (T m)

/-- **Effectivity.** The transition isomorphisms of `cotangentDescentDatum` coincide with the
canonical base-change identifications `(Hⁱ(L_{S/R}) ⊗ₛ Tⱼ) ⊗_{Tⱼ} (Tⱼ ⊗ₛ Tₗ) ≃ Hⁱ(L_{S/R}) ⊗ₛ
(Tⱼ ⊗ₛ Tₗ)` of `Hⁱ(L_{S/R})` (`i ∈ {0, -1}`), i.e. the descended module is literally
`Hⁱ(L_{S/R})` itself: this is exactly what makes the presheaf of `Hⁱ`'s a quasi-coherent sheaf
on the small étale site of `S`. -/
theorem cotangentDescentDatum_eq_canonical (j l : J) :
    (((cotangentDescentDatum R S J T).hZero j l).toLinearMap ∘ₗ
        (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id : (T j ⊗[S] T l) →ₗ[T j ⊗[S] T l] (T j ⊗[S] T l))
          (equivMapBaseChange R S (T j)).toLinearMap) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S (T j) (T j ⊗[S] T l) (T j ⊗[S] T l)
        Ω[S⁄R]).symm.toLinearMap
      = (equivMapBaseChange R S (T j ⊗[S] T l)).toLinearMap) ∧
    (((cotangentDescentDatum R S J T).hNegOne j l).toLinearMap ∘ₗ
        (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id : (T j ⊗[S] T l) →ₗ[T j ⊗[S] T l] (T j ⊗[S] T l))
          (tensorH1CotangentOfEtale R S (T j)).toLinearMap) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S (T j) (T j ⊗[S] T l) (T j ⊗[S] T l)
        (Algebra.H1Cotangent R S)).symm.toLinearMap
      = (tensorH1CotangentOfEtale R S (T j ⊗[S] T l)).toLinearMap) :=
  ⟨hZeroTransition_eq_canonical R S (T j) (T l), hNegOneTransition_eq_canonical R S (T j) (T l)⟩

end Datum

end AtlasDescent

end GromovWitten.AlgebraicGeometry.CotangentComplex
