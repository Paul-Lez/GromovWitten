/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.Full

/-!
# The transitivity (Jacobi--Zariski) sequence for a tower of the cotangent complex

For a tower of commutative rings `R → S → T` (`IsScalarTower R S T`), this file assembles the
six-term Jacobi--Zariski exact sequence of the cohomology of the (truncated) cotangent complexes
`Full.cotangentComplex` from `Full.lean`:
```
H⁻¹(L_{S/R}) ⊗_S T → H⁻¹(L_{T/R}) → H⁻¹(L_{T/S})
  → H⁰(L_{S/R}) ⊗_S T → H⁰(L_{T/R}) → H⁰(L_{T/S}) → 0.
```
Four of the five arrows, together with their exactness, and the final surjectivity, are already
provided *unconditionally* (no flatness needed) by `Full.lean`'s `Full.jzH1Map`, `Full.jzDelta`,
`Full.jzBaseChange`, `Full.jzOmegaMap`, transported from Mathlib's `Algebra.H1Cotangent.map`,
`Algebra.H1Cotangent.δ`, `KaehlerDifferential.mapBaseChange`, `KaehlerDifferential.map`. This
file supplies the missing first arrow `jzH1BaseChange : H⁻¹(L_{S/R}) ⊗_S T ⟶ H⁻¹(L_{T/R})`,
obtained from Mathlib's `Algebra.H1Cotangent.map` lifted along the base change `T ⊗[S] -`, and
its exactness at `H⁻¹(L_{T/R})`, transported from Mathlib's
`Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat` (which, unlike the other four exactness
statements, genuinely needs `[Module.Flat S T]`).

## Main declarations

* `jzH1BaseChange`: the missing base-change map `H¹(L_{S/R}) ⊗_S T ⟶ H⁻¹(L_{T/R})`.
* `exact_jzH1BaseChange_jzH1Map`: exactness at `H⁻¹(L_{T/R})`, given `[Module.Flat S T]`.
* `jzH1BaseChangeₗ`, `jzH1Mapₗ`, `jzDeltaₗ`, `jzBaseChangeₗ`, `jzOmegaMapₗ`: the five maps of the
  sequence, restricted to `R`-linear maps between their underlying Mathlib objects (all five are
  manifestly linear over the *base ring* `R` of the extensions involved, in addition to being
  linear over their displayed intermediate ring).
* `TransitivitySequence`, `transitivitySequence`: the bundled six-term sequence (five maps and
  five exactness/surjectivity statements), for any tower with `T` flat over `S`.
* `bijective_jzBaseChange_of_formallyEtale`: for `S → T` formally étale (no flatness needed),
  `Full.jzBaseChange R S T` is bijective, i.e. `H⁰(L_{S/R}) ⊗_S T ≅ H⁰(L_{T/R})`.
* `hZeroBaseChangeIso`: the resulting isomorphism `H⁰(L_{S/R}) ⊗_S T ≅ H⁰(L_{T/R})`.
* `surjective_jzH1BaseChange_of_formallyEtale`: for `S → T` formally étale and `T` flat over `S`,
  `jzH1BaseChange` is surjective.

## Not done here

* The distinguished triangle `L_{S/R} ⊗ᴸ T ⟶ L_{T/R} ⟶ L_{T/S} ⟶ (+1)` in `DerivedCategory` (the
  mapping cone realising this exact sequence) is **not** constructed: this repository has no
  flat-base-change comparison for the derived category of modules and no mapping-cone
  machinery in `CotangentComplex/`.
* Consequently `jzH1BaseChange` is shown to be *surjective* under `[Module.Flat S T]` and
  `[Algebra.FormallyEtale S T]`, not bijective. Mathlib's own route to an isomorphism
  `T ⊗[S] H¹(L_{S/R}) ≃ H¹(L_{T/R})` for a general formally étale map
  (`Algebra.Extension.tensorH1CotangentOfFormallyEtale`) additionally needs a *compatible
  presentation pair* on the level of the chosen presentations of `S/R` and `T/R`, which is not
  constructed here (this matches the assessment already recorded in `Global.lean`'s own
  "not done" notes for the missing flat base change of the cotangent complex).
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Transitivity

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-! ### The missing first arrow -/

/-- The base-change map `H¹(L_{S/R}) ⊗_S T ⟶ H⁻¹(L_{T/R})`, the missing first arrow of the
six-term Jacobi--Zariski sequence: Mathlib's `Algebra.H1Cotangent.map R R S T`, lifted along the
base change `T ⊗[S] -`, transported into the cohomology of `Full.cotangentComplex`. -/
noncomputable def jzH1BaseChange :
    ModuleCat.of T (T ⊗[S] Algebra.H1Cotangent R S) ⟶
      Full.cohomology (Full.cotangentComplex R T) (-1) :=
  ModuleCat.ofHom ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) ≫
    (Full.cohomologyNegOne R T).inv

/-- Exactness of the Jacobi--Zariski sequence at `H⁻¹(L_{T/R})`, given `T` flat over `S`:
transported from Mathlib's `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`. -/
theorem exact_jzH1BaseChange_jzH1Map [Module.Flat S T] :
    Function.Exact (jzH1BaseChange R S T).hom (Full.jzH1Map R S T).hom := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := LinearEquiv.refl T (T ⊗[S] Algebra.H1Cotangent R S))
    (e₂ := (Full.cohomologyNegOne R T).toLinearEquiv.symm)
    (e₃ := (Full.cohomologyNegOne S T).toLinearEquiv.symm) ?_ ?_
    (Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat R S T)
  · refine LinearMap.ext fun x => ?_
    simp only [jzH1BaseChange, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearEquiv.refl_apply]
    rw [Full.iso_symm_apply_eq_inv]
  · refine LinearMap.ext fun x => ?_
    simp only [Full.jzH1Map, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    rw [Full.iso_hom_symm_apply, Full.iso_symm_apply_eq_inv]

/-! ### `R`-linearity of the five maps -/

/-- `jzH1BaseChange`'s underlying Mathlib map, as an `R`-linear map (in addition to being
`T`-linear): both `Algebra.H1Cotangent R S` and `Algebra.H1Cotangent R T` are `R`-modules since
`R` is the base ring of the extensions defining them. -/
noncomputable def jzH1BaseChangeₗ :
    T ⊗[S] Algebra.H1Cotangent R S →ₗ[R] Algebra.H1Cotangent R T :=
  ((Algebra.H1Cotangent.map R R S T).liftBaseChange T).restrictScalars R

/-- `Full.jzH1Map`'s underlying Mathlib map, as an `R`-linear map. -/
noncomputable def jzH1Mapₗ : Algebra.H1Cotangent R T →ₗ[R] Algebra.H1Cotangent S T :=
  (Algebra.H1Cotangent.map R S T T).restrictScalars R

/-- `Full.jzDelta`'s underlying Mathlib map, as an `R`-linear map. -/
noncomputable def jzDeltaₗ : Algebra.H1Cotangent S T →ₗ[R] T ⊗[S] Ω[S⁄R] :=
  (Algebra.H1Cotangent.δ R S T).restrictScalars R

/-- `Full.jzBaseChange`'s underlying Mathlib map, as an `R`-linear map. -/
noncomputable def jzBaseChangeₗ : T ⊗[S] Ω[S⁄R] →ₗ[R] Ω[T⁄R] :=
  (KaehlerDifferential.mapBaseChange R S T).restrictScalars R

/-- `Full.jzOmegaMap`'s underlying Mathlib map, as an `R`-linear map. -/
noncomputable def jzOmegaMapₗ : Ω[T⁄R] →ₗ[R] Ω[T⁄S] :=
  (KaehlerDifferential.map R S T T).restrictScalars R

/-! ### The bundled six-term sequence -/

/-- The transitivity (Jacobi--Zariski) six-term exact sequence relating the cohomology of the
`Full.cotangentComplex` for a tower `R → S → T` with `T` flat over `S`:
```
H⁻¹(L_{S/R}) ⊗_S T → H⁻¹(L_{T/R}) → H⁻¹(L_{T/S})
  → H⁰(L_{S/R}) ⊗_S T → H⁰(L_{T/R}) → H⁰(L_{T/S}) → 0.
```
All five maps are morphisms of `ModuleCat.{u} T` (hence `T`-linear), and by
`jzH1BaseChangeₗ`–`jzOmegaMapₗ` are also `R`-linear. -/
structure TransitivitySequence (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Module.Flat S T] where
  /-- `H⁻¹(L_{S/R}) ⊗_S T ⟶ H⁻¹(L_{T/R})`. -/
  hMinusOneBaseChange :
    ModuleCat.of T (T ⊗[S] Algebra.H1Cotangent R S) ⟶
      Full.cohomology (Full.cotangentComplex R T) (-1)
  /-- `H⁻¹(L_{T/R}) ⟶ H⁻¹(L_{T/S})`. -/
  hMinusOneMap :
    Full.cohomology (Full.cotangentComplex R T) (-1) ⟶
      Full.cohomology (Full.cotangentComplex S T) (-1)
  /-- The connecting map `H⁻¹(L_{T/S}) ⟶ H⁰(L_{S/R}) ⊗_S T`. -/
  delta :
    Full.cohomology (Full.cotangentComplex S T) (-1) ⟶ ModuleCat.of T (T ⊗[S] Ω[S⁄R])
  /-- `H⁰(L_{S/R}) ⊗_S T ⟶ H⁰(L_{T/R})`. -/
  hZeroBaseChange : ModuleCat.of T (T ⊗[S] Ω[S⁄R]) ⟶ Full.cohomology (Full.cotangentComplex R T) 0
  /-- `H⁰(L_{T/R}) ⟶ H⁰(L_{T/S})`. -/
  hZeroMap :
    Full.cohomology (Full.cotangentComplex R T) 0 ⟶ Full.cohomology (Full.cotangentComplex S T) 0
  /-- Exactness at `H⁻¹(L_{T/R})`. -/
  exact_hMinusOneBaseChange_hMinusOneMap :
    Function.Exact hMinusOneBaseChange.hom hMinusOneMap.hom
  /-- Exactness at `H⁻¹(L_{T/S})`. -/
  exact_hMinusOneMap_delta : Function.Exact hMinusOneMap.hom delta.hom
  /-- Exactness at `H⁰(L_{S/R}) ⊗_S T`. -/
  exact_delta_hZeroBaseChange : Function.Exact delta.hom hZeroBaseChange.hom
  /-- Exactness at `H⁰(L_{T/R})`. -/
  exact_hZeroBaseChange_hZeroMap : Function.Exact hZeroBaseChange.hom hZeroMap.hom
  /-- The sequence ends in a surjection onto `H⁰(L_{T/S})`. -/
  surjective_hZeroMap : Function.Surjective hZeroMap.hom

/-- The transitivity sequence exists for every tower `R → S → T` with `T` flat over `S`, built
from `jzH1BaseChange` together with `Full.lean`'s `jzH1Map`, `jzDelta`, `jzBaseChange`,
`jzOmegaMap` and their (transported) exactness theorems. -/
noncomputable def transitivitySequence [Module.Flat S T] : TransitivitySequence R S T where
  hMinusOneBaseChange := jzH1BaseChange R S T
  hMinusOneMap := Full.jzH1Map R S T
  delta := Full.jzDelta R S T
  hZeroBaseChange := Full.jzBaseChange R S T
  hZeroMap := Full.jzOmegaMap R S T
  exact_hMinusOneBaseChange_hMinusOneMap := exact_jzH1BaseChange_jzH1Map R S T
  exact_hMinusOneMap_delta := Full.exact_jzH1Map_jzDelta R S T
  exact_delta_hZeroBaseChange := Full.exact_jzDelta_jzBaseChange R S T
  exact_hZeroBaseChange_hZeroMap := Full.exact_jzBaseChange_jzOmegaMap R S T
  surjective_hZeroMap := Full.surjective_jzOmegaMap R S T

/-! ### The étale corollary feeding atlas descent -/

/-- Along a formally étale map `S → T`, both cohomology groups of `L_{T/S}` vanish (this is
`Full.formallyEtale_iff` applied to the pair `(S, T)`). -/
theorem isZero_cohomology_of_formallyEtale [Algebra.FormallyEtale S T] :
    IsZero (Full.cohomology (Full.cotangentComplex S T) 0) ∧
      IsZero (Full.cohomology (Full.cotangentComplex S T) (-1)) :=
  (Full.formallyEtale_iff S T).mp inferInstance

/-- Along a formally étale map `S → T`, `Full.jzBaseChange` is bijective: this is the
"H⁰(L_{S/R}) ⊗_S T ≅ H⁰(L_{T/R})" atlas-compatibility statement, and needs *no* flatness
hypothesis (only the vanishing of both cohomology groups of `L_{T/S}`, via exactness on either
side of `Full.jzBaseChange` in the unconditional five-term Jacobi--Zariski sequence). -/
theorem bijective_jzBaseChange_of_formallyEtale [Algebra.FormallyEtale S T] :
    Function.Bijective (Full.jzBaseChange R S T).hom := by
  have h0 : Subsingleton (Full.cohomology (Full.cotangentComplex S T) 0) :=
    ModuleCat.isZero_iff_subsingleton.mp (isZero_cohomology_of_formallyEtale S T).1
  have h1 : Subsingleton (Full.cohomology (Full.cotangentComplex S T) (-1)) :=
    ModuleCat.isZero_iff_subsingleton.mp (isZero_cohomology_of_formallyEtale S T).2
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Full.exact_jzDelta_jzBaseChange R S T x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro x
    have hz : (Full.jzOmegaMap R S T).hom x = 0 := Subsingleton.elim _ _
    exact (Full.exact_jzBaseChange_jzOmegaMap R S T x).mp hz

/-- Along a formally étale map `S → T`, `Full.jzBaseChange` is an isomorphism, i.e.
`H⁰(L_{S/R}) ⊗_S T ≅ H⁰(L_{T/R})`. -/
theorem isIso_jzBaseChange_of_formallyEtale [Algebra.FormallyEtale S T] :
    IsIso (Full.jzBaseChange R S T) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_jzBaseChange_of_formallyEtale R S T

/-- The isomorphism `H⁰(L_{S/R}) ⊗_S T ≅ H⁰(L_{T/R})` for `S → T` formally étale, feeding
atlas descent in degree `0`. -/
noncomputable def hZeroBaseChangeIso [Algebra.FormallyEtale S T] :
    ModuleCat.of T (T ⊗[S] Ω[S⁄R]) ≅ Full.cohomology (Full.cotangentComplex R T) 0 :=
  haveI := isIso_jzBaseChange_of_formallyEtale R S T
  asIso (Full.jzBaseChange R S T)

/-- Along a formally étale map `S → T` with `T` flat over `S`, `jzH1BaseChange` is surjective:
the "H⁻¹" half of the atlas-compatibility statement, weaker than an isomorphism (see the
module docstring's "Not done here" section for why bijectivity is not established here). -/
theorem surjective_jzH1BaseChange_of_formallyEtale [Module.Flat S T] [Algebra.FormallyEtale S T] :
    Function.Surjective (jzH1BaseChange R S T).hom := by
  have h1 : Subsingleton (Full.cohomology (Full.cotangentComplex S T) (-1)) :=
    ModuleCat.isZero_iff_subsingleton.mp (isZero_cohomology_of_formallyEtale S T).2
  intro x
  have hz : (Full.jzH1Map R S T).hom x = 0 := Subsingleton.elim _ _
  exact (exact_jzH1BaseChange_jzH1Map R S T x).mp hz

end Transitivity

end GromovWitten.AlgebraicGeometry.CotangentComplex
