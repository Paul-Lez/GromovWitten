/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VectorBundleTrivial
import GromovWitten.AlgebraicGeometry.RelativeSpecAffineHom
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyGlobal

/-!
# Injectivity of the global flat pullback along a globally trivialised bundle

This file globalises the rank induction of `IntersectionTheory/BundleHomotopyInjective.lean` to a
vector bundle of finite rank over a scheme `X` which is compact and locally of finite type over a
field: injectivity of the flat pullback in rank one (the theorem proved in
`IntersectionTheory/LineBundleInjective.lean`, taken here as an explicit hypothesis
`RankOneInjective`) implies injectivity in every finite rank, for every bundle admitting a global
trivialisation.

The induction step needs the *tower*: the trivial bundle of rank `Option ι'` over `X` is the
trivial line bundle over the total space `E'` of the trivial bundle of rank `ι'` over `X`.  Both
total spaces are relative `Spec`s over `X`: the second one because the composite
`(trivialData E' PUnit).totalSpace ⟶ E' ⟶ X` is an affine morphism, so
`RelativeSpec.AlgebraData.ofAffineHom` turns it into a quasi-coherent algebra on `X`, whose ring
over an affine open `W` of `X` is computed by `RelativeSpec.ringEquivGamma` (twice) to be
`MvPolynomial PUnit (MvPolynomial ι' Γ(X, W))`.  Comparing it with
`MvPolynomial (Option ι') Γ(X, W)` gives an isomorphism of algebra data over `X` and hence the
isomorphism of total spaces `towerIso`.

## Main declarations

* `RankOneInjective k`: the rank-one injectivity statement over the field `k`, quantified over all
  compact schemes locally of finite type over `k`; it is the theorem of
  `IntersectionTheory/LineBundleInjective.lean` and is a hypothesis of every theorem below.
* `bundlePoint_specializes_of_specializes`, `bundlePoint_map_of_isIso'`,
  `pullbackOpen_pullbackBundle_of_isIso`, `pullbackOpen_pullbackBundle_tower`: transport of the
  generic points of the fibres and of the flat pullback of cycles along an isomorphism of total
  spaces over the base, including the tower case.
* `towerIso`: the isomorphism `(trivialData E' PUnit).totalSpace ≅
  (trivialData X (Option ι')).totalSpace` over `X`.
* `pullbackBundle_trivialData_injective`: injectivity in every finite rank for the trivial bundle.
* `pullbackBundle_injective_of_globalTrivialisation`: the same for a globally trivialised bundle.
* `chowPullbackBundleGlobal_injective`: the resulting injectivity on rational Chow groups.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobal

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
open GromovWitten.AlgebraicGeometry.RelativeSpec
open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen res)

/-! ## Generic points of fibres and isomorphisms of total spaces -/

section Transport

variable {X : Scheme.{u}} {ι κ : Type u}

/-- The generic point of the fibre over `x` specialises to every point of the total space lying
over a specialisation of `x`. -/
theorem bundlePoint_specializes_of_specializes (𝓑 : BundleData X ι) {x : X} {q : 𝓑.totalSpace}
    (h : x ⤳ 𝓑.proj.base q) : bundlePoint 𝓑 x ⤳ q := by
  set j := chartIndex 𝓑 (𝓑.proj.base q) with hj
  have hq : 𝓑.proj.base q ∈ (𝓑.chart j).1 := mem_chart_chartIndex 𝓑 _
  have hx : x ∈ (𝓑.chart j).1 := h.mem_open (𝓑.chart j).1.2 hq
  have hbp : bundlePoint 𝓑 x = 𝓑.chartBundlePoint j ⟨x, hx⟩ :=
    bundlePoint_chart 𝓑 j ⟨x, hx⟩
  rw [hbp]
  exact (chartBundlePoint_specializes_iff 𝓑 j ⟨x, hx⟩ q hq).mpr h

/-- Two bundles over the same base, of possibly different ranks, with an isomorphism of total
spaces over the base, have matching generic fibre points. -/
theorem bundlePoint_map_of_isIso' {𝓑 : BundleData X ι} {𝓒 : BundleData X κ}
    (φ : 𝓑.totalSpace ≅ 𝓒.totalSpace) (hφ : φ.hom ≫ 𝓒.proj = 𝓑.proj) (x : X) :
    φ.hom.base (bundlePoint 𝓑 x) = bundlePoint 𝓒 x := by
  have hφ' : φ.inv ≫ 𝓑.proj = 𝓒.proj := by
    rw [← hφ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hproj : ∀ q : 𝓑.totalSpace, 𝓒.proj.base (φ.hom.base q) = 𝓑.proj.base q := fun q ↦
    congrArg (fun g : 𝓑.totalSpace ⟶ X ↦ g.base q) hφ
  have hproj' : ∀ q : 𝓒.totalSpace, 𝓑.proj.base (φ.inv.base q) = 𝓒.proj.base q := fun q ↦
    congrArg (fun g : 𝓒.totalSpace ⟶ X ↦ g.base q) hφ'
  have hinv : ∀ q : 𝓒.totalSpace, φ.hom.base (φ.inv.base q) = q := fun q ↦
    congrArg (fun g : 𝓒.totalSpace ⟶ 𝓒.totalSpace ↦ g.base q) φ.inv_hom_id
  have h₁ : φ.hom.base (bundlePoint 𝓑 x) ⤳ bundlePoint 𝓒 x := by
    have hspec : bundlePoint 𝓑 x ⤳ φ.inv.base (bundlePoint 𝓒 x) :=
      VectorBundleTotalSpace.bundlePoint_specializes 𝓑 x _ (by rw [hproj', proj_bundlePoint])
    have := hspec.map φ.hom.continuous
    rwa [hinv] at this
  have h₂ : bundlePoint 𝓒 x ⤳ φ.hom.base (bundlePoint 𝓑 x) :=
    VectorBundleTotalSpace.bundlePoint_specializes 𝓒 x _ (by rw [hproj, proj_bundlePoint])
  exact (h₁.antisymm h₂).eq

/-- An isomorphism of total spaces over the base matches the flat pullbacks of cycles. -/
theorem pullbackOpen_pullbackBundle_of_isIso {𝓑 : BundleData X ι} {𝓒 : BundleData X κ}
    (φ : 𝓑.totalSpace ≅ 𝓒.totalSpace) (hφ : φ.hom ≫ 𝓒.proj = 𝓑.proj) (w : AlgebraicCycle X ℚ) :
    AlgebraicCycle.pullbackOpen φ.hom (pullbackBundle 𝓒 w) = pullbackBundle 𝓑 w := by
  have hinj : Function.Injective φ.hom.base :=
    Function.LeftInverse.injective (g := φ.inv.base) fun q ↦
      congrArg (fun g : 𝓑.totalSpace ⟶ 𝓑.totalSpace ↦ g.base q) φ.hom_inv_id
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  change pullbackBundle 𝓒 w (φ.hom.base q) = pullbackBundle 𝓑 w q
  by_cases h : q ∈ Set.range (bundlePoint 𝓑)
  · obtain ⟨y, rfl⟩ := h
    rw [bundlePoint_map_of_isIso' φ hφ, pullbackBundle_apply_bundlePoint,
      pullbackBundle_apply_bundlePoint]
  · have hne : φ.hom.base q ∉ Set.range (bundlePoint 𝓒) := by
      rintro ⟨y, hy⟩
      exact h ⟨y, hinj (by rw [bundlePoint_map_of_isIso' φ hφ, hy])⟩
    rw [pullbackBundle_eq_zero_of_notMem _ _ hne, pullbackBundle_eq_zero_of_notMem _ _ h]

end Transport

/-! ## The tower of two bundles -/

section Tower

variable {X : Scheme.{u}} {ι κ lam : Type u} {𝓑 : BundleData X ι}
  {𝓕 : BundleData 𝓑.totalSpace κ} {𝓒 : BundleData X lam}

/-- In a tower of two bundles, the generic point of the fibre of the composite is the generic
fibre point of the second bundle at the generic fibre point of the first. -/
theorem bundlePoint_tower (φ : 𝓕.totalSpace ≅ 𝓒.totalSpace)
    (hφ : φ.hom ≫ 𝓒.proj = 𝓕.proj ≫ 𝓑.proj) (x : X) :
    φ.hom.base (bundlePoint 𝓕 (bundlePoint 𝓑 x)) = bundlePoint 𝓒 x := by
  have hφ' : φ.inv ≫ 𝓕.proj ≫ 𝓑.proj = 𝓒.proj := by
    rw [← hφ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hproj : ∀ q : 𝓕.totalSpace,
      𝓒.proj.base (φ.hom.base q) = 𝓑.proj.base (𝓕.proj.base q) := fun q ↦
    congrArg (fun g : 𝓕.totalSpace ⟶ X ↦ g.base q) hφ
  have hproj' : ∀ q : 𝓒.totalSpace,
      𝓑.proj.base (𝓕.proj.base (φ.inv.base q)) = 𝓒.proj.base q := fun q ↦
    congrArg (fun g : 𝓒.totalSpace ⟶ X ↦ g.base q) hφ'
  have hinv : ∀ q : 𝓒.totalSpace, φ.hom.base (φ.inv.base q) = q := fun q ↦
    congrArg (fun g : 𝓒.totalSpace ⟶ 𝓒.totalSpace ↦ g.base q) φ.inv_hom_id
  have h₂ : bundlePoint 𝓒 x ⤳ φ.hom.base (bundlePoint 𝓕 (bundlePoint 𝓑 x)) :=
    VectorBundleTotalSpace.bundlePoint_specializes 𝓒 x _ (by
      rw [hproj, proj_bundlePoint, proj_bundlePoint])
  have h₁ : φ.hom.base (bundlePoint 𝓕 (bundlePoint 𝓑 x)) ⤳ bundlePoint 𝓒 x := by
    have hbase : 𝓑.proj.base (𝓕.proj.base (φ.inv.base (bundlePoint 𝓒 x))) = x := by
      rw [hproj', proj_bundlePoint]
    have hspec : bundlePoint 𝓑 x ⤳ 𝓕.proj.base (φ.inv.base (bundlePoint 𝓒 x)) :=
      VectorBundleTotalSpace.bundlePoint_specializes 𝓑 x _ hbase
    have hspec2 : bundlePoint 𝓕 (bundlePoint 𝓑 x) ⤳ φ.inv.base (bundlePoint 𝓒 x) :=
      bundlePoint_specializes_of_specializes 𝓕 hspec
    have := hspec2.map φ.hom.continuous
    rwa [hinv] at this
  exact (h₁.antisymm h₂).eq

/-- The flat pullback along a tower of two bundles is the composite of the two flat pullbacks. -/
theorem pullbackOpen_pullbackBundle_tower (φ : 𝓕.totalSpace ≅ 𝓒.totalSpace)
    (hφ : φ.hom ≫ 𝓒.proj = 𝓕.proj ≫ 𝓑.proj) (w : AlgebraicCycle X ℚ) :
    AlgebraicCycle.pullbackOpen φ.hom (pullbackBundle 𝓒 w) =
      pullbackBundle 𝓕 (pullbackBundle 𝓑 w) := by
  have hinj : Function.Injective φ.hom.base :=
    Function.LeftInverse.injective (g := φ.inv.base) fun q ↦
      congrArg (fun g : 𝓕.totalSpace ⟶ 𝓕.totalSpace ↦ g.base q) φ.hom_inv_id
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  change pullbackBundle 𝓒 w (φ.hom.base q) = pullbackBundle 𝓕 (pullbackBundle 𝓑 w) q
  by_cases h : q ∈ Set.range (bundlePoint 𝓕) ∧ 𝓕.proj.base q ∈ Set.range (bundlePoint 𝓑)
  · obtain ⟨⟨y, rfl⟩, ⟨x, hx⟩⟩ := h
    rw [proj_bundlePoint] at hx
    subst hx
    rw [bundlePoint_tower φ hφ, pullbackBundle_apply_bundlePoint,
      pullbackBundle_apply_bundlePoint, pullbackBundle_apply_bundlePoint]
  · have hne : φ.hom.base q ∉ Set.range (bundlePoint 𝓒) := by
      rintro ⟨x, hx⟩
      refine h ⟨⟨bundlePoint 𝓑 x, hinj ?_⟩, ?_⟩
      · rw [bundlePoint_tower φ hφ, hx]
      · have hq : q = bundlePoint 𝓕 (bundlePoint 𝓑 x) := hinj (by rw [bundlePoint_tower φ hφ, hx])
        rw [hq, proj_bundlePoint]
        exact ⟨x, rfl⟩
    rw [pullbackBundle_eq_zero_of_notMem _ _ hne]
    by_cases h' : q ∈ Set.range (bundlePoint 𝓕)
    · obtain ⟨y, rfl⟩ := h'
      rw [pullbackBundle_apply_bundlePoint, proj_bundlePoint] at *
      exact (pullbackBundle_eq_zero_of_notMem 𝓑 w (fun hy ↦ h ⟨⟨y, rfl⟩, hy⟩)).symm
    · exact (pullbackBundle_eq_zero_of_notMem _ _ h').symm

end Tower

/-! ## Transport of rational relations -/

section Relations

variable {A B : Scheme.{u}}

/-- Rational relations transport along an isomorphism of schemes. -/
theorem mem_totalRationalRelations_of_iso (ε : A ≅ B) (dimA : DimensionFunction A)
    (dimB : DimensionFunction B) (z : AlgebraicCycle B ℚ)
    (hz : z ∈ totalRationalRelations B dimB) :
    AlgebraicCycle.pullbackOpen ε.hom z ∈ totalRationalRelations A dimA := by
  rw [← VectorBundleTotalSpace.totalRationalRelations_map_pullbackOpenLinear ε dimA dimB]
  exact ⟨z, hz, rfl⟩

end Relations

/-! ## The comparison of polynomial rings in the tower -/

section OptionComparison

variable (ι' : Type u) (A B : Type u) [CommRing A] [CommRing B]

/-- The comparison isomorphism `A[Option ι'] ≃ (A[ι'])[PUnit]` of the rank tower. -/
noncomputable def optionComparison :
    MvPolynomial (Option ι') A ≃ₐ[A] MvPolynomial PUnit.{u + 1} (MvPolynomial ι' A) :=
  (MvPolynomial.renameEquiv A
      ((Equiv.optionEquivSumPUnit ι').trans (Equiv.sumComm ι' PUnit.{u + 1}))).trans
    (MvPolynomial.sumAlgEquiv A PUnit.{u + 1} ι')

@[simp]
theorem optionComparison_C (a : A) :
    optionComparison ι' A (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp [optionComparison]

@[simp]
theorem optionComparison_X_none :
    optionComparison ι' A (MvPolynomial.X none) = MvPolynomial.X PUnit.unit := by
  simp [optionComparison]

@[simp]
theorem optionComparison_X_some (i : ι') :
    optionComparison ι' A (MvPolynomial.X (some i)) =
      MvPolynomial.C (MvPolynomial.X i) := by
  simp [optionComparison]

/-- The comparison isomorphism is natural in the coefficient ring. -/
theorem optionComparison_map (f : A →+* B) (p : MvPolynomial (Option ι') A) :
    optionComparison ι' B (MvPolynomial.map f p) =
      MvPolynomial.map (MvPolynomial.map f) (optionComparison ι' A p) := by
  have h : ((optionComparison ι' B).toAlgHom.toRingHom.comp (MvPolynomial.map f) :
      MvPolynomial (Option ι') A →+* MvPolynomial PUnit.{u + 1} (MvPolynomial ι' B)) =
      (MvPolynomial.map (MvPolynomial.map f)).comp
        (optionComparison ι' A).toAlgHom.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · rintro (_ | i) <;> simp
  exact congrArg (fun r : MvPolynomial (Option ι') A →+*
    MvPolynomial PUnit.{u + 1} (MvPolynomial ι' B) ↦ r p) h

end OptionComparison

/-! ## The tower isomorphism -/

section TowerConstruction

/- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
type of affine opens; as in Mathlib's own development of that cover, the unifier is told not to
respect transparency in this section. -/
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u}) (ι' : Type u)

/-- The base of the rank tower: the total space of the trivial bundle of rank `ι'`. -/
noncomputable abbrev towerBase : Scheme.{u} := (trivialData X ι').totalSpace

/-- The top of the rank tower: the total space of the trivial line bundle over `towerBase`. -/
noncomputable abbrev towerTop : Scheme.{u} :=
  (trivialData (towerBase X ι') PUnit.{u + 1}).totalSpace

/-- The projection of the top of the tower to `X`. -/
noncomputable abbrev towerProj : towerTop X ι' ⟶ X :=
  (trivialData (towerBase X ι') PUnit.{u + 1}).proj ≫ (trivialData X ι').proj

/-- The quasi-coherent algebra on `X` attached to the tower. -/
noncomputable abbrev towerAlgebra : AlgebraData X := AlgebraData.ofAffineHom (towerProj X ι')

/-- The affine open of the total space of the trivial bundle lying over an affine open of the
base. -/
noncomputable def trivialChart {Y : Scheme.{u}} (kappa : Type u) (U : Y.affineOpens) :
    (trivialData Y kappa).totalSpace.affineOpens :=
  ⟨(trivialData Y kappa).proj ⁻¹ᵁ U.1, U.2.preimage _⟩

/-- The chart construction is monotone. -/
theorem trivialChart_mono {Y : Scheme.{u}} (kappa : Type u) {U V : Y.affineOpens} (h : U ≤ V) :
    trivialChart kappa U ≤ trivialChart kappa V :=
  (trivialData Y kappa).proj.preimage_mono (h : U.1 ≤ V.1)

/-- The sections of the trivial bundle over the preimage of an affine open form the polynomial
ring over the sections of that open. -/
noncomputable def trivialGamma {Y : Scheme.{u}} (kappa : Type u) (U : Y.affineOpens) :
    MvPolynomial kappa Γ(Y, U.1) ≃+*
      Γ((trivialData Y kappa).totalSpace, (trivialChart kappa U).1) :=
  ringEquivGamma Y (trivialAlgebraData Y kappa) U

/-- Constants go to pullbacks of sections of the base. -/
theorem trivialGamma_C {Y : Scheme.{u}} (kappa : Type u) (U : Y.affineOpens) (r : Γ(Y, U.1)) :
    trivialGamma kappa U (MvPolynomial.C r) = (trivialData Y kappa).proj.app U.1 r :=
  ringEquivGamma_algebraMap Y (trivialAlgebraData Y kappa) U r

/-- Compatibility with the restriction maps. -/
theorem trivialGamma_map {Y : Scheme.{u}} (kappa : Type u) {U V : Y.affineOpens} (h : U ≤ V)
    (a : MvPolynomial kappa Γ(Y, V.1)) :
    trivialGamma kappa U (MvPolynomial.map (res Y h) a) =
      res (trivialData Y kappa).totalSpace (trivialChart_mono kappa h) (trivialGamma kappa V a) :=
  ringEquivGamma_map Y (trivialAlgebraData Y kappa) h a

/-- The sections of the tower over an affine open of `X` form a polynomial ring in
`Option ι'` variables over the sections of `X`. -/
noncomputable def towerEquiv (W : X.affineOpens) :
    MvPolynomial (Option ι') Γ(X, W.1) ≃+* (towerAlgebra X ι').ring W :=
  ((optionComparison ι' Γ(X, W.1)).toRingEquiv.trans
      (MvPolynomial.mapEquiv PUnit.{u + 1} (trivialGamma ι' W))).trans
    (trivialGamma PUnit.{u + 1} (trivialChart ι' W))

/-- The tower comparison, unfolded. -/
theorem towerEquiv_apply (W : X.affineOpens) (p : MvPolynomial (Option ι') Γ(X, W.1)) :
    towerEquiv X ι' W p = trivialGamma PUnit.{u + 1} (trivialChart ι' W)
      (MvPolynomial.map ((trivialGamma ι' W : _ →+* _)) (optionComparison ι' Γ(X, W.1) p)) :=
  rfl

/-- The tower comparison is `Γ(X, W)`-linear. -/
theorem towerEquiv_algebraMap (W : X.affineOpens) (r : Γ(X, W.1)) :
    towerEquiv X ι' W (algebraMap Γ(X, W.1) (MvPolynomial (Option ι') Γ(X, W.1)) r) =
      algebraMap Γ(X, W.1) ((towerAlgebra X ι').ring W) r := by
  have hC : algebraMap Γ(X, W.1) (MvPolynomial (Option ι') Γ(X, W.1)) r = MvPolynomial.C r := rfl
  rw [hC, towerEquiv_apply, optionComparison_C, MvPolynomial.map_C, trivialGamma_C,
    RingEquiv.coe_toRingHom, trivialGamma_C]
  rfl

/-- The tower comparison, as a morphism of algebras over the sections of `X`. -/
noncomputable def towerHomApp (W : X.affineOpens) :
    MvPolynomial (Option ι') Γ(X, W.1) →ₐ[Γ(X, W.1)] (towerAlgebra X ι').ring W :=
  { (towerEquiv X ι' W).toRingHom with commutes' := towerEquiv_algebraMap X ι' W }

/-- The tower comparison is compatible with the restriction maps. -/
theorem towerEquiv_map {W V : X.affineOpens} (h : W ≤ V)
    (p : MvPolynomial (Option ι') Γ(X, V.1)) :
    towerEquiv X ι' W (MvPolynomial.map (res X h) p) =
      (towerAlgebra X ι').map h (towerEquiv X ι' V p) := by
  have h' : trivialChart ι' W ≤ trivialChart ι' V := trivialChart_mono ι' h
  have hr1 : (((trivialGamma ι' W : _ →+* _)).comp (MvPolynomial.map (res X h)) :
        MvPolynomial ι' Γ(X, V.1) →+* Γ((trivialData X ι').totalSpace, (trivialChart ι' W).1)) =
      ((res (trivialData X ι').totalSpace h').comp ((trivialGamma ι' V : _ →+* _))) :=
    RingHom.ext fun a ↦ trivialGamma_map ι' h a
  have hkey : MvPolynomial.map ((trivialGamma ι' W : _ →+* _))
        (MvPolynomial.map (MvPolynomial.map (res X h)) (optionComparison ι' Γ(X, V.1) p)) =
      MvPolynomial.map (res (trivialData X ι').totalSpace h')
        (MvPolynomial.map ((trivialGamma ι' V : _ →+* _))
          (optionComparison ι' Γ(X, V.1) p)) := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    exact congrArg (fun f : MvPolynomial ι' Γ(X, V.1) →+*
      Γ((trivialData X ι').totalSpace, (trivialChart ι' W).1) ↦
        MvPolynomial.map f (optionComparison ι' Γ(X, V.1) p)) hr1
  rw [towerEquiv_apply, optionComparison_map, hkey]
  exact trivialGamma_map PUnit.{u + 1} h' _

/-- The tower comparison as a morphism of quasi-coherent algebras on `X`. -/
noncomputable def towerHom :
    RelativeSpec.Hom X (towerAlgebra X ι') (trivialAlgebraData X (Option ι')) where
  app := towerHomApp X ι'
  naturality h := RingHom.ext fun p ↦ towerEquiv_map X ι' h p

instance isIso_towerHom_map : IsIso (towerHom X ι').map :=
  RelativeSpec.Hom.isIso_map _ fun U ↦ (towerEquiv X ι' U).bijective

/-- **The rank tower**: the trivial line bundle over the total space of the trivial bundle of
rank `ι'` is the trivial bundle of rank `Option ι'`. -/
noncomputable def towerIso : towerTop X ι' ≅ (trivialData X (Option ι')).totalSpace :=
  (relativeSpecOfAffineHomIso (towerProj X ι')).symm ≪≫ asIso (towerHom X ι').map

/-- The tower isomorphism lies over `X`. -/
theorem towerIso_hom_proj :
    (towerIso X ι').hom ≫ (trivialData X (Option ι')).proj =
      (trivialData (towerBase X ι') PUnit.{u + 1}).proj ≫ (trivialData X ι').proj := by
  have h1 : (towerHom X ι').map ≫ (trivialData X (Option ι')).proj =
      toBase X (towerAlgebra X ι') := RelativeSpec.Hom.map_toBase _
  have h2 : (relativeSpecOfAffineHomIso (towerProj X ι')).hom ≫ towerProj X ι' =
      toBase X (towerAlgebra X ι') := relativeSpecOfAffineHomIso_hom_comp _
  have h3 : (towerIso X ι').hom = (relativeSpecOfAffineHomIso (towerProj X ι')).inv ≫
      (towerHom X ι').map := rfl
  rw [h3, Category.assoc, h1, ← h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The flat pullback along the trivial bundle of rank `Option ι'` is the flat pullback along the
trivial line bundle of the flat pullback along the trivial bundle of rank `ι'`. -/
theorem pullbackOpen_towerIso (w : AlgebraicCycle X ℚ) :
    AlgebraicCycle.pullbackOpen (towerIso X ι').hom
        (pullbackBundle (trivialData X (Option ι')) w) =
      pullbackBundle (trivialData (towerBase X ι') PUnit.{u + 1})
        (pullbackBundle (trivialData X ι') w) :=
  pullbackOpen_pullbackBundle_tower (towerIso X ι') (towerIso_hom_proj X ι') w

end TowerConstruction

/-! ## Renaming the index type, and the bundle of rank zero -/

section Rename

variable {X : Scheme.{u}} {ι kappa : Type u}

/-- Renaming the variables: a morphism of trivial algebra data. -/
noncomputable def renameHomOfEquiv (e : ι ≃ kappa) :
    RelativeSpec.Hom X (trivialAlgebraData X ι) (trivialAlgebraData X kappa) where
  app U := (MvPolynomial.renameEquiv Γ(X, U.1) e.symm).toAlgHom
  naturality h := RingHom.ext fun p ↦ (MvPolynomial.map_rename (res X h) e.symm p).symm

instance isIso_renameHomOfEquiv_map (e : ι ≃ kappa) :
    IsIso (renameHomOfEquiv (X := X) e).map :=
  RelativeSpec.Hom.isIso_map _ fun U ↦ (MvPolynomial.renameEquiv Γ(X, U.1) e.symm).bijective

/-- Renaming the index type: an isomorphism of total spaces over `X`. -/
noncomputable def renameIso (e : ι ≃ kappa) :
    (trivialData X ι).totalSpace ≅ (trivialData X kappa).totalSpace :=
  asIso (renameHomOfEquiv (X := X) e).map

theorem renameIso_inv_proj (e : ι ≃ kappa) :
    (renameIso (X := X) e).inv ≫ (trivialData X ι).proj = (trivialData X kappa).proj := by
  have h : (renameIso (X := X) e).hom ≫ (trivialData X kappa).proj = (trivialData X ι).proj :=
    RelativeSpec.Hom.map_toBase _
  rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Membership in the rational relations is insensitive to a renaming of the variables. -/
theorem mem_relations_of_rename (e : ι ≃ kappa)
    (dimI : DimensionFunction (trivialData X ι).totalSpace)
    (dimK : DimensionFunction (trivialData X kappa).totalSpace) (w : AlgebraicCycle X ℚ)
    (hw : pullbackBundle (trivialData X ι) w ∈
      totalRationalRelations (trivialData X ι).totalSpace dimI) :
    pullbackBundle (trivialData X kappa) w ∈
      totalRationalRelations (trivialData X kappa).totalSpace dimK := by
  have hmem := mem_totalRationalRelations_of_iso (renameIso (X := X) e).symm dimK dimI _ hw
  rwa [pullbackOpen_pullbackBundle_of_isIso (renameIso (X := X) e).symm
    (renameIso_inv_proj e) w] at hmem

/-- The trivial bundle of rank zero: a morphism to the structure algebra. -/
noncomputable def emptyHom (ι : Type u) [IsEmpty ι] :
    RelativeSpec.Hom X (trivialAlgebraData X ι) (structureData X) where
  app U := Algebra.ofId Γ(X, U.1) (MvPolynomial ι Γ(X, U.1))
  naturality h := RingHom.ext fun a ↦ (MvPolynomial.map_C (res X h) (a := a)).symm

instance isIso_proj_trivialData_of_isEmpty (ι : Type u) [IsEmpty ι] :
    IsIso ((trivialData X ι).proj) := by
  have h1 : IsIso (emptyHom (X := X) ι).map :=
    RelativeSpec.Hom.isIso_map _ fun U ↦
      (MvPolynomial.isEmptyAlgEquiv Γ(X, U.1) ι).symm.bijective
  have h2 : (emptyHom (X := X) ι).map ≫ toBase X (structureData X) =
      (trivialData X ι).proj := RelativeSpec.Hom.map_toBase _
  rw [← h2]
  infer_instance

/-- The flat pullback along the trivial bundle of rank zero is the inverse of the projection. -/
theorem pullbackOpen_proj_pullbackBundle_of_isEmpty (ι : Type u) [IsEmpty ι]
    (w : AlgebraicCycle X ℚ) :
    AlgebraicCycle.pullbackOpen (asIso ((trivialData X ι).proj)).symm.hom
        (pullbackBundle (trivialData X ι) w) = w := by
  set ε : X ≅ (trivialData X ι).totalSpace := (asIso ((trivialData X ι).proj)).symm with hε
  have hcomp : ∀ x : X, (trivialData X ι).proj.base (ε.hom.base x) = x := fun x ↦
    congrArg (fun g : X ⟶ X ↦ g.base x) ε.hom_inv_id
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  change pullbackBundle (trivialData X ι) w (ε.hom.base x) = w x
  have hb : ε.hom.base x = bundlePoint (trivialData X ι) x := by
    have hinj : Function.Injective ((trivialData X ι).proj.base) :=
      Function.LeftInverse.injective (g := ε.hom.base) fun q ↦
        congrArg (fun g : (trivialData X ι).totalSpace ⟶ (trivialData X ι).totalSpace ↦ g.base q)
          ε.inv_hom_id
    exact hinj (by rw [hcomp, proj_bundlePoint])
  rw [hb, pullbackBundle_apply_bundlePoint]

/-- Injectivity of the flat pullback along the trivial bundle of rank zero. -/
theorem mem_relations_of_rank_zero (ι : Type u) [IsEmpty ι] (dimX : DimensionFunction X)
    (dimE : DimensionFunction (trivialData X ι).totalSpace) (w : AlgebraicCycle X ℚ)
    (hw : pullbackBundle (trivialData X ι) w ∈
      totalRationalRelations (trivialData X ι).totalSpace dimE) :
    w ∈ totalRationalRelations X dimX := by
  have hmem := mem_totalRationalRelations_of_iso (asIso ((trivialData X ι).proj)).symm dimX dimE
    _ hw
  rwa [pullbackOpen_proj_pullbackBundle_of_isEmpty ι w] at hmem

end Rename

/-! ## The rank induction -/

section Induction

open FiniteTypeDimension

variable {k : Type u} [Field k]

/-- **The rank-one global injectivity statement** over the field `k`: for every compact scheme
`Y` locally of finite type over `k`, a cycle whose flat pullback to the trivial line bundle over
`Y` is a rational relation is itself a rational relation.  This is the theorem of
`IntersectionTheory/LineBundleInjective.lean`; it is an explicit hypothesis of every theorem in
this section. -/
def RankOneInjective (k : Type u) [Field k] : Prop :=
  ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType g] [CompactSpace Y] (w : AlgebraicCycle Y ℚ),
    pullbackBundle (trivialData Y PUnit.{u + 1}) w ∈
        totalRationalRelations (trivialData Y PUnit.{u + 1}).totalSpace
          (dimensionFunction ((trivialData Y PUnit.{u + 1}).proj ≫ g)) →
      w ∈ totalRationalRelations Y (dimensionFunction g)

/-- The rank induction: injectivity in rank one implies injectivity in rank `n`. -/
theorem mem_relations_of_pullbackBundle_trivialData (hrank1 : RankOneInjective k) (n : ℕ) :
    ∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
      [_root_.AlgebraicGeometry.LocallyOfFiniteType f] [CompactSpace X] (ι : Type u) [Finite ι],
      Nat.card ι = n → ∀ w : AlgebraicCycle X ℚ,
      pullbackBundle (trivialData X ι) w ∈
          totalRationalRelations (trivialData X ι).totalSpace
            (dimensionFunction ((trivialData X ι).proj ≫ f)) →
        w ∈ totalRationalRelations X (dimensionFunction f) := by
  induction n with
  | zero =>
    intro X f _ _ ι _ hcard w hw
    have hempty : IsEmpty ι := by
      rcases Nat.card_eq_zero.mp hcard with h | h
      · exact h
      · exact absurd h (not_infinite_iff_finite.mpr inferInstance)
    exact mem_relations_of_rank_zero ι _ _ w hw
  | succ n IH =>
    intro X f _ _ ι _ hcard w hw
    obtain ⟨ι', hfin', e, hcard'⟩ := VectorBundle.exists_option_equiv ι n hcard
    have _ : Finite ι' := hfin'
    have _ : CompactSpace (towerBase X ι') := compactSpace_totalSpace (trivialData X ι')
    have _ : _root_.AlgebraicGeometry.LocallyOfFiniteType ((trivialData X ι').proj ≫ f) :=
      FiniteTypeDimension.locallyOfFiniteType_proj f (trivialData X ι')
    have hw' : pullbackBundle (trivialData X (Option ι')) w ∈
        totalRationalRelations (trivialData X (Option ι')).totalSpace
          (dimensionFunction ((trivialData X (Option ι')).proj ≫ f)) :=
      mem_relations_of_rename e _ _ w hw
    have htower := mem_totalRationalRelations_of_iso (towerIso X ι')
      (dimensionFunction ((trivialData (towerBase X ι') PUnit.{u + 1}).proj ≫
        ((trivialData X ι').proj ≫ f))) _ _ hw'
    rw [pullbackOpen_towerIso] at htower
    exact IH X f ι' hcard' w (hrank1 (towerBase X ι') ((trivialData X ι').proj ≫ f)
      (pullbackBundle (trivialData X ι') w) htower)

/-- **Injectivity of the global flat pullback along a trivial bundle of finite rank**, at the
level of cycles: if the flat pullback of `w` to `X × 𝔸^ι` is a rational relation, then so is `w`.
The rank-one case is the hypothesis `hrank1`. -/
theorem pullbackBundle_trivialData_injective (hrank1 : RankOneInjective k) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [_root_.AlgebraicGeometry.LocallyOfFiniteType f]
    [CompactSpace X] {ι : Type u} [Finite ι] (w : AlgebraicCycle X ℚ)
    (hw : pullbackBundle (trivialData X ι) w ∈
      totalRationalRelations (trivialData X ι).totalSpace
        (dimensionFunction ((trivialData X ι).proj ≫ f))) :
    w ∈ totalRationalRelations X (dimensionFunction f) :=
  mem_relations_of_pullbackBundle_trivialData hrank1 (Nat.card ι) X f ι rfl w hw

/-- **Injectivity of the global flat pullback along a globally trivialised bundle**, at the level
of cycles. -/
theorem pullbackBundle_injective_of_globalTrivialisation (hrank1 : RankOneInjective k)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType f] [CompactSpace X] {ι : Type u} [Finite ι]
    {𝓔 : BundleData X ι} (t : GlobalTrivialisation 𝓔) (w : AlgebraicCycle X ℚ)
    (hw : pullbackBundle 𝓔 w ∈
      totalRationalRelations 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))) :
    w ∈ totalRationalRelations X (dimensionFunction f) := by
  have hproj : t.totalSpaceIso.symm.hom ≫ 𝓔.proj = (trivialData X ι).proj := by
    have h := t.totalSpaceIso_hom_proj
    rw [Iso.symm_hom, ← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hmem := mem_totalRationalRelations_of_iso t.totalSpaceIso.symm
    (dimensionFunction ((trivialData X ι).proj ≫ f)) _ _ hw
  rw [pullbackOpen_pullbackBundle_of_isIso t.totalSpaceIso.symm hproj w] at hmem
  exact pullbackBundle_trivialData_injective hrank1 f w hmem

/-- **Injectivity of the global flat pullback on rational Chow groups** for a globally
trivialised vector bundle of finite rank over a compact scheme locally of finite type over a
field.  This is the map `bundlePullbackFT` of
`VirtualFundamentalClass/GlobalVirtualClass.lean`. -/
theorem chowPullbackBundleGlobal_injective (hrank1 : RankOneInjective k) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [_root_.AlgebraicGeometry.LocallyOfFiniteType f]
    [CompactSpace X] {ι : Type u} [Finite ι] {𝓔 : BundleData X ι}
    (t : GlobalTrivialisation 𝓔) (i : ℤ)
    (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
      (i + (Nat.card ι : ℤ))) :
    Function.Injective (BundleOverSubscheme.chowPullbackBundleGlobal 𝓔 (dimensionFunction f)
      (dimensionFunction (𝓔.proj ≫ f)) (dimensionFunction_bundlePoint f 𝓔) i RX RE) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro α hα
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective RX.relations α
  have h0 : RE.quotientMap (flatPullbackBundleGlobal 𝓔 (dimensionFunction f)
      (dimensionFunction (𝓔.proj ≫ f)) (dimensionFunction_bundlePoint f 𝓔) i z) = 0 :=
    LinearMap.mem_ker.1 hα
  have h1 : flatPullbackBundleGlobal 𝓔 (dimensionFunction f) (dimensionFunction (𝓔.proj ≫ f))
      (dimensionFunction_bundlePoint f 𝓔) i z ∈ RE.relations :=
    (Submodule.Quotient.mk_eq_zero _).1 h0
  have h2 : (z : AlgebraicCycle X ℚ) ∈ totalRationalRelations X (dimensionFunction f) := by
    refine pullbackBundle_injective_of_globalTrivialisation hrank1 f t _ ?_
    cases RE
    exact h1
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  cases RX
  exact h2

end Induction

end GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobal
