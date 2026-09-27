/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.Global
import GromovWitten.AlgebraicGeometry.CotangentComplex.AtlasDescent

/-!
# The cohomology of the cotangent complex as a presheaf on the affine charts

This file packages `H⁰` and `H⁻¹` of the cotangent complex `L_{S/R}` into honest presheaves
of `Γ(Y,V)`-modules on the (Zariski) category of affine charts of a morphism of schemes
`f : X ⟶ Y` over an affine open `V ⊆ Y`, and records their quasi-coherence along étale (in
particular, basic-open) chart refinements.

## Main declarations

* `EtaleChart f V`: the affine charts of `f` over `V` (`Global.AffineChart f V`), ordered by
  inclusion of the underlying affine open and thereby made into a category (a morphism
  `c ⟶ c'` exists iff `c.U ≤ c'.U`).
* `hZeroPresheaf`, `hNegOnePresheaf : (EtaleChart f V)ᵒᵖ ⥤ ModuleCat Γ(Y,V)`: the presheaves
  sending a chart `c` to `Ω[Γ(X,c.U)⁄Γ(Y,V)]`, resp. `Algebra.H1Cotangent Γ(Y,V) Γ(X,c.U)`,
  restricted to `Γ(Y,V)`-modules, with restriction maps `KaehlerDifferential.map`, resp.
  `Algebra.H1Cotangent.map`.
* `hZeroMap_id`, `hZeroMap_comp`, `hNegOneMap_id`, `hNegOneMap_comp`: the presheaf identity and
  composition laws, stated as standalone theorems (these are exactly the `map_id`/`map_comp`
  fields of the two functors above).
* `kaehlerMap_self_apply`, `h1CotangentMap_self_apply`: the ring-theoretic input to the identity
  laws, namely that a self-algebra structure whose structure map is the identity induces the
  identity on `Ω[A⁄R]`, resp. on `Algebra.H1Cotangent R A`.
* `sectionsPresheaf`, `derivationNatTrans`: the presheaf of sections of `X` on the same charts,
  and the universal derivation as a morphism of presheaves `sectionsPresheaf ⟶ hZeroPresheaf`
  (naturality of `d` in the chart).
* `isQuasiCoherent_hZeroPresheaf`, `isQuasiCoherent_hNegOnePresheaf`: along a basic-open
  refinement of charts (a Zariski, hence formally étale, chart transition) the restriction map
  becomes an isomorphism after base change: this is the "quasi-coherent module presheaf on the
  small étale site" content requested for a presheaf of the shape produced here (see the second
  design note below for why a literal `Modules/Stack.lean` `IsQuasiCoherent` term is not
  produced).

## Design notes

* Everything is stated over the *fixed* base ring `R := Γ(Y,V)`: `Ω[Γ(X,c.U)⁄R]` and
  `Algebra.H1Cotangent R Γ(X,c.U)` are viewed via `LinearMap.restrictScalars R` as `R`-modules,
  so that the presheaf genuinely lands in a single fixed category `ModuleCat R`, matching the
  literal shape `(EtaleChart f V)ᵒᵖ ⥤ ModuleCat R` requested by the task (rather than a
  `PresheafOfModules` over a presheaf of *varying* rings, which is a heavier piece of
  Mathlib/repository infrastructure not otherwise used here).
* `Modules/Stack.lean`'s `IsQuasiCoherent` is Mathlib's `SheafOfModules.IsQuasicoherent`
  predicate on an actual sheaf of modules on `Sites.RingedSite`; producing an object of that
  type for the presheaves here would require gluing them into a sheaf on
  `Sites.smallEtaleStackRingedSite`, which `Global.lean`'s own module docstring already records
  as unavailable in this repository (a universe mismatch between `Full.cotangentComplex`, which
  lives in a single universe `u`, and the structure sheaf of that site, which is
  `CommRingCat.{u+1}`-valued). We therefore state quasi-coherence directly as the named
  base-change isomorphism theorems `isQuasiCoherent_hZeroPresheaf`/
  `isQuasiCoherent_hNegOnePresheaf`, as explicitly allowed by the task description.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

open CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AtlasDescentGlobal

open Transitivity AtlasDescent Global

/-! ### Two identity lemmas for self-algebra structures

The presheaf identity law proved below compares `KaehlerDifferential.map`, resp.
`Algebra.H1Cotangent.map`, taken along a *nonstandard* algebra structure of `A` over itself — the
one carried by `Global.AffineChart.resAlgebra (le_refl c.U)` — with the identity map.  Since
`Algebra.id` is declared with priority `1100`, it wins every instance search against a local
`Algebra A A` hypothesis; so the two lemmas below take the offending instance as an *explicit*
argument, supplied by `@`-application, and are stated *pointwise*.  This way no `Module` or
`LinearMap` instance occurs in their statements, hence no instance diamond either, so that
`subst` (via `Algebra.algebra_ext`) can eliminate it before Mathlib's own
`Derivation.liftKaehlerDifferential_unique`, resp. `Algebra.Extension.H1Cotangent.map_eq` and
`Algebra.Extension.H1Cotangent.map_id`, finish the proof. -/

section Rings

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- If an algebra structure `i` of `A` over itself has the identity as its structure map, then the
map it induces on Kähler differentials, `Ω[A⁄R] →ₗ[A] Ω[A⁄R]`, is the identity.  The instance `i`
is an explicit argument, and the statement is pointwise, so that it contains no instance
diamond. -/
theorem kaehlerMap_self_apply (i : Algebra A A) (hi : ∀ a : A, i.algebraMap a = a)
    (ts : @IsScalarTower R A A _ (@Algebra.toSMul A A _ _ i) _)
    (scc : @SMulCommClass R A A _ (@Algebra.toSMul A A _ _ i)) (x : Ω[A⁄R]) :
    (@KaehlerDifferential.map R R _ _ _ A A _ _ _ i _ _ ts _ scc) x = x := by
  have h : i = Algebra.id A := Algebra.algebra_ext _ _ hi
  subst h
  have key : (KaehlerDifferential.map R R A A) = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    simp
  exact LinearMap.congr_fun key x

/-- The `H⁻¹` analogue of `kaehlerMap_self_apply`: if an algebra structure `i` of `A` over itself
has the identity as its structure map, then the map it induces on `H¹` of the cotangent complex,
`Algebra.H1Cotangent R A →ₗ[A] Algebra.H1Cotangent R A`, is the identity. -/
theorem h1CotangentMap_self_apply (i : Algebra A A) (hi : ∀ a : A, i.algebraMap a = a)
    (ts : @IsScalarTower R A A _ (@Algebra.toSMul A A _ _ i) _) (x : Algebra.H1Cotangent R A) :
    (@Algebra.H1Cotangent.map R R _ _ _ A _ _ A _ _ _ _ i ts) x = x := by
  have h : i = Algebra.id A := Algebra.algebra_ext _ _ hi
  subst h
  exact LinearMap.congr_fun
    ((Algebra.Extension.H1Cotangent.map_eq _ (Algebra.Extension.Hom.id _)).trans
      Algebra.Extension.H1Cotangent.map_id) x

end Rings

section Schemes

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Opens}

attribute [local instance] Global.AffineChart.algebra

/-! ### The category of affine charts -/

/-- The affine charts of `f : X ⟶ Y` over `V`, as an indexing category for presheaves: this is
literally `Global.AffineChart f V`, renamed to stress its role as a (Zariski) site. A morphism
`c ⟶ c'` exists iff `c.U ≤ c'.U`, matching the convention for the category of opens of a
topological space. -/
abbrev EtaleChart (f : X ⟶ Y) (V : Y.Opens) := Global.AffineChart f V

/-- The preorder on `EtaleChart f V` making it into the category of a Zariski cover: `c ≤ c'`
iff `c.U ≤ c'.U`. -/
instance instPreorderEtaleChart : Preorder (EtaleChart f V) where
  le c c' := c.U ≤ c'.U
  le_refl c := le_refl c.U
  le_trans _ _ _ h h' := h.trans h'

/-! ### An identity fact for the restriction of sections -/

/-- Restricting sections along the identity inclusion of an open is the identity ring
homomorphism: the fact underlying the presheaf identity law for the charts below. -/
theorem sectionsRes_self (Z : Scheme.{u}) (U : Z.Opens) :
    sectionsRes Z (le_refl U) = RingHom.id Γ(Z, U) := by
  simp [sectionsRes]

/-- Along the identity refinement of a chart, `resAlgebra` gives the identity ring
homomorphism as its algebra map. -/
theorem resAlgebra_self_algebraMap (c : EtaleChart f V) :
    letI := Global.AffineChart.resAlgebra (le_refl c.U)
    algebraMap Γ(X, c.U) Γ(X, c.U) = RingHom.id Γ(X, c.U) := by
  simp [RingHom.algebraMap_toAlgebra, sectionsRes_self]

/-! ### The objects of the two presheaves -/

/-- `H⁰` of the affine-local cotangent complex on a chart, viewed as a `Γ(Y,V)`-module: the
module of relative differentials `Ω[Γ(X,c.U)⁄Γ(Y,V)]`. -/
noncomputable def hZeroObj (c : EtaleChart f V) : ModuleCat.{u} Γ(Y, V) :=
  ModuleCat.of Γ(Y, V) Ω[Γ(X, c.U)⁄Γ(Y, V)]

/-- `H⁻¹` of the affine-local cotangent complex on a chart, viewed as a `Γ(Y,V)`-module. -/
noncomputable def hNegOneObj (c : EtaleChart f V) : ModuleCat.{u} Γ(Y, V) :=
  ModuleCat.of Γ(Y, V) (Algebra.H1Cotangent Γ(Y, V) Γ(X, c.U))

/-! ### The restriction maps -/

/-- The `H⁰` restriction map attached to a chart refinement `c.U ≤ c'.U`: a `Γ(Y,V)`-linear map
`Ω[Γ(X,c'.U)⁄Γ(Y,V)] ⟶ Ω[Γ(X,c.U)⁄Γ(Y,V)]`, restricting from the bigger chart `c'` to the
smaller chart `c`. -/
noncomputable def hZeroMap {c c' : EtaleChart f V} (h : c.U ≤ c'.U) :
    hZeroObj c' ⟶ hZeroObj c :=
  letI := Global.AffineChart.resAlgebra h
  letI := Global.AffineChart.isScalarTower_res h
  ModuleCat.ofHom
    ((KaehlerDifferential.map Γ(Y, V) Γ(Y, V) Γ(X, c'.U) Γ(X, c.U)).restrictScalars Γ(Y, V))

/-- The `H⁻¹` restriction map attached to a chart refinement `c.U ≤ c'.U`. -/
noncomputable def hNegOneMap {c c' : EtaleChart f V} (h : c.U ≤ c'.U) :
    hNegOneObj c' ⟶ hNegOneObj c :=
  letI := Global.AffineChart.resAlgebra h
  letI := Global.AffineChart.isScalarTower_res h
  ModuleCat.ofHom
    ((Algebra.H1Cotangent.map Γ(Y, V) Γ(Y, V) Γ(X, c'.U) Γ(X, c.U)).restrictScalars Γ(Y, V))

/-! ### The presheaf composition law -/

/-- **Composition law for `hZeroMap`.** Restricting directly from the biggest chart `c''` to
the smallest chart `c` agrees with restricting in two steps: this is the `H⁰` presheaf
composition law. -/
theorem hZeroMap_comp {c c' c'' : EtaleChart f V} (h : c.U ≤ c'.U) (h' : c'.U ≤ c''.U) :
    hZeroMap (h.trans h') = hZeroMap h' ≫ hZeroMap h := by
  let _ := Global.AffineChart.resAlgebra h
  let _ := Global.AffineChart.resAlgebra h'
  let _ := Global.AffineChart.resAlgebra (h.trans h')
  let _ := Global.AffineChart.isScalarTower_res h
  let _ := Global.AffineChart.isScalarTower_res h'
  let _ := Global.AffineChart.isScalarTower_res (h.trans h')
  let _ := Global.AffineChart.isScalarTower_res_res h' h
  apply ModuleCat.hom_ext
  change ((KaehlerDifferential.map Γ(Y, V) Γ(Y, V) Γ(X, c''.U) Γ(X, c.U)).restrictScalars Γ(Y, V)) =
      ((KaehlerDifferential.map Γ(Y, V) Γ(Y, V) Γ(X, c'.U) Γ(X, c.U)).restrictScalars Γ(Y, V)) ∘ₗ
      ((KaehlerDifferential.map Γ(Y, V) Γ(Y, V) Γ(X, c''.U) Γ(X, c'.U)).restrictScalars Γ(Y, V))
  rw [kaehlerMap_comp Γ(Y, V) Γ(X, c''.U) Γ(X, c'.U) Γ(X, c.U)]
  simp

/-- **Composition law for `hNegOneMap`.** The `H⁻¹` analogue of `hZeroMap_comp`. -/
theorem hNegOneMap_comp {c c' c'' : EtaleChart f V} (h : c.U ≤ c'.U) (h' : c'.U ≤ c''.U) :
    hNegOneMap (h.trans h') = hNegOneMap h' ≫ hNegOneMap h := by
  let _ := Global.AffineChart.resAlgebra h
  let _ := Global.AffineChart.resAlgebra h'
  let _ := Global.AffineChart.resAlgebra (h.trans h')
  let _ := Global.AffineChart.isScalarTower_res h
  let _ := Global.AffineChart.isScalarTower_res h'
  let _ := Global.AffineChart.isScalarTower_res (h.trans h')
  let _ := Global.AffineChart.isScalarTower_res_res h' h
  apply ModuleCat.hom_ext
  change ((Algebra.H1Cotangent.map Γ(Y, V) Γ(Y, V) Γ(X, c''.U) Γ(X, c.U)).restrictScalars Γ(Y, V)) =
      ((Algebra.H1Cotangent.map Γ(Y, V) Γ(Y, V) Γ(X, c'.U) Γ(X, c.U)).restrictScalars Γ(Y, V)) ∘ₗ
      ((Algebra.H1Cotangent.map Γ(Y, V) Γ(Y, V) Γ(X, c''.U) Γ(X, c'.U)).restrictScalars Γ(Y, V))
  rw [h1CotangentMap_comp Γ(Y, V) Γ(X, c''.U) Γ(X, c.U) Γ(X, c'.U)]
  simp

/-! ### The presheaf identity law -/

/-- The inclusion of affine opens underlying a morphism of charts. -/
theorem le_of_hom {c c' : EtaleChart f V} (h : c ⟶ c') : c.U ≤ c'.U := leOfHom h

/-- Pointwise form of `resAlgebra_self_algebraMap`: along the identity refinement of a chart, the
structure map of `resAlgebra` is the identity function on sections. -/
theorem resAlgebra_self_algebraMap_apply (c : EtaleChart f V) (a : Γ(X, c.U)) :
    (Global.AffineChart.resAlgebra (c := c) (c' := c) (le_refl c.U)).algebraMap a = a :=
  DFunLike.congr_fun (resAlgebra_self_algebraMap c) a

/-- **Identity law for `hZeroMap`.** Restricting along the identity refinement of a chart is the
identity map of `H⁰`: this is the `H⁰` presheaf identity law. -/
theorem hZeroMap_id (c : EtaleChart f V) : hZeroMap (le_refl c.U) = 𝟙 (hZeroObj c) := by
  let _ := Global.AffineChart.resAlgebra (c := c) (c' := c) (le_refl c.U)
  let _ := Global.AffineChart.isScalarTower_res (c := c) (c' := c) (le_refl c.U)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact kaehlerMap_self_apply (Global.AffineChart.resAlgebra (c := c) (c' := c) (le_refl c.U))
    (resAlgebra_self_algebraMap_apply c) _ _ x

/-- **Identity law for `hNegOneMap`.** The `H⁻¹` analogue of `hZeroMap_id`. -/
theorem hNegOneMap_id (c : EtaleChart f V) : hNegOneMap (le_refl c.U) = 𝟙 (hNegOneObj c) := by
  let _ := Global.AffineChart.resAlgebra (c := c) (c' := c) (le_refl c.U)
  let _ := Global.AffineChart.isScalarTower_res (c := c) (c' := c) (le_refl c.U)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact h1CotangentMap_self_apply (Global.AffineChart.resAlgebra (c := c) (c' := c) (le_refl c.U))
    (resAlgebra_self_algebraMap_apply c) _ x

/-! ### The two presheaves -/

/-- **The `H⁰` presheaf of the cotangent complex on the affine charts.** The presheaf of
`Γ(Y,V)`-modules on the category of affine charts of `f` over `V` sending a chart `c` to
`Ω[Γ(X,c.U)⁄Γ(Y,V)]`, with restriction maps `hZeroMap`.  Its functoriality is
`hZeroMap_id`/`hZeroMap_comp`. -/
noncomputable def hZeroPresheaf : (EtaleChart f V)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, V) where
  obj c := hZeroObj c.unop
  map h := hZeroMap (le_of_hom h.unop)
  map_id c := hZeroMap_id c.unop
  map_comp h h' := hZeroMap_comp (le_of_hom h'.unop) (le_of_hom h.unop)

/-- **The `H⁻¹` presheaf of the cotangent complex on the affine charts.** The presheaf of
`Γ(Y,V)`-modules on the category of affine charts of `f` over `V` sending a chart `c` to
`Algebra.H1Cotangent Γ(Y,V) Γ(X,c.U)`, with restriction maps `hNegOneMap`.  Its functoriality is
`hNegOneMap_id`/`hNegOneMap_comp`. -/
noncomputable def hNegOnePresheaf : (EtaleChart f V)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, V) where
  obj c := hNegOneObj c.unop
  map h := hNegOneMap (le_of_hom h.unop)
  map_id c := hNegOneMap_id c.unop
  map_comp h h' := hNegOneMap_comp (le_of_hom h'.unop) (le_of_hom h.unop)

/-- The value of `hZeroPresheaf` on a chart. -/
@[simp]
theorem hZeroPresheaf_obj (c : (EtaleChart f V)ᵒᵖ) :
    (hZeroPresheaf (f := f) (V := V)).obj c = hZeroObj c.unop := rfl

/-- The restriction map of `hZeroPresheaf` along a refinement of charts. -/
@[simp]
theorem hZeroPresheaf_map {c c' : (EtaleChart f V)ᵒᵖ} (h : c ⟶ c') :
    (hZeroPresheaf (f := f) (V := V)).map h = hZeroMap (le_of_hom h.unop) := rfl

/-- The value of `hNegOnePresheaf` on a chart. -/
@[simp]
theorem hNegOnePresheaf_obj (c : (EtaleChart f V)ᵒᵖ) :
    (hNegOnePresheaf (f := f) (V := V)).obj c = hNegOneObj c.unop := rfl

/-- The restriction map of `hNegOnePresheaf` along a refinement of charts. -/
@[simp]
theorem hNegOnePresheaf_map {c c' : (EtaleChart f V)ᵒᵖ} (h : c ⟶ c') :
    (hNegOnePresheaf (f := f) (V := V)).map h = hNegOneMap (le_of_hom h.unop) := rfl

/-! ### Naturality of the universal derivation -/

/-- The restriction of sections attached to a chart refinement `c.U ≤ c'.U`, as a morphism of
`Γ(Y,V)`-modules `Γ(X,c'.U) ⟶ Γ(X,c.U)`: this is `sectionsRes` made `Γ(Y,V)`-linear using the
tower `Γ(Y,V) → Γ(X,c'.U) → Γ(X,c.U)`. -/
noncomputable def sectionsResLinear {c c' : EtaleChart f V} (h : c.U ≤ c'.U) :
    ModuleCat.of Γ(Y, V) Γ(X, c'.U) ⟶ ModuleCat.of Γ(Y, V) Γ(X, c.U) :=
  letI := Global.AffineChart.resAlgebra h
  letI := Global.AffineChart.isScalarTower_res h
  ModuleCat.ofHom (IsScalarTower.toAlgHom Γ(Y, V) Γ(X, c'.U) Γ(X, c.U)).toLinearMap

/-- **Identity law for `sectionsResLinear`.** -/
theorem sectionsResLinear_id (c : EtaleChart f V) :
    sectionsResLinear (le_refl c.U) = 𝟙 (ModuleCat.of Γ(Y, V) Γ(X, c.U)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact resAlgebra_self_algebraMap_apply c x

/-- **Composition law for `sectionsResLinear`.** -/
theorem sectionsResLinear_comp {c c' c'' : EtaleChart f V} (h : c.U ≤ c'.U) (h' : c'.U ≤ c''.U) :
    sectionsResLinear (h.trans h') = sectionsResLinear h' ≫ sectionsResLinear h := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun (sectionsRes_comp X h' h) x

/-- **The presheaf of sections on the affine charts of `f` over `V`**, valued in
`Γ(Y,V)`-modules: a chart `c` is sent to `Γ(X,c.U)` and a refinement to `sectionsResLinear`.  This
is the source of the universal derivation `derivationNatTrans`. -/
noncomputable def sectionsPresheaf : (EtaleChart f V)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, V) where
  obj c := ModuleCat.of Γ(Y, V) Γ(X, c.unop.U)
  map h := sectionsResLinear (le_of_hom h.unop)
  map_id c := sectionsResLinear_id c.unop
  map_comp h h' := sectionsResLinear_comp (le_of_hom h'.unop) (le_of_hom h.unop)

/-- **The universal derivation is natural in the chart.** The maps
`d : Γ(X,c.U) → Ω[Γ(X,c.U)⁄Γ(Y,V)]` assemble into a morphism of presheaves of `Γ(Y,V)`-modules
`sectionsPresheaf ⟶ hZeroPresheaf`; naturality is `KaehlerDifferential.map_D`, i.e. the
restriction maps of `hZeroPresheaf` send `d s` to `d` of the restriction of `s`. -/
noncomputable def derivationNatTrans :
    sectionsPresheaf (f := f) (V := V) ⟶ hZeroPresheaf where
  app c := ModuleCat.ofHom
    ((KaehlerDifferential.D Γ(Y, V) Γ(X, c.unop.U)).toLinearMap.restrictScalars Γ(Y, V))
  naturality c c' h := by
    let _ := Global.AffineChart.resAlgebra (le_of_hom h.unop)
    let _ := Global.AffineChart.isScalarTower_res (le_of_hom h.unop)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (KaehlerDifferential.map_D Γ(Y, V) Γ(Y, V) Γ(X, c.unop.U) Γ(X, c'.unop.U) x).symm

/-- The value of `sectionsPresheaf` on a chart. -/
@[simp]
theorem sectionsPresheaf_obj (c : (EtaleChart f V)ᵒᵖ) :
    (sectionsPresheaf (f := f) (V := V)).obj c = ModuleCat.of Γ(Y, V) Γ(X, c.unop.U) := rfl

/-- The restriction map of `sectionsPresheaf` along a refinement of charts. -/
@[simp]
theorem sectionsPresheaf_map {c c' : (EtaleChart f V)ᵒᵖ} (h : c ⟶ c') :
    (sectionsPresheaf (f := f) (V := V)).map h = sectionsResLinear (le_of_hom h.unop) := rfl

/-- The component of `derivationNatTrans` at a chart is the universal derivation. -/
@[simp]
theorem derivationNatTrans_app (c : (EtaleChart f V)ᵒᵖ) :
    (derivationNatTrans (f := f) (V := V)).app c = ModuleCat.ofHom
      ((KaehlerDifferential.D Γ(Y, V) Γ(X, c.unop.U)).toLinearMap.restrictScalars Γ(Y, V)) := rfl

/-! ### Quasi-coherence along basic-open (Zariski) chart refinements -/

/-- **Quasi-coherence for `hZeroMap`.** Along a basic-open (hence Zariski, hence formally
étale) chart refinement, `hZeroMap`'s underlying map becomes bijective after base change to the
smaller chart: `Γ(X, (basicOpenChart c g).U) ⊗[Γ(X,c.U)] Ω[Γ(X,c.U)⁄Γ(Y,V)] ≅ Ω[Γ(X,(basicOpenChart
c g).U)⁄Γ(Y,V)]`. This is exactly the base-change isomorphism that would exhibit `hZeroPresheaf`
as a quasi-coherent module presheaf on the small étale site (see the module docstring for why a
literal `Modules/Stack.lean` `IsQuasiCoherent` term is not produced). -/
theorem isQuasiCoherent_hZeroPresheaf (c : EtaleChart f V) (g : Γ(X, c.U)) :
    letI := Global.AffineChart.resAlgebra (Global.AffineChart.basicOpenChart_le c g)
    letI := Global.AffineChart.isScalarTower_res (Global.AffineChart.basicOpenChart_le c g)
    Function.Bijective (KaehlerDifferential.mapBaseChange Γ(Y, V) Γ(X, c.U)
      Γ(X, (Global.AffineChart.basicOpenChart c g).U)) :=
  letI := Global.AffineChart.resAlgebra (Global.AffineChart.basicOpenChart_le c g)
  letI := Global.AffineChart.isScalarTower_res (Global.AffineChart.basicOpenChart_le c g)
  letI := Global.AffineChart.formallyEtale_basicOpenChart c g
  bijective_mapBaseChange_of_formallyEtale Γ(Y, V) Γ(X, c.U)
    Γ(X, (Global.AffineChart.basicOpenChart c g).U)

/-- **Quasi-coherence for `hNegOneMap`.** The `H⁻¹` analogue of
`isQuasiCoherent_hZeroPresheaf`: along a basic-open chart refinement, the base-changed
`H⁻¹` restriction map is bijective. A basic-open refinement is an `Away` localisation, hence
genuinely `Algebra.Etale` (not just formally étale), which is what the `H⁻¹` base-change result
needs. -/
theorem isQuasiCoherent_hNegOnePresheaf (c : EtaleChart f V) (g : Γ(X, c.U)) :
    letI := Global.AffineChart.resAlgebra (Global.AffineChart.basicOpenChart_le c g)
    letI := Global.AffineChart.isScalarTower_res (Global.AffineChart.basicOpenChart_le c g)
    Function.Bijective ((Algebra.H1Cotangent.map Γ(Y, V) Γ(Y, V) Γ(X, c.U)
      Γ(X, (Global.AffineChart.basicOpenChart c g).U)).liftBaseChange
      Γ(X, (Global.AffineChart.basicOpenChart c g).U)) :=
  letI := Global.AffineChart.resAlgebra (Global.AffineChart.basicOpenChart_le c g)
  letI := Global.AffineChart.isScalarTower_res (Global.AffineChart.basicOpenChart_le c g)
  letI := Global.AffineChart.isLocalization_basicOpenChart c g
  letI : Algebra.Etale Γ(X, c.U) Γ(X, (Global.AffineChart.basicOpenChart c g).U) :=
    Algebra.Etale.of_isLocalizationAway g
  bijective_liftBaseChange_of_etale Γ(Y, V) Γ(X, c.U)
    Γ(X, (Global.AffineChart.basicOpenChart c g).U)

end Schemes

end AtlasDescentGlobal

end GromovWitten.AlgebraicGeometry.CotangentComplex
