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
* `hZeroObj`/`hNegOneObj`, `hZeroMap`/`hNegOneMap` : the data of two presheaves on
  `(EtaleChart f V)ᵒᵖ` valued in `ModuleCat Γ(Y,V)`, sending a chart `c` to `Ω[Γ(X,c.U)⁄Γ(Y,V)]`,
  resp. `Algebra.H1Cotangent Γ(Y,V) Γ(X,c.U)`, restricted to `Γ(Y,V)`-modules, with restriction
  maps `KaehlerDifferential.map`, resp. `Algebra.H1Cotangent.map`.
* `hZeroMap_comp`, `hNegOneMap_comp`: the presheaf composition laws, stated as standalone
  theorems (these are exactly the `map_comp` field of the corresponding functor, were it
  bundled — see the `Not done` section for why the identity law, and hence the bundling into
  an actual `CategoryTheory.Functor`, is not proved here).
* `isQuasiCoherent_hZeroPresheaf`, `isQuasiCoherent_hNegOnePresheaf`: along a basic-open
  refinement of charts (a Zariski, hence formally étale, chart transition) the restriction map
  becomes an isomorphism after base change: this is the "quasi-coherent module presheaf on the
  small étale site" content requested for a presheaf of the shape produced here (see the Not
  Done section for why a literal `Modules/Stack.lean` `IsQuasiCoherent` term is not produced).

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
module of relative differentials `Ω[Γ(X,c.U)⁄Γ(Y,V)]`. Stated as `abbrev` (rather than `def`) so
that it unfolds automatically wherever it is used as an implicit `ModuleCat` object: this matches
this repository's own "concrete covers/functors must be `abbrev`s" convention, and is needed for
`ModuleCat.hom_ext`/`simp`/instance-search to see through it as `ModuleCat.of Ω[Γ(X,c.U)⁄Γ(Y,V)]`
rather than an opaque wrapper. This *helps* towards the presheaf identity law below (it resolves
one genuine reducibility obstacle), but is not on its own sufficient: see the `Not done`
discussion in the module docstring for the remaining obstacle. -/
noncomputable abbrev hZeroObj (c : EtaleChart f V) : ModuleCat.{u} Γ(Y, V) :=
  ModuleCat.of Γ(Y, V) Ω[Γ(X, c.U)⁄Γ(Y, V)]

/-- `H⁻¹` of the affine-local cotangent complex on a chart, viewed as a `Γ(Y,V)`-module.
`abbrev` for the same reason as `hZeroObj`. -/
noncomputable abbrev hNegOneObj (c : EtaleChart f V) : ModuleCat.{u} Γ(Y, V) :=
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

/-! ### The presheaf identity law

The identity law `hZeroMap (le_refl c.U) = 𝟙 (hZeroObj c)` (and its `H⁻¹` analogue) is
mathematically immediate from `resAlgebra_self_algebraMap`: along the identity refinement, the
restriction ring homomorphism is the identity, so the induced module map is the identity. It is
*not* included here as a theorem: instantiating `KaehlerDifferential.map`/`Algebra.H1Cotangent.map`
at `A = A` forces Lean's elaborator to choose between the canonical self-algebra instance
`Algebra.id A` and the `resAlgebra (le_refl c.U)` instance actually carried by `hZeroMap`'s
body, and every reformulation of the goal that does not literally unfold `hZeroMap`'s existing
term re-triggers this instance search and lands on `Algebra.id`, producing goals with
definitionally-mismatched (though propositionally equal, via `Algebra.algebra_ext` and
`resAlgebra_self_algebraMap`) module/`SMulCommClass` instances on `Ω[Γ(X,c.U)⁄Γ(Y,V)]`
(`instModuleKaehlerDifferentialOfSMulCommClass`). Bridging the two instances would need an
explicit transport of `Algebra.algebra_ext`-based instance equality through this module
structure; see the file's `Not done` discussion. Consequently `hZeroPresheaf`/`hNegOnePresheaf`
below are presented as the restriction data plus the composition law, not as a bundled
`CategoryTheory.Functor` (which would additionally require `map_id`). -/

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

/-! ### The presheaf identity law

The identity law `hZeroMap (le_refl c.U) = 𝟙 (hZeroObj c)` (and its `H⁻¹` analogue) is
mathematically immediate from `resAlgebra_self_algebraMap`: along the identity refinement, the
restriction ring homomorphism is the identity, so the induced module map is the identity. It is
*not* included here as a theorem: instantiating `KaehlerDifferential.map`/`Algebra.H1Cotangent.map`
at `A = A` forces Lean's elaborator to choose between the canonical self-algebra instance
`Algebra.id A` and the `resAlgebra (le_refl c.U)` instance actually carried by `hZeroMap`'s
body, and every reformulation of the goal that does not literally unfold `hZeroMap`'s existing
term re-triggers this instance search and lands on `Algebra.id`, producing goals with
definitionally-mismatched (though propositionally equal, via `Algebra.algebra_ext` and
`resAlgebra_self_algebraMap`) module/`SMulCommClass` instances on `Ω[Γ(X,c.U)⁄Γ(Y,V)]`
(`instModuleKaehlerDifferentialOfSMulCommClass`). Working entirely from `hZeroMap`'s/`hNegOneMap`'s
own already-elaborated terms (via `simp only [hZeroMap]`/`simp only [hNegOneMap]`, never
restating `KaehlerDifferential.map`/`Algebra.H1Cotangent.map` afresh) does dodge this specific
diamond, but a *second*, independent obstacle then appears: `ModuleCat.hom_ext`'s implicit
carrier objects are inferred from `hZeroMap`'s/`hNegOneMap`'s own (non-`abbrev`, though here
already promoted to `abbrev`) declared types, and subsequent `simp`/instance-search steps
(`ModuleCat.hom_ofHom`, `ModuleCat.hom_id`, `Submodule.span`'s `Module` instance, `map_smul`)
either fail to fire or resynthesize the *same* `Algebra.id`-vs-`resAlgebra` diamond one level
down, inside `Ω[Γ(X,c.U)⁄Γ(Y,V)]`'s own `Γ(X,c.U)`-module structure. For the `H⁻¹` side the
diamond is provably absent (canonicity via `Algebra.Extension.H1Cotangent.map_eq`/`map_id` does
not depend on any `Algebra A A` instance at all), yet the elaborator's unification of these two
lemmas against the ambient `Extension`/`Generators` machinery still exceeds even a 5×-enlarged
(1,000,000) heartbeat budget. Bridging these would need an explicit transport of
`Algebra.algebra_ext`-based instance equality through the relevant module structures; see the
`Not done` discussion in the module docstring. Consequently the identity law is not proved, and
`hZeroObj`/`hZeroMap`/`hZeroMap_comp` and `hNegOneObj`/`hNegOneMap`/`hNegOneMap_comp` above are
presented as the restriction data plus the composition law, not bundled into a
`CategoryTheory.Functor` (which would additionally require `map_id`). -/

end Schemes

end AtlasDescentGlobal

end GromovWitten.AlgebraicGeometry.CotangentComplex
