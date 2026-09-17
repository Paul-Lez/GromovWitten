/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.Full
import GromovWitten.AlgebraicGeometry.Stacks.Algebraic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.Basic

/-!
# Globalising the cotangent complex: affine charts and their comparisons

`CotangentComplex/Full.lean` constructs the truncated cotangent complex `L_{S/R}` of a ring map
as an actual object of `DerivedCategory (ModuleCat S)`.  This file globalises it in the only
way that is genuinely available: it constructs, for a morphism of schemes `f : X ⟶ Y` and a
pair of affine opens `V ⊆ Y`, `U ⊆ f⁻¹V`, the cotangent complex of `Γ(Y,V) → Γ(X,U)`, together
with the comparison morphisms attached to a refinement of charts, and proves that those
comparison morphisms are canonical and compose strictly.  The same charts are then used along
an étale atlas of a Deligne--Mumford stack, where the relative cotangent complex of every
chart transition is proved to vanish.

The technical device that makes the comparison morphisms into honest morphisms of complexes is
restriction of scalars: if `S₀` is a ring mapping to all the rings occurring in a chain of
refinements (in the geometric situation, the sections over the smallest chart), then every
presentation complex in the chain becomes a complex of `S₀`-modules and the comparisons are
`S₀`-linear chain maps.  Composition of comparison maps is then a strict equality of chain
maps, so the cocycle condition needs no coherence isomorphism.

## Main constructions and results

### Comparison of presentation complexes over a common ground ring

* `restrictComplexFunctor`, `restrictHom`: restriction of scalars on cochain complexes, and the
  promotion of a map that is semilinear over `S → S'` to an `S₀`-linear map of the restricted
  modules.
* `mapOverX`, `mapOver`: the chain map of presentation complexes induced by a morphism
  `P.Hom P'` of `Algebra.Extension`s lying over a map of base rings, viewed over `S₀`.
* `mapOver_id`, `mapOver_comp`: strict functoriality, i.e. the cocycle condition for chart
  refinements holds on the nose, with no coherence isomorphism.
* `homSub_smul`, `homotopyOverX`, `homotopyOver`: two morphisms of extensions over the same
  map of base rings induce chain homotopic comparison maps, the homotopy being Mathlib's
  `Algebra.Extension.Hom.sub`.
* `objectOver`, `derivedMapOver`, `derivedMapOver_eq`, `derivedMapOver_id`,
  `derivedMapOver_comp`: the induced morphism in `DerivedCategory (ModuleCat S₀)` is canonical
  (independent of the chosen morphism of extensions) and functorial.
* `towerHom`, `cotangentComplexOver`, `towerComparison`, `towerComparison_self`,
  `towerComparison_trans`: for a tower `R → S → T` the restriction comparison
  `L_{S/R} ⟶ L_{T/R}` in `DerivedCategory (ModuleCat R)`, with the identity and composition
  laws.

### The local complex `[I/I² → Ω_M|_U]`

* `localComplex_X_negOne`, `cotangent_def`, `localComplex_X_zero`, `localComplex_d`,
  `localComplex_isZero`: the two-term complex of a presentation is exactly `I/I²` in degree
  `-1`, the restricted ambient differentials `S ⊗_{P.Ring} Ω[P.Ring⁄R]` in degree `0`, the
  conormal map between them, and zero elsewhere.
* `cohomologyZeroLocalIso`, `cohomologyNegOneSmoothLocalIso`: when the ambient ring is formally
  smooth over the base, this local complex computes both cohomology modules of `L_{S/R}`.
* `embeddingIso`, `embeddingIso_hom`, `isIso_comparePresentation`, `embeddingIso_trans`,
  `embeddingIso_self`, `embeddingCotangentSpaceBasis`: for an embedding of the chart into an
  affine space over the base the comparison is an actual isomorphism in the derived category,
  the comparisons of two embeddings are coherent, and degree `0` is free on the coordinate
  differentials.  The public object carries no embedding.

### Étale maps, transitivity, atlas compatibility

* `isZero_cotangentComplex_of_formallyEtale`, `isZero_cotangentComplex_of_etale`:
  `L_{T/S} = 0` for a (formally) étale ring map.
* `kaehlerRestrictionEquiv`, `cohomologyZeroEtaleIso`,
  `jzBaseChange_eq_cohomologyZeroEtaleIso`, `isIso_jzBaseChange_of_formallyEtale`: `H⁰` base
  changes along a formally étale map, and the Jacobi--Zariski base-change map is exactly that
  isomorphism.
* `h1CotangentLocalizationEquiv`, `cohomologyNegOneLocalizationIso`: `H⁻¹` base changes along
  a localisation.
* `isZero_cohomology_of_formallyEtale`, `jzH1Map_eq_zero`, `jzOmegaMap_eq_zero`,
  `jzDelta_eq_zero`: the Jacobi--Zariski sequence of `R → S → T` collapses for a formally
  étale second step.

### Schemes

* `sectionsRes`, `sectionsRes_comp`: restriction of sections along nested opens.
* `AffineChart`, `AffineChart.algebra`, `AffineChart.algebraMap_eq`,
  `AffineChart.cotangentComplex`, `AffineChart.objectOverBase`: the affine-local cotangent
  complex of a morphism of schemes on an affine chart over a fixed affine open of the target.
  The chart stores only geometric data, and the complex stores no embedding.
* `AffineChart.resAlgebra`, `AffineChart.isScalarTower_res`,
  `AffineChart.isScalarTower_res_res`, `AffineChart.comparison`,
  `AffineChart.comparison_trans`: the comparison morphisms attached to refinements of charts
  and their cocycle coherence.
* `AffineChart.basicOpenChart`, `AffineChart.isLocalization_basicOpenChart`,
  `AffineChart.formallyEtale_basicOpenChart`,
  `AffineChart.isZero_cotangentComplex_basicOpenChart`,
  `AffineChart.cohomologyZeroBasicOpenIso`, `AffineChart.cohomologyNegOneBasicOpenIso`:
  Zariski refinements are localisations, so both cohomology modules base change.
* `AffineChart.coverChart`, `AffineChart.etale_appLE`,
  `AffineChart.isZero_cotangentComplex_etaleCover`, `AffineChart.isScalarTower_coverChart`,
  `AffineChart.cohomologyZeroEtaleCoverIso`: an affine open of an étale `X`-scheme over a
  chart is again a chart, the transition map is an étale ring map, its relative cotangent
  complex vanishes, and `H⁰` base changes.  This is the atlas-independence input for an étale
  atlas.

### Deligne--Mumford stacks

* `nonempty_atlasPullbackPresentation`, `etale_atlasPullbackPresentation_fst`: every base
  change of an étale atlas is presented by an actual scheme and the projection is étale.
* `isZero_cotangentComplex_atlasTransition`, `cohomologyZeroAtlasTransitionIso`,
  `exists_etaleAtlas_isZero_cotangentComplex_transition`: the affine-local cotangent complexes
  attached to the charts of an étale atlas form a descent datum: the relative cotangent
  complex of every chart transition over the atlas overlap vanishes and `H⁰` base changes.
  The last statement produces the atlas from the stack's own étale-atlas hypothesis, so no
  atlas and no embedding is chosen in its formulation.

## Not done here

The comparison morphisms are constructed and proved coherent, but they are *not* proved to be
isomorphisms after base change in the derived category: that needs derived flat base change for
the two-term presentation complex, i.e. a comparison of `Modules.Derived.baseChangeFunctor`
with the derived tensor product, which `Modules/Derived.lean` records as unavailable (Mathlib
v4.33.1 has no natural isomorphism `extendScalars f ⋙ restrictScalars f ≅ _ ⊗ f_*S`).  Only
the cohomology modules are proved to base change, and `H⁻¹` only for a localisation (from
`Algebra.tensorH1CotangentOfIsLocalization`); `H⁻¹` along a general étale map needs
`Algebra.Extension.tensorH1CotangentOfFormallyEtale`, whose hypothesis is the bijectivity of
`J ≃ Q ⊗_P I` for a compatible pair of presentations, and no such pair is constructed here.

The smooth-embedding comparison is an actual derived isomorphism only for an embedding into an
affine space (`embeddingIso`); for an arbitrary formally smooth ambient ring only the two
cohomology comparisons are available, because `Full.comparePresentation` would have to be
shown to be a quasi-isomorphism and Mathlib has no naturality statement for
`ShortComplex.moduleCatHomologyIso`, nor a morphism of extensions from a formally smooth
presentation back to the canonical polynomial one (formal smoothness lifts only along
square-zero, not arbitrary, surjections).

Consequently no sheaf of cotangent complexes on the small étale site of a Deligne--Mumford
stack is assembled: the descent datum is available chartwise (the family of chart complexes
together with the coherent comparisons above, and the vanishing of the relative complex along
étale transitions), but gluing it into an object of a derived category of sheaves of modules
would need the derived category of `SheafOfModules` on `Sites.smallEtaleStackRingedSite`
together with an effectivity statement for descent data, neither of which exists in this
repository; moreover the structure sheaf of that site is `CommRingCat.{u+1}`-valued while
`Full.cotangentComplex` lives in one universe.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Global

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SMulCommClass.of_commMonoid

/-! ### Restriction of scalars on presentation complexes -/

section Restrict

variable (S₀ S : Type u) [CommRing S₀] [CommRing S] [Algebra S₀ S]

/-- Restriction of scalars along `S₀ → S`, applied termwise to cochain complexes. -/
noncomputable abbrev restrictComplexFunctor :
    CochainComplex (ModuleCat.{u} S) ℤ ⥤ CochainComplex (ModuleCat.{u} S₀) ℤ :=
  (ModuleCat.restrictScalars (algebraMap S₀ S)).mapHomologicalComplex (ComplexShape.up ℤ)

variable {S₀ S}

/-- An additive map that is semilinear over `S → S'`, regarded as an `S₀`-linear map between
the restrictions of scalars along `S₀ → S` and `S₀ → S'`. -/
noncomputable def restrictHom {S' : Type u} [CommRing S']
    [Algebra S S'] [Algebra S₀ S'] [IsScalarTower S₀ S S']
    (M : Type u) [AddCommGroup M] [Module S M]
    (N : Type u) [AddCommGroup N] [Module S' N]
    (g : M →+ N) (hg : ∀ (s : S) (x : M), g (s • x) = algebraMap S S' s • g x) :
    (ModuleCat.restrictScalars (algebraMap S₀ S)).obj (ModuleCat.of S M) ⟶
      (ModuleCat.restrictScalars (algebraMap S₀ S')).obj (ModuleCat.of S' N) :=
  ModuleCat.ofHom
    (X := ((ModuleCat.restrictScalars (algebraMap S₀ S)).obj
      (ModuleCat.of S M) : ModuleCat.{u} S₀))
    (Y := ((ModuleCat.restrictScalars (algebraMap S₀ S')).obj
      (ModuleCat.of S' N) : ModuleCat.{u} S₀))
    { toFun := fun x => g x
      map_add' := fun x y => g.map_add x y
      map_smul' := fun r x => by
        refine (hg (algebraMap S₀ S r) x).trans ?_
        change algebraMap S S' (algebraMap S₀ S r) • g x = algebraMap S₀ S' r • g x
        rw [← IsScalarTower.algebraMap_apply] }

@[simp]
theorem restrictHom_hom_apply {S' : Type u} [CommRing S']
    [Algebra S S'] [Algebra S₀ S'] [IsScalarTower S₀ S S']
    (M : Type u) [AddCommGroup M] [Module S M]
    (N : Type u) [AddCommGroup N] [Module S' N]
    (g : M →+ N) (hg : ∀ (s : S) (x : M), g (s • x) = algebraMap S S' s • g x) (x : M) :
    (restrictHom (S₀ := S₀) M N g hg).hom x = g x :=
  rfl

end Restrict

/-! ### The comparison chain map attached to a morphism of extensions -/

section MapOver

variable {S₀ : Type u} [CommRing S₀]
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra S₀ S]
variable {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R' S'] [Algebra S₀ S']
variable [Algebra R R'] [Algebra S S'] [Algebra R S']
variable [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsScalarTower S₀ S S']
variable {P : Algebra.Extension.{u} R S} {P' : Algebra.Extension.{u} R' S'}

omit [Algebra S₀ S] [Algebra S₀ S'] [IsScalarTower S₀ S S'] [IsScalarTower R S S'] in
/-- Semilinearity of Mathlib's conormal comparison map over the base ring map. -/
theorem cotangentMap_smul (f : P.Hom P') (s : S) (x : P.Cotangent) :
    Algebra.Extension.Cotangent.map f (s • x) =
      algebraMap S S' s • Algebra.Extension.Cotangent.map f x := by
  rw [map_smul, algebraMap_smul]

omit [Algebra S₀ S] [Algebra S₀ S'] [IsScalarTower S₀ S S'] [IsScalarTower R S S'] in
/-- Semilinearity of Mathlib's ambient differentials comparison map over the base ring map. -/
theorem cotangentSpaceMap_smul (f : P.Hom P') (s : S) (x : P.CotangentSpace) :
    Algebra.Extension.CotangentSpace.map f (s • x) =
      algebraMap S S' s • Algebra.Extension.CotangentSpace.map f x := by
  rw [map_smul, algebraMap_smul]

/-- The degreewise comparison map of presentation complexes, viewed over the ground ring
`S₀`. -/
noncomputable def mapOverX (f : P.Hom P') (i : ℤ) :
    ((restrictComplexFunctor S₀ S).obj (Full.complex R S P)).X i ⟶
      ((restrictComplexFunctor S₀ S').obj (Full.complex R' S' P')).X i := by
  by_cases h1 : i = -1
  · subst h1
    exact restrictHom (S₀ := S₀) P.Cotangent P'.Cotangent
      (Algebra.Extension.Cotangent.map f).toAddMonoidHom (cotangentMap_smul f)
  · by_cases h0 : i = 0
    · subst h0
      exact restrictHom (S₀ := S₀) P.CotangentSpace P'.CotangentSpace
        (Algebra.Extension.CotangentSpace.map f).toAddMonoidHom (cotangentSpaceMap_smul f)
    · exact 0

omit [IsScalarTower R S S'] in
theorem mapOverX_negOne (f : P.Hom P') :
    mapOverX (S₀ := S₀) f (-1) =
      restrictHom P.Cotangent P'.Cotangent
        (Algebra.Extension.Cotangent.map f).toAddMonoidHom (cotangentMap_smul f) := rfl

omit [IsScalarTower R S S'] in
theorem mapOverX_zero (f : P.Hom P') :
    mapOverX (S₀ := S₀) f 0 =
      restrictHom P.CotangentSpace P'.CotangentSpace
        (Algebra.Extension.CotangentSpace.map f).toAddMonoidHom
        (cotangentSpaceMap_smul f) := rfl

omit [IsScalarTower R S S'] in
theorem mapOverX_eq_zero (f : P.Hom P') {i : ℤ} (h1 : i ≠ -1) (h0 : i ≠ 0) :
    mapOverX (S₀ := S₀) f i = 0 := by
  rw [mapOverX, dif_neg h1, dif_neg h0]

/-- The comparison chain map of presentation complexes attached to a morphism of extensions
lying over a map of base rings, viewed over the ground ring `S₀`. -/
noncomputable def mapOver (f : P.Hom P') :
    (restrictComplexFunctor S₀ S).obj (Full.complex R S P) ⟶
      (restrictComplexFunctor S₀ S').obj (Full.complex R' S' P') where
  f i := mapOverX f i
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    by_cases h1 : i = -1
    · subst h1
      rw [show (-1 : ℤ) + 1 = 0 by ring]
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact (Algebra.Extension.CotangentSpace.map_cotangentComplex f x).symm
    · have e1 : ((restrictComplexFunctor S₀ S).obj (Full.complex R S P)).d i (i + 1) = 0 := by
        simp only [Functor.mapHomologicalComplex_obj_d, Full.complex_d_eq_zero P h1,
          Functor.map_zero]
        rfl
      have e2 : ((restrictComplexFunctor S₀ S').obj (Full.complex R' S' P')).d i (i + 1) = 0 := by
        simp only [Functor.mapHomologicalComplex_obj_d, Full.complex_d_eq_zero P' h1,
          Functor.map_zero]
        rfl
      rw [e1, e2, Limits.comp_zero, Limits.zero_comp]

omit [IsScalarTower R S S'] in
@[simp]
theorem mapOver_f (f : P.Hom P') (i : ℤ) : (mapOver (S₀ := S₀) f).f i = mapOverX f i := rfl

end MapOver

/-! ### Strict functoriality of the comparison maps -/

section Functoriality

variable {S₀ : Type u} [CommRing S₀]

section Id

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra S₀ S]
variable {P : Algebra.Extension.{u} R S}

theorem mapOver_id :
    mapOver (S₀ := S₀) (Algebra.Extension.Hom.id P) =
      𝟙 ((restrictComplexFunctor S₀ S).obj (Full.complex R S P)) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h1 : i = -1
  · subst h1
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact congrFun (congrArg DFunLike.coe (Algebra.Extension.Cotangent.map_id (P := P))) x
  · by_cases h0 : i = 0
    · subst h0
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact congrFun (congrArg DFunLike.coe
        (Algebra.Extension.CotangentSpace.map_id (P := P))) x
    · rw [mapOver_f, mapOverX_eq_zero _ h1 h0]
      exact ((ModuleCat.restrictScalars (algebraMap S₀ S)).map_isZero
        (Full.complex_isZero P h1 h0)).eq_of_src _ _

end Id

section Comp

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra S₀ S]
variable {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R' S'] [Algebra S₀ S']
variable {R'' S'' : Type u} [CommRing R''] [CommRing S''] [Algebra R'' S''] [Algebra S₀ S'']
variable [Algebra R R'] [Algebra S S'] [Algebra R S']
variable [Algebra R' R''] [Algebra S' S''] [Algebra R' S'']
variable [Algebra R R''] [Algebra S S''] [Algebra R S'']
variable [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsScalarTower S₀ S S']
variable [IsScalarTower R' R'' S''] [IsScalarTower R' S' S''] [IsScalarTower S₀ S' S'']
variable [IsScalarTower R R'' S''] [IsScalarTower R S S''] [IsScalarTower S₀ S S'']
variable [IsScalarTower R R' R''] [IsScalarTower S S' S'']
variable {P : Algebra.Extension.{u} R S} {P' : Algebra.Extension.{u} R' S'}
variable {P'' : Algebra.Extension.{u} R'' S''}

omit [IsScalarTower R S S'] [IsScalarTower R' S' S''] [IsScalarTower R S S''] in
/-- The comparison maps of a chain of refinements compose strictly: over a common ground ring
the comparison attached to a composite morphism of extensions is the composite of the two
comparisons.  This is the cocycle condition for chart refinements. -/
theorem mapOver_comp (f : P.Hom P') (g : P'.Hom P'') :
    mapOver (S₀ := S₀) (g.comp f) = mapOver (S₀ := S₀) f ≫ mapOver (S₀ := S₀) g := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h1 : i = -1
  · subst h1
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact congrFun (congrArg DFunLike.coe (Algebra.Extension.Cotangent.map_comp P'' f g)) x
  · by_cases h0 : i = 0
    · subst h0
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact Algebra.Extension.CotangentSpace.map_comp_apply f g x
    · rw [mapOver_f, mapOverX_eq_zero _ h1 h0]
      exact ((ModuleCat.restrictScalars (algebraMap S₀ S)).map_isZero
        (Full.complex_isZero P h1 h0)).eq_of_src _ _

end Comp

end Functoriality


/-! ### Canonicity of the comparison maps in the derived category -/

section Homotopy

variable {S₀ : Type u} [CommRing S₀]
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra S₀ S]
variable {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R' S'] [Algebra S₀ S']
variable [Algebra R R'] [Algebra S S'] [Algebra R S']
variable [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsScalarTower S₀ S S']
variable {P : Algebra.Extension.{u} R S} {P' : Algebra.Extension.{u} R' S'}

omit [Algebra S₀ S] [Algebra S₀ S'] [IsScalarTower S₀ S S'] in
/-- Semilinearity of Mathlib's difference map attached to two morphisms of extensions. -/
theorem homSub_smul (f g : P.Hom P') (s : S) (x : P.CotangentSpace) :
    Algebra.Extension.Hom.sub f g (s • x) =
      algebraMap S S' s • Algebra.Extension.Hom.sub f g x := by
  rw [map_smul, algebraMap_smul]

/-- The degreewise homotopy datum attached to a pair of morphisms of extensions, viewed over
the ground ring `S₀`.  It is Mathlib's difference map `Algebra.Extension.Hom.sub` in bidegree
`(0, -1)` and zero elsewhere. -/
noncomputable def homotopyOverX (f g : P.Hom P') (i j : ℤ) :
    ((restrictComplexFunctor S₀ S).obj (Full.complex R S P)).X i ⟶
      ((restrictComplexFunctor S₀ S').obj (Full.complex R' S' P')).X j :=
  if h : i = 0 ∧ j = -1 then
    cast (by rw [h.1, h.2]; rfl)
      (restrictHom (S₀ := S₀) P.CotangentSpace P'.Cotangent
        (Algebra.Extension.Hom.sub f g).toAddMonoidHom (homSub_smul f g))
  else 0

theorem homotopyOverX_eq_zero (f g : P.Hom P') {i j : ℤ} (h : ¬(i = 0 ∧ j = -1)) :
    homotopyOverX (S₀ := S₀) f g i j = 0 :=
  dif_neg h

theorem homotopyOverX_zero_negOne (f g : P.Hom P') :
    homotopyOverX (S₀ := S₀) f g 0 (-1) =
      restrictHom P.CotangentSpace P'.Cotangent
        (Algebra.Extension.Hom.sub f g).toAddMonoidHom (homSub_smul f g) := rfl

/-- Two morphisms of extensions lying over the same map of base rings induce homotopic
comparison maps; the homotopy is Mathlib's difference map. -/
noncomputable def homotopyOver (f g : P.Hom P') :
    Homotopy (mapOver (S₀ := S₀) f) (mapOver (S₀ := S₀) g) where
  hom := homotopyOverX f g
  zero i j hij := by
    refine homotopyOverX_eq_zero f g ?_
    rintro ⟨rfl, rfl⟩
    exact hij (by simp)
  comm i := by
    by_cases h1 : i = -1
    · subst h1
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp),
        homotopyOverX_eq_zero (i := (-1 : ℤ)) (j := (-2 : ℤ)) f g (by rintro ⟨h, -⟩; omega),
        Limits.zero_comp, add_zero]
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      have hx : Algebra.Extension.Cotangent.map f x - Algebra.Extension.Cotangent.map g x =
          Algebra.Extension.Hom.sub f g (P.cotangentComplex x) :=
        congrFun (congrArg DFunLike.coe (Algebra.Extension.Cotangent.map_sub_map f g)) x
      exact sub_eq_iff_eq_add.mp hx
    · by_cases h0 : i = 0
      · subst h0
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
          homotopyOverX_eq_zero (i := (1 : ℤ)) (j := (0 : ℤ)) f g (by rintro ⟨h, -⟩; omega),
          Limits.comp_zero, zero_add]
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        have hx : Algebra.Extension.CotangentSpace.map f x -
            Algebra.Extension.CotangentSpace.map g x =
              P'.cotangentComplex (Algebra.Extension.Hom.sub f g x) :=
          congrFun (congrArg DFunLike.coe
            (Algebra.Extension.CotangentSpace.map_sub_map f g)) x
        exact sub_eq_iff_eq_add.mp hx
      · exact ((ModuleCat.restrictScalars (algebraMap S₀ S)).map_isZero
          (Full.complex_isZero P h1 h0)).eq_of_src _ _

end Homotopy

/-! ### The comparison morphism in the derived category -/

section DerivedMapOver

variable {S₀ : Type u} [CommRing S₀]

/-- The presentation complex of an extension `P` of `S` over `R`, viewed as an object of the
derived category of `S₀`-modules. -/
noncomputable def objectOver (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra S₀ S] (P : Algebra.Extension.{u} R S) : DerivedCategory (ModuleCat.{u} S₀) :=
  DerivedCategory.Q.obj ((restrictComplexFunctor S₀ S).obj (Full.complex R S P))

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra S₀ S]
variable {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R' S'] [Algebra S₀ S']
variable [Algebra R R'] [Algebra S S'] [Algebra R S']
variable [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsScalarTower S₀ S S']
variable {P : Algebra.Extension.{u} R S} {P' : Algebra.Extension.{u} R' S'}

/-- The comparison morphism in the derived category of `S₀`-modules attached to a morphism of
extensions lying over a map of base rings. -/
noncomputable def derivedMapOver (f : P.Hom P') :
    objectOver (S₀ := S₀) R S P ⟶ objectOver (S₀ := S₀) R' S' P' :=
  DerivedCategory.Q.map (mapOver f)

/-- The comparison morphism does not depend on the chosen morphism of extensions: it is
canonical. -/
theorem derivedMapOver_eq (f g : P.Hom P') :
    derivedMapOver (S₀ := S₀) f = derivedMapOver (S₀ := S₀) g :=
  Full.Q_map_eq_of_homotopy (homotopyOver f g)

end

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra S₀ S]
variable {P : Algebra.Extension.{u} R S}

theorem derivedMapOver_id :
    derivedMapOver (S₀ := S₀) (Algebra.Extension.Hom.id P) = 𝟙 (objectOver R S P) := by
  rw [derivedMapOver, mapOver_id, CategoryTheory.Functor.map_id]
  rfl

end

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra S₀ S]
variable {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R' S'] [Algebra S₀ S']
variable {R'' S'' : Type u} [CommRing R''] [CommRing S''] [Algebra R'' S''] [Algebra S₀ S'']
variable [Algebra R R'] [Algebra S S'] [Algebra R S']
variable [Algebra R' R''] [Algebra S' S''] [Algebra R' S'']
variable [Algebra R R''] [Algebra S S''] [Algebra R S'']
variable [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsScalarTower S₀ S S']
variable [IsScalarTower R' R'' S''] [IsScalarTower R' S' S''] [IsScalarTower S₀ S' S'']
variable [IsScalarTower R R'' S''] [IsScalarTower R S S''] [IsScalarTower S₀ S S'']
variable [IsScalarTower R R' R''] [IsScalarTower S S' S'']
variable {P : Algebra.Extension.{u} R S} {P' : Algebra.Extension.{u} R' S'}
variable {P'' : Algebra.Extension.{u} R'' S''}

omit [IsScalarTower R S S'] [IsScalarTower R' S' S''] [IsScalarTower R S S''] in
/-- The derived comparison morphisms compose. -/
theorem derivedMapOver_comp (f : P.Hom P') (g : P'.Hom P'') :
    derivedMapOver (S₀ := S₀) (g.comp f) =
      derivedMapOver (S₀ := S₀) f ≫ derivedMapOver (S₀ := S₀) g := by
  rw [derivedMapOver, mapOver_comp, CategoryTheory.Functor.map_comp]
  rfl

end

end DerivedMapOver


/-! ### Restriction along a tower: the comparison maps of chart refinements -/

section Tower

variable {S₀ : Type u} [CommRing S₀]
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The canonical morphism between the canonical presentations of `S` and of `T` over `R`,
for a tower `R → S → T`. -/
noncomputable def towerHom : (Full.selfExtension R S).Hom (Full.selfExtension R T) :=
  (Algebra.Generators.defaultHom (Algebra.Generators.self R S)
    (Algebra.Generators.self R T)).toExtensionHom

variable [Algebra S₀ S] [Algebra S₀ T] [IsScalarTower S₀ S T]

/-- The cotangent complex `L_{S/R}` of a ring map, viewed as an object of the derived category
of `S₀`-modules.  For `S₀ = S` this is the object `Full.cotangentComplex R S` after the
(identity) restriction of scalars. -/
noncomputable def cotangentComplexOver : DerivedCategory (ModuleCat.{u} S₀) :=
  objectOver R S (Full.selfExtension R S)

/-- The restriction comparison morphism `L_{S/R} ⟶ L_{T/R}` attached to a tower `R → S → T`,
as an actual morphism in the derived category of `S₀`-modules.  In the geometric situation
`R = Γ(Y,V)`, `S = Γ(X,U)`, `T = Γ(X,U')` with `U' ⊆ U`, this is the comparison map of the
affine-local cotangent complex along the refinement of charts. -/
noncomputable def towerComparison :
    cotangentComplexOver (S₀ := S₀) R S ⟶ cotangentComplexOver (S₀ := S₀) R T :=
  derivedMapOver (towerHom R S T)

end Tower

section TowerCoherence

variable {S₀ : Type u} [CommRing S₀]
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra S₀ S]

/-- The comparison map of a chart with itself is the identity. -/
theorem towerComparison_self :
    towerComparison (S₀ := S₀) R S S = 𝟙 (cotangentComplexOver R S) :=
  (derivedMapOver_eq (towerHom R S S) (Algebra.Extension.Hom.id _)).trans derivedMapOver_id

end TowerCoherence

section TowerTrans

variable {S₀ : Type u} [CommRing S₀]
variable (R S T W : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing W]
variable [Algebra R S] [Algebra R T] [Algebra R W]
variable [Algebra S T] [Algebra S W] [Algebra T W]
variable [IsScalarTower R S T] [IsScalarTower R S W] [IsScalarTower R T W]
variable [IsScalarTower S T W]
variable [Algebra S₀ S] [Algebra S₀ T] [Algebra S₀ W]
variable [IsScalarTower S₀ S T] [IsScalarTower S₀ S W] [IsScalarTower S₀ T W]

/-- The comparison maps commute with chart refinements: for a chain `R → S → T → W` the
comparison of the outer pair is the composite of the two intermediate comparisons. -/
theorem towerComparison_trans :
    towerComparison (S₀ := S₀) R S W =
      towerComparison (S₀ := S₀) R S T ≫ towerComparison (S₀ := S₀) R T W := by
  refine Eq.trans (derivedMapOver_eq (towerHom R S W)
    ((towerHom R T W).comp (towerHom R S T))) ?_
  exact derivedMapOver_comp (towerHom R S T) (towerHom R T W)

end TowerTrans

/-! ### Étale maps: vanishing and base change of cohomology -/

section Etale

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The cotangent complex of a formally étale ring map vanishes.  For an étale atlas this is
the statement `L_{U'/U} = 0`. -/
theorem isZero_cotangentComplex_of_formallyEtale [Algebra.FormallyEtale S T] :
    IsZero (Full.cotangentComplex S T) :=
  (Full.formallyEtale_iff_isZero S T).mp inferInstance

/-- The cotangent complex of an étale ring map vanishes. -/
theorem isZero_cotangentComplex_of_etale [Algebra.Etale S T] :
    IsZero (Full.cotangentComplex S T) :=
  isZero_cotangentComplex_of_formallyEtale S T

/-- Along a formally étale map `S → T` the module of relative differentials over `R` is the
base change: `T ⊗_S Ω_{S/R} ≃ Ω_{T/R}`. -/
noncomputable def kaehlerRestrictionEquiv [Algebra.FormallyEtale S T] :
    (T ⊗[S] Ω[S⁄R]) ≃ₗ[T] Ω[T⁄R] :=
  KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T

/-- `H⁰` of the cotangent complex base changes along a formally étale map: this is the
atlas-compatibility statement for degree zero. -/
noncomputable def cohomologyZeroEtaleIso [Algebra.FormallyEtale S T] :
    ModuleCat.of T (T ⊗[S] Ω[S⁄R]) ≅ Full.cohomology (Full.cotangentComplex R T) 0 :=
  (kaehlerRestrictionEquiv R S T).toModuleIso ≪≫ (Full.cohomologyZero R T).symm

/-- The Jacobi--Zariski base-change map is exactly the degree-zero atlas comparison. -/
theorem jzBaseChange_eq_cohomologyZeroEtaleIso [Algebra.FormallyEtale S T] :
    Full.jzBaseChange R S T = (cohomologyZeroEtaleIso R S T).hom := by
  rfl

/-- Along a formally étale map the Jacobi--Zariski base-change map is an isomorphism. -/
theorem isIso_jzBaseChange_of_formallyEtale [Algebra.FormallyEtale S T] :
    IsIso (Full.jzBaseChange R S T) := by
  rw [jzBaseChange_eq_cohomologyZeroEtaleIso]
  infer_instance

/-- Along a localisation `S → T` the module `H⁻¹` of the cotangent complex base changes. -/
noncomputable def h1CotangentLocalizationEquiv (M : Submonoid S) [IsLocalization M T] :
    (T ⊗[S] Algebra.H1Cotangent R S) ≃ₗ[T] Algebra.H1Cotangent R T :=
  Algebra.tensorH1CotangentOfIsLocalization R T M

/-- `H⁻¹` of the cotangent complex base changes along a localisation: this is the
refinement-compatibility statement for degree `-1` on a Zariski refinement of charts. -/
noncomputable def cohomologyNegOneLocalizationIso (M : Submonoid S) [IsLocalization M T] :
    ModuleCat.of T (T ⊗[S] Algebra.H1Cotangent R S) ≅
      Full.cohomology (Full.cotangentComplex R T) (-1) :=
  (h1CotangentLocalizationEquiv R S T M).toModuleIso ≪≫ (Full.cohomologyNegOne R T).symm

end Etale


/-! ### The local complex `[I/I² → Ω_M|_U]` of a closed embedding into a smooth ambient -/

section LocalEmbedding

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Algebra.Extension.{u} R S)

/-- Degree `-1` of the local two-term complex of a presentation is the conormal module
`I/I²` of the ideal `I = P.ker` cutting out the chart inside the ambient ring. -/
theorem localComplex_X_negOne :
    (Full.complex R S P).X (-1) = ModuleCat.of S P.Cotangent := rfl

/-- The conormal term of a presentation is `I/I²` for the defining ideal `I = P.ker`. -/
theorem cotangent_def : P.Cotangent = P.ker.Cotangent := rfl

/-- Degree `0` of the local two-term complex is the restriction `Ω_{M/V}|_U` of the ambient
differentials, i.e. `S ⊗_{P.Ring} Ω[P.Ring⁄R]`. -/
theorem localComplex_X_zero :
    (Full.complex R S P).X 0 = ModuleCat.of S (S ⊗[P.Ring] Ω[P.Ring⁄R]) := rfl

/-- The only differential of the local two-term complex is Mathlib's conormal map
`I/I² → Ω_{M/V}|_U`. -/
theorem localComplex_d :
    (Full.complex R S P).d (-1) 0 = ModuleCat.ofHom P.cotangentComplex :=
  Full.complex_d_negOne_zero P

/-- The local two-term complex is concentrated in degrees `-1` and `0`. -/
theorem localComplex_isZero {i : ℤ} (h1 : i ≠ -1) (h0 : i ≠ 0) :
    IsZero ((Full.complex R S P).X i) :=
  Full.complex_isZero P h1 h0

/-- Degree `0` cohomology of the local two-term complex is `H⁰(L_{S/R})`, for an arbitrary
ambient ring. -/
noncomputable def cohomologyZeroLocalIso :
    Full.cohomology (AffinePresentation.derivedObject R S P) 0 ≅
      Full.cohomology (Full.cotangentComplex R S) 0 :=
  Full.cohomologyZeroIso P ≪≫ (Full.cohomologyZero R S).symm

/-- If the ambient ring is formally smooth over the base, degree `-1` cohomology of the local
two-term complex `[I/I² → Ω_{M/V}|_U]` is `H⁻¹(L_{S/R})`.  Together with
`cohomologyZeroLocalIso` and `localComplex_isZero` this is the local smooth-embedding
comparison at the level of cohomology. -/
noncomputable def cohomologyNegOneSmoothLocalIso [Algebra.FormallySmooth R P.Ring] :
    Full.cohomology (AffinePresentation.derivedObject R S P) (-1) ≅
      Full.cohomology (Full.cotangentComplex R S) (-1) :=
  Full.cohomologyNegOneIso P ≪≫ P.equivH1CotangentOfFormallySmooth.toModuleIso ≪≫
    (Full.cohomologyNegOne R S).symm

variable {ι : Type u}

/-- A presentation of the chart as a closed subscheme of an affine space over the base:
`Γ(U) = Γ(V)[xᵢ]/I`.  The cotangent complex of `Γ(V) → Γ(U)` is then canonically isomorphic to
the actual two-term complex `[I/I² → ⊕ᵢ Γ(U) dxᵢ]` placed in degrees `-1` and `0`. -/
noncomputable def embeddingIso (G : Algebra.Generators R S ι) :
    Full.cotangentComplex R S ≅ DerivedCategory.Q.obj (Full.complex R S G.toExtension) :=
  Full.presentationIso G

/-- The embedding comparison is the canonical comparison morphism of presentations: it does
not depend on any choice beyond the embedding itself. -/
theorem embeddingIso_hom (G : Algebra.Generators R S ι) :
    (embeddingIso G).hom = Full.comparePresentation G.toExtension :=
  Full.presentationIso_hom G

/-- The canonical comparison morphism attached to an embedding into affine space is an
isomorphism. -/
theorem isIso_comparePresentation (G : Algebra.Generators R S ι) :
    IsIso (Full.comparePresentation G.toExtension) := by
  rw [← embeddingIso_hom G]
  exact (embeddingIso G).isIso_hom

/-- Two embeddings into affine spaces give coherent comparisons: the public object carries no
chosen embedding. -/
theorem embeddingIso_trans {ι' : Type u} (G : Algebra.Generators R S ι)
    (G' : Algebra.Generators R S ι') :
    (embeddingIso G).symm ≪≫ embeddingIso G' = Full.generatorsIso G G' :=
  Full.presentationIso_trans G G'

/-- The embedding comparison of an embedding with itself is the identity. -/
theorem embeddingIso_self (G : Algebra.Generators R S ι) :
    (embeddingIso G).symm ≪≫ embeddingIso G = Iso.refl _ :=
  (embeddingIso_trans G G).trans (Full.generatorsIso_refl G)

/-- Degree `0` of the local complex attached to an embedding into affine space is free on the
coordinate differentials `dxᵢ`. -/
noncomputable def embeddingCotangentSpaceBasis (G : Algebra.Generators R S ι) :
    Module.Basis ι S G.toExtension.CotangentSpace :=
  G.cotangentSpaceBasis

end LocalEmbedding


/-! ### The affine-local cotangent complex of a morphism of schemes -/

section Schemes

variable {X Y : Scheme.{u}}

/-- The restriction map on sections attached to an inclusion of opens. -/
noncomputable abbrev sectionsRes (Z : Scheme.{u}) {U U' : Z.Opens} (h : U' ≤ U) :
    Γ(Z, U) →+* Γ(Z, U') :=
  (Z.presheaf.map (homOfLE h).op).hom

theorem sectionsRes_comp (Z : Scheme.{u}) {U U' U'' : Z.Opens} (h : U' ≤ U) (h' : U'' ≤ U') :
    sectionsRes Z (h'.trans h) = (sectionsRes Z h').comp (sectionsRes Z h) := by
  rw [← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

/-- An affine chart of a morphism of schemes `f : X ⟶ Y` above a fixed open `V` of `Y`: an
affine open `U` of `X` contained in `f⁻¹V`.  Only geometric data is stored: no embedding into a
smooth ambient scheme, no presentation and no cotangent complex appear as fields. -/
structure AffineChart (f : X ⟶ Y) (V : Y.Opens) where
  /-- The affine open of the source lying over `V`. -/
  U : X.Opens
  /-- The open `U` is affine. -/
  isAffineOpen : IsAffineOpen U
  /-- The open `U` lies over `V`. -/
  le : U ≤ f ⁻¹ᵁ V

namespace AffineChart

variable {f : X ⟶ Y} {V : Y.Opens}

/-- The `Γ(Y,V)`-algebra structure on the sections over an affine chart. -/
@[instance_reducible]
noncomputable def algebra (c : AffineChart f V) : Algebra Γ(Y, V) Γ(X, c.U) :=
  (f.appLE V c.U c.le).hom.toAlgebra

attribute [local instance] AffineChart.algebra

theorem algebraMap_eq (c : AffineChart f V) :
    algebraMap Γ(Y, V) Γ(X, c.U) = (f.appLE V c.U c.le).hom :=
  rfl

/-- The affine-local cotangent complex of `f` on an affine chart: the cotangent complex of the
ring map `Γ(Y,V) → Γ(X,U)`, as an actual object of `DerivedCategory (ModuleCat Γ(X,U))`. -/
noncomputable def cotangentComplex (c : AffineChart f V) :
    DerivedCategory (ModuleCat.{u} Γ(X, c.U)) :=
  Full.cotangentComplex Γ(Y, V) Γ(X, c.U)

/-- The affine-local cotangent complex of `f` on an affine chart, viewed as an object of the
derived category of `Γ(Y,V)`-modules.  This is the object in which the comparison morphisms
attached to refinements of charts live. -/
noncomputable def objectOverBase (c : AffineChart f V) :
    DerivedCategory (ModuleCat.{u} Γ(Y, V)) :=
  cotangentComplexOver (S₀ := Γ(Y, V)) Γ(Y, V) Γ(X, c.U)

/-- The restriction algebra structure attached to a refinement of affine charts. -/
@[instance_reducible]
noncomputable def resAlgebra {c c' : AffineChart f V} (h : c'.U ≤ c.U) :
    Algebra Γ(X, c.U) Γ(X, c'.U) :=
  (sectionsRes X h).toAlgebra

/-- A refinement of charts is a tower over the base: the restriction of sections is compatible
with the structure maps of the two charts. -/
theorem isScalarTower_res {c c' : AffineChart f V} (h : c'.U ≤ c.U) :
    letI := resAlgebra h
    IsScalarTower Γ(Y, V) Γ(X, c.U) Γ(X, c'.U) := by
  let _ := resAlgebra h
  refine IsScalarTower.of_algebraMap_eq' ?_
  have key : f.appLE V c.U c.le ≫ X.presheaf.map (homOfLE h).op = f.appLE V c'.U c'.le :=
    Scheme.Hom.appLE_map f c.le (homOfLE h).op
  have key' := congrArg CommRingCat.Hom.hom key
  rw [CommRingCat.hom_comp] at key'
  exact key'.symm

/-- Restriction of sections along a chain of refinements composes. -/
theorem isScalarTower_res_res {c c' c'' : AffineChart f V}
    (h : c'.U ≤ c.U) (h' : c''.U ≤ c'.U) :
    letI := resAlgebra h
    letI := resAlgebra h'
    letI := resAlgebra (h'.trans h)
    IsScalarTower Γ(X, c.U) Γ(X, c'.U) Γ(X, c''.U) := by
  let _ := resAlgebra h
  let _ := resAlgebra h'
  let _ := resAlgebra (h'.trans h)
  exact IsScalarTower.of_algebraMap_eq' (sectionsRes_comp X h h')

/-- The comparison morphism of affine-local cotangent complexes attached to a refinement of
affine charts, as an actual morphism in the derived category of `Γ(Y,V)`-modules. -/
noncomputable def comparison {c c' : AffineChart f V} (h : c'.U ≤ c.U) :
    c.objectOverBase ⟶ c'.objectOverBase :=
  letI := resAlgebra h
  letI := isScalarTower_res h
  towerComparison Γ(Y, V) Γ(X, c.U) Γ(X, c'.U)

/-- Comparison maps commute with chart refinements: for a chain `U'' ⊆ U' ⊆ U` of affine
charts the comparison of the outer pair is the composite of the two intermediate
comparisons. -/
theorem comparison_trans {c c' c'' : AffineChart f V} (h : c'.U ≤ c.U) (h' : c''.U ≤ c'.U) :
    comparison (h'.trans h) = comparison h ≫ comparison h' := by
  let _ := resAlgebra h
  let _ := resAlgebra h'
  let _ := resAlgebra (h'.trans h)
  have _ := isScalarTower_res h
  have _ := isScalarTower_res h'
  have _ := isScalarTower_res (h'.trans h)
  have _ := isScalarTower_res_res h h'
  exact towerComparison_trans Γ(Y, V) Γ(X, c.U) Γ(X, c'.U) Γ(X, c''.U)

/-! #### Basic-open refinements -/

/-- The basic open subset of an affine chart attached to a section: again an affine chart. -/
noncomputable def basicOpenChart (c : AffineChart f V) (g : Γ(X, c.U)) : AffineChart f V where
  U := X.basicOpen g
  isAffineOpen := c.isAffineOpen.basicOpen g
  le := le_trans (X.basicOpen_le g) c.le

theorem basicOpenChart_le (c : AffineChart f V) (g : Γ(X, c.U)) :
    (basicOpenChart c g).U ≤ c.U :=
  X.basicOpen_le g

theorem resAlgebra_basicOpenChart (c : AffineChart f V) (g : Γ(X, c.U)) :
    resAlgebra (basicOpenChart_le c g) =
      Scheme.algebra_section_section_basicOpen g :=
  rfl

/-- Sections over a basic open of a chart are the localisation of the sections of the chart:
a Zariski refinement of charts is a localisation, hence formally étale. -/
theorem isLocalization_basicOpenChart (c : AffineChart f V) (g : Γ(X, c.U)) :
    letI := resAlgebra (basicOpenChart_le c g)
    IsLocalization.Away g Γ(X, (basicOpenChart c g).U) :=
  c.isAffineOpen.isLocalization_basicOpen g

/-- A basic-open refinement of charts is formally étale. -/
theorem formallyEtale_basicOpenChart (c : AffineChart f V) (g : Γ(X, c.U)) :
    letI := resAlgebra (basicOpenChart_le c g)
    Algebra.FormallyEtale Γ(X, c.U) Γ(X, (basicOpenChart c g).U) :=
  let _ := resAlgebra (basicOpenChart_le c g)
  have _ := isLocalization_basicOpenChart c g
  Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)

/-- The relative cotangent complex of a basic-open refinement of charts vanishes.  This is the
local form of the atlas-independence input `L_{U'/U} = 0`. -/
theorem isZero_cotangentComplex_basicOpenChart (c : AffineChart f V) (g : Γ(X, c.U)) :
    letI := resAlgebra (basicOpenChart_le c g)
    IsZero (Full.cotangentComplex Γ(X, c.U) Γ(X, (basicOpenChart c g).U)) :=
  let _ := resAlgebra (basicOpenChart_le c g)
  have _ := isLocalization_basicOpenChart c g
  Full.isZero_cotangentComplex_of_isLocalization Γ(X, c.U) _ (Submonoid.powers g)

/-- Along a basic-open refinement, `H⁰` of the affine-local cotangent complex is the base
change of `H⁰` on the bigger chart. -/
noncomputable def cohomologyZeroBasicOpenIso (c : AffineChart f V) (g : Γ(X, c.U)) :
    letI := resAlgebra (basicOpenChart_le c g)
    ModuleCat.of Γ(X, (basicOpenChart c g).U)
        (Γ(X, (basicOpenChart c g).U) ⊗[Γ(X, c.U)] Ω[Γ(X, c.U)⁄Γ(Y, V)]) ≅
      Full.cohomology ((basicOpenChart c g).cotangentComplex) 0 :=
  letI := resAlgebra (basicOpenChart_le c g)
  letI := formallyEtale_basicOpenChart c g
  letI := isScalarTower_res (basicOpenChart_le c g)
  cohomologyZeroEtaleIso Γ(Y, V) Γ(X, c.U) Γ(X, (basicOpenChart c g).U)

/-- Along a basic-open refinement, `H⁻¹` of the affine-local cotangent complex is the base
change of `H⁻¹` on the bigger chart. -/
noncomputable def cohomologyNegOneBasicOpenIso (c : AffineChart f V) (g : Γ(X, c.U)) :
    letI := resAlgebra (basicOpenChart_le c g)
    ModuleCat.of Γ(X, (basicOpenChart c g).U)
        (Γ(X, (basicOpenChart c g).U) ⊗[Γ(X, c.U)]
          Algebra.H1Cotangent Γ(Y, V) Γ(X, c.U)) ≅
      Full.cohomology ((basicOpenChart c g).cotangentComplex) (-1) :=
  letI := resAlgebra (basicOpenChart_le c g)
  letI := isLocalization_basicOpenChart c g
  letI := isScalarTower_res (basicOpenChart_le c g)
  cohomologyNegOneLocalizationIso Γ(Y, V) Γ(X, c.U) Γ(X, (basicOpenChart c g).U)
    (Submonoid.powers g)

end AffineChart

end Schemes


/-! ### Étale covers of charts: atlas compatibility -/

section EtaleAtlas

variable {X Y W : Scheme.{u}} {f : X ⟶ Y} {V : Y.Opens}

namespace AffineChart

attribute [local instance] AffineChart.algebra

/-- An affine open of an étale (or arbitrary) `X`-scheme lying over an affine chart of `f` is
again an affine chart, now of the composite `e ≫ f`.  For `e` an étale atlas of the source,
these are exactly the charts of the atlas lying over the given chart. -/
noncomputable def coverChart (c : AffineChart f V) (e : W ⟶ X) (U' : W.Opens)
    (hU' : IsAffineOpen U') (h : U' ≤ e ⁻¹ᵁ c.U) : AffineChart (e ≫ f) V where
  U := U'
  isAffineOpen := hU'
  le := by
    intro x hx
    have hx' : e.base x ∈ c.U := h hx
    have hx'' : f.base (e.base x) ∈ V := c.le hx'
    simpa using hx''

@[simp]
theorem coverChart_U (c : AffineChart f V) (e : W ⟶ X) (U' : W.Opens)
    (hU' : IsAffineOpen U') (h : U' ≤ e ⁻¹ᵁ c.U) :
    (coverChart c e U' hU' h).U = U' :=
  rfl

/-- Sections over an affine open of an étale `X`-scheme form an étale algebra over the
sections of the chart underneath: the transition maps of an étale atlas are étale ring
maps. -/
theorem etale_appLE (c : AffineChart f V) (e : W ⟶ X) [Etale e] (U' : W.Opens)
    (hU' : IsAffineOpen U') (h : U' ≤ e ⁻¹ᵁ c.U) :
    RingHom.Etale (e.appLE c.U U' h).hom :=
  HasRingHomProperty.appLE @Etale e inferInstance ⟨c.U, c.isAffineOpen⟩ ⟨U', hU'⟩ h

/-- The relative cotangent complex of an étale cover of a chart vanishes, `L_{U'/U} = 0`.
This is the atlas-independence input: the cotangent complex of a Deligne--Mumford stack is
insensitive to replacing a chart by an étale cover of it. -/
theorem isZero_cotangentComplex_etaleCover (c : AffineChart f V) (e : W ⟶ X) [Etale e]
    (U' : W.Opens) (hU' : IsAffineOpen U') (h : U' ≤ e ⁻¹ᵁ c.U) :
    letI := (e.appLE c.U U' h).hom.toAlgebra
    IsZero (Full.cotangentComplex Γ(X, c.U) Γ(W, U')) :=
  let _ := (e.appLE c.U U' h).hom.toAlgebra
  have _ : Algebra.Etale Γ(X, c.U) Γ(W, U') := etale_appLE c e U' hU' h
  isZero_cotangentComplex_of_etale Γ(X, c.U) Γ(W, U')

/-- The charts of an étale cover are a tower over the base: the structure map of the cover
chart factors through the chart underneath. -/
theorem isScalarTower_coverChart (c : AffineChart f V) (e : W ⟶ X) (U' : W.Opens)
    (hU' : IsAffineOpen U') (h : U' ≤ e ⁻¹ᵁ c.U) :
    letI : Algebra Γ(X, c.U) Γ(W, (coverChart c e U' hU' h).U) :=
      (e.appLE c.U U' h).hom.toAlgebra
    IsScalarTower Γ(Y, V) Γ(X, c.U) Γ(W, (coverChart c e U' hU' h).U) := by
  let _ : Algebra Γ(X, c.U) Γ(W, (coverChart c e U' hU' h).U) :=
    (e.appLE c.U U' h).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have key : f.appLE V c.U c.le ≫ e.appLE c.U U' h =
      (e ≫ f).appLE V U' (coverChart c e U' hU' h).le :=
    Scheme.Hom.appLE_comp_appLE e f V c.U U' c.le h
  have key' := congrArg CommRingCat.Hom.hom key
  rw [CommRingCat.hom_comp] at key'
  exact key'.symm

/-- Atlas compatibility in degree zero: along an étale cover of a chart, `H⁰` of the
affine-local cotangent complex is the base change of `H⁰` on the chart underneath. -/
noncomputable def cohomologyZeroEtaleCoverIso (c : AffineChart f V) (e : W ⟶ X) [Etale e]
    (U' : W.Opens) (hU' : IsAffineOpen U') (h : U' ≤ e ⁻¹ᵁ c.U) :
    letI : Algebra Γ(X, c.U) Γ(W, (coverChart c e U' hU' h).U) :=
      (e.appLE c.U U' h).hom.toAlgebra
    ModuleCat.of Γ(W, (coverChart c e U' hU' h).U)
        (Γ(W, (coverChart c e U' hU' h).U) ⊗[Γ(X, c.U)] Ω[Γ(X, c.U)⁄Γ(Y, V)]) ≅
      Full.cohomology ((coverChart c e U' hU' h).cotangentComplex) 0 :=
  letI : Algebra Γ(X, c.U) Γ(W, (coverChart c e U' hU' h).U) :=
    (e.appLE c.U U' h).hom.toAlgebra
  letI : Algebra.Etale Γ(X, c.U) Γ(W, (coverChart c e U' hU' h).U) :=
    etale_appLE c e U' hU' h
  letI := isScalarTower_coverChart c e U' hU' h
  cohomologyZeroEtaleIso Γ(Y, V) Γ(X, c.U) Γ(W, (coverChart c e U' hU' h).U)

end AffineChart

end EtaleAtlas

/-! ### Transitivity -/

section Transitivity

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- All cohomology of the relative cotangent complex of a formally étale step vanishes. -/
theorem isZero_cohomology_of_formallyEtale [Algebra.FormallyEtale S T] (n : ℤ) :
    IsZero (Full.cohomology (Full.cotangentComplex S T) n) :=
  (Modules.Derived.cohomologyFunctor (ModuleCat.{u} T) n).map_isZero
    (isZero_cotangentComplex_of_formallyEtale S T)

/-- For a formally étale second step the first map of the Jacobi--Zariski sequence vanishes. -/
theorem jzH1Map_eq_zero [Algebra.FormallyEtale S T] : Full.jzH1Map R S T = 0 :=
  (isZero_cohomology_of_formallyEtale S T (-1)).eq_of_tgt _ _

/-- For a formally étale second step the last map of the Jacobi--Zariski sequence vanishes,
so `H⁰(L_{T/R})` is generated by the base change of `H⁰(L_{S/R})`. -/
theorem jzOmegaMap_eq_zero [Algebra.FormallyEtale S T] : Full.jzOmegaMap R S T = 0 :=
  (isZero_cohomology_of_formallyEtale S T 0).eq_of_tgt _ _

/-- For a formally étale second step the Jacobi--Zariski connecting map vanishes. -/
theorem jzDelta_eq_zero [Algebra.FormallyEtale S T] : Full.jzDelta R S T = 0 :=
  (isZero_cohomology_of_formallyEtale S T (-1)).eq_of_src _ _

end Transitivity


/-! ### Étale atlases of Deligne--Mumford stacks -/

section DeligneMumford

attribute [local instance] AffineChart.algebra

variable {Z : DeligneMumfordStack.{u}}

/-- Every base change of an étale atlas is presented by an actual scheme. -/
theorem nonempty_atlasPullbackPresentation {A : StackChart Z.toStack}
    (hA : A.IsEtaleSurjective) (T : Scheme.{u}) (x : StackFiber Z.toStack T) :
    Nonempty (A.PullbackPresentation T x) :=
  hA.1 T x

/-- The projection of any base change of an étale atlas is an étale morphism of schemes; in
particular the source and target maps of the presentation groupoid of the atlas are étale. -/
theorem etale_atlasPullbackPresentation_fst {A : StackChart Z.toStack}
    (hA : A.IsEtaleSurjective) {T : Scheme.{u}} {x : StackFiber Z.toStack T}
    (p : A.PullbackPresentation T x) : Etale p.fst :=
  (hA.2 T x p).1

/-- The atlas-independence input for a Deligne--Mumford stack.  Let `A` be an étale atlas, let
`p` present the self-overlap `A.scheme ×_Z A.scheme`, let `f` be a morphism from the atlas
scheme to a base scheme, `c` an affine chart of `f` and `U'` an affine open of the overlap
lying over `c`.  Then the relative cotangent complex of the chart transition vanishes, so the
affine-local cotangent complexes of the atlas form a descent datum whose transition complexes
are zero. -/
theorem isZero_cotangentComplex_atlasTransition {A : StackChart Z.toStack}
    (hA : A.IsEtaleSurjective) {T : Scheme.{u}} {x : StackFiber Z.toStack T}
    (p : A.PullbackPresentation T x)
    {Y : Scheme.{u}} {f : T ⟶ Y} {V : Y.Opens} (c : AffineChart f V)
    (U' : p.space.Opens) (hU' : IsAffineOpen U') (h : U' ≤ p.fst ⁻¹ᵁ c.U) :
    letI := (p.fst.appLE c.U U' h).hom.toAlgebra
    IsZero (Full.cotangentComplex Γ(T, c.U) Γ(p.space, U')) :=
  have _ : Etale p.fst := etale_atlasPullbackPresentation_fst hA p
  AffineChart.isZero_cotangentComplex_etaleCover c p.fst U' hU' h

/-- Degree-zero atlas compatibility for a Deligne--Mumford stack: along a chart transition of
an étale atlas, `H⁰` of the affine-local cotangent complex is the base change of `H⁰` on the
chart underneath. -/
noncomputable def cohomologyZeroAtlasTransitionIso {A : StackChart Z.toStack}
    (hA : A.IsEtaleSurjective) {T : Scheme.{u}} {x : StackFiber Z.toStack T}
    (p : A.PullbackPresentation T x)
    {Y : Scheme.{u}} {f : T ⟶ Y} {V : Y.Opens} (c : AffineChart f V)
    (U' : p.space.Opens) (hU' : IsAffineOpen U') (h : U' ≤ p.fst ⁻¹ᵁ c.U) :
    letI : Algebra Γ(T, c.U) Γ(p.space, (AffineChart.coverChart c p.fst U' hU' h).U) :=
      (p.fst.appLE c.U U' h).hom.toAlgebra
    ModuleCat.of Γ(p.space, (AffineChart.coverChart c p.fst U' hU' h).U)
        (Γ(p.space, (AffineChart.coverChart c p.fst U' hU' h).U) ⊗[Γ(T, c.U)]
          Ω[Γ(T, c.U)⁄Γ(Y, V)]) ≅
      Full.cohomology ((AffineChart.coverChart c p.fst U' hU' h).cotangentComplex) 0 :=
  letI : Etale p.fst := etale_atlasPullbackPresentation_fst hA p
  AffineChart.cohomologyZeroEtaleCoverIso c p.fst U' hU' h

/-- Every Deligne--Mumford stack carries an étale atlas all of whose chart transitions have
vanishing relative cotangent complex.  The statement mentions no chosen atlas and no chosen
embedding: the atlas is produced from the stack's own étale-atlas hypothesis. -/
theorem exists_etaleAtlas_isZero_cotangentComplex_transition (Z : DeligneMumfordStack.{u}) :
    ∃ A : StackChart Z.toStack, A.IsEtaleSurjective ∧
      ∀ (T : Scheme.{u}) (x : StackFiber Z.toStack T)
        (p : A.PullbackPresentation T x) (Y : Scheme.{u}) (f : T ⟶ Y) (V : Y.Opens)
        (c : AffineChart f V) (U' : p.space.Opens) (_ : IsAffineOpen U')
        (h : U' ≤ p.fst ⁻¹ᵁ c.U),
        letI := (p.fst.appLE c.U U' h).hom.toAlgebra
        IsZero (Full.cotangentComplex Γ(T, c.U) Γ(p.space, U')) := by
  obtain ⟨A, hA⟩ := Z.etaleAtlas
  exact ⟨A, hA, fun _ _ p _ _ _ c U' hU' h =>
    isZero_cotangentComplex_atlasTransition hA p c U' hU' h⟩

end DeligneMumford

end Global

end GromovWitten.AlgebraicGeometry.CotangentComplex
