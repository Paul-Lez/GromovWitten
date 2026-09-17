/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.Picard
import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectComplex
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Category.Cat

/-!
# `h¹/h⁰` for derived two-term complexes

`Cones/Picard.lean` builds the translation groupoid `[E¹/E⁰]` of a two-term complex of modules
and turns chain maps into functors, chain homotopies into natural isomorphisms, and
quasi-isomorphisms into equivalences.  This file assembles that data into a genuine
`2`-functor and transports it to the derived setting.

## Main results

* `LinearTwoTermComplex.instCategory`: two-term complexes of `R`-modules form a category.
* `LinearTwoTermComplex.picardFunctor`: the assignment `E ↦ [E¹/E⁰]` is an honest functor into
  `Cat`, with the pseudofunctor comparison `2`-cells `picardCompIso`, `picardIdIso` and their
  associativity and unit coherence laws proved (here they are strict, which is a theorem about
  the chain-level formulas, not an assumption).
* `LinearTwoTermComplex.ChainHomotopy.refl`, `vcomp`, `symm`, `postcomp`, `precomp`, `hcomp`:
  chain homotopies form the invertible `2`-cells, and `natTrans_vcomp`, `natTrans_symm`,
  `natTrans_postcomp`, `natTrans_precomp`, `natTrans_hcomp` prove that `ChainHomotopy.natTrans`
  is `2`-functorial for all of these operations.
* `LinearTwoTermComplex.cochainFunctor`: a cochain complex of modules has an underlying two-term
  complex in degrees `-1` and `0`, functorially in chain maps.
* `GlobalTwoTermResolution.picard`: the Picard groupoid `h¹/h⁰(E)` computed from a chosen global
  two-term resolution of a derived object `E`, whose vertex automorphisms are `h⁰` and whose
  isomorphism classes are `h¹`.
* `GlobalTwoTermResolution.Comparison` and
  `GlobalTwoTermResolution.nonempty_picardEquivalence_of_hasChainComparison`: resolution
  independence under an explicit chain-level comparison, compatibly with composition of
  comparisons.
* `GlobalTwoTermResolution.isKProjective`, `exists_chain_realization`, `exists_homotopyEquiv`,
  `hasChainComparison` and `nonempty_picardEquivalence`: the chain-level comparison always
  exists, so **resolution independence holds with no hypothesis at all**: any two global
  two-term resolutions of the same derived object have equivalent Picard groupoids.
* `HomotopyEquivalence.quasiIsoInverseIso` and `AcyclicSummand.inverseIsoProjection`: the
  inverse of the equivalence produced by a quasi-isomorphism agrees with the chain-level inverse,
  in particular with the projection of the acyclic summand `[K ≃ K]`.

## Implementation notes

The lifting of the derived comparison isomorphism to an actual chain map is the bijectivity of
`Hom_{K(R)}(P, X) → Hom_{D(R)}(P, X)` for `P` a bounded above complex of projectives; this is
`CochainComplex.IsKProjective.Qh_map_bijective` in Mathlib, and the resolving complex of a
global two-term resolution is K-projective because it is concentrated in degrees `-1` and `0`
and its terms are free.  The passage from the resulting quasi-isomorphism back to chain-level
data uses `CochainComplex.IsKProjective.quasiIso_iff`, which turns it into a homotopy
equivalence of cochain complexes; `LinearTwoTermComplex.ofHomotopyEquiv` restricts that to the
two-term complexes.

## What is not proved

The equivalence of Picard groupoids attached to two resolutions is not canonical: the realizing
chain map is unique only up to homotopy, so the equivalence is well defined only up to the
`2`-cells produced by `ChainHomotopy.natIso`.  No uniqueness statement for it is proved here.
Nor is the elementwise `LinearTwoTermComplex.Hom.IsQuasiIsomorphism` predicate compared with
Mathlib's `QuasiIso`; that comparison would need the identification of the homology of a
`[-1, 0]`-complex in degrees `-1` and `0` with the kernel and the cokernel of its differential,
which Mathlib does not provide in usable elementwise form for `ModuleCat`.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-! ## Inverses of equivalences with a common functor -/

/-- Two equivalences with the same underlying functor have canonically isomorphic inverses.
This is the uniqueness of right adjoints; it is what compares the noncomputable inverse produced
by `Functor.asEquivalence` with an explicitly constructed inverse. -/
noncomputable def equivalenceInverseIso {C : Type*} [Category C] {D : Type*} [Category D]
    (e e' : C ≌ D) (h : e.functor = e'.functor) : e.inverse ≅ e'.inverse :=
  Adjunction.rightAdjointUniq (e.toAdjunction.ofNatIsoLeft (eqToIso h)) e'.toAdjunction

namespace LinearTwoTermComplex

/-! ## The category of two-term complexes -/

/-- Two chain maps agreeing in both degrees are equal; the commutation law is a proposition. -/
@[ext]
theorem Hom.ext {E F : LinearTwoTermComplex R} {f g : Hom E F}
    (h0 : f.degreeZero = g.degreeZero) (h1 : f.degreeOne = g.degreeOne) : f = g := by
  revert h0 h1
  obtain ⟨f0, f1, -⟩ := f
  obtain ⟨g0, g1, -⟩ := g
  rintro rfl rfl
  rfl

/-- Two-term complexes of `R`-modules and chain maps form a category. -/
instance instCategory : Category.{u} (LinearTwoTermComplex R) where
  Hom E F := Hom E F
  id E := Hom.id E
  comp f g := Hom.comp g f

@[simp]
theorem id_degreeZero (E : LinearTwoTermComplex R) :
    (𝟙 E : Hom E E).degreeZero = LinearMap.id :=
  rfl

@[simp]
theorem id_degreeOne (E : LinearTwoTermComplex R) :
    (𝟙 E : Hom E E).degreeOne = LinearMap.id :=
  rfl

@[simp]
theorem comp_degreeZero {E F G : LinearTwoTermComplex R} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).degreeZero = g.degreeZero.comp f.degreeZero :=
  rfl

@[simp]
theorem comp_degreeOne {E F G : LinearTwoTermComplex R} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).degreeOne = g.degreeOne.comp f.degreeOne :=
  rfl

/-- Categorical composition is the chain-level composition of `Cones/Picard.lean`. -/
theorem comp_eq {E F G : LinearTwoTermComplex R} (f : E ⟶ F) (g : F ⟶ G) :
    f ≫ g = g.comp f :=
  rfl

/-- The categorical identity is the chain-level identity of `Cones/Picard.lean`. -/
theorem id_eq (E : LinearTwoTermComplex R) : 𝟙 E = Hom.id E :=
  rfl

/-! ## The Picard groupoid as a functor into `Cat` -/

/-- The `h¹/h⁰` construction as a functor from two-term complexes to categories: a complex goes
to its translation groupoid `[E¹/E⁰]` and a chain map to the induced functor. -/
def picardFunctor (R : Type u) [CommRing R] : LinearTwoTermComplex R ⥤ Cat.{u, u} where
  obj E := Cat.of E.quotient
  map f := f.quotientFunctor.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem picardFunctor_obj (E : LinearTwoTermComplex R) :
    (picardFunctor R).obj E = Cat.of E.quotient :=
  rfl

@[simp]
theorem picardFunctor_map {E F : LinearTwoTermComplex R} (f : E ⟶ F) :
    (picardFunctor R).map f = f.quotientFunctor.toCatHom :=
  rfl

/-- The specified comparison `2`-cell of the `h¹/h⁰` pseudofunctor: the functor induced by a
composite of chain maps against the composite of the induced functors.  The chain-level formulas
make it the identity, so the pseudofunctor is strict. -/
def picardCompIso {E F G : LinearTwoTermComplex R} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).quotientFunctor ≅ f.quotientFunctor ⋙ g.quotientFunctor :=
  Iso.refl _

/-- The specified unit comparison `2`-cell of the `h¹/h⁰` pseudofunctor. -/
def picardIdIso (E : LinearTwoTermComplex R) :
    (𝟙 E : Hom E E).quotientFunctor ≅ 𝟭 E.quotient :=
  Iso.refl _

/-- Associativity coherence for the composition comparison `2`-cells. -/
theorem picardCompIso_assoc {E F G H : LinearTwoTermComplex R} (f : E ⟶ F) (g : F ⟶ G)
    (h : G ⟶ H) :
    (picardCompIso (f ≫ g) h).hom ≫ Functor.whiskerRight (picardCompIso f g).hom h.quotientFunctor =
      (picardCompIso f (g ≫ h)).hom ≫
        Functor.whiskerLeft f.quotientFunctor (picardCompIso g h).hom := by
  apply NatTrans.ext
  funext x
  apply TwoTermQuotient.Hom.ext
  change (0 : H.degreeZero) + h.degreeZero 0 = 0 + 0
  simp

/-- Left unit coherence for the comparison `2`-cells. -/
theorem picardCompIso_id_left {E F : LinearTwoTermComplex R} (f : E ⟶ F) :
    (picardCompIso (𝟙 E) f).hom ≫ Functor.whiskerRight (picardIdIso E).hom f.quotientFunctor =
      𝟙 f.quotientFunctor := by
  apply NatTrans.ext
  funext x
  apply TwoTermQuotient.Hom.ext
  change (0 : F.degreeZero) + f.degreeZero 0 = 0
  simp

/-- Right unit coherence for the comparison `2`-cells. -/
theorem picardCompIso_id_right {E F : LinearTwoTermComplex R} (f : E ⟶ F) :
    (picardCompIso f (𝟙 F)).hom ≫ Functor.whiskerLeft f.quotientFunctor (picardIdIso F).hom =
      𝟙 f.quotientFunctor := by
  apply NatTrans.ext
  funext x
  apply TwoTermQuotient.Hom.ext
  change (0 : F.degreeZero) + 0 = 0
  simp

/-! ## Chain homotopies as invertible `2`-cells -/

namespace ChainHomotopy

variable {D E F G : LinearTwoTermComplex R}

/-- The identity `2`-cell of a chain map: the zero homotopy. -/
def refl (f : Hom E F) : ChainHomotopy f f where
  homotopy := 0
  degreeZero x := by simp
  degreeOne x := by simp

@[simp]
theorem refl_homotopy (f : Hom E F) : (refl f).homotopy = 0 :=
  rfl

/-- Vertical composition of chain homotopies: homotopies add. -/
def vcomp {f g h : Hom E F} (H : ChainHomotopy f g) (H' : ChainHomotopy g h) :
    ChainHomotopy f h where
  homotopy := H.homotopy + H'.homotopy
  degreeZero x := by
    rw [H'.degreeZero, H.degreeZero, LinearMap.add_apply, add_assoc]
  degreeOne x := by
    rw [H'.degreeOne, H.degreeOne, LinearMap.add_apply, map_add, add_assoc]

@[simp]
theorem vcomp_homotopy {f g h : Hom E F} (H : ChainHomotopy f g) (H' : ChainHomotopy g h) :
    (H.vcomp H').homotopy = H.homotopy + H'.homotopy :=
  rfl

/-- Chain homotopy is symmetric: negate the homotopy. -/
def symm {f g : Hom E F} (H : ChainHomotopy f g) : ChainHomotopy g f where
  homotopy := -H.homotopy
  degreeZero x := by
    rw [H.degreeZero]
    simp
  degreeOne x := by
    rw [H.degreeOne]
    simp

@[simp]
theorem symm_homotopy {f g : Hom E F} (H : ChainHomotopy f g) :
    H.symm.homotopy = -H.homotopy :=
  rfl

/-- Post-composing a chain homotopy with a chain map. -/
def postcomp {f g : Hom E F} (H : ChainHomotopy f g) (k : Hom F G) :
    ChainHomotopy (k.comp f) (k.comp g) where
  homotopy := k.degreeZero.comp H.homotopy
  degreeZero x := by
    change k.degreeZero (g.degreeZero x) = k.degreeZero (f.degreeZero x) + _
    rw [H.degreeZero, map_add]
    rfl
  degreeOne x := by
    change k.degreeOne (g.degreeOne x) = k.degreeOne (f.degreeOne x) + _
    rw [H.degreeOne, map_add, k.comm]
    rfl

@[simp]
theorem postcomp_homotopy {f g : Hom E F} (H : ChainHomotopy f g) (k : Hom F G) :
    (H.postcomp k).homotopy = k.degreeZero.comp H.homotopy :=
  rfl

/-- Pre-composing a chain homotopy with a chain map. -/
def precomp {f g : Hom E F} (H : ChainHomotopy f g) (k : Hom D E) :
    ChainHomotopy (f.comp k) (g.comp k) where
  homotopy := H.homotopy.comp k.degreeOne
  degreeZero x := by
    change g.degreeZero (k.degreeZero x) = f.degreeZero (k.degreeZero x) + _
    rw [H.degreeZero, ← k.comm]
    rfl
  degreeOne x := by
    change g.degreeOne (k.degreeOne x) = f.degreeOne (k.degreeOne x) + _
    rw [H.degreeOne]
    rfl

@[simp]
theorem precomp_homotopy {f g : Hom E F} (H : ChainHomotopy f g) (k : Hom D E) :
    (H.precomp k).homotopy = H.homotopy.comp k.degreeOne :=
  rfl

/-- Horizontal composition of chain homotopies. -/
def hcomp {f f' : Hom D E} {g g' : Hom E F} (H : ChainHomotopy f f')
    (H' : ChainHomotopy g g') : ChainHomotopy (g.comp f) (g'.comp f') :=
  (H'.precomp f).vcomp (H.postcomp g')

/-! ### Compatibility of the induced natural transformations -/

/-- The natural isomorphism induced by a chain homotopy has the induced natural transformation
as its forward direction. -/
@[simp]
theorem natIso_hom {f g : Hom E F} (H : ChainHomotopy f g) : H.natIso.hom = H.natTrans :=
  rfl

@[simp]
theorem natTrans_app_val {f g : Hom E F} (H : ChainHomotopy f g) (x : E.quotient) :
    (H.natTrans.app x).val = H.homotopy x.back :=
  rfl

/-- The zero homotopy induces the identity natural transformation. -/
@[simp]
theorem natTrans_refl (f : Hom E F) : (refl f).natTrans = 𝟙 f.quotientFunctor := by
  apply NatTrans.ext
  funext x
  apply TwoTermQuotient.Hom.ext
  simp

/-- Vertical composition of homotopies induces composition of natural transformations. -/
@[simp]
theorem natTrans_vcomp {f g h : Hom E F} (H : ChainHomotopy f g) (H' : ChainHomotopy g h) :
    (H.vcomp H').natTrans = H.natTrans ≫ H'.natTrans := by
  apply NatTrans.ext
  funext x
  apply TwoTermQuotient.Hom.ext
  simp

/-- The reversed homotopy induces the inverse natural isomorphism. -/
theorem natTrans_symm {f g : Hom E F} (H : ChainHomotopy f g) :
    H.symm.natTrans = H.natIso.inv := by
  apply NatTrans.ext
  funext x
  apply TwoTermQuotient.Hom.ext
  have h := congrArg TwoTermQuotient.Hom.val (H.natIso.hom_inv_id_app x)
  rw [TwoTermQuotient.comp_val, TwoTermQuotient.id_val, natIso_hom, natTrans_app_val] at h
  change -H.homotopy x.back = _
  exact (eq_neg_of_add_eq_zero_right h).symm

/-- Post-composition of a homotopy with a chain map is right whiskering. -/
@[simp]
theorem natTrans_postcomp {f g : Hom E F} (H : ChainHomotopy f g) (k : Hom F G) :
    (H.postcomp k).natTrans = Functor.whiskerRight H.natTrans k.quotientFunctor := by
  apply NatTrans.ext
  funext x
  apply TwoTermQuotient.Hom.ext
  rfl

/-- Pre-composition of a homotopy with a chain map is left whiskering. -/
@[simp]
theorem natTrans_precomp {f g : Hom E F} (H : ChainHomotopy f g) (k : Hom D E) :
    (H.precomp k).natTrans = Functor.whiskerLeft k.quotientFunctor H.natTrans := by
  apply NatTrans.ext
  funext x
  apply TwoTermQuotient.Hom.ext
  rfl

/-- Horizontal composition of homotopies induces horizontal composition of the natural
transformations. -/
theorem natTrans_hcomp {f f' : Hom D E} {g g' : Hom E F} (H : ChainHomotopy f f')
    (H' : ChainHomotopy g g') :
    (H.hcomp H').natTrans = NatTrans.hcomp H.natTrans H'.natTrans := by
  apply NatTrans.ext
  funext x
  apply TwoTermQuotient.Hom.ext
  rfl

end ChainHomotopy

/-! ## Two-term complexes underlying cochain complexes -/

/-- The two-term complex in degrees `-1` and `0` underlying a cochain complex of modules. -/
def ofCochainComplex (K : CochainComplex (ModuleCat.{u} R) ℤ) : LinearTwoTermComplex R where
  degreeZero := K.X (-1)
  degreeOne := K.X 0
  differential := (K.d (-1) 0).hom

@[simp]
theorem ofCochainComplex_differential (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (ofCochainComplex K).differential = (K.d (-1) 0).hom :=
  rfl

/-- A chain map of cochain complexes restricts to a chain map of the underlying two-term
complexes. -/
def ofCochainComplexHom {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) :
    Hom (ofCochainComplex K) (ofCochainComplex L) where
  degreeZero := (φ.f (-1)).hom
  degreeOne := (φ.f 0).hom
  comm x := by
    have h : (ModuleCat.Hom.hom (φ.f (-1) ≫ L.d (-1) 0)) x =
        (ModuleCat.Hom.hom (K.d (-1) 0 ≫ φ.f 0)) x := by
      rw [φ.comm (-1) 0]
    exact h.symm

@[simp]
theorem ofCochainComplexHom_degreeZero {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) :
    (ofCochainComplexHom φ).degreeZero = (φ.f (-1)).hom :=
  rfl

@[simp]
theorem ofCochainComplexHom_degreeOne {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) :
    (ofCochainComplexHom φ).degreeOne = (φ.f 0).hom :=
  rfl

@[simp]
theorem ofCochainComplexHom_id (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ofCochainComplexHom (𝟙 K) = Hom.id (ofCochainComplex K) := by
  ext <;> rfl

@[simp]
theorem ofCochainComplexHom_comp {K L M : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)
    (ψ : L ⟶ M) :
    ofCochainComplexHom (φ ≫ ψ) = (ofCochainComplexHom ψ).comp (ofCochainComplexHom φ) := by
  ext <;> rfl

/-- Taking the two-term complex in degrees `-1` and `0` is a functor from cochain complexes of
modules to two-term complexes. -/
def cochainFunctor (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ LinearTwoTermComplex R where
  obj := ofCochainComplex
  map := ofCochainComplexHom
  map_id K := ofCochainComplexHom_id K
  map_comp φ ψ := ofCochainComplexHom_comp φ ψ

/-- The `h¹/h⁰` groupoid of a cochain complex of modules, as a functor into `Cat`. -/
def cochainPicardFunctor (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ Cat.{u, u} :=
  cochainFunctor R ⋙ picardFunctor R

@[simp]
theorem cochainPicardFunctor_obj (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainPicardFunctor R).obj K = Cat.of (ofCochainComplex K).quotient :=
  rfl

/-! ## Homotopies of cochain complexes -/

/-- A homotopy between two chain maps of cochain complexes restricts to a chain homotopy of the
underlying two-term complexes, provided the source vanishes in degree `1` and the target
vanishes in degree `-2`; this is what kills the two homotopy components outside the displayed
window. -/
def ofHomotopy {K L : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsZero (K.X 1))
    (hL : IsZero (L.X (-2))) {φ ψ : K ⟶ L} (H : Homotopy φ ψ) :
    ChainHomotopy (ofCochainComplexHom ψ) (ofCochainComplexHom φ) where
  homotopy := (H.hom 0 (-1)).hom
  degreeZero x := by
    have hcomm := H.comm (-1)
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp),
      hL.eq_of_tgt (H.hom (-1) (-2)) 0, zero_comp, add_zero] at hcomm
    have hmor : φ.f (-1) = ψ.f (-1) + K.d (-1) 0 ≫ H.hom 0 (-1) := by
      rw [hcomm]
      abel
    exact congrArg (fun m : K.X (-1) ⟶ L.X (-1) => (ModuleCat.Hom.hom m) x) hmor
  degreeOne x := by
    have hcomm := H.comm 0
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
      hK.eq_of_tgt (K.d 0 1) 0, zero_comp, zero_add] at hcomm
    have hmor : φ.f 0 = ψ.f 0 + H.hom 0 (-1) ≫ L.d (-1) 0 := by
      rw [hcomm]
      abel
    exact congrArg (fun m : K.X 0 ⟶ L.X 0 => (ModuleCat.Hom.hom m) x) hmor

/-- A homotopy equivalence of cochain complexes supported in degrees `-1` and `0` restricts to a
chain-homotopy equivalence of the underlying two-term complexes. -/
def ofHomotopyEquiv {K L : CochainComplex (ModuleCat.{u} R) ℤ} (hK1 : IsZero (K.X 1))
    (hK2 : IsZero (K.X (-2))) (hL1 : IsZero (L.X 1)) (hL2 : IsZero (L.X (-2)))
    (e : HomotopyEquiv K L) :
    HomotopyEquivalence (ofCochainComplex K) (ofCochainComplex L) where
  hom := ofCochainComplexHom e.hom
  inv := ofCochainComplexHom e.inv
  unit := by
    have h := ofHomotopy hK1 hK2 e.homotopyHomInvId
    rw [ofCochainComplexHom_id, ofCochainComplexHom_comp] at h
    exact h
  counit := by
    have h := ofHomotopy hL1 hL2 e.homotopyInvHomId
    rw [ofCochainComplexHom_id, ofCochainComplexHom_comp] at h
    exact h.symm

/-! ## Inverses of the equivalences induced by quasi-isomorphisms -/

namespace Hom

variable {E F G : LinearTwoTermComplex R}

namespace IsQuasiIsomorphism

/-- The equivalence induced by a quasi-isomorphism has the induced functor as its forward
direction. -/
theorem quotientEquivalence_functor {f : Hom E F} (hf : f.IsQuasiIsomorphism) :
    hf.quotientEquivalence.functor = f.quotientFunctor :=
  rfl

/-- Composites of quasi-isomorphisms induce the composite equivalence, on the nose in the
forward direction. -/
theorem quotientEquivalence_comp_functor {f : Hom E F} {g : Hom F G}
    (hf : f.IsQuasiIsomorphism) (hg : g.IsQuasiIsomorphism) :
    (hg.comp hf).quotientEquivalence.functor =
      (hf.quotientEquivalence.trans hg.quotientEquivalence).functor :=
  rfl

/-- The inverse equivalences of a composite of quasi-isomorphisms and of the composite of the
equivalences agree up to a canonical natural isomorphism. -/
noncomputable def quotientEquivalenceCompInverseIso {f : Hom E F} {g : Hom F G}
    (hf : f.IsQuasiIsomorphism) (hg : g.IsQuasiIsomorphism) :
    (hg.comp hf).quotientEquivalence.inverse ≅
      (hf.quotientEquivalence.trans hg.quotientEquivalence).inverse :=
  equivalenceInverseIso _ _ (quotientEquivalence_comp_functor hf hg)

end IsQuasiIsomorphism

end Hom

namespace HomotopyEquivalence

variable {E F : LinearTwoTermComplex R}

/-- The equivalence coming from a chain-homotopy equivalence and the equivalence coming from the
underlying quasi-isomorphism have the same forward functor. -/
theorem quasiIso_quotientEquivalence_functor (e : HomotopyEquivalence E F) :
    e.isQuasiIsomorphism.quotientEquivalence.functor = e.quotientEquivalence.functor :=
  rfl

/-- The inverse of the equivalence produced by a chain-homotopy equivalence, viewed as a
quasi-isomorphism, is canonically isomorphic to the functor induced by the chain-level inverse.
This is the compatibility of the abstract inverse with explicitly constructed inverses. -/
noncomputable def quasiIsoInverseIso (e : HomotopyEquivalence E F) :
    e.isQuasiIsomorphism.quotientEquivalence.inverse ≅ e.inv.quotientFunctor :=
  equivalenceInverseIso _ e.quotientEquivalence (quasiIso_quotientEquivalence_functor e)

end HomotopyEquivalence

namespace AcyclicSummand

variable (E : LinearTwoTermComplex R) (K : Type u) [AddCommGroup K] [Module R K]

/-- The equivalence attached to the acyclic summand `[K ≃ K]` is induced by the inclusion. -/
theorem quotientEquivalence_functor :
    (quotientEquivalence E K).functor = (inclusion E K).quotientFunctor :=
  rfl

/-- The inverse of the equivalence produced by the quasi-isomorphism `E ⟶ E ⊕ [K ≃ K]` is
canonically isomorphic to the projection away from the acyclic summand. -/
noncomputable def inverseIsoProjection :
    (inclusion_isQuasiIsomorphism E K).quotientEquivalence.inverse ≅
      (projection E K).quotientFunctor :=
  (homotopyEquivalence E K).quasiIsoInverseIso

/-- The projection functor strictly retracts the inclusion functor: the acyclic summand is
split off on the nose, not merely up to a homotopy. -/
theorem inclusion_quotientFunctor_comp_projection :
    (inclusion E K).quotientFunctor ⋙ (projection E K).quotientFunctor = 𝟭 E.quotient :=
  rfl

/-- On objects, the projection functor forgets the acyclic coordinate. -/
theorem projection_quotientFunctor_obj_back (x : (add E K).quotient) :
    ((projection E K).quotientFunctor.obj x).back = x.back.1 :=
  rfl

end AcyclicSummand

end LinearTwoTermComplex

/-! ## `h¹/h⁰` of a derived object with a global two-term resolution -/

namespace CotangentComplex.PerfectComplex

open CotangentComplex.PerfectComplex

attribute [local instance] HasDerivedCategory.standard

namespace GlobalTwoTermResolution

variable {E E' : DerivedCategory (ModuleCat.{u} R)}

/-- The two-term complex of modules underlying a global two-term resolution. -/
abbrev linearComplex (F : GlobalTwoTermResolution E) : LinearTwoTermComplex R :=
  LinearTwoTermComplex.ofCochainComplex F.complex

/-- The Picard groupoid `h¹/h⁰(E)` computed from the chosen global two-term resolution `F`. -/
abbrev picard (F : GlobalTwoTermResolution E) := F.linearComplex.quotient

/-- Automorphisms of the vertex of `h¹/h⁰(E)` are exactly `h⁰` of the resolving complex. -/
def vertexAutEquiv (F : GlobalTwoTermResolution E) :
    (TwoTermQuotient.vertex F.linearComplex.differential ⟶
        TwoTermQuotient.vertex F.linearComplex.differential) ≃
      LinearMap.ker (F.complex.d (-1) 0).hom :=
  TwoTermQuotient.vertexAutEquivKernel _

/-- Two objects of `h¹/h⁰(E)` are isomorphic exactly when they differ by an element of the
image of the differential, so isomorphism classes are `h¹` of the resolving complex. -/
theorem nonempty_iso_iff (F : GlobalTwoTermResolution E) (x y : F.picard) :
    Nonempty (x ≅ y) ↔ y.back - x.back ∈ LinearMap.range (F.complex.d (-1) 0).hom :=
  TwoTermQuotient.nonempty_iso_iff _ x y

/-- A chain-level comparison of two global two-term resolutions of the same derived object: an
actual map of cochain complexes which is a quasi-isomorphism in degrees `-1` and `0` and which
realizes the derived comparison isomorphism.  All three components are honest data or honest
hypotheses about that data; nothing asserts a conclusion. -/
structure Comparison (F F' : GlobalTwoTermResolution E) where
  /-- The comparison chain map between the two resolving complexes. -/
  map : F.complex ⟶ F'.complex
  /-- It induces bijections on the kernel and on the cokernel of the differential. -/
  isQuasiIso : (LinearTwoTermComplex.ofCochainComplexHom map).IsQuasiIsomorphism
  /-- Its image in the derived category is the comparison isomorphism of the two resolutions. -/
  realizes : DerivedCategory.Q.map map = (F.iso ≪≫ F'.iso.symm).hom

namespace Comparison

variable {F F' F'' : GlobalTwoTermResolution E}

/-- Every resolution is compared with itself by the identity chain map. -/
def refl (F : GlobalTwoTermResolution E) : Comparison F F where
  map := 𝟙 F.complex
  isQuasiIso := by
    rw [LinearTwoTermComplex.ofCochainComplexHom_id]
    exact LinearTwoTermComplex.Hom.IsQuasiIsomorphism.id _
  realizes := by simp

/-- Comparisons compose. -/
def trans (c : Comparison F F') (c' : Comparison F' F'') : Comparison F F'' where
  map := c.map ≫ c'.map
  isQuasiIso := by
    rw [LinearTwoTermComplex.ofCochainComplexHom_comp]
    exact c'.isQuasiIso.comp c.isQuasiIso
  realizes := by
    rw [Functor.map_comp, c.realizes, c'.realizes]
    simp

/-- A comparison transports along an isomorphism of the resolved derived object. -/
def replace (c : Comparison F F') (e : E ≅ E') :
    Comparison (F.replace e) (F'.replace e) where
  map := c.map
  isQuasiIso := c.isQuasiIso
  realizes := by
    change DerivedCategory.Q.map c.map = ((F.iso ≪≫ e) ≪≫ (F'.iso ≪≫ e).symm).hom
    rw [c.realizes]
    simp

/-- The equivalence of Picard groupoids induced by a chain-level comparison of resolutions.
This is resolution independence of `h¹/h⁰`. -/
noncomputable def picardEquivalence (c : Comparison F F') : F.picard ≌ F'.picard :=
  c.isQuasiIso.quotientEquivalence

/-- The equivalence is induced by the comparison chain map. -/
theorem picardEquivalence_functor (c : Comparison F F') :
    c.picardEquivalence.functor =
      (LinearTwoTermComplex.ofCochainComplexHom c.map).quotientFunctor :=
  rfl

/-- Composition of comparisons induces the composite equivalence, on the nose in the forward
direction. -/
theorem trans_picardEquivalence_functor (c : Comparison F F') (c' : Comparison F' F'') :
    (c.trans c').picardEquivalence.functor =
      (c.picardEquivalence.trans c'.picardEquivalence).functor :=
  rfl

/-- The inverse equivalences attached to a composite comparison and to the composite of the two
equivalences agree up to a canonical natural isomorphism. -/
noncomputable def transPicardEquivalenceInverseIso (c : Comparison F F')
    (c' : Comparison F' F'') :
    (c.trans c').picardEquivalence.inverse ≅
      (c.picardEquivalence.trans c'.picardEquivalence).inverse :=
  equivalenceInverseIso _ _ (trans_picardEquivalence_functor c c')

end Comparison

/-- Two global two-term resolutions of the same derived object are *chain comparable* when their
derived comparison isomorphism is realized by an actual quasi-isomorphism of complexes.  This
always holds (`hasChainComparison`); it is kept as a named predicate because the results below
only use this much, and because the analogous statement over a base other than a ring will have
to be assumed until a sheaf-level lifting lemma is available. -/
def HasChainComparison (F F' : GlobalTwoTermResolution E) : Prop :=
  Nonempty (Comparison F F')

/-- Every resolution is chain comparable with itself. -/
theorem hasChainComparison_refl (F : GlobalTwoTermResolution E) : HasChainComparison F F :=
  ⟨Comparison.refl F⟩

/-- Chain comparability is transitive. -/
theorem HasChainComparison.trans {F F' F'' : GlobalTwoTermResolution E}
    (h : HasChainComparison F F') (h' : HasChainComparison F' F'') :
    HasChainComparison F F'' :=
  ⟨h.some.trans h'.some⟩

/-- **Resolution independence.**  Two global two-term resolutions of the same derived object
whose comparison isomorphism is realized by a quasi-isomorphism of complexes have equivalent
Picard groupoids `h¹/h⁰`. -/
theorem nonempty_picardEquivalence_of_hasChainComparison {F F' : GlobalTwoTermResolution E}
    (h : HasChainComparison F F') : Nonempty (F.picard ≌ F'.picard) :=
  ⟨h.some.picardEquivalence⟩

/-! ### The chain-level comparison always exists -/

/-- Every term of a resolving complex is a projective object: it is free by assumption. -/
theorem projective_complex_X (F : GlobalTwoTermResolution E) (n : ℤ) :
    CategoryTheory.Projective (F.complex.X n) :=
  have := (F.finiteFree n).free
  ModuleCat.projective_of_free (Module.Free.chooseBasis R (F.complex.X n))

/-- The resolving complex of a global two-term resolution is K-projective: it is a bounded above
complex of projective modules. -/
theorem isKProjective (F : GlobalTwoTermResolution E) : F.complex.IsKProjective := by
  have hle : F.complex.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact F.supported i (Or.inr hi)
  have hproj : ∀ n : ℤ, CategoryTheory.Projective (F.complex.X n) := F.projective_complex_X
  exact CochainComplex.isKProjective_of_projective _ 0

/-- **The derived comparison isomorphism is realized by a chain map.**  Since the resolving
complexes are K-projective, morphisms out of them in the derived category are exactly homotopy
classes of chain maps, so the isomorphism `Q(F.complex) ≅ Q(F'.complex)` coming from the two
resolutions of `E` is the image of an actual morphism of cochain complexes. -/
theorem exists_chain_realization (F F' : GlobalTwoTermResolution E) :
    ∃ φ : F.complex ⟶ F'.complex,
      DerivedCategory.Q.map φ = (F.iso ≪≫ F'.iso.symm).hom := by
  have hK := F.isKProjective
  obtain ⟨γ, hγ⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective F.complex
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
        F'.complex)).surjective
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app F.complex ≫
        (F.iso ≪≫ F'.iso.symm).hom ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app F'.complex)
  obtain ⟨φ, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_surjective γ
  refine ⟨φ, ?_⟩
  have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality φ
  rw [Functor.comp_map, hγ] at hnat
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hnat
  exact ((cancel_epi _).mp hnat).symm

/-- The realizing chain map of `exists_chain_realization` is a quasi-isomorphism, hence, both
complexes being K-projective, an honest homotopy equivalence of cochain complexes. -/
theorem exists_homotopyEquiv (F F' : GlobalTwoTermResolution E) :
    ∃ e : HomotopyEquiv F.complex F'.complex,
      DerivedCategory.Q.map e.hom = (F.iso ≪≫ F'.iso.symm).hom := by
  obtain ⟨φ, hφ⟩ := exists_chain_realization F F'
  have hK := F.isKProjective
  have hK' := F'.isKProjective
  have hiso : IsIso (DerivedCategory.Q.map φ) := by
    rw [hφ]
    infer_instance
  have hq : QuasiIso φ := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hiso
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff φ).mp hq
  refine ⟨e, ?_⟩
  rw [he]
  exact hφ

/-- **Any two global two-term resolutions of the same derived object are chain comparable.**
Nothing is assumed: the comparison chain map is produced by K-projectivity and it is a
quasi-isomorphism because it is the restriction of a homotopy equivalence. -/
theorem hasChainComparison (F F' : GlobalTwoTermResolution E) : HasChainComparison F F' := by
  obtain ⟨e, he⟩ := exists_homotopyEquiv F F'
  refine ⟨{ map := e.hom, realizes := he, isQuasiIso := ?_ }⟩
  exact (LinearTwoTermComplex.ofHomotopyEquiv (F.supported 1 (Or.inr (by norm_num)))
    (F.supported (-2) (Or.inl (by norm_num))) (F'.supported 1 (Or.inr (by norm_num)))
    (F'.supported (-2) (Or.inl (by norm_num))) e).isQuasiIsomorphism

/-- **Resolution independence of `h¹/h⁰`.**  The Picard groupoids computed from any two global
two-term resolutions of the same derived object are equivalent, with no hypothesis beyond the
two resolutions themselves. -/
theorem nonempty_picardEquivalence (F F' : GlobalTwoTermResolution E) :
    Nonempty (F.picard ≌ F'.picard) :=
  nonempty_picardEquivalence_of_hasChainComparison (hasChainComparison F F')

/-- Transporting a resolution along an isomorphism of the resolved object does not change the
two-term complex, hence does not change `h¹/h⁰` at all. -/
theorem replace_linearComplex (F : GlobalTwoTermResolution E) (e : E ≅ E') :
    (F.replace e).linearComplex = F.linearComplex :=
  rfl

end GlobalTwoTermResolution

end CotangentComplex.PerfectComplex

end GromovWitten.AlgebraicGeometry
