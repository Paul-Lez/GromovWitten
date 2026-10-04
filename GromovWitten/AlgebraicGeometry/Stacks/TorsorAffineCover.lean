/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Cones.QuotientTorsor
import GromovWitten.AlgebraicGeometry.Descent.AffineRepresentability
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# A torsor over an affine base is trivialised by a faithfully flat affine cover

Group algebraic spaces represented by an affine scheme (`affineGroup`), and the trivialisation of
an `FppfTorsor` over an affine base, by a faithfully flat finitely presented affine cover with a
section (`TorsorAffineTrivialisation`), into an `AffineDescentInput`
(`Descent/AffineRepresentability.lean`).  Every torsor over an affine base has such a cover:
this is proved in `Stacks/TorsorAffineRefinement.lean`
(`FppfTorsor.nonempty_torsorAffineTrivialisation`), independently of the present file, using
`AlgebraicGeometry.UniversallyOpen.of_flat`; so nothing below is conditional.

## Universe convention for "`ℤ`"

The blueprint's base ring `ℤ` cannot literally appear in `Scheme.{u}`-valued constructions for a
general universe `u` (`Spec` needs its argument in `CommRingCat.{u}`, and `ℤ : Type 0`). Exactly
as in the repository's own `ProjectiveLineRing.lean`, `PolynomialRelativeProj.lean` and
`Cones/QuotientTorsor.lean`, we realise "`ℤ`" as `TorsorZu := ULift.{u} ℤ`, canonically isomorphic
to `ℤ` as a ring; this changes nothing mathematically, only the universe at which the integers
are modelled.

## Main results

* `affineGroup R grp` : the group algebraic space represented by `Spec R`, for a chosen group
  object structure `grp` on the fppf sheaf `fppfYoneda.obj (Spec R)`.
* `affineGroup_space_toSheaf` : the defining `rfl`-identification
  `(affineGroup R grp).space.toSheaf = fppfYoneda.obj (Spec (.of R))`.
* `TorsorAffineTrivialisation` : for any `G : AlgebraicSpaceGroup` and torsor `P` over an affine
  base, the data of an affine, faithfully flat, finitely presented cover `B` of the base together
  with a section of `P` over it.
* `TorsorAffineTrivialisation.descentInput` (for `G = affineGroup R grp`) : the
  `AffineDescentInput` obtained from a `TorsorAffineTrivialisation` by trivialising the torsor's
  base change to `Spec D.B` using
  `fppfYoneda.obj (Spec R) ⊗ fppfYoneda.obj (Spec D.B) ≅ fppfYoneda.obj (Spec (D.B ⊗[TorsorZu] R))`
  (the left-hand side being, up to the `rfl` of `affineGroup_space_toSheaf`, the trivialisation of
  the base-changed torsor), with `M := D.B ⊗[TorsorZu] R` a `D.B`-algebra via the left tensor
  factor.
* `TorsorAffineTrivialisation.etale_descentInput`, `.finite_descentInput`,
  `.surjective_descentInput` : if `R` is étale (resp. a finite module, resp. gives a surjective
  `Spec R ⟶ Spec TorsorZu`) over `TorsorZu`, then `D.descentInput.M` is étale over `D.B`
  (resp. a finite `D.B`-module, resp. `Spec D.descentInput.M ⟶ Spec D.B` is surjective).
* `torsorZuAlgebra_eq`, `etale_torsorZu_of_etale`, `finite_torsorZu_of_finite` : bridge lemmas
  back to the ordinary hypotheses `[Algebra.Etale ℤ R]`/`[Module.Finite ℤ R]`, and
  `TorsorAffineTrivialisation.etale_descentInput_of_int`, `.finite_descentInput_of_int` : the
  corresponding corollaries of `etale_descentInput`/`finite_descentInput` taking those ordinary
  hypotheses directly.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory TensorProduct
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

/-- `ℤ` lifted to the working universe `u`, the repository's standard representative of the
integers at universe `u` (matching `ProjectiveLineRing.lean`'s `Zu`,
`Cones/QuotientTorsor.lean`'s `intPoly`, and Mathlib's `AlgebraicGeometry.AffineSpace`), used
because `Spec` and `CommRingCat.of` require their argument in `Type u`.

This is literally `GromovWitten.AlgebraicGeometry.P1.Zu` of `ProjectiveLineRing.lean` under a
different name; the two should be unified into one shared declaration in a later round. -/
abbrev TorsorZu : Type u := ULift.{u} ℤ

/-- Every commutative ring is canonically a `TorsorZu`-algebra, through the ring isomorphism
`TorsorZu ≃+* ℤ` and the unique ring homomorphism `ℤ ⟶ R`. Not registered as a global instance
(matching Mathlib's `ULift.algebra'`, which is deliberately not an instance to avoid a diamond
when `R` is itself built out of `ULift`); supplied explicitly wherever needed. -/
noncomputable abbrev torsorZuAlgebra (R : Type u) [CommRing R] : Algebra TorsorZu R :=
  ULift.algebra' ℤ R

section TorsorZuBridge

/-!
### Bridging `TorsorZu` back to `ℤ`

`torsorZuAlgebra R` is the *only* `TorsorZu`-algebra structure on `R`, so every fact about an
arbitrary such structure reduces to a fact about `torsorZuAlgebra R`; and a `ℤ`-algebra property
of `R` transports to the corresponding `TorsorZu`-algebra property through the ring isomorphism
`TorsorZu ≃+* ℤ` and the scalar tower `TorsorZu ⟶ ℤ ⟶ R`. These lemmas connect the `TorsorZu`
hypotheses used below back to the ordinary hypotheses `[Algebra.Etale ℤ R]`/`[Module.Finite ℤ R]`
that a concrete `R` (e.g. a finite group ring) actually satisfies.
-/

variable {R : Type u} [CommRing R]

/-- Ring homomorphisms out of `TorsorZu ≃ ℤ` are unique, so `torsorZuAlgebra R` is the *only*
`TorsorZu`-algebra structure on `R`. -/
theorem torsorZuAlgebra_eq (inst : Algebra TorsorZu.{u} R) : inst = torsorZuAlgebra R := by
  have e : TorsorZu.{u} ≃+* ℤ := ULift.ringEquiv
  have key : (@algebraMap TorsorZu.{u} R _ _ inst).comp e.symm.toRingHom =
      (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)).comp e.symm.toRingHom :=
    RingHom.ext_int _ _
  refine Algebra.algebra_ext inst (torsorZuAlgebra R) (fun z => ?_)
  have hz : z = e.symm (e z) := (e.symm_apply_apply z).symm
  calc (@algebraMap TorsorZu.{u} R _ _ inst) z
      = (@algebraMap TorsorZu.{u} R _ _ inst) (e.symm (e z)) := by rw [← hz]
    _ = (@algebraMap TorsorZu.{u} R _ _ inst).comp e.symm.toRingHom (e z) := rfl
    _ = (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)).comp e.symm.toRingHom (e z) := by
        rw [key]
    _ = (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)) (e.symm (e z)) := rfl
    _ = (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)) z := by rw [← hz]

/-- `ℤ`, as a `TorsorZu`-algebra through the ring isomorphism `TorsorZu ≃+* ℤ`. -/
noncomputable abbrev torsorZuAlgebraInt : Algebra TorsorZu.{u} ℤ :=
  (ULift.ringEquiv : TorsorZu.{u} ≃+* ℤ).toRingHom.toAlgebra

/-- An étale `ℤ`-algebra `R` is an étale `TorsorZu`-algebra (for `torsorZuAlgebra R`): compose
the isomorphism `TorsorZu ≃+* ℤ` (étale, since bijective) with the étale map `ℤ ⟶ R`, using that
`Etale` is stable under composition along the scalar tower `TorsorZu ⟶ ℤ ⟶ R`. -/
theorem etale_torsorZu_of_etale [Algebra.Etale ℤ R] :
    @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R) := by
  let algI : Algebra TorsorZu.{u} ℤ := torsorZuAlgebraInt
  let algR : Algebra TorsorZu.{u} R := torsorZuAlgebra R
  have hiso : Algebra.Etale TorsorZu.{u} ℤ := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.of_bijective (ULift.ringEquiv : TorsorZu.{u} ≃+* ℤ).bijective
  have htower : @IsScalarTower TorsorZu.{u} ℤ R algI.toSMul _ algR.toSMul :=
    @IsScalarTower.of_algebraMap_eq' TorsorZu.{u} ℤ R _ _ _ algI _ algR rfl
  exact Algebra.Etale.comp TorsorZu.{u} ℤ R

/-- A finite `ℤ`-module `R` is a finite `TorsorZu`-module (for `torsorZuAlgebra R`): `ℤ` is a
finite `TorsorZu`-module (the isomorphism `TorsorZu ≃+* ℤ` is in particular surjective), and
finiteness is transitive along the scalar tower `TorsorZu ⟶ ℤ ⟶ R`. -/
theorem finite_torsorZu_of_finite [Module.Finite ℤ R] :
    Module.Finite TorsorZu.{u} R := by
  let algI : Algebra TorsorZu.{u} ℤ := torsorZuAlgebraInt
  let algR : Algebra TorsorZu.{u} R := torsorZuAlgebra R
  have hfin : Module.Finite TorsorZu.{u} ℤ :=
    Module.Finite.of_surjective (Algebra.linearMap TorsorZu.{u} ℤ)
      (ULift.ringEquiv : TorsorZu.{u} ≃+* ℤ).surjective
  have htower : @IsScalarTower TorsorZu.{u} ℤ R algI.toSMul _ algR.toSMul :=
    @IsScalarTower.of_algebraMap_eq' TorsorZu.{u} ℤ R _ _ _ algI _ algR rfl
  exact Module.Finite.trans ℤ R

end TorsorZuBridge

section AffineGroup

variable (R : Type u) [CommRing R]

/-- The group algebraic space represented by `Spec R`, for a chosen group object structure `grp`
on the fppf sheaf of points of `Spec R`. -/
noncomputable def affineGroup (grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))) :
    AlgebraicSpaceGroup.{u} where
  space := AlgebraicSpace.ofScheme.obj (Spec (CommRingCat.of R))
  group := grp

/-- The underlying sheaf of `affineGroup R grp` is, definitionally, the fppf sheaf of points of
`Spec R`. -/
@[simp]
theorem affineGroup_space_toSheaf (grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))) :
    (affineGroup R grp).space.toSheaf = fppfYoneda.obj (Spec (CommRingCat.of R)) :=
  rfl

end AffineGroup

section CartesianHelpers

/-!
### Categorical helpers

The trivialisation of a torsor over an affine cover identifies a monoidal tensor product of
representable fppf sheaves with the representable sheaf of a product of affine schemes, and
then that product of affine schemes with the `Spec` of a tensor product of rings. These lemmas
record the two comparison steps and their compatibility with the second projection /
`CartesianMonoidalCategory.snd`, generically enough to apply to `FppfSheaf.{u}` and to
`Scheme.{u}`.
-/

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

/-- In a cartesian monoidal category, the monoidal tensor product of two objects is canonically
isomorphic to their categorical binary product `Limits.prod`. -/
noncomputable def tensorIsoProd (X Y : C) : X ⊗ Y ≅ X ⨯ Y :=
  (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
    (limit.isLimit _)

@[simp]
theorem tensorIsoProd_hom_snd (X Y : C) :
    (tensorIsoProd X Y).hom ≫ Limits.prod.snd = CartesianMonoidalCategory.snd X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ (limit.isLimit _) (Discrete.mk WalkingPair.right)

end CartesianHelpers

section Trivialisation

variable {G : AlgebraicSpaceGroup.{u}} {A : Type u} [CommRing A]

/-- The data produced by Step 1 of blueprint section B2: an affine, faithfully flat, finitely
presented cover `Spec B ⟶ Spec A` of the base of a torsor `P` under a group algebraic space `G`,
together with a section of `P` over it. See the module docstring for why this is recorded as
data (a hypothesis-carrying structure) rather than constructed from an arbitrary fppf-local
section: the construction is a separate (and non-trivial) piece of Mathlib engineering, carried
out independently of this file in `Stacks/TorsorAffineRefinement.lean`
(`FppfTorsor.nonempty_torsorAffineTrivialisation`). None of the fields below mention `G`'s
presentation, so the structure is stated for an arbitrary `G`; `descentInput` below specialises
to `G = affineGroup R grp`, where `R` is used. -/
structure TorsorAffineTrivialisation (P : FppfTorsor G (Spec (CommRingCat.of A))) where
  /-- The coordinate ring of the affine cover. -/
  B : Type u
  [commRing : CommRing B]
  [algebra : Algebra A B]
  [faithfullyFlat : Module.FaithfullyFlat A B]
  [finitePresentation : Algebra.FinitePresentation A B]
  /-- The section of the torsor over the cover. -/
  s : fppfYoneda.obj (Spec (CommRingCat.of B)) ⟶ P.P
  /-- The section lies over `Spec B ⟶ Spec A`. -/
  s_over : s ≫ P.projection =
      fppfYoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))

namespace TorsorAffineTrivialisation

attribute [instance] commRing algebra faithfullyFlat finitePresentation

variable {P : FppfTorsor G (Spec (CommRingCat.of A))}
  (D : TorsorAffineTrivialisation P)

/-- The scheme map underlying the cover. -/
noncomputable abbrev cover : Spec (CommRingCat.of D.B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A D.B))

/-- The base change of `P` to the cover `Spec B`. -/
noncomputable abbrev pullbackTorsor : FppfTorsor G (Spec (CommRingCat.of D.B)) :=
  FppfTorsor.pullbackTorsor P D.cover

/-- The section `D.s`, viewed as a genuine global section of the base-changed torsor
`D.pullbackTorsor`. -/
noncomputable def pullbackSection :
    fppfYoneda.obj (Spec (CommRingCat.of D.B)) ⟶ D.pullbackTorsor.P :=
  Limits.pullback.lift D.s (𝟙 _) (by rw [D.s_over, Category.id_comp])

@[simp]
theorem pullbackSection_projection :
    D.pullbackSection ≫ D.pullbackTorsor.projection = 𝟙 _ :=
  Limits.pullback.lift_snd _ _ _

end TorsorAffineTrivialisation

end Trivialisation

section AffineTrivialisation

variable {R : Type u} [CommRing R] {grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))}
  {A : Type u} [CommRing A]

namespace TorsorAffineTrivialisation

variable {P : FppfTorsor (affineGroup R grp) (Spec (CommRingCat.of A))}
  (D : TorsorAffineTrivialisation P)

/-- Step 2 of blueprint section B2. Trivialising the torsor's base change to `Spec D.B` using
the section `D.pullbackSection` identifies it with
`fppfYoneda.obj (Spec R) ⊗ fppfYoneda.obj (Spec D.B)` (`ConeQuotient.sectionIso`, applied through
the `rfl`-identification `(affineGroup R grp).space.toSheaf = fppfYoneda.obj (Spec R)`); since
`fppfYoneda` preserves binary products, this tensor product is identified with the fppf-Yoneda
sheaf of `Spec R ⨯ Spec D.B`, and finally (realising `Spec TorsorZu` as a terminal object of
`Scheme.{u}`) with the fppf-Yoneda sheaf of `Spec (D.B ⊗[TorsorZu] R)`. The resulting
`AffineDescentInput` has `M := D.B ⊗[TorsorZu] R`, a `D.B`-algebra via the left tensor factor. -/
noncomputable def descentInput : AffineDescentInput A D.B P.P P.projection :=
  letI algR : Algebra TorsorZu R := torsorZuAlgebra R
  letI algB : Algebra TorsorZu D.B := torsorZuAlgebra D.B
  -- The trivialisation of the base-changed torsor over `Spec D.B`; `(affineGroup R grp).space.
  -- toSheaf` is definitionally `fppfYoneda.obj (Spec R)` (`affineGroup_space_toSheaf`).
  let θ₀ : fppfYoneda.obj (Spec (CommRingCat.of R)) ⊗ fppfYoneda.obj (Spec (CommRingCat.of D.B)) ≅
      D.pullbackTorsor.P :=
    ConeQuotient.sectionIso (ActionTorsor.ofFppfTorsor D.pullbackTorsor)
      D.pullbackSection D.pullbackSection_projection
  let e2 := tensorIsoProd (fppfYoneda.obj (Spec (CommRingCat.of R)))
    (fppfYoneda.obj (Spec (CommRingCat.of D.B)))
  let e3 := (PreservesLimitPair.iso fppfYoneda (Spec (CommRingCat.of R))
    (Spec (CommRingCat.of D.B))).symm
  let e3b := fppfYoneda.mapIso
    (Limits.prod.braiding (Spec (CommRingCat.of R)) (Spec (CommRingCat.of D.B)))
  let f := Spec.map (CommRingCat.ofHom (algebraMap TorsorZu D.B))
  let g := Spec.map (CommRingCat.ofHom (algebraMap TorsorZu R))
  have hprod : IsLimit (BinaryFan.mk (pullback.fst f g) (pullback.snd f g)) :=
    isProductOfIsTerminalIsPullback f g (pullback.fst f g) (pullback.snd f g)
      specULiftZIsTerminal (pullbackIsPullback f g)
  let e4sch : Spec (CommRingCat.of D.B) ⨯ Spec (CommRingCat.of R) ≅
      Spec (CommRingCat.of (D.B ⊗[TorsorZu] R)) :=
    (IsLimit.conePointUniqueUpToIso (limit.isLimit (pair (Spec (CommRingCat.of D.B))
      (Spec (CommRingCat.of R)))) hprod) ≪≫ pullbackSpecIso TorsorZu D.B R
  let e4 := fppfYoneda.mapIso e4sch
  let θ := θ₀.symm ≪≫ e2 ≪≫ e3 ≪≫ e3b ≪≫ e4
  have hsnd0 : θ₀.hom ≫ D.pullbackTorsor.projection =
      CartesianMonoidalCategory.snd (fppfYoneda.obj (Spec (CommRingCat.of R)))
        (fppfYoneda.obj (Spec (CommRingCat.of D.B))) :=
    ConeQuotient.sectionMap_projection (ActionTorsor.ofFppfTorsor D.pullbackTorsor)
      D.pullbackSection D.pullbackSection_projection
  have he2 : e2.hom ≫ Limits.prod.snd = CartesianMonoidalCategory.snd
      (fppfYoneda.obj (Spec (CommRingCat.of R))) (fppfYoneda.obj (Spec (CommRingCat.of D.B))) :=
    tensorIsoProd_hom_snd _ _
  have hprodSnd : (PreservesLimitPair.iso fppfYoneda (Spec (CommRingCat.of R))
      (Spec (CommRingCat.of D.B))).hom ≫ Limits.prod.snd =
      fppfYoneda.map Limits.prod.snd := by
    rw [PreservesLimitPair.iso_hom]; exact prodComparison_snd _ _ _
  have he3 : e3.hom ≫ fppfYoneda.map Limits.prod.snd = Limits.prod.snd := by
    change (PreservesLimitPair.iso fppfYoneda (Spec (CommRingCat.of R))
      (Spec (CommRingCat.of D.B))).inv ≫ fppfYoneda.map Limits.prod.snd = Limits.prod.snd
    rw [← hprodSnd, Iso.inv_hom_id_assoc]
  have hbraid : (Limits.prod.braiding (Spec (CommRingCat.of R))
      (Spec (CommRingCat.of D.B))).hom ≫ Limits.prod.fst = Limits.prod.snd := by
    simp [Limits.prod.braiding, Limits.prod.lift_fst]
  have he3b : e3b.hom ≫ fppfYoneda.map Limits.prod.fst = fppfYoneda.map Limits.prod.snd := by
    change fppfYoneda.map (Limits.prod.braiding (Spec (CommRingCat.of R))
      (Spec (CommRingCat.of D.B))).hom ≫ fppfYoneda.map Limits.prod.fst = _
    rw [← fppfYoneda.map_comp, hbraid]
  have he4sch : e4sch.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap D.B (D.B ⊗[TorsorZu] R))) = Limits.prod.fst := by
    change (IsLimit.conePointUniqueUpToIso (limit.isLimit (pair (Spec (CommRingCat.of D.B))
      (Spec (CommRingCat.of R)))) hprod ≪≫ pullbackSpecIso TorsorZu D.B R).hom ≫ _ = _
    rw [Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst]
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ hprod (Discrete.mk WalkingPair.left)
  have he4 : e4.hom ≫
      fppfYoneda.map (Spec.map (CommRingCat.ofHom (algebraMap D.B (D.B ⊗[TorsorZu] R)))) =
      fppfYoneda.map Limits.prod.fst := by
    change fppfYoneda.map e4sch.hom ≫
      fppfYoneda.map (Spec.map (CommRingCat.ofHom (algebraMap D.B (D.B ⊗[TorsorZu] R)))) = _
    rw [← fppfYoneda.map_comp, he4sch]
  let algM : Algebra A (D.B ⊗[TorsorZu] R) :=
    ((algebraMap D.B (D.B ⊗[TorsorZu] R)).comp (algebraMap A D.B)).toAlgebra
  { M := D.B ⊗[TorsorZu] R
    algebraBase := algM
    isScalarTower :=
      @IsScalarTower.of_algebraMap_eq' A D.B (D.B ⊗[TorsorZu] R) _ _ _ _ _ algM rfl
    θ := θ
    θ_over := by
      change θ.hom ≫
        fppfYoneda.map (Spec.map (CommRingCat.ofHom (algebraMap D.B (D.B ⊗[TorsorZu] R)))) =
        Limits.pullback.snd _ _
      have hchain : θ.hom ≫
          fppfYoneda.map (Spec.map (CommRingCat.ofHom (algebraMap D.B (D.B ⊗[TorsorZu] R)))) =
          θ₀.inv ≫ CartesianMonoidalCategory.snd (fppfYoneda.obj (Spec (CommRingCat.of R)))
            (fppfYoneda.obj (Spec (CommRingCat.of D.B))) := by
        change (θ₀.symm ≪≫ e2 ≪≫ e3 ≪≫ e3b ≪≫ e4).hom ≫ _ = _
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
        rw [he4, he3b, he3, he2]
      have hfinal : θ₀.inv ≫
          CartesianMonoidalCategory.snd (fppfYoneda.obj (Spec (CommRingCat.of R)))
            (fppfYoneda.obj (Spec (CommRingCat.of D.B))) = D.pullbackTorsor.projection := by
        rw [← hsnd0, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      rw [hchain, hfinal] }

/-- If `R` is étale over `TorsorZu` (= `ℤ`), the coordinate ring `M` of `D.descentInput` is
étale over the cover `D.B`, by base change of étale algebras (`Algebra.Etale.baseChange`)
along `D.B ⊗[TorsorZu] R`. -/
theorem etale_descentInput (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R)) :
    Algebra.Etale D.B D.descentInput.M := by
  let _ : Algebra TorsorZu.{u} R := torsorZuAlgebra R
  let _ : Algebra TorsorZu.{u} D.B := torsorZuAlgebra D.B
  change Algebra.Etale D.B (D.B ⊗[TorsorZu.{u}] R)
  exact @Algebra.Etale.baseChange TorsorZu.{u} R D.B _ _ (torsorZuAlgebra R) _
    (torsorZuAlgebra D.B) hEtale

/-- If `R` is a finite `TorsorZu`-module, the coordinate ring `M` of `D.descentInput` is a
finite `D.B`-module, by base change of finite modules (`Module.Finite.base_change`). -/
theorem finite_descentInput [Module.Finite TorsorZu.{u} R] :
    Module.Finite D.B D.descentInput.M := by
  let _ : Algebra TorsorZu.{u} R := torsorZuAlgebra R
  let _ : Algebra TorsorZu.{u} D.B := torsorZuAlgebra D.B
  change Module.Finite D.B (D.B ⊗[TorsorZu.{u}] R)
  infer_instance

/-- The ordinary-hypothesis form of `etale_descentInput`: if `R` is étale over `ℤ`, the
coordinate ring `M` of `D.descentInput` is étale over the cover `D.B`. -/
theorem etale_descentInput_of_int [Algebra.Etale ℤ R] :
    Algebra.Etale D.B D.descentInput.M :=
  D.etale_descentInput etale_torsorZu_of_etale

/-- The ordinary-hypothesis form of `finite_descentInput`: if `R` is a finite `ℤ`-module, the
coordinate ring `M` of `D.descentInput` is a finite `D.B`-module. -/
theorem finite_descentInput_of_int [Module.Finite ℤ R] :
    Module.Finite D.B D.descentInput.M :=
  letI := finite_torsorZu_of_finite (R := R)
  D.finite_descentInput

/-- If `Spec R ⟶ Spec TorsorZu` is surjective, then so is
`Spec D.descentInput.M ⟶ Spec D.B`: surjectivity is stable under base change, and
`Spec D.descentInput.M ⟶ Spec D.B` is (via `pullbackSpecIso`) the base change of
`Spec R ⟶ Spec TorsorZu` along `Spec D.B ⟶ Spec TorsorZu`. -/
theorem surjective_descentInput
    (hR : AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R))))) :
    AlgebraicGeometry.Surjective
      (Spec.map (CommRingCat.ofHom (algebraMap D.B D.descentInput.M))) := by
  let _ : Algebra TorsorZu.{u} R := torsorZuAlgebra R
  let _ : Algebra TorsorZu.{u} D.B := torsorZuAlgebra D.B
  change AlgebraicGeometry.Surjective
    (Spec.map (CommRingCat.ofHom (algebraMap D.B (D.B ⊗[TorsorZu.{u}] R))))
  set f := Spec.map (CommRingCat.ofHom (algebraMap TorsorZu.{u} D.B)) with hf
  set g := Spec.map (CommRingCat.ofHom (algebraMap TorsorZu.{u} R)) with hg
  have hsurj : AlgebraicGeometry.Surjective (pullback.fst f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @AlgebraicGeometry.Surjective)
      (IsPullback.of_hasPullback f g).flip hR
  have heq : Spec.map (CommRingCat.ofHom (algebraMap D.B (D.B ⊗[TorsorZu.{u}] R))) =
      (pullbackSpecIso TorsorZu.{u} D.B R).inv ≫ pullback.fst f g := by
    rw [pullbackSpecIso_inv_fst']
  rw [heq]
  infer_instance

end TorsorAffineTrivialisation

end AffineTrivialisation

end GromovWitten.AlgebraicGeometry
