/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeLineBundles
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Proper pushforward and cohomology/base-change data for curves

Mathlib already provides the actual pushforward and pullback functors on sheaves of modules.  This
file constructs the ordinary Beck--Chevalley morphism from the pullback square and the two
pullback--pushforward adjunctions.  The still-missing theorem that this canonical morphism is an
isomorphism is isolated in a typed interface.

The higher direct images are *constructed*, not assumed, on the level of the underlying sheaves of
abelian groups: the category of abelian sheaves on a scheme is a Grothendieck abelian category,
hence has enough injectives, so `Rⁿ f_*` is available as the `n`-th right derived functor of the
pushforward (`higherDirectImageAb`).  We prove the degree-zero identification
`R⁰ f_* = f_*` (`higherDirectImageAbZeroIso`, `higherDirectImageModuleAbZeroIso`), the vanishing
of the higher direct images of an injective sheaf, and the higher vanishing for a morphism whose
pushforward is exact (`isZero_higherDirectImageAb_succ_of_exact`, an instance of the general
statement `isZero_rightDerived_succ_of_preservesHomology`).

What is *not* available in the pinned Mathlib is the `𝒪_S`-module structure on `Rⁿ f_*` for
`n ≥ 1` (this needs enough injectives in the category of `𝒪_X`-modules, which Mathlib does not
provide yet) and the base-change comparison in positive degrees.  Consequently
`CurveCohomologyBaseChangeData` still carries the positive-degree direct images, their
base-change comparisons and their vanishing as fields.  Those fields are however no longer
unconstrained: a positive-degree direct image is a `ModuleStructure` on the constructed derived
functor `Rⁿ⁺¹ f_*`, that is, an `𝒪`-module whose underlying abelian sheaf *is* the honest higher
direct image, so the assumed base-change comparison is a statement about the genuine `Rⁿ f_*`.
Everything in degree zero is now constructed:

* the degree-zero direct image *is* `f_* M`;
* its base change *is* `g_* p^* M`;
* the degree-zero comparison *is* the canonical Beck--Chevalley morphism
  `canonicalPushforwardBaseChangeComparison`;
* the degree-zero base-change assertion *is* `PushforwardBaseChangeData`.

The vanishing of the base-changed direct images in degrees at least two is likewise no longer a
field: it is deduced from the vanishing upstairs and from the base-change comparison, using that
pullback of modules is an additive functor.

The structures are proof-bearing theorem packages, not propositions asserted without witnesses.
They allow the stable-reduction layers to consume a locally constructed duality/cohomology proof
without depending on an external package.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u v₁ u₁ v₂ u₂

noncomputable section

variable {X S : Scheme.{u}}

/-- Ordinary proper pushforward of the underlying module of a line bundle. -/
abbrev LineBundle.pushforwardModule (f : X ⟶ S) (L : LineBundle X) : S.Modules :=
  (Scheme.Modules.pushforward f).obj L.obj

/-- The canonical ordinary-pushforward base-change morphism.  Its adjoint is obtained by
identifying the two iterated pullbacks around the Cartesian square and then applying the
pullback of the counit for `f⁎ ⊣ f_*`. -/
def canonicalPushforwardBaseChangeComparison (f : X ⟶ S) (M : X.Modules)
    {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M) := by
  refine (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ ?_
  exact
    (Scheme.Modules.pullbackComp g b).hom.app _ ≫
      (Scheme.Modules.pullbackCongr h.w.symm).hom.app _ ≫
      (Scheme.Modules.pullbackComp p f).inv.app _ ≫
      (Scheme.Modules.pullback p).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)

/-- Arbitrary-base-change for ordinary pushforward is the assertion that the canonical
Beck--Chevalley morphism is invertible. -/
structure PushforwardBaseChangeData (f : X ⟶ S) (M : X.Modules) : Prop where
  comparison_isIso : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b),
      IsIso (canonicalPushforwardBaseChangeComparison f M b p g h)

namespace PushforwardBaseChangeData

variable {f : X ⟶ S} {M : X.Modules}

/-- The comparison attached to the chosen pullback square. -/
def chosenComparison (_B : PushforwardBaseChangeData f M)
    {T : Scheme.{u}} (b : T ⟶ S) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward (pullback.snd f b)).obj
        ((Scheme.Modules.pullback (pullback.fst f b)).obj M) :=
  canonicalPushforwardBaseChangeComparison f M b (pullback.fst f b) (pullback.snd f b)
    (IsPullback.of_hasPullback f b)

instance chosenComparison_isIso (B : PushforwardBaseChangeData f M)
    {T : Scheme.{u}} (b : T ⟶ S) :
    IsIso (chosenComparison B b) :=
  B.comparison_isIso b (pullback.fst f b) (pullback.snd f b)
    (IsPullback.of_hasPullback f b)

end PushforwardBaseChangeData

/-!
### Higher direct images of abelian sheaves

Abelian sheaves on a scheme form a Grothendieck abelian category, hence have enough injectives,
so the right derived functors of the pushforward exist.  This is the actual construction of the
higher direct images `Rⁿ f_*` on underlying abelian sheaves.
-/

/-- The underlying sheaf of abelian groups of an `𝒪_X`-module, as a functor. -/
def moduleToSheafAb (X : Scheme.{u}) : X.Modules ⥤ TopCat.Sheaf Ab.{u} X where
  obj M := ⟨M.presheaf, M.isSheaf⟩
  map φ := ⟨φ.mapPresheaf⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance moduleToSheafAb_additive (X : Scheme.{u}) : (moduleToSheafAb X).Additive :=
  ⟨by intros; rfl⟩

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

instance pushforwardAb_additive (f : X ⟶ S) :
    (TopCat.Sheaf.pushforward Ab.{u} f.base).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- The `n`-th higher direct image functor on abelian sheaves: the `n`-th right derived functor
of the pushforward.  This is the honest derived-functor definition of `Rⁿ f_*`, available because
abelian sheaves on a scheme form a Grothendieck abelian category. -/
def higherDirectImageAb (f : X ⟶ S) (n : ℕ) :
    TopCat.Sheaf Ab.{u} X ⥤ TopCat.Sheaf Ab.{u} S :=
  (TopCat.Sheaf.pushforward Ab.{u} f.base).rightDerived n

/-- The degree-zero higher direct image is the ordinary pushforward: `R⁰ f_* = f_*`. -/
def higherDirectImageAbZeroIso (f : X ⟶ S) :
    higherDirectImageAb f 0 ≅ TopCat.Sheaf.pushforward Ab.{u} f.base :=
  Functor.rightDerivedZeroIsoSelf _

/-- Higher direct images of an injective abelian sheaf vanish in positive degrees. -/
theorem isZero_higherDirectImageAb_succ_of_injective (f : X ⟶ S) (n : ℕ)
    (F : TopCat.Sheaf Ab.{u} X) [Injective F] :
    IsZero ((higherDirectImageAb f (n + 1)).obj F) :=
  Functor.isZero_rightDerived_obj_injective_succ _ _ _

/-- If an additive functor is exact, in the sense that it preserves homology, then all of its
higher right derived functors vanish.  This is the abstract form of the vanishing of the higher
direct images along a morphism whose pushforward is exact. -/
theorem isZero_rightDerived_succ_of_preservesHomology {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [EnoughInjectives C] {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [F.PreservesHomology] (n : ℕ) (Z : C) : IsZero ((F.rightDerived (n + 1)).obj Z) := by
  let I : InjectiveResolution Z := InjectiveResolution.of Z
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj F (n + 1))
  have hqi : QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) (n + 1) :=
    inferInstance
  rw [quasiIsoAt_iff_isIso_homologyMap] at hqi
  have hzero : IsZero
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((CochainComplex.single₀ C).obj Z)).homology (n + 1)) := by
    refine IsZero.of_iso ?_
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) (n + 1)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app Z))
    exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ (by omega)
  exact hzero.of_iso (asIso (HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) (n + 1))).symm

/-- If the pushforward of abelian sheaves along `f` is exact, then every higher direct image
vanishes in positive degrees. -/
theorem isZero_higherDirectImageAb_succ_of_exact (f : X ⟶ S)
    [(TopCat.Sheaf.pushforward Ab.{u} f.base).PreservesHomology] (n : ℕ)
    (F : TopCat.Sheaf Ab.{u} X) :
    IsZero ((higherDirectImageAb f (n + 1)).obj F) :=
  isZero_rightDerived_succ_of_preservesHomology _ n F

/-- The higher direct images of the underlying abelian sheaf of an `𝒪_X`-module. -/
def higherDirectImageModuleAb (f : X ⟶ S) (M : X.Modules) (n : ℕ) : TopCat.Sheaf Ab.{u} S :=
  (higherDirectImageAb f n).obj ((moduleToSheafAb X).obj M)

/-- The underlying abelian sheaf of the pushforward of a module is the pushforward of the
underlying abelian sheaf. -/
theorem moduleToSheafAb_pushforward (f : X ⟶ S) (M : X.Modules) :
    (moduleToSheafAb S).obj ((Scheme.Modules.pushforward f).obj M) =
      (TopCat.Sheaf.pushforward Ab.{u} f.base).obj ((moduleToSheafAb X).obj M) :=
  rfl

/-- Degree-zero cohomology of a module is genuinely its ordinary pushforward: the derived-functor
`R⁰ f_* M` is the underlying abelian sheaf of `f_* M`. -/
def higherDirectImageModuleAbZeroIso (f : X ⟶ S) (M : X.Modules) :
    higherDirectImageModuleAb f M 0 ≅
      (moduleToSheafAb S).obj ((Scheme.Modules.pushforward f).obj M) :=
  (higherDirectImageAbZeroIso f).app _

/-- Higher direct images of a module whose underlying abelian sheaf is injective vanish in
positive degrees. -/
theorem isZero_higherDirectImageModuleAb_succ_of_injective (f : X ⟶ S) (M : X.Modules) (n : ℕ)
    [Injective ((moduleToSheafAb X).obj M)] :
    IsZero (higherDirectImageModuleAb f M (n + 1)) :=
  isZero_higherDirectImageAb_succ_of_injective f n _

/-!
### Cohomology and base change for a family of curves

Only the positive-degree data are assumed; degree zero is constructed.  Moreover the assumed
positive-degree objects are not arbitrary: they are required to be `𝒪`-module structures on the
actual derived-functor higher direct images, so the base-change comparison below is a statement
about the genuine `Rⁿ f_*` and not about unconstrained placeholders.
-/

/-- An `𝒪_S`-module structure on a sheaf of abelian groups `N`: an `𝒪_S`-module together with an
identification of its underlying abelian sheaf with `N`.

This is what is still missing from Mathlib for the higher direct images: `Rⁿ f_*` is constructed
above as a sheaf of abelian groups (`higherDirectImageAb`), but the category of `𝒪_X`-modules is
not yet known to have enough injectives, so the `𝒪_S`-module structure on `Rⁿ f_*` for `n ≥ 1`
cannot yet be constructed. -/
structure ModuleStructure (S : Scheme.{u}) (N : TopCat.Sheaf Ab.{u} S) where
  /-- The underlying `𝒪_S`-module. -/
  toModule : S.Modules
  /-- The identification of the underlying abelian sheaf of `toModule` with `N`. -/
  underlyingIso : (moduleToSheafAb S).obj toModule ≅ N

/-- The ordinary pushforward `f_* M` is a module structure on the derived-functor `R⁰ f_* M`.
This is the constructed degree-zero higher direct image. -/
def pushforwardModuleStructure (f : X ⟶ S) (M : X.Modules) :
    ModuleStructure S (higherDirectImageModuleAb f M 0) where
  toModule := (Scheme.Modules.pushforward f).obj M
  underlyingIso := (higherDirectImageModuleAbZeroIso f M).symm

@[simp]
theorem pushforwardModuleStructure_toModule (f : X ⟶ S) (M : X.Modules) :
    (pushforwardModuleStructure f M).toModule = (Scheme.Modules.pushforward f).obj M := rfl

/-- Higher direct images with arbitrary-base-change comparison.

Degree zero is not part of the data: `R⁰ f_* M` is the ordinary pushforward `f_* M`, its base
change is `g_* p^* M`, and the degree-zero comparison is the canonical Beck--Chevalley morphism
`canonicalPushforwardBaseChangeComparison`, whose invertibility is exactly the field
`toPushforwardBaseChangeData`.  The remaining fields record the positive-degree higher direct
images `Rⁿ⁺¹ f_* M` — as `𝒪`-module structures on the derived functors constructed above, so that
they are the genuine higher direct images — together with their base changes, the comparison
morphisms, and the vanishing of `Rⁿ f_* M` for `n ≥ 2`, which is the curve-specific input. -/
structure CurveCohomologyBaseChangeData (f : X ⟶ S) (M : X.Modules) where
  /-- The `𝒪_S`-module structure on the positive-degree higher direct image `Rⁿ⁺¹ f_* M`. -/
  higherDirectImageSucc : ∀ n : ℕ, ModuleStructure S (higherDirectImageModuleAb f M (n + 1))
  /-- The `𝒪_T`-module structure on the positive-degree higher direct image `Rⁿ⁺¹ g_* p^* M` of a
  Cartesian base change. -/
  onBaseChangeSucc : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T),
    IsPullback p g f b → ∀ n : ℕ,
      ModuleStructure T (higherDirectImageModuleAb g ((Scheme.Modules.pullback p).obj M) (n + 1))
  /-- The base-change comparison morphism in positive degrees. -/
  comparisonSucc : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ),
      (Scheme.Modules.pullback b).obj (higherDirectImageSucc n).toModule ⟶
        (onBaseChangeSucc b p g h n).toModule
  /-- Cohomology and base change in positive degrees. -/
  comparisonSucc_isIso : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ), IsIso (comparisonSucc b p g h n)
  /-- Cohomology and base change in degree zero is ordinary-pushforward base change: the
  canonical Beck--Chevalley morphism is invertible. -/
  toPushforwardBaseChangeData : PushforwardBaseChangeData f M
  /-- Higher direct images of a family of curves vanish in degrees at least two. -/
  vanishesSucc : ∀ n, 1 ≤ n → IsZero (higherDirectImageSucc n).toModule

namespace CurveCohomologyBaseChangeData

variable {f : X ⟶ S} {M : X.Modules} (C : CurveCohomologyBaseChangeData f M)

/-- The `𝒪_S`-module structure on `Rⁿ f_* M`; in degree zero it is the ordinary pushforward. -/
def higherDirectImageStructure : ∀ n : ℕ, ModuleStructure S (higherDirectImageModuleAb f M n)
  | 0 => pushforwardModuleStructure f M
  | (n + 1) => C.higherDirectImageSucc n

/-- The higher direct image `Rⁿ f_* M` as an `𝒪_S`-module; in degree zero this is the ordinary
pushforward. -/
def higherDirectImage (n : ℕ) : S.Modules := (C.higherDirectImageStructure n).toModule

/-- The higher direct images carried by the data are the actual derived-functor higher direct
images, on underlying sheaves of abelian groups. -/
def higherDirectImageIso (n : ℕ) :
    (moduleToSheafAb S).obj (C.higherDirectImage n) ≅ higherDirectImageModuleAb f M n :=
  (C.higherDirectImageStructure n).underlyingIso

@[simp]
theorem higherDirectImage_zero :
    C.higherDirectImage 0 = (Scheme.Modules.pushforward f).obj M := rfl

@[simp]
theorem higherDirectImage_succ (n : ℕ) :
    C.higherDirectImage (n + 1) = (C.higherDirectImageSucc n).toModule := rfl

/-- The `𝒪_T`-module structure on `Rⁿ g_* p^* M` for a Cartesian base change; in degree zero it is
the ordinary pushforward of the pulled-back module. -/
def onBaseChangeStructure {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    ∀ n : ℕ, ModuleStructure T (higherDirectImageModuleAb g ((Scheme.Modules.pullback p).obj M) n)
  | 0 => pushforwardModuleStructure g ((Scheme.Modules.pullback p).obj M)
  | (n + 1) => C.onBaseChangeSucc b p g h n

/-- The higher direct image `Rⁿ g_* p^* M` of a Cartesian base change, as an `𝒪_T`-module. -/
def onBaseChange {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) : T.Modules :=
  (C.onBaseChangeStructure b p g h n).toModule

/-- The base-changed higher direct images carried by the data are the actual derived-functor
higher direct images of the base-changed family, on underlying sheaves of abelian groups. -/
def onBaseChangeIso {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) :
    (moduleToSheafAb T).obj (C.onBaseChange b p g h n) ≅
      higherDirectImageModuleAb g ((Scheme.Modules.pullback p).obj M) n :=
  (C.onBaseChangeStructure b p g h n).underlyingIso

@[simp]
theorem onBaseChange_zero {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    C.onBaseChange b p g h 0 =
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M) := rfl

@[simp]
theorem onBaseChange_succ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) :
    C.onBaseChange b p g h (n + 1) = (C.onBaseChangeSucc b p g h n).toModule := rfl

/-- The base-change comparison morphism; in degree zero it *is* the canonical Beck--Chevalley
morphism of the Cartesian square. -/
def comparison {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    ∀ n, (Scheme.Modules.pullback b).obj (C.higherDirectImage n) ⟶ C.onBaseChange b p g h n
  | 0 => canonicalPushforwardBaseChangeComparison f M b p g h
  | (n + 1) => C.comparisonSucc b p g h n

@[simp]
theorem comparison_zero {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    C.comparison b p g h 0 = canonicalPushforwardBaseChangeComparison f M b p g h := rfl

@[simp]
theorem comparison_succ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) :
    C.comparison b p g h (n + 1) = C.comparisonSucc b p g h n := rfl

/-- Cohomology and base change in every degree. -/
theorem comparison_isIso {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) : ∀ n, IsIso (C.comparison b p g h n)
  | 0 => C.toPushforwardBaseChangeData.comparison_isIso b p g h
  | (n + 1) => C.comparisonSucc_isIso b p g h n

/-- Cohomology and base change in degree zero gives ordinary pushforward base change. -/
theorem pushforwardBaseChangeData (C : CurveCohomologyBaseChangeData f M) :
    PushforwardBaseChangeData f M :=
  C.toPushforwardBaseChangeData

/-- The degree-zero higher direct image is the ordinary pushforward, by construction. -/
def degreeZeroIso : C.higherDirectImage 0 ≅ (Scheme.Modules.pushforward f).obj M :=
  Iso.refl _

/-- The base-changed degree-zero higher direct image is the ordinary pushforward of the
pulled-back module, by construction. -/
def baseChangedDegreeZeroIso {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    C.onBaseChange b p g h 0 ≅
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M) :=
  Iso.refl _

/-- The degree-zero comparison is the canonical Beck--Chevalley morphism. -/
theorem degreeZeroComparison {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    canonicalPushforwardBaseChangeComparison f M b p g h =
      (Scheme.Modules.pullback b).map C.degreeZeroIso.inv ≫
        C.comparison b p g h 0 ≫ (C.baseChangedDegreeZeroIso b p g h).hom := by
  simp [degreeZeroIso, baseChangedDegreeZeroIso]

/-- Higher direct images of a family of curves vanish in degrees at least two. -/
theorem vanishesAboveOne : ∀ n, 2 ≤ n → IsZero (C.higherDirectImage n)
  | 0, hn => by omega
  | 1, hn => by omega
  | (n + 2), _ => C.vanishesSucc (n + 1) (by omega)

/-- The actual derived-functor higher direct images of a family of curves vanish in degrees at
least two: the vanishing carried by the data transfers to the genuine `Rⁿ f_*` because the data
is a module structure on it. -/
theorem isZero_higherDirectImageModuleAb (C : CurveCohomologyBaseChangeData f M) (n : ℕ)
    (hn : 2 ≤ n) :
    IsZero (higherDirectImageModuleAb f M n) :=
  ((moduleToSheafAb S).map_isZero (C.vanishesAboveOne n hn)).of_iso
    (C.higherDirectImageIso n).symm

/-- The vanishing in degrees at least two is inherited by every base change: this is deduced from
the vanishing upstairs and from cohomology and base change, since pullback of modules is an
additive functor. -/
theorem baseChangedVanishesAboveOne {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) (hn : 2 ≤ n) : IsZero (C.onBaseChange b p g h n) := by
  have hiso : IsIso (C.comparison b p g h n) := C.comparison_isIso b p g h n
  have hzero : IsZero ((Scheme.Modules.pullback b).obj (C.higherDirectImage n)) :=
    (Scheme.Modules.pullback b).map_isZero (C.vanishesAboveOne n hn)
  exact hzero.of_iso (asIso (C.comparison b p g h n)).symm

/-- On the chosen base change, every higher comparison is an isomorphism. -/
instance chosenComparison_isIso {T : Scheme.{u}} (b : T ⟶ S) (n : ℕ) :
    IsIso (C.comparison b (pullback.fst f b) (pullback.snd f b)
      (IsPullback.of_hasPullback f b) n) :=
  C.comparison_isIso b (pullback.fst f b) (pullback.snd f b)
    (IsPullback.of_hasPullback f b) n

end CurveCohomologyBaseChangeData

/-- Algebraic upper semicontinuity for a natural-number-valued function: every jumping locus
`{s | m ≤ rank(s)}` is closed. -/
def IsUpperSemicontinuousNat {S : Type*} [TopologicalSpace S] (rank : S → ℕ) : Prop :=
  ∀ m, IsClosed {s | m ≤ rank s}

/-- A constant function is upper semicontinuous. -/
theorem isUpperSemicontinuousNat_const {S : Type*} [TopologicalSpace S] (r : ℕ) :
    IsUpperSemicontinuousNat (fun _ : S => r) := by
  intro m
  by_cases hm : m ≤ r
  · have hset : {_s : S | m ≤ r} = Set.univ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hm
    rw [hset]
    exact isClosed_univ
  · have hset : {_s : S | m ≤ r} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact hm
    rw [hset]
    exact isClosed_empty

/-- A rank profile for the fibre cohomology groups of a curve family. -/
structure CohomologyRankProfile (S : Scheme.{u}) where
  /-- The rank of the `n`-th fibre cohomology at a point of the base. -/
  rank : ℕ → S → ℕ
  /-- Every jumping locus is closed. -/
  upperSemicontinuous : ∀ n, IsUpperSemicontinuousNat (rank n)

namespace CohomologyRankProfile

/-- The constant rank profile; in particular rank profiles always exist. -/
def const (S : Scheme.{u}) (r : ℕ → ℕ) : CohomologyRankProfile S where
  rank n _ := r n
  upperSemicontinuous n := isUpperSemicontinuousNat_const (r n)

instance (S : Scheme.{u}) : Inhabited (CohomologyRankProfile S) :=
  ⟨const S fun _ => 0⟩

/-- Pullback of a rank profile along a scheme morphism. -/
def pullback {T S : Scheme.{u}} (P : CohomologyRankProfile S) (b : T ⟶ S) :
    CohomologyRankProfile T where
  rank n t := P.rank n (b t)
  upperSemicontinuous := by
    intro n m
    have hclosed := P.upperSemicontinuous n m
    have heq : {t : T | m ≤ P.rank n (b t)} = b ⁻¹' {s : S | m ≤ P.rank n s} := rfl
    rw [heq]
    exact hclosed.preimage b.continuous

@[simp]
theorem pullback_rank {T S : Scheme.{u}} (P : CohomologyRankProfile S) (b : T ⟶ S)
    (n : ℕ) (t : T) : (P.pullback b).rank n t = P.rank n (b t) := rfl

end CohomologyRankProfile

end

end GromovWitten.AlgebraicGeometry.Curves
