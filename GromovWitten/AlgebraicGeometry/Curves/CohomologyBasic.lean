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
# Ordinary module base change and abelian higher direct images

The ordinary Beck--Chevalley map is constructed from the pullback square and adjunctions.
Abelian higher direct images are right-derived pushforwards. `ModuleStructure` records an
identification with an underlying abelian sheaf; `ModuleDerived.lean` constructs this structure
for every higher direct image by comparing module injective resolutions with flasque resolutions.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open scoped ZeroObject

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
### Module structures on abelian higher direct images

The module-valued construction in `ModuleDerived.lean` supplies these structures canonically.
The degree-zero structure is already the ordinary module pushforward.
-/

/-- An `𝒪_S`-module structure on a sheaf of abelian groups `N`: an `𝒪_S`-module together with an
identification of its underlying abelian sheaf with `N`.

The canonical structure for every higher direct image is constructed in
`ModuleDerived.lean`. -/
structure ModuleStructure (S : Scheme.{u}) (N : TopCat.Sheaf Ab.{u} S) where
  /-- The underlying `𝒪_S`-module. -/
  toModule : S.Modules
  /-- The identification of the underlying abelian sheaf of `toModule` with `N`. -/
  underlyingIso : (moduleToSheafAb S).obj toModule ≅ N

/-- A zero abelian sheaf has its canonical zero `𝒪_S`-module structure.

This constructor is useful for acyclic derived images. It only applies after an actual
`IsZero` proof; it does not manufacture module structures for nonzero derived images. -/
noncomputable def ModuleStructure.of_isZero (S : Scheme.{u})
    (N : TopCat.Sheaf Ab.{u} S) (hN : IsZero N) : ModuleStructure S N where
  toModule := 0
  underlyingIso := (moduleToSheafAb S).map_isZero (isZero_zero _)
    |>.iso hN

/-- An injective underlying abelian sheaf has a canonical zero module structure on every positive
higher direct image. The proof uses derived vanishing and does not assert that the forgetful
functor preserves injectives. -/
noncomputable def higherDirectImageModuleStructure_of_injective (f : X ⟶ S) (M : X.Modules)
    (n : ℕ) [Injective ((moduleToSheafAb X).obj M)] :
    ModuleStructure S (higherDirectImageModuleAb f M (n + 1)) :=
  ModuleStructure.of_isZero S _
    (isZero_higherDirectImageModuleAb_succ_of_injective f M n)

/-- The ordinary pushforward `f_* M` is a module structure on the derived-functor `R⁰ f_* M`.
This is the constructed degree-zero higher direct image. -/
def pushforwardModuleStructure (f : X ⟶ S) (M : X.Modules) :
    ModuleStructure S (higherDirectImageModuleAb f M 0) where
  toModule := (Scheme.Modules.pushforward f).obj M
  underlyingIso := (higherDirectImageModuleAbZeroIso f M).symm

@[simp]
theorem pushforwardModuleStructure_toModule (f : X ⟶ S) (M : X.Modules) :
    (pushforwardModuleStructure f M).toModule = (Scheme.Modules.pushforward f).obj M := rfl

end

end GromovWitten.AlgebraicGeometry.Curves
