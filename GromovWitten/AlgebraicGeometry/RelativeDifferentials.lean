import GromovWitten.AlgebraicGeometry.FittingIdealsSheaf
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.CommRingCat

open CategoryTheory Limits Topology
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

noncomputable section

/-- The inverse image of the target structure sheaf, as a sheaf of commutative rings. -/
def inverseImageCommRingSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pullback CommRingCat f.base).obj Y.sheaf

/-- The canonical map from the inverse image of the target structure sheaf to the source. -/
def inverseImageCommRingSheaf.toStructureSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    inverseImageCommRingSheaf f ⟶ X.sheaf :=
  let g : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf :=
    ObjectProperty.homMk f.toLRSHom.toShHom.hom.c
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv
    Y.sheaf X.sheaf |>.symm g

/-- The presheaf map of commutative rings underlying the structural map used above. -/
def relativeDifferentialsRingMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (inverseImageCommRingSheaf f).presheaf ⟶ X.sheaf.presheaf :=
  (inverseImageCommRingSheaf.toStructureSheaf f).hom

/-- The presheaf of relative Kähler differentials obtained from the structural sheaf map. -/
def relativeDifferentialsPresheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.PresheafOfModules := by
  exact PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (relativeDifferentialsRingMap f)

/-- The sheafification of the relative differential presheaf over the source structure sheaf. -/
def relativeDifferentialsSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (relativeDifferentialsPresheaf f)

/-- The Fitting ideal of the relative differential sections on an open of the source.

This is the sectionwise ingredient for the global Fitting ideal sheaf; compatibility under
restriction requires the usual finite-presentation and localization hypotheses. -/
def relativeDifferentialsSectionFittingIdeal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (i : ℕ) : Ideal Γ(X, U) :=
  Module.fittingIdeal Γ(X, U) Γ(relativeDifferentialsSheaf f, U) i

/-- The sheaf-level map induced by the universal property of relative differentials.

The input is a compatible presheaf derivation into a sheaf of source modules; the
sheafification adjunction turns the resulting presheaf map into a morphism of sheaves. -/
def relativeDifferentialsSheafLift {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N : X.Modules}
    (d : ((Scheme.Modules.toPresheafOfModules X).obj N).Derivation'
      (relativeDifferentialsRingMap f)) :
    relativeDifferentialsSheaf f ⟶ N :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
    ((PresheafOfModules.DifferentialsConstruction.isUniversal'
      (relativeDifferentialsRingMap f)).desc d)

/-- The universal derivation after passing from the presheaf to its sheafification. -/
def relativeDifferentialsSheafDerivation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((Scheme.Modules.toPresheafOfModules X).obj (relativeDifferentialsSheaf f)).Derivation'
      (relativeDifferentialsRingMap f) :=
  (PresheafOfModules.DifferentialsConstruction.derivation'
    (relativeDifferentialsRingMap f)).postcomp
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (relativeDifferentialsPresheaf f))

theorem relativeDifferentialsSheafLift_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N : X.Modules}
    (d : ((Scheme.Modules.toPresheafOfModules X).obj N).Derivation'
      (relativeDifferentialsRingMap f)) :
    (relativeDifferentialsSheafDerivation f).postcomp
        ((Scheme.Modules.toPresheafOfModules X).map (relativeDifferentialsSheafLift f d)) = d := by
  have hq :
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (relativeDifferentialsPresheaf f) ≫
        (Scheme.Modules.toPresheafOfModules X).map (relativeDifferentialsSheafLift f d) =
      (PresheafOfModules.DifferentialsConstruction.isUniversal'
        (relativeDifferentialsRingMap f)).desc d := by
    change (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj))
        (relativeDifferentialsSheafLift f d) = _
    exact Equiv.apply_symm_apply _ _
  apply PresheafOfModules.Derivation.ext
  ext Z b
  dsimp [relativeDifferentialsSheafDerivation, PresheafOfModules.Derivation.postcomp]
  have hqZ := congrArg (fun q =>
      (q.app Z).hom ((PresheafOfModules.DifferentialsConstruction.derivation'
        (relativeDifferentialsRingMap f)).d b)) hq
  have hfac := (PresheafOfModules.DifferentialsConstruction.isUniversal'
    (relativeDifferentialsRingMap f)).fac d
  have hfacZ := congrArg (fun q => q.d b) hfac
  calc
    _ = (ModuleCat.Hom.hom (((PresheafOfModules.DifferentialsConstruction.isUniversal'
      (relativeDifferentialsRingMap f)).desc d).app Z))
        ((PresheafOfModules.DifferentialsConstruction.derivation'
          (relativeDifferentialsRingMap f)).d b) := hqZ
    _ = d.d b := by simpa [PresheafOfModules.Derivation.postcomp] using hfacZ

theorem relativeDifferentialsSheafLift_unique {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N : X.Modules}
    (d : ((Scheme.Modules.toPresheafOfModules X).obj N).Derivation'
      (relativeDifferentialsRingMap f))
    (g : relativeDifferentialsSheaf f ⟶ N)
    (hg : (relativeDifferentialsSheafDerivation f).postcomp
        ((Scheme.Modules.toPresheafOfModules X).map g) = d) :
    relativeDifferentialsSheafLift f d = g := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).injective
  apply (PresheafOfModules.DifferentialsConstruction.isUniversal'
    (relativeDifferentialsRingMap f)).postcomp_injective
  have hqlift :
      (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj))
          (relativeDifferentialsSheafLift f d) =
        (PresheafOfModules.DifferentialsConstruction.isUniversal'
          (relativeDifferentialsRingMap f)).desc d := by
    exact Equiv.apply_symm_apply _ _
  rw [hqlift]
  calc
    _ = d := (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (relativeDifferentialsRingMap f)).fac d
    _ = _ := by
      symm
      have hqg :
          (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (relativeDifferentialsPresheaf f) ≫
            (Scheme.Modules.toPresheafOfModules X).map g =
          (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)) g := by
        change (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)) g = _
        rfl
      apply PresheafOfModules.Derivation.ext
      ext Z b
      dsimp [PresheafOfModules.Derivation.postcomp]
      have hqgZ := congrArg (fun q =>
          (q.app Z).hom ((PresheafOfModules.DifferentialsConstruction.derivation'
            (relativeDifferentialsRingMap f)).d b)) hqg
      have hgZ := congrArg (fun q => q.d b) hg
      calc
        _ = (ModuleCat.Hom.hom (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app (relativeDifferentialsPresheaf f) ≫
            (Scheme.Modules.toPresheafOfModules X).map g).app Z))
            ((PresheafOfModules.DifferentialsConstruction.derivation'
              (relativeDifferentialsRingMap f)).d b) := hqgZ.symm
        _ = d.d b := by
          change (ModuleCat.Hom.hom (((Scheme.Modules.toPresheafOfModules X).map g).app Z))
              ((ModuleCat.Hom.hom (((PresheafOfModules.sheafificationAdjunction
                (𝟙 X.ringCatSheaf.obj)).unit.app (relativeDifferentialsPresheaf f)).app Z))
                ((PresheafOfModules.DifferentialsConstruction.derivation'
                  (relativeDifferentialsRingMap f)).d b)) = d.d b
          convert hgZ using 1; rfl

end

end GromovWitten.AlgebraicGeometry
