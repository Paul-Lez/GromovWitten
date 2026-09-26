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

/-- The presheaf of relative Kähler differentials obtained from the structural sheaf map. -/
def relativeDifferentialsPresheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.PresheafOfModules := by
  exact PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (inverseImageCommRingSheaf.toStructureSheaf f).hom

/-- The sheafification of the relative differential presheaf over the source structure sheaf. -/
def relativeDifferentialsSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (relativeDifferentialsPresheaf f)

end

end GromovWitten.AlgebraicGeometry
