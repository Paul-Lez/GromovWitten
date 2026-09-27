import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineFlasque
import GromovWitten.AlgebraicGeometry.SheafCohomology.Flasque
import GromovWitten.AlgebraicGeometry.Curves.CohomologyBaseChange
import GromovWitten.AlgebraicGeometry.Curves.ModuleExact
import GromovWitten.AlgebraicGeometry.Curves.ModuleEnoughInjectives
import GromovWitten.AlgebraicGeometry.SheafCohomology.FlasqueResolution
import GromovWitten.AlgebraicGeometry.SheafCohomology.PointSheaves
import GromovWitten.AlgebraicGeometry.SheafCohomology.TildeExact

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

universe u

noncomputable section

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The unique map from an affine scheme's underlying space to the one-point space. -/
def affineToPoint (A : CommRingCat.{u}) :
    (Spec A).toTopCat ⟶ TopCat.of PUnit := TopCat.isTerminalPUnit.from _

noncomputable instance affineToPoint_additive (A : CommRingCat.{u}) :
    (TopCat.Sheaf.pushforward AddCommGrpCat (affineToPoint A)).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- Positive derived pushforwards of an injective affine module sheaf vanish.

The sheaf is the actual underlying abelian sheaf of `M^~`; its flasqueness is proved by
localization and Noetherian compactness in `AffineFlasque`. -/
theorem isZero_affineToPoint_rightDerived_succ_of_injective
    (A : CommRingCat.{u}) [IsNoetherianRing A] (M : ModuleCat.{u} A)
    [Module.Injective A M] (n : ℕ) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat (affineToPoint A)).rightDerived (n + 1)).obj
      ((SheafOfModules.toSheaf (Spec A).ringCatSheaf).obj (tilde M))) := by
  let _ : TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (Spec A).ringCatSheaf).obj (tilde M)) :=
    AlgebraicGeometry.AffineFlasque.isFlasque_tilde_of_injective A M
  exact TopCat.Sheaf.isZero_rightDerived_pushforward_of_isFlasque
    (affineToPoint A) _ n

/-- The additive group of global sections of the associated sheaf on an affine scheme. -/
def affineTildeGlobalSections (A : CommRingCat.{u}) :
    ModuleCat A ⥤ AddCommGrpCat :=
  tilde.functor A ⋙ moduleSpecΓFunctor ⋙ forget₂ (ModuleCat A) AddCommGrpCat

/-- Global sections identify affine associated sheaves with their defining modules. -/
noncomputable def affineTildeGlobalSectionsIso (A : CommRingCat.{u}) :
    affineTildeGlobalSections A ≅ forget₂ (ModuleCat A) AddCommGrpCat := by
  exact Functor.isoWhiskerRight (tilde.toTildeΓNatIso (R := A)).symm
    (forget₂ (ModuleCat A) AddCommGrpCat)

noncomputable instance affineTildeGlobalSections_preservesFiniteLimits
    (A : CommRingCat.{u}) :
    PreservesFiniteLimits (affineTildeGlobalSections A) := by
  apply preservesFiniteLimits_of_natIso (affineTildeGlobalSectionsIso A).symm

noncomputable instance affineTildeGlobalSections_preservesFiniteColimits
    (A : CommRingCat.{u}) :
    PreservesFiniteColimits (affineTildeGlobalSections A) := by
  apply preservesFiniteColimits_of_natIso (affineTildeGlobalSectionsIso A).symm

noncomputable instance affineTildeGlobalSections_preservesHomology
    (A : CommRingCat.{u}) :
    (affineTildeGlobalSections A).PreservesHomology := by
  infer_instance

noncomputable instance affineTildeGlobalSections_additive (A : CommRingCat.{u}) :
    (affineTildeGlobalSections A).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- The composite associated-sheaf/global-sections functor is exact, so its positive
right derived functors vanish. The sheaf-cohomology comparison is proved below. -/
theorem isZero_affineTildeGlobalSections_rightDerived_succ
    (A : CommRingCat.{u}) (M : ModuleCat A) (n : ℕ) :
    IsZero (((affineTildeGlobalSections A).rightDerived (n + 1)).obj M) :=
  GromovWitten.AlgebraicGeometry.Curves.isZero_rightDerived_succ_of_preservesHomology
    (affineTildeGlobalSections A) n M

noncomputable def affineTildeSheaf (A : CommRingCat.{u}) :
    ModuleCat A ⥤ TopCat.Sheaf AddCommGrpCat (Spec A).toTopCat :=
  tilde.functor A ⋙ moduleToSheafAb (Spec A)

noncomputable instance tilde_additive (A : CommRingCat.{u}) :
    (tilde.functor A).Additive := by
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (tilde.functor A)
  exact Functor.additive_of_preservesBinaryBiproducts _

noncomputable instance affineTildeSheaf_additive (A : CommRingCat.{u}) :
    (affineTildeSheaf A).Additive := by
  change (tilde.functor A ⋙ moduleToSheafAb (Spec A)).Additive
  infer_instance

noncomputable instance affineTildeSheaf_preservesZeroMorphisms (A : CommRingCat.{u}) :
    (affineTildeSheaf A).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

noncomputable instance affineTildeSheaf_preservesHomology (A : CommRingCat.{u}) :
    (affineTildeSheaf A).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  have htilde := (Functor.exact_tfae (tilde.functor A)).out 2 1 |>.mp
    (AlgebraicGeometry.tilde.preservesHomology A)
  have hmodule := (Functor.exact_tfae (moduleToSheafAb (Spec A))).out 2 1 |>.mp
    (Curves.moduleToSheafAb_preservesHomology (X := Spec A))
  exact hmodule _ (htilde S hS)

/-- Positive cohomology of an arbitrary quasi-coherent module on an affine vanishes. -/
theorem isZero_affineToPoint_rightDerived_succ
    (A : CommRingCat.{u}) [IsNoetherianRing A] (M : ModuleCat.{u} A) (n : ℕ) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat (affineToPoint A)).rightDerived
      (n + 1)).obj ((affineTildeSheaf A).obj M)) := by
  let I : InjectiveResolution M := InjectiveResolution.of M
  let T := affineTildeSheaf A
  let K := (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let eSingle := HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0
  let a := (eSingle.inv.app M) ≫
    (T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have hK (k : ℕ) : TopCat.Sheaf.IsFlasque (K.X k) := by
    let hmod : Module.Injective A (I.cocomplex.X k) :=
      @Module.injective_module_of_injective_object A (I.cocomplex.X k)
        _ _ _ (I.injective k)
    exact @AlgebraicGeometry.AffineFlasque.isFlasque_tilde_of_injective A _ _ hmod
  let _ : QuasiIso a := by infer_instance
  let hright := TopCat.Sheaf.flasqueResolutionRightDerivedIso
    (f := (affineToPoint A)) a hK (n + 1)
  refine IsZero.of_iso ?_ hright
  let P := TopCat.Sheaf.pushforward AddCommGrpCat (affineToPoint A)
  let Kp := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let B := PointSheaves.globalSections
  let hBhom : B.obj (Kp.homology (n + 1)) ≅
      ((B.mapHomologicalComplex (ComplexShape.up ℕ)).obj Kp).homology (n + 1) := by
    exact (ShortComplex.mapHomologyIso (Kp.sc (n + 1)) B).symm
  have hglobal : IsZero
      ((((affineTildeGlobalSections A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology (n + 1)) := by
    exact IsZero.of_iso
      (isZero_affineTildeGlobalSections_rightDerived_succ A M n)
      (I.isoRightDerivedObj (affineTildeGlobalSections A) (n + 1)).symm
  have htargetglobal : IsZero (B.obj (Kp.homology (n + 1))) := by
    exact IsZero.of_iso hglobal hBhom
  exact PointSheaves.isZero_of_globalSections_obj _ htargetglobal

end
end GromovWitten.AlgebraicGeometry.SheafCohomology
