/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleFlasqueSections
import GromovWitten.AlgebraicGeometry.Curves.HigherDirectImageQuasiCoherent
import GromovWitten.AlgebraicGeometry.Curves.ModuleFlasqueResolution
import GromovWitten.AlgebraicGeometry.SheafCohomology.AcyclicComplexSections

/-!
# Global sections of higher direct images

For a quasi-compact separated morphism to a Noetherian affine base, global
sections of every module-valued higher direct image identify with the source
cohomology as a module over the base ring.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R : CommRingCat.{u}} [IsNoetherianRing R]
  {X : Scheme.{u}} [IsLocallyNoetherian X]

set_option backward.isDefEq.respectTransparency false in
/-- Over a Noetherian affine base, global sections of every higher direct image
are the actual base-linear cohomology of the source. -/
def higherDirectImageSectionsIsoCohomology
    (s : X ⟶ Spec R) [QuasiCompact s] [IsSeparated s]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (moduleSpecΓFunctor (R := R)).obj (higherDirectImageModule s M n) ≅
      cohomologyModuleCat R s M n := by
  cases n with
  | zero =>
    exact (moduleSpecΓFunctor (R := R)).mapIso (higherDirectImageModuleZeroIso s M) ≪≫
      (pushforwardSectionsBaseLinearEquiv s M).toModuleIso ≪≫
        (cohomologyZeroBaseLinearEquiv R s M).symm.toModuleIso
  | succ n =>
    let _ : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_Spec.mpr inferInstance
    let I := InjectiveResolution.of M
    let K := ((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    have hI (j : ℕ) : TopCat.Sheaf.IsFlasque
        ((moduleToSheafAb X).obj (I.cocomplex.X j)) :=
      module_isFlasque_of_injective _
    have hK (j : ℕ) : TopCat.Sheaf.IsFlasque
        ((moduleToSheafAb (Spec R)).obj (K.X j)) := by
      let _ := hI j
      exact modulePushforward_isFlasque s _
    have hH (j : ℕ) : (K.homology j).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
        (I.isoRightDerivedObj (Scheme.Modules.pushforward s) j)
        (isQuasicoherent_higherDirectImageModule_of_quasiCompact_separated s M j)
    exact (moduleSpecΓFunctor (R := R)).mapIso
      (I.isoRightDerivedObj (Scheme.Modules.pushforward s) (n + 1)) ≪≫
        moduleSpecΓHomologyIsoOfFlasque K hK hH (n + 1) ≪≫
          moduleFlasqueResolutionSectionsIsoCohomology s I.ι hI n
end GromovWitten.AlgebraicGeometry.Curves
