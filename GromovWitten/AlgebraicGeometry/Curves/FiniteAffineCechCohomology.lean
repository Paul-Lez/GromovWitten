/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteAffineCechComplex
import GromovWitten.AlgebraicGeometry.Curves.FlasqueFiniteCechComparison
import GromovWitten.AlgebraicGeometry.Curves.BaseSectionsFlasqueCohomology

/-!
# Sheaf cohomology from finite affine Čech complexes

The resolution augmentation and the finite-cover augmentation of a flasque
resolution are both quasi-isomorphisms. Their induced homology isomorphisms
identify the explicit finite affine complex with actual base-linear sheaf cohomology.
The construction works for quasi-coherent modules on locally Noetherian separated
schemes; it does not require properness or assert finite generation of cohomology.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R : CommRingCat.{u}} {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The two canonical finite Čech comparison maps identify the homology of the
finite affine complex with base-linear cohomology computed by a flasque resolution. -/
noncomputable def baseFiniteCechHomologyIsoOfFlasqueResolution
    [IsLocallyNoetherian X] [X.IsSeparated]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W) (hcover : coverUnion U = ⊤)
    (n : ℕ) :
    (baseFiniteCechComplex s M U).homology (n : ℤ) ≅ cohomologyModuleCat R s M n := by
  let KI := K.extend ComplexShape.embeddingUpNat
  let F := ((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj KI
  let f := (evaluatePresheafComplexMap
    (finiteCechMap (resolutionSectionsAugmentation s a) U)).app (op ⊤)
  let g := (finiteCechAugmentation F U).app (op ⊤)
  have hf : QuasiIso f := resolutionFiniteCechMap_quasiIso s M a hK U hU
  have hg : QuasiIso g := finiteCechAugmentation_baseSections_quasiIso s KI
    (moduleFlasque_extend_nat K hK) U ⊤ (by rw [hcover])
  exact asIso (homologyMap f (n : ℤ)) ≪≫ (asIso (homologyMap g (n : ℤ))).symm ≪≫
    intBaseSectionsFlasqueHomologyIso s a hK n

/-- A finite affine cover computes actual base-linear sheaf cohomology in every
nonnegative degree. The comparison uses the chosen injective resolution. -/
noncomputable def baseFiniteCechHomologyIso
    [IsLocallyNoetherian X] [X.IsSeparated]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W) (hcover : coverUnion U = ⊤)
    (n : ℕ) :
    (baseFiniteCechComplex s M U).homology (n : ℤ) ≅ cohomologyModuleCat R s M n :=
  baseFiniteCechHomologyIsoOfFlasqueResolution s M (injectiveResolution M).ι
    (fun i => module_isFlasque_of_injective ((injectiveResolution M).cocomplex.X i))
    U hU hcover n

end GromovWitten.AlgebraicGeometry.Curves
