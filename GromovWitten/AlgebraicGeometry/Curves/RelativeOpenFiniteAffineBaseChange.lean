/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechUnionQuasiIso
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineCoverVanishing

/-!
# Finite affine unions for relative open-complex base change

The affine open-complex comparison extends by Mayer--Vietoris to the union
of any finite list of affine opens.  The argument is local to that union and
does not require the list to cover the whole source.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- For a finite list of affine opens, the open-complex base-change map
associated to a fixed compatible resolution comparison is a quasi-isomorphism
on their union.  The source and target schemes are locally Noetherian, the
source is separated over an affine base, and the comparison uses canonical
injective resolutions. -/
lemma relativeOpenComplexBaseChangeMap_quasiIso_of_finiteAffine
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    [IsAffine S] [X.IsSeparated] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent]
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution M).cocomplex ⟶
        (injectiveResolution ((Scheme.Modules.pullback p).obj M)).cocomplex)
    (hφ : (singleMapHomologicalComplex (Scheme.Modules.pullback p) (.up ℕ) 0).inv.app M ≫
      ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).map
        (injectiveResolution M).ι ≫ φ =
          (injectiveResolution ((Scheme.Modules.pullback p).obj M)).ι)
    (Us : List X.Opens) (hUs : ∀ U ∈ Us, IsAffineOpen U) :
    QuasiIso (relativeOpenComplexBaseChangeMap s b p g h.w φ (affineUnion Us)) := by
  let I := injectiveResolution M
  let J := injectiveResolution ((Scheme.Modules.pullback p).obj M)
  cases Us with
  | nil =>
    let _ : IsAffine (⊥ : X.Opens).toScheme := isAffineOpen_bot X
    exact relativeOpenComplexBaseChangeMap_quasiIso_of_affine
      s b p g h M φ hφ (⊥ : X.Opens)
  | cons U Us =>
    have hU : IsAffineOpen U := hUs U (by simp)
    let _ : IsAffine U.toScheme := hU
    let _ : IsAffineHom (U.ι ≫ s) := inferInstance
    let _ : QuasiIso (relativeOpenComplexBaseChangeMap s b p g h.w φ U) :=
      relativeOpenComplexBaseChangeMap_quasiIso_of_affine
        s b p g h M φ hφ U
    have htailUs : ∀ V ∈ Us, IsAffineOpen V := by
      intro V hV
      exact hUs V (by simp [hV])
    let _ : QuasiIso
        (relativeOpenComplexBaseChangeMap s b p g h.w φ (affineUnion Us)) :=
      relativeOpenComplexBaseChangeMap_quasiIso_of_finiteAffine
        s b p g h M φ hφ Us htailUs
    have hmap : ∀ V ∈ Us.map (fun W => U ⊓ W), IsAffineOpen V := by
      intro V hV
      obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hV
      exact hU.inf (htailUs W hW)
    let _ : QuasiIso
        (relativeOpenComplexBaseChangeMap s b p g h.w φ
          (U ⊓ affineUnion Us)) := by
      rw [affineUnion_inf]
      exact relativeOpenComplexBaseChangeMap_quasiIso_of_finiteAffine
        s b p g h M φ hφ (Us.map (fun W => U ⊓ W)) hmap
    have hsup := relativeOpenComplexBaseChangeMap_quasiIso_sup
      s b p g h.w φ
      (fun n => module_isFlasque_of_injective (I.cocomplex.X n))
      (fun n => module_isFlasque_of_injective (J.cocomplex.X n))
      U (affineUnion Us)
    simpa only [affineUnion] using hsup
termination_by Us.length
decreasing_by
  all_goals
    simp_wf
    simp_all only [List.length_cons]
    omega

end GromovWitten.AlgebraicGeometry.Curves
