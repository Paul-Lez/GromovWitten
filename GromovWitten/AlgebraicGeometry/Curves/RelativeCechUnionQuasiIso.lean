/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechPairComplexBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechUnionBaseChange
import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechUnionSections
import GromovWitten.CategoryTheory.HomologySequenceLeftQuasiIso

/-!
# Relative Čech union-complex base change

The Mayer--Vietoris short exact sequence for the union complex extends the
pair-complex comparison to a union of two opens.  This file supplies the
quasi-isomorphism gluing step for the corresponding open-complex maps.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- If the open-complex base-change maps on `U`, `V`, and their intersection
are quasi-isomorphisms, then the map on `U ⊔ V` is a quasi-isomorphism. -/
lemma relativeOpenComplexBaseChangeMap_quasiIso_sup
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (w : p ≫ s = g ≫ b) [(Scheme.Modules.pullback b).PreservesHomology]
    {K : CochainComplex X.Modules ℕ} {J : CochainComplex Y.Modules ℕ}
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (hJ : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb Y).obj (J.X n)))
    (U V : X.Opens)
    [QuasiIso (relativeOpenComplexBaseChangeMap s b p g w φ U)]
    [QuasiIso (relativeOpenComplexBaseChangeMap s b p g w φ V)]
    [QuasiIso (relativeOpenComplexBaseChangeMap s b p g w φ (U ⊓ V))] :
    QuasiIso (relativeOpenComplexBaseChangeMap s b p g w φ (U ⊔ V)) := by
  let F := Scheme.Modules.pullback b
  let _ : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let _ : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  let CS := relativeCechUnionComplexMV K s U V
  let CT := relativeCechUnionComplexMV J g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
  have hs : CS.ShortExact := relativeCechUnionComplexMV_shortExact K s U V hK
  have ht : CT.ShortExact :=
    relativeCechUnionComplexMV_shortExact J g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hJ
  have hsF : (CS.map (F.mapHomologicalComplex (.up ℕ))).ShortExact :=
    hs.map_of_exact (F.mapHomologicalComplex (.up ℕ))
  let Φ : CS.map (F.mapHomologicalComplex (.up ℕ)) ⟶ CT :=
    relativeCechUnionComplexBaseChange K s b p g w U V ≫
      relativeCechUnionComplexMVMap φ g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
  have : QuasiIso Φ.τ₂ :=
    relativeCechPairComplexBaseChangeMap_quasiIso s b p g w φ U V
  have : QuasiIso Φ.τ₃ := by
    change QuasiIso (relativeOpenComplexBaseChangeMap s b p g w φ (U ⊓ V))
    infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₁ hsF ht Φ
end GromovWitten.AlgebraicGeometry.Curves
