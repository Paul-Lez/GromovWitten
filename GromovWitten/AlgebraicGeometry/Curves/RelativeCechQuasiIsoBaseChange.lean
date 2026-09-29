/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechPairComplexBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechComplexBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechDerived
import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenComplexBaseChange
import GromovWitten.AlgebraicGeometry.Curves.HigherBaseChange
import GromovWitten.CategoryTheory.HomologySequenceLeftQuasiIso

/-!
# A fixed-resolution Čech base-change criterion

Once the two branch complexes and the overlap complex have supplied
quasi-isomorphisms, the canonical base-change map on every derived degree is
invertible.  No affine, Noetherian, or quasicoherence hypotheses are used
here.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
open Scheme.Modules

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical derived base-change map is an isomorphism when the three
open-complex maps in a two-open cover are quasi-isomorphisms. -/
lemma moduleHigherBaseChange_isIso_of_threeQuasiIso
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    (M : X.Modules)
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution M).cocomplex ⟶
        (injectiveResolution ((Scheme.Modules.pullback p).obj M)).cocomplex)
    (hφ : (singleMapHomologicalComplex (Scheme.Modules.pullback p) (.up ℕ) 0).inv.app M ≫
      ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).map
        (injectiveResolution M).ι ≫ φ =
          (injectiveResolution ((Scheme.Modules.pullback p).obj M)).ι)
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [QuasiIso (relativeOpenComplexBaseChangeMap s b p g h.w φ U)]
    [QuasiIso (relativeOpenComplexBaseChangeMap s b p g h.w φ V)]
    [QuasiIso (relativeOpenComplexBaseChangeMap s b p g h.w φ (U ⊓ V))]
    (n : ℕ) :
    IsIso ((moduleHigherBaseChangeNatTrans s b p g h n).app M) := by
  let F := Scheme.Modules.pullback b
  have : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  let L := Scheme.Modules.pullback p
  let I := injectiveResolution M
  let J := injectiveResolution (L.obj M)
  let Up := p ⁻¹ᵁ U
  let Vp := p ⁻¹ᵁ V
  have hcover' : Up ⊔ Vp = ⊤ := by
    dsimp only [Up, Vp]
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  let CS := relativeCechComplexMV I.cocomplex s U V
  let CT := relativeCechComplexMV J.cocomplex g Up Vp
  have hs : CS.ShortExact := relativeCechComplexMV_shortExact I.cocomplex s U V hcover
    (fun k => module_isFlasque_of_injective (I.cocomplex.X k))
  have ht : CT.ShortExact := relativeCechComplexMV_shortExact J.cocomplex g Up Vp hcover'
    (fun k => module_isFlasque_of_injective (J.cocomplex.X k))
  let Φ : CS.map (F.mapHomologicalComplex (.up ℕ)) ⟶ CT :=
    relativeCechComplexBaseChange I.cocomplex s b p g h U V ≫
      relativeCechComplexMVMap φ g Up Vp
  have hsF : (CS.map (F.mapHomologicalComplex (.up ℕ))).ShortExact :=
    hs.map_of_exact (F.mapHomologicalComplex (.up ℕ))
  have : QuasiIso Φ.τ₂ := by
    exact relativeCechPairComplexBaseChangeMap_quasiIso s b p g h.w φ U V
  have : QuasiIso Φ.τ₃ := by
    change QuasiIso (relativeOpenComplexBaseChangeMap s b p g h.w φ (U ⊓ V))
    infer_instance
  have : QuasiIso Φ.τ₁ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₁ hsF ht Φ
  have hₙ : IsIso (HomologicalComplex.homologyMap Φ.τ₁ n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  exact (NatTrans.rightDerivedBaseChange_isIso_iff
    (modulePushforwardBaseChangeNatTrans s b p g h) M n φ hφ).mpr hₙ

end GromovWitten.AlgebraicGeometry.Curves
