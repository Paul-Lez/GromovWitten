/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechAcyclicity
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechDerived
import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentHomology

/-!
# Quasicoherence of relative higher direct images

The selected-resolution comparison identifies open-piece homology with the
corresponding higher direct image objectwise.  A two-open short exact Čech
complex then glues quasicoherence from explicit all-degree hypotheses on the
two opens and their intersection over a locally Noetherian base.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
open Scheme.Modules
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The selected-resolution open homology comparison is objectwise; no
naturality in the module or open is asserted. -/
def relativeOpenHomologyIsoHigherDirectImage (s : X ⟶ S) (M : X.Modules)
    (I : InjectiveResolution M) (W : X.Opens) (n : ℕ) :
    (((relativeOpenPushforward s W).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology n ≅
      higherDirectImageModule (W.ι ≫ s) (M.restrict W.ι) n :=
  (I.isoRightDerivedObj (relativeOpenPushforward s W) n).symm ≪≫
    (NatIso.rightDerivedIso
      (Functor.isoWhiskerLeft (restrictFunctor W.ι) (pushforwardComp W.ι s)) n).app M ≪≫
    restrictPushforwardRightDerivedIso s W M n

set_option backward.isDefEq.respectTransparency false in
/-- Over a locally Noetherian base, a two-open Čech short exact complex glues
quasicoherence of the higher direct image from explicit all-degree
quasicoherence on the two opens and their intersection.  No source
Noetherianity or source-module quasicoherence is assumed beyond these inputs. -/
lemma isQuasicoherent_higherDirectImageModule_of_twoOpen [IsLocallyNoetherian S]
    (s : X ⟶ S) (M : X.Modules) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (hU : ∀ n, (higherDirectImageModule (U.ι ≫ s) (M.restrict U.ι) n).IsQuasicoherent)
    (hV : ∀ n, (higherDirectImageModule (V.ι ≫ s) (M.restrict V.ι) n).IsQuasicoherent)
    (hUV : ∀ n,
      (higherDirectImageModule ((U ⊓ V).ι ≫ s) (M.restrict (U ⊓ V).ι) n).IsQuasicoherent)
    (n : ℕ) : (higherDirectImageModule s M n).IsQuasicoherent := by
  let I := InjectiveResolution.of M
  let T := relativeCechComplexMV I.cocomplex s U V
  have hT : T.ShortExact := relativeCechComplexMV_shortExact I.cocomplex s U V hcover
    (fun k => module_isFlasque_of_injective (I.cocomplex.X k))
  have hopen (W : X.Opens)
      (hW : ∀ k, (higherDirectImageModule (W.ι ≫ s) (M.restrict W.ι) k).IsQuasicoherent)
      (k : ℕ) :
      ((((relativeOpenPushforward s W).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology k).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (relativeOpenHomologyIsoHigherDirectImage s M I W k).symm (hW k)
  have h₂ (k : ℕ) : (T.X₂.homology k).IsQuasicoherent :=
    isQuasicoherent_relativeCechPair_homology s U V I.cocomplex k
      (hopen U hU k) (hopen V hV k)
  have h₃ (k : ℕ) : (T.X₃.homology k).IsQuasicoherent := hopen (U ⊓ V) hUV k
  have h₁ := isQuasicoherent_homology_left T hT h₂ h₃ n
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (I.isoRightDerivedObj (pushforward s) n).symm h₁
end GromovWitten.AlgebraicGeometry.Curves
