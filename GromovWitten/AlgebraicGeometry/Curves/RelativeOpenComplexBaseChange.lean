/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenAffineBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechAcyclicity
import GromovWitten.AlgebraicGeometry.Curves.HigherBaseChange

/-!
# Base change for relative open-pushforward complexes

The generic open-complex base-change map accepts arbitrary cochain complexes
and a supplied map from the pulled-back source complex.  For canonical
injective resolutions over an affine source composite, exact pullbacks and
local Noetherianity make this map a quasi-isomorphism.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The generic open-complex base-change map, followed by a supplied cochain
map from the pulled-back source complex.  Its definition imposes no
chosen-resolution compatibility condition. -/
def relativeOpenComplexBaseChangeMap
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (w : p ≫ s = g ≫ b)
    {K : CochainComplex X.Modules ℕ} {J : CochainComplex Y.Modules ℕ}
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (U : X.Opens) :
    ((Scheme.Modules.pullback b).mapHomologicalComplex (.up ℕ)).obj
      (((relativeOpenPushforward s U).mapHomologicalComplex (.up ℕ)).obj K) ⟶
      ((relativeOpenPushforward g (p ⁻¹ᵁ U)).mapHomologicalComplex (.up ℕ)).obj J := by
  let F := Scheme.Modules.pullback b
  let L := Scheme.Modules.pullback p
  let Q := relativeOpenPushforward s U
  let P := relativeOpenPushforward g (p ⁻¹ᵁ U)
  let a : (F.mapHomologicalComplex (.up ℕ)).obj
      ((Q.mapHomologicalComplex (.up ℕ)).obj K) ⟶
      (P.mapHomologicalComplex (.up ℕ)).obj ((L.mapHomologicalComplex (.up ℕ)).obj K) :=
    (NatTrans.mapHomologicalComplex (relativeOpenBaseChangeNatTrans s b p g w U)
      (.up ℕ)).app K
  exact a ≫ (P.mapHomologicalComplex (.up ℕ)).map φ

set_option backward.isDefEq.respectTransparency false in
/-- For canonical injective resolutions with compatible augmentation, exact
pullbacks, locally Noetherian source and target, a quasicoherent module, and
an affine source open composite, the open-complex base-change map is a
quasi-isomorphism.  No Noetherian hypothesis on the base is required. -/
lemma relativeOpenComplexBaseChangeMap_quasiIso_of_affine
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent]
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution M).cocomplex ⟶
        (injectiveResolution ((Scheme.Modules.pullback p).obj M)).cocomplex)
    (hφ : (singleMapHomologicalComplex (Scheme.Modules.pullback p) (.up ℕ) 0).inv.app M ≫
      ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).map
        (injectiveResolution M).ι ≫ φ =
          (injectiveResolution ((Scheme.Modules.pullback p).obj M)).ι)
    (U : X.Opens) [IsAffineHom (U.ι ≫ s)] :
    QuasiIso (relativeOpenComplexBaseChangeMap s b p g h.w φ U) := by
  let F := Scheme.Modules.pullback b
  let I := injectiveResolution M
  let N := (Scheme.Modules.pullback p).obj M
  let J := injectiveResolution N
  let K := ((relativeOpenPushforward s U).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let hU := (isPullback_morphismRestrict p U).paste_vert h
  let _ : IsAffineHom ((p ⁻¹ᵁ U).ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hU inferInstance
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  cases n with
  | zero =>
    let _ : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) := by
      let _ : PreservesFiniteLimits (Scheme.Modules.pullback U.ι) :=
        Functor.preservesFiniteLimits_of_preservesHomology _
      exact preservesFiniteLimits_of_natIso
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
    let _ : PreservesFiniteLimits (Scheme.Modules.restrictFunctor (p ⁻¹ᵁ U).ι) := by
      let _ : PreservesFiniteLimits (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι) :=
        Functor.preservesFiniteLimits_of_preservesHomology _
      exact preservesFiniteLimits_of_natIso
        (Scheme.Modules.restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι).symm
    have : IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w U).app M) :=
      relativeOpenBaseChangeNatTrans_isIso s b p g h U M
    exact NatTrans.baseChange_homologyMap_zero_isIso
      (relativeOpenBaseChangeNatTrans s b p g h.w U) M φ hφ
  | succ n =>
    have hK : IsZero (K.homology (n + 1)) :=
      (isZero_relativeOpenPushforward_rightDerived_succ s U M n).of_iso
        (I.isoRightDerivedObj (relativeOpenPushforward s U) (n + 1)).symm
    have hsource : IsZero
        (((F.mapHomologicalComplex (.up ℕ)).obj K).homology (n + 1)) :=
      (F.map_isZero hK).of_iso ((K.sc (n + 1)).mapHomologyIso F)
    have htarget : IsZero
        ((((relativeOpenPushforward g (p ⁻¹ᵁ U)).mapHomologicalComplex (.up ℕ)).obj
          J.cocomplex).homology (n + 1)) :=
      (isZero_relativeOpenPushforward_rightDerived_succ g (p ⁻¹ᵁ U) N n).of_iso
        (J.isoRightDerivedObj (relativeOpenPushforward g (p ⁻¹ᵁ U)) (n + 1)).symm
    exact hsource.isIso htarget _
end GromovWitten.AlgebraicGeometry.Curves
