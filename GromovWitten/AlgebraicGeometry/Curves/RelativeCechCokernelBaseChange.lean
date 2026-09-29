/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenAffineBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechDerived

/-!
# Relative Čech cokernel base change

The cokernel comparison is assembled from the pair and overlap base-change maps
for a specified Cartesian square.  The higher-direct-image map transports this
comparison through the two chosen relative Čech comparisons.  Its agreement
with the separately defined canonical derived base-change map is established
elsewhere.
-/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel map induced by the relative Čech base-change square.  This
construction has no Noetherian, flatness, or affine hypotheses. -/
def relativeCechCokernelBaseChangeMap (s : X ⟶ S) (b : T ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ T) (h : IsPullback p g s b) (M : X.Modules)
    (U V : X.Opens) :
    (Scheme.Modules.pullback b).obj
        (cokernel (relativeCechFromPair s M U V)) ⟶
    cokernel (relativeCechFromPair g ((Scheme.Modules.pullback p).obj M)
        (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)) := by
  let F := Scheme.Modules.pullback b
  let d := relativeCechFromPair s M U V
  let d' := relativeCechFromPair g ((Scheme.Modules.pullback p).obj M)
    (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
  let βpair : F.obj ((relativeCechPairFunctor s U V).obj M) ⟶
      (relativeCechPairFunctor g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)).obj
        ((Scheme.Modules.pullback p).obj M) :=
    (relativeCechPairBaseChangeNatTrans s b p g h.w U V).app M
  let βoverlap : F.obj ((relativeOpenPushforward s (U ⊓ V)).obj M) ⟶
      (relativeOpenPushforward g ((p ⁻¹ᵁ U) ⊓ (p ⁻¹ᵁ V))).obj
        ((Scheme.Modules.pullback p).obj M) :=
    (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app M
  let _ : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback b) :=
    (Scheme.Modules.pullbackPushforwardAdjunction b).leftAdjoint_preservesColimits
  exact
    inv (cokernelComparison d F) ≫ cokernel.map (F.map d) d' βpair βoverlap
        (by
          exact (relativeCechFromPair_baseChange s b p g h.w U V M).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel base-change map commutes with the canonical Čech projection. -/
lemma relativeCechCokernelBaseChangeMap_π
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) (M : X.Modules) (U V : X.Opens) :
    (Scheme.Modules.pullback b).map (cokernel.π (relativeCechFromPair s M U V)) ≫
        relativeCechCokernelBaseChangeMap s b p g h M U V =
      (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app M ≫
        cokernel.π (relativeCechFromPair g ((Scheme.Modules.pullback p).obj M)
          (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)) := by
  let F := Scheme.Modules.pullback b
  let d := relativeCechFromPair s M U V
  let d' := relativeCechFromPair g ((Scheme.Modules.pullback p).obj M)
    (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
  let βpair : F.obj ((relativeCechPairFunctor s U V).obj M) ⟶
      (relativeCechPairFunctor g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)).obj
        ((Scheme.Modules.pullback p).obj M) :=
    (relativeCechPairBaseChangeNatTrans s b p g h.w U V).app M
  let βoverlap : F.obj ((relativeOpenPushforward s (U ⊓ V)).obj M) ⟶
      (relativeOpenPushforward g ((p ⁻¹ᵁ U) ⊓ (p ⁻¹ᵁ V))).obj
        ((Scheme.Modules.pullback p).obj M) :=
    (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app M
  let hsq : F.map d ≫ βoverlap = βpair ≫ d' := by
    exact (relativeCechFromPair_baseChange s b p g h.w U V M).symm
  let _ : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback b) :=
    (Scheme.Modules.pullbackPushforwardAdjunction b).leftAdjoint_preservesColimits
  change F.map (cokernel.π d) ≫
      inv (cokernelComparison d F) ≫
        cokernel.map (F.map d) d' βpair βoverlap hsq =
    βoverlap ≫ cokernel.π d'
  rw [← Category.assoc, ← π_comp_cokernelComparison]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact cokernel.π_desc (F.map d) (βoverlap ≫ cokernel.π d')
    (by rw [← Category.assoc, hsq]; simp)

set_option backward.isDefEq.respectTransparency false in
/-- The relative Čech cokernel map is invertible when the three open maps are. -/
lemma relativeCechCokernelBaseChangeMap_isIso
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) (M : X.Modules) (U V : X.Opens)
    [M.IsQuasicoherent]
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)]
    [IsAffineHom ((U ⊓ V).ι ≫ s)] :
    IsIso (relativeCechCokernelBaseChangeMap s b p g h M U V) := by
  let _ : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback b) :=
    (Scheme.Modules.pullbackPushforwardAdjunction b).leftAdjoint_preservesColimits
  let _ : IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w U).app M) :=
    relativeOpenBaseChangeNatTrans_isIso s b p g h U M
  let _ : IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w V).app M) :=
    relativeOpenBaseChangeNatTrans_isIso s b p g h V M
  let _ : IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app M) :=
    relativeOpenBaseChangeNatTrans_isIso s b p g h (U ⊓ V) M
  let _ : IsIso ((relativeCechPairBaseChangeNatTrans s b p g h.w U V).app M) :=
    relativeCechPairBaseChangeNatTrans_isIso s b p g h.w U V M
  dsimp only [relativeCechCokernelBaseChangeMap]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The specified-cover comparison transported to first higher direct images.
The construction assumes local Noetherianity on both schemes and affine
composites for the chosen source opens; the target affine composites are
obtained from the restricted pullback square. -/
def relativeCechHigherBaseChangeMap
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) (M : X.Modules)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [M.IsQuasicoherent]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] :
    (Scheme.Modules.pullback b).obj (higherDirectImageModule s M 1) ⟶
      higherDirectImageModule g ((Scheme.Modules.pullback p).obj M) 1 := by
  let hU := (isPullback_morphismRestrict p U).paste_vert h
  let hV := (isPullback_morphismRestrict p V).paste_vert h
  let _ : IsAffineHom ((p ⁻¹ᵁ U).ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hU inferInstance
  let _ : IsAffineHom ((p ⁻¹ᵁ V).ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hV inferInstance
  have hcover' : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  let eSource := relativeCechCokernelIsoHigherDirectImageOne s M U V hcover
  let eTarget := relativeCechCokernelIsoHigherDirectImageOne g
    ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hcover'
  exact (Scheme.Modules.pullback b).map eSource.inv ≫
    relativeCechCokernelBaseChangeMap s b p g h M U V ≫ eTarget.hom

set_option backward.isDefEq.respectTransparency false in
/-- The higher-direct-image comparison is invertible when the source cover has
affine open composites and affine overlap.  The overlap-affine hypothesis is
needed only for this invertibility statement. -/
lemma relativeCechHigherBaseChangeMap_isIso
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) (M : X.Modules)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [M.IsQuasicoherent]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)]
    [IsAffineHom ((U ⊓ V).ι ≫ s)] :
    IsIso (relativeCechHigherBaseChangeMap s b p g h M U V hcover) := by
  let hU := (isPullback_morphismRestrict p U).paste_vert h
  let hV := (isPullback_morphismRestrict p V).paste_vert h
  let _ : IsAffineHom ((p ⁻¹ᵁ U).ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hU inferInstance
  let _ : IsAffineHom ((p ⁻¹ᵁ V).ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hV inferInstance
  have hcover' : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  have hcoker : IsIso (relativeCechCokernelBaseChangeMap s b p g h M U V) :=
    relativeCechCokernelBaseChangeMap_isIso s b p g h M U V
  dsimp only [relativeCechHigherBaseChangeMap]
  infer_instance

end GromovWitten.AlgebraicGeometry.Curves
