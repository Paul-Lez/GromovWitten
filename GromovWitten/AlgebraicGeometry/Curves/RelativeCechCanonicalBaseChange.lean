/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechCokernelBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechConnectingBaseChange

/-!
# Relative Čech canonical base change

The intrinsic specified-cover relative Čech comparison is constructed for
arbitrary old and new bases and arbitrary base morphisms.  Its equality with
the canonical derived base-change comparison requires both horizontal
pullback functors to preserve homology; the flat theorem is the corresponding
specialization.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open Scheme.Modules
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S T Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- For a Cartesian square whose horizontal pullback functors preserve
homology, the relative Čech cokernel comparison agrees with the canonical
derived base-change map in degree one. -/
lemma relativeCechCokernelIsoHigherDirectImageOne_baseChange
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (hcover' : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)]
    [IsAffineHom ((p ⁻¹ᵁ U).ι ≫ g)] [IsAffineHom ((p ⁻¹ᵁ V).ι ≫ g)] :
    (Scheme.Modules.pullback b).map
        (relativeCechCokernelIsoHigherDirectImageOne s M U V hcover).hom ≫
      (moduleHigherBaseChangeNatTrans s b p g h 1).app M =
    relativeCechCokernelBaseChangeMap s b p g h M U V ≫
      (relativeCechCokernelIsoHigherDirectImageOne g
        ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hcover').hom := by
  let F := Scheme.Modules.pullback b
  let L := Scheme.Modules.pullback p
  let I := injectiveResolution M
  let J := injectiveResolution (L.obj M)
  let a : (CochainComplex.single₀ Y.Modules).obj (L.obj M) ⟶
      (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
    (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso a := by dsimp only [a]; infer_instance
  obtain ⟨φ, hφ, _⟩ := J.exists_desc_of_quasiIso a
  have hφ' : (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι ≫ φ = J.ι := by
    simpa only [a, Category.assoc] using hφ
  have hs : (relativeCechComplexMV I.cocomplex s U V).ShortExact :=
    relativeCechComplexMV_shortExact I.cocomplex s U V hcover
      (fun n => module_isFlasque_of_injective (I.cocomplex.X n))
  have ht : (relativeCechComplexMV J.cocomplex g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)).ShortExact :=
    relativeCechComplexMV_shortExact J.cocomplex g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hcover'
      (fun n => module_isFlasque_of_injective (J.cocomplex.X n))
  let eS := relativeCechCokernelIsoHigherDirectImageOne s M U V hcover
  let eT := relativeCechCokernelIsoHigherDirectImageOne g
    (L.obj M) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hcover'
  let dS := relativeCechFromPair s M U V
  let dT := relativeCechFromPair g (L.obj M) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
  let β := relativeCechCokernelBaseChangeMap s b p g h M U V
  let α := (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app M
  have hπS := relativeCechCokernelIsoHigherDirectImageOne_π s M I U V hcover hs
  have hπT := relativeCechCokernelIsoHigherDirectImageOne_π
    g (L.obj M) J (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hcover' ht
  have hδ := relativeCechConnecting_baseChange s b p g h M U V hs ht φ hφ'
  have hπβ : F.map (cokernel.π dS) ≫ β = α ≫ cokernel.π dT :=
    relativeCechCokernelBaseChangeMap_π s b p g h M U V
  have : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  apply (cancel_epi (F.map (cokernel.π dS))).mp
  change F.map (cokernel.π dS) ≫ F.map eS.hom ≫
      (moduleHigherBaseChangeNatTrans s b p g h 1).app M =
    F.map (cokernel.π dS) ≫ β ≫ eT.hom
  rw [← F.map_comp_assoc, hπS]
  calc
    _ = α ≫ (relativeOpenPushforward g (p ⁻¹ᵁ U ⊓ p ⁻¹ᵁ V)).toRightDerivedZero.app
        (L.obj M) ≫
        (J.isoRightDerivedObj (relativeOpenPushforward g (p ⁻¹ᵁ U ⊓ p ⁻¹ᵁ V)) 0).hom ≫
        ht.δ 0 1 rfl ≫ (J.isoRightDerivedObj (pushforward g) 1).inv := by
      simpa only [F, L, I, J, α, Scheme.Hom.preimage_inf, Category.assoc] using hδ
    _ = α ≫ cokernel.π dT ≫ eT.hom := by
      simpa only [Category.assoc] using
        congrArg (fun t => α ≫ t) hπT.symm
    _ = F.map (cokernel.π dS) ≫ β ≫ eT.hom := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ eT.hom) hπβ.symm

set_option backward.isDefEq.respectTransparency false in
/-- For a Cartesian square whose horizontal pullback functors preserve
homology, the specified-cover relative Čech degree-one comparison equals the
canonical derived base-change map. -/
lemma relativeCechHigherBaseChangeMap_eq
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] :
    relativeCechHigherBaseChangeMap s b p g h M U V hcover =
      (moduleHigherBaseChangeNatTrans s b p g h 1).app M := by
  let _ : IsAffineHom ((p ⁻¹ᵁ U).ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      ((isPullback_morphismRestrict p U).paste_vert h) inferInstance
  let _ : IsAffineHom ((p ⁻¹ᵁ V).ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      ((isPullback_morphismRestrict p V).paste_vert h) inferInstance
  have hcover' : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  let F := Scheme.Modules.pullback b
  let eS := relativeCechCokernelIsoHigherDirectImageOne s M U V hcover
  have hc := relativeCechCokernelIsoHigherDirectImageOne_baseChange
    s b p g h M U V hcover hcover'
  have hc' := congrArg (fun t => F.map eS.inv ≫ t) hc
  simpa only [relativeCechHigherBaseChangeMap, F, eS, Category.assoc,
    Iso.map_inv_hom_id_assoc] using hc'.symm

/-- Under flat base change, the specified-cover relative Čech degree-one
comparison equals the canonical flat base-change map. -/
lemma relativeCechHigherBaseChangeMap_eq_flat
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) [Flat b]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] :
    relativeCechHigherBaseChangeMap s b p g h M U V hcover =
      (moduleFlatHigherBaseChangeNatTrans s b p g h 1).app M := by
  let _ : Flat p := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  exact relativeCechHigherBaseChangeMap_eq s b p g h M U V hcover

end GromovWitten.AlgebraicGeometry.Curves
