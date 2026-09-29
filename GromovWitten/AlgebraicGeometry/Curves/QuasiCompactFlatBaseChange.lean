/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteAffineCanonicalBaseChange
import GromovWitten.AlgebraicGeometry.Curves.HigherBaseChangeIsomorphism
import GromovWitten.AlgebraicGeometry.Curves.FlasqueComplexBaseChange
import GromovWitten.AlgebraicGeometry.Curves.ModuleComplexLocality
import GromovWitten.AlgebraicGeometry.Curves.ModuleComplexBaseChangeCongr
import GromovWitten.AlgebraicGeometry.Curves.ModuleComplexBaseChangePasting
import GromovWitten.AlgebraicGeometry.Curves.ModuleComplexOpenBaseChange
import GromovWitten.AlgebraicGeometry.Curves.HigherOpenBaseChange

/-!
# Flat base change for quasi-compact separated morphisms

The canonical higher direct-image comparison is invertible under flat base change
for quasicoherent coefficients, assuming the total spaces before and after base
change are locally Noetherian. The old and new bases are arbitrary schemes.
The proof localizes the finite affine-cover comparison by pasting complex maps
and comparing flasque resolutions.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
open Scheme.Modules
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Flat base change is an isomorphism in every degree for a quasi-compact
separated morphism with quasicoherent coefficients and locally Noetherian total
spaces before and after base change. The old and new bases are arbitrary. -/
theorem moduleFlatHigherBaseChange_isIso_of_quasiCompact_separated
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) [Flat b] [QuasiCompact s] [IsSeparated s]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso ((moduleFlatHigherBaseChangeNatTrans s b p g h n).app M) := by
  let _ : Flat p := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  let Q := Scheme.Modules.pushforward s
  let F := Scheme.Modules.pullback b
  let L := Scheme.Modules.pullback p
  let P := Scheme.Modules.pushforward g
  let I := injectiveResolution M
  let J := injectiveResolution (L.obj M)
  let d : (CochainComplex.single₀ Y.Modules).obj (L.obj M) ⟶
      (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
    (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι
  have hd : QuasiIso d := by dsimp [d]; infer_instance
  obtain ⟨φ, hφ, hφiso⟩ := J.exists_desc_of_quasiIso d
  let _ : QuasiIso φ := hφiso
  have hφ' : (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι ≫ φ = J.ι := by
    simpa only [d, Category.assoc] using hφ
  let Γ := NatTrans.complexBaseChangeMap Q F L P
    (modulePushforwardBaseChangeNatTrans s b p g h) φ
  have hΓ : QuasiIso Γ := by
    apply moduleComplex_quasiIso_of_open_pullbacks Γ
    intro t
    obtain ⟨U, hU, htU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
      (x := b t) (by simp)
    let V : T.Opens := b ⁻¹ᵁ U
    have htV : t ∈ V := htU
    let aU : X.Opens := s ⁻¹ᵁ U
    let qV : Y.Opens := g ⁻¹ᵁ V
    have hVU : V ≤ b ⁻¹ᵁ U := le_rfl
    have hWU : qV ≤ p ⁻¹ᵁ aU := by
      change (g ≫ b) ⁻¹ᵁ U ≤ (p ≫ s) ⁻¹ᵁ U
      rw [h.w]
    let bU : V.toScheme ⟶ U.toScheme := b.resLE U V hVU
    let pU : qV.toScheme ⟶ aU.toScheme := p.resLE aU qV hWU
    let sU : aU.toScheme ⟶ U.toScheme := s ∣_ U
    let kU : qV.toScheme ⟶ V.toScheme := g ∣_ V
    have hB : bU ≫ U.ι = V.ι ≫ b := b.resLE_comp_ι hVU
    have hP : pU ≫ aU.ι = qV.ι ≫ p := p.resLE_comp_ι hWU
    have hLocal : IsPullback pU kU sU bU := by
      dsimp only [pU, kU, sU, bU]
      simpa only [Scheme.Hom.resLE_eq_morphismRestrict, aU, qV, V] using
        Scheme.Hom.isPullback_resLE h hVU le_rfl
          (show qV = p ⁻¹ᵁ aU ⊓ qV from (inf_eq_right.mpr hWU).symm)
    let _ : IsAffine U.toScheme := hU
    let _ : CompactSpace aU.toScheme :=
      QuasiCompact.compactSpace_of_compactSpace (s ∣_ U)
    let _ : aU.toScheme.IsSeparated := by
      constructor
      rw [← terminal.comp_from (s ∣_ U)]
      infer_instance
    let _ : IsLocallyNoetherian aU.toScheme := inferInstance
    let _ : IsLocallyNoetherian qV.toScheme := inferInstance
    let _ : Flat bU := inferInstance
    let _ : Flat pU := MorphismProperty.of_isPullback (P := @Flat)
      hLocal.flip inferInstance
    let Mu := (Scheme.Modules.pullback aU.ι).obj M
    let Ku := ((Scheme.Modules.pullback aU.ι).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    let Ju := ((Scheme.Modules.pullback qV.ι).mapHomologicalComplex (.up ℕ)).obj J.cocomplex
    let au : (CochainComplex.single₀ aU.toScheme.Modules).obj Mu ⟶ Ku :=
      (singleMapHomologicalComplex (Scheme.Modules.pullback aU.ι) (.up ℕ) 0).inv.app M ≫
        ((Scheme.Modules.pullback aU.ι).mapHomologicalComplex (.up ℕ)).map I.ι
    have hau : QuasiIso au := by
      dsimp only [au]
      infer_instance
    let ξ :
        ((Scheme.Modules.pullback pU).mapHomologicalComplex (.up ℕ)).obj Ku ≅
          ((Scheme.Modules.pullback qV.ι).mapHomologicalComplex (.up ℕ)).obj
            (((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) :=
      (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp pU aU.ι) (.up ℕ)).app
          I.cocomplex ≪≫
        (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackCongr hP) (.up ℕ)).app
          I.cocomplex ≪≫
        ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp qV.ι p) (.up ℕ)).app
          I.cocomplex).symm
    let φu :
        ((Scheme.Modules.pullback pU).mapHomologicalComplex (.up ℕ)).obj Ku ⟶ Ju :=
      ξ.hom ≫ ((Scheme.Modules.pullback qV.ι).mapHomologicalComplex (.up ℕ)).map φ
    have hφu : QuasiIso φu := by
      dsimp only [φu]
      infer_instance
    have hK : ∀ m, TopCat.Sheaf.IsFlasque
        ((moduleToSheafAb aU.toScheme).obj (Ku.X m)) := by
      intro m
      dsimp only [Ku]
      exact modulePullback_isFlasque aU.ι (I.cocomplex.X m)
    have hJ : ∀ m, TopCat.Sheaf.IsFlasque
        ((moduleToSheafAb qV.toScheme).obj (Ju.X m)) := by
      intro m
      dsimp only [Ju]
      exact modulePullback_isFlasque qV.ι (J.cocomplex.X m)
    have hBC : ∀ m, IsIso
        ((moduleHigherBaseChangeNatTrans sU bU pU kU hLocal m).app Mu) := by
      intro m
      exact moduleFlatHigherBaseChange_isIso_of_compactSource
        sU bU pU kU hLocal Mu m
    have hlocal : QuasiIso (NatTrans.complexBaseChangeMap
        (Scheme.Modules.pushforward sU) (Scheme.Modules.pullback bU)
        (Scheme.Modules.pullback pU) (Scheme.Modules.pushforward kU)
        (modulePushforwardBaseChangeNatTrans sU bU pU kU hLocal) φu) := by
      exact moduleComplexBaseChange_quasiIso_of_flasque_of_quasiIso
        sU bU pU kU hLocal Mu au φu hK hJ hBC
    let βopen := NatTrans.complexBaseChangeMap
      (Scheme.Modules.pushforward s) (Scheme.Modules.pullback U.ι)
      (Scheme.Modules.pullback aU.ι) (Scheme.Modules.pushforward sU)
      (modulePushforwardBaseChangeNatTrans s U.ι aU.ι sU
        (isPullback_morphismRestrict s U).flip) (K := I.cocomplex)
      (J := Ku) (𝟙 _)
    have hβopen : IsIso βopen := by
      exact moduleComplexBaseChange_open_isIso s U (K := I.cocomplex)
    let φout :
        ((Scheme.Modules.pullback (qV.ι ≫ p)).mapHomologicalComplex (.up ℕ)).obj
            I.cocomplex ⟶ Ju :=
      (NatIso.mapHomologicalComplex
          (Scheme.Modules.pullbackComp qV.ι p) (.up ℕ)).inv.app I.cocomplex ≫
        ((Scheme.Modules.pullback qV.ι).mapHomologicalComplex (.up ℕ)).map φ
    let hOuter : IsPullback (qV.ι ≫ p) kU s (V.ι ≫ b) :=
      (isPullback_morphismRestrict g V).flip.paste_horiz h
    have hOuterLocal : IsPullback (pU ≫ aU.ι) kU s (bU ≫ U.ι) :=
      hLocal.paste_horiz ((isPullback_morphismRestrict s U).flip)
    let _ : IsIso βopen := hβopen
    have hforward := moduleComplexBaseChange_pasting_quasiIso_outer
      s U.ι aU.ι sU bU pU kU
      ((isPullback_morphismRestrict s U).flip) hLocal (𝟙 _) φu
    let βouter := NatTrans.complexBaseChangeMap
      (Scheme.Modules.pushforward s) (Scheme.Modules.pullback (V.ι ≫ b))
      (Scheme.Modules.pullback (qV.ι ≫ p)) (Scheme.Modules.pushforward kU)
      (modulePushforwardBaseChangeNatTrans s (V.ι ≫ b) (qV.ι ≫ p) kU hOuter)
      φout
    have hcoef :
        (NatIso.mapHomologicalComplex
          (Scheme.Modules.pullbackComp pU aU.ι) (.up ℕ)).inv.app I.cocomplex ≫
          ((Scheme.Modules.pullback pU).mapHomologicalComplex (.up ℕ)).map
            (𝟙 Ku) ≫ φu =
        (NatIso.mapHomologicalComplex
          (Scheme.Modules.pullbackCongr hP) (.up ℕ)).hom.app I.cocomplex ≫ φout := by
      let eA := (NatIso.mapHomologicalComplex
        (Scheme.Modules.pullbackComp pU aU.ι) (.up ℕ)).app I.cocomplex
      let eP := (NatIso.mapHomologicalComplex
        (Scheme.Modules.pullbackCongr hP) (.up ℕ)).app I.cocomplex
      let eQ := (NatIso.mapHomologicalComplex
        (Scheme.Modules.pullbackComp qV.ι p) (.up ℕ)).app I.cocomplex
      rw [((Scheme.Modules.pullback pU).mapHomologicalComplex (.up ℕ)).map_id]
      change eA.inv ≫ 𝟙 _ ≫ (eA.hom ≫ eP.hom ≫ eQ.inv) ≫ _ =
        eP.hom ≫ eQ.inv ≫ _
      simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc]
    have hforward' : QuasiIso βouter := by
      apply (moduleComplexBaseChange_quasiIso_congr_iff
        s (bU ≫ U.ι) (pU ≫ aU.ι) kU hOuterLocal
        (V.ι ≫ b) (qV.ι ≫ p) hB hP hOuter φout).mp
      dsimp only at hforward
      rw [hcoef] at hforward
      exact hforward
    have hopen : IsIso (NatTrans.complexBaseChangeMap
        (Scheme.Modules.pushforward g) (Scheme.Modules.pullback V.ι)
        (Scheme.Modules.pullback qV.ι) (Scheme.Modules.pushforward kU)
        (modulePushforwardBaseChangeNatTrans g V.ι qV.ι kU
          (isPullback_morphismRestrict g V).flip) (K := J.cocomplex) (𝟙 _)) := by
      exact moduleComplexBaseChange_open_isIso g V (K := J.cocomplex)
    have hreverse : QuasiIso
        (((Scheme.Modules.pullback V.ι).mapHomologicalComplex (.up ℕ)).map Γ) := by
      let _ : QuasiIso βouter := hforward'
      let _ : QuasiIso
          (NatTrans.complexBaseChangeMap
            (Scheme.Modules.pushforward s) (Scheme.Modules.pullback (V.ι ≫ b))
            (Scheme.Modules.pullback (qV.ι ≫ p)) (Scheme.Modules.pushforward kU)
            (modulePushforwardBaseChangeNatTrans s (V.ι ≫ b) (qV.ι ≫ p) kU hOuter)
            ((NatIso.mapHomologicalComplex
              (Scheme.Modules.pullbackComp qV.ι p) (.up ℕ)).inv.app I.cocomplex ≫
                ((Scheme.Modules.pullback qV.ι).mapHomologicalComplex (.up ℕ)).map φ ≫
                  𝟙 Ju)) := by
        simpa only [βouter, φout, Ju, Category.comp_id] using hforward'
      let _ : QuasiIso (NatTrans.complexBaseChangeMap
          (Scheme.Modules.pushforward g) (Scheme.Modules.pullback V.ι)
          (Scheme.Modules.pullback qV.ι) (Scheme.Modules.pushforward kU)
          (modulePushforwardBaseChangeNatTrans g V.ι qV.ι kU
            (isPullback_morphismRestrict g V).flip) (K := J.cocomplex) (𝟙 _)) := by
        let _ : IsIso (NatTrans.complexBaseChangeMap
            (Scheme.Modules.pushforward g) (Scheme.Modules.pullback V.ι)
            (Scheme.Modules.pullback qV.ι) (Scheme.Modules.pushforward kU)
            (modulePushforwardBaseChangeNatTrans g V.ι qV.ι kU
              (isPullback_morphismRestrict g V).flip) (K := J.cocomplex) (𝟙 _)) := hopen
        infer_instance
      exact moduleComplexBaseChange_pasting_quasiIso_inner
        s b p g V.ι qV.ι kU h (isPullback_morphismRestrict g V).flip φ (𝟙 _)
    exact ⟨V, htV, hreverse⟩
  exact (NatTrans.rightDerivedBaseChange_isIso_iff
    (modulePushforwardBaseChangeNatTrans s b p g h) M n φ hφ').mpr
    (by
      have : QuasiIso Γ := hΓ
      change IsIso (homologyMap Γ n)
      infer_instance)

end GromovWitten.AlgebraicGeometry.Curves
