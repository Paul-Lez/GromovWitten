/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.ComplexBaseChangeHomotopy
import GromovWitten.AlgebraicGeometry.Curves.HigherOpenBaseChange

/-!
# Flasque complex base change

This transfers the canonical higher base-change isomorphisms from injective
resolutions to arbitrary flasque resolutions.
-/

open CategoryTheory Limits HomologicalComplex
open _root_.AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A compatible quasi-isomorphism between flasque resolutions induces a
quasi-isomorphism on the generic complex base-change map. -/
lemma moduleComplexBaseChange_quasiIso_of_flasque
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    (M : X.Modules)
    {K : CochainComplex X.Modules ℕ} {J : CochainComplex Y.Modules ℕ}
    (a : (CochainComplex.single₀ X.Modules).obj M ⟶ K) [QuasiIso a]
    (a' : (CochainComplex.single₀ Y.Modules).obj
      ((Scheme.Modules.pullback p).obj M) ⟶ J) [QuasiIso a']
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (hφ : (singleMapHomologicalComplex (Scheme.Modules.pullback p) (.up ℕ) 0).inv.app M ≫
      ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).map a ≫ φ = a')
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (hJ : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb Y).obj (J.X n)))
    (hBC : ∀ n, IsIso ((moduleHigherBaseChangeNatTrans s b p g h n).app M)) :
    QuasiIso (NatTrans.complexBaseChangeMap (Scheme.Modules.pushforward s)
      (Scheme.Modules.pullback b) (Scheme.Modules.pullback p) (Scheme.Modules.pushforward g)
      (modulePushforwardBaseChangeNatTrans s b p g h) φ) := by
  let Q := Scheme.Modules.pushforward s
  let F := Scheme.Modules.pullback b
  let L := Scheme.Modules.pullback p
  let P := Scheme.Modules.pushforward g
  let I := injectiveResolution M
  let I' := injectiveResolution (L.obj M)
  obtain ⟨u, hu, hqu⟩ := I.exists_desc_of_quasiIso a
  obtain ⟨v, hv, hqv⟩ := I'.exists_desc_of_quasiIso a'
  have : QuasiIso u := hqu
  have : QuasiIso v := hqv
  let c : (CochainComplex.single₀ Y.Modules).obj (L.obj M) ⟶
      (L.mapHomologicalComplex (.up ℕ)).obj K :=
    (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map a
  let d : (CochainComplex.single₀ Y.Modules).obj (L.obj M) ⟶
      (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
    (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso c := by dsimp only [c]; infer_instance
  have : QuasiIso d := by dsimp only [d]; infer_instance
  obtain ⟨ψ, hψ, _⟩ := I'.exists_desc_of_quasiIso d
  have hψ' : (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι ≫ ψ = I'.ι := by
    simpa only [d, Category.assoc] using hψ
  have hc : c ≫ (L.mapHomologicalComplex (.up ℕ)).map u = d := by
    dsimp only [c, d]
    rw [Category.assoc, ← Functor.map_comp, hu]
  have hcφ : c ≫ φ = a' := by simpa only [c, Category.assoc] using hφ
  have hcomp : c ≫ ((L.mapHomologicalComplex (.up ℕ)).map u ≫ ψ) =
      c ≫ (φ ≫ v) := by
    rw [← Category.assoc, hc, hψ, ← Category.assoc, hcφ, hv]
  obtain ⟨H⟩ := CochainComplex.nonempty_homotopy_of_precomp_quasiIso_nat c
    ((L.mapHomologicalComplex (.up ℕ)).map u ≫ ψ) (φ ≫ v) hcomp
  have : QuasiIso ((Q.mapHomologicalComplex (.up ℕ)).map u) :=
    modulePushforward_quasiIso_of_flasque s u hK
      (fun n => module_isFlasque_of_injective (I.cocomplex.X n))
  have : QuasiIso ((P.mapHomologicalComplex (.up ℕ)).map v) :=
    modulePushforward_quasiIso_of_flasque g v hJ
      (fun n => module_isFlasque_of_injective (I'.cocomplex.X n))
  have : QuasiIso (NatTrans.complexBaseChangeMap Q F L P
      (modulePushforwardBaseChangeNatTrans s b p g h) ψ) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (NatTrans.rightDerivedBaseChange_isIso_iff
      (modulePushforwardBaseChangeNatTrans s b p g h) M n ψ hψ').mp (hBC n)
  exact NatTrans.complexBaseChangeMap_quasiIso_of_homotopy Q F L P
    (modulePushforwardBaseChangeNatTrans s b p g h) u v φ ψ H

set_option backward.isDefEq.respectTransparency false in
/-- The flasque base-change criterion with the target augmentation chosen from
the coefficient quasi-isomorphism. -/
lemma moduleComplexBaseChange_quasiIso_of_flasque_of_quasiIso
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    (M : X.Modules)
    {K : CochainComplex X.Modules ℕ} {J : CochainComplex Y.Modules ℕ}
    (a : (CochainComplex.single₀ X.Modules).obj M ⟶ K) [QuasiIso a]
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    [QuasiIso φ]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (hJ : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb Y).obj (J.X n)))
    (hBC : ∀ n, IsIso ((moduleHigherBaseChangeNatTrans s b p g h n).app M)) :
    QuasiIso (NatTrans.complexBaseChangeMap (Scheme.Modules.pushforward s)
      (Scheme.Modules.pullback b) (Scheme.Modules.pullback p) (Scheme.Modules.pushforward g)
      (modulePushforwardBaseChangeNatTrans s b p g h) φ) := by
  let L := Scheme.Modules.pullback p
  let a' : (CochainComplex.single₀ Y.Modules).obj (L.obj M) ⟶ J :=
    (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map a ≫ φ
  have : QuasiIso a' := by dsimp only [a']; infer_instance
  exact moduleComplexBaseChange_quasiIso_of_flasque s b p g h M a a' φ rfl hK hJ hBC
end GromovWitten.AlgebraicGeometry.Curves
