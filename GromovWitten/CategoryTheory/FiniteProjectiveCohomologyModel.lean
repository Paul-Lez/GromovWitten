/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.FiniteFlatTwoTerm
import GromovWitten.CategoryTheory.BoundedFlatComplex
import GromovWitten.CategoryTheory.ScalarHomologyBaseChange
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Finite projective models for the first two cohomology modules

A bounded flat integer-indexed complex that is exact in degrees at least two
compresses to one differential. Finite degree-zero and degree-one homology give
that differential finite kernel and cokernel, and the finite flat two-term
replacement then provides a finite projective-to-free model compatible with
arbitrary scalar extension.
-/

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex

noncomputable section
universe u v

namespace CochainComplex
/-- The degree-zero differential with codomain restricted to the next cycle module. -/
noncomputable def bounded_int_flat_compression_d
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    K.X 0 →ₗ[R] LinearMap.ker (K.d 1 2).hom :=
  (K.d 0 1).hom.codRestrict _ (by
    intro x
    change (K.d 1 2).hom ((K.d 0 1).hom x) = 0
    have h := K.d_comp_d 0 1 2
    exact congrArg (fun f : K.X 0 ⟶ K.X 2 => f.hom x) h)

/-- The target of the compression differential is flat under the boundedness hypotheses. -/
lemma bounded_int_flat_compression_d_flat_target
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) [CochainComplex.IsStrictlyGE K 0]
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n) :
    Module.Flat R (LinearMap.ker (K.d 1 2).hom) :=
  bounded_int_exact_flat_cycles_at K hflat N htail hexact 1 (by omega)

/-- The compression differential has the same kernel as the original degree-zero differential. -/
noncomputable def bounded_int_flat_compression_kernel_iso
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    ModuleCat.of R (LinearMap.ker (K.d 0 1).hom) ≅
      ModuleCat.of R (LinearMap.ker (bounded_int_flat_compression_d K)) := by
  have hker : LinearMap.ker (bounded_int_flat_compression_d K) =
      LinearMap.ker (K.d 0 1).hom := by
    simp [bounded_int_flat_compression_d, LinearMap.ker_codRestrict]
  exact (LinearEquiv.ofEq _ _ hker.symm).toModuleIso

/-- For a complex strictly supported in nonnegative degrees, its degree-zero homology is the
kernel of the compression differential. -/
noncomputable def bounded_int_flat_compression_kernel_homology_iso
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ)
    [CochainComplex.IsStrictlyGE K 0] :
    K.homology 0 ≅ ModuleCat.of R
      (LinearMap.ker (bounded_int_flat_compression_d K)) := by
  let S := K.sc' (-1 : ℤ) 0 1
  have hprevZero : IsZero (K.X (-1 : ℤ)) :=
    CochainComplex.isZero_of_isStrictlyGE K 0 (-1) (by omega)
  have hsource : Subsingleton S.X₁ :=
    (ModuleCat.isZero_iff_subsingleton).mp hprevZero
  have hmap : S.moduleCatToCycles = 0 := by
    ext x
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx]
  have hrange : LinearMap.range S.moduleCatToCycles = ⊥ := by
    rw [hmap]
    simp
  have hnext : (ComplexShape.up ℤ).next (0 : ℤ) = 1 := by
    apply (ComplexShape.up ℤ).next_eq'
    exact ComplexShape.up_mk _ _ (by norm_num)
  have hprev : (ComplexShape.up ℤ).prev (0 : ℤ) = -1 := by
    apply (ComplexShape.up ℤ).prev_eq'
    exact ComplexShape.up_mk _ _ (by norm_num)
  have hsc := K.homologyIsoSc' (-1 : ℤ) 0 1 hprev hnext
  let hquot : S.moduleCatLeftHomologyData.H ≅
      ModuleCat.of R (LinearMap.ker (K.d 0 1).hom) :=
    (Submodule.quotEquivOfEqBot _ hrange).toModuleIso
  exact hsc ≪≫ S.moduleCatHomologyIso ≪≫ hquot ≪≫
    bounded_int_flat_compression_kernel_iso K

/-- The cokernel of the compression differential is the degree-one homology. -/
noncomputable def bounded_int_flat_compression_cokernel_homology_iso
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    cokernel (ModuleCat.ofHom (bounded_int_flat_compression_d K)) ≅
      K.homology 1 := by
  let S := K.sc' (0 : ℤ) 1 2
  have hmap : S.moduleCatToCycles = bounded_int_flat_compression_d K := by
    ext x
    rfl
  have hrange : LinearMap.range (bounded_int_flat_compression_d K) =
      LinearMap.range S.moduleCatToCycles := by
    exact (congrArg LinearMap.range hmap).symm
  let hquot : ModuleCat.of R
      (LinearMap.ker (K.d 1 2).hom ⧸
        LinearMap.range (bounded_int_flat_compression_d K)) ≅
      S.moduleCatLeftHomologyData.H :=
    (Submodule.quotEquivOfEq _ _ hrange).toModuleIso
  have hprev : (ComplexShape.up ℤ).prev (1 : ℤ) = 0 := by
    apply (ComplexShape.up ℤ).prev_eq'
    exact ComplexShape.up_mk _ _ (by norm_num)
  have hnext : (ComplexShape.up ℤ).next (1 : ℤ) = 2 := by
    apply (ComplexShape.up ℤ).next_eq'
    exact ComplexShape.up_mk _ _ (by norm_num)
  have hsc := K.homologyIsoSc' (0 : ℤ) 1 2 hprev hnext
  exact ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom
      (bounded_int_flat_compression_d K)) ≪≫ hquot ≪≫
    S.moduleCatHomologyIso.symm ≪≫ hsc.symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def linearKernelComparisonIso
    {R T : Type u} [CommRing R] [CommRing T] (σ : R →+* T)
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    [IsIso (kernelComparison f (ModuleCat.extendScalars σ))] :
    (ModuleCat.extendScalars σ).obj (ModuleCat.of R (LinearMap.ker f.hom)) ≅
      ModuleCat.of T
        (LinearMap.ker ((ModuleCat.extendScalars σ).map f).hom) :=
  ((ModuleCat.extendScalars σ).mapIso (ModuleCat.kernelIsoKer f)).symm ≪≫
    asIso (kernelComparison f (ModuleCat.extendScalars σ)) ≪≫
    ModuleCat.kernelIsoKer ((ModuleCat.extendScalars σ).map f)

set_option backward.isDefEq.respectTransparency false in
private lemma linearKernelComparisonIso_subtype
    {R T : Type u} [CommRing R] [CommRing T] (σ : R →+* T)
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    [IsIso (kernelComparison f (ModuleCat.extendScalars σ))] :
    (linearKernelComparisonIso σ f).hom ≫
        ModuleCat.ofHom
          (LinearMap.ker ((ModuleCat.extendScalars σ).map f).hom).subtype =
      (ModuleCat.extendScalars σ).map
        (ModuleCat.ofHom (LinearMap.ker f.hom).subtype) := by
  dsimp only [linearKernelComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, asIso_hom]
  rw [Category.assoc, Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
    kernelComparison_comp_ι, ← Functor.map_comp,
    ModuleCat.kernelIsoKer_inv_kernel_ι]

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the compression differential after any scalar extension is degree-zero
homology of the extended complex. This statement does not require flatness on the degree-one
homology module. -/
noncomputable def bounded_int_flat_compression_baseChange_h0Iso
    {R T : Type u} [CommRing R] [CommRing T] (σ : R →+* T)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    [CochainComplex.IsStrictlyGE K 0]
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n) :
    ModuleCat.of T (LinearMap.ker
      ((ModuleCat.extendScalars σ).map
        (ModuleCat.ofHom (bounded_int_flat_compression_d K))).hom) ≅
      ((((ModuleCat.extendScalars σ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology 0) := by
  letI : Algebra R T := σ.toAlgebra
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} T := ModuleCat.extendScalars σ
  let L : CochainComplex (ModuleCat.{u} T) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hstrictL : CochainComplex.IsStrictlyGE L 0 := by
    apply (CochainComplex.isStrictlyGE_iff L 0).2
    intro i hi
    exact Functor.map_isZero F (K.isZero_of_isStrictlyGE 0 i hi)
  letI : CochainComplex.IsStrictlyGE L 0 := hstrictL
  let gK : K.X 0 ⟶ ModuleCat.of R (LinearMap.ker (K.d 1 2).hom) :=
    ModuleCat.ofHom (bounded_int_flat_compression_d K)
  have hcmp : IsIso (kernelComparison (K.d 1 2) F) := by
    rw [← bounded_int_d1_kernelComparisonIso_hom σ K hflat N htail hexact]
    infer_instance
  letI : IsIso (kernelComparison (K.d 1 2) F) := hcmp
  let κ := linearKernelComparisonIso σ (K.d 1 2)
  let fF := F.map (K.d 1 2)
  have hzero : F.map (K.d 0 1) ≫ fF = 0 := by
    rw [← F.map_comp, K.d_comp_d]
    exact F.map_zero _ _
  let gF : F.obj (K.X 0) ⟶ ModuleCat.of T (LinearMap.ker fF.hom) :=
    kernel.lift fF (F.map (K.d 0 1)) hzero ≫ (ModuleCat.kernelIsoKer fF).hom
  have hκsub := linearKernelComparisonIso_subtype σ (K.d 1 2)
  have hfactorK : gK ≫
      ModuleCat.ofHom (LinearMap.ker (K.d 1 2).hom).subtype = K.d 0 1 := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  have hfactorF : gF ≫ ModuleCat.ofHom (LinearMap.ker fF.hom).subtype =
      F.map (K.d 0 1) := by
    dsimp [gF]
    simp only [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype, kernel.lift_ι]
  have hcomm : F.map gK ≫ κ.hom = gF := by
    apply (cancel_mono (ModuleCat.ofHom (LinearMap.ker fF.hom).subtype)).mp
    calc
      F.map gK ≫ κ.hom ≫ ModuleCat.ofHom (LinearMap.ker fF.hom).subtype =
          F.map (gK ≫ ModuleCat.ofHom (LinearMap.ker (K.d 1 2).hom).subtype) := by
        rw [hκsub, ← F.map_comp]
      _ = F.map (K.d 0 1) := by rw [hfactorK]
      _ = gF ≫ ModuleCat.ofHom (LinearMap.ker fF.hom).subtype := by rw [hfactorF]
  let eker := kernel.mapIso (F.map gK) gF (Iso.refl _) κ hcomm
  have hgF : gF.hom = bounded_int_flat_compression_d L := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx0 : (gF.hom x).val = (F.map (K.d 0 1)).hom x := by
      have hh := congrArg (fun f => f.hom x) hfactorF
      change (gF.hom x).val = (F.map (K.d 0 1)).hom x at hh
      exact hh
    change (gF.hom x).val = (bounded_int_flat_compression_d L x).val
    rw [hx0]
    rfl
  exact (ModuleCat.kernelIsoKer (F.map gK)).symm ≪≫ eker ≪≫
    ModuleCat.kernelIsoKer gF ≪≫
    (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hgF)).toModuleIso ≪≫
      (bounded_int_flat_compression_kernel_homology_iso L).symm

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel of the compression differential after any scalar extension is degree-one
homology of the extended complex. -/
noncomputable def bounded_int_flat_compression_baseChange_h1Iso
    {R T : Type u} [CommRing R] [CommRing T] (σ : R →+* T)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n) :
    cokernel ((ModuleCat.extendScalars σ).map
      (ModuleCat.ofHom (bounded_int_flat_compression_d K))) ≅
      (((ModuleCat.extendScalars σ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology 1 := by
  letI : Algebra R T := σ.toAlgebra
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} T := ModuleCat.extendScalars σ
  let L : CochainComplex (ModuleCat.{u} T) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let gK : K.X 0 ⟶ ModuleCat.of R (LinearMap.ker (K.d 1 2).hom) :=
    ModuleCat.ofHom (bounded_int_flat_compression_d K)
  have hcmp := bounded_int_positive_homologyComparison_isIso σ K hflat N htail
    hexact 1 (by omega)
  letI : IsIso (K.homologyComparison F (1 : ℤ)) := hcmp
  exact (PreservesCokernel.iso F gK).symm ≪≫
    F.mapIso (bounded_int_flat_compression_cokernel_homology_iso K) ≪≫
    asIso (K.homologyComparison F (1 : ℤ))
attribute [local instance] ModuleCat.hasKernels_moduleCat
attribute [local instance] ModuleCat.hasCokernels_moduleCat

/-- A bounded flat complex exact in degrees at least two has a universal
finite projective-to-free two-term model for its first two homology modules.
The kernel and cokernel of the extended model differential are canonically
the degree-zero and degree-one homology after every scalar extension. -/
theorem exists_bounded_int_finiteProjective_finiteFree_twoTerm_model
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    [CochainComplex.IsStrictlyGE K 0]
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n)
    (hfinite0 : Module.Finite R (K.homology 0 : ModuleCat R))
    (hfinite1 : Module.Finite R (K.homology 1 : ModuleCat R)) :
    let d := bounded_int_flat_compression_d K
    ∃ (n : ℕ) (q : (Fin n → R) →ₗ[R] LinearMap.ker (K.d 1 2).hom),
      Function.Surjective ((LinearMap.range d).mkQ.comp q) ∧
      Module.Finite R (LinearMap.ker (LinearMap.finiteFlatTwoTermMap d q)) ∧
      Module.Projective R (LinearMap.ker (LinearMap.finiteFlatTwoTermMap d q)) ∧
      ∀ {T : Type u} [CommRing T] (σ : R →+* T),
        Nonempty (ModuleCat.of T (LinearMap.ker
          ((ModuleCat.extendScalars σ).map
            (ModuleCat.ofHom (LinearMap.finiteFlatTwoTermDifferential d q))).hom) ≅
            (((ModuleCat.extendScalars σ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K).homology 0) ∧
        Nonempty (cokernel ((ModuleCat.extendScalars σ).map
          (ModuleCat.ofHom (LinearMap.finiteFlatTwoTermDifferential d q))) ≅
            (((ModuleCat.extendScalars σ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K).homology 1) := by
  classical
  let d := bounded_int_flat_compression_d K
  have hkerIso := bounded_int_flat_compression_kernel_homology_iso K
  have hkerFinite : Module.Finite R (LinearMap.ker d) := by
    have : Module.Finite R (K.homology 0 : ModuleCat R) := hfinite0
    exact Module.Finite.of_surjective hkerIso.toLinearEquiv.toLinearMap
      hkerIso.toLinearEquiv.surjective
  let c := cokernel (ModuleCat.ofHom d)
  have hcokerIso := bounded_int_flat_compression_cokernel_homology_iso K
  have hcokerFinite : Module.Finite R (c : ModuleCat R) := by
    have : Module.Finite R (K.homology 1 : ModuleCat R) := hfinite1
    exact Module.Finite.of_surjective hcokerIso.symm.toLinearEquiv.toLinearMap
      hcokerIso.symm.toLinearEquiv.surjective
  have hquotFinite : Module.Finite R
      ((LinearMap.ker (K.d 1 2).hom) ⧸ LinearMap.range d) := by
    have : Module.Finite R (c : ModuleCat R) := hcokerFinite
    exact Module.Finite.of_surjective
      (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom d)).toLinearEquiv.toLinearMap
      (ModuleCat.cokernelIsoRangeQuotient
        (ModuleCat.ofHom d)).toLinearEquiv.surjective
  have : Module.Flat R (K.X 0) := hflat 0
  have : Module.Flat R (LinearMap.ker (K.d 1 2).hom) :=
    bounded_int_flat_compression_d_flat_target K hflat N htail hexact
  have : Module.Finite R (LinearMap.ker d) := hkerFinite
  have : Module.Finite R
      ((LinearMap.ker (K.d 1 2).hom) ⧸ LinearMap.range d) := hquotFinite
  obtain ⟨n, q, hq, _, hfinite, hprojective⟩ :=
    LinearMap.exists_finiteFlatTwoTerm d
  refine ⟨n, q, hq, hfinite, hprojective, ?_⟩
  intro T _ σ
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} T := ModuleCat.extendScalars σ
  let p := ModuleCat.ofHom (LinearMap.finiteFlatTwoTermDifferential d q)
  let a := ModuleCat.ofHom (LinearMap.finiteFlatTwoTermLeft d q)
  let qcat := ModuleCat.ofHom q
  let dcat := ModuleCat.ofHom d
  have : Module.Flat R (LinearMap.ker (K.d 1 2).hom) :=
    bounded_int_flat_compression_d_flat_target K hflat N htail hexact
  let hpull := LinearMap.finiteFlatTwoTerm_extendScalars_isPullback σ d q hq
  have hkernelMap : IsIso (kernel.map (F.map p) (F.map dcat) (F.map a)
      (F.map qcat) hpull.w) :=
    LinearMap.finiteFlatTwoTerm_extendScalars_kernel_map_isIso σ d q hq
  let kernelModelIso : ModuleCat.of T (LinearMap.ker (F.map p).hom) ≅
      (((ModuleCat.extendScalars σ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology 0 :=
    (ModuleCat.kernelIsoKer (F.map p)).symm ≪≫
      asIso (kernel.map (F.map p) (F.map dcat) (F.map a) (F.map qcat) hpull.w) ≪≫
      ModuleCat.kernelIsoKer (F.map dcat) ≪≫
      bounded_int_flat_compression_baseChange_h0Iso σ K hflat N htail hexact
  let hpush := (LinearMap.finiteFlatTwoTerm_isPushout d q hq).map F
  have hcokernelMap : IsIso (cokernel.map (F.map p) (F.map dcat) (F.map a)
      (F.map qcat) hpush.w) :=
    LinearMap.finiteFlatTwoTerm_extendScalars_cokernel_map_isIso σ d q hq
  let cokernelModelIso : cokernel (F.map p) ≅ cokernel (F.map dcat) :=
    asIso (cokernel.map (F.map p) (F.map dcat) (F.map a) (F.map qcat) hpush.w)
  exact ⟨⟨kernelModelIso⟩,
    ⟨cokernelModelIso ≪≫
      bounded_int_flat_compression_baseChange_h1Iso σ K hflat N htail hexact⟩⟩

end CochainComplex
