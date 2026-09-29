/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.FiniteFreeHomologyLocus
import GromovWitten.AlgebraicGeometry.FiniteProjectiveFibreRank

/-!
# Semicontinuity of fibre homology for finite-projective complexes

Split free covers stabilize a short complex of finite-projective modules to a finite-free
complex. Its fibre homology dimension differs from the original by a locally constant rank.
The finite-free determinantal locus theorem therefore gives upper semicontinuity of the
actual categorical fibre homology dimension.
-/

open CategoryTheory CategoryTheory.ShortComplex
open _root_.AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
open GromovWitten.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Matrix
open GromovWitten.AlgebraicGeometry.FiniteFreeHomologyLocus

namespace GromovWitten.AlgebraicGeometry.FiniteProjectiveHomologyLocus
universe u
noncomputable section
variable {R : Type u} [CommRing R]

private structure FreeSplitCover (M : ModuleCat.{u} R) where
  n : ℕ
  q : (Fin n → R) →ₗ[R] (M : Type u)
  s : (M : Type u) →ₗ[R] (Fin n → R)
  q_surj : Function.Surjective q
  q_section : q.comp s = LinearMap.id

private noncomputable def freeSplitCover (M : ModuleCat.{u} R)
    [Module.Finite R (M : Type u)] [Module.Projective R (M : Type u)] : FreeSplitCover M := by
  let h := Module.Finite.exists_comp_eq_id_of_projective R M
  let n := Classical.choose h
  let h₁ := Classical.choose_spec h
  let q := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let s := Classical.choose h₂
  let h₃ := Classical.choose_spec h₂
  exact ⟨n, q, s, h₃.1, h₃.2.2⟩

private noncomputable def freeBaseChangeBasis (M : ModuleCat.{u} R)
    [Module.Free R (M : Type u)] [Module.Finite R (M : Type u)]
    {K : Type u} [Field K] (f : R →+* K) :
    Module.Basis (Module.Free.ChooseBasisIndex R (M : Type u)) K
      ((ModuleCat.extendScalars f).obj M : Type u) := by
  let _ : Algebra R K := f.toAlgebra
  let b := Module.Free.chooseBasis R (M : Type u)
  change Module.Basis (Module.Free.ChooseBasisIndex R (M : Type u)) K
    (K ⊗[R] (M : Type u))
  exact Algebra.TensorProduct.basis K b

private theorem freeBaseChangeFinite (M : ModuleCat.{u} R)
    [Module.Free R (M : Type u)] [Module.Finite R (M : Type u)]
    {K : Type u} [Field K] (f : R →+* K) :
    Module.Finite K ((ModuleCat.extendScalars f).obj M : Type u) :=
  (freeBaseChangeBasis M f).finiteDimensional_of_finite

private theorem splitCoverBaseChangeFinite (M : ModuleCat.{u} R)
    (P : FreeSplitCover M) {K : Type u} [Field K] (f : R →+* K) :
    Module.Finite K ((ModuleCat.extendScalars f).obj M : Type u) := by
  let _ : Algebra R K := f.toAlgebra
  let E := ModuleCat.extendScalars f
  let hfree : Module.Finite K (E.obj (ModuleCat.of R (Fin P.n → R)) : Type u) :=
    freeBaseChangeFinite (ModuleCat.of R (Fin P.n → R)) f
  have hqs : ModuleCat.ofHom P.s ≫ ModuleCat.ofHom P.q = 𝟙 _ := by
    apply ModuleCat.hom_ext
    change P.q.comp P.s = LinearMap.id
    exact P.q_section
  have hsec' : E.map (ModuleCat.ofHom P.s) ≫ E.map (ModuleCat.ofHom P.q) = 𝟙 _ := by
    rw [← E.map_comp, hqs]
    simp
  have hsec : (E.map (ModuleCat.ofHom P.q)).hom.comp
      (E.map (ModuleCat.ofHom P.s)).hom = LinearMap.id := by
    simpa using congrArg ModuleCat.Hom.hom hsec'
  have hsurj : Function.Surjective (E.map (ModuleCat.ofHom P.q)).hom := by
    intro y
    refine ⟨(E.map (ModuleCat.ofHom P.s)).hom y, ?_⟩
    simpa [LinearMap.comp_apply] using congrArg (fun m => m y) hsec
  exact @Module.Finite.of_surjective
    K (E.obj (ModuleCat.of R (Fin P.n → R)) : Type u) _ _ _
    K (E.obj M : Type u) _ _ _ _ hfree
    (E.map (ModuleCat.ofHom P.q)).hom hsurj

private noncomputable def liftedComplexOf
    {S : ShortComplex (ModuleCat.{u} R)}
    (P₁ : FreeSplitCover S.X₁) (P₃ : FreeSplitCover S.X₃)
  [Module.Free R (S.X₂ : Type u)] [Module.Finite R (S.X₂ : Type u)] :
    ShortComplex (ModuleCat.{u} R) := by
  refine ShortComplex.mk (ModuleCat.ofHom P₁.q ≫ S.f) (S.g ≫ ModuleCat.ofHom P₃.s) ?_
  simp only [Category.assoc]
  rw [← Category.assoc S.f S.g (ModuleCat.ofHom P₃.s)]
  rw [S.zero]
  simp

private lemma lifted_range_fibre
    {S : ShortComplex (ModuleCat.{u} R)}
    (P₁ : FreeSplitCover S.X₁) (P₃ : FreeSplitCover S.X₃)
    [Module.Free R (S.X₂ : Type u)] [Module.Finite R (S.X₂ : Type u)]
    (p : PrimeSpectrum R) :
    Module.finrank p.asIdeal.ResidueField
        (LinearMap.range ((liftedComplexOf P₁ P₃).map
          (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).f.hom) =
      Module.finrank p.asIdeal.ResidueField
        (LinearMap.range (S.map
          (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).f.hom) := by
  dsimp [liftedComplexOf]
  let K := p.asIdeal.ResidueField
  let E := ModuleCat.extendScalars (algebraMap R K)
  change Module.finrank K (LinearMap.range
      (E.map (ModuleCat.ofHom P₁.q ≫ S.f)).hom) =
    Module.finrank K (LinearMap.range (E.map S.f).hom)
  let qₚ := (E.map (ModuleCat.ofHom P₁.q)).hom
  let fₚ := (E.map S.f).hom
  rw [E.map_comp]
  change Module.finrank K (LinearMap.range (fₚ.comp qₚ)) =
    Module.finrank K (LinearMap.range fₚ)
  have hqₚ : Function.Surjective qₚ := by
    have hqs : ModuleCat.ofHom P₁.s ≫ ModuleCat.ofHom P₁.q = 𝟙 _ := by
      apply ModuleCat.hom_ext
      change P₁.q.comp P₁.s = LinearMap.id
      exact P₁.q_section
    have hsec' : E.map (ModuleCat.ofHom P₁.s) ≫
        E.map (ModuleCat.ofHom P₁.q) = 𝟙 _ := by
      rw [← E.map_comp, hqs]
      simp
    have hsec : qₚ.comp (E.map (ModuleCat.ofHom P₁.s)).hom = LinearMap.id := by
      simpa using congrArg ModuleCat.Hom.hom hsec'
    intro y
    refine ⟨(E.map (ModuleCat.ofHom P₁.s)).hom y, ?_⟩
    simpa [LinearMap.comp_apply] using congrArg (fun m => m y) hsec
  have hrange : LinearMap.range (fₚ.comp qₚ) = LinearMap.range fₚ := by
    exact LinearMap.range_comp_of_range_eq_top fₚ (LinearMap.range_eq_top.2 hqₚ)
  rw [hrange]

private lemma lifted_ker_fibre
    {S : ShortComplex (ModuleCat.{u} R)}
    (P₁ : FreeSplitCover S.X₁) (P₃ : FreeSplitCover S.X₃)
    [Module.Free R (S.X₂ : Type u)] [Module.Finite R (S.X₂ : Type u)]
    (p : PrimeSpectrum R) :
    LinearMap.ker ((liftedComplexOf P₁ P₃).map
          (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).g.hom =
      LinearMap.ker (S.map
          (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).g.hom := by
  dsimp [liftedComplexOf]
  let K := p.asIdeal.ResidueField
  let E := ModuleCat.extendScalars (algebraMap R K)
  change LinearMap.ker (E.map (S.g ≫ ModuleCat.ofHom P₃.s)).hom =
    LinearMap.ker (E.map S.g).hom
  rw [E.map_comp]
  let sₚ := (E.map (ModuleCat.ofHom P₃.s)).hom
  let gₚ := (E.map S.g).hom
  have hsₚ : Function.Injective sₚ := by
    have hqs : ModuleCat.ofHom P₃.s ≫ ModuleCat.ofHom P₃.q = 𝟙 _ := by
      apply ModuleCat.hom_ext
      change P₃.q.comp P₃.s = LinearMap.id
      exact P₃.q_section
    have hsec' : E.map (ModuleCat.ofHom P₃.s) ≫
        E.map (ModuleCat.ofHom P₃.q) = 𝟙 _ := by
      rw [← E.map_comp, hqs]
      simp
    have hsec : (E.map (ModuleCat.ofHom P₃.q)).hom.comp sₚ = LinearMap.id := by
      simpa using congrArg ModuleCat.Hom.hom hsec'
    intro x y hxy
    have hxy' := congrArg (fun z => (E.map (ModuleCat.ofHom P₃.q)).hom z) hxy
    have hx := congrArg (fun m => m x) hsec
    have hy := congrArg (fun m => m y) hsec
    simpa [LinearMap.comp_apply] using (hx.symm.trans (hxy'.trans hy))
  have hker : LinearMap.ker (sₚ.comp gₚ) = LinearMap.ker gₚ :=
    LinearMap.ker_comp_of_ker_eq_bot gₚ (LinearMap.ker_eq_bot.2 hsₚ)
  exact hker

private lemma finrank_range_add_finrank_ker_of_finite
    {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (hV : Module.Finite K V) (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) =
      Module.finrank K V :=
  @LinearMap.finrank_range_add_finrank_ker K V _ _ _ W _ _ hV f

private noncomputable def stabilizedComplexOf
    {S : ShortComplex (ModuleCat.{u} R)}
    (P₁ : FreeSplitCover S.X₁) (P₂ : FreeSplitCover S.X₂) (P₃ : FreeSplitCover S.X₃) :
    ShortComplex (ModuleCat.{u} R) := by
  refine ShortComplex.mk
    (ModuleCat.ofHom P₁.q ≫ S.f ≫ ModuleCat.ofHom P₂.s)
    (ModuleCat.ofHom P₂.q ≫ S.g ≫ ModuleCat.ofHom P₃.s) ?_
  simp only [← Category.assoc]
  rw [Category.assoc (ModuleCat.ofHom P₁.q ≫ S.f)
      (ModuleCat.ofHom P₂.s) (ModuleCat.ofHom P₂.q),
    show ModuleCat.ofHom P₂.s ≫ ModuleCat.ofHom P₂.q = 𝟙 _ by
      apply ModuleCat.hom_ext
      change P₂.q.comp P₂.s = LinearMap.id
      exact P₂.q_section]
  simp only [Category.comp_id]
  rw [Category.assoc (ModuleCat.ofHom P₁.q) S.f S.g, S.zero]
  simp

private lemma stabilized_range_fibre
    {S : ShortComplex (ModuleCat.{u} R)}
    [Module.Finite R (S.X₁ : Type u)] [Module.Projective R (S.X₁ : Type u)]
    [Module.Finite R (S.X₂ : Type u)] [Module.Projective R (S.X₂ : Type u)]
    [Module.Finite R (S.X₃ : Type u)] [Module.Projective R (S.X₃ : Type u)]
    (P₁ : FreeSplitCover S.X₁) (P₂ : FreeSplitCover S.X₂) (P₃ : FreeSplitCover S.X₃)
    (p : PrimeSpectrum R) :
    Module.finrank p.asIdeal.ResidueField
        (LinearMap.range ((stabilizedComplexOf P₁ P₂ P₃).map
          (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).f.hom) =
      Module.finrank p.asIdeal.ResidueField
        (LinearMap.range (S.map
          (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).f.hom) := by
  dsimp [stabilizedComplexOf]
  let K := p.asIdeal.ResidueField
  let E := ModuleCat.extendScalars (algebraMap R K)
  let hE₁ : Module.Finite K (E.obj S.X₁ : Type u) :=
    splitCoverBaseChangeFinite S.X₁ P₁ (algebraMap R K)
  let hE₂ : Module.Finite K (E.obj S.X₂ : Type u) :=
    splitCoverBaseChangeFinite S.X₂ P₂ (algebraMap R K)
  change Module.finrank K (LinearMap.range
      (E.map (ModuleCat.ofHom P₁.q ≫ S.f ≫ ModuleCat.ofHom P₂.s)).hom) =
    Module.finrank K (LinearMap.range (E.map S.f).hom)
  rw [E.map_comp, E.map_comp]
  change Module.finrank K (LinearMap.range
      ((E.map (ModuleCat.ofHom P₂.s)).hom.comp
        ((E.map S.f).hom.comp (E.map (ModuleCat.ofHom P₁.q)).hom))) = _
  let qp : E.obj (ModuleCat.of R (Fin P₁.n → R)) →ₗ[K] E.obj S.X₁ :=
    (E.map (ModuleCat.ofHom P₁.q)).hom
  let fp : E.obj S.X₁ →ₗ[K] E.obj S.X₂ := (E.map S.f).hom
  let sp : E.obj S.X₂ →ₗ[K] E.obj (ModuleCat.of R (Fin P₂.n → R)) :=
    (E.map (ModuleCat.ofHom P₂.s)).hom
  have hq : Function.Surjective qp := by
    have hqs : ModuleCat.ofHom P₁.s ≫ ModuleCat.ofHom P₁.q = 𝟙 _ := by
      apply ModuleCat.hom_ext
      change P₁.q.comp P₁.s = LinearMap.id
      exact P₁.q_section
    have hsec' : E.map (ModuleCat.ofHom P₁.s) ≫ E.map (ModuleCat.ofHom P₁.q) = 𝟙 _ := by
      rw [← E.map_comp, hqs]
      simp
    have hsec : qp.comp (E.map (ModuleCat.ofHom P₁.s)).hom = LinearMap.id := by
      simpa [qp] using congrArg ModuleCat.Hom.hom hsec'
    intro y
    refine ⟨(E.map (ModuleCat.ofHom P₁.s)).hom y, ?_⟩
    simpa [LinearMap.comp_apply] using congrArg (fun m => m y) hsec
  have hsp : Function.Injective sp := by
    have hqs : ModuleCat.ofHom P₂.s ≫ ModuleCat.ofHom P₂.q = 𝟙 _ := by
      apply ModuleCat.hom_ext
      change P₂.q.comp P₂.s = LinearMap.id
      exact P₂.q_section
    have hsec' : E.map (ModuleCat.ofHom P₂.s) ≫ E.map (ModuleCat.ofHom P₂.q) = 𝟙 _ := by
      rw [← E.map_comp, hqs]
      simp
    have hsec : (E.map (ModuleCat.ofHom P₂.q)).hom.comp sp = LinearMap.id := by
      simpa [sp] using congrArg ModuleCat.Hom.hom hsec'
    intro x y hxy
    have hxy' := congrArg (fun z => (E.map (ModuleCat.ofHom P₂.q)).hom z) hxy
    have hx := congrArg (fun m => m x) hsec
    have hy := congrArg (fun m => m y) hsec
    simpa [LinearMap.comp_apply] using (hx.symm.trans (hxy'.trans hy))
  have hleft : LinearMap.range ((sp.comp fp).comp qp) = LinearMap.range (sp.comp fp) :=
    LinearMap.range_comp_of_range_eq_top (sp.comp fp) (LinearMap.range_eq_top.2 hq)
  have hrank_s : Module.finrank K (LinearMap.range (sp.comp fp)) =
      Module.finrank K (LinearMap.range fp) := by
    have h1 := finrank_range_add_finrank_ker_of_finite hE₁ (sp.comp fp)
    have h2 := finrank_range_add_finrank_ker_of_finite hE₁ fp
    rw [LinearMap.ker_comp_of_ker_eq_bot fp (LinearMap.ker_eq_bot.2 hsp)] at h1
    omega
  rw [show sp.comp (fp.comp qp) = (sp.comp fp).comp qp by rfl, hleft, hrank_s]

private lemma stabilized_range_g_fibre
    {S : ShortComplex (ModuleCat.{u} R)}
    [Module.Finite R (S.X₁ : Type u)] [Module.Projective R (S.X₁ : Type u)]
    [Module.Finite R (S.X₂ : Type u)] [Module.Projective R (S.X₂ : Type u)]
    [Module.Finite R (S.X₃ : Type u)] [Module.Projective R (S.X₃ : Type u)]
    (P₁ : FreeSplitCover S.X₁) (P₂ : FreeSplitCover S.X₂) (P₃ : FreeSplitCover S.X₃)
    (p : PrimeSpectrum R) :
    Module.finrank p.asIdeal.ResidueField
        (LinearMap.range ((stabilizedComplexOf P₁ P₂ P₃).map
          (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).g.hom) =
      Module.finrank p.asIdeal.ResidueField
        (LinearMap.range (S.map
          (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).g.hom) := by
  dsimp [stabilizedComplexOf]
  let K := p.asIdeal.ResidueField
  let E := ModuleCat.extendScalars (algebraMap R K)
  let hE₂ : Module.Finite K (E.obj S.X₂ : Type u) :=
    splitCoverBaseChangeFinite S.X₂ P₂ (algebraMap R K)
  change Module.finrank K (LinearMap.range
      (E.map (ModuleCat.ofHom P₂.q ≫ S.g ≫ ModuleCat.ofHom P₃.s)).hom) =
    Module.finrank K (LinearMap.range (E.map S.g).hom)
  rw [E.map_comp, E.map_comp]
  change Module.finrank K (LinearMap.range
      ((E.map (ModuleCat.ofHom P₃.s)).hom.comp
        ((E.map S.g).hom.comp (E.map (ModuleCat.ofHom P₂.q)).hom))) = _
  let qp : E.obj (ModuleCat.of R (Fin P₂.n → R)) →ₗ[K] E.obj S.X₂ :=
    (E.map (ModuleCat.ofHom P₂.q)).hom
  let gp : E.obj S.X₂ →ₗ[K] E.obj S.X₃ := (E.map S.g).hom
  let sp : E.obj S.X₃ →ₗ[K] E.obj (ModuleCat.of R (Fin P₃.n → R)) :=
    (E.map (ModuleCat.ofHom P₃.s)).hom
  have hq : Function.Surjective qp := by
    have hqs : ModuleCat.ofHom P₂.s ≫ ModuleCat.ofHom P₂.q = 𝟙 _ := by
      apply ModuleCat.hom_ext
      change P₂.q.comp P₂.s = LinearMap.id
      exact P₂.q_section
    have hsec' : E.map (ModuleCat.ofHom P₂.s) ≫ E.map (ModuleCat.ofHom P₂.q) = 𝟙 _ := by
      rw [← E.map_comp, hqs]
      simp
    have hsec : qp.comp (E.map (ModuleCat.ofHom P₂.s)).hom = LinearMap.id := by
      simpa [qp] using congrArg ModuleCat.Hom.hom hsec'
    intro y
    refine ⟨(E.map (ModuleCat.ofHom P₂.s)).hom y, ?_⟩
    simpa [LinearMap.comp_apply] using congrArg (fun m => m y) hsec
  have hsp : Function.Injective sp := by
    have hqs : ModuleCat.ofHom P₃.s ≫ ModuleCat.ofHom P₃.q = 𝟙 _ := by
      apply ModuleCat.hom_ext
      change P₃.q.comp P₃.s = LinearMap.id
      exact P₃.q_section
    have hsec' : E.map (ModuleCat.ofHom P₃.s) ≫ E.map (ModuleCat.ofHom P₃.q) = 𝟙 _ := by
      rw [← E.map_comp, hqs]
      simp
    have hsec : (E.map (ModuleCat.ofHom P₃.q)).hom.comp sp = LinearMap.id := by
      simpa [sp] using congrArg ModuleCat.Hom.hom hsec'
    intro x y hxy
    have hxy' := congrArg (fun z => (E.map (ModuleCat.ofHom P₃.q)).hom z) hxy
    have hx := congrArg (fun m => m x) hsec
    have hy := congrArg (fun m => m y) hsec
    simpa [LinearMap.comp_apply] using (hx.symm.trans (hxy'.trans hy))
  have hleft : LinearMap.range ((sp.comp gp).comp qp) = LinearMap.range (sp.comp gp) :=
    LinearMap.range_comp_of_range_eq_top (sp.comp gp) (LinearMap.range_eq_top.2 hq)
  have hrank_s : Module.finrank K (LinearMap.range (sp.comp gp)) =
      Module.finrank K (LinearMap.range gp) := by
    have h1 := finrank_range_add_finrank_ker_of_finite hE₂ (sp.comp gp)
    have h2 := finrank_range_add_finrank_ker_of_finite hE₂ gp
    rw [LinearMap.ker_comp_of_ker_eq_bot gp (LinearMap.ker_eq_bot.2 hsp)] at h1
    omega
  rw [show sp.comp (gp.comp qp) = (sp.comp gp).comp qp by rfl, hleft, hrank_s]

private lemma stabilized_fibreHomologyFinrank_add_rankAtStalk
    {S : ShortComplex (ModuleCat.{u} R)}
    [Module.Finite R (S.X₁ : Type u)] [Module.Projective R (S.X₁ : Type u)]
    [Module.Finite R (S.X₂ : Type u)] [Module.Projective R (S.X₂ : Type u)]
    [Module.Finite R (S.X₃ : Type u)] [Module.Projective R (S.X₃ : Type u)]
    (P₁ : FreeSplitCover S.X₁) (P₂ : FreeSplitCover S.X₂) (P₃ : FreeSplitCover S.X₃)
    (p : PrimeSpectrum R) :
    fibreHomologyFinrank (S := S) p + P₂.n =
      fibreHomologyFinrank (S := stabilizedComplexOf P₁ P₂ P₃) p +
        Module.rankAtStalk (R := R) (S.X₂ : Type u) p := by
  let K := p.asIdeal.ResidueField
  let E := ModuleCat.extendScalars (algebraMap R K)
  let T := stabilizedComplexOf P₁ P₂ P₃
  let hE₁ : Module.Finite K (E.obj S.X₁ : Type u) :=
    splitCoverBaseChangeFinite S.X₁ P₁ (algebraMap R K)
  let hE₂ : Module.Finite K (E.obj S.X₂ : Type u) :=
    splitCoverBaseChangeFinite S.X₂ P₂ (algebraMap R K)
  let hT₁ : Module.Finite K (E.obj (ModuleCat.of R (Fin P₁.n → R)) : Type u) :=
    freeBaseChangeFinite (ModuleCat.of R (Fin P₁.n → R)) (algebraMap R K)
  let hT₂ : Module.Finite K (E.obj (ModuleCat.of R (Fin P₂.n → R)) : Type u) :=
    freeBaseChangeFinite (ModuleCat.of R (Fin P₂.n → R)) (algebraMap R K)
  have hS := @shortComplexHomologyFinrank_add_finrank_range_add_finrank_range
    K _ (S.map E) hE₁ hE₂
  have hT := @shortComplexHomologyFinrank_add_finrank_range_add_finrank_range
    K _ (T.map E) hT₁ hT₂
  change Module.finrank K ((S.map E).homology) +
      Module.finrank K (LinearMap.range (S.map E).f.hom) +
      Module.finrank K (LinearMap.range (S.map E).g.hom) =
      Module.finrank K (E.obj S.X₂ : Type u) at hS
  change Module.finrank K ((T.map E).homology) +
      Module.finrank K (LinearMap.range (T.map E).f.hom) +
      Module.finrank K (LinearMap.range (T.map E).g.hom) =
      Module.finrank K (E.obj (ModuleCat.of R (Fin P₂.n → R)) : Type u) at hT
  have hRf := stabilized_range_fibre P₁ P₂ P₃ p
  have hRf' : Module.finrank K (LinearMap.range (T.map E).f.hom) =
      Module.finrank K (LinearMap.range (S.map E).f.hom) := by
    simpa [T, E, K] using hRf
  have hRg := stabilized_range_g_fibre P₁ P₂ P₃ p
  have hRg' : Module.finrank K (LinearMap.range (T.map E).g.hom) =
      Module.finrank K (LinearMap.range (S.map E).g.hom) := by
    simpa [T, E, K] using hRg
  have hP₂ : Module.finrank K (E.obj (ModuleCat.of R (Fin P₂.n → R)) : Type u) = P₂.n := by
    let e := ModuleCat.extendScalarsAlgebraIso (C := K)
      (ModuleCat.of R (Fin P₂.n → R))
    calc
      Module.finrank K (E.obj (ModuleCat.of R (Fin P₂.n → R)) : Type u) =
          Module.finrank K (K ⊗[R] (Fin P₂.n → R)) := e.toLinearEquiv.finrank_eq
      _ = P₂.n := by
        rw [Module.finrank_eq_card_basis
          (Algebra.TensorProduct.basis K (Pi.basisFun R (Fin P₂.n)))]
        simp
  have hRank :=
    GromovWitten.AlgebraicGeometry.FiniteProjectiveFibreRank.finrank_extendScalars_eq_rankAtStalk
      S.X₂ p
  have hRank' : Module.finrank K (E.obj S.X₂ : Type u) =
      Module.rankAtStalk (R := R) (S.X₂ : Type u) p := by
    simpa [E, K] using hRank
  change Module.finrank K ((S.map E).homology) + P₂.n =
      Module.finrank K ((T.map E).homology) +
        Module.rankAtStalk (R := R) (S.X₂ : Type u) p
  omega

private lemma fibreHomology_eq_free_of_free_middle
    {S : ShortComplex (ModuleCat.{u} R)}
    [Module.Finite R (S.X₁ : Type u)] [Module.Projective R (S.X₁ : Type u)]
    [Module.Finite R (S.X₃ : Type u)] [Module.Projective R (S.X₃ : Type u)]
    [Module.Free R (S.X₂ : Type u)] [Module.Finite R (S.X₂ : Type u)]
    (p : PrimeSpectrum R) :
    fibreHomologyFinrank (S := S) p =
      fibreHomologyFinrank (S := liftedComplexOf (freeSplitCover S.X₁)
        (freeSplitCover S.X₃)) p := by
  let P₁ := freeSplitCover S.X₁
  let P₃ := freeSplitCover S.X₃
  let T := liftedComplexOf P₁ P₃
  let K := p.asIdeal.ResidueField
  let E := ModuleCat.extendScalars (algebraMap R K)
  let hE₁ : Module.Finite K (E.obj S.X₁ : Type u) :=
    splitCoverBaseChangeFinite S.X₁ P₁ (algebraMap R K)
  let hE₂ : Module.Finite K (E.obj S.X₂ : Type u) :=
    freeBaseChangeFinite S.X₂ (algebraMap R K)
  let hE₃ : Module.Finite K (E.obj S.X₃ : Type u) :=
    splitCoverBaseChangeFinite S.X₃ P₃ (algebraMap R K)
  let hT₁ : Module.Finite K (E.obj (ModuleCat.of R (Fin P₁.n → R)) : Type u) :=
    freeBaseChangeFinite (ModuleCat.of R (Fin P₁.n → R)) (algebraMap R K)
  have hS := @shortComplexHomologyFinrank_add_finrank_range_add_finrank_range
    K _ (S.map E) hE₁ hE₂
  have hT := @shortComplexHomologyFinrank_add_finrank_range_add_finrank_range
    K _ (T.map E) hT₁ hE₂
  have hRf := lifted_range_fibre P₁ P₃ p
  have hRf' : Module.finrank K (LinearMap.range (T.map E).f.hom) =
      Module.finrank K (LinearMap.range (S.map E).f.hom) := by
    simpa [T, E, K] using hRf
  have hKg := lifted_ker_fibre P₁ P₃ p
  have hKg' : LinearMap.ker (T.map E).g.hom = LinearMap.ker (S.map E).g.hom := by
    simpa [T, E, K] using hKg
  have hKgFin : Module.finrank K (LinearMap.ker (T.map E).g.hom) =
      Module.finrank K (LinearMap.ker (S.map E).g.hom) :=
    congrArg (fun L : Submodule K (E.obj S.X₂ : Type u) => Module.finrank K L) hKg'
  have hRg : Module.finrank K (LinearMap.range (T.map E).g.hom) =
      Module.finrank K (LinearMap.range (S.map E).g.hom) := by
    have hTg := finrank_range_add_finrank_ker_of_finite hE₂ (T.map E).g.hom
    have hSg := finrank_range_add_finrank_ker_of_finite hE₂ (S.map E).g.hom
    change Module.finrank K (LinearMap.range (T.map E).g.hom) +
      Module.finrank K (LinearMap.ker (T.map E).g.hom) =
        Module.finrank K (E.obj S.X₂ : Type u) at hTg
    change Module.finrank K (LinearMap.range (S.map E).g.hom) +
      Module.finrank K (LinearMap.ker (S.map E).g.hom) =
        Module.finrank K (E.obj S.X₂ : Type u) at hSg
    omega
  have hS' := hS
  have hT' := hT
  have hX₂ : Module.finrank K ((T.map E).X₂ : Type u) =
      Module.finrank K ((S.map E).X₂ : Type u) := by rfl
  change Module.finrank K ((S.map E).homology) =
      Module.finrank K ((T.map E).homology)
  rw [hRf'] at hT'
  omega

/-- The actual categorical fibre homology locus is open with finite-projective outer terms. -/
theorem isOpen_fibreHomologyLocus_of_free_middle
    {S : ShortComplex (ModuleCat.{u} R)}
    [Module.Finite R (S.X₁ : Type u)] [Module.Projective R (S.X₁ : Type u)]
    [Module.Finite R (S.X₃ : Type u)] [Module.Projective R (S.X₃ : Type u)]
    [Module.Free R (S.X₂ : Type u)] [Module.Finite R (S.X₂ : Type u)] (d : ℕ) :
    IsOpen (fibreHomologyLocus (S := S) d) := by
  let T := liftedComplexOf (freeSplitCover S.X₁) (freeSplitCover S.X₃)
  have hset : fibreHomologyLocus (S := S) d =
      fibreHomologyLocus (S := T) d := by
    ext p
    change fibreHomologyFinrank (S := S) p ≤ d ↔
      fibreHomologyFinrank (S := T) p ≤ d
    rw [fibreHomology_eq_free_of_free_middle p]
  have hfreeT₁ : Module.Free R (T.X₁ : Type u) := by
    change Module.Free R (Fin (freeSplitCover S.X₁).n → R)
    infer_instance
  have hfiniteT₁ : Module.Finite R (T.X₁ : Type u) := by
    change Module.Finite R (Fin (freeSplitCover S.X₁).n → R)
    infer_instance
  have hfreeT₂ : Module.Free R (T.X₂ : Type u) := by
    change Module.Free R (S.X₂ : Type u)
    infer_instance
  have hfiniteT₂ : Module.Finite R (T.X₂ : Type u) := by
    change Module.Finite R (S.X₂ : Type u)
    infer_instance
  have hfreeT₃ : Module.Free R (T.X₃ : Type u) := by
    change Module.Free R (Fin (freeSplitCover S.X₃).n → R)
    infer_instance
  have hfiniteT₃ : Module.Finite R (T.X₃ : Type u) := by
    change Module.Finite R (Fin (freeSplitCover S.X₃).n → R)
    infer_instance
  let hOpen : IsOpen (fibreHomologyLocus (S := T) d) :=
    @isOpen_fibreHomologyLocus R _ T hfreeT₁ hfiniteT₁ hfreeT₂ hfiniteT₂
      hfreeT₃ hfiniteT₃ d
  rw [hset]
  exact hOpen

private lemma locallyConstant_rankAtStalk_of_finite_projective
    (M : ModuleCat.{u} R)
    [Module.Finite R (M : Type u)] [Module.Projective R (M : Type u)] :
    IsLocallyConstant (Module.rankAtStalk (R := R) (M : Type u)) := by
  let hfp : Module.FinitePresentation R (M : Type u) :=
    Module.finitePresentation_of_projective R (M : Type u)
  let hflat : Module.Flat R (M : Type u) := Module.Flat.of_projective
  exact @Module.isLocallyConstant_rankAtStalk R (M : Type u) _ _ _ hfp hflat

/-- The actual categorical fibre homology locus is open for finite-projective terms. -/
theorem isOpen_fibreHomologyLocus_of_finite_projective
    {S : ShortComplex (ModuleCat.{u} R)}
    [Module.Finite R (S.X₁ : Type u)] [Module.Projective R (S.X₁ : Type u)]
    [Module.Finite R (S.X₂ : Type u)] [Module.Projective R (S.X₂ : Type u)]
    [Module.Finite R (S.X₃ : Type u)] [Module.Projective R (S.X₃ : Type u)] (d : ℕ) :
    IsOpen (fibreHomologyLocus (S := S) d) := by
  let P₁ := freeSplitCover S.X₁
  let P₂ := freeSplitCover S.X₂
  let P₃ := freeSplitCover S.X₃
  let T := stabilizedComplexOf P₁ P₂ P₃
  have hfreeT₁ : Module.Free R (T.X₁ : Type u) := by
    change Module.Free R (Fin P₁.n → R)
    infer_instance
  have hfiniteT₁ : Module.Finite R (T.X₁ : Type u) := by
    change Module.Finite R (Fin P₁.n → R)
    infer_instance
  have hfreeT₂ : Module.Free R (T.X₂ : Type u) := by
    change Module.Free R (Fin P₂.n → R)
    infer_instance
  have hfiniteT₂ : Module.Finite R (T.X₂ : Type u) := by
    change Module.Finite R (Fin P₂.n → R)
    infer_instance
  have hfreeT₃ : Module.Free R (T.X₃ : Type u) := by
    change Module.Free R (Fin P₃.n → R)
    infer_instance
  have hfiniteT₃ : Module.Finite R (T.X₃ : Type u) := by
    change Module.Finite R (Fin P₃.n → R)
    infer_instance
  have hT : ∀ e : ℕ, IsOpen (fibreHomologyLocus (S := T) e) := by
    intro e
    exact @isOpen_fibreHomologyLocus R _ T hfreeT₁ hfiniteT₁ hfreeT₂ hfiniteT₂
      hfreeT₃ hfiniteT₃ e
  have hrank : IsLocallyConstant
      (Module.rankAtStalk (R := R) (S.X₂ : Type u)) :=
    locallyConstant_rankAtStalk_of_finite_projective S.X₂
  have hbound : ∀ n : ℕ, IsOpen {p : PrimeSpectrum R |
      fibreHomologyFinrank (S := T) p + n ≤ d + P₂.n} := by
    intro n
    by_cases hn : n ≤ d + P₂.n
    · let e := d + P₂.n - n
      have heq : {p : PrimeSpectrum R |
          fibreHomologyFinrank (S := T) p + n ≤ d + P₂.n} =
          fibreHomologyLocus (S := T) e := by
        ext p
        change fibreHomologyFinrank (S := T) p + n ≤ d + P₂.n ↔
          fibreHomologyFinrank (S := T) p ≤ e
        dsimp [e]
        omega
      rw [heq]
      exact hT e
    · have heq : {p : PrimeSpectrum R |
          fibreHomologyFinrank (S := T) p + n ≤ d + P₂.n} = ∅ := by
        ext p
        constructor
        · intro hp
          change fibreHomologyFinrank (S := T) p + n ≤ d + P₂.n at hp
          exfalso
          exact hn (by omega)
        · simp
      rw [heq]
      exact isOpen_empty
  have hset : fibreHomologyLocus (S := S) d =
      ⋃ n : ℕ, {p : PrimeSpectrum R |
        Module.rankAtStalk (R := R) (S.X₂ : Type u) p = n} ∩
        {p : PrimeSpectrum R |
          fibreHomologyFinrank (S := T) p + n ≤ d + P₂.n} := by
    ext p
    constructor
    · intro hp
      let n := Module.rankAtStalk (R := R) (S.X₂ : Type u) p
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      constructor
      · rfl
      · have hformula := stabilized_fibreHomologyFinrank_add_rankAtStalk P₁ P₂ P₃ p
        change fibreHomologyFinrank (S := S) p ≤ d at hp
        change fibreHomologyFinrank (S := T) p + n ≤ d + P₂.n
        omega
    · intro hp
      rcases Set.mem_iUnion.1 hp with ⟨n, hn⟩
      have hformula := stabilized_fibreHomologyFinrank_add_rankAtStalk P₁ P₂ P₃ p
      have hbound' := hn.2
      have hrank' := hn.1
      change fibreHomologyFinrank (S := S) p ≤ d
      change fibreHomologyFinrank (S := T) p + n ≤ d + P₂.n at hbound'
      change Module.rankAtStalk (R := R) (S.X₂ : Type u) p = n at hrank'
      omega
  rw [hset]
  exact isOpen_iUnion fun n => (hrank.isOpen_fiber n).inter (hbound n)

/-- Fibre homology dimension is upper semicontinuous for a finite-projective short complex. -/
theorem upperSemicontinuous_fibreHomologyFinrank_of_finite_projective
    {S : ShortComplex (ModuleCat.{u} R)}
    [Module.Finite R (S.X₁ : Type u)] [Module.Projective R (S.X₁ : Type u)]
    [Module.Finite R (S.X₂ : Type u)] [Module.Projective R (S.X₂ : Type u)]
    [Module.Finite R (S.X₃ : Type u)] [Module.Projective R (S.X₃ : Type u)] :
    UpperSemicontinuous (fibreHomologyFinrank (S := S)) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro y
  cases y with
  | zero => simp
  | succ d =>
      have hopen := isOpen_fibreHomologyLocus_of_finite_projective (S := S) d
      convert hopen using 1
      ext p
      simp [fibreHomologyLocus]

end
end GromovWitten.AlgebraicGeometry.FiniteProjectiveHomologyLocus
