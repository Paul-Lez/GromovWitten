/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.RightDerived
/-!
# Comparison with an injective resolution

An exact augmented cochain complex maps to an injective resolution of its initial
object. The construction extends the augmentation in degree zero using injectivity,
then extends one degree at a time using exactness. If the augmentation is a
quasi-isomorphism, so is the comparison map.
-/

open CategoryTheory Limits HomologicalComplex
noncomputable section
namespace CategoryTheory.InjectiveResolution
variable {C : Type*} [Category C] [Abelian C] {Z : C} (I : InjectiveResolution Z)
/-- An augmented exact complex admits a compatible map to an injective resolution. -/
lemma exists_desc_from_exact (K : CochainComplex C ℕ) (ι : Z ⟶ K.X 0) [Mono ι]
    (w : ι ≫ K.d 0 1 = 0) (hzero : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (hexact : ∀ n, K.ExactAt (n + 1)) :
    ∃ φ : K ⟶ I.cocomplex, ι ≫ φ.f 0 = I.ι.f 0 := by
  let j : Z ⟶ I.cocomplex.X 0 := I.ι.f 0
  let g₀ := Injective.factorThru j ι
  have hg₀ : ι ≫ g₀ = I.ι.f 0 := Injective.comp_factorThru j ι
  let g₁ := hzero.descToInjective (g₀ ≫ I.cocomplex.d 0 1)
    (by
      rw [← Category.assoc, hg₀]
      exact I.ι_f_zero_comp_complex_d)
  have hg₁ : K.d 0 1 ≫ g₁ = g₀ ≫ I.cocomplex.d 0 1 :=
    hzero.comp_descToInjective _ _
  have hs (n : ℕ) : (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d _ _ _)).Exact :=
    (exactAt_iff' K n (n + 1) (n + 2) (by simp) (by simp)).mp (hexact n)
  let φ : K ⟶ I.cocomplex := CochainComplex.mkHom _ _ g₀ g₁ hg₁.symm
    (fun n ⟨g, g', hw⟩ =>
      let k := (hs n).descToInjective (g' ≫ I.cocomplex.d (n + 1) (n + 2))
        (by rw [← Category.assoc, ← hw, Category.assoc, I.cocomplex.d_comp_d, comp_zero])
      ⟨k, ((hs n).comp_descToInjective _ _).symm⟩)
  exact ⟨φ, hg₀⟩
end CategoryTheory.InjectiveResolution

namespace CochainComplex
variable {C : Type*} [Category C] [Abelian C] {Z : C}
variable {K : CochainComplex C ℕ} (a : (single₀ C).obj Z ⟶ K) [QuasiIsoAt a 0]
omit [QuasiIsoAt a 0] in
/-- The augmentation of a cochain complex is killed by its first differential. -/
lemma single₀_hom_comp_d : a.f 0 ≫ K.d 0 1 = 0 := by
  exact ((fromSingle₀Equiv K Z) a).property

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A quasi-isomorphism from a complex concentrated in degree zero identifies its
initial object with the kernel of the first differential. -/
def isLimitKernelFork_of_quasiIso :
    IsLimit (KernelFork.ofι (a.f 0) (single₀_hom_comp_d a)) := by
  refine IsLimit.ofIsoLimit (K.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt a 0 ≪≫ K.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up ℕ) _ _).hom,
    ← cancel_epi (isoHomologyπ₀ _).hom,
    ← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up ℕ) _ _).inv]
  simp
end CochainComplex

namespace CategoryTheory.InjectiveResolution
variable {C : Type*} [Category C] [Abelian C] {Z : C} (I : InjectiveResolution Z)
set_option backward.isDefEq.respectTransparency false in
/-- A resolution maps by a quasi-isomorphism to any injective resolution of the same object. -/
lemma exists_desc_of_quasiIso {K : CochainComplex C ℕ}
    (a : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso a] :
    ∃ φ : K ⟶ I.cocomplex, a ≫ φ = I.ι ∧ QuasiIso φ := by
  have hk := CochainComplex.isLimitKernelFork_of_quasiIso a
  have : Mono (show Z ⟶ K.X 0 from a.f 0) := mono_of_isLimit_fork hk
  have hexact (n : ℕ) : K.ExactAt (n + 1) := by
    rw [← quasiIsoAt_iff_exactAt a (n + 1) (CochainComplex.exactAt_succ_single_obj _ _)]
    infer_instance
  obtain ⟨φ, hφ⟩ := I.exists_desc_from_exact K (a.f 0)
    (CochainComplex.single₀_hom_comp_d a) (ShortComplex.exact_of_f_is_kernel _ hk) hexact
  have hcomm : a ≫ φ = I.ι := by
    ext
    exact hφ
  have : QuasiIso (a ≫ φ) := by rw [hcomm]; infer_instance
  exact ⟨φ, hcomm, quasiIso_of_comp_left a φ⟩
end CategoryTheory.InjectiveResolution

end
