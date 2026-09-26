/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Cones.DerivedCriteria
import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# The connecting map of two-term complexes agrees with Mathlib's connecting homomorphism

`Cones/Criteria.lean` builds, for a degreewise short exact sequence `0 → K' → K → K'' → 0` of
two-term complexes, an elementwise connecting homomorphism `PicardCriteria.ShortExact.delta :
h⁰(K'') →ₗ[R] h¹(K')` and proves the six-term cohomology sequence is exact.
`Cones/DerivedCriteria.lean` separately identifies the cochain realizations of two-term complexes
with Mathlib's homological algebra, identifying `h⁰`/`h¹` with the cohomology of the cochain
complex in degrees `-1`/`0` (`homologyNegOneIsoKer`, `homologyZeroIsoCoker`) and a degreewise
short exact sequence with a Mathlib `ShortComplex.ShortExact` of cochain complexes
(`PicardCriteria.ShortExact.cochainShortExact`). This file proves that `delta` agrees with
Mathlib's connecting homomorphism `ShortComplex.ShortExact.δ` of the associated long exact
cohomology sequence, under these identifications.

## Main results

* `homologyπ_comp_homologyNegOneIsoKer_hom`, `homologyπ_comp_homologyZeroIsoCoker_hom`: the
  isomorphisms `homologyNegOneIsoKer`/`homologyZeroIsoCoker` computed against `homologyπ`,
  `iCycles` and the submodule inclusion/quotient map.
* `homologyπ_cyclesMk_eq_homologyNegOneIsoKer_inv`,
  `homologyπ_cyclesMk_eq_homologyZeroIsoCoker_inv`: the elementwise ("constructor") form of the
  previous two lemmas, describing `(homologyNegOneIsoKer E).inv`/`(homologyZeroIsoCoker E).inv`
  applied to a class as the `homologyπ` of an explicit cocycle built with `cyclesMk`.
* `delta_eq_δ`: **the main theorem.** For `h : PicardCriteria.ShortExact ι π` and
  `c : PicardCriteria.h0 K''`, `(homologyZeroIsoCoker K').hom (h.cochainShortExact.δ (-1) 0 _
  ((homologyNegOneIsoKer K'').inv c)) = h.delta c`.
* `injective_delta_iff`: **the comparison is usable.** `h.delta` is injective iff Mathlib's
  `h.cochainShortExact.δ (-1) 0` is, transporting exactness of the repository's six-term sequence
  at `h⁰(K'')`/`h¹(K')` to exactness of Mathlib's homology long exact sequence and conversely.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (E : LinearTwoTermComplex R)

/-- The composite of `homologyπ` with `homologyNegOneIsoKer` and the submodule
inclusion is `iCycles`. -/
theorem homologyπ_comp_homologyNegOneIsoKer_hom :
    E.toCochainComplex.homologyπ (-1) ≫ (LinearTwoTermComplex.homologyNegOneIsoKer E).hom ≫
      ModuleCat.ofHom (PicardCriteria.h0 E).subtype = E.toCochainComplex.iCycles (-1) := by
  have hi : (ComplexShape.up ℤ).prev (-1) = (-2 : ℤ) := by rw [CochainComplex.prev]; norm_num
  have hk : (ComplexShape.up ℤ).next (-1) = (0 : ℤ) := by rw [CochainComplex.next]; norm_num
  have hz : IsZero (E.toCochainComplex.X (-2)) :=
    LinearTwoTermComplex.toCochainComplex_X_isZero E (-2) (by norm_num) (by norm_num)
  have hf : (E.toCochainComplex.sc' (-2) (-1) 0).f = 0 := by
    apply hz.eq_of_src
  have key : (LinearTwoTermComplex.homologyNegOneIsoKer E).hom =
      ((E.toCochainComplex.homologyIsoSc' (-2) (-1) 0 hi hk) ≪≫
        (ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
          hf _ (ModuleCat.kernelIsLimit _)).homologyIso).hom := rfl
  have step1 :
      E.toCochainComplex.homologyπ (-1) ≫ (LinearTwoTermComplex.homologyNegOneIsoKer E).hom ≫
        ModuleCat.ofHom (PicardCriteria.h0 E).subtype =
      (E.toCochainComplex.homologyπ (-1) ≫
        (E.toCochainComplex.homologyIsoSc' (-2) (-1) 0 hi hk).hom) ≫
        ((ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
          hf _ (ModuleCat.kernelIsLimit _)).homologyIso.hom ≫
          ModuleCat.ofHom (PicardCriteria.h0 E).subtype) := by
    rw [key]; rfl
  have step2 :
      (E.toCochainComplex.homologyπ (-1) ≫
        (E.toCochainComplex.homologyIsoSc' (-2) (-1) 0 hi hk).hom) ≫
        ((ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
          hf _ (ModuleCat.kernelIsLimit _)).homologyIso.hom ≫
          ModuleCat.ofHom (PicardCriteria.h0 E).subtype) =
      ((E.toCochainComplex.cyclesIsoSc' (-2) (-1) 0 hi hk).hom ≫
        (E.toCochainComplex.sc' (-2) (-1) 0).homologyπ) ≫
        ((ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
          hf _ (ModuleCat.kernelIsLimit _)).homologyIso.hom ≫
          ModuleCat.ofHom (PicardCriteria.h0 E).subtype) :=
    congrArg (· ≫ _) (HomologicalComplex.π_homologyIsoSc'_hom E.toCochainComplex (-2) (-1) 0 hi hk)
  have step3 :
      ((E.toCochainComplex.cyclesIsoSc' (-2) (-1) 0 hi hk).hom ≫
        (E.toCochainComplex.sc' (-2) (-1) 0).homologyπ) ≫
        ((ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
          hf _ (ModuleCat.kernelIsLimit _)).homologyIso.hom ≫
          ModuleCat.ofHom (PicardCriteria.h0 E).subtype) =
      (E.toCochainComplex.cyclesIsoSc' (-2) (-1) 0 hi hk).hom ≫
        (((E.toCochainComplex.sc' (-2) (-1) 0).homologyπ ≫
          (ShortComplex.LeftHomologyData.ofIsLimitKernelFork
            (E.toCochainComplex.sc' (-2) (-1) 0) hf _
            (ModuleCat.kernelIsLimit _)).homologyIso.hom) ≫
          ModuleCat.ofHom (PicardCriteria.h0 E).subtype) := rfl
  have step4 :
      (E.toCochainComplex.sc' (-2) (-1) 0).homologyπ ≫
        (ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
          hf _ (ModuleCat.kernelIsLimit _)).homologyIso.hom =
      (ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
        hf _ (ModuleCat.kernelIsLimit _)).cyclesIso.hom :=
    (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom
      (E.toCochainComplex.sc' (-2) (-1) 0)
      (ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
        hf _ (ModuleCat.kernelIsLimit _))).trans rfl
  have step6 :
      (ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
        hf _ (ModuleCat.kernelIsLimit _)).cyclesIso.hom ≫
        ModuleCat.ofHom (PicardCriteria.h0 E).subtype =
      (E.toCochainComplex.sc' (-2) (-1) 0).iCycles := by
    have heq : ModuleCat.ofHom (PicardCriteria.h0 E).subtype =
        (ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
          hf _ (ModuleCat.kernelIsLimit _)).i := rfl
    exact (congrArg (fun x =>
        (ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
          hf _ (ModuleCat.kernelIsLimit _)).cyclesIso.hom ≫ x) heq).trans
      (ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i
        (ShortComplex.LeftHomologyData.ofIsLimitKernelFork (E.toCochainComplex.sc' (-2) (-1) 0)
          hf _ (ModuleCat.kernelIsLimit _)))
  have step7 :
      (E.toCochainComplex.cyclesIsoSc' (-2) (-1) 0 hi hk).hom ≫
        (E.toCochainComplex.sc' (-2) (-1) 0).iCycles = E.toCochainComplex.iCycles (-1) :=
    HomologicalComplex.cyclesIsoSc'_hom_iCycles E.toCochainComplex (-2) (-1) 0 hi hk
  exact step1.trans (step2.trans (step3.trans
    ((congrArg (fun x => (E.toCochainComplex.cyclesIsoSc' (-2) (-1) 0 hi hk).hom ≫ x)
        (congrArg (· ≫ ModuleCat.ofHom (PicardCriteria.h0 E).subtype) step4)).trans
      ((congrArg (fun x => (E.toCochainComplex.cyclesIsoSc' (-2) (-1) 0 hi hk).hom ≫ x) step6).trans
        step7))))

/-- The composite of `homologyπ` with `homologyZeroIsoCoker` agrees with `iCycles`
followed by the quotient map onto `h¹`. -/
theorem homologyπ_comp_homologyZeroIsoCoker_hom :
    E.toCochainComplex.homologyπ 0 ≫ (LinearTwoTermComplex.homologyZeroIsoCoker E).hom =
      E.toCochainComplex.iCycles 0 ≫
        ModuleCat.ofHom (LinearMap.range E.differential).mkQ := by
  have hi : (ComplexShape.up ℤ).prev 0 = (-1 : ℤ) := by rw [CochainComplex.prev]; norm_num
  have hk : (ComplexShape.up ℤ).next 0 = (1 : ℤ) := by rw [CochainComplex.next]; norm_num
  have hz : IsZero (E.toCochainComplex.X 1) :=
    LinearTwoTermComplex.toCochainComplex_X_isZero E 1 (by norm_num) (by norm_num)
  have hg : (E.toCochainComplex.sc' (-1) 0 1).g = 0 := by
    apply hz.eq_of_tgt
  have key : (LinearTwoTermComplex.homologyZeroIsoCoker E).hom =
      ((E.toCochainComplex.homologyIsoSc' (-1) 0 1 hi hk) ≪≫
        (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
          (E.toCochainComplex.sc' (-1) 0 1)
          hg _ (ModuleCat.cokernelIsColimit _)).homologyIso).hom := rfl
  have step1 :
      E.toCochainComplex.homologyπ 0 ≫ (LinearTwoTermComplex.homologyZeroIsoCoker E).hom =
      (E.toCochainComplex.homologyπ 0 ≫
        (E.toCochainComplex.homologyIsoSc' (-1) 0 1 hi hk).hom) ≫
        (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
          (E.toCochainComplex.sc' (-1) 0 1) hg _
          (ModuleCat.cokernelIsColimit _)).homologyIso.hom := by
    rw [key]; rfl
  have step2 :
      (E.toCochainComplex.homologyπ 0 ≫
        (E.toCochainComplex.homologyIsoSc' (-1) 0 1 hi hk).hom) ≫
        (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
          (E.toCochainComplex.sc' (-1) 0 1) hg _
          (ModuleCat.cokernelIsColimit _)).homologyIso.hom =
      ((E.toCochainComplex.cyclesIsoSc' (-1) 0 1 hi hk).hom ≫
        (E.toCochainComplex.sc' (-1) 0 1).homologyπ) ≫
        (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
          (E.toCochainComplex.sc' (-1) 0 1) hg _
          (ModuleCat.cokernelIsColimit _)).homologyIso.hom :=
    congrArg (· ≫ _) (HomologicalComplex.π_homologyIsoSc'_hom E.toCochainComplex (-1) 0 1 hi hk)
  have step3 :
      ((E.toCochainComplex.cyclesIsoSc' (-1) 0 1 hi hk).hom ≫
        (E.toCochainComplex.sc' (-1) 0 1).homologyπ) ≫
        (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
          (E.toCochainComplex.sc' (-1) 0 1) hg _
          (ModuleCat.cokernelIsColimit _)).homologyIso.hom =
      (E.toCochainComplex.cyclesIsoSc' (-1) 0 1 hi hk).hom ≫
        ((E.toCochainComplex.sc' (-1) 0 1).homologyπ ≫
          (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
            (E.toCochainComplex.sc' (-1) 0 1) hg _
            (ModuleCat.cokernelIsColimit _)).homologyIso.hom) := rfl
  have step4 :
      (E.toCochainComplex.sc' (-1) 0 1).homologyπ ≫
        (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
          (E.toCochainComplex.sc' (-1) 0 1) hg _
          (ModuleCat.cokernelIsColimit _)).homologyIso.hom =
      (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
        (E.toCochainComplex.sc' (-1) 0 1) hg _ (ModuleCat.cokernelIsColimit _)).cyclesIso.hom ≫
        (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
          (E.toCochainComplex.sc' (-1) 0 1) hg _ (ModuleCat.cokernelIsColimit _)).π :=
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom
      (E.toCochainComplex.sc' (-1) 0 1)
      (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
        (E.toCochainComplex.sc' (-1) 0 1) hg _ (ModuleCat.cokernelIsColimit _))
  have step5 :
      (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
        (E.toCochainComplex.sc' (-1) 0 1) hg _ (ModuleCat.cokernelIsColimit _)).cyclesIso.hom =
      (E.toCochainComplex.sc' (-1) 0 1).iCycles :=
    (Category.comp_id _).symm.trans
      (ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i
        (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
          (E.toCochainComplex.sc' (-1) 0 1) hg _ (ModuleCat.cokernelIsColimit _)))
  have step6 :
      (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
        (E.toCochainComplex.sc' (-1) 0 1) hg _ (ModuleCat.cokernelIsColimit _)).cyclesIso.hom ≫
        (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
          (E.toCochainComplex.sc' (-1) 0 1) hg _ (ModuleCat.cokernelIsColimit _)).π =
      (E.toCochainComplex.sc' (-1) 0 1).iCycles ≫
        ModuleCat.ofHom (LinearMap.range E.differential).mkQ := by
    have heq :
        (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
          (E.toCochainComplex.sc' (-1) 0 1) hg _ (ModuleCat.cokernelIsColimit _)).π =
        ModuleCat.ofHom (LinearMap.range E.differential).mkQ := rfl
    rw [step5, heq]
    rfl
  have step7 :
      (E.toCochainComplex.cyclesIsoSc' (-1) 0 1 hi hk).hom ≫
        (E.toCochainComplex.sc' (-1) 0 1).iCycles = E.toCochainComplex.iCycles 0 :=
    HomologicalComplex.cyclesIsoSc'_hom_iCycles E.toCochainComplex (-1) 0 1 hi hk
  exact step1.trans (step2.trans (step3.trans
    ((congrArg (fun x => (E.toCochainComplex.cyclesIsoSc' (-1) 0 1 hi hk).hom ≫ x)
        (step4.trans step6)).trans
      (congrArg (· ≫ ModuleCat.ofHom (LinearMap.range E.differential).mkQ) step7))))

/-- Elementwise form of `homologyπ_comp_homologyNegOneIsoKer_hom`: the class in `Mathlib`'s
cohomology `homology (-1)` of the cocycle built from an element of `h⁰(E)` is
`(homologyNegOneIsoKer E).inv` applied to that element. -/
theorem homologyπ_cyclesMk_eq_homologyNegOneIsoKer_inv (c : PicardCriteria.h0 E)
    (hj : (ComplexShape.up ℤ).next (-1) = (0 : ℤ))
    (hx : E.toCochainComplex.d (-1) 0 (c : E.degreeZero) = 0) :
    E.toCochainComplex.homologyπ (-1) (E.toCochainComplex.cyclesMk (c : E.degreeZero) 0 hj hx) =
      (LinearTwoTermComplex.homologyNegOneIsoKer E).inv c := by
  set z := E.toCochainComplex.cyclesMk (c : E.degreeZero) 0 hj hx with hz
  have hiz : E.toCochainComplex.iCycles (-1) z = (c : E.degreeZero) :=
    E.toCochainComplex.i_cyclesMk _ 0 hj hx
  have happ := ConcreteCategory.congr_hom (homologyπ_comp_homologyNegOneIsoKer_hom E) z
  simp only [CategoryTheory.comp_apply] at happ
  have hval : ((LinearTwoTermComplex.homologyNegOneIsoKer E).hom
      (E.toCochainComplex.homologyπ (-1) z) : E.degreeZero) = (c : E.degreeZero) :=
    happ.trans hiz
  have hc : (LinearTwoTermComplex.homologyNegOneIsoKer E).hom
      (E.toCochainComplex.homologyπ (-1) z) = c := Subtype.ext hval
  have hinvhom := ConcreteCategory.congr_hom
    (LinearTwoTermComplex.homologyNegOneIsoKer E).hom_inv_id
    (E.toCochainComplex.homologyπ (-1) z)
  simp only [CategoryTheory.comp_apply] at hinvhom
  exact hinvhom.symm.trans (congrArg (LinearTwoTermComplex.homologyNegOneIsoKer E).inv hc)

/-- Elementwise form of `homologyπ_comp_homologyZeroIsoCoker_hom`: the class in `Mathlib`'s
cohomology `homology 0` of the cocycle built from an element of `E.degreeOne` is
`(homologyZeroIsoCoker E).inv` applied to its class in `h¹(E)`. -/
theorem homologyπ_cyclesMk_eq_homologyZeroIsoCoker_inv (b : E.degreeOne)
    (hj : (ComplexShape.up ℤ).next 0 = (1 : ℤ)) (hx : E.toCochainComplex.d 0 1 b = 0) :
    E.toCochainComplex.homologyπ 0 (E.toCochainComplex.cyclesMk b 1 hj hx) =
      (LinearTwoTermComplex.homologyZeroIsoCoker E).inv (PicardCriteria.h1mk E b) := by
  set z := E.toCochainComplex.cyclesMk b 1 hj hx with hz
  have hiz : E.toCochainComplex.iCycles 0 z = b :=
    E.toCochainComplex.i_cyclesMk _ 1 hj hx
  have happ := ConcreteCategory.congr_hom (homologyπ_comp_homologyZeroIsoCoker_hom E) z
  simp only [CategoryTheory.comp_apply] at happ
  have hcomp : (E.toCochainComplex.iCycles 0 ≫
      ModuleCat.ofHom (LinearMap.range E.differential).mkQ) z =
      ModuleCat.ofHom (LinearMap.range E.differential).mkQ (E.toCochainComplex.iCycles 0 z) :=
    rfl
  have hc : (LinearTwoTermComplex.homologyZeroIsoCoker E).hom
      (E.toCochainComplex.homologyπ 0 z) = PicardCriteria.h1mk E b :=
    happ.trans (hcomp.trans (congrArg
      (ModuleCat.ofHom (LinearMap.range E.differential).mkQ) hiz))
  have hinvhom := ConcreteCategory.congr_hom
    (LinearTwoTermComplex.homologyZeroIsoCoker E).hom_inv_id
    (E.toCochainComplex.homologyπ 0 z)
  simp only [CategoryTheory.comp_apply] at hinvhom
  exact hinvhom.symm.trans (congrArg (LinearTwoTermComplex.homologyZeroIsoCoker E).inv hc)

section MainTheorem

variable {K' K K'' : LinearTwoTermComplex R} {ι : LinearTwoTermComplex.Hom K' K}
  {π : LinearTwoTermComplex.Hom K K''} (h : PicardCriteria.ShortExact ι π)

/-- **The connecting map of two-term complexes agrees with Mathlib's connecting
homomorphism.** For a degreewise short exact sequence `0 → K' → K → K'' → 0` of two-term
complexes, the repository's connecting map `h.delta : h⁰(K'') → h¹(K')` agrees, under the
identification of `h⁰`/`h¹` with the cohomology of the cochain realizations
(`homologyNegOneIsoKer`, `homologyZeroIsoCoker`), with Mathlib's connecting homomorphism
`h.cochainShortExact.δ (-1) 0` of the associated short exact sequence of cochain complexes. -/
theorem delta_eq_δ (c : PicardCriteria.h0 K'') :
    (LinearTwoTermComplex.homologyZeroIsoCoker K').hom
      (h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))
        ((LinearTwoTermComplex.homologyNegOneIsoKer K'').inv c)) = h.delta c := by
  obtain ⟨b, a, ha, hb⟩ := h.exists_delta_lift c
  have hij : (ComplexShape.up ℤ).Rel (-1) 0 := ComplexShape.up_mk (-1) 0 (by norm_num)
  have hk : (ComplexShape.up ℤ).next 0 = (1 : ℤ) := by rw [CochainComplex.next]; norm_num
  have hjc : (ComplexShape.up ℤ).next (-1) = (0 : ℤ) := ComplexShape.next_eq' _ hij
  have hx3 : (h.cochainShortComplex.X₃.d (-1) 0) (c : K''.degreeZero) = 0 := by
    change K''.toCochainComplex.d (-1) 0 (c : K''.degreeZero) = 0
    rw [LinearTwoTermComplex.toCochainComplex_d_negOne_zero]
    exact c.2
  have hx2 : (h.cochainShortComplex.g.f (-1)) a = (c : K''.degreeZero) := by
    change (LinearTwoTermComplex.toCochainComplexHom π).f (-1) a = (c : K''.degreeZero)
    rw [LinearTwoTermComplex.toCochainComplexHom_f,
      LinearTwoTermComplex.cochainHomComponent_negOne]
    exact ha
  have hx1 : (h.cochainShortComplex.f.f 0) b = (h.cochainShortComplex.X₂.d (-1) 0) a := by
    change (LinearTwoTermComplex.toCochainComplexHom ι).f 0 b = K.toCochainComplex.d (-1) 0 a
    rw [LinearTwoTermComplex.toCochainComplexHom_f, LinearTwoTermComplex.cochainHomComponent_zero,
      LinearTwoTermComplex.toCochainComplex_d_negOne_zero]
    exact hb
  have hx1' : (h.cochainShortComplex.X₁.d 0 1) b = 0 := by
    have hd0 : h.cochainShortComplex.X₁.d 0 1 = 0 := by
      apply (LinearTwoTermComplex.toCochainComplex_X_isZero K' 1 (by norm_num)
        (by norm_num)).eq_of_tgt
    rw [hd0]
    rfl
  have key : h.cochainShortExact.δ (-1) 0 hij
      (K''.toCochainComplex.homologyπ (-1)
        (K''.toCochainComplex.cyclesMk (c : K''.degreeZero) 0 hjc hx3)) =
      K'.toCochainComplex.homologyπ 0 (K'.toCochainComplex.cyclesMk b 1 hk hx1') :=
    CategoryTheory.ShortComplex.ShortExact.δ_apply h.cochainShortExact (-1) 0 hij
      (c : K''.degreeZero) hx3 a hx2 b hx1 1 hk
  have hA := homologyπ_cyclesMk_eq_homologyNegOneIsoKer_inv K'' c hjc hx3
  have hB := homologyπ_cyclesMk_eq_homologyZeroIsoCoker_inv K' b hk hx1'
  have key2 : h.cochainShortExact.δ (-1) 0 hij
      ((LinearTwoTermComplex.homologyNegOneIsoKer K'').inv c) =
      (LinearTwoTermComplex.homologyZeroIsoCoker K').inv (PicardCriteria.h1mk K' b) :=
    ((congrArg (h.cochainShortExact.δ (-1) 0 hij) hA).symm.trans key).trans hB
  have hhomInv := ConcreteCategory.congr_hom
    (LinearTwoTermComplex.homologyZeroIsoCoker K').inv_hom_id (PicardCriteria.h1mk K' b)
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hhomInv
  rw [key2, hhomInv, PicardCriteria.ShortExact.delta_apply,
    PicardCriteria.ShortExact.deltaFun_eq h c ha hb]

/-- **The comparison is usable**: the repository's connecting map `h.delta` is injective
exactly when Mathlib's connecting homomorphism `h.cochainShortExact.δ (-1) 0` is. Combined with
`PicardCriteria.exact_h1_left` (`ker (h¹(ι)) = range h.delta`) this identifies the exactness of
the repository's six-term sequence at `h¹(K')` with the exactness of Mathlib's homology long
exact sequence (`ShortComplex.ShortExact.homology_exact₃`) at the corresponding spot. -/
theorem injective_delta_iff :
    Function.Injective h.delta ↔
      Function.Injective (h.cochainShortExact.δ (-1) 0
        (ComplexShape.up_mk (-1) 0 (by norm_num))) := by
  set hij : (ComplexShape.up ℤ).Rel (-1) 0 := ComplexShape.up_mk (-1) 0 (by norm_num) with hijdef
  set homHom := (LinearTwoTermComplex.homologyNegOneIsoKer K'').hom with homHomdef
  set homInv := (LinearTwoTermComplex.homologyNegOneIsoKer K'').inv with homInvdef
  set cokHom := (LinearTwoTermComplex.homologyZeroIsoCoker K').hom with cokHomdef
  have hLeftInv1 : Function.LeftInverse homInv homHom := fun x => by
    have hthis := ConcreteCategory.congr_hom
      (LinearTwoTermComplex.homologyNegOneIsoKer K'').hom_inv_id x
    simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hthis
    exact hthis
  have hLeftInv2 : Function.LeftInverse homHom homInv := fun x => by
    have hthis := ConcreteCategory.congr_hom
      (LinearTwoTermComplex.homologyNegOneIsoKer K'').inv_hom_id x
    simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hthis
    exact hthis
  have hBijHomInv : Function.Bijective homInv := ⟨hLeftInv2.injective, hLeftInv1.surjective⟩
  have hInjCok : Function.Injective cokHom := by
    have hL : Function.LeftInverse (LinearTwoTermComplex.homologyZeroIsoCoker K').inv cokHom :=
      fun x => by
        have hthis := ConcreteCategory.congr_hom
          (LinearTwoTermComplex.homologyZeroIsoCoker K').hom_inv_id x
        simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hthis
        exact hthis
    exact hL.injective
  have hfun : h.delta = cokHom ∘ (h.cochainShortExact.δ (-1) 0 hij) ∘ homInv :=
    funext fun c => (delta_eq_δ h c).symm
  rw [hfun]
  rw [Function.Injective.of_comp_iff hInjCok]
  exact Function.Injective.of_comp_iff' _ hBijHomInv

end MainTheorem

end GromovWitten.AlgebraicGeometry
