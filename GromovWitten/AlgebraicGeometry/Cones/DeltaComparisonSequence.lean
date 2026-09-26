/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Cones.DeltaComparison
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Exact.Basic

/-!
# The full six-term correspondence with Mathlib's homology sequence

`Cones/DeltaComparison.lean` identifies the repository's connecting map
`PicardCriteria.ShortExact.delta` with Mathlib's connecting homomorphism
`ShortComplex.ShortExact.δ` of the cochain realization of a degreewise short exact sequence of
two-term complexes. This file extends the comparison to the whole six-term exact sequence: each
of the six exactness statements of `Cones/Criteria.lean`'s `PicardCriteria.ShortExact` namespace
(`injective_kernelMap`, `exact_h0_middle`, `exact_h0_right`, `exact_h1_left`, `exact_h1_middle`,
`surjective_cokernelMap`) is shown equivalent to the corresponding piece of Mathlib's long exact
homology sequence (`ShortComplex.ShortExact.homology_exact₁/₂/₃` of
`Mathlib.Algebra.Homology.HomologySequence`) for `h.cochainShortExact`, transported through the
identifications `LinearTwoTermComplex.homologyNegOneIsoKer`/`homologyZeroIsoCoker`.

## Main results

* `LinearTwoTermComplex.kerLinearEquiv`, `LinearTwoTermComplex.cokerLinearEquiv`: the linear
  equivalences underlying `homologyNegOneIsoKer`/`homologyZeroIsoCoker`.
* `LinearTwoTermComplex.kerLinearEquiv_naturality`,
  `LinearTwoTermComplex.cokerLinearEquiv_naturality`: these identifications are natural in the
  chain map, i.e. intertwine `HomologicalComplex.homologyMap` of the cochain realization with
  `Hom.kernelMap`/`Hom.cokernelMap`.
* `PicardCriteria.ShortExact.exact_h0_middle_iff`, `exact_h0_right_iff`, `exact_h1_left_iff`,
  `exact_h1_middle_iff`, `injective_kernelMap_iff`, `surjective_cokernelMap_iff`: the six
  equivalences between the repository's exactness statements and the corresponding
  `Function.Exact`/`Function.Injective`/`Function.Surjective` statements about the homology of
  the cochain realizations.
* `PicardCriteria.ShortExact.homology_exact_sequence`: **the main theorem.** The repository's
  six-term exact sequence `h⁰(K') → h⁰(K) → h⁰(K'') → h¹(K') → h¹(K) → h¹(K'')` is literally the
  image, under the above identifications, of Mathlib's long exact homology sequence of
  `h.cochainShortExact` in cohomological degrees `-1` and `0`.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {E F : LinearTwoTermComplex R}

/-- The linear equivalence underlying `homologyNegOneIsoKer`: the homology of the cochain
realization of a two-term complex in degree `-1` is linearly equivalent to `h⁰`. -/
noncomputable def LinearTwoTermComplex.kerLinearEquiv (E : LinearTwoTermComplex R) :
    E.toCochainComplex.homology (-1) ≃ₗ[R] PicardCriteria.h0 E :=
  (LinearTwoTermComplex.homologyNegOneIsoKer E).toLinearEquiv

/-- The linear equivalence underlying `homologyZeroIsoCoker`: the homology of the cochain
realization of a two-term complex in degree `0` is linearly equivalent to `h¹`. -/
noncomputable def LinearTwoTermComplex.cokerLinearEquiv (E : LinearTwoTermComplex R) :
    E.toCochainComplex.homology 0 ≃ₗ[R] PicardCriteria.h1 E :=
  (LinearTwoTermComplex.homologyZeroIsoCoker E).toLinearEquiv

/-- `kerLinearEquiv` acts by `homologyNegOneIsoKer.hom`. -/
@[simp]
theorem LinearTwoTermComplex.kerLinearEquiv_apply (E : LinearTwoTermComplex R)
    (x : E.toCochainComplex.homology (-1)) :
    LinearTwoTermComplex.kerLinearEquiv E x = (LinearTwoTermComplex.homologyNegOneIsoKer E).hom x :=
  rfl

/-- `cokerLinearEquiv` acts by `homologyZeroIsoCoker.hom`. -/
@[simp]
theorem LinearTwoTermComplex.cokerLinearEquiv_apply (E : LinearTwoTermComplex R)
    (x : E.toCochainComplex.homology 0) :
    LinearTwoTermComplex.cokerLinearEquiv E x =
      (LinearTwoTermComplex.homologyZeroIsoCoker E).hom x :=
  rfl

/-- The inverse of `kerLinearEquiv` acts by `homologyNegOneIsoKer.inv`. -/
@[simp]
theorem LinearTwoTermComplex.kerLinearEquiv_symm_apply (E : LinearTwoTermComplex R)
    (a : PicardCriteria.h0 E) :
    (LinearTwoTermComplex.kerLinearEquiv E).symm a =
      (LinearTwoTermComplex.homologyNegOneIsoKer E).inv a :=
  rfl

/-- The inverse of `cokerLinearEquiv` acts by `homologyZeroIsoCoker.inv`. -/
@[simp]
theorem LinearTwoTermComplex.cokerLinearEquiv_symm_apply (E : LinearTwoTermComplex R)
    (b : PicardCriteria.h1 E) :
    (LinearTwoTermComplex.cokerLinearEquiv E).symm b =
      (LinearTwoTermComplex.homologyZeroIsoCoker E).inv b :=
  rfl

/-- **Naturality of `kerLinearEquiv`.** The identification of the homology of the cochain
realization in degree `-1` with `h⁰` intertwines `HomologicalComplex.homologyMap` of the cochain
realization of a chain map with the induced map `Hom.kernelMap` on `h⁰`. -/
theorem LinearTwoTermComplex.kerLinearEquiv_naturality (f : LinearTwoTermComplex.Hom E F)
    (x : E.toCochainComplex.homology (-1)) :
    LinearTwoTermComplex.kerLinearEquiv F
      (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom f) (-1) x) =
      f.kernelMap (LinearTwoTermComplex.kerLinearEquiv E x) := by
  change (LinearTwoTermComplex.homologyNegOneIsoKer F).hom
      (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom f) (-1) x) =
      f.kernelMap ((LinearTwoTermComplex.homologyNegOneIsoKer E).hom x)
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (E.toCochainComplex.homologyπ (-1))).1
    inferInstance x
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (LinearTwoTermComplex.toCochainComplexHom f) (-1)) z
  simp only [CategoryTheory.comp_apply] at hnat
  rw [hnat]
  have hF := ConcreteCategory.congr_hom (homologyπ_comp_homologyNegOneIsoKer_hom F)
    (HomologicalComplex.cyclesMap (LinearTwoTermComplex.toCochainComplexHom f) (-1) z)
  simp only [CategoryTheory.comp_apply] at hF
  have hF' : ((LinearTwoTermComplex.homologyNegOneIsoKer F).hom
      (F.toCochainComplex.homologyπ (-1)
        (HomologicalComplex.cyclesMap (LinearTwoTermComplex.toCochainComplexHom f) (-1) z)) :
      F.degreeZero) =
      F.toCochainComplex.iCycles (-1)
        (HomologicalComplex.cyclesMap (LinearTwoTermComplex.toCochainComplexHom f) (-1) z) := hF
  have hE := ConcreteCategory.congr_hom (homologyπ_comp_homologyNegOneIsoKer_hom E) z
  simp only [CategoryTheory.comp_apply] at hE
  have hE' : ((LinearTwoTermComplex.homologyNegOneIsoKer E).hom
      (E.toCochainComplex.homologyπ (-1) z) : E.degreeZero) =
      E.toCochainComplex.iCycles (-1) z := hE
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (LinearTwoTermComplex.toCochainComplexHom f) (-1)) z
  simp only [CategoryTheory.comp_apply] at hi
  rw [LinearTwoTermComplex.toCochainComplexHom_f,
    LinearTwoTermComplex.cochainHomComponent_negOne] at hi
  have hi' : F.toCochainComplex.iCycles (-1)
      (HomologicalComplex.cyclesMap (LinearTwoTermComplex.toCochainComplexHom f) (-1) z) =
      f.degreeZero (E.toCochainComplex.iCycles (-1) z) := hi
  apply Subtype.ext
  rw [PicardCriteria.kernelMap_coe, hE', ← hi', hF']

/-- **Naturality of `cokerLinearEquiv`.** The identification of the homology of the cochain
realization in degree `0` with `h¹` intertwines `HomologicalComplex.homologyMap` of the cochain
realization of a chain map with the induced map `Hom.cokernelMap` on `h¹`. -/
theorem LinearTwoTermComplex.cokerLinearEquiv_naturality (f : LinearTwoTermComplex.Hom E F)
    (x : E.toCochainComplex.homology 0) :
    LinearTwoTermComplex.cokerLinearEquiv F
      (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom f) 0 x) =
      f.cokernelMap (LinearTwoTermComplex.cokerLinearEquiv E x) := by
  change (LinearTwoTermComplex.homologyZeroIsoCoker F).hom
      (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom f) 0 x) =
      f.cokernelMap ((LinearTwoTermComplex.homologyZeroIsoCoker E).hom x)
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (E.toCochainComplex.homologyπ 0)).1
    inferInstance x
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (LinearTwoTermComplex.toCochainComplexHom f) 0) z
  simp only [CategoryTheory.comp_apply] at hnat
  rw [hnat]
  have hF := ConcreteCategory.congr_hom (homologyπ_comp_homologyZeroIsoCoker_hom F)
    (HomologicalComplex.cyclesMap (LinearTwoTermComplex.toCochainComplexHom f) 0 z)
  simp only [CategoryTheory.comp_apply] at hF
  have hE := ConcreteCategory.congr_hom (homologyπ_comp_homologyZeroIsoCoker_hom E) z
  simp only [CategoryTheory.comp_apply] at hE
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (LinearTwoTermComplex.toCochainComplexHom f) 0) z
  simp only [CategoryTheory.comp_apply] at hi
  rw [LinearTwoTermComplex.toCochainComplexHom_f,
    LinearTwoTermComplex.cochainHomComponent_zero] at hi
  have hi' : F.toCochainComplex.iCycles 0
      (HomologicalComplex.cyclesMap (LinearTwoTermComplex.toCochainComplexHom f) 0 z) =
      f.degreeOne (E.toCochainComplex.iCycles 0 z) := hi
  have hcompF : (F.toCochainComplex.iCycles 0 ≫
      ModuleCat.ofHom (LinearMap.range F.differential).mkQ)
      (HomologicalComplex.cyclesMap (LinearTwoTermComplex.toCochainComplexHom f) 0 z) =
      PicardCriteria.h1mk F (F.toCochainComplex.iCycles 0
        (HomologicalComplex.cyclesMap (LinearTwoTermComplex.toCochainComplexHom f) 0 z)) := rfl
  have hcompE : (E.toCochainComplex.iCycles 0 ≫
      ModuleCat.ofHom (LinearMap.range E.differential).mkQ) z =
      PicardCriteria.h1mk E (E.toCochainComplex.iCycles 0 z) := rfl
  have hF' := hF.trans hcompF
  have hE' := hE.trans hcompE
  rw [hF', hi', hE']
  exact (PicardCriteria.cokernelMap_h1mk f _).symm

/-- Naturality of `kerLinearEquiv`, conjugated by the inverse equivalences on both sides: the
form needed to build a ladder of linear equivalences with Mathlib's `Function.Exact`. -/
theorem LinearTwoTermComplex.kerLinearEquiv_symm_naturality (f : LinearTwoTermComplex.Hom E F)
    (a : PicardCriteria.h0 E) :
    HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom f) (-1)
        ((LinearTwoTermComplex.kerLinearEquiv E).symm a) =
      (LinearTwoTermComplex.kerLinearEquiv F).symm (f.kernelMap a) := by
  have hx := LinearTwoTermComplex.kerLinearEquiv_naturality f
    ((LinearTwoTermComplex.kerLinearEquiv E).symm a)
  rw [LinearEquiv.apply_symm_apply] at hx
  rw [← hx, LinearEquiv.symm_apply_apply]

/-- Naturality of `cokerLinearEquiv`, conjugated by the inverse equivalences on both sides. -/
theorem LinearTwoTermComplex.cokerLinearEquiv_symm_naturality (f : LinearTwoTermComplex.Hom E F)
    (a : PicardCriteria.h1 E) :
    HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom f) 0
        ((LinearTwoTermComplex.cokerLinearEquiv E).symm a) =
      (LinearTwoTermComplex.cokerLinearEquiv F).symm (f.cokernelMap a) := by
  have hx := LinearTwoTermComplex.cokerLinearEquiv_naturality f
    ((LinearTwoTermComplex.cokerLinearEquiv E).symm a)
  rw [LinearEquiv.apply_symm_apply] at hx
  rw [← hx, LinearEquiv.symm_apply_apply]

/-- The `LinearMap`-composite form of `kerLinearEquiv_symm_naturality`, as needed by
`Function.Exact.iff_of_ladder_linearEquiv`. -/
theorem LinearTwoTermComplex.kerLinearEquiv_symm_naturality_linearMap
    (f : LinearTwoTermComplex.Hom E F) :
    (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom f) (-1)).hom.comp
        (LinearTwoTermComplex.kerLinearEquiv E).symm.toLinearMap =
      (LinearTwoTermComplex.kerLinearEquiv F).symm.toLinearMap.comp f.kernelMap :=
  LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    exact LinearTwoTermComplex.kerLinearEquiv_symm_naturality f a

/-- The `LinearMap`-composite form of `cokerLinearEquiv_symm_naturality`. -/
theorem LinearTwoTermComplex.cokerLinearEquiv_symm_naturality_linearMap
    (f : LinearTwoTermComplex.Hom E F) :
    (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom f) 0).hom.comp
        (LinearTwoTermComplex.cokerLinearEquiv E).symm.toLinearMap =
      (LinearTwoTermComplex.cokerLinearEquiv F).symm.toLinearMap.comp f.cokernelMap :=
  LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    exact LinearTwoTermComplex.cokerLinearEquiv_symm_naturality f a

section MainTheorem

variable {K' K K'' : LinearTwoTermComplex R} {ι : LinearTwoTermComplex.Hom K' K}
  {π : LinearTwoTermComplex.Hom K K''}

/-- **Exactness at `h⁰(K)`, compared to Mathlib.** The repository's exactness statement
`exact_h0_middle` (`ker π.kernelMap = range ι.kernelMap`) is equivalent to `Function.Exact`
of the two induced maps on the homology, in degree `-1`, of the cochain realizations of `ι`
and `π`. -/
theorem PicardCriteria.ShortExact.exact_h0_middle_iff (_h : PicardCriteria.ShortExact ι π) :
    LinearMap.ker π.kernelMap = LinearMap.range ι.kernelMap ↔
      Function.Exact
        (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom ι) (-1)).hom
        (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom π) (-1)).hom := by
  rw [← LinearMap.exact_iff,
    Function.Exact.iff_of_ladder_linearEquiv
      (LinearTwoTermComplex.kerLinearEquiv_symm_naturality_linearMap ι)
      (LinearTwoTermComplex.kerLinearEquiv_symm_naturality_linearMap π)]

/-- **Exactness at `h¹(K)`, compared to Mathlib.** The repository's exactness statement
`exact_h1_middle` (`ker π.cokernelMap = range ι.cokernelMap`) is equivalent to `Function.Exact`
of the two induced maps on the homology, in degree `0`, of the cochain realizations of `ι`
and `π`. -/
theorem PicardCriteria.ShortExact.exact_h1_middle_iff (_h : PicardCriteria.ShortExact ι π) :
    LinearMap.ker π.cokernelMap = LinearMap.range ι.cokernelMap ↔
      Function.Exact
        (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom ι) 0).hom
        (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom π) 0).hom := by
  rw [← LinearMap.exact_iff,
    Function.Exact.iff_of_ladder_linearEquiv
      (LinearTwoTermComplex.cokerLinearEquiv_symm_naturality_linearMap ι)
      (LinearTwoTermComplex.cokerLinearEquiv_symm_naturality_linearMap π)]

/-- **Naturality of `delta`, conjugated by the inverse equivalences.** The elementwise
connecting map `h.delta` intertwines Mathlib's connecting homomorphism `h.cochainShortExact.δ`
with the identifications `kerLinearEquiv`/`cokerLinearEquiv`. -/
theorem PicardCriteria.ShortExact.delta_symm_naturality (h : PicardCriteria.ShortExact ι π)
    (c : PicardCriteria.h0 K'') :
    h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))
        ((LinearTwoTermComplex.kerLinearEquiv K'').symm c) =
      (LinearTwoTermComplex.cokerLinearEquiv K').symm (h.delta c) := by
  have hx : LinearTwoTermComplex.cokerLinearEquiv K'
      (h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))
        ((LinearTwoTermComplex.kerLinearEquiv K'').symm c)) = h.delta c :=
    delta_eq_δ h c
  exact (LinearEquiv.symm_apply_apply (LinearTwoTermComplex.cokerLinearEquiv K') _).symm.trans
    (congrArg (LinearTwoTermComplex.cokerLinearEquiv K').symm hx)

/-- **Exactness at `h¹(K')`, compared to Mathlib.** The repository's exactness statement
`exact_h1_left` (`ker ι.cokernelMap = range h.delta`) is equivalent to `Function.Exact` of
Mathlib's connecting homomorphism followed by the induced map on homology, in degree `0`, of
the cochain realization of `ι`. -/
theorem PicardCriteria.ShortExact.exact_h1_left_iff (h : PicardCriteria.ShortExact ι π) :
    LinearMap.ker ι.cokernelMap = LinearMap.range h.delta ↔
      Function.Exact
        (h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))).hom
        (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom ι) 0).hom := by
  have hrepo := h.exact_h1_left
  refine ⟨fun _ y => ?_, fun _ => hrepo⟩
  have hker : (HomologicalComplex.homologyMap
      (LinearTwoTermComplex.toCochainComplexHom ι) 0).hom y = 0 ↔
      ι.cokernelMap (LinearTwoTermComplex.cokerLinearEquiv K' y) = 0 := by
    constructor
    · intro hy
      have hnat := LinearTwoTermComplex.cokerLinearEquiv_naturality ι y
      rw [hy, map_zero] at hnat
      exact hnat.symm
    · intro hy
      have hnat := LinearTwoTermComplex.cokerLinearEquiv_naturality ι y
      rw [hy] at hnat
      exact (LinearTwoTermComplex.cokerLinearEquiv K).injective (hnat.trans (map_zero _).symm)
  rw [hker, ← LinearMap.mem_ker, hrepo, LinearMap.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(LinearTwoTermComplex.kerLinearEquiv K'').symm c, ?_⟩
    have := h.delta_symm_naturality c
    rw [hc] at this
    exact this.trans (LinearEquiv.symm_apply_apply _ _)
  · rintro ⟨z, hz⟩
    refine ⟨LinearTwoTermComplex.kerLinearEquiv K'' z, ?_⟩
    have hzz : (LinearTwoTermComplex.kerLinearEquiv K'').symm
        (LinearTwoTermComplex.kerLinearEquiv K'' z) = z :=
      LinearEquiv.symm_apply_apply _ _
    have hx := h.delta_symm_naturality (LinearTwoTermComplex.kerLinearEquiv K'' z)
    have hstep : h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num)) z =
        h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))
          ((LinearTwoTermComplex.kerLinearEquiv K'').symm
            (LinearTwoTermComplex.kerLinearEquiv K'' z)) :=
      congrArg (fun w =>
        h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num)) w) hzz.symm
    have hx' : (h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))).hom z =
        (LinearTwoTermComplex.cokerLinearEquiv K').symm
          (h.delta (LinearTwoTermComplex.kerLinearEquiv K'' z)) :=
      hstep.trans hx
    exact (LinearEquiv.symm_apply_eq _).mp (hx'.symm.trans hz)

/-- **Exactness at `h⁰(K'')`, compared to Mathlib.** The repository's exactness statement
`exact_h0_right` (`ker h.delta = range π.kernelMap`) is equivalent to `Function.Exact` of the
induced map on homology, in degree `-1`, of the cochain realization of `π`, followed by
Mathlib's connecting homomorphism. -/
theorem PicardCriteria.ShortExact.exact_h0_right_iff (h : PicardCriteria.ShortExact ι π) :
    LinearMap.ker h.delta = LinearMap.range π.kernelMap ↔
      Function.Exact
        (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom π) (-1)).hom
        (h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))).hom := by
  have hrepo := h.exact_h0_right
  refine ⟨fun _ y => ?_, fun _ => hrepo⟩
  set c := LinearTwoTermComplex.kerLinearEquiv K'' y with hc
  have hcy : (LinearTwoTermComplex.kerLinearEquiv K'').symm c = y :=
    LinearEquiv.symm_apply_apply (LinearTwoTermComplex.kerLinearEquiv K'') y
  have hδ : LinearTwoTermComplex.cokerLinearEquiv K'
      ((h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))).hom y) =
      h.delta c := by
    have hx := delta_eq_δ h c
    have hstep : h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num)) y =
        h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))
          ((LinearTwoTermComplex.kerLinearEquiv K'').symm c) :=
      congrArg (fun w =>
        h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num)) w) hcy.symm
    exact (congrArg (LinearTwoTermComplex.cokerLinearEquiv K') hstep).trans hx
  have hker : (h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))).hom y = 0 ↔
      h.delta c = 0 := by
    constructor
    · intro hy
      have hzero : LinearTwoTermComplex.cokerLinearEquiv K'
          ((h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))).hom y) = 0 := by
        rw [hy]; exact map_zero _
      exact hδ.symm.trans hzero
    · intro hy
      have hzero : LinearTwoTermComplex.cokerLinearEquiv K'
          ((h.cochainShortExact.δ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))).hom y) = 0 := by
        rw [hδ, hy]
      exact (LinearEquiv.map_eq_zero_iff
        (e := LinearTwoTermComplex.cokerLinearEquiv K')).mp hzero
  rw [hker, ← LinearMap.mem_ker, hrepo, LinearMap.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(LinearTwoTermComplex.kerLinearEquiv K).symm a, ?_⟩
    have := LinearTwoTermComplex.kerLinearEquiv_symm_naturality π a
    rw [ha, hc, LinearEquiv.symm_apply_apply] at this
    exact this
  · rintro ⟨x, hx⟩
    refine ⟨LinearTwoTermComplex.kerLinearEquiv K x, ?_⟩
    have := LinearTwoTermComplex.kerLinearEquiv_naturality π x
    rw [hx] at this
    exact this.symm

/-- **Exactness at `h⁰(K')`, compared to Mathlib.** The repository's exactness statement
`injective_kernelMap` is equivalent to injectivity of the induced map on homology, in degree
`-1`, of the cochain realization of `ι`. -/
theorem PicardCriteria.ShortExact.injective_kernelMap_iff (_h : PicardCriteria.ShortExact ι π) :
    Function.Injective ι.kernelMap ↔
      Function.Injective
        (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom ι) (-1)).hom := by
  have heq : (LinearTwoTermComplex.kerLinearEquiv K).toLinearMap.comp
      (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom ι) (-1)).hom =
      ι.kernelMap.comp (LinearTwoTermComplex.kerLinearEquiv K').toLinearMap :=
    LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      exact LinearTwoTermComplex.kerLinearEquiv_naturality ι x
  constructor
  · intro hinj
    have h1 : Function.Injective (⇑(ι.kernelMap.comp
        (LinearTwoTermComplex.kerLinearEquiv K').toLinearMap)) := by
      simp only [LinearMap.coe_comp]
      exact hinj.comp (LinearTwoTermComplex.kerLinearEquiv K').injective
    rw [← heq] at h1
    simp only [LinearMap.coe_comp] at h1
    exact h1.of_comp
  · intro hinj
    have h1 : Function.Injective
        (⇑((LinearTwoTermComplex.kerLinearEquiv K).toLinearMap.comp
          (HomologicalComplex.homologyMap
            (LinearTwoTermComplex.toCochainComplexHom ι) (-1)).hom)) := by
      simp only [LinearMap.coe_comp]
      exact (LinearTwoTermComplex.kerLinearEquiv K).injective.comp hinj
    rw [heq] at h1
    simp only [LinearMap.coe_comp] at h1
    exact h1.of_comp_right (LinearTwoTermComplex.kerLinearEquiv K').surjective

/-- **Exactness at `h¹(K'')`, compared to Mathlib.** The repository's exactness statement
`surjective_cokernelMap` is equivalent to surjectivity of the induced map on homology, in
degree `0`, of the cochain realization of `π`. -/
theorem PicardCriteria.ShortExact.surjective_cokernelMap_iff (_h : PicardCriteria.ShortExact ι π) :
    Function.Surjective π.cokernelMap ↔
      Function.Surjective
        (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom π) 0).hom := by
  have heq : (LinearTwoTermComplex.cokerLinearEquiv K'').toLinearMap.comp
      (HomologicalComplex.homologyMap (LinearTwoTermComplex.toCochainComplexHom π) 0).hom =
      π.cokernelMap.comp (LinearTwoTermComplex.cokerLinearEquiv K).toLinearMap :=
    LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      exact LinearTwoTermComplex.cokerLinearEquiv_naturality π x
  constructor
  · intro hsurj
    have h1 : Function.Surjective (⇑(π.cokernelMap.comp
        (LinearTwoTermComplex.cokerLinearEquiv K).toLinearMap)) := by
      simp only [LinearMap.coe_comp]
      exact hsurj.comp (LinearTwoTermComplex.cokerLinearEquiv K).surjective
    rw [← heq] at h1
    simp only [LinearMap.coe_comp] at h1
    exact h1.of_comp_left (LinearTwoTermComplex.cokerLinearEquiv K'').injective
  · intro hsurj
    have h1 : Function.Surjective
        (⇑((LinearTwoTermComplex.cokerLinearEquiv K'').toLinearMap.comp
          (HomologicalComplex.homologyMap
            (LinearTwoTermComplex.toCochainComplexHom π) 0).hom)) := by
      simp only [LinearMap.coe_comp]
      exact (LinearTwoTermComplex.cokerLinearEquiv K'').surjective.comp hsurj
    rw [heq] at h1
    simp only [LinearMap.coe_comp] at h1
    exact h1.of_comp

/-- **The main theorem: the repository's six-term exact sequence is the image of Mathlib's
long exact homology sequence.** Each of the four "middle" exactness statements of
`PicardCriteria.ShortExact` (`Cones/Criteria.lean`) is derived here from the corresponding piece
of Mathlib's long exact homology sequence of `h.cochainShortExact`
(`ShortComplex.ShortExact.homology_exact₁/₂/₃` of `Mathlib.Algebra.Homology.HomologySequence`,
converted to `Function.Exact` via `ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`),
transported through `kerLinearEquiv`/`cokerLinearEquiv`. Combined with `injective_kernelMap_iff`
and `surjective_cokernelMap_iff` (the two endpoints), this identifies every one of the six
exactness statements of the repository's sequence with Mathlib's homology long exact sequence in
cohomological degrees `-1` and `0`. -/
theorem PicardCriteria.ShortExact.homology_exact_sequence (h : PicardCriteria.ShortExact ι π) :
    LinearMap.ker π.kernelMap = LinearMap.range ι.kernelMap ∧
      LinearMap.ker h.delta = LinearMap.range π.kernelMap ∧
      LinearMap.ker ι.cokernelMap = LinearMap.range h.delta ∧
      LinearMap.ker π.cokernelMap = LinearMap.range ι.cokernelMap :=
  ⟨h.exact_h0_middle_iff.2
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (h.cochainShortExact.homology_exact₂ (-1))),
    h.exact_h0_right_iff.2
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (h.cochainShortExact.homology_exact₃ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num)))),
    h.exact_h1_left_iff.2
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (h.cochainShortExact.homology_exact₁ (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num)))),
    h.exact_h1_middle_iff.2
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (h.cochainShortExact.homology_exact₂ 0))⟩

end MainTheorem

end GromovWitten.AlgebraicGeometry
