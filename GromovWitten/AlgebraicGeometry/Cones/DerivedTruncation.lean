/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.DerivedCriteria

/-!
# `h¹/h⁰` by two-term truncation

`Cones/DerivedPicard.lean` attaches the Picard groupoid `h¹/h⁰` to a *two-term* complex.  This
file extends the construction to an arbitrary cochain complex of modules by truncation, and
proves that the result only depends on the class of the complex in the derived category.

## Main results

* `LinearTwoTermComplex.twoTermTrunc K = [K⁻¹/im d⁻² → K⁰]`, functorial in chain maps
  (`twoTermTruncHom`, `twoTermTruncFunctor`), with the projection `truncProjection K` from `K`
  onto the cochain realization of the truncation (`truncProjection_naturality`).
* `LinearTwoTermComplex.quasiIsoAt_truncProjection_negOne`: that projection is a
  quasi-isomorphism in degree `-1`, unconditionally, and
  `quasiIsoAt_truncProjection_zero` says the same in degree `0` as soon as `K.d 0 1 = 0`.
  Consequently `homologyNegOneIsoTrunc : H⁻¹(K) ≅ h⁰(twoTermTrunc K)` and
  `homologyZeroIsoTrunc : H⁰(K) ≅ h¹(twoTermTrunc K)`.  The hypothesis in degree `0` is
  necessary: `h¹` of the truncation is the cokernel of `d⁻¹`, which is `H⁰(K)` only when there
  is no differential out of degree `0`.
* `LinearTwoTermComplex.isQuasiIsomorphism_twoTermTruncHom` and `truncQuotientEquivalence`: a
  chain map which is a quasi-isomorphism in degrees `-1` and `0` truncates to an elementwise
  quasi-isomorphism, hence induces an equivalence of the Picard groupoids;
  `nonempty_truncQuotientEquivalence_of_roof` is the version for a roof of quasi-isomorphisms.
* `LinearTwoTermComplex.ofHomotopyTrunc`: a homotopy of chain maps descends to a chain homotopy
  of the truncations whenever the source has no differential out of degree `0` — no hypothesis
  on the target is needed, the component `K⁻¹ ⟶ L⁻²` being killed by the quotient;
  `ofHomotopyEquivTrunc` is the resulting homotopy equivalence of truncations.
* `TruncPresentation E`: a K-projective complex with `d⁰ = 0` representing a derived object `E`,
  with `TruncPresentation.picard` its Picard groupoid and
  `TruncPresentation.nonempty_picardEquivalence` the **independence of the presentation**
  (proved by realizing the comparison isomorphism by a chain map, as K-projectivity allows).
  `TruncPresentation.ofProjective` builds a presentation from a bounded-above complex of
  projectives.
* `CotangentComplex.PerfectComplex.GlobalTwoTermResolution.truncPresentation` and
  `nonempty_picardEquivalence_truncPresentation`: the truncation construction agrees with the
  two-term construction of `Cones/DerivedPicard.lean`.

Residual hypotheses: independence of the representative is proved for K-projective complexes
with no differential out of degree `0` (the case of interest for cotangent complexes).  For
arbitrary representatives one would have to represent an isomorphism of the derived category by
a roof of quasi-isomorphisms and truncate the intermediate complex;
`nonempty_truncQuotientEquivalence_of_roof` is the statement one would feed with such a roof.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace GromovWitten.AlgebraicGeometry

namespace LinearTwoTermComplex

variable {R : Type u} [CommRing R]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

/-! ## The two-term truncation of a cochain complex -/

/-- The two-term truncation of a cochain complex of modules: the term in degree `-1` modulo the
boundaries coming from degree `-2`, mapping to the term in degree `0` by the induced
differential.  Its `h⁰` is `H⁻¹(K)` and, when `K` has no differential out of degree `0`, its
`h¹` is `H⁰(K)`. -/
abbrev twoTermTrunc (K : CochainComplex (ModuleCat.{u} R) ℤ) : LinearTwoTermComplex R where
  degreeZero := K.X (-1) ⧸ (LinearMap.range (K.d (-2) (-1)).hom : Submodule R (K.X (-1)))
  degreeOne := K.X 0
  differential := Submodule.liftQ _ (K.d (-1) 0).hom (by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact congrArg (fun m : K.X (-2) ⟶ K.X 0 => (ModuleCat.Hom.hom m) x)
      (K.d_comp_d (-2) (-1) 0))

@[simp]
theorem twoTermTrunc_differential_mk (K : CochainComplex (ModuleCat.{u} R) ℤ) (x : K.X (-1)) :
    (twoTermTrunc K).differential (Submodule.Quotient.mk x) = (K.d (-1) 0).hom x :=
  rfl

/-- The truncation of a chain map of cochain complexes. -/
def twoTermTruncHom (φ : K ⟶ L) : Hom (twoTermTrunc K) (twoTermTrunc L) where
  degreeZero := Submodule.mapQ _ _ (φ.f (-1)).hom (by
    intro y hy
    rw [Submodule.mem_comap]
    obtain ⟨x, rfl⟩ := hy
    exact ⟨(φ.f (-2)).hom x,
      congrArg (fun m : K.X (-2) ⟶ L.X (-1) => (ModuleCat.Hom.hom m) x) (φ.comm (-2) (-1))⟩)
  degreeOne := (φ.f 0).hom
  comm x := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (congrArg (fun m : K.X (-1) ⟶ L.X 0 => (ModuleCat.Hom.hom m) y) (φ.comm (-1) 0)).symm

@[simp]
theorem twoTermTruncHom_degreeZero_mk (φ : K ⟶ L) (x : K.X (-1)) :
    (twoTermTruncHom φ).degreeZero (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((φ.f (-1)).hom x) :=
  rfl

@[simp]
theorem twoTermTruncHom_degreeOne (φ : K ⟶ L) :
    (twoTermTruncHom φ).degreeOne = (φ.f 0).hom :=
  rfl

@[simp]
theorem twoTermTruncHom_id (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    twoTermTruncHom (𝟙 K) = Hom.id (twoTermTrunc K) := by
  refine Hom.ext (LinearMap.ext fun x => ?_) rfl
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

@[simp]
theorem twoTermTruncHom_comp (φ : K ⟶ L) (ψ : L ⟶ M) :
    twoTermTruncHom (φ ≫ ψ) = (twoTermTruncHom ψ).comp (twoTermTruncHom φ) := by
  refine Hom.ext (LinearMap.ext fun x => ?_) rfl
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- Two-term truncation as a functor from cochain complexes of modules to two-term complexes. -/
def twoTermTruncFunctor (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ LinearTwoTermComplex R where
  obj := twoTermTrunc
  map := twoTermTruncHom
  map_id K := twoTermTruncHom_id K
  map_comp φ ψ := twoTermTruncHom_comp φ ψ

/-! ## The projection of a complex onto its two-term truncation -/

/-- The degreewise component of the projection of a cochain complex onto the cochain realization
of its two-term truncation. -/
noncomputable def truncProjectionComponent (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    K.X n ⟶ (twoTermTrunc K).toCochainComplex.X n := by
  by_cases hneg : n = -1
  · subst hneg
    exact ModuleCat.ofHom (LinearMap.range (K.d (-2) (-1)).hom :
      Submodule R (K.X (-1))).mkQ
  · by_cases hzero : n = 0
    · subst hzero
      exact 𝟙 (K.X 0)
    · exact 0

@[simp]
theorem truncProjectionComponent_negOne (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    truncProjectionComponent K (-1) =
      ModuleCat.ofHom (LinearMap.range (K.d (-2) (-1)).hom :
        Submodule R (K.X (-1))).mkQ :=
  rfl

@[simp]
theorem truncProjectionComponent_zero (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    truncProjectionComponent K 0 = 𝟙 (K.X 0) :=
  rfl

/-- Outside the two displayed degrees the projection vanishes, its target being a zero object. -/
theorem truncProjectionComponent_eq_zero (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hneg : n ≠ -1) (hzero : n ≠ 0) : truncProjectionComponent K n = 0 :=
  (toCochainComplex_X_isZero (twoTermTrunc K) n hneg hzero).eq_of_tgt _ _

/-- The projection of a cochain complex onto the cochain realization of its two-term
truncation. -/
noncomputable def truncProjection (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K ⟶ (twoTermTrunc K).toCochainComplex :=
  CochainComplex.ofHom (truncProjectionComponent K) (by
    intro n
    by_cases hneg : n = -1
    · subst hneg
      change truncProjectionComponent K (-1) ≫ (twoTermTrunc K).toCochainComplex.d (-1) 0 =
        K.d (-1) 0 ≫ truncProjectionComponent K 0
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
    · by_cases hneg2 : n = -2
      · subst hneg2
        change truncProjectionComponent K (-2) ≫ (twoTermTrunc K).toCochainComplex.d (-2) (-1) =
          K.d (-2) (-1) ≫ truncProjectionComponent K (-1)
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ((Submodule.Quotient.mk_eq_zero
          (LinearMap.range (K.d (-2) (-1)).hom : Submodule R (K.X (-1)))).2
          (LinearMap.mem_range_self (ModuleCat.Hom.hom (K.d (-2) (-1))) x)).symm
      · exact (toCochainComplex_X_isZero (twoTermTrunc K) (n + 1)
          (by omega) (by omega)).eq_of_tgt _ _)

@[simp]
theorem truncProjection_f (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (truncProjection K).f n = truncProjectionComponent K n :=
  rfl

/-- The projection onto the two-term truncation is natural in the complex. -/
theorem truncProjection_naturality (φ : K ⟶ L) :
    φ ≫ truncProjection L = truncProjection K ≫ toCochainComplexHom (twoTermTruncHom φ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  by_cases hneg : n = -1
  · subst hneg
    change φ.f (-1) ≫ truncProjectionComponent L (-1) =
      truncProjectionComponent K (-1) ≫ cochainHomComponent (twoTermTruncHom φ) (-1)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · by_cases hzero : n = 0
    · subst hzero
      change φ.f 0 ≫ truncProjectionComponent L 0 =
        truncProjectionComponent K 0 ≫ cochainHomComponent (twoTermTruncHom φ) 0
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
    · exact (toCochainComplex_X_isZero (twoTermTrunc L) n hneg hzero).eq_of_tgt _ _

/-! ## The projection is a quasi-isomorphism in degrees `-1` and `0` -/

/-- The cochain realization of a two-term complex has no differential into degree `-1`. -/
theorem toCochainComplex_sc'_f_eq_zero (E : LinearTwoTermComplex R) :
    (E.toCochainComplex.sc' (-2) (-1) 0).f = 0 :=
  (toCochainComplex_X_isZero E (-2) (by norm_num) (by norm_num)).eq_of_src _ _

/-- The cochain realization of a two-term complex has no differential out of degree `0`. -/
theorem toCochainComplex_sc'_g_eq_zero (E : LinearTwoTermComplex R) :
    (E.toCochainComplex.sc' (-1) 0 1).g = 0 :=
  (toCochainComplex_X_isZero E 1 (by norm_num) (by norm_num)).eq_of_tgt _ _

/-- The comparison of the cycles in degree `-1` with `h⁰` of the two-term truncation: a cycle is
sent to its class modulo the boundaries. -/
def truncKernelMap (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    LinearMap.ker (K.d (-1) 0).hom →ₗ[R]
      LinearMap.ker (twoTermTrunc K).differential where
  toFun x := ⟨Submodule.Quotient.mk (x : K.X (-1)), x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem truncKernelMap_coe (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (x : LinearMap.ker (K.d (-1) 0).hom) :
    ((truncKernelMap K x : LinearMap.ker (twoTermTrunc K).differential) :
      (twoTermTrunc K).degreeZero) = Submodule.Quotient.mk (x : K.X (-1)) :=
  rfl

/-- The boundaries coming from degree `-2`, as a submodule of the cycles in degree `-1`.  This
is the submodule by which Mathlib's concrete homology of `K` in degree `-1` is a quotient. -/
def truncBoundaries (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    Submodule R (LinearMap.ker (K.d (-1) 0).hom) :=
  LinearMap.range (K.sc' (-2) (-1) 0).moduleCatToCycles

/-- Every element of `h⁰` of the truncation is the class of a cycle. -/
theorem truncKernelMap_surjective (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    Function.Surjective (truncKernelMap K) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨⟨x, hy⟩, rfl⟩

/-- A cycle in degree `-1` becomes zero in `h⁰` of the truncation exactly when it is a
boundary. -/
theorem ker_truncKernelMap (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    LinearMap.ker (truncKernelMap K) = truncBoundaries K := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [LinearMap.mem_ker] at hx
    have hx' : (x : K.X (-1)) ∈ LinearMap.range (K.d (-2) (-1)).hom := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact congrArg Subtype.val hx
    obtain ⟨w, hw⟩ := hx'
    exact ⟨w, Subtype.ext hw⟩
  · rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).2
      (LinearMap.mem_range_self (ModuleCat.Hom.hom (K.d (-2) (-1))) w)

/-- The induced map from `H⁻¹(K)`, computed as cycles modulo boundaries, to `h⁰` of the two-term
truncation. -/
noncomputable def truncHomologyNegOneMap (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (LinearMap.ker (K.d (-1) 0).hom ⧸ truncBoundaries K) →ₗ[R]
      LinearMap.ker (twoTermTrunc K).differential :=
  Submodule.liftQ _ (truncKernelMap K) (le_of_eq (ker_truncKernelMap K).symm)

/-- **`h⁰` of the two-term truncation is `H⁻¹(K)`.** -/
theorem bijective_truncHomologyNegOneMap (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    Function.Bijective (truncHomologyNegOneMap K) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq, ← ker_truncKernelMap, LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact hab
  · intro y
    obtain ⟨x, hx⟩ := truncKernelMap_surjective K y
    exact ⟨Submodule.Quotient.mk x, hx⟩

/-- The left homology map data in degree `-1` comparing the concrete `ModuleCat` homology of `K`
with the kernel description of `h⁰` of the two-term truncation. -/
noncomputable def truncLeftHomologyMapDataNegOne (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (-2) (-1) 0).map (truncProjection K))
      (K.sc' (-2) (-1) 0).moduleCatLeftHomologyData
      (ShortComplex.LeftHomologyData.ofIsLimitKernelFork
        ((twoTermTrunc K).toCochainComplex.sc' (-2) (-1) 0)
        (toCochainComplex_sc'_f_eq_zero (twoTermTrunc K)) _
        (ModuleCat.kernelIsLimit _)) where
  φK := ModuleCat.ofHom (truncKernelMap K)
  φH := ModuleCat.ofHom (truncHomologyNegOneMap K)
  commi := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  commf' := by
    rw [ShortComplex.LeftHomologyData.ofIsLimitKernelFork_f', comp_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).2
      (LinearMap.mem_range_self (ModuleCat.Hom.hom (K.d (-2) (-1))) w)
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- **The projection onto the two-term truncation is a quasi-isomorphism in degree `-1`.**  This
is unconditional: `H⁻¹` of a complex only depends on the terms in degrees `-2, -1, 0`. -/
theorem quasiIsoAt_truncProjection_negOne (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIsoAt (truncProjection K) (-1) := by
  rw [quasiIsoAt_iff' (truncProjection K) (-2) (-1) 0
      (by rw [CochainComplex.prev]; norm_num) (by rw [CochainComplex.next]; norm_num),
    (truncLeftHomologyMapDataNegOne K).quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  exact bijective_truncHomologyNegOneMap K

/-- The differential of the two-term truncation has the same image as the differential of `K`
from degree `-1` to degree `0`. -/
theorem range_twoTermTrunc_differential (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    LinearMap.range (twoTermTrunc K).differential = LinearMap.range (K.d (-1) 0).hom := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨y, rfl⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- The comparison of `H⁰(K)`, computed as the cokernel of the differential into degree `0` when
`K` has no differential out of degree `0`, with `h¹` of the two-term truncation. -/
noncomputable def truncHomologyZeroMap (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (K.X 0 ⧸ LinearMap.range (K.d (-1) 0).hom) →ₗ[R]
      ((twoTermTrunc K).degreeOne ⧸
        (LinearMap.range (twoTermTrunc K).differential :
          Submodule R (twoTermTrunc K).degreeOne)) :=
  Submodule.mapQ _ _ LinearMap.id (by
    rw [range_twoTermTrunc_differential]
    exact fun x hx => hx)

/-- **`h¹` of the two-term truncation is `H⁰(K)`** when `K` has no differential out of degree
`0`; the comparison map is bijective because the two differentials have the same image. -/
theorem bijective_truncHomologyZeroMap (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    Function.Bijective (truncHomologyZeroMap K) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    simp only [truncHomologyZeroMap, Submodule.mapQ_apply, LinearMap.id_coe] at hab
    have h := (Submodule.Quotient.eq _).1 hab
    rw [range_twoTermTrunc_differential] at h
    exact (Submodule.Quotient.eq _).2 h
  · intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- **The projection onto the two-term truncation is a quasi-isomorphism in degree `0`**, as soon
as `K` has no differential out of degree `0` (for instance when `K` is supported in degrees
`≤ 0`).  Without that hypothesis the statement is false: `h¹` of the truncation is the cokernel
of `d⁻¹`, not `H⁰(K)`. -/
theorem quasiIsoAt_truncProjection_zero (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.d 0 1 = 0) : QuasiIsoAt (truncProjection K) 0 := by
  have hg₂ : ((twoTermTrunc K).toCochainComplex.sc' (-1) 0 1).g = 0 :=
    toCochainComplex_sc'_g_eq_zero (twoTermTrunc K)
  have comm : ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (-1) 0 1).map (truncProjection K)).τ₂ ≫
      (ModuleCat.cokernelCocone ((twoTermTrunc K).toCochainComplex.sc' (-1) 0 1).f).π =
      (ModuleCat.cokernelCocone (K.sc' (-1) 0 1).f).π ≫
        ModuleCat.ofHom (truncHomologyZeroMap K) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  rw [quasiIsoAt_iff' (truncProjection K) (-1) 0 1
      (by rw [CochainComplex.prev]; norm_num) (by rw [CochainComplex.next]; norm_num),
    (ShortComplex.LeftHomologyMapData.ofIsColimitCokernelCofork _ hK _
      (ModuleCat.cokernelIsColimit _) hg₂ _ (ModuleCat.cokernelIsColimit _)
      (ModuleCat.ofHom (truncHomologyZeroMap K)) comm).quasiIso_iff,
    ConcreteCategory.isIso_iff_bijective]
  exact bijective_truncHomologyZeroMap K

/-! ## The cohomology of the truncation -/

/-- **`h⁰` of the two-term truncation is `H⁻¹(K)`.**  No hypothesis is needed: `H⁻¹` only
involves the terms of `K` in degrees `-2, -1, 0`. -/
noncomputable def homologyNegOneIsoTrunc (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K.homology (-1) ≅ ModuleCat.of R (LinearMap.ker (twoTermTrunc K).differential) :=
  have _ : QuasiIsoAt (truncProjection K) (-1) := quasiIsoAt_truncProjection_negOne K
  isoOfQuasiIsoAt (truncProjection K) (-1) ≪≫ homologyNegOneIsoKer (twoTermTrunc K)

/-- **`h¹` of the two-term truncation is `H⁰(K)`** when `K` has no differential out of degree
`0`. -/
noncomputable def homologyZeroIsoTrunc (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.d 0 1 = 0) :
    K.homology 0 ≅ ModuleCat.of R ((twoTermTrunc K).degreeOne ⧸
      (LinearMap.range (twoTermTrunc K).differential :
        Submodule R (twoTermTrunc K).degreeOne)) :=
  have _ : QuasiIsoAt (truncProjection K) 0 := quasiIsoAt_truncProjection_zero K hK
  isoOfQuasiIsoAt (truncProjection K) 0 ≪≫ homologyZeroIsoCoker (twoTermTrunc K)

/-! ## Transfer of quasi-isomorphisms to the truncations -/

/-- **A map which is a quasi-isomorphism in degrees `-1` and `0` truncates to an elementwise
quasi-isomorphism.**  The hypotheses on the differentials out of degree `0` cannot be dropped:
`h¹` of the truncation is the cokernel of `d⁻¹`, which is `H⁰` only under that assumption. -/
theorem isQuasiIsomorphism_twoTermTruncHom (φ : K ⟶ L) (hK : K.d 0 1 = 0) (hL : L.d 0 1 = 0)
    (hneg : QuasiIsoAt φ (-1)) (hzero : QuasiIsoAt φ 0) :
    (twoTermTruncHom φ).IsQuasiIsomorphism := by
  have _ := hneg
  have _ := hzero
  rw [isQuasiIsomorphism_iff_quasiIso, quasiIso_iff]
  intro n
  by_cases h1 : n = -1
  · subst h1
    have hp := quasiIsoAt_truncProjection_negOne K
    have hpL := quasiIsoAt_truncProjection_negOne L
    have hcomp : QuasiIsoAt (truncProjection K ≫
        toCochainComplexHom (twoTermTruncHom φ)) (-1) := by
      rw [← truncProjection_naturality φ]
      infer_instance
    exact (quasiIsoAt_iff_comp_left (truncProjection K) _ (-1)).1 hcomp
  · by_cases h0 : n = 0
    · subst h0
      have hp := quasiIsoAt_truncProjection_zero K hK
      have hpL := quasiIsoAt_truncProjection_zero L hL
      have hcomp : QuasiIsoAt (truncProjection K ≫
          toCochainComplexHom (twoTermTruncHom φ)) 0 := by
        rw [← truncProjection_naturality φ]
        infer_instance
      exact (quasiIsoAt_iff_comp_left (truncProjection K) _ 0).1 hcomp
    · rw [quasiIsoAt_iff_exactAt _ n (HomologicalComplex.ExactAt.of_isZero
        (toCochainComplex_X_isZero (twoTermTrunc K) n h1 h0))]
      exact HomologicalComplex.ExactAt.of_isZero
        (toCochainComplex_X_isZero (twoTermTrunc L) n h1 h0)

/-- **Equivalence of the Picard groupoids of the truncations.**  A chain map which is a
quasi-isomorphism in degrees `-1` and `0` induces an equivalence `h¹/h⁰(K) ≌ h¹/h⁰(L)`. -/
noncomputable def truncQuotientEquivalence (φ : K ⟶ L) (hK : K.d 0 1 = 0) (hL : L.d 0 1 = 0)
    (hneg : QuasiIsoAt φ (-1)) (hzero : QuasiIsoAt φ 0) :
    (twoTermTrunc K).quotient ≌ (twoTermTrunc L).quotient :=
  (isQuasiIsomorphism_twoTermTruncHom φ hK hL hneg hzero).quotientEquivalence

/-- **Comparison through a roof.**  If two complexes with no differential out of degree `0` are
connected by a roof of quasi-isomorphisms through a third such complex, their truncations have
equivalent Picard groupoids.  This is the chain-level form of the independence statement for
representatives of a derived object. -/
theorem nonempty_truncQuotientEquivalence_of_roof {N : CochainComplex (ModuleCat.{u} R) ℤ}
    (α : N ⟶ K) (β : N ⟶ L) (hK : K.d 0 1 = 0) (hL : L.d 0 1 = 0) (hN : N.d 0 1 = 0)
    (hα : QuasiIso α) (hβ : QuasiIso β) :
    Nonempty ((twoTermTrunc K).quotient ≌ (twoTermTrunc L).quotient) :=
  ⟨(truncQuotientEquivalence α hN hK (hα.quasiIsoAt (-1)) (hα.quasiIsoAt 0)).symm.trans
    (truncQuotientEquivalence β hN hL (hβ.quasiIsoAt (-1)) (hβ.quasiIsoAt 0))⟩

/-! ## Homotopies -/

/-- **A homotopy of chain maps descends to the truncations.**  Only the component `K⁰ → L⁻¹` of
the homotopy survives: the component `K⁻¹ → L⁻²` contributes a boundary, which is killed by the
quotient defining the truncation, and the component `K¹ → K⁰` is killed by the hypothesis that
`K` has no differential out of degree `0`.  So no hypothesis on `L` is needed, in contrast with
`LinearTwoTermComplex.ofHomotopy`. -/
def ofHomotopyTrunc {φ ψ : K ⟶ L} (hK : K.d 0 1 = 0) (H : Homotopy φ ψ) :
    ChainHomotopy (twoTermTruncHom ψ) (twoTermTruncHom φ) where
  homotopy := (LinearMap.range (L.d (-2) (-1)).hom :
    Submodule R (L.X (-1))).mkQ.comp (H.hom 0 (-1)).hom
  degreeZero x := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hcomm := H.comm (-1)
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp)] at hcomm
    have happ := congrArg (fun m : K.X (-1) ⟶ L.X (-1) => (ModuleCat.Hom.hom m) y) hcomm
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
      LinearMap.comp_apply] at happ
    change Submodule.Quotient.mk ((φ.f (-1)).hom y) =
      Submodule.Quotient.mk ((ψ.f (-1)).hom y) +
        Submodule.Quotient.mk ((H.hom 0 (-1)).hom ((K.d (-1) 0).hom y))
    rw [happ, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    have hmem : (ModuleCat.Hom.hom (L.d (-2) (-1))) ((ModuleCat.Hom.hom (H.hom (-1) (-2))) y) ∈
        (LinearMap.range (L.d (-2) (-1)).hom : Submodule R (L.X (-1))) :=
      LinearMap.mem_range_self _ _
    convert hmem using 1
    abel
  degreeOne x := by
    have hcomm := H.comm 0
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp), hK, zero_comp,
      zero_add] at hcomm
    have hmor : φ.f 0 = ψ.f 0 + H.hom 0 (-1) ≫ L.d (-1) 0 := by
      rw [hcomm]
      abel
    exact congrArg (fun m : K.X 0 ⟶ L.X 0 => (ModuleCat.Hom.hom m) x) hmor

/-- A homotopy equivalence of complexes with no differential out of degree `0` induces a
chain-homotopy equivalence of the two-term truncations. -/
def ofHomotopyEquivTrunc (hK : K.d 0 1 = 0) (hL : L.d 0 1 = 0) (e : HomotopyEquiv K L) :
    HomotopyEquivalence (twoTermTrunc K) (twoTermTrunc L) where
  hom := twoTermTruncHom e.hom
  inv := twoTermTruncHom e.inv
  unit := by
    have h := ofHomotopyTrunc hK e.homotopyHomInvId
    rw [twoTermTruncHom_id, twoTermTruncHom_comp] at h
    exact h
  counit := by
    have h := ofHomotopyTrunc hL e.homotopyInvHomId
    rw [twoTermTruncHom_id, twoTermTruncHom_comp] at h
    exact h.symm

/-! ## Comparison with the naive two-term complex -/

/-- The comparison from the naive two-term complex in degrees `-1` and `0` to the truncation. -/
def toTwoTermTrunc (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    Hom (ofCochainComplex K) (twoTermTrunc K) where
  degreeZero := (LinearMap.range (K.d (-2) (-1)).hom : Submodule R (K.X (-1))).mkQ
  degreeOne := LinearMap.id
  comm _ := rfl

/-- **The truncation does not change anything when the complex vanishes in degree `-2`.** -/
theorem isQuasiIsomorphism_toTwoTermTrunc (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : IsZero (K.X (-2))) : (toTwoTermTrunc K).IsQuasiIsomorphism := by
  have hd : K.d (-2) (-1) = 0 := h.eq_of_src _ _
  have hrange : (LinearMap.range (K.d (-2) (-1)).hom : Submodule R (K.X (-1))) = ⊥ := by
    rw [hd]
    exact LinearMap.range_eq_bot.2 rfl
  have hinj : Function.Injective (toTwoTermTrunc K).degreeZero := by
    change Function.Injective
      (LinearMap.range (K.d (-2) (-1)).hom : Submodule R (K.X (-1))).mkQ
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]
    exact hrange
  constructor
  · constructor
    · intro a b hab
      apply Subtype.ext
      exact hinj (congrArg Subtype.val hab)
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact ⟨⟨x, hz⟩, rfl⟩
  · constructor
    · intro a b hab
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      have hxy := (Submodule.Quotient.eq _).1 hab
      rw [range_twoTermTrunc_differential] at hxy
      exact (Submodule.Quotient.eq _).2 hxy
    · intro y
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- **The two definitions of `h¹/h⁰` agree** for a complex concentrated in degrees `-1` and `0`:
the Picard groupoid of the naive two-term complex is equivalent to the one of the truncation. -/
noncomputable def toTwoTermTruncQuotientEquivalence (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : IsZero (K.X (-2))) : (ofCochainComplex K).quotient ≌ (twoTermTrunc K).quotient :=
  (isQuasiIsomorphism_toTwoTermTrunc K h).quotientEquivalence

end LinearTwoTermComplex

/-! ## `h¹/h⁰` of a derived object -/

section Derived

open LinearTwoTermComplex

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- A *truncation presentation* of an object `E` of the derived category of `R`-modules: a
K-projective complex with no differential out of degree `0`, together with an isomorphism onto
`E`.  Every field is data or a hypothesis about that data; the Picard groupoid it computes is
`TruncPresentation.picard`, and `TruncPresentation.nonempty_picardEquivalence` proves that this
does not depend on the presentation. -/
structure TruncPresentation (E : DerivedCategory (ModuleCat.{u} R)) where
  /-- The representing complex. -/
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  /-- It is K-projective: derived morphisms out of it are chain maps up to homotopy. -/
  isKProjective : complex.IsKProjective
  /-- It has no differential out of degree `0`, which makes `h¹` of the truncation `H⁰`. -/
  d_zero_one : complex.d 0 1 = 0
  /-- It represents `E`. -/
  iso : DerivedCategory.Q.obj complex ≅ E

namespace TruncPresentation

variable {E : DerivedCategory (ModuleCat.{u} R)}

/-- The Picard groupoid `h¹/h⁰(E)` computed from a truncation presentation: the translation
groupoid of the two-term truncation of the representing complex. -/
abbrev picard (P : TruncPresentation E) := (twoTermTrunc P.complex).quotient

/-- Vertex automorphisms of `h¹/h⁰(E)` are `H⁻¹(E)`, computed as the kernel of the differential
of the truncation. -/
def vertexAutEquiv (P : TruncPresentation E) :
    (TwoTermQuotient.vertex (twoTermTrunc P.complex).differential ⟶
        TwoTermQuotient.vertex (twoTermTrunc P.complex).differential) ≃
      LinearMap.ker (twoTermTrunc P.complex).differential :=
  TwoTermQuotient.vertexAutEquivKernel _

/-- A bounded-above complex of projective modules is a truncation presentation of the derived
object it represents. -/
noncomputable def ofProjective (K : CochainComplex (ModuleCat.{u} R) ℤ) (hle : K.IsStrictlyLE 0)
    (hproj : ∀ n : ℤ, CategoryTheory.Projective (K.X n)) :
    TruncPresentation (DerivedCategory.Q.obj K) where
  complex := K
  isKProjective := by
    have h := hle
    have h' := hproj
    exact CochainComplex.isKProjective_of_projective _ 0
  d_zero_one := by
    have h1 : IsZero (K.X 1) := by
      rw [CochainComplex.isStrictlyLE_iff] at hle
      exact hle 1 (by norm_num)
    exact h1.eq_of_tgt _ _
  iso := Iso.refl _

/-- **The comparison isomorphism of two presentations is realized by a chain map**, because the
source is K-projective. -/
theorem exists_chain_realization (P P' : TruncPresentation E) :
    ∃ φ : P.complex ⟶ P'.complex,
      DerivedCategory.Q.map φ = (P.iso ≪≫ P'.iso.symm).hom := by
  have hK := P.isKProjective
  obtain ⟨γ, hγ⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective P.complex
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
        P'.complex)).surjective
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app P.complex ≫
        (P.iso ≪≫ P'.iso.symm).hom ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app P'.complex)
  obtain ⟨φ, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_surjective γ
  refine ⟨φ, ?_⟩
  have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality φ
  rw [Functor.comp_map, hγ] at hnat
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hnat
  exact ((cancel_epi _).mp hnat).symm

/-- **Independence of the presentation.**  Any two truncation presentations of the same derived
object have equivalent Picard groupoids, with no further hypothesis: the comparison isomorphism
is realized by a chain map, which is a quasi-isomorphism, hence induces an equivalence of the
Picard groupoids of the truncations. -/
theorem nonempty_picardEquivalence (P P' : TruncPresentation E) :
    Nonempty (P.picard ≌ P'.picard) := by
  obtain ⟨φ, hφ⟩ := exists_chain_realization P P'
  have hiso : IsIso (DerivedCategory.Q.map φ) := by
    rw [hφ]
    infer_instance
  have hq : QuasiIso φ := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hiso
  exact ⟨truncQuotientEquivalence φ P.d_zero_one P'.d_zero_one
    (hq.quasiIsoAt (-1)) (hq.quasiIsoAt 0)⟩

/-- Transport a truncation presentation along an isomorphism of the represented object. -/
noncomputable def replace {E' : DerivedCategory (ModuleCat.{u} R)} (P : TruncPresentation E)
    (e : E ≅ E') :
    TruncPresentation E' where
  complex := P.complex
  isKProjective := P.isKProjective
  d_zero_one := P.d_zero_one
  iso := P.iso ≪≫ e

@[simp]
theorem replace_complex {E' : DerivedCategory (ModuleCat.{u} R)} (P : TruncPresentation E)
    (e : E ≅ E') : (P.replace e).complex = P.complex :=
  rfl

end TruncPresentation

namespace CotangentComplex.PerfectComplex

open CotangentComplex.PerfectComplex

namespace GlobalTwoTermResolution

variable {E : DerivedCategory (ModuleCat.{u} R)}

/-- A global two-term resolution is in particular a truncation presentation: its complex is
K-projective and supported in degrees `-1` and `0`. -/
def truncPresentation (F : GlobalTwoTermResolution E) : TruncPresentation E where
  complex := F.complex
  isKProjective := F.isKProjective
  d_zero_one := (F.supported 1 (Or.inr (by norm_num))).eq_of_tgt _ _
  iso := F.iso

@[simp]
theorem truncPresentation_complex (F : GlobalTwoTermResolution E) :
    F.truncPresentation.complex = F.complex :=
  rfl

/-- **The truncation construction agrees with the two-term construction.**  For a global
two-term resolution, the Picard groupoid of `Cones/DerivedPicard.lean` is equivalent to the one
computed by truncation, because the resolving complex vanishes in degree `-2`. -/
theorem nonempty_picardEquivalence_truncPresentation (F : GlobalTwoTermResolution E) :
    Nonempty (F.picard ≌ F.truncPresentation.picard) :=
  ⟨toTwoTermTruncQuotientEquivalence F.complex (F.supported (-2) (Or.inl (by norm_num)))⟩

end GlobalTwoTermResolution

end CotangentComplex.PerfectComplex

end Derived

end GromovWitten.AlgebraicGeometry
