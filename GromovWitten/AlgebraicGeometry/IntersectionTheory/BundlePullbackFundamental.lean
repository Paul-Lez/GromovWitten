/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobal
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackBaseChange
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.IndependenceAcyclic

/-!
# The flat pullback of the fundamental cycle along a vector bundle

Let `𝓔 : BundleData X ι` be a vector bundle of finite rank over a locally Noetherian scheme `X`
(`GromovWitten/AlgebraicGeometry/VectorBundleTotalSpace.lean`) and let

`pullbackBundle 𝓔 : AlgebraicCycle X ℚ → AlgebraicCycle 𝓔.totalSpace ℚ`

be the global flat pullback of
`GromovWitten/AlgebraicGeometry/IntersectionTheory/BundlePullbackGlobal.lean`.  This file proves

**`pullbackBundle_fundamentalCycle : pullbackBundle 𝓔 X.fundamentalCycle =
𝓔.totalSpace.fundamentalCycle`**,

the global form of the affine identity
`VirtualFundamentalClass.VirtualClass.pullbackBundle_fundamentalCycle`.

## Contents

* `isNoetherianRing_chart`, `isLocallyNoetherian_totalSpace`: the total
  space of a finite-rank bundle over a locally Noetherian scheme is locally Noetherian, because it
  is covered by the affine charts `Spec (MvPolynomial ι Γ(X, U_j))` and `MvPolynomial ι` preserves
  Noetherian rings in finitely many variables (Hilbert basis).
* `pullbackBundle_fundamentalCycle`: the main identity, proved chart by chart from
  `BundlePullbackGlobal.pullbackBundle_unique`, the restriction lemma
  `AlgebraicCycle.pullbackOpen_fundamentalCycle` of
  `IntersectionTheory/CycleGluing.lean` (applied both to the chart `𝓔.chartι j` of the total space
  and to the chart `isoSpec.inv ≫ U_j.ι` of the base) and the affine statement.
* `flatPullbackBundleGlobal_fundamental`: the graded corollary, identifying the image of the
  fundamental class of a pure base under the graded pullback with the fundamental class of the
  total space.
* `chartCover`, `isReduced_totalSpace`, `irreducibleSpace_totalSpace`, `isIntegral_totalSpace`:
  the total space of a bundle over a reduced (resp. integral) base is reduced (resp. integral).
  Reducedness is local on the chart cover; irreducibility goes through the generic point:
  `specializes_bundlePoint_genericPoint` shows that `bundlePoint 𝓔 η`, the generic point of the
  fibre over the generic point `η` of `X`, specialises to every point of the total space, so its
  closure is everything.

## What is not here

Nothing is descended to Chow groups: as in the affine case, the compatibility of the flat
pullback with rational equivalence is not proved anywhere in the repository.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order

attribute [local instance] specializationOrder

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

namespace BundlePullbackGlobal

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι)

/-! ## Noetherianity of the total space -/

/-- The sections of `X` over a trivialising chart of a bundle form a Noetherian ring. -/
instance isNoetherianRing_chart [IsLocallyNoetherian X] (j : 𝓔.J) :
    IsNoetherianRing Γ(X, (𝓔.chart j).1) :=
  IsLocallyNoetherian.component_noetherian (𝓔.chart j)

/-- The total space of a bundle of finite rank over a locally Noetherian scheme is locally
Noetherian: it is covered by the affine charts `Spec (MvPolynomial ι Γ(X, U_j))`, whose coordinate
rings are Noetherian by the Hilbert basis theorem. -/
instance isLocallyNoetherian_totalSpace [Finite ι] [IsLocallyNoetherian X] :
    IsLocallyNoetherian 𝓔.totalSpace := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun j : 𝓔.J => ⟨(𝓔.chartι j).opensRange, isAffineOpen_opensRange (𝓔.chartι j)⟩)
    𝓔.iSup_opensRange_chartι fun j => ?_
  exact isNoetherianRing_of_ringEquiv (MvPolynomial ι Γ(X, (𝓔.chart j).1))
    (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))).symm ≪≫
      IsOpenImmersion.ΓIsoTop (𝓔.chartι j)).commRingCatIsoToRingEquiv)

/-! ## The fundamental cycle -/

/-- **The flat pullback of the fundamental cycle along the total space of a vector bundle is the
fundamental cycle of the total space.**  The proof is chart by chart: on the chart
`Spec (MvPolynomial ι Γ(X, U_j))` the global pullback is the affine pullback
(`pullbackOpen_chartι_pullbackBundle`), the fundamental cycles of `X` and of the total space
restrict to the fundamental cycles of the charts (`AlgebraicCycle.pullbackOpen_fundamentalCycle`),
and the affine statement is
`VirtualFundamentalClass.VirtualClass.pullbackBundle_fundamentalCycle`. -/
theorem pullbackBundle_fundamentalCycle [Finite ι] [IsLocallyNoetherian X] :
    pullbackBundle 𝓔 X.fundamentalCycle = 𝓔.totalSpace.fundamentalCycle := by
  refine (pullbackBundle_unique 𝓔 X.fundamentalCycle _ fun j => ?_).symm
  rw [AlgebraicCycle.pullbackOpen_fundamentalCycle (𝓔.chartι j),
    AlgebraicCycle.pullbackOpen_fundamentalCycle
      ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι)]
  exact (VirtualFundamentalClass.VirtualClass.pullbackBundle_fundamentalCycle
    (AlgEquiv.refl (R := Γ(X, (𝓔.chart j).1))
      (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))).symm

/-- The graded form of `pullbackBundle_fundamentalCycle`: if every irreducible component of `X`
has dimension `i` and every irreducible component of the total space has dimension
`i + rank`, then the graded flat pullback sends the fundamental class of `X` to the fundamental
class of the total space. -/
theorem flatPullbackBundleGlobal_fundamental [Finite ι] [IsLocallyNoetherian X]
    (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
    (hshift : ∀ x, dimE (bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ)) (i : ℤ)
    (pureX : ∀ x : X, IsMax x → dimX x = i)
    (pureE : ∀ q : 𝓔.totalSpace, IsMax q → dimE q = i + (Nat.card ι : ℤ)) :
    flatPullbackBundleGlobal 𝓔 dimX dimE hshift i (cyclesOfDimension.fundamental pureX) =
      cyclesOfDimension.fundamental pureE :=
  Subtype.ext (pullbackBundle_fundamentalCycle 𝓔)

/-! ## Reducedness and integrality of the total space -/

/-- The open cover of the total space by the trivialising charts `Spec (MvPolynomial ι Γ(X, U_j))`.
-/
noncomputable abbrev chartCover : 𝓔.totalSpace.OpenCover :=
  Scheme.Cover.mkOfCovers 𝓔.J
    (fun j => Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))))
    (fun j => 𝓔.chartι j)
    (fun q => by
      have hq : q ∈ (⨆ j, (𝓔.chartι j).opensRange : 𝓔.totalSpace.Opens) := by
        rw [BundleData.iSup_opensRange_chartι]
        trivial
      obtain ⟨j, q₀, hq₀⟩ := Opens.mem_iSup.mp hq
      exact ⟨j, q₀, hq₀⟩)

/-- The `j`-th member of the chart cover is the affine space over the `j`-th chart. -/
theorem chartCover_X (j : 𝓔.J) :
    (chartCover 𝓔).X j = Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))) := rfl

/-- The `j`-th inclusion of the chart cover is `BundleData.chartι`. -/
theorem chartCover_f (j : 𝓔.J) : (chartCover 𝓔).f j = 𝓔.chartι j := rfl

/-- The total space of a vector bundle over a reduced scheme is reduced: in the charts its
coordinate rings are polynomial rings over reduced rings. -/
instance isReduced_totalSpace [IsReduced X] : IsReduced 𝓔.totalSpace :=
  have h : ∀ j : (chartCover 𝓔).I₀, IsReduced ((chartCover 𝓔).X j) := fun j =>
    inferInstanceAs (IsReduced (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
  @IsReduced.of_openCover 𝓔.totalSpace (chartCover 𝓔) h

/-- The generic point of the total space of a vector bundle over an integral scheme is the
generic point of the fibre over the generic point of the base. -/
theorem specializes_bundlePoint_genericPoint [IsIntegral X] (q : 𝓔.totalSpace) :
    bundlePoint 𝓔 (genericPoint X) ⤳ q := by
  obtain ⟨j, hj⟩ : ∃ j, 𝓔.proj.base q ∈ (𝓔.chart j).1 := by
    have hmem : 𝓔.proj.base q ∈ (⨆ j, (𝓔.chart j).1 : X.Opens) := by
      rw [𝓔.iSup_chart]
      trivial
    exact Opens.mem_iSup.mp hmem
  have hne : (genericPoint X) ∈ (𝓔.chart j).1 := by
    have hdense := genericPoint_specializes (α := X) (𝓔.proj.base q)
    exact hdense.mem_open (𝓔.chart j).1.2 hj
  have hpt : bundlePoint 𝓔 (genericPoint X) =
      𝓔.chartBundlePoint j ⟨genericPoint X, hne⟩ :=
    bundlePoint_chart 𝓔 j ⟨genericPoint X, hne⟩
  rw [hpt, chartBundlePoint_specializes_iff 𝓔 j ⟨genericPoint X, hne⟩ q hj]
  exact genericPoint_specializes (α := X) (𝓔.proj.base q)

/-- The total space of a vector bundle over an integral scheme is irreducible. -/
instance irreducibleSpace_totalSpace [IsIntegral X] : IrreducibleSpace 𝓔.totalSpace := by
  have hclosure : closure ({bundlePoint 𝓔 (genericPoint X)} :
      Set 𝓔.totalSpace) = Set.univ :=
    Set.eq_univ_of_forall fun q =>
      specializes_iff_mem_closure.mp (specializes_bundlePoint_genericPoint 𝓔 q)
  rw [irreducibleSpace_def]
  have huniv : (⊤ : Set 𝓔.totalSpace) = closure {bundlePoint 𝓔 (genericPoint X)} := by
    rw [hclosure]
    rfl
  rw [huniv]
  exact isIrreducible_singleton.closure

/-- The total space of a vector bundle over an integral scheme is integral. -/
instance isIntegral_totalSpace [IsIntegral X] : IsIntegral 𝓔.totalSpace :=
  isIntegral_of_irreducibleSpace_of_isReduced 𝓔.totalSpace

end BundlePullbackGlobal

end GromovWitten.AlgebraicGeometry.IntersectionTheory
