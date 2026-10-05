/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import GromovWitten.AlgebraicGeometry.ProjectiveLineSeparated
import GromovWitten.AlgebraicGeometry.RegularScheme
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension

/-!
# Topology of proper curves

This file collects the topological and local-algebraic consequences of one-dimensionality that
are needed to compare a rational function on a curve with a morphism to the projective line.

## Main results

* `GromovWitten.AlgebraicGeometry.finite_of_isClosed_of_ne_univ`: in an irreducible sober
  Noetherian space all of whose non-generic points are closed, every proper closed subset is
  finite.
* `GromovWitten.AlgebraicGeometry.isClosed_singleton_of_ne_genericPoint`: on an irreducible
  scheme whose generic point has height one, every other point is closed.
* `GromovWitten.AlgebraicGeometry.valuationRing_stalk_of_regular`: the local rings of a regular
  integral one-dimensional scheme are valuation rings.
* `GromovWitten.AlgebraicGeometry.RegularProperCurve`: the bundle of hypotheses "regular proper
  integral one-dimensional scheme over `k`", from which the three hypotheses `hv`, `hpt` and
  `hone` of `Curves/RationalFunctionToProjectiveLine.lean` are derived.
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct

universe u

namespace GromovWitten.AlgebraicGeometry

section Topology

variable {α : Type u} [TopologicalSpace α]

/-- If every point of `α` other than the generic point is closed, then every irreducible closed
subset of `α` which is not the whole space is a singleton. -/
theorem eq_singleton_of_isIrreducible_of_isClosed [QuasiSober α] [IrreducibleSpace α]
    (hpt : ∀ x : α, x ≠ genericPoint α → IsClosed ({x} : Set α))
    {t : Set α} (ht : IsIrreducible t) (htc : IsClosed t) (htne : t ≠ Set.univ) :
    ∃ x : α, t = {x} := by
  refine ⟨ht.genericPoint, ?_⟩
  have hclos : closure ({ht.genericPoint} : Set α) = t := ht.closure_genericPoint htc
  have hne : ht.genericPoint ≠ genericPoint α := fun h =>
    htne (by rw [← hclos, h, genericPoint_closure])
  exact hclos.symm.trans (hpt _ hne).closure_eq

/-- In an irreducible sober Noetherian space all of whose non-generic points are closed, every
closed subset different from the whole space is finite. This is the topological content of
one-dimensionality of an integral curve. -/
theorem finite_of_isClosed_of_ne_univ [TopologicalSpace.NoetherianSpace α] [QuasiSober α]
    [IrreducibleSpace α] (hpt : ∀ x : α, x ≠ genericPoint α → IsClosed ({x} : Set α))
    (Z : Set α) (hZ : IsClosed Z) (hne : Z ≠ Set.univ) : Z.Finite := by
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hSU]
  refine hSf.sUnion fun t ht => ?_
  have htne : t ≠ Set.univ := by
    rintro rfl
    exact hne (hSU.trans (Set.univ_subset_iff.mp (Set.subset_sUnion_of_mem ht)))
  obtain ⟨x, rfl⟩ :=
    eq_singleton_of_isIrreducible_of_isClosed hpt (hSi t ht) (hSc t ht) htne
  exact Set.finite_singleton x

end Topology

section Dimension

/-- A point of a scheme whose singleton is closed is minimal for the specialisation order. -/
theorem isMin_of_isClosed_singleton {X : Scheme.{u}} {x : X} (h : IsClosed ({x} : Set X)) :
    IsMin x := fun z hz => by
  have hmem : z ∈ closure ({x} : Set X) :=
    specializes_iff_mem_closure.1 (IntersectionTheory.HomogeneityLocal.le_iff_specializes.1 hz)
  rw [h.closure_eq] at hmem
  exact le_of_eq hmem.symm

/-- A point of a scheme which is minimal for the specialisation order is closed. -/
theorem isClosed_singleton_of_isMin {X : Scheme.{u}} {x : X} (hx : IsMin x) :
    IsClosed ({x} : Set X) := by
  refine isClosed_of_closure_subset fun z hz ↦ ?_
  have h1 : x ⤳ z := specializes_iff_mem_closure.2 hz
  have h2 : z ⤳ x :=
    IntersectionTheory.HomogeneityLocal.le_iff_specializes.1
      (hx (IntersectionTheory.HomogeneityLocal.le_iff_specializes.2 h1))
  exact (h1.antisymm h2).eq.symm

/-- A point of an irreducible scheme other than the generic point is strictly below it in the
specialisation order. -/
theorem lt_genericPoint {X : Scheme.{u}} [IrreducibleSpace X] {x : X}
    (hx : x ≠ genericPoint X) : x < genericPoint X :=
  lt_of_le_not_ge (IntersectionTheory.HomogeneityLocal.isTop_genericPoint X x) fun hge =>
    hx ((IntersectionTheory.HomogeneityLocal.le_iff_specializes.1 hge).antisymm
      (IntersectionTheory.HomogeneityLocal.le_iff_specializes.1
        (IntersectionTheory.HomogeneityLocal.isTop_genericPoint X x))).eq

/-- **One-dimensionality implies that non-generic points are closed.**  On an irreducible scheme
whose generic point has height one for the specialisation order — that is, on a one-dimensional
irreducible scheme — every point different from the generic point is closed. -/
theorem isClosed_singleton_of_ne_genericPoint {X : Scheme.{u}} [IrreducibleSpace X]
    (h : Order.height (genericPoint X) = 1) (x : X) (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) := by
  have hle : x ≤ genericPoint X := IntersectionTheory.HomogeneityLocal.isTop_genericPoint X x
  have hfin : Order.height x < ⊤ :=
    lt_of_le_of_lt (Order.height_mono hle) (by rw [h]; simp)
  have hlt1 : Order.height x < 1 := h ▸ Order.height_strictMono (lt_genericPoint hx) hfin
  exact isClosed_singleton_of_isMin (Order.height_eq_zero.mp (Order.lt_one_iff.mp hlt1))

/-- The dimension-function form of `isClosed_singleton_of_ne_genericPoint`: if the residue field
of the generic point of an irreducible scheme locally of finite type over a field has
transcendence degree one, every other point is closed. -/
theorem isClosed_singleton_of_ne_genericPoint_of_resTrdeg {k : Type u} [Field k]
    {X : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f]
    (h : IntersectionTheory.FiniteTypeDimension.resTrdeg f (genericPoint X) = 1)
    (x : X) (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) :=
  isClosed_singleton_of_ne_genericPoint
    ((IntersectionTheory.FiniteTypeDimension.height_eq_resTrdeg f _).trans h) x hx

/-- Points of a one-dimensional irreducible scheme other than the generic point have
codimension one. -/
theorem coheight_eq_one_of_ne_genericPoint {X : Scheme.{u}} [IrreducibleSpace X]
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X)) (x : X)
    (hx : x ≠ genericPoint X) : Order.coheight x = 1 := by
  rw [IntersectionTheory.HomogeneityLocal.coheight_eq_one_iff_covBy
    (IntersectionTheory.HomogeneityLocal.isTop_genericPoint X)]
  refine ⟨lt_genericPoint hx, fun c hxc hcg ↦ ?_⟩
  exact absurd (isMin_of_isClosed_singleton (hpt c hcg.ne) hxc.le) (not_le_of_gt hxc)

end Dimension

section Regular

variable {X : Scheme.{u}}

/-- The stalk at the generic point of an integral scheme is the function field, hence a valuation
ring. -/
theorem valuationRing_stalk_genericPoint [IsIntegral X] :
    ValuationRing (X.presheaf.stalk (genericPoint X)) :=
  let _ : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  inferInstance

/-- **A regular local ring of a scheme at a point of codimension one is a discrete valuation
ring.** -/
theorem isDiscreteValuationRing_stalk [IsIntegral X] (hreg : SchemeIsRegular X) (x : X)
    (hx : Order.coheight x = 1) : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have hstalk := hreg x
  rw [← IsLocalRing.finrank_CotangentSpace_eq_one_iff]
  have h1 :=
    (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk x)).mp inferInstance
  rw [ringKrullDim_stalk_eq_coheight, hx] at h1
  exact_mod_cast h1

/-- **The local rings of a regular integral one-dimensional scheme are valuation rings.**  This
is the hypothesis `hv` needed to extend a rational function to a morphism to `ℙ¹`. -/
theorem valuationRing_stalk_of_regular [IsIntegral X] (hreg : SchemeIsRegular X)
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X)) (x : X) :
    ValuationRing (X.presheaf.stalk x) := by
  by_cases hx : x = genericPoint X
  · subst hx
    exact valuationRing_stalk_genericPoint
  · have hdvr := isDiscreteValuationRing_stalk hreg x (coheight_eq_one_of_ne_genericPoint hpt x hx)
    infer_instance

end Regular

section Package

/-- **A regular proper one-dimensional integral curve over a field.**  This bundles exactly the
hypotheses under which a nonzero rational function on `W` defines a morphism `W ⟶ ℙ¹_k` whose
principal divisor has degree zero: `W` is an integral scheme, proper and regular over `k`, whose
generic point has residue transcendence degree one.

The three hypotheses `hv`, `hpt` and `hone` required by
`Curves/RationalFunctionToProjectiveLine.lean` are derived below. -/
structure RegularProperCurve (k : Type u) [Field k] where
  /-- The underlying scheme. -/
  W : Scheme.{u}
  /-- The structure morphism to `Spec k`. -/
  f : W ⟶ Spec (CommRingCat.of k)
  /-- `W` is integral. -/
  [isIntegral : IsIntegral W]
  /-- The structure morphism is proper. -/
  [isProper : IsProper f]
  /-- `W` is a regular scheme. -/
  regular : SchemeIsRegular W
  /-- `W` is one-dimensional: the residue field of the generic point has transcendence degree
  one over `k`. -/
  dim_eq_one : IntersectionTheory.FiniteTypeDimension.resTrdeg f (genericPoint W) = 1

attribute [instance] RegularProperCurve.isIntegral RegularProperCurve.isProper

namespace RegularProperCurve

variable {k : Type u} [Field k] (C : RegularProperCurve k)

/-- The total space of a proper curve is a Noetherian scheme: it is quasi-compact over the
compact space `Spec k` and locally of finite type over the Noetherian ring `k`. -/
theorem isNoetherian : AlgebraicGeometry.IsNoetherian C.W :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian C.f
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace C.f }

/-- Every point of a regular curve other than the generic point is closed. -/
theorem isClosed_singleton (x : C.W) (hx : x ≠ genericPoint C.W) : IsClosed ({x} : Set C.W) :=
  isClosed_singleton_of_ne_genericPoint_of_resTrdeg C.f C.dim_eq_one x hx

/-- Every proper closed subset of a regular curve is finite. -/
theorem finite_of_isClosed (Z : Set C.W) (hZ : IsClosed Z) (hne : Z ≠ Set.univ) : Z.Finite :=
  have := C.isNoetherian
  finite_of_isClosed_of_ne_univ C.isClosed_singleton Z hZ hne

/-- All local rings of a regular curve are valuation rings. -/
theorem valuationRing_stalk (x : C.W) : ValuationRing (C.W.presheaf.stalk x) :=
  valuationRing_stalk_of_regular C.regular C.isClosed_singleton x

end RegularProperCurve

end Package


end GromovWitten.AlgebraicGeometry
