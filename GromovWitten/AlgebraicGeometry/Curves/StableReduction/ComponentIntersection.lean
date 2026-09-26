/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ModelBlowup
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.CartierIntersection
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.Contraction

/-!
# Intersection numbers of special-fibre components from stalk multiplicities

This file starts to construct the fields of `SpecialFiberIntersectionData` from the actual
geometry of an arithmetic surface, using the stalk-theoretic local intersection theory of
`StalkIntersection.lean`/`CartierIntersection.lean`.

* `vanishingIdeal i` is the (reduced) vanishing ideal sheaf, on the total space, of the closed
  subset swept out by a component `i` of the special fibre.
* `componentIntersection i j` is the sum, over the total space, of the stalk-theoretic local
  intersection multiplicities of `vanishingIdeal i` and `vanishingIdeal j`; it is symmetric and
  vanishes when the two components are disjoint, unconditionally.  Finiteness needs an explicit
  hypothesis recording that the two components meet properly in finitely many points with
  0-dimensional local intersection algebras (the content of the "dimension 1 special fibre"
  fact that is not derived here from the bare `ArithmeticSurface` data).
* `genericPoint i` is the (unique, by soberness of schemes) generic point of a component, viewed
  in the total space.  `componentMultiplicity i π` is the order of vanishing, at that point, of
  the germ of a chosen element `π` of the base ring; it is always positive when `π` lies in the
  maximal ideal of the base (in particular for a uniformiser), unconditionally.  Its value being
  a genuine natural number (rather than merely a value in `ℕ∞`) again needs the local ring at the
  generic point to be a discrete valuation ring, which is not derived here.

## Not done

The self-intersection numbers (via the fibre relation) and the genus function of
`SpecialFiberIntersectionData` are not constructed; see the module docstring of
`ArithmeticSurface.lean` and the file-level remarks below for the precise gaps.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

section NoetherianInstances

variable (M : Model R K C toK)

/-- The total space of a model is quasi-compact: it is the whole preimage, under the
quasi-compact structure map, of the (affine, hence compact) base spectrum. -/
instance : CompactSpace M.total :=
  QuasiCompact.compactSpace_of_compactSpace M.toBase

/-- The total space of a model is a Noetherian scheme. -/
instance : AlgebraicGeometry.IsNoetherian M.total := {}

/-- The special fibre of a model is locally Noetherian, being a closed (hence locally of finite
type) subscheme of the locally Noetherian total space. -/
instance : IsLocallyNoetherian M.specialFiberScheme :=
  LocallyOfFiniteType.isLocallyNoetherian (specialFiberι R M.toBase)

/-- The special fibre of a model is quasi-compact: closed immersions are affine, hence
quasi-compact, morphisms. -/
instance : CompactSpace M.specialFiberScheme :=
  QuasiCompact.compactSpace_of_compactSpace (specialFiberι R M.toBase)

/-- The special fibre of a model is a Noetherian scheme. -/
instance : AlgebraicGeometry.IsNoetherian M.specialFiberScheme := {}

end NoetherianInstances

variable {M : Model R K C toK}

/-! ### The vanishing ideal of a component of the special fibre -/

/-- The closed subset of the total space swept out by a component of the special fibre: the
image of the abstract irreducible component under the closed immersion of the special fibre into
the total space. -/
def componentCloseds (i : ArithmeticSurface.Component M) : Closeds M.total where
  carrier := ArithmeticSurface.componentCarrierInTotal M i
  isClosed' :=
    (Scheme.Hom.isClosedEmbedding (specialFiberι R M.toBase)).isClosedMap _
      (isClosed_of_mem_irreducibleComponents (i : Set M.specialFiberScheme) i.2)

@[simp]
theorem coe_componentCloseds (i : ArithmeticSurface.Component M) :
    (componentCloseds i : Set M.total) = ArithmeticSurface.componentCarrierInTotal M i := rfl

/-- The (reduced) vanishing ideal sheaf, on the total space, of a component of the special
fibre. -/
def vanishingIdeal (i : ArithmeticSurface.Component M) : M.total.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (componentCloseds i)

/-- The support of the vanishing ideal of a component is exactly the closed subset it sweeps
out. -/
theorem vanishingIdeal_support (i : ArithmeticSurface.Component M) :
    (vanishingIdeal i).support = componentCloseds i :=
  StableReduction.support_vanishingIdeal (componentCloseds i)

/-- A point of the total space lies in the support of a component's vanishing ideal exactly
when it lies in the closed subset the component sweeps out. -/
theorem mem_support_vanishingIdeal_iff (i : ArithmeticSurface.Component M) (x : M.total) :
    x ∈ (vanishingIdeal i).support ↔ x ∈ componentCloseds i := by
  rw [vanishingIdeal_support]

/-! ### Local intersection numbers of two components -/

/-- The total intersection number of two components of the special fibre: the sum, over the
whole total space, of the stalk-theoretic local intersection multiplicities of their vanishing
ideals.  The summand vanishes outside the (set-theoretic) intersection of the two components, so
this is really a sum over that intersection locus. -/
def componentIntersection (i j : ArithmeticSurface.Component M) : ℕ∞ :=
  ∑ᶠ x, idealSheafIntersectionMultiplicity (vanishingIdeal i) (vanishingIdeal j) x

/-- The intersection number of two components does not depend on their order. -/
theorem componentIntersection_comm (i j : ArithmeticSurface.Component M) :
    componentIntersection i j = componentIntersection j i :=
  finsum_congr fun x ↦ idealSheafIntersectionMultiplicity_comm (vanishingIdeal i)
    (vanishingIdeal j) x

/-- Distinct components with disjoint carriers do not intersect at all. -/
theorem componentIntersection_eq_zero_of_disjoint (i j : ArithmeticSurface.Component M)
    (h : (componentCloseds i : Set M.total) ∩ componentCloseds j = ∅) :
    componentIntersection i j = 0 := by
  have hzero : ∀ x, idealSheafIntersectionMultiplicity (vanishingIdeal i) (vanishingIdeal j) x
      = 0 := by
    intro x
    apply idealSheafIntersectionMultiplicity_eq_zero_of_not_mem_support
    by_contra hx
    push Not at hx
    rw [mem_support_vanishingIdeal_iff, mem_support_vanishingIdeal_iff] at hx
    have hmem : x ∈ (componentCloseds i : Set M.total) ∩ componentCloseds j := ⟨hx.1, hx.2⟩
    rw [h] at hmem
    exact (Set.mem_empty_iff_false x).mp hmem
  rw [componentIntersection, finsum_congr hzero, finsum_zero]

/-- Finiteness of the intersection number of two components, under the explicit hypothesis that
they meet in finitely many points at each of which the sum of the two (stalk-level) vanishing
ideals already has maximal radical in a Noetherian stalk.  This is the "proper intersection with
0-dimensional local algebra" condition; deriving it from the bare `ArithmeticSurface` hypotheses
would need identifying the special fibre with the zero locus of the base uniformiser and
invoking Krull's principal ideal theorem to bound the dimension of each component, which is not
carried out here (see the module docstring). -/
theorem componentIntersection_ne_top (i j : ArithmeticSurface.Component M)
    (hfin : ((componentCloseds i : Set M.total) ∩ componentCloseds j).Finite)
    (hrad : ∀ x ∈ (componentCloseds i : Set M.total) ∩ componentCloseds j,
      IsNoetherianRing (M.total.presheaf.stalk x) ∧
        (stalkIdeal (vanishingIdeal i) x ⊔ stalkIdeal (vanishingIdeal j) x).radical =
          IsLocalRing.maximalIdeal (M.total.presheaf.stalk x)) :
    componentIntersection i j ≠ ⊤ := by
  have hsupp : Function.support
      (fun x ↦ idealSheafIntersectionMultiplicity (vanishingIdeal i) (vanishingIdeal j) x) ⊆
      (componentCloseds i : Set M.total) ∩ componentCloseds j := by
    intro x hx
    by_contra hxmem
    rw [Set.mem_inter_iff, not_and_or] at hxmem
    apply hx
    apply idealSheafIntersectionMultiplicity_eq_zero_of_not_mem_support
    rcases hxmem with hxi | hxj
    · exact Or.inl (mt (mem_support_vanishingIdeal_iff i x).mp hxi)
    · exact Or.inr (mt (mem_support_vanishingIdeal_iff j x).mp hxj)
  rw [componentIntersection, finsum_eq_sum_of_support_subset_of_finite _ hsupp hfin,
    Ne, ENat.sum_eq_top]
  rintro ⟨x, hx, htop⟩
  have hxmem : x ∈ (componentCloseds i : Set M.total) ∩ componentCloseds j := by
    rwa [Set.Finite.mem_toFinset] at hx
  obtain ⟨hnoeth, hradx⟩ := hrad x hxmem
  let _ : IsNoetherianRing (M.total.presheaf.stalk x) := hnoeth
  exact idealIntersectionMultiplicity_ne_top_of_radical_eq_maximalIdeal
    (stalkIdeal (vanishingIdeal i) x) (stalkIdeal (vanishingIdeal j) x) hradx
    (idealSheafIntersectionMultiplicity_eq_idealIntersectionMultiplicity (vanishingIdeal i)
      (vanishingIdeal j) x ▸ htop)

/-! ### The generic point of a component and the multiplicity of the special fibre there -/

/-- Every point of the special fibre, viewed in the total space, maps to the closed point of the
base under the structure map. -/
theorem toBase_specialFiberι (y : M.specialFiberScheme) :
    M.toBase (specialFiberι R M.toBase y) = dvrSpecialPoint R := by
  have hcond : M.toBase (specialFiberι R M.toBase y) =
      specialPointMap R ((specialFiber R M.toBase).hom y) :=
    congrArg (fun h : M.specialFiberScheme ⟶ Spec (.of R) ↦ h y)
      (specialFiberι_toBase R M.toBase)
  rw [hcond]
  have heq : ((specialResidueSpecIso R).hom ≫
      (Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R))
        ((specialFiber R M.toBase).hom y) = specialPointMap R ((specialFiber R M.toBase).hom y) :=
    congrArg (fun h : Spec (.of (specialResidueField R)) ⟶ Spec (.of R) ↦
      h ((specialFiber R M.toBase).hom y)) (specialResidueSpecIso_hom_fromSpecResidueField R)
  rw [← heq]
  have hmem : (Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R)
      ((specialResidueSpecIso R).hom ((specialFiber R M.toBase).hom y)) ∈
      Set.range ((Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R)) := ⟨_, rfl⟩
  rwa [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at hmem

/-- A choice of generic point, in the special fibre, of a component. -/
def specialFiberGenericPoint (i : ArithmeticSurface.Component M) : M.specialFiberScheme :=
  i.2.prop.genericPoint

/-- The chosen point of a component genuinely generates it, inside the special fibre. -/
theorem isGenericPoint_specialFiberGenericPoint (i : ArithmeticSurface.Component M) :
    IsGenericPoint (specialFiberGenericPoint i) (i : Set M.specialFiberScheme) := by
  have h := i.2.prop.isGenericPoint_genericPoint_closure
  rwa [(isClosed_of_mem_irreducibleComponents (i : Set M.specialFiberScheme) i.2).closure_eq]
    at h

/-- The generic point, in the total space, of a component of the special fibre. -/
def genericPoint (i : ArithmeticSurface.Component M) : M.total :=
  specialFiberι R M.toBase (specialFiberGenericPoint i)

/-- The generic point of a component genuinely generates the closed subset it sweeps out. -/
theorem isGenericPoint_genericPoint (i : ArithmeticSurface.Component M) :
    IsGenericPoint (genericPoint i) (componentCloseds i : Set M.total) := by
  have h := (isGenericPoint_specialFiberGenericPoint i).image
    (Scheme.Hom.isClosedEmbedding (specialFiberι R M.toBase)).continuous
  change IsGenericPoint (genericPoint i) (closure (componentCloseds i : Set M.total)) at h
  rwa [(componentCloseds i).isClosed.closure_eq] at h

/-- The generic point of a component lies over the closed point of the base. -/
theorem toBase_genericPoint (i : ArithmeticSurface.Component M) :
    M.toBase (genericPoint i) = dvrSpecialPoint R :=
  toBase_specialFiberι (specialFiberGenericPoint i)

/-- The germ, at a point of the total space, of an element of the base ring pulled back along
the structure map. -/
def baseElementGerm (x : M.total) (r : R) : M.total.presheaf.stalk x :=
  M.total.presheaf.germ ⊤ x trivial
    (M.toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv r))

/-- The germ of an element of the maximal ideal of the base, at a point mapping to the closed
point of the base, is not a unit. -/
theorem baseElementGerm_not_isUnit {x : M.total} (hx : M.toBase x = dvrSpecialPoint R)
    {r : R} (hr : r ∈ IsLocalRing.maximalIdeal R) : ¬ IsUnit (baseElementGerm x r) := by
  rw [baseElementGerm, ← Scheme.mem_basicOpen_top]
  intro hmem
  have hmem1 : x ∈ M.toBase ⁻¹ᵁ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv r) := by
    rw [Scheme.preimage_basicOpen_top]; exact hmem
  have hmem2 : M.toBase x ∈ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv r) :=
    TopologicalSpace.Opens.mem_map.mp hmem1
  have hbasic : (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv r) =
      PrimeSpectrum.basicOpen r := by
    rw [basicOpen_eq_of_affine', Iso.inv_hom_id_apply]
  rw [hbasic, hx] at hmem2
  exact ((PrimeSpectrum.mem_basicOpen r _).mp hmem2) ((IsLocalRing.mem_maximalIdeal r).mp hr)

/-- The order of vanishing, at the generic point of a component of the special fibre, of an
element of the base ring pulled back along the structure map.  For a uniformiser `π` this is the
multiplicity with which the component occurs in the special fibre divisor. -/
def componentMultiplicity (i : ArithmeticSurface.Component M) (π : R) : ℕ∞ :=
  Ring.ord (M.total.presheaf.stalk (genericPoint i)) (baseElementGerm (genericPoint i) π)

/-- The multiplicity of a component is positive as soon as the chosen element of the base ring
lies in the maximal ideal there, in particular for any uniformiser. -/
theorem componentMultiplicity_pos (i : ArithmeticSurface.Component M) {π : R}
    (hπ : π ∈ IsLocalRing.maximalIdeal R) : 0 < componentMultiplicity i π := by
  change 0 < Module.length (M.total.presheaf.stalk (genericPoint i))
    (M.total.presheaf.stalk (genericPoint i) ⧸
      Ideal.span {baseElementGerm (genericPoint i) π})
  rw [Module.length_pos_iff, Ideal.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top]
  exact baseElementGerm_not_isUnit (toBase_genericPoint i) hπ

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
