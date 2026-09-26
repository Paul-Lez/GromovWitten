/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import Mathlib.Topology.KrullDimension
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.SpecialFibreDimension

/-!
# The local rings of an arithmetic surface at closed points of the special fibre

`SpecialFibreDimension.lean` computes the local ring of a regular proper model `M` of a curve
over a discrete valuation ring `R` at the *generic* point of a component of the special fibre:
it is a discrete valuation ring.  This file treats the remaining points of the special fibre.

The bridge is the prime-to-point dictionary for `Scheme.fromSpecStalk`: the primes of
`𝒪_{M,x}` are exactly the points of the total space specialising to `x`, and such a prime
contains the germ of a uniformiser `π` of `R` exactly when the corresponding point lies on the
special fibre.  Consequently the primes of `𝒪_{M,x} ⧸ (π)` are exactly the points of the special
fibre specialising to `x`, and the Krull dimension of `𝒪_{M,x} ⧸ (π)` is the length of the
longest chain of specialisations inside the special fibre ending at `x`.

## Main results

* `stalkIdeal_le_iff_fromSpecStalk_mem_support`: the stalk ideal/support dictionary for an
  arbitrary ideal sheaf on an arbitrary scheme, together with the neighbourhood version
  `mem_basicOpen_fromSpecStalk_of_mem` of `mem_basicOpen_fromSpecStalk`.
* `toBase_fromSpecStalk_of_mem` / `baseElementGerm_mem_of_toBase_eq`: the primes of `𝒪_{M,x}`
  containing the germ of a uniformiser are exactly the points of the special fibre specialising
  to `x`.
* `ringKrullDim_quotient_baseElementGerm_le_one`: if every non-closed point of the special fibre
  is the generic point of an irreducible component of it (the "special fibre is at most
  one-dimensional" hypothesis `hgen`), then `dim (𝒪_{M,x} ⧸ (π)) ≤ 1` for every `x`.
* `ringKrullDim_quotient_baseElementGerm_eq_one`, `ringKrullDim_stalk_eq_two_of_isClosed`,
  `krullDimLE_two_stalk`: at a closed point of the special fibre of a regular proper model whose
  special fibre is a curve of pure dimension one, `dim (𝒪_{M,x} ⧸ (π)) = 1` and
  `dim 𝒪_{M,x} = 2`.
* `finite_componentCloseds_inter`: two distinct components of the special fibre meet in a finite
  set of closed points; `radical_sup_stalkIdeal_eq_maximalIdeal` shows the local intersection
  algebras there are zero-dimensional, whence `componentIntersection_ne_top_of_ne` and
  `coe_componentIntersectionNat_of_ne`: the intersection number of two *distinct* components of
  the special fibre is a genuine natural number.
* `specialFiberStalkQuotientHom` and `ringKrullDim_stalk_specialFiberScheme_le_one`: the stalk of
  the special fibre at a point is a quotient of `𝒪_{M,x} ⧸ (π)`, so it has Krull dimension at
  most one.

## Implementation notes

The `Model` structure carries flatness, local finite presentation and quasi-compactness of the
structure morphism, but no relative-dimension hypothesis, so the one-dimensionality of the
special fibre cannot be derived here; it is taken as an explicit hypothesis, in the form

* `hgen : ∀ y, M.toBase y = dvrSpecialPoint R → ¬ IsClosed {y} → ∃ i, y = genericPoint i`
  (the special fibre has dimension at most one), and
* `hnc : ∀ i, ¬ IsClosed {genericPoint i}` (no component of the special fibre is a point),

both of which are statements about the topology of the special fibre alone.  The first is
*equivalent* to the usual one-dimensionality statement: it is derived from
`topologicalKrullDim M.specialFiberScheme ≤ 1` in
`exists_eq_genericPoint_of_topologicalKrullDim_le_one`, and the main results are restated in that
form in `ringKrullDim_stalk_eq_two_of_topologicalKrullDim_le_one`,
`finite_componentCloseds_inter_of_topologicalKrullDim_le_one`,
`componentIntersection_ne_top_of_topologicalKrullDim_le_one` and
`coe_componentIntersectionNat_of_topologicalKrullDim_le_one`.

## Not done

`specialFiberStalkQuotientHom` is only shown to be surjective.  Its injectivity says that the
ideal sheaf of the special fibre is *generated* by the uniformiser `π`, equivalently that on an
affine chart `Spec A` of the total space the fibre is `Spec (A ⧸ π A)`; that is the affine base
change `A ⊗[R] (R ⧸ m) ≅ A ⧸ π A` for the pullback presentation of `specialFiber`, which is not
formalised here.  Consequently the ring isomorphism
`𝒪_{specialFibre, x'} ≅ 𝒪_{M,x} ⧸ (germ π)` is not available, only the surjection.
-/

open IsLocalRing
open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

/-- A closed subset of a Noetherian sober space all of whose points are closed is finite: the
subset is a finite union of irreducible closed sets, and each of those is the closure of its
generic point, hence a singleton. -/
theorem Set.Finite.of_isClosed_of_forall_isClosed_singleton {α : Type u} [TopologicalSpace α]
    [NoetherianSpace α] [QuasiSober α] {W : Set α} (hW : IsClosed W)
    (hpt : ∀ y ∈ W, IsClosed {y}) : W.Finite := by
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hW
  have hsing : ∀ t ∈ S, t.Finite := by
    intro t ht
    obtain ⟨y, hgen⟩ : ∃ y, closure {y} = t := by
      refine ⟨(hSi t ht).genericPoint, ?_⟩
      have h := (hSi t ht).isGenericPoint_genericPoint_closure
      rwa [(hSc t ht).closure_eq] at h
    have hmem : y ∈ t := by
      rw [← hgen]
      exact subset_closure rfl
    have hWmem : y ∈ W := by
      rw [hSU]
      exact Set.mem_sUnion_of_mem hmem ht
    rw [← hgen, (hpt _ hWmem).closure_eq]
    exact Set.finite_singleton _
  rw [hSU]
  exact hSf.sUnion hsing

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

noncomputable section

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)} {M : Model R K C toK}

/-! ### The prime-to-point dictionary along the special fibre -/

/-- The global section of the total space of a model obtained by pulling back an element of the
base ring along the structure morphism. -/
def baseElementSection (M : Model R K C toK) (r : R) : Γ(M.total, ⊤) :=
  M.toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv r)

@[simp]
theorem germ_baseElementSection (x : M.total) (r : R) :
    M.total.presheaf.germ ⊤ x trivial (baseElementSection M r) = baseElementGerm x r := rfl

/-- The basic open set of the pullback of an element of the base ring is the preimage of the
basic open set of that element. -/
theorem preimage_basicOpen_baseElementSection (r : R) :
    M.toBase ⁻¹ᵁ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv r) =
      M.total.basicOpen (baseElementSection M r) :=
  Scheme.preimage_basicOpen_top _ _

/-- A point of the total space at which the pullback of a generator `π` of the maximal ideal of
the base vanishes lies over the closed point of the base. -/
theorem toBase_eq_dvrSpecialPoint_of_notMem_basicOpen {y : M.total} {π : R}
    (hπ : maximalIdeal R = Ideal.span {π})
    (hy : y ∉ M.total.basicOpen (baseElementSection M π)) :
    M.toBase y = dvrSpecialPoint R := by
  have hbasic : (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv π) =
      PrimeSpectrum.basicOpen π := by
    rw [basicOpen_eq_of_affine', Iso.inv_hom_id_apply]
  have hnot : M.toBase y ∉ PrimeSpectrum.basicOpen π := by
    intro hc
    refine hy ?_
    rw [← preimage_basicOpen_baseElementSection]
    change M.toBase y ∈ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv π)
    rw [hbasic]
    exact hc
  have hin : π ∈ (M.toBase y).asIdeal := by
    by_contra hc
    exact hnot ((PrimeSpectrum.mem_basicOpen _ _).mpr hc)
  refine PrimeSpectrum.ext ((maximalIdeal.isMaximal R).eq_of_le
    (M.toBase y).isPrime.ne_top ?_).symm
  rw [hπ, Ideal.span_le, Set.singleton_subset_iff]
  exact hin

/-- **A prime of the stalk containing the germ of a uniformiser is a point of the special
fibre.**  Together with `baseElementGerm_mem_of_toBase_eq` this identifies the primes of
`𝒪_{M,x} ⧸ (π)` with the points of the special fibre specialising to `x`. -/
theorem toBase_fromSpecStalk_of_mem (x : M.total) {π : R} (hπ : maximalIdeal R = Ideal.span {π})
    {p : PrimeSpectrum (M.total.presheaf.stalk x)} (hp : baseElementGerm x π ∈ p.asIdeal) :
    M.toBase (M.total.fromSpecStalk x p) = dvrSpecialPoint R :=
  toBase_eq_dvrSpecialPoint_of_notMem_basicOpen hπ
    (by rw [mem_basicOpen_fromSpecStalk]; exact fun hc => hc hp)

/-- **A point of the special fibre specialising to `x` gives a prime of `𝒪_{M,x}` containing the
germ of any element of the maximal ideal of the base.** -/
theorem baseElementGerm_mem_of_toBase_eq (x : M.total) {π : R} (hπ : π ∈ maximalIdeal R)
    {p : PrimeSpectrum (M.total.presheaf.stalk x)}
    (hp : M.toBase (M.total.fromSpecStalk x p) = dvrSpecialPoint R) :
    baseElementGerm x π ∈ p.asIdeal := by
  by_contra hc
  have h1 : M.total.fromSpecStalk x p ∈ M.total.basicOpen (baseElementSection M π) :=
    (mem_basicOpen_fromSpecStalk _ _ _).mpr hc
  rw [Scheme.mem_basicOpen_top] at h1
  exact baseElementGerm_not_isUnit hp hπ h1

/-- Every point of the total space swept out by a component of the special fibre lies over the
closed point of the base. -/
theorem toBase_eq_of_mem_componentCloseds {i : ArithmeticSurface.Component M} {x : M.total}
    (hx : x ∈ (componentCloseds i : Set M.total)) : M.toBase x = dvrSpecialPoint R := by
  rw [coe_componentCloseds, ArithmeticSurface.componentCarrierInTotal] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact toBase_specialFiberι y

/-! ### One-dimensionality of the special fibre -/

/-- **There is no chain of three distinct specialising points on a special fibre of dimension at
most one.**  If `y₀` specialises to `y₁` and `y₁` to `y₂`, all three distinct and the first two on
the special fibre, then `y₀` and `y₁` are non-closed points, hence generic points of components of
the special fibre; but then one component contains the generic point of the other, so the two
components coincide and `y₀ = y₁`. -/
theorem not_specializes_chain
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    {y₀ y₁ y₂ : M.total} (h₀ : M.toBase y₀ = dvrSpecialPoint R)
    (h₁ : M.toBase y₁ = dvrSpecialPoint R) (hs₀ : y₀ ⤳ y₁) (hs₁ : y₁ ⤳ y₂)
    (hne₀ : y₀ ≠ y₁) (hne₁ : y₁ ≠ y₂) : False := by
  have hnc₀ : ¬ IsClosed ({y₀} : Set M.total) := fun hc =>
    hne₀ (Set.mem_singleton_iff.mp (hs₀.mem_closed hc rfl)).symm
  have hnc₁ : ¬ IsClosed ({y₁} : Set M.total) := fun hc =>
    hne₁ (Set.mem_singleton_iff.mp (hs₁.mem_closed hc rfl)).symm
  obtain ⟨i, hi⟩ := hgen y₀ h₀ hnc₀
  obtain ⟨j, hj⟩ := hgen y₁ h₁ hnc₁
  have hmem : genericPoint j ∈ (componentCloseds i : Set M.total) := by
    rw [← hj, ← isGenericPoint_genericPoint i, ← hi]
    exact specializes_iff_mem_closure.mp hs₀
  rcases eq_or_ne j i with rfl | hji
  · exact hne₀ (hi.trans hj.symm)
  · exact genericPoint_notMem_componentCloseds hji hmem

/-- **The germ of a uniformiser cuts the stalk down to dimension at most one**, at every point of
the total space, as soon as every non-closed point of the special fibre is the generic point of an
irreducible component of the special fibre.  Geometrically: a chain of primes of
`𝒪_{M,x} ⧸ (π)` is a chain of specialisations inside the special fibre ending at `x`, and there is
no chain of length two. -/
theorem ringKrullDim_quotient_baseElementGerm_le_one
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    (x : M.total) {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    ringKrullDim (M.total.presheaf.stalk x ⧸ Ideal.span {baseElementGerm x π}) ≤ 1 := by
  have hinj : Function.Injective (M.total.fromSpecStalk x) :=
    (Scheme.Hom.isEmbedding (M.total.fromSpecStalk x)).injective
  have hcont : Continuous (M.total.fromSpecStalk x) :=
    (Scheme.Hom.isEmbedding (M.total.fromSpecStalk x)).continuous
  rw [ringKrullDim_quotient, Order.krullDim_le_one_iff]
  intro q
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨p₀, hp₀⟩ := not_isMin_iff.mp hcon.1
  obtain ⟨p₂, hp₂⟩ := not_isMax_iff.mp hcon.2
  have hlt₀ : p₀.1 < q.1 := Subtype.coe_lt_coe.mpr hp₀
  have hlt₁ : q.1 < p₂.1 := Subtype.coe_lt_coe.mpr hp₂
  have hg : baseElementGerm x π ∈ p₀.1.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus _ _).mp p₀.2 (Ideal.mem_span_singleton_self _)
  refine not_specializes_chain hgen
    (toBase_fromSpecStalk_of_mem x hπ hg)
    (toBase_fromSpecStalk_of_mem x hπ (hlt₀.le hg))
    (((PrimeSpectrum.le_iff_specializes _ _).mp hlt₀.le).map hcont)
    (((PrimeSpectrum.le_iff_specializes _ _).mp hlt₁.le).map hcont)
    (fun hc => hlt₀.ne (hinj hc)) (fun hc => hlt₁.ne (hinj hc))

/-- **The special fibre is at least one-dimensional at a point of a component which is not the
generic point of that component**: the generic point of the component provides a prime of the
stalk strictly between the ideal generated by the germ of a uniformiser and the maximal ideal. -/
theorem one_le_ringKrullDim_quotient_baseElementGerm {x : M.total} {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) {i : ArithmeticSurface.Component M}
    (hxi : x ∈ (componentCloseds i : Set M.total)) (hne : x ≠ genericPoint i) :
    1 ≤ ringKrullDim (M.total.presheaf.stalk x ⧸ Ideal.span {baseElementGerm x π}) := by
  have hπmem : π ∈ maximalIdeal R := by
    rw [hπ]
    exact Ideal.mem_span_singleton_self π
  have hspec : genericPoint i ⤳ x := by
    refine specializes_iff_mem_closure.mpr ?_
    rw [isGenericPoint_genericPoint i]
    exact hxi
  have hrange : genericPoint i ∈ Set.range (M.total.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hspec
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum (M.total.presheaf.stalk x),
      M.total.fromSpecStalk x q = genericPoint i := hrange
  have hqmem : baseElementGerm x π ∈ q.asIdeal :=
    baseElementGerm_mem_of_toBase_eq x hπmem (by rw [hq]; exact toBase_genericPoint i)
  have hqne : q ≠ closedPoint (M.total.presheaf.stalk x) := by
    intro hc
    rw [hc, Scheme.fromSpecStalk_closedPoint] at hq
    exact hne hq
  rw [ringKrullDim_quotient]
  refine Order.one_le_krullDim_iff.mpr ⟨⟨q, ?_⟩, ⟨closedPoint (M.total.presheaf.stalk x), ?_⟩, ?_⟩
  · refine (PrimeSpectrum.mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqmem)))
  · refine (PrimeSpectrum.mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)))
    exact baseElementGerm_mem_maximalIdeal (toBase_eq_of_mem_componentCloseds hxi) hπmem
  · rw [Subtype.mk_lt_mk]
    exact lt_of_le_of_ne
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (IsLocalRing.le_maximalIdeal q.2.1)) hqne

/-- **The one-dimensionality hypothesis used throughout this file follows from the topological
Krull dimension of the special fibre being at most one.**  A point of the special fibre which is
neither closed nor the generic point of an irreducible component of the special fibre produces a
chain of three distinct irreducible closed subsets of the special fibre. -/
theorem exists_eq_genericPoint_of_topologicalKrullDim_le_one
    (htop : topologicalKrullDim M.specialFiberScheme ≤ 1) (y : M.total)
    (hy : M.toBase y = dvrSpecialPoint R) (hncl : ¬ IsClosed ({y} : Set M.total)) :
    ∃ i : ArithmeticSurface.Component M, y = genericPoint i := by
  have htop' : Order.krullDim (IrreducibleCloseds M.specialFiberScheme) ≤ 1 := htop
  obtain ⟨y', rfl⟩ : y ∈ Set.range (specialFiberι R M.toBase) := by
    rw [range_specialFiberι]
    exact hy
  have hncl' : ¬ IsClosed ({y'} : Set M.specialFiberScheme) := by
    intro hc
    refine hncl ?_
    have h := (Scheme.Hom.isClosedEmbedding (specialFiberι R M.toBase)).isClosedMap _ hc
    rwa [Set.image_singleton] at h
  rcases Order.krullDim_le_one_iff.mp htop'
    ⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩ with hmin | hmax
  · exfalso
    have hsub : ¬ (closure ({y'} : Set M.specialFiberScheme) ⊆ {y'}) := by
      intro hsub
      refine hncl' ?_
      rw [← Set.Subset.antisymm hsub subset_closure]
      exact isClosed_closure
    obtain ⟨z, hz, hzne⟩ := Set.not_subset.mp hsub
    have hle : (⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        IrreducibleCloseds M.specialFiberScheme) ≤
        ⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      isClosed_closure.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz)
    have heq : closure ({z} : Set M.specialFiberScheme) = closure {y'} :=
      le_antisymm hle (hmin hle)
    exact hzne (Set.mem_singleton_iff.mpr (IsGenericPoint.eq heq isGenericPoint_closure))
  · have hmem : closure ({y'} : Set M.specialFiberScheme) ∈
        irreducibleComponents M.specialFiberScheme := by
      refine ⟨isIrreducible_singleton.closure, fun {t} ht hle => ?_⟩
      have hle' : (⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩ :
          IrreducibleCloseds M.specialFiberScheme) ≤
          ⟨closure t, ht.closure, isClosed_closure⟩ := hle.trans subset_closure
      exact subset_closure.trans (hmax hle')
    refine ⟨⟨closure {y'}, hmem⟩, ?_⟩
    have hgp : y' = specialFiberGenericPoint
        (⟨closure {y'}, hmem⟩ : ArithmeticSurface.Component M) :=
      IsGenericPoint.eq isGenericPoint_closure (isGenericPoint_specialFiberGenericPoint _)
    rw [genericPoint, ← hgp]

/-! ### Dimension two at closed points of the special fibre -/

/-- Every point of the special fibre lies on some irreducible component of the special fibre. -/
theorem exists_mem_componentCloseds {x : M.total} (hx : M.toBase x = dvrSpecialPoint R) :
    ∃ i : ArithmeticSurface.Component M, x ∈ (componentCloseds i : Set M.total) := by
  obtain ⟨x', rfl⟩ : x ∈ Set.range (specialFiberι R M.toBase) := by
    rw [range_specialFiberι]
    exact hx
  have huniv : x' ∈ ⋃₀ irreducibleComponents M.specialFiberScheme := by
    rw [sUnion_irreducibleComponents]
    exact Set.mem_univ x'
  obtain ⟨Z, hZ, hxZ⟩ := huniv
  refine ⟨⟨Z, hZ⟩, ?_⟩
  rw [coe_componentCloseds, ArithmeticSurface.componentCarrierInTotal]
  exact ⟨x', hxZ, rfl⟩

/-- **The special fibre is exactly one-dimensional at each of its closed points.**  The upper bound
is the one-dimensionality hypothesis `hgen`; the lower bound comes from the generic point of a
component through the point, which is distinct from it because components are not points. -/
theorem ringKrullDim_quotient_baseElementGerm_eq_one
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    (hnc : ∀ i : ArithmeticSurface.Component M,
      ¬ IsClosed ({genericPoint i} : Set M.total))
    {x : M.total} (hx : M.toBase x = dvrSpecialPoint R) (hxc : IsClosed ({x} : Set M.total))
    {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    ringKrullDim (M.total.presheaf.stalk x ⧸ Ideal.span {baseElementGerm x π}) = 1 := by
  obtain ⟨i, hxi⟩ := exists_mem_componentCloseds hx
  refine le_antisymm (ringKrullDim_quotient_baseElementGerm_le_one hgen x hπ)
    (one_le_ringKrullDim_quotient_baseElementGerm hπ hxi ?_)
  intro hc
  rw [hc] at hxc
  exact hnc i hxc

/-- **The local ring of a regular proper model at a closed point of the special fibre has Krull
dimension two.**  Together with regularity this makes it a two-dimensional regular local ring,
the local model of an arithmetic surface. -/
theorem ringKrullDim_stalk_eq_two_of_isClosed (hM : ArithmeticSurface M)
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    (hnc : ∀ i : ArithmeticSurface.Component M,
      ¬ IsClosed ({genericPoint i} : Set M.total))
    {x : M.total} (hx : M.toBase x = dvrSpecialPoint R) (hxc : IsClosed ({x} : Set M.total))
    {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    ringKrullDim (M.total.presheaf.stalk x) = 2 :=
  ringKrullDim_stalk_eq_two hM hx (hπ ▸ Ideal.mem_span_singleton_self π)
    (uniformiser_ne_zero hπ) (ringKrullDim_quotient_baseElementGerm_eq_one hgen hnc hx hxc hπ)

/-- The local ring of a regular proper model at a closed point of the special fibre has Krull
dimension at most two. -/
theorem krullDimLE_two_stalk (hM : ArithmeticSurface M)
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    (hnc : ∀ i : ArithmeticSurface.Component M,
      ¬ IsClosed ({genericPoint i} : Set M.total))
    {x : M.total} (hx : M.toBase x = dvrSpecialPoint R) (hxc : IsClosed ({x} : Set M.total))
    {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    Ring.KrullDimLE 2 (M.total.presheaf.stalk x) :=
  Ring.krullDimLE_iff.mpr
    (le_of_eq (ringKrullDim_stalk_eq_two_of_isClosed hM hgen hnc hx hxc hπ))

/-! ### Finiteness of the intersection locus of two distinct components -/

/-- A point lying on two distinct components of the special fibre is a closed point: a non-closed
point of the special fibre is the generic point of a component, and the generic point of a
component lies on no other component. -/
theorem isClosed_singleton_of_mem_componentCloseds_inter
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    {i j : ArithmeticSurface.Component M} (hij : i ≠ j) {y : M.total}
    (hy : y ∈ (componentCloseds i : Set M.total) ∩ componentCloseds j) :
    IsClosed ({y} : Set M.total) := by
  by_contra hc
  obtain ⟨k, rfl⟩ := hgen y (toBase_eq_of_mem_componentCloseds hy.1) hc
  have h1 : k = i := by
    by_contra hki
    exact genericPoint_notMem_componentCloseds hki hy.1
  have h2 : k = j := by
    by_contra hkj
    exact genericPoint_notMem_componentCloseds hkj hy.2
  exact hij (h1.symm.trans h2)

/-- **Two distinct components of the special fibre meet in a finite set.**  Their intersection is a
closed subset of the Noetherian sober space `M.total` all of whose points are closed. -/
theorem finite_componentCloseds_inter
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    {i j : ArithmeticSurface.Component M} (hij : i ≠ j) :
    ((componentCloseds i : Set M.total) ∩ componentCloseds j).Finite :=
  Set.Finite.of_isClosed_of_forall_isClosed_singleton
    ((componentCloseds i).isClosed.inter (componentCloseds j).isClosed)
    fun _ hy => isClosed_singleton_of_mem_componentCloseds_inter hgen hij hy

/-! ### The stalk ideal of an ideal sheaf and its support -/

section IdealSheaf

variable {X : Scheme.{u}}

/-- The point of `X` determined by a prime of the stalk at `x` lies in every open neighbourhood of
`x`: it specialises to `x`. -/
theorem fromSpecStalk_mem_of_mem {x : X} {U : X.Opens} (hxU : x ∈ U)
    (p : PrimeSpectrum (X.presheaf.stalk x)) : X.fromSpecStalk x p ∈ U := by
  have hr : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hr
  exact hr.mem_open U.2 hxU

/-- **A point of `Spec 𝒪_{X,x}` lands in the basic open set of a section over a neighbourhood `U`
of `x` exactly when the germ of that section at `x` avoids the corresponding prime.**  This is the
version of `mem_basicOpen_fromSpecStalk` for an arbitrary open neighbourhood of `x`. -/
theorem mem_basicOpen_fromSpecStalk_of_mem {x : X} {U : X.Opens} (hxU : x ∈ U) (s : Γ(X, U))
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ X.basicOpen s ↔ X.presheaf.germ U x hxU s ∉ p.asIdeal := by
  have hmemU : p ∈ X.fromSpecStalk x ⁻¹ᵁ U := fromSpecStalk_mem_of_mem hxU p
  have h1 : X.fromSpecStalk x ⁻¹ᵁ X.basicOpen s =
      (Spec (X.presheaf.stalk x)).basicOpen ((X.fromSpecStalk x).app U s) :=
    Scheme.preimage_basicOpen _ s
  have h3 : (Spec (X.presheaf.stalk x)).basicOpen ((X.fromSpecStalk x).app U s) =
      (X.fromSpecStalk x ⁻¹ᵁ U) ⊓ PrimeSpectrum.basicOpen (X.presheaf.germ U x hxU s) := by
    rw [Scheme.fromSpecStalk_app hxU, CommRingCat.comp_apply, CommRingCat.comp_apply,
      Scheme.basicOpen_res, basicOpen_eq_of_affine', Iso.inv_hom_id_apply]
  constructor
  · intro hmem
    have hmem' : p ∈ X.fromSpecStalk x ⁻¹ᵁ X.basicOpen s := hmem
    rw [h1, h3] at hmem'
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hmem'.2
  · intro hnot
    have hmem' : p ∈ (X.fromSpecStalk x ⁻¹ᵁ U) ⊓
        PrimeSpectrum.basicOpen (X.presheaf.germ U x hxU s) :=
      ⟨hmemU, (PrimeSpectrum.mem_basicOpen _ _).mpr hnot⟩
    rw [← h3, ← h1] at hmem'
    exact hmem'

/-- **The stalk ideal/support dictionary.**  A prime of `𝒪_{X,x}` contains the stalk ideal of an
ideal sheaf exactly when the corresponding point of `X` lies in the support of the ideal sheaf. -/
theorem stalkIdeal_le_iff_fromSpecStalk_mem_support (I : X.IdealSheafData) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    stalkIdeal I x ≤ p.asIdeal ↔ X.fromSpecStalk x p ∈ I.support := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hmemU : X.fromSpecStalk x p ∈ U := fromSpecStalk_mem_of_mem hxU p
  rw [stalkIdeal_eq_map I x ⟨U, hU⟩ hxU, Ideal.map_le_iff_le_comap,
    I.mem_support_iff_of_mem (U := ⟨U, hU⟩) hmemU, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h f hf
    rw [mem_basicOpen_fromSpecStalk_of_mem hxU]
    exact fun hc => hc (h hf)
  · intro h f hf
    by_contra hc
    exact h f hf ((mem_basicOpen_fromSpecStalk_of_mem hxU f p).mpr hc)

end IdealSheaf

/-! ### Intersection numbers of two distinct components -/

/-- **The scheme-theoretic intersection of two distinct components of the special fibre is
zero-dimensional at each of its points.**  A prime of the stalk containing the sum of the two
stalk-level vanishing ideals corresponds to a point lying on both components, hence to a closed
point specialising to `x`, hence to `x` itself. -/
theorem radical_sup_stalkIdeal_eq_maximalIdeal
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    {i j : ArithmeticSurface.Component M} (hij : i ≠ j) {x : M.total}
    (hx : x ∈ (componentCloseds i : Set M.total) ∩ componentCloseds j) :
    (stalkIdeal (vanishingIdeal i) x ⊔ stalkIdeal (vanishingIdeal j) x).radical =
      maximalIdeal (M.total.presheaf.stalk x) := by
  have hinj : Function.Injective (M.total.fromSpecStalk x) :=
    (Scheme.Hom.isEmbedding (M.total.fromSpecStalk x)).injective
  have hzl : PrimeSpectrum.zeroLocus
      ((stalkIdeal (vanishingIdeal i) x ⊔ stalkIdeal (vanishingIdeal j) x :
        Ideal (M.total.presheaf.stalk x)) : Set _) =
      {closedPoint (M.total.presheaf.stalk x)} := by
    refine Set.Subset.antisymm (fun p hp => ?_) (fun q hq => ?_)
    · have hle : stalkIdeal (vanishingIdeal i) x ⊔ stalkIdeal (vanishingIdeal j) x ≤ p.asIdeal :=
        SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hp)
      have h1 : M.total.fromSpecStalk x p ∈ (componentCloseds i : Set M.total) := by
        have h := (stalkIdeal_le_iff_fromSpecStalk_mem_support _ _ _).mp (le_sup_left.trans hle)
        rwa [vanishingIdeal_support] at h
      have h2 : M.total.fromSpecStalk x p ∈ (componentCloseds j : Set M.total) := by
        have h := (stalkIdeal_le_iff_fromSpecStalk_mem_support _ _ _).mp (le_sup_right.trans hle)
        rwa [vanishingIdeal_support] at h
      have hclosed :=
        isClosed_singleton_of_mem_componentCloseds_inter hgen hij (Set.mem_inter h1 h2)
      have hspec : M.total.fromSpecStalk x p ⤳ x := by
        have hr : M.total.fromSpecStalk x p ∈ Set.range (M.total.fromSpecStalk x) := ⟨p, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at hr
      have hxeq : x = M.total.fromSpecStalk x p :=
        Set.mem_singleton_iff.mp (hspec.mem_closed hclosed rfl)
      refine Set.mem_singleton_iff.mpr (hinj ?_)
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hxeq.symm
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      refine (PrimeSpectrum.mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr (sup_le ?_ ?_))
      · refine (stalkIdeal_le_iff_fromSpecStalk_mem_support _ _ _).mpr ?_
        rw [Scheme.fromSpecStalk_closedPoint, vanishingIdeal_support]
        exact hx.1
      · refine (stalkIdeal_le_iff_fromSpecStalk_mem_support _ _ _).mpr ?_
        rw [Scheme.fromSpecStalk_closedPoint, vanishingIdeal_support]
        exact hx.2
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hzl,
    PrimeSpectrum.vanishingIdeal_singleton]
  rfl

/-- **The intersection number of two distinct components of the special fibre is a genuine natural
number.**  Both hypotheses of `componentIntersection_ne_top_of_radical_eq` are now discharged:
finiteness of the intersection locus by `finite_componentCloseds_inter` and zero-dimensionality of
the local intersection algebras by `radical_sup_stalkIdeal_eq_maximalIdeal`. -/
theorem componentIntersection_ne_top_of_ne (hM : ArithmeticSurface M)
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    {i j : ArithmeticSurface.Component M} (hij : i ≠ j) :
    componentIntersection i j ≠ ⊤ :=
  componentIntersection_ne_top_of_radical_eq hM i j (finite_componentCloseds_inter hgen hij)
    fun _ hx => radical_sup_stalkIdeal_eq_maximalIdeal hgen hij hx

/-- The natural-number intersection number of two distinct components of the special fibre really
is the `ℕ∞`-valued one. -/
theorem coe_componentIntersectionNat_of_ne (hM : ArithmeticSurface M)
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    {i j : ArithmeticSurface.Component M} (hij : i ≠ j) :
    (componentIntersectionNat i j : ℕ∞) = componentIntersection i j :=
  ENat.natCast_toNat (componentIntersection_ne_top_of_ne hM hgen hij)

/-! ### The stalks of the special fibre -/

/-- The pullback of a generator of the maximal ideal of the base to the special fibre vanishes:
the structure morphism of the special fibre factors through the residue field of the base. -/
theorem appTop_specialFiberι_baseElementSection {π : R} (hπ : π ∈ maximalIdeal R) :
    (specialFiberι R M.toBase).appTop (baseElementSection M π) = 0 := by
  have happ : (Spec.map (CommRingCat.ofHom
        (algebraMap R (specialResidueField R)))).appTop ((Scheme.ΓSpecIso (.of R)).inv π) =
      (Scheme.ΓSpecIso (.of (specialResidueField R))).inv
        (algebraMap R (specialResidueField R) π) :=
    (congrArg (fun g : (CommRingCat.of R) ⟶ _ => g π) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap R (specialResidueField R))))).symm
  have hzero : (specialPointMap R).appTop ((Scheme.ΓSpecIso (.of R)).inv π) = 0 := by
    rw [show (specialPointMap R).appTop = (Spec.map (CommRingCat.ofHom
      (algebraMap R (specialResidueField R)))).appTop from rfl, happ,
      Ideal.algebraMap_residueField_eq_zero.mpr hπ, map_zero]
  have hcomp : (specialFiberι R M.toBase).appTop (baseElementSection M π) =
      ((specialFiber R M.toBase).hom ≫ specialPointMap R).appTop
        ((Scheme.ΓSpecIso (.of R)).inv π) := by
    rw [← specialFiberι_toBase R M.toBase, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rfl
  rw [hcomp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hzero, map_zero]

/-- **The germ of a uniformiser of the base vanishes in every stalk of the special fibre.** -/
theorem stalkMap_specialFiberι_baseElementGerm (x' : M.specialFiberScheme) {π : R}
    (hπ : π ∈ maximalIdeal R) :
    (specialFiberι R M.toBase).stalkMap x'
        (baseElementGerm (specialFiberι R M.toBase x') π) = 0 := by
  have h : baseElementGerm (specialFiberι R M.toBase x') π =
      M.total.presheaf.germ ⊤ (specialFiberι R M.toBase x') trivial
        (baseElementSection M π) := rfl
  rw [h, Scheme.Hom.germ_stalkMap_apply (specialFiberι R M.toBase) ⊤ x' trivial,
    show (specialFiberι R M.toBase).app ⊤ (baseElementSection M π) = 0 from
      appTop_specialFiberι_baseElementSection hπ, map_zero]

/-- **The stalk of the special fibre at a point is a quotient of the stalk of the total space by
the germ of a uniformiser of the base.**  The stalk map of the closed immersion `specialFiberι` is
surjective and kills the germ of `π`, hence induces a surjection
`𝒪_{M,x} ⧸ (germ π) → 𝒪_{specialFibre, x'}`.  That this surjection is injective — i.e. that the
ideal sheaf of the special fibre is *generated* by `π` — is the flat base-change statement that is
not available here. -/
def specialFiberStalkQuotientHom (x' : M.specialFiberScheme) {π : R}
    (hπ : π ∈ maximalIdeal R) :
    (M.total.presheaf.stalk (specialFiberι R M.toBase x') ⧸
        Ideal.span {baseElementGerm (specialFiberι R M.toBase x') π}) →+*
      M.specialFiberScheme.presheaf.stalk x' :=
  Ideal.Quotient.lift _ ((specialFiberι R M.toBase).stalkMap x').hom (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, stalkMap_specialFiberι_baseElementGerm x' hπ, mul_zero])

@[simp]
theorem specialFiberStalkQuotientHom_mk (x' : M.specialFiberScheme) {π : R}
    (hπ : π ∈ maximalIdeal R)
    (a : M.total.presheaf.stalk (specialFiberι R M.toBase x')) :
    specialFiberStalkQuotientHom x' hπ (Ideal.Quotient.mk _ a) =
      (specialFiberι R M.toBase).stalkMap x' a := rfl

/-- The comparison map from the stalk of the total space modulo the germ of a uniformiser onto the
stalk of the special fibre is surjective. -/
theorem specialFiberStalkQuotientHom_surjective (x' : M.specialFiberScheme) {π : R}
    (hπ : π ∈ maximalIdeal R) :
    Function.Surjective (specialFiberStalkQuotientHom x' hπ) := by
  intro y
  obtain ⟨z, hz⟩ := (specialFiberι R M.toBase).stalkMap_surjective x' y
  exact ⟨Ideal.Quotient.mk _ z, hz⟩

/-- **The special fibre has one-dimensional local rings**: the stalk of the special fibre at any
point has Krull dimension at most one, under the one-dimensionality hypothesis on the special
fibre. -/
theorem ringKrullDim_stalk_specialFiberScheme_le_one
    (hgen : ∀ y : M.total, M.toBase y = dvrSpecialPoint R → ¬ IsClosed ({y} : Set M.total) →
      ∃ i : ArithmeticSurface.Component M, y = genericPoint i)
    (x' : M.specialFiberScheme) {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    ringKrullDim (M.specialFiberScheme.presheaf.stalk x') ≤ 1 := by
  have hπmem : π ∈ maximalIdeal R := by
    rw [hπ]
    exact Ideal.mem_span_singleton_self π
  exact le_trans (ringKrullDim_le_of_surjective _
      (specialFiberStalkQuotientHom_surjective x' hπmem))
    (ringKrullDim_quotient_baseElementGerm_le_one hgen _ hπ)

/-! ### The main statements for a one-dimensional special fibre -/

/-- **The local ring of a regular proper model at a closed point of the special fibre has Krull
dimension two**, for a model whose special fibre has topological Krull dimension at most one and
none of whose components is a single point. -/
theorem ringKrullDim_stalk_eq_two_of_topologicalKrullDim_le_one (hM : ArithmeticSurface M)
    (htop : topologicalKrullDim M.specialFiberScheme ≤ 1)
    (hnc : ∀ i : ArithmeticSurface.Component M,
      ¬ IsClosed ({genericPoint i} : Set M.total))
    {x : M.total} (hx : M.toBase x = dvrSpecialPoint R) (hxc : IsClosed ({x} : Set M.total))
    {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    ringKrullDim (M.total.presheaf.stalk x) = 2 :=
  ringKrullDim_stalk_eq_two_of_isClosed hM
    (exists_eq_genericPoint_of_topologicalKrullDim_le_one htop) hnc hx hxc hπ

/-- **Two distinct components of the special fibre meet in a finite set of closed points**, for a
model whose special fibre has topological Krull dimension at most one. -/
theorem finite_componentCloseds_inter_of_topologicalKrullDim_le_one
    (htop : topologicalKrullDim M.specialFiberScheme ≤ 1)
    {i j : ArithmeticSurface.Component M} (hij : i ≠ j) :
    ((componentCloseds i : Set M.total) ∩ componentCloseds j).Finite :=
  finite_componentCloseds_inter (exists_eq_genericPoint_of_topologicalKrullDim_le_one htop) hij

/-- **The intersection number of two distinct components of the special fibre of a regular proper
model is a genuine natural number**, for a model whose special fibre has topological Krull
dimension at most one. -/
theorem componentIntersection_ne_top_of_topologicalKrullDim_le_one (hM : ArithmeticSurface M)
    (htop : topologicalKrullDim M.specialFiberScheme ≤ 1)
    {i j : ArithmeticSurface.Component M} (hij : i ≠ j) :
    componentIntersection i j ≠ ⊤ :=
  componentIntersection_ne_top_of_ne hM
    (exists_eq_genericPoint_of_topologicalKrullDim_le_one htop) hij

/-- The natural-number intersection number of two distinct components of the special fibre of a
regular proper model with a one-dimensional special fibre agrees with the `ℕ∞`-valued one. -/
theorem coe_componentIntersectionNat_of_topologicalKrullDim_le_one (hM : ArithmeticSurface M)
    (htop : topologicalKrullDim M.specialFiberScheme ≤ 1)
    {i j : ArithmeticSurface.Component M} (hij : i ≠ j) :
    (componentIntersectionNat i j : ℕ∞) = componentIntersection i j :=
  ENat.natCast_toNat (componentIntersection_ne_top_of_topologicalKrullDim_le_one hM htop hij)

/-- The stalk of the special fibre of a model with a one-dimensional special fibre has Krull
dimension at most one at every point. -/
theorem ringKrullDim_stalk_specialFiberScheme_le_one_of_topologicalKrullDim_le_one
    (htop : topologicalKrullDim M.specialFiberScheme ≤ 1) (x' : M.specialFiberScheme) {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) :
    ringKrullDim (M.specialFiberScheme.presheaf.stalk x') ≤ 1 :=
  ringKrullDim_stalk_specialFiberScheme_le_one
    (exists_eq_genericPoint_of_topologicalKrullDim_le_one htop) x' hπ

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
