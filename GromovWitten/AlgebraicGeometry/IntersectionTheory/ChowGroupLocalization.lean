/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup

/-!
# Flat pullback along open immersions and the localization sequence

This file constructs the flat pullback of dimension-graded rational cycles along an open
immersion, proves that it is functorial and that it descends through rational equivalence, and
assembles the right-exact part of the localization sequence.

An open immersion is flat of relative dimension zero and all of its pullback multiplicities are
one, so the pullback of cycles is literally restriction of coefficient functions.  The content is
that restriction sends a principal divisor to a principal divisor: the trace of an integral closed
subscheme on an open set is again integral, its function field is canonically the same, and the
scheme-theoretic order of vanishing is unchanged.  The last point is the etale invariance of the
order of vanishing proved in `ChowGroup.lean`.

The file also proves that the principal divisor of a rational function on an integral locally
Noetherian scheme lies in the canonical rational-equivalence subspace, so its rational Chow class
is zero; this is the codimension-one comparison in the form the Chow-group definition uses.

## What is still missing for general proper pushforward

`cyclesOfDimension.properPushforward` already exists for an arbitrary proper morphism of locally
Noetherian schemes and is proved functorial, and `RationalEquivalenceSystem.DescendingMap`
descends it to Chow groups whenever it preserves the canonical span of principal divisors.  That
preservation is proved here and in `ChowGroup.lean` for closed immersions (and for isomorphisms),
but not for a general proper morphism.  The precise missing input is the norm/divisor theorem
(Fulton, *Intersection Theory*, Proposition 1.4): for a proper surjective morphism `p : Z → W` of
integral locally Noetherian schemes and a nonzero `f : K(Z)`,

* if `dim W < dim Z` then `p_* div_Z(f) = 0`, and
* if `dim W = dim Z` then `K(Z)/K(W)` is a finite field extension and
  `p_* div_Z(f) = div_W (N_{K(Z)/K(W)} f)`.

Neither the field norm along a finite extension of function fields of schemes, nor the additivity
of `Ring.ord` along a finite local extension which the theorem rests on, is available in Mathlib
v4.33.1 (`Mathlib/RingTheory/OrderOfVanishing/*` and `Mathlib/AlgebraicGeometry/OrderOfVanishing`
contain no norm statements), so no unconditional general statement is made here.
-/

open CategoryTheory TopologicalSpace Topology Order

open scoped AlgebraicGeometry

attribute [local instance] specializationOrder

namespace AlgebraicGeometry.Scheme

universe u

/-! ## Codimension is preserved by open immersions -/

/-- An open immersion of schemes preserves the codimension of every point.  Open sets are stable
under generization, so every chain of generizations of an image point lifts. -/
lemma coheight_eq_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    coheight x = coheight (f.base x) := by
  apply Order.coheight_eq_of_strictMono f.base
  · intro a b hab
    apply lt_of_le_of_ne
    · change f.base b ⤳ f.base a
      exact f.base.hom.map_specializes (show b ⤳ a from hab.le)
    · intro h
      exact hab.ne (f.isOpenEmbedding.injective h)
  · intro a b hab
    have hspec : b ⤳ f.base a := hab.le
    have hb : b ∈ Set.range f.base :=
      hspec.mem_open f.isOpenEmbedding.isOpen_range ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ := hb
    refine ⟨a', ?_, rfl⟩
    apply lt_of_le_of_ne
    · change a' ⤳ a
      exact f.isOpenEmbedding.isInducing.specializes_iff.mp hab.le
    · rintro rfl
      exact hab.ne rfl

/-- An open immersion from a nonempty scheme into an irreducible scheme is dominant. -/
lemma isDominant_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [Nonempty X] [IrreducibleSpace Y] : IsDominant f := by
  refine ⟨?_⟩
  exact f.isOpenEmbedding.isOpen_range.dense ⟨f.base (Nonempty.some ‹_›), Set.mem_range_self _⟩

/-- A nonempty open subscheme of an irreducible scheme is dominant in it. -/
instance isDominant_opens_ι {Y : Scheme.{u}} (V : Y.Opens) [Nonempty V] [IrreducibleSpace Y] :
    IsDominant V.ι :=
  isDominant_of_isOpenImmersion _

/-- The order of vanishing is unchanged by pullback along a dominant open immersion of integral
locally Noetherian schemes.  Both the codimension of the point and the local length computation
are preserved; nothing is assumed about the divisor. -/
lemma ord_dominantFunctionFieldMap_of_isOpenImmersion
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsOpenImmersion f] [IsDominant f] (x : X) (q : Y.functionField) :
    X.ord (dominantFunctionFieldMap f q) x = Y.ord q (f.base x) := by
  have hcoheight : coheight x = coheight (f.base x) := coheight_eq_of_isOpenImmersion f x
  by_cases hx : coheight x = 1
  · have hy : coheight (f.base x) = 1 := hcoheight ▸ hx
    rw [← etaleLocalFunctionFieldMap_eq_dominantFunctionFieldMap f x]
    exact ord_etaleLocalFunctionFieldMap f x hx hy q
  · have hy : coheight (f.base x) ≠ 1 := fun h ↦ hx (hcoheight.trans h)
    rw [X.ord_eq_zero_of_coheight_neq_one hx, Y.ord_eq_zero_of_coheight_neq_one hy]

end AlgebraicGeometry.Scheme

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

namespace AlgebraicCycle

variable {X Y : Scheme.{u}}

/-! ## Flat pullback of cycles along an open immersion

An open immersion is flat of relative dimension zero, and every fibre of an open immersion over a
point of its image is a single reduced point.  Hence all pullback multiplicities equal one and the
pullback of a cycle is the restriction of its coefficient function. -/

/-- Flat pullback of a rational algebraic cycle along an open immersion.  Every multiplicity is
one because the scheme-theoretic fibres of an open immersion are single reduced points. -/
noncomputable def pullbackOpen (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsOpenImmersion f]
    (c : AlgebraicCycle Y ℚ) : AlgebraicCycle X ℚ where
  toFun x := c (f.base x)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ := by
    obtain ⟨t, ht, hfinite⟩ := c.supportLocallyFiniteWithinDomain (f.base x) (by trivial)
    refine ⟨f.base ⁻¹' t, f.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
    apply Set.Finite.of_finite_image (f := f.base) (hfinite.subset ?_)
    · exact f.isOpenEmbedding.injective.injOn
    · rintro y ⟨z, hz, rfl⟩
      exact ⟨hz.1, hz.2⟩

@[simp]
lemma pullbackOpen_apply (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsOpenImmersion f]
    (c : AlgebraicCycle Y ℚ) (x : X) : pullbackOpen f c x = c (f.base x) :=
  rfl

/-- Flat pullback along an open immersion is additive. -/
lemma pullbackOpen_add (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsOpenImmersion f]
    (c d : AlgebraicCycle Y ℚ) :
    pullbackOpen f (c + d) = pullbackOpen f c + pullbackOpen f d := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  simp

/-- Flat pullback along an open immersion commutes with rational scalars. -/
lemma pullbackOpen_smul (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsOpenImmersion f]
    (q : ℚ) (c : AlgebraicCycle Y ℚ) :
    pullbackOpen f (q • c) = q • pullbackOpen f c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  simp

/-- Flat pullback along an open immersion, bundled with its proved rational linearity. -/
noncomputable def pullbackOpenLinear (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsOpenImmersion f] :
    AlgebraicCycle Y ℚ →ₗ[ℚ] AlgebraicCycle X ℚ where
  toFun := pullbackOpen f
  map_add' := pullbackOpen_add f
  map_smul' := pullbackOpen_smul f

@[simp]
lemma pullbackOpenLinear_apply (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsOpenImmersion f]
    (c : AlgebraicCycle Y ℚ) : pullbackOpenLinear f c = pullbackOpen f c :=
  rfl

/-- Flat pullback along the identity open immersion is the identity. -/
@[simp]
lemma pullbackOpen_id (c : AlgebraicCycle X ℚ) : pullbackOpen (𝟙 X) c = c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  rfl

/-- Flat pullback along open immersions is contravariantly functorial. -/
@[simp]
lemma pullbackOpen_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [_root_.AlgebraicGeometry.IsOpenImmersion f] [_root_.AlgebraicGeometry.IsOpenImmersion g]
    (c : AlgebraicCycle Z ℚ) :
    pullbackOpen f (pullbackOpen g c) = pullbackOpen (f ≫ g) c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  rfl

/-- Flat pullback along an open subscheme commutes with the residue-degree pushforward of a
closed immersion: the trace of the closed subscheme is its scheme-theoretic restriction.  Both
pushforwards use the pulled-back weight, so every multiplicity is one. -/
lemma pullbackOpen_map_closedImmersion {W : Scheme.{u}} (i : W ⟶ X) (U : X.Opens)
    [_root_.AlgebraicGeometry.IsClosedImmersion i]
    (wX : X → ℤ) (wU : U.toScheme → ℤ) (c : AlgebraicCycle W ℚ) :
    pullbackOpen U.ι
        (_root_.AlgebraicGeometry.AlgebraicCycle.map i (fun w ↦ wX (i.base w)) wX c) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (i ∣_ U)
        (fun w ↦ wU ((i ∣_ U).base w)) wU (pullbackOpen (i ⁻¹ᵁ U).ι c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext u
  change _root_.AlgebraicGeometry.AlgebraicCycle.map i (fun w ↦ wX (i.base w)) wX c
      (U.ι.base u) =
    _root_.AlgebraicGeometry.AlgebraicCycle.map (i ∣_ U) (fun w ↦ wU ((i ∣_ U).base w)) wU
      (pullbackOpen (i ⁻¹ᵁ U).ι c) u
  by_cases hmem : U.ι.base u ∈ Set.range i.base
  · obtain ⟨z, hz⟩ := hmem
    have hzU : z ∈ i ⁻¹ᵁ U := by
      change i.base z ∈ U
      rw [hz]
      exact u.2
    have hw : (i ∣_ U).base (⟨z, hzU⟩ : (i ⁻¹ᵁ U).toScheme) = u := by
      apply Subtype.ext
      exact (_root_.AlgebraicGeometry.morphismRestrict_base_coe i U ⟨z, hzU⟩).trans hz
    have hL : _root_.AlgebraicGeometry.AlgebraicCycle.map i
        (fun w ↦ wX (i.base w)) wX c (U.ι.base u) = c z := by
      rw [← hz]
      exact map_closedImmersion_apply_image i wX c z
    have hR : _root_.AlgebraicGeometry.AlgebraicCycle.map (i ∣_ U)
        (fun w ↦ wU ((i ∣_ U).base w)) wU (pullbackOpen (i ⁻¹ᵁ U).ι c) u = c z := by
      rw [← hw]
      exact map_closedImmersion_apply_image (i ∣_ U) wU
        (pullbackOpen (i ⁻¹ᵁ U).ι c) ⟨z, hzU⟩
    rw [hL, hR]
  · have hnot : u ∉ Set.range (i ∣_ U).base := by
      rintro ⟨w, hw⟩
      refine hmem ⟨w.1, ?_⟩
      rw [← hw]
      exact (_root_.AlgebraicGeometry.morphismRestrict_base_coe i U w).symm
    rw [map_closedImmersion_apply_of_not_mem_range _ _ _ _ hmem,
      map_closedImmersion_apply_of_not_mem_range _ _ _ _ hnot]

end AlgebraicCycle

/-! ## Principal divisors restrict to principal divisors -/

open _root_.AlgebraicGeometry.Scheme in
/-- Flat pullback along a dominant open immersion of integral locally Noetherian schemes carries
the principal cycle of a rational function to the principal cycle of its restriction. -/
lemma principalCycle_pullbackOpen {X Y : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral X] [_root_.AlgebraicGeometry.IsIntegral Y]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
    (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsOpenImmersion f]
    [_root_.AlgebraicGeometry.IsDominant f] (q : Y.functionField) :
    X.principalCycle (dominantFunctionFieldMap f q) =
      AlgebraicCycle.pullbackOpen f (Y.principalCycle q) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  change (X.ord (dominantFunctionFieldMap f q) x : ℚ) = (Y.ord q (f.base x) : ℚ)
  rw [ord_dominantFunctionFieldMap_of_isOpenImmersion f x q]

namespace IntegralClosedSubscheme

variable {X : Scheme.{u}} (Z : IntegralClosedSubscheme X) (U : X.Opens)

/-- The trace of an integral closed subscheme on an open subscheme, provided the trace is
nonempty.  It is the actual scheme-theoretic restriction of the closed immersion, so integrality
and local Noetherianity are inherited rather than assumed. -/
noncomputable def restrictOpen [Nonempty (Z.inclusion ⁻¹ᵁ U)] :
    IntegralClosedSubscheme U.toScheme where
  scheme := (Z.inclusion ⁻¹ᵁ U).toScheme
  inclusion := Z.inclusion ∣_ U

@[simp]
lemma restrictOpen_scheme [Nonempty (Z.inclusion ⁻¹ᵁ U)] :
    (Z.restrictOpen U).scheme = (Z.inclusion ⁻¹ᵁ U).toScheme :=
  rfl

@[simp]
lemma restrictOpen_inclusion [Nonempty (Z.inclusion ⁻¹ᵁ U)] :
    (Z.restrictOpen U).inclusion = Z.inclusion ∣_ U :=
  rfl

/-- The canonical identification of the function field of an integral closed subscheme with the
function field of its nonempty trace on an open subscheme.  It is the function-field map of the
dominant open immersion, not a chosen comparison. -/
noncomputable def traceFunctionFieldMap [Nonempty (Z.inclusion ⁻¹ᵁ U)] :
    Z.scheme.functionField →+* (Z.inclusion ⁻¹ᵁ U).toScheme.functionField :=
  _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (Z.inclusion ⁻¹ᵁ U).ι

end IntegralClosedSubscheme

namespace RationalFunctionGenerator

variable {X : Scheme.{u}} (g : RationalFunctionGenerator X) (U : X.Opens)

/-- The trace of a principal-divisor generator on an open subscheme: the trace of its integral
closed subscheme together with the restriction of the same rational function along the canonical
function-field identification. -/
noncomputable def restrictOpen [Nonempty (g.subspace.inclusion ⁻¹ᵁ U)] :
    RationalFunctionGenerator U.toScheme where
  subspace := g.subspace.restrictOpen U
  function :=
    Units.map (g.subspace.traceFunctionFieldMap U).toMonoidHom g.function

/-- The principal divisor of a restricted generator, with all definitions unfolded. -/
lemma restrictOpen_divisor [Nonempty (g.subspace.inclusion ⁻¹ᵁ U)]
    (dimensionU : DimensionFunction U.toScheme) :
    (g.restrictOpen U).divisor dimensionU =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (g.subspace.inclusion ∣_ U)
        (fun w ↦ dimensionU ((g.subspace.inclusion ∣_ U).base w)) dimensionU
        ((g.subspace.inclusion ⁻¹ᵁ U).toScheme.principalCycle
          (g.subspace.traceFunctionFieldMap U
            (g.function : g.subspace.scheme.functionField))) :=
  rfl

/-- Flat pullback along an open immersion sends the principal divisor of a generator to the
principal divisor of its trace, whenever that trace is nonempty.  No dimension hypothesis is
needed: both pushforwards use the pulled-back weight, so every multiplicity is one. -/
lemma pullbackOpen_divisor [Nonempty (g.subspace.inclusion ⁻¹ᵁ U)]
    (dimensionX : DimensionFunction X) (dimensionU : DimensionFunction U.toScheme) :
    AlgebraicCycle.pullbackOpen U.ι (g.divisor dimensionX) =
      (g.restrictOpen U).divisor dimensionU := by
  have hpc : (g.subspace.inclusion ⁻¹ᵁ U).toScheme.principalCycle
      (g.subspace.traceFunctionFieldMap U
        (g.function : g.subspace.scheme.functionField)) =
      AlgebraicCycle.pullbackOpen (g.subspace.inclusion ⁻¹ᵁ U).ι
        (g.subspace.scheme.principalCycle
          (g.function : g.subspace.scheme.functionField)) :=
    principalCycle_pullbackOpen _ _
  rw [restrictOpen_divisor, hpc]
  exact AlgebraicCycle.pullbackOpen_map_closedImmersion g.subspace.inclusion U
    dimensionX dimensionU _

/-- If the trace of the integral closed subscheme of a generator on an open subscheme is empty,
its principal divisor restricts to zero. -/
lemma pullbackOpen_divisor_eq_zero [hempty : IsEmpty (g.subspace.inclusion ⁻¹ᵁ U)]
    (dimensionX : DimensionFunction X) :
    AlgebraicCycle.pullbackOpen U.ι (g.divisor dimensionX) = 0 := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext u
  change AlgebraicCycle.pullbackOpen U.ι (g.divisor dimensionX) u = (0 : ℚ)
  rw [AlgebraicCycle.pullbackOpen_apply]
  unfold divisor IntegralClosedSubscheme.pushforward
  have hmem : U.ι.base u ∉ Set.range g.subspace.inclusion.base := by
    rintro ⟨z, hz⟩
    have hzU : z ∈ g.subspace.inclusion ⁻¹ᵁ U := by
      change g.subspace.inclusion.base z ∈ U
      rw [hz]
      exact u.2
    exact hempty.false ⟨z, hzU⟩
  rw [AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ hmem]

end RationalFunctionGenerator

/-! ## Rational equivalence is preserved by flat pullback along open immersions -/

/-- Pull a certified dimension grading back along a closed immersion.  Heights are preserved by
closed immersions, so the pulled-back function is again certified. -/
def DimensionFunction.comapClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsClosedImmersion f] (dimensionY : DimensionFunction Y) :
    DimensionFunction X where
  toFun x := dimensionY (f.base x)
  nonnegative x := dimensionY.nonnegative _
  height_eq x := by
    rw [← height_eq_of_isClosedImmersion f x]
    exact dimensionY.height_eq _

namespace AlgebraicCycle

variable {X Y : Scheme.{u}}

/-- Flat pullback along an isomorphism is the residue-degree pushforward along its inverse. -/
lemma pullbackOpen_eq_map_of_isIso (e : X ≅ Y)
    (dimensionX : DimensionFunction X) (dimensionY : DimensionFunction Y)
    (c : AlgebraicCycle Y ℚ) :
    pullbackOpen e.hom c =
      _root_.AlgebraicGeometry.AlgebraicCycle.map e.inv dimensionY dimensionX c := by
  have hdim : (dimensionY : Y → ℤ) = fun y ↦ (dimensionX : X → ℤ) (e.inv.base y) := by
    funext y
    exact DimensionFunction.apply_eq_of_isClosedImmersion dimensionY dimensionX e.inv y
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  have hx : e.inv.base (e.hom.base x) = x := by
    change (e.hom ≫ e.inv).base x = x
    rw [e.hom_inv_id]
    rfl
  have hval := map_closedImmersion_apply_image e.inv (dimensionX : X → ℤ) c (e.hom.base x)
  rw [hx] at hval
  change c (e.hom.base x) =
    _root_.AlgebraicGeometry.AlgebraicCycle.map e.inv dimensionY dimensionX c x
  rw [hdim]
  exact hval.symm

end AlgebraicCycle

/-- Flat pullback along an open subscheme carries the canonical span of principal divisors into
the canonical span on that subscheme.  Generators whose integral closed subscheme misses the open
set restrict to zero; the others restrict to the principal divisor of their trace. -/
lemma totalRationalRelations_pullbackOpen_opens {X : Scheme.{u}} (U : X.Opens)
    (dimensionX : DimensionFunction X) (dimensionU : DimensionFunction U.toScheme) :
    Submodule.map (AlgebraicCycle.pullbackOpenLinear U.ι)
        (totalRationalRelations X dimensionX) ≤
      totalRationalRelations U.toScheme dimensionU := by
  rw [totalRationalRelations, Submodule.map_span, Submodule.span_le]
  rintro z ⟨c, ⟨g, rfl⟩, rfl⟩
  change AlgebraicCycle.pullbackOpen U.ι (g.divisor dimensionX) ∈
    totalRationalRelations U.toScheme dimensionU
  by_cases hne : Nonempty (g.subspace.inclusion ⁻¹ᵁ U)
  · have hne' : Nonempty (g.subspace.inclusion ⁻¹ᵁ U) := hne
    rw [g.pullbackOpen_divisor U dimensionX dimensionU]
    exact Submodule.subset_span (Set.mem_range_self _)
  · have hempty : IsEmpty (g.subspace.inclusion ⁻¹ᵁ U) := not_nonempty_iff.mp hne
    rw [g.pullbackOpen_divisor_eq_zero U dimensionX]
    exact Submodule.zero_mem _

/-- Flat pullback along an isomorphism carries the canonical span of principal divisors into the
canonical span on the source. -/
lemma totalRationalRelations_pullbackOpen_of_isIso {X Y : Scheme.{u}} (e : X ≅ Y)
    (dimensionX : DimensionFunction X) (dimensionY : DimensionFunction Y) :
    Submodule.map (AlgebraicCycle.pullbackOpenLinear e.hom)
        (totalRationalRelations Y dimensionY) ≤
      totalRationalRelations X dimensionX := by
  have hmap : AlgebraicCycle.pullbackOpenLinear e.hom =
      AlgebraicCycle.mapLinear e.inv dimensionY dimensionX := by
    apply LinearMap.ext
    intro c
    exact AlgebraicCycle.pullbackOpen_eq_map_of_isIso e dimensionX dimensionY c
  rw [hmap]
  exact totalRationalRelations_map_closedImmersion e.inv dimensionY dimensionX

/-- Flat pullback along an arbitrary open immersion carries the canonical span of principal
divisors into the canonical span on the source.  No relation between the two dimension gradings is
needed, because principal divisors are pushed forward with the pulled-back weight. -/
lemma totalRationalRelations_pullbackOpen {X U : Scheme.{u}} (j : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion j]
    (dimensionX : DimensionFunction X) (dimensionU : DimensionFunction U) :
    Submodule.map (AlgebraicCycle.pullbackOpenLinear j)
        (totalRationalRelations X dimensionX) ≤
      totalRationalRelations U dimensionU := by
  rintro z ⟨c, hc, rfl⟩
  have hsplit : AlgebraicCycle.pullbackOpen j c =
      AlgebraicCycle.pullbackOpen j.isoOpensRange.hom
        (AlgebraicCycle.pullbackOpen j.opensRange.ι c) := by
    apply Function.locallyFinsuppWithin.coe_injective
    funext u
    change c (j.base u) = c (j.opensRange.ι.base (j.isoOpensRange.hom.base u))
    rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, j.isoOpensRange_hom_ι]
  change AlgebraicCycle.pullbackOpen j c ∈ totalRationalRelations U dimensionU
  rw [hsplit]
  refine totalRationalRelations_pullbackOpen_of_isIso j.isoOpensRange dimensionU
    (dimensionU.comapClosedImmersion j.isoOpensRange.inv) ⟨_, ?_, rfl⟩
  exact totalRationalRelations_pullbackOpen_opens j.opensRange dimensionX _ ⟨c, hc, rfl⟩

/-! ## Codimension-one classes: principal divisors vanish in the Chow group -/

/-- An integral locally Noetherian scheme is an integral closed subscheme of itself. -/
noncomputable def IntegralClosedSubscheme.self (X : Scheme.{u})
    [_root_.AlgebraicGeometry.IsIntegral X]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X] : IntegralClosedSubscheme X where
  scheme := X
  inclusion := 𝟙 X

/-- Pushing a cycle forward along the identity closed immersion changes nothing. -/
@[simp]
lemma IntegralClosedSubscheme.pushforward_self {X : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral X]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    (dimension : DimensionFunction X) (c : AlgebraicCycle X ℚ) :
    (IntegralClosedSubscheme.self X).pushforward dimension c = c := by
  unfold IntegralClosedSubscheme.pushforward
  have hw : (fun z ↦ (dimension : X → ℤ) ((𝟙 X : X ⟶ X).base z)) = (dimension : X → ℤ) := by
    funext z
    rfl
  change _root_.AlgebraicGeometry.AlgebraicCycle.map (𝟙 X)
    (fun z ↦ (dimension : X → ℤ) ((𝟙 X : X ⟶ X).base z)) dimension c = c
  rw [hw]
  exact _root_.AlgebraicGeometry.AlgebraicCycle.map_id _ c

/-- The principal divisor of a nonzero rational function on an integral locally Noetherian
scheme lies in the canonical span of principal divisors.  This is the codimension-one comparison:
a Weil divisor of a rational function is a rational-equivalence relation, with the scheme itself
playing the role of the integral closed subscheme. -/
lemma principalCycle_mem_totalRationalRelations (X : Scheme.{u})
    [_root_.AlgebraicGeometry.IsIntegral X]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    (dimension : DimensionFunction X) (f : X.functionFieldˣ) :
    X.principalCycle (f : X.functionField) ∈ totalRationalRelations X dimension := by
  refine Submodule.subset_span ⟨⟨IntegralClosedSubscheme.self X, f⟩, ?_⟩
  change (IntegralClosedSubscheme.self X).pushforward dimension
    (X.principalCycle (f : X.functionField)) = X.principalCycle (f : X.functionField)
  exact IntegralClosedSubscheme.pushforward_self dimension _

/-- The rational Chow class of the principal divisor of a rational function vanishes. -/
theorem quotientMap_principalCycle_eq_zero {X : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral X]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    {dimension : DimensionFunction X} {i : ℤ}
    (R : RationalEquivalenceSystem X dimension i) (f : X.functionFieldˣ)
    (hmem : X.principalCycle (f : X.functionField) ∈ cyclesOfDimension X dimension i) :
    R.quotientMap ⟨X.principalCycle (f : X.functionField), hmem⟩ = 0 := by
  change (Submodule.Quotient.mk
    (⟨X.principalCycle (f : X.functionField), hmem⟩ :
      cyclesOfDimension X dimension i) : R.ChowGroup) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  cases R
  exact principalCycle_mem_totalRationalRelations X dimension f

/-! ## Extension by zero from an open subscheme -/

namespace AlgebraicCycle

variable {X : Scheme.{u}}

/-- Extension by zero of a rational cycle from an open subscheme of a Noetherian scheme.  On a
Noetherian space every locally finite support is finite, so the extended function is again a
cycle. -/
noncomputable def extendByZero [NoetherianSpace X] (U : X.Opens)
    (c : AlgebraicCycle U.toScheme ℚ) : AlgebraicCycle X ℚ where
  toFun := Function.extend U.ι.base (c : U.toScheme → ℚ) (0 : X → ℚ)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ := by
    have hnoeth : NoetherianSpace U.toScheme := NoetherianSpace.set _
    have hcompact : ((Set.univ : Set U.toScheme) ∩
        Function.support (c : U.toScheme → ℚ)).Finite :=
      c.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ
    rw [Set.univ_inter] at hcompact
    refine ⟨Set.univ, Filter.univ_mem, (hcompact.image U.ι.base).subset ?_⟩
    rintro y ⟨-, hy⟩
    by_cases h : ∃ u : U.toScheme, U.ι.base u = y
    · obtain ⟨u, rfl⟩ := h
      refine ⟨u, ?_, rfl⟩
      intro hzero
      exact hy (by
        rw [Function.Injective.extend_apply U.ι.isOpenEmbedding.injective]
        exact hzero)
    · exact absurd (Function.extend_apply' (f := U.ι.base) (c : U.toScheme → ℚ)
        (0 : X → ℚ) y h) hy

@[simp]
lemma extendByZero_apply_coe [NoetherianSpace X] (U : X.Opens)
    (c : AlgebraicCycle U.toScheme ℚ) (u : U.toScheme) :
    extendByZero U c (U.ι.base u) = c u :=
  Function.Injective.extend_apply U.ι.isOpenEmbedding.injective _ _ u

@[simp]
lemma extendByZero_apply_of_notMem [NoetherianSpace X] (U : X.Opens)
    (c : AlgebraicCycle U.toScheme ℚ) (x : X) (hx : x ∉ U) :
    extendByZero U c x = 0 :=
  Function.extend_apply' (f := U.ι.base) (c : U.toScheme → ℚ) (0 : X → ℚ) x
    (by rintro ⟨u, rfl⟩; exact hx u.2)

/-- Extension by zero is additive. -/
lemma extendByZero_add [NoetherianSpace X] (U : X.Opens)
    (c d : AlgebraicCycle U.toScheme ℚ) :
    extendByZero U (c + d) = extendByZero U c + extendByZero U d := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  by_cases h : ∃ u : U.toScheme, U.ι.base u = x
  · obtain ⟨u, rfl⟩ := h
    simp
  · have hx : x ∉ U := fun hxU ↦ h ⟨⟨x, hxU⟩, rfl⟩
    simp [hx]

/-- Extension by zero commutes with rational scalars. -/
lemma extendByZero_smul [NoetherianSpace X] (U : X.Opens) (q : ℚ)
    (c : AlgebraicCycle U.toScheme ℚ) :
    extendByZero U (q • c) = q • extendByZero U c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  by_cases h : ∃ u : U.toScheme, U.ι.base u = x
  · obtain ⟨u, rfl⟩ := h
    simp
  · have hx : x ∉ U := fun hxU ↦ h ⟨⟨x, hxU⟩, rfl⟩
    simp [hx]

/-- Extension by zero is a section of flat pullback along the open immersion. -/
@[simp]
lemma pullbackOpen_extendByZero [NoetherianSpace X] (U : X.Opens)
    (c : AlgebraicCycle U.toScheme ℚ) :
    pullbackOpen U.ι (extendByZero U c) = c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext u
  change extendByZero U c (U.ι.base u) = c u
  rw [extendByZero_apply_coe]

/-- Flat pullback to an open subscheme kills every cycle pushed forward from a closed subscheme
of the complement. -/
lemma pullbackOpen_map_eq_zero_of_notMem {W : Scheme.{u}} (i : W ⟶ X)
    [_root_.AlgebraicGeometry.IsClosedImmersion i] (U : X.Opens)
    (hdisjoint : ∀ w, i.base w ∉ U) (wW : W → ℤ) (wX : X → ℤ)
    (c : AlgebraicCycle W ℚ) :
    pullbackOpen U.ι (_root_.AlgebraicGeometry.AlgebraicCycle.map i wW wX c) = 0 := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext u
  change _root_.AlgebraicGeometry.AlgebraicCycle.map i wW wX c (U.ι.base u) = (0 : ℚ)
  unfold _root_.AlgebraicGeometry.AlgebraicCycle.map
  change (∑ᶠ w ∈ i.base ⁻¹' {U.ι.base u},
    c w * (_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff i wW wX w : ℚ)) = 0
  apply finsum_mem_of_eqOn_zero
  intro w hw
  have hmem : i.base w ∈ U := by
    have hwu : i.base w = U.ι.base u := by simpa using hw
    rw [hwu]
    exact u.2
  exact absurd hmem (hdisjoint w)

end AlgebraicCycle

/-! ## Dimension-graded flat pullback and the induced map on Chow groups -/

namespace cyclesOfDimension

variable {X U : Scheme.{u}} {dimensionX : DimensionFunction X}
  {dimensionU : DimensionFunction U} {i : ℤ}

/-- Flat pullback of dimension-graded rational cycles along an open immersion.  The geometric
hypothesis is exactly that the open immersion has relative dimension zero for the two certified
gradings; all multiplicities are one. -/
noncomputable def flatPullbackOpen (j : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion j]
    (hdim : ∀ u, dimensionU u = dimensionX (j.base u)) :
    cyclesOfDimension X dimensionX i →ₗ[ℚ] cyclesOfDimension U dimensionU i where
  toFun c := ⟨AlgebraicCycle.pullbackOpen j c.1, by
    intro u hu
    refine c.2 (j.base u) ?_
    rw [← hdim u]
    exact hu⟩
  map_add' c d := Subtype.ext (AlgebraicCycle.pullbackOpen_add j c.1 d.1)
  map_smul' q c := Subtype.ext (AlgebraicCycle.pullbackOpen_smul j q c.1)

@[simp]
theorem flatPullbackOpen_apply (j : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion j]
    (hdim : ∀ u, dimensionU u = dimensionX (j.base u))
    (c : cyclesOfDimension X dimensionX i) (u : U) :
    ((flatPullbackOpen (i := i) j hdim c : cyclesOfDimension U dimensionU i) :
        AlgebraicCycle U ℚ) u = (c : AlgebraicCycle X ℚ) (j.base u) :=
  rfl

/-- Flat pullback along the identity open immersion is the identity. -/
@[simp]
theorem flatPullbackOpen_id
    (hdim : ∀ x, dimensionX x = dimensionX ((𝟙 X : X ⟶ X).base x)) :
    flatPullbackOpen (dimensionU := dimensionX) (i := i) (𝟙 X) hdim = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact AlgebraicCycle.pullbackOpen_id c.1

/-- Dimension-graded flat pullback along open immersions is contravariantly functorial. -/
@[simp]
theorem flatPullbackOpen_comp {V : Scheme.{u}} {dimensionV : DimensionFunction V}
    (j₁ : V ⟶ U) (j₂ : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion j₁]
    [_root_.AlgebraicGeometry.IsOpenImmersion j₂]
    (h₁ : ∀ v, dimensionV v = dimensionU (j₁.base v))
    (h₂ : ∀ u, dimensionU u = dimensionX (j₂.base u))
    (h : ∀ v, dimensionV v = dimensionX ((j₁ ≫ j₂).base v)) :
    flatPullbackOpen (dimensionU := dimensionV) (i := i) (j₁ ≫ j₂) h =
      (flatPullbackOpen j₁ h₁).comp (flatPullbackOpen j₂ h₂) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact (AlgebraicCycle.pullbackOpen_comp j₁ j₂ c.1).symm

section ExtendByZero

variable {X : Scheme.{u}} [NoetherianSpace X] {dimensionX : DimensionFunction X}
  {V : X.Opens} {dimensionV : DimensionFunction V.toScheme} {i : ℤ}

/-- Extension by zero of dimension-graded rational cycles from an open subscheme of a Noetherian
scheme. -/
noncomputable def extendByZero (hdim : ∀ v, dimensionV v = dimensionX (V.ι.base v)) :
    cyclesOfDimension V.toScheme dimensionV i →ₗ[ℚ] cyclesOfDimension X dimensionX i where
  toFun c := ⟨AlgebraicCycle.extendByZero V c.1, by
    intro x hx
    by_cases h : x ∈ V
    · have hval : AlgebraicCycle.extendByZero V c.1 x = c.1 ⟨x, h⟩ :=
        AlgebraicCycle.extendByZero_apply_coe V c.1 ⟨x, h⟩
      rw [hval]
      refine c.2 ⟨x, h⟩ ?_
      rw [hdim ⟨x, h⟩]
      exact hx
    · exact AlgebraicCycle.extendByZero_apply_of_notMem V c.1 x h⟩
  map_add' c d := Subtype.ext (AlgebraicCycle.extendByZero_add V c.1 d.1)
  map_smul' q c := Subtype.ext (AlgebraicCycle.extendByZero_smul V q c.1)

/-- Extension by zero is a section of the dimension-graded flat pullback. -/
@[simp]
theorem flatPullbackOpen_extendByZero
    (hdim : ∀ v, dimensionV v = dimensionX (V.ι.base v))
    (c : cyclesOfDimension V.toScheme dimensionV i) :
    flatPullbackOpen (i := i) V.ι hdim (extendByZero hdim c) = c :=
  Subtype.ext (AlgebraicCycle.pullbackOpen_extendByZero V c.1)

end ExtendByZero

end cyclesOfDimension

namespace RationalEquivalenceSystem

namespace DescendingMap

variable {X U : Scheme.{u}} {dimensionX : DimensionFunction X}
  {dimensionU : DimensionFunction U} {i : ℤ}
  (R : RationalEquivalenceSystem X dimensionX i)

/-- The dimension-graded flat pullback of an open immersion, together with its proved
preservation of the canonical rational-equivalence subspaces. -/
noncomputable def ofOpenImmersion (j : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion j]
    (hdim : ∀ u, dimensionU u = dimensionX (j.base u))
    (S : RationalEquivalenceSystem U dimensionU i) : R.DescendingMap S where
  onCycles := cyclesOfDimension.flatPullbackOpen j hdim
  maps_relations := by
    cases R
    cases S
    intro z hz
    change AlgebraicCycle.pullbackOpen j z.1 ∈ totalRationalRelations U dimensionU
    exact totalRationalRelations_pullbackOpen j dimensionX dimensionU ⟨z.1, hz, rfl⟩

/-- Flat pullback along an open immersion on dimension-graded rational Chow groups. -/
noncomputable def openImmersionPullback (j : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion j]
    (hdim : ∀ u, dimensionU u = dimensionX (j.base u))
    (S : RationalEquivalenceSystem U dimensionU i) :
    R.ChowGroup →ₗ[ℚ] S.ChowGroup :=
  inducedMap R (ofOpenImmersion R j hdim S)

/-- The Chow-group flat pullback is induced by the actual flat pullback of cycles. -/
@[simp]
theorem openImmersionPullback_quotientMap (j : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion j]
    (hdim : ∀ u, dimensionU u = dimensionX (j.base u))
    (S : RationalEquivalenceSystem U dimensionU i)
    (z : cyclesOfDimension X dimensionX i) :
    openImmersionPullback R j hdim S (R.quotientMap z) =
      S.quotientMap (cyclesOfDimension.flatPullbackOpen j hdim z) :=
  rfl

/-- Flat pullback along the identity is the identity on rational Chow groups. -/
@[simp]
theorem openImmersionPullback_id
    (hdim : ∀ x, dimensionX x = dimensionX ((𝟙 X : X ⟶ X).base x)) :
    openImmersionPullback R (𝟙 X) hdim R = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change R.quotientMap (cyclesOfDimension.flatPullbackOpen (𝟙 X) hdim z) =
    R.quotientMap z
  rw [cyclesOfDimension.flatPullbackOpen_id]
  rfl

/-- Flat pullback along open immersions is contravariantly functorial on rational Chow
groups. -/
@[simp]
theorem openImmersionPullback_comp {V : Scheme.{u}} {dimensionV : DimensionFunction V}
    (S : RationalEquivalenceSystem U dimensionU i)
    (T : RationalEquivalenceSystem V dimensionV i)
    (j₁ : V ⟶ U) (j₂ : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion j₁]
    [_root_.AlgebraicGeometry.IsOpenImmersion j₂]
    (h₁ : ∀ v, dimensionV v = dimensionU (j₁.base v))
    (h₂ : ∀ u, dimensionU u = dimensionX (j₂.base u))
    (h : ∀ v, dimensionV v = dimensionX ((j₁ ≫ j₂).base v)) :
    openImmersionPullback R (j₁ ≫ j₂) h T =
      (openImmersionPullback S j₁ h₁ T).comp (openImmersionPullback R j₂ h₂ S) := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change T.quotientMap (cyclesOfDimension.flatPullbackOpen (j₁ ≫ j₂) h z) =
    T.quotientMap (cyclesOfDimension.flatPullbackOpen j₁ h₁
      (cyclesOfDimension.flatPullbackOpen j₂ h₂ z))
  rw [cyclesOfDimension.flatPullbackOpen_comp j₁ j₂ h₁ h₂ h]
  rfl

/-! ## The right-exact part of the localization sequence -/

section Localization

variable {X : Scheme.{u}} {dimensionX : DimensionFunction X} {i : ℤ}
  (R : RationalEquivalenceSystem X dimensionX i) (V : X.Opens)
  {dimensionV : DimensionFunction V.toScheme}

/-- Restriction of rational Chow classes to an open subscheme of a Noetherian scheme is
surjective.  Extension by zero of cycles is an actual section on cycles, so no exactness
statement is assumed. -/
theorem openImmersionPullback_surjective [NoetherianSpace X]
    (hdim : ∀ v, dimensionV v = dimensionX (V.ι.base v))
    (S : RationalEquivalenceSystem V.toScheme dimensionV i) :
    Function.Surjective (openImmersionPullback R V.ι hdim S) := by
  rintro ⟨z⟩
  refine ⟨R.quotientMap (cyclesOfDimension.extendByZero hdim z), ?_⟩
  rw [openImmersionPullback_quotientMap, cyclesOfDimension.flatPullbackOpen_extendByZero]
  rfl

/-- A cycle pushed forward from a closed subscheme of the complement restricts to zero on the
open subscheme.  Together with the previous theorem this is the right-exact part of the
localization sequence. -/
theorem openImmersionPullback_comp_closedImmersionPushforward
    {W : Scheme.{u}} {dimensionW : DimensionFunction W}
    (Q : RationalEquivalenceSystem W dimensionW i)
    (S : RationalEquivalenceSystem V.toScheme dimensionV i)
    (f : W ⟶ X) [_root_.AlgebraicGeometry.IsClosedImmersion f]
    (hdisjoint : ∀ w, f.base w ∉ V)
    (hdim : ∀ v, dimensionV v = dimensionX (V.ι.base v)) :
    (openImmersionPullback R V.ι hdim S).comp
        (closedImmersionPushforward Q f R) = 0 := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change S.quotientMap (cyclesOfDimension.flatPullbackOpen V.ι hdim
    (cyclesOfDimension.properPushforward f z)) = 0
  have hzero : cyclesOfDimension.flatPullbackOpen (i := i) V.ι hdim
      (cyclesOfDimension.properPushforward f z) = 0 := by
    apply Subtype.ext
    exact AlgebraicCycle.pullbackOpen_map_eq_zero_of_notMem f V hdisjoint
      dimensionW dimensionX z.1
  rw [hzero]
  exact map_zero _

end Localization

end DescendingMap

end RationalEquivalenceSystem

end GromovWitten.AlgebraicGeometry.IntersectionTheory
