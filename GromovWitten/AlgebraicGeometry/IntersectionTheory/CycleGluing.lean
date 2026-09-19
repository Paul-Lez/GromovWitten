/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalizationExact

/-!
# Gluing algebraic cycles along open covers

A rational algebraic cycle on a scheme is a coefficient function with locally finite support, so
it is a purely local object: it is determined by its restrictions to the members of an open cover
and an arbitrary compatible family of local cycles glues.  This file proves that, together with
the two compatibilities of the fundamental cycle that the globalisation of the virtual class
needs: restriction to an open subscheme preserves the fundamental cycle, and it commutes with the
pushforward along a closed immersion.

## Main results

* `AlgebraicCycle.pullbackOpen_eq_zero_of_forall` and `AlgebraicCycle.ext_of_cover`: a cycle
  whose restriction to every member of an open cover vanishes is zero, hence two cycles with
  equal restrictions agree.
* `CycleGluing.glue`: the cycle glued from a `CycleGluing.Compatible` family of cycles on the
  members of an open cover, with `CycleGluing.pullbackOpen_glue` and `CycleGluing.glue_unique`.
* `CycleGluing.isMax_map_iff`: an open immersion identifies the generic points of its source with
  the generic points of `X` lying in its image, for the specialisation order.
* `CycleGluing.genericLength_eq_of_isOpenImmersion` and
  `AlgebraicCycle.pullbackOpen_fundamentalCycle`: the fundamental cycle of a locally Noetherian
  scheme restricts to the fundamental cycle of any open subscheme.  The graded form is
  `cyclesOfDimension.flatPullbackOpen_fundamental`.
* `cyclesOfDimension.flatPullbackOpen_project`: restriction commutes with the projection onto the
  dimension-`i` part, and `CycleGluing.glue_mem_cyclesOfDimension`: a glued cycle is graded as
  soon as all of its pieces are.
* `AlgebraicCycle.pullbackOpen_map_fundamentalCycle`: the pushforward of the fundamental cycle
  along a closed immersion `g : Z ⟶ X` restricts on an open `V` to the pushforward of the
  fundamental cycle of `g ⁻¹ᵁ V`, which is the fibre product `Z ×_X V` by Mathlib's
  `isPullback_morphismRestrict`.
* `CycleGluing.principalDivisorsHomogeneous_restrict`: homogeneity of principal divisors passes
  to open subschemes of a Noetherian scheme, and `CycleGluing.principalDivisorsHomogeneous_of_cover`
  is the converse under the extra hypothesis `hcommon` discussed below.

## Zariski locality of `PrincipalDivisorsHomogeneous`

Homogeneity of principal divisors restricts to opens unconditionally (on a Noetherian scheme),
because every generator of an open subscheme is the restriction of its closure
(`RationalFunctionGenerator.closureIn`).  The converse is *not* a formal consequence of
homogeneity on the members of a cover: local homogeneity gives one dimension `dᵢ` per member of
the cover, and nothing ties the `dᵢ` of two different members together unless some member
contains support points of both.  `principalDivisorsHomogeneous_of_cover` therefore carries the
explicit hypothesis `hcommon`, that any two points at which a principal divisor is nonzero lie in
a common member of the cover; it holds for instance for a directed cover.  Deducing the global
statement from purely local ones would need catenarity of `X`, which the repository consistently
avoids assuming.
-/

open CategoryTheory TopologicalSpace Topology Order

open _root_.AlgebraicGeometry (IsOpenImmersion IsClosedImmersion IsLocallyNoetherian)

open scoped AlgebraicGeometry

attribute [local instance] specializationOrder

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u v

/-! ## A cycle is determined by its restrictions to an open cover -/

namespace CycleGluing

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens}

/-- Every point of a scheme lies in some member of an open cover of it. -/
theorem exists_mem_of_iSup_eq_top (hU : ⨆ i, U i = ⊤) (x : X) : ∃ i, x ∈ U i := by
  have hx : x ∈ ⨆ i, U i := by
    rw [hU]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

end CycleGluing

namespace AlgebraicCycle

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens}

/-- A rational algebraic cycle whose restriction to every member of an open cover vanishes is
zero, because every point of the ambient scheme lies in some member of the cover. -/
theorem pullbackOpen_eq_zero_of_forall (hU : ⨆ i, U i = ⊤) (c : AlgebraicCycle X ℚ)
    (h : ∀ i, pullbackOpen (U i).ι c = 0) : c = 0 := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  obtain ⟨i, hx⟩ := CycleGluing.exists_mem_of_iSup_eq_top hU x
  have hi : pullbackOpen (U i).ι c ⟨x, hx⟩ = 0 := by
    rw [h i]
    rfl
  exact hi

/-- Two rational algebraic cycles with the same restrictions to the members of an open cover are
equal. -/
theorem ext_of_cover (hU : ⨆ i, U i = ⊤) (c d : AlgebraicCycle X ℚ)
    (h : ∀ i, pullbackOpen (U i).ι c = pullbackOpen (U i).ι d) : c = d := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  obtain ⟨i, hx⟩ := CycleGluing.exists_mem_of_iSup_eq_top hU x
  have hi : pullbackOpen (U i).ι c ⟨x, hx⟩ = pullbackOpen (U i).ι d ⟨x, hx⟩ := by rw [h i]
  exact hi

end AlgebraicCycle

/-! ## Gluing a compatible family of cycles -/

namespace CycleGluing

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens}

/-- A family of rational cycles on the members of a family of open subschemes is *compatible* if
any two of its members take the same value at any two points with the same image in `X`. -/
def Compatible (c : ∀ i, AlgebraicCycle (U i).toScheme ℚ) : Prop :=
  ∀ (i j : ι) (x : (U i).toScheme) (y : (U j).toScheme),
    (U i).ι.base x = (U j).ι.base y → c i x = c j y

variable (hU : ⨆ i, U i = ⊤) (c : ∀ i, AlgebraicCycle (U i).toScheme ℚ)

/-- The coefficient function of the glued cycle: the value at `x` is the value of `c i` at `x`
for the member `U i` of the cover selected by `exists_mem_of_iSup_eq_top`. -/
noncomputable def glueFun (x : X) : ℚ :=
  c (exists_mem_of_iSup_eq_top hU x).choose ⟨x, (exists_mem_of_iSup_eq_top hU x).choose_spec⟩

/-- For a compatible family the glued coefficient function has the expected value on every member
of the cover, not only on the selected one. -/
theorem glueFun_apply (hc : Compatible c) (i : ι) (x : X) (hx : x ∈ U i) :
    glueFun hU c x = c i ⟨x, hx⟩ :=
  hc _ i _ ⟨x, hx⟩ rfl

/-- The glued coefficient function pulled back along the inclusion of a member of the cover is
the corresponding member of the family. -/
theorem glueFun_map (hc : Compatible c) (i : ι) (u : (U i).toScheme) :
    glueFun hU c ((U i).ι.base u) = c i u :=
  hc _ i _ u rfl

/-- The cycle glued from a compatible family of cycles on the members of an open cover.  Local
finiteness of the support is inherited from any single member: the image of a locally finite
neighbourhood under the open embedding `(U i).ι` is again open. -/
noncomputable def glue (hc : Compatible c) : AlgebraicCycle X ℚ where
  toFun := glueFun hU c
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := by
    intro x _
    obtain ⟨i, hx⟩ := exists_mem_of_iSup_eq_top hU x
    obtain ⟨t, ht, hfinite⟩ := (c i).supportLocallyFiniteWithinDomain ⟨x, hx⟩ (by trivial)
    obtain ⟨t', ht'sub, ht'open, hxt'⟩ := mem_nhds_iff.mp ht
    refine ⟨(U i).ι.base '' t', ?_, ?_⟩
    · exact ((U i).ι.isOpenEmbedding.isOpenMap t' ht'open).mem_nhds ⟨⟨x, hx⟩, hxt', rfl⟩
    · refine Set.Finite.subset
        ((hfinite.subset (Set.inter_subset_inter_left _ ht'sub)).image (U i).ι.base) ?_
      rintro y ⟨⟨u, hu, rfl⟩, hy⟩
      refine ⟨u, ⟨hu, ?_⟩, rfl⟩
      rw [Function.mem_support] at hy ⊢
      rwa [glueFun_map hU c hc i u] at hy

/-- The glued cycle restricts to the given cycle on every member of the cover. -/
@[simp]
theorem pullbackOpen_glue (hc : Compatible c) (i : ι) :
    AlgebraicCycle.pullbackOpen (U i).ι (glue hU c hc) = c i := by
  apply Function.locallyFinsuppWithin.ext
  intro u
  exact glueFun_map hU c hc i u

/-- The glued cycle is the unique cycle with the prescribed restrictions. -/
theorem glue_unique (hc : Compatible c) (d : AlgebraicCycle X ℚ)
    (hd : ∀ i, AlgebraicCycle.pullbackOpen (U i).ι d = c i) : d = glue hU c hc :=
  AlgebraicCycle.ext_of_cover hU d (glue hU c hc) fun i ↦ by
    rw [hd i, pullbackOpen_glue]

end CycleGluing


/-! ## Restriction of the fundamental cycle along an open immersion -/

namespace CycleGluing

/-- The length of a commutative ring as a module over itself is invariant under ring isomorphism:
an isomorphism of rings is a bijective semilinear map, hence induces an order isomorphism of the
two lattices of ideals, and the length is the Krull dimension of that lattice. -/
theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  let _ : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : R →ₛₗ[(e : R →+* S)] S :=
    { toFun := e
      map_add' := map_add e
      map_smul' := fun r x ↦ by simp [map_mul e r x] }
  have hbij : Function.Bijective f := e.bijective
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hbij)]

variable {X Y : Scheme.{u}}

/-- An open immersion identifies the generic points of its source with the generic points of the
target that lie in its image.  Open sets are stable under generisation, so every generisation of
a point of the image is again in the image, and specialisation transfers back and forth along an
open embedding. -/
theorem isMax_map_iff (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    IsMax (f.base y) ↔ IsMax y := by
  constructor
  · intro hmax z hz
    have hzX : f.base y ≤ f.base z := hz.map f.continuous
    exact f.isOpenEmbedding.isInducing.specializes_iff.mp (hmax hzX)
  · intro hmax z hz
    have hspec : z ⤳ f.base y := hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range f.base :=
      hspec.mem_open f.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
    have hle : y ≤ z' := f.isOpenEmbedding.isInducing.specializes_iff.mp hspec
    exact (hmax hle).map f.continuous

/-- An open immersion induces an isomorphism on stalks, hence preserves the generic multiplicity
of every point of its source. -/
theorem genericLength_eq_of_isOpenImmersion [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    X.genericLength (f.base y) = Y.genericLength y := by
  have he : Module.length (X.presheaf.stalk (f.base y)) (X.presheaf.stalk (f.base y)) =
      Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) :=
    length_self_eq_of_ringEquiv (CategoryTheory.asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  unfold _root_.AlgebraicGeometry.Scheme.genericLength
  rw [he]

end CycleGluing

namespace AlgebraicCycle

variable {X Y : Scheme.{u}}

/-- Flat pullback along an open immersion carries the fundamental cycle to the fundamental cycle:
generic points of the open correspond to generic points of `X` lying in it, and the generic
multiplicities agree because the stalks are isomorphic. -/
theorem pullbackOpen_fundamentalCycle [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsOpenImmersion f] :
    pullbackOpen f X.fundamentalCycle = Y.fundamentalCycle := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [pullbackOpen_apply]
  by_cases hy : IsMax y
  · rw [X.fundamentalCycle_apply_of_isMax _ ((CycleGluing.isMax_map_iff f y).mpr hy),
      Y.fundamentalCycle_apply_of_isMax y hy,
      CycleGluing.genericLength_eq_of_isOpenImmersion f y]
  · rw [X.fundamentalCycle_apply_of_not_isMax _
      (fun h ↦ hy ((CycleGluing.isMax_map_iff f y).mp h)),
      Y.fundamentalCycle_apply_of_not_isMax y hy]

end AlgebraicCycle

/-! ## Graded restriction: projection, fundamental class and gluing -/

namespace cyclesOfDimension

variable {X U : Scheme.{u}} {dimensionX : DimensionFunction X}
  {dimensionU : DimensionFunction U} {i : ℤ}

/-- Restriction to an open subscheme commutes with the projection onto the dimension-`i` part,
because the two gradings agree along the open immersion. -/
theorem flatPullbackOpen_project (j : U ⟶ X) [IsOpenImmersion j]
    (hdim : ∀ u, dimensionU u = dimensionX (j.base u)) (z : AlgebraicCycle X ℚ) :
    flatPullbackOpen (dimensionU := dimensionU) (i := i) j hdim
        (project (dimension := dimensionX) (i := i) z) =
      project (dimension := dimensionU) (i := i) (AlgebraicCycle.pullbackOpen j z) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro u
  change (if dimensionX (j.base u) = i then z (j.base u) else 0) =
    (if dimensionU u = i then z (j.base u) else 0)
  rw [hdim u]

/-- Restriction to an open subscheme carries the graded fundamental class to the graded
fundamental class. -/
theorem flatPullbackOpen_fundamental [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (hdim : ∀ u, dimensionU u = dimensionX (j.base u))
    (pureX : ∀ x : X, IsMax x → dimensionX x = i)
    (pureU : ∀ u : U, IsMax u → dimensionU u = i) :
    flatPullbackOpen (dimensionU := dimensionU) (i := i) j hdim (fundamental pureX) =
      fundamental pureU :=
  Subtype.ext (AlgebraicCycle.pullbackOpen_fundamentalCycle j)

end cyclesOfDimension

namespace CycleGluing

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens}

/-- A cycle glued from graded pieces is graded: the coefficient of the glued cycle at a point of
`U i` is a coefficient of `c i`, and the two dimension functions agree there. -/
theorem glue_mem_cyclesOfDimension {d : ℤ} (hU : ⨆ i, U i = ⊤)
    (c : ∀ i, AlgebraicCycle (U i).toScheme ℚ) (hc : Compatible c)
    (dimensionX : DimensionFunction X)
    (dimensionU : ∀ i, DimensionFunction (U i).toScheme)
    (hdim : ∀ i (u : (U i).toScheme), dimensionU i u = dimensionX ((U i).ι.base u))
    (hmem : ∀ i, c i ∈ cyclesOfDimension (U i).toScheme (dimensionU i) d) :
    glue hU c hc ∈ cyclesOfDimension X dimensionX d := by
  intro x hx
  obtain ⟨i, hxi⟩ := exists_mem_of_iSup_eq_top hU x
  have hval : glue hU c hc x = c i ⟨x, hxi⟩ := glueFun_map hU c hc i ⟨x, hxi⟩
  rw [hval]
  refine hmem i ⟨x, hxi⟩ ?_
  rw [hdim i ⟨x, hxi⟩]
  exact hx

end CycleGluing

/-! ## Restriction of the fundamental cycle of a closed subscheme -/

namespace AlgebraicCycle

/-- The pushforward of the fundamental cycle along a closed immersion `g : Z ⟶ X` restricts on an
open subscheme `V` to the pushforward of the fundamental cycle of the trace `g ⁻¹ᵁ V`, which is
the fibre product `Z ×_X V` by Mathlib's `isPullback_morphismRestrict`.  Both pushforwards use
the pulled-back weight, so all multiplicities are one. -/
theorem pullbackOpen_map_fundamentalCycle {X Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (g : Z ⟶ X) [IsClosedImmersion g] (V : X.Opens) (wX : X → ℤ) (wV : V.toScheme → ℤ) :
    pullbackOpen V.ι (_root_.AlgebraicGeometry.AlgebraicCycle.map g
        (fun z ↦ wX (g.base z)) wX Z.fundamentalCycle) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (g ∣_ V)
        (fun z ↦ wV ((g ∣_ V).base z)) wV (g ⁻¹ᵁ V).toScheme.fundamentalCycle := by
  rw [pullbackOpen_map_closedImmersion g V wX wV Z.fundamentalCycle,
    pullbackOpen_fundamentalCycle (g ⁻¹ᵁ V).ι]

end AlgebraicCycle

/-! ## Zariski locality of the homogeneity of principal divisors -/

namespace CycleGluing

/-- Homogeneity of principal divisors passes to open subschemes of a Noetherian scheme: every
principal-divisor generator of an open subscheme is the restriction of its closure in the ambient
scheme (`RationalFunctionGenerator.closureIn`). -/
theorem principalDivisorsHomogeneous_restrict {X : Scheme.{u}} [NoetherianSpace X]
    [IsLocallyNoetherian X] (V : X.Opens) (dimensionX : DimensionFunction X)
    (dimensionV : DimensionFunction V.toScheme)
    (hdim : ∀ v, dimensionV v = dimensionX (V.ι.base v))
    (hhom : PrincipalDivisorsHomogeneous X dimensionX) :
    PrincipalDivisorsHomogeneous V.toScheme dimensionV := by
  intro g
  obtain ⟨d, hd⟩ := hhom (g.closureIn V)
  refine ⟨d, fun v hv ↦ ?_⟩
  rw [hdim v]
  refine hd (V.ι.base v) ?_
  rw [← g.pullbackOpen_divisor_closureIn V dimensionX dimensionV] at hv
  exact hv

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens}

/-- Homogeneity of principal divisors is deduced from homogeneity on the members of an open cover
under the explicit hypothesis `hcommon`: any two points at which a given principal divisor is
nonzero lie in a common member of the cover.  Some such hypothesis is genuinely needed, because
local homogeneity produces one dimension per member of the cover and nothing links the dimensions
attached to two disjoint members.  The covering hypothesis `⨆ i, U i = ⊤` is not needed: it is
subsumed by `hcommon`, which already provides a member of the family around every relevant pair
of points. -/
theorem principalDivisorsHomogeneous_of_cover
    (dimensionX : DimensionFunction X)
    (dimensionU : ∀ i, DimensionFunction (U i).toScheme)
    (hdim : ∀ i (u : (U i).toScheme), dimensionU i u = dimensionX ((U i).ι.base u))
    (hhom : ∀ i, PrincipalDivisorsHomogeneous (U i).toScheme (dimensionU i))
    (hcommon : ∀ (g : RationalFunctionGenerator X) (x y : X),
      g.divisor dimensionX x ≠ 0 → g.divisor dimensionX y ≠ 0 → ∃ i, x ∈ U i ∧ y ∈ U i) :
    PrincipalDivisorsHomogeneous X dimensionX := by
  intro g
  by_cases hzero : ∀ x : X, g.divisor dimensionX x = 0
  · exact ⟨0, fun x hx ↦ absurd (hzero x) hx⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x : X, g.divisor dimensionX x ≠ 0 := by
    by_contra hcon
    exact hzero fun x ↦ not_not.mp fun h ↦ hcon ⟨x, h⟩
  refine ⟨dimensionX x₀, fun y hy ↦ ?_⟩
  obtain ⟨i, hx₀i, hyi⟩ := hcommon g x₀ y hx₀ hy
  have hne : Nonempty (g.subspace.inclusion ⁻¹ᵁ U i) := by
    by_contra hemp
    let _ : IsEmpty (g.subspace.inclusion ⁻¹ᵁ U i) := not_nonempty_iff.mp hemp
    have h0 := RationalFunctionGenerator.pullbackOpen_divisor_eq_zero g (U i) dimensionX
    have hzz : AlgebraicCycle.pullbackOpen (U i).ι (g.divisor dimensionX) ⟨x₀, hx₀i⟩ = 0 := by
      rw [h0]
      rfl
    exact hx₀ hzz
  let _ := hne
  have hres := RationalFunctionGenerator.pullbackOpen_divisor g (U i) dimensionX (dimensionU i)
  obtain ⟨d, hd⟩ := hhom i (g.restrictOpen (U i))
  have hx₀d : dimensionU i ⟨x₀, hx₀i⟩ = d := by
    refine hd ⟨x₀, hx₀i⟩ ?_
    rw [← hres]
    exact hx₀
  have hyd : dimensionU i ⟨y, hyi⟩ = d := by
    refine hd ⟨y, hyi⟩ ?_
    rw [← hres]
    exact hy
  rw [hdim i ⟨x₀, hx₀i⟩] at hx₀d
  rw [hdim i ⟨y, hyi⟩] at hyd
  have hfin : dimensionX ((U i).ι.base ⟨y, hyi⟩) =
      dimensionX ((U i).ι.base ⟨x₀, hx₀i⟩) := by rw [hx₀d, hyd]
  exact hfin

end CycleGluing

end GromovWitten.AlgebraicGeometry.IntersectionTheory
