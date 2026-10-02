/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.EtalePullback
import GromovWitten.AlgebraicGeometry.IntersectionTheory.PointOrder
import GromovWitten.AlgebraicGeometry.IntersectionTheory.EtalePointDivisor

/-!
# Vistoli relations and Morita invariance of étale presentation groupoids

The live `EtalePresentationGroupoid.chow` divides the invariant cycles on the atlas by *all*
rational equivalences of the atlas, which is not atlas independent.  Following Vistoli, the
correct relations are the divisors of *invariant* rational functions: an invariant system on a
groupoid `R ⇉ U` is a family of units `value w ∈ κ(w)ˣ`, nontrivial at finitely many points of
dimension `i + 1`, whose two pullbacks to every arrow agree, and its divisor is
`∑_w div_w (value w)`.  This file introduces these relations, the resulting Vistoli rational
Chow groups, and proves their invariance under Morita maps of étale groupoids.

Standing hypotheses (`EtalePresentationGroupoid.Good`): atlas and arrow scheme quasi-compact and
locally Noetherian, both dimension functions satisfying `CovByDimension`.

## Main definitions

* `EtalePresentationGroupoid.Good`: the standing hypotheses.
* `identityGroupoid X dX`: the groupoid `X ⇉ X` with both legs the identity.
* `InvariantSystem G i`, `InvariantSystem.divisor`: invariant systems of rational functions and
  their divisors.
* `EtalePresentationGroupoid.vistoliRelations`, `vistoliChow`, `vistoliQuotientMap`: the span of
  the divisors of invariant systems, and the quotient of the Vistoli cycles by it.
* `MoritaMap H G`: a morphism of étale groupoids, étale of relative dimension zero on atlases,
  satisfying (F0) surjectivity, (F1) points in a fibre are joined by arrows with compatible
  residue maps, (F2) Galois descent in fibres, (F3) fullness.
* `MoritaMap.onCycles`: pullback of Vistoli cycles; `InvariantSystem.pullback`: pullback of
  invariant systems.

## Main results

* `InvariantSystem.divisor_mem_cycles`: the divisor of an invariant system is a Vistoli cycle.
* `EtalePresentationGroupoid.vistoliRelations_le_relations`: Vistoli relations are rational
  equivalences on the atlas, so `vistoliChow_toChow` maps the Vistoli Chow group onto the live
  `chow` (`vistoliChow_toChow_surjective`).
* `vistoliRelations_identityGroupoid`, `vistoliChow_identity_equiv`: for the identity groupoid
  of a scheme `X` the Vistoli Chow group is the rational Chow group `A_i(X)`.
* `MoritaMap.onCycles_bijective`: pullback along a Morita map is a bijection on Vistoli cycles.
* `MoritaMap.divisor_pullback`, `MoritaMap.exists_pullback_eq`: pullback of invariant systems is
  compatible with divisors and every invariant system of `H` is a pullback.
* `MoritaMap.map_vistoliRelations`, `MoritaMap.vistoliChowEquiv`: a Morita map induces an
  isomorphism `vistoliChow G i ≃ₗ[ℚ] vistoliChow H i`.

The étale pullback formula for divisors of point generators is
`pullbackEtale_sum_divisor_pointGenerator` (`EtalePointDivisor.lean`).
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Order

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open LineBundleInjective

/-! ## Pulling back families of residue units -/

section UnitPull

variable {X Y Z : Scheme.{u}}

/-- The pullback of a family of residue units `v y ∈ κ(y)ˣ` along a morphism `f : X ⟶ Y`: at
`x : X` it is the image of `v (f x)` under the residue field map `κ(f x) → κ(x)`. -/
noncomputable def unitPull (f : X ⟶ Y) (v : ∀ y : Y, (Y.residueField y)ˣ) (x : X) :
    (X.residueField x)ˣ :=
  pullbackUnit f x (v (f.base x))

/-- The map on units induced by a residue field map is injective (a field homomorphism is
injective). -/
theorem units_map_residueFieldMap_injective (f : X ⟶ Y) (x : X) :
    Function.Injective (Units.map (f.residueFieldMap x).hom.toMonoidHom) := fun _ _ h ↦
  Units.ext ((f.residueFieldMap x).hom.injective (congrArg Units.val h))

/-- Pulling back residue units along a composite is the iterated pullback. -/
theorem unitPull_comp (f : X ⟶ Y) (g : Y ⟶ Z) (v : ∀ z : Z, (Z.residueField z)ˣ) (x : X) :
    unitPull (f ≫ g) v x = unitPull f (unitPull g v) x := by
  apply Units.ext
  simp only [unitPull, pullbackUnit, Units.coe_map, Scheme.residueFieldMap_comp]
  rfl

/-- Pulling back residue units along equal morphisms gives equal results. -/
theorem unitPull_congr {f g : X ⟶ Y} (h : f = g) (v : ∀ y : Y, (Y.residueField y)ˣ) (x : X) :
    unitPull f v x = unitPull g v x := by
  subst h
  rfl

/-- Transport of a family of residue units along an equality of points. -/
theorem residueFieldCongr_hom_apply_family {y₁ y₂ : Y} (h : y₁ = y₂)
    (v : ∀ y : Y, (Y.residueField y)ˣ) :
    (Y.residueFieldCongr h).hom.hom (v y₁ : Y.residueField y₁) = v y₂ := by
  subst h
  rfl

/-- If two morphisms agree at `x` together with their residue field maps (after identifying the
two image points), the pullbacks of every family of residue units agree at `x`. -/
theorem unitPull_eq_of_residueFieldMap_eq {f g : X ⟶ Y} {x : X} (h : f.base x = g.base x)
    (hfg : f.residueFieldMap x = (Y.residueFieldCongr h).hom ≫ g.residueFieldMap x)
    (v : ∀ y : Y, (Y.residueField y)ˣ) : unitPull f v x = unitPull g v x := by
  apply Units.ext
  change (f.residueFieldMap x).hom (v (f.base x) : Y.residueField (f.base x)) =
    (g.residueFieldMap x).hom (v (g.base x) : Y.residueField (g.base x))
  rw [hfg, CommRingCat.hom_comp, RingHom.comp_apply, residueFieldCongr_hom_apply_family h v]

/-- The pullback of the trivial family is trivial. -/
@[simp]
theorem unitPull_one (f : X ⟶ Y) (x : X) : unitPull f (fun _ ↦ 1) x = 1 :=
  map_one _

/-- The pullback of a family at `x` is trivial exactly when the family is trivial at `f x`. -/
theorem unitPull_eq_one_iff (f : X ⟶ Y) (v : ∀ y : Y, (Y.residueField y)ˣ) (x : X) :
    unitPull f v x = 1 ↔ v (f.base x) = 1 :=
  (units_map_residueFieldMap_injective f x).eq_iff' (map_one _)

end UnitPull

/-! ## Finite fibres of étale morphisms from quasi-compact schemes -/

/-- Preimages of finite sets under an étale morphism with quasi-compact source are finite. -/
private theorem finite_preimage_of_etale_of_compactSpace {X Y : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f] {A : Set Y} (hA : A.Finite) :
    (f.base ⁻¹' A).Finite := by
  classical
  choose V hxV hV using fun x ↦
    AlgebraicCycle.exists_isOpen_finite_inter_preimage_of_etale f x hA
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x ↦ (V x : Set X))
    (fun x _ ↦ (V x).isOpen.mem_nhds (hxV x))
  refine (Set.Finite.biUnion t.finite_toSet fun x _ ↦ hV x).subset ?_
  intro y hy
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht.2 (Set.mem_univ y))
  exact Set.mem_iUnion₂.2 ⟨x, hx, hyx, hy⟩

/-- A cycle with finite support on a scheme. -/
private noncomputable def cycleOfFiniteSupport {X : Scheme.{u}} (f : X → ℚ)
    (hf : (Function.support f).Finite) : AlgebraicCycle X ℚ where
  toFun := f
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' _ _ := ⟨Set.univ, Filter.univ_mem, by simpa using hf⟩

private theorem finite_support_of_compactSpace {X : Scheme.{u}} [CompactSpace X]
    (z : AlgebraicCycle X ℚ) : (Function.support (z : X → ℚ)).Finite := by
  have h := Function.locallyFinsupp.locallyFiniteSupport z
  have h2 := h.finite_inter_support_of_isCompact (isCompact_univ (X := X))
  simpa using h2

/-! ## Degree bookkeeping for point-generator divisors -/

section Degree

variable {X : Scheme.{u}}

/-- Projection onto the dimension-`i` part, as a `ℚ`-linear map. -/
private noncomputable def projectLinear (dim : DimensionFunction X) (i : ℤ) :
    AlgebraicCycle X ℚ →ₗ[ℚ] cyclesOfDimension X dim i where
  toFun c := cyclesOfDimension.project c
  map_add' c d := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.coe_injective
    funext x
    simp only [cyclesOfDimension.project_apply, Submodule.coe_add,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' q c := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.coe_injective
    funext x
    simp only [cyclesOfDimension.project_apply, SetLike.val_smul, RingHom.id_apply]
    split_ifs <;> simp_all

/-- Projecting a dimension-`i` cycle onto its dimension-`i` part does nothing. -/
private theorem project_of_mem {dim : DimensionFunction X} {i : ℤ} (c : AlgebraicCycle X ℚ)
    (hc : c ∈ cyclesOfDimension X dim i) :
    (cyclesOfDimension.project (dimension := dim) (i := i) c : AlgebraicCycle X ℚ) = c := by
  refine Function.locallyFinsuppWithin.ext fun x ↦ ?_
  rw [cyclesOfDimension.project_apply]
  split_ifs with hx
  · rfl
  · exact (hc x hx).symm

open scoped Classical in
/-- **The divisor of the point generator** `pointGenerator w u` on a locally Noetherian scheme
with Noetherian underlying space (`pointDivisor_eq`), and the junk value `0` on other schemes.
The case split only serves to make the Vistoli relations below definable without hypotheses;
every theorem about them assumes the Noetherian hypotheses. -/
noncomputable def pointDivisor (dim : DimensionFunction X) (w : X) (u : (X.residueField w)ˣ) :
    AlgebraicCycle X ℚ :=
  if h : _root_.AlgebraicGeometry.IsLocallyNoetherian X ∧ NoetherianSpace X then
    haveI := h.1
    haveI := h.2
    (pointGenerator w u).divisor dim
  else 0

variable [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]

/-- On a locally Noetherian scheme with Noetherian underlying space, `pointDivisor` is the
divisor of the point generator. -/
theorem pointDivisor_eq (dim : DimensionFunction X) (w : X) (u : (X.residueField w)ˣ) :
    pointDivisor dim w u = (pointGenerator w u).divisor dim := by
  rw [pointDivisor, dif_pos ⟨‹_›, ‹_›⟩]

/-- Under `CovByDimension`, the divisor of the point generator of a point of dimension `i + 1`
is a dimension-`i` cycle. -/
theorem divisor_pointGenerator_mem_cyclesOfDimension (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) {i : ℤ} (w : X)
    (u : (X.residueField w)ˣ) (hw : dim w = i + 1) :
    (pointGenerator w u).divisor dim ∈ cyclesOfDimension X dim i := by
  intro x hx
  refine divisor_pointGenerator_apply_eq_zero_of_dim_ne dim hcov w u x ?_
  omega

/-- Under `CovByDimension`, the dimension-`i` part of the divisor of the point generator of a
point whose dimension is not `i + 1` vanishes. -/
theorem project_divisor_pointGenerator_of_ne (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) {i : ℤ} (w : X)
    (u : (X.residueField w)ˣ) (hw : dim w ≠ i + 1) :
    cyclesOfDimension.project (dimension := dim) (i := i)
      ((pointGenerator w u).divisor dim) = 0 := by
  apply Subtype.ext
  refine Function.locallyFinsuppWithin.ext fun x ↦ ?_
  rw [cyclesOfDimension.project_apply]
  split_ifs with hx
  · refine divisor_pointGenerator_apply_eq_zero_of_dim_ne dim hcov w u x ?_
    omega
  · rfl

end Degree

/-! ## Standing hypotheses and the identity groupoid -/

namespace EtalePresentationGroupoid

/-- **The standing hypotheses on an étale presentation groupoid.**  Both the atlas and the
arrow scheme are quasi-compact and locally Noetherian, and both certified dimension functions
drop by exactly one along the covering relation of the specialisation order.  All of these hold
for an étale groupoid of schemes of finite type over a field. -/
structure Good (G : EtalePresentationGroupoid.{u}) : Prop where
  /-- The atlas is quasi-compact. -/
  compactSpace_base : CompactSpace G.base
  /-- The arrow scheme is quasi-compact. -/
  compactSpace_arrows : CompactSpace G.arrows
  /-- The atlas is locally Noetherian. -/
  isLocallyNoetherian_base : _root_.AlgebraicGeometry.IsLocallyNoetherian G.base
  /-- The arrow scheme is locally Noetherian. -/
  isLocallyNoetherian_arrows : _root_.AlgebraicGeometry.IsLocallyNoetherian G.arrows
  /-- The dimension function of the atlas drops by one along covering specialisations. -/
  covByDimension_base : HomogeneityLocal.CovByDimension G.baseDim
  /-- The dimension function of the arrow scheme drops by one along covering
  specialisations. -/
  covByDimension_arrows : HomogeneityLocal.CovByDimension G.arrowsDim

/-- Under the standing hypotheses the atlas is a Noetherian scheme. -/
theorem Good.isNoetherian_base {G : EtalePresentationGroupoid.{u}} (hG : G.Good) :
    _root_.AlgebraicGeometry.IsNoetherian G.base :=
  have := hG.compactSpace_base
  have := hG.isLocallyNoetherian_base
  {}

/-- Under the standing hypotheses the arrow scheme is a Noetherian scheme. -/
theorem Good.isNoetherian_arrows {G : EtalePresentationGroupoid.{u}} (hG : G.Good) :
    _root_.AlgebraicGeometry.IsNoetherian G.arrows :=
  have := hG.compactSpace_arrows
  have := hG.isLocallyNoetherian_arrows
  {}

end EtalePresentationGroupoid

/-- **The identity groupoid of a scheme** `X` with a dimension function: the atlas and the arrow
scheme are both `X`, and both legs are the identity. -/
abbrev identityGroupoid (X : Scheme.{u}) (dX : DimensionFunction X) :
    EtalePresentationGroupoid.{u} where
  base := X
  arrows := X
  baseDim := dX
  arrowsDim := dX
  src := 𝟙 X
  tgt := 𝟙 X
  src_etale := inferInstance
  tgt_etale := inferInstance
  src_dim _ := rfl
  tgt_dim _ := rfl

/-- The identity groupoid of a quasi-compact locally Noetherian scheme whose dimension function
satisfies `CovByDimension` satisfies the standing hypotheses. -/
theorem identityGroupoid_good (X : Scheme.{u}) (dX : DimensionFunction X)
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X]
    (hcov : HomogeneityLocal.CovByDimension dX) : (identityGroupoid X dX).Good where
  compactSpace_base := ‹_›
  compactSpace_arrows := ‹_›
  isLocallyNoetherian_base := ‹_›
  isLocallyNoetherian_arrows := ‹_›
  covByDimension_base := hcov
  covByDimension_arrows := hcov

/-! ## Invariant systems of rational functions -/

/-- **An invariant system of rational functions** of dimension `i + 1` on an étale presentation
groupoid `G`: a unit `value w ∈ κ(w)ˣ` at every point `w` of the atlas, nontrivial exactly on the
finite set `support` of points of dimension `i + 1`, and invariant under the groupoid: for every
arrow `r`, the images of `value (src r)` and `value (tgt r)` in `κ(r)` agree.  These are the
rational functions on the integral closed substacks of dimension `i + 1`, read on the atlas. -/
@[ext]
structure InvariantSystem (G : EtalePresentationGroupoid.{u}) (i : ℤ) where
  /-- The finite set of points where the system is nontrivial. -/
  support : Finset G.base
  /-- The unit of the residue field at each point of the atlas. -/
  value : ∀ w : G.base, (G.base.residueField w)ˣ
  /-- The support is exactly the set of points with a nontrivial value. -/
  mem_support_iff : ∀ w, w ∈ support ↔ value w ≠ 1
  /-- Every point of the support has dimension `i + 1`. -/
  dim_support : ∀ w ∈ support, G.baseDim w = i + 1
  /-- Groupoid invariance: the two pullbacks to every arrow agree in its residue field. -/
  invariant : ∀ r : G.arrows,
    Units.map (G.src.residueFieldMap r).hom.toMonoidHom (value (G.src.base r)) =
      Units.map (G.tgt.residueFieldMap r).hom.toMonoidHom (value (G.tgt.base r))

namespace InvariantSystem

variable {G : EtalePresentationGroupoid.{u}} {i : ℤ} (F : InvariantSystem G i)

/-- Groupoid invariance, in terms of `unitPull`. -/
theorem unitPull_src_eq (r : G.arrows) :
    unitPull G.src F.value r = unitPull G.tgt F.value r :=
  F.invariant r

/-- The source of an arrow lies in the support of an invariant system exactly when its target
does. -/
theorem mem_support_src_iff_tgt (r : G.arrows) :
    G.src.base r ∈ F.support ↔ G.tgt.base r ∈ F.support := by
  rw [F.mem_support_iff, F.mem_support_iff, ne_eq, ne_eq, ← unitPull_eq_one_iff G.src,
    ← unitPull_eq_one_iff G.tgt, F.unitPull_src_eq]

/-- The sum of the divisors of the point generators of an invariant system, as a cycle on the
atlas. -/
noncomputable def divisorCycle : AlgebraicCycle G.base ℚ :=
  ∑ w ∈ F.support, pointDivisor G.baseDim w (F.value w)

/-- **The divisor of an invariant system**: the dimension-`i` part of
`∑_{w ∈ support} div (value w)`.  Under the standing hypotheses the projection does nothing
(`InvariantSystem.coe_divisor`). -/
noncomputable def divisor : cyclesOfDimension G.base G.baseDim i :=
  cyclesOfDimension.project F.divisorCycle

/-- Coefficients of `divisorCycle`. -/
theorem divisorCycle_apply (x : G.base) :
    F.divisorCycle x =
      ∑ w ∈ F.support, (pointDivisor G.baseDim w (F.value w) : G.base → ℚ) x := by
  rw [divisorCycle, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]

/-- Under the standing hypotheses the divisor of an invariant system is the sum of the divisors
of its point generators. -/
theorem coe_divisor (hG : G.Good) :
    (F.divisor : AlgebraicCycle G.base ℚ) = F.divisorCycle := by
  have := hG.isLocallyNoetherian_base
  have := hG.isNoetherian_base
  refine project_of_mem _ (Submodule.sum_mem _ fun w hw ↦ ?_)
  rw [pointDivisor_eq]
  exact divisor_pointGenerator_mem_cyclesOfDimension G.baseDim hG.covByDimension_base w _
    (F.dim_support w hw)

/-- The divisor of an invariant system depends only on its values. -/
theorem divisor_eq_of_value_eq {F F' : InvariantSystem G i} (h : F.value = F'.value) :
    F.divisor = F'.divisor := by
  have hs : F.support = F'.support := by
    ext w
    rw [F.mem_support_iff, F'.mem_support_iff, h]
  rw [divisor, divisor, divisorCycle, divisorCycle, hs, h]

end InvariantSystem

/-! ## Vistoli relations and the Vistoli Chow group -/

namespace EtalePresentationGroupoid

variable (G : EtalePresentationGroupoid.{u}) (i : ℤ)

/-- **The Vistoli relations** of an étale presentation groupoid in dimension `i`: the span of
the Vistoli cycles which are divisors of invariant systems.  Under the standing hypotheses every
such divisor is a Vistoli cycle (`InvariantSystem.divisor_mem_cycles`), so this is the span of
all divisors of invariant systems (`vistoliRelations_eq_span`). -/
noncomputable def vistoliRelations : Submodule ℚ (G.cycles i) :=
  Submodule.span ℚ
    {z | ∃ F : InvariantSystem G i, (z : cyclesOfDimension G.base G.baseDim i) = F.divisor}

/-- **The Vistoli rational Chow group** of an étale presentation groupoid in dimension `i`:
invariant dimension-`i` cycles on the atlas modulo divisors of invariant systems.  This coincides
with Vistoli's group (relations = divisors of invariant systems) only under the hypotheses
`EtalePresentationGroupoid.Good`; see the `vistoliRelations`/`pointDivisor` docstrings. -/
noncomputable abbrev vistoliChow := G.cycles i ⧸ G.vistoliRelations i

/-- The class of a Vistoli cycle in the Vistoli Chow group. -/
noncomputable abbrev vistoliQuotientMap : G.cycles i →ₗ[ℚ] G.vistoliChow i :=
  (G.vistoliRelations i).mkQ

variable {G i}

/-- A Vistoli cycle which is the divisor of an invariant system is a Vistoli relation. -/
theorem mem_vistoliRelations_of_divisor (z : G.cycles i) (F : InvariantSystem G i)
    (h : (z : cyclesOfDimension G.base G.baseDim i) = F.divisor) :
    z ∈ G.vistoliRelations i :=
  Submodule.subset_span ⟨F, h⟩

/-- **Vistoli relations are rational equivalences on the atlas.** -/
theorem vistoliRelations_le_relations (hG : G.Good) : G.vistoliRelations i ≤ G.relations i := by
  have := hG.isLocallyNoetherian_base
  have := hG.isNoetherian_base
  refine Submodule.span_le.2 ?_
  rintro z ⟨F, hF⟩
  change ((z : cyclesOfDimension G.base G.baseDim i) : AlgebraicCycle G.base ℚ) ∈
    totalRationalRelations G.base G.baseDim
  rw [hF, F.coe_divisor hG]
  exact Submodule.sum_mem _ fun w _ ↦ (pointDivisor_eq G.baseDim w _).symm ▸
    Submodule.subset_span ⟨_, rfl⟩

/-- **The comparison map from the Vistoli Chow group onto the quotient of the Vistoli cycles by
all rational equivalences of the atlas** (the group `EtalePresentationGroupoid.chow`). -/
noncomputable def vistoliChow_toChow (hG : G.Good) : G.vistoliChow i →ₗ[ℚ] G.chow i :=
  (G.vistoliRelations i).mapQ (G.relations i) LinearMap.id
    (by rw [Submodule.comap_id]; exact vistoliRelations_le_relations hG)

/-- The comparison map sends the Vistoli class of a cycle to its class in `chow`. -/
@[simp]
theorem vistoliChow_toChow_mk (hG : G.Good) (z : G.cycles i) :
    vistoliChow_toChow hG (G.vistoliQuotientMap i z) = G.quotientMap i z :=
  rfl

/-- The comparison map from the Vistoli Chow group onto `chow` is surjective. -/
theorem vistoliChow_toChow_surjective (hG : G.Good) :
    Function.Surjective (vistoliChow_toChow (G := G) (i := i) hG) := by
  intro c
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ c
  exact ⟨G.vistoliQuotientMap i z, rfl⟩

end EtalePresentationGroupoid

/-! ## Invariant systems are determined by their values -/

namespace InvariantSystem

variable {G : EtalePresentationGroupoid.{u}} {i : ℤ}

/-- Two invariant systems with the same values are equal (the support is determined by the
values). -/
theorem ext_of_value {F F' : InvariantSystem G i} (h : F.value = F'.value) : F = F' := by
  refine InvariantSystem.ext ?_ h
  ext w
  rw [F.mem_support_iff, F'.mem_support_iff, h]

end InvariantSystem

/-! ## The identity groupoid: Vistoli relations are the rational equivalences -/

section Identity

variable (X : Scheme.{u}) (dX : DimensionFunction X) (i : ℤ)

/-- The dimension-`i` projection of cycles on `X`, landing in the Vistoli cycles of the identity
groupoid (which are all dimension-`i` cycles). -/
private noncomputable def identityProject :
    AlgebraicCycle X ℚ →ₗ[ℚ] (identityGroupoid X dX).cycles i :=
  LinearMap.codRestrict _ (projectLinear dX i) fun c ↦ by
    rw [(identityGroupoid X dX).cycles_eq_top_of_src_eq_tgt i rfl]
    trivial

open scoped Classical in
/-- The invariant system of the identity groupoid supported at a single point. -/
private noncomputable def singleSystem (w : X) (u : (X.residueField w)ˣ) (hu : u ≠ 1)
    (hw : dX w = i + 1) : InvariantSystem (identityGroupoid X dX) i where
  support := {w}
  value := Pi.mulSingle w u
  mem_support_iff x := by
    by_cases hx : x = w
    · subst hx
      simp [hu]
    · simp [hx]
  dim_support x hx := by
    rw [Finset.mem_singleton.1 hx]
    exact hw
  invariant _ := rfl

/-- **For the identity groupoid the Vistoli relations are exactly the rational equivalences.** -/
theorem vistoliRelations_identityGroupoid [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    [CompactSpace X] (hcov : HomogeneityLocal.CovByDimension dX) :
    (identityGroupoid X dX).vistoliRelations i = (identityGroupoid X dX).relations i := by
  classical
  have hG := identityGroupoid_good X dX hcov
  have : _root_.AlgebraicGeometry.IsNoetherian X := hG.isNoetherian_base
  refine le_antisymm (EtalePresentationGroupoid.vistoliRelations_le_relations hG) ?_
  intro z hz
  have hz' : ((z : cyclesOfDimension X dX i) : AlgebraicCycle X ℚ) ∈
      totalRationalRelations X dX := hz
  have hΨ : identityProject X dX i ((z : cyclesOfDimension X dX i) : AlgebraicCycle X ℚ) = z :=
    Subtype.ext (Subtype.ext (project_of_mem _ (z : cyclesOfDimension X dX i).2))
  rw [← hΨ]
  refine (Submodule.map_le_iff_le_comap.mpr ?_) (Submodule.mem_map_of_mem hz')
  rw [totalRationalRelations, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  dsimp only
  rw [← divisor_pointGenerator dX g]
  by_cases hw : dX g.subspace.genericPointImage = i + 1
  · by_cases hu : g.residueFunction = 1
    · rw [hu, divisor_pointGenerator_one, map_zero]
      exact zero_mem _
    · refine EtalePresentationGroupoid.mem_vistoliRelations_of_divisor _
        (singleSystem X dX i _ _ hu hw) ?_
      change cyclesOfDimension.project _ = cyclesOfDimension.project _
      congr 1
      simp [InvariantSystem.divisorCycle, singleSystem, pointDivisor_eq]
  · have h0 : identityProject X dX i
        ((pointGenerator g.subspace.genericPointImage g.residueFunction).divisor dX) = 0 :=
      Subtype.ext (project_divisor_pointGenerator_of_ne dX hcov _ _ hw)
    rw [h0]
    exact zero_mem _

/-- **The Vistoli Chow group of the identity groupoid of a scheme is its rational Chow group**
`A_i(X)`, for `X` quasi-compact and locally Noetherian with a dimension function satisfying
`CovByDimension`. -/
noncomputable def vistoliChow_identity_equiv [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    [CompactSpace X] (hcov : HomogeneityLocal.CovByDimension dX) :
    (identityGroupoid X dX).vistoliChow i ≃ₗ[ℚ]
      (RationalEquivalenceSystem.canonical (X := X) (dimension := dX) (i := i)).ChowGroup :=
  (Submodule.quotEquivOfEq _ _ (vistoliRelations_identityGroupoid X dX i hcov)).trans
    ((identityGroupoid X dX).chowEquivSchemeChow i rfl)

/-- The identification of `vistoliChow_identity_equiv` sends the Vistoli class of a cycle to its
rational-equivalence class. -/
@[simp]
theorem vistoliChow_identity_equiv_mk [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    [CompactSpace X] (hcov : HomogeneityLocal.CovByDimension dX)
    (z : (identityGroupoid X dX).cycles i) :
    vistoliChow_identity_equiv X dX i hcov ((identityGroupoid X dX).vistoliQuotientMap i z) =
      (RationalEquivalenceSystem.canonical (X := X) (dimension := dX) (i := i)).quotientMap
        (z : cyclesOfDimension X dX i) :=
  rfl

end Identity

/-! ## Morita maps of étale presentation groupoids -/

/-- **A Morita map** `H → G` of étale presentation groupoids: a morphism of groupoids
(`onBase`, `onArrows`, compatible with sources and targets) whose map of atlases is étale of
relative dimension zero, and which satisfies the four conditions

* (F0) `onBase` is surjective;
* (F1) two points of `H.base` over the same point `u` of `G.base` are joined by an arrow `r'` of
  `H` along which the two composite residue field maps `κ(u) → κ(r')` agree;
* (F2) Galois descent in the fibres of `onBase`: an element of `κ(u')` with equal images under
  the two legs of every self-arrow of `u'` comes from `κ(onBase u')`;
* (F3) fullness: for every arrow `r` of `G` and points `u'`, `v'` over its source and target,
  there is an arrow of `H` from `u'` to `v'` over `r`.

These hold for the comparison map from the Čech groupoid of `U'' = U ×_𝒳 U'` to that of `U`,
for two étale atlases `U`, `U'` of a Deligne–Mumford stack `𝒳`, and for the Čech groupoid of an
étale surjection onto a scheme compared with the identity groupoid of that scheme. -/
structure MoritaMap (H G : EtalePresentationGroupoid.{u}) where
  /-- The map of atlases. -/
  onBase : H.base ⟶ G.base
  /-- The map of arrow schemes. -/
  onArrows : H.arrows ⟶ G.arrows
  /-- The map of atlases is étale. -/
  onBase_etale : _root_.AlgebraicGeometry.Etale onBase
  /-- The map of atlases has relative dimension zero for the two certified gradings. -/
  onBase_dim (u : H.base) : H.baseDim u = G.baseDim (onBase.base u)
  /-- Compatibility with the source maps. -/
  src_comm : onArrows ≫ G.src = H.src ≫ onBase
  /-- Compatibility with the target maps. -/
  tgt_comm : onArrows ≫ G.tgt = H.tgt ≫ onBase
  /-- (F0) The map of atlases is surjective. -/
  onBase_surjective : Function.Surjective onBase.base
  /-- (F1) Two points over the same point are joined by an arrow along which the two composite
  residue field maps agree. -/
  exists_arrow_over_identity (u' v' : H.base) :
    onBase.base u' = onBase.base v' →
      ∃ (r' : H.arrows) (h : (H.src ≫ onBase).base r' = (H.tgt ≫ onBase).base r'),
        H.src.base r' = u' ∧ H.tgt.base r' = v' ∧
          (H.src ≫ onBase).residueFieldMap r' =
            (G.base.residueFieldCongr h).hom ≫ (H.tgt ≫ onBase).residueFieldMap r'
  /-- (F2) Galois descent: an element of `κ(u')` whose images under the two legs of every
  self-arrow of `u'` agree is the image of an element of `κ(onBase u')`. -/
  residue_descent (u' : H.base) (a : H.base.residueField u') :
    (∀ (r' : H.arrows) (hs : H.src.base r' = u') (ht : H.tgt.base r' = u'),
      (H.src.residueFieldMap r').hom ((H.base.residueFieldCongr hs).inv.hom a) =
        (H.tgt.residueFieldMap r').hom ((H.base.residueFieldCongr ht).inv.hom a)) →
      ∃ b : G.base.residueField (onBase.base u'), (onBase.residueFieldMap u').hom b = a
  /-- (F3) Fullness: arrows of `G` lift to arrows of `H` between any chosen lifts of their
  source and target. -/
  full (r : G.arrows) (u' v' : H.base) :
    onBase.base u' = G.src.base r → onBase.base v' = G.tgt.base r →
      ∃ r' : H.arrows, H.src.base r' = u' ∧ H.tgt.base r' = v' ∧ onArrows.base r' = r

attribute [instance] MoritaMap.onBase_etale

namespace MoritaMap

variable {H G : EtalePresentationGroupoid.{u}} (φ : MoritaMap H G) (i : ℤ)

/-- The map of atlases intertwines the source maps on points. -/
theorem onBase_src_apply (r' : H.arrows) :
    φ.onBase.base (H.src.base r') = G.src.base (φ.onArrows.base r') := by
  have h := congrArg (fun f : H.arrows ⟶ G.base ↦ f.base r') φ.src_comm
  simpa using h.symm

/-- The map of atlases intertwines the target maps on points. -/
theorem onBase_tgt_apply (r' : H.arrows) :
    φ.onBase.base (H.tgt.base r') = G.tgt.base (φ.onArrows.base r') := by
  have h := congrArg (fun f : H.arrows ⟶ G.base ↦ f.base r') φ.tgt_comm
  simpa using h.symm

/-- Étale pullback along the map of atlases preserves Vistoli cycles. -/
theorem flatPullbackEtale_mem_cycles {z : cyclesOfDimension G.base G.baseDim i}
    (hz : z ∈ G.cycles i) :
    cyclesOfDimension.flatPullbackEtale φ.onBase φ.onBase_dim z ∈ H.cycles i := by
  rw [EtalePresentationGroupoid.mem_cycles_iff] at hz ⊢
  intro r'
  simp only [cyclesOfDimension.flatPullbackEtale_apply]
  rw [φ.onBase_src_apply, φ.onBase_tgt_apply]
  exact hz _

/-- **The pullback of Vistoli cycles along a Morita map.** -/
noncomputable def onCycles : G.cycles i →ₗ[ℚ] H.cycles i :=
  (cyclesOfDimension.flatPullbackEtale φ.onBase φ.onBase_dim).restrict
    fun _ hz ↦ φ.flatPullbackEtale_mem_cycles i hz

/-- Coefficients of the pullback of a Vistoli cycle along a Morita map. -/
@[simp]
theorem onCycles_apply (z : G.cycles i) (u' : H.base) :
    (((φ.onCycles i z : H.cycles i) : cyclesOfDimension H.base H.baseDim i) :
        AlgebraicCycle H.base ℚ) u' =
      ((z : cyclesOfDimension G.base G.baseDim i) : AlgebraicCycle G.base ℚ)
        (φ.onBase.base u') :=
  rfl

/-- The pullback of a Vistoli cycle along a Morita map is its étale pullback. -/
theorem coe_onCycles (z : G.cycles i) :
    ((φ.onCycles i z : H.cycles i) : cyclesOfDimension H.base H.baseDim i) =
      cyclesOfDimension.flatPullbackEtale φ.onBase φ.onBase_dim
        (z : cyclesOfDimension G.base G.baseDim i) :=
  rfl

/-- Étale pullback along the (surjective) map of atlases is injective on cycles. -/
theorem flatPullbackEtale_injective :
    Function.Injective (cyclesOfDimension.flatPullbackEtale (i := i) φ.onBase φ.onBase_dim) := by
  intro z₁ z₂ h
  apply Subtype.ext
  refine Function.locallyFinsuppWithin.ext fun x ↦ ?_
  obtain ⟨u', rfl⟩ := φ.onBase_surjective x
  have := congrArg (fun z : cyclesOfDimension H.base H.baseDim i ↦
    (z : AlgebraicCycle H.base ℚ) u') h
  simpa using this

/-- Points of `H.base` in the same fibre of `onBase` have the same coefficient in every Vistoli
cycle of `H`. -/
theorem apply_eq_of_onBase_eq (z' : H.cycles i) {u₁ u₂ : H.base}
    (h : φ.onBase.base u₁ = φ.onBase.base u₂) :
    ((z' : cyclesOfDimension H.base H.baseDim i) : AlgebraicCycle H.base ℚ) u₁ =
      ((z' : cyclesOfDimension H.base H.baseDim i) : AlgebraicCycle H.base ℚ) u₂ := by
  obtain ⟨r', -, hs, ht, -⟩ := φ.exists_arrow_over_identity u₁ u₂ h
  have := (H.mem_cycles_iff i).1 z'.2 r'
  rwa [hs, ht] at this

/-- The pullback of Vistoli cycles along a Morita map is injective. -/
theorem onCycles_injective : Function.Injective (φ.onCycles i) := fun _ _ h ↦
  Subtype.ext (φ.flatPullbackEtale_injective i (congrArg Subtype.val h))

/-- The pullback of Vistoli cycles along a Morita map is surjective when the atlas of `H` is
quasi-compact. -/
theorem onCycles_surjective (hH : H.Good) : Function.Surjective (φ.onCycles i) := by
  intro z'
  have := hH.compactSpace_base
  let Z' : AlgebraicCycle H.base ℚ := (z' : cyclesOfDimension H.base H.baseDim i)
  let c : G.base → H.base := fun x ↦ (φ.onBase_surjective x).choose
  have hc : ∀ x, φ.onBase.base (c x) = x := fun x ↦ (φ.onBase_surjective x).choose_spec
  let f : G.base → ℚ := fun x ↦ Z' (c x)
  have hf : (Function.support f).Finite := by
    refine ((finite_support_of_compactSpace Z').image φ.onBase.base).subset ?_
    intro x hx
    exact ⟨c x, hx, hc x⟩
  let z₀ : cyclesOfDimension G.base G.baseDim i := ⟨cycleOfFiniteSupport f hf, fun x hx ↦ by
    change Z' (c x) = 0
    refine (z' : cyclesOfDimension H.base H.baseDim i).2 (c x) ?_
    rw [φ.onBase_dim, hc]
    exact hx⟩
  have hz₀ : z₀ ∈ G.cycles i := by
    rw [EtalePresentationGroupoid.mem_cycles_iff]
    intro r
    obtain ⟨r', hs, ht, -⟩ := φ.full r (c (G.src.base r)) (c (G.tgt.base r)) (hc _) (hc _)
    change Z' (c (G.src.base r)) = Z' (c (G.tgt.base r))
    rw [← hs, ← ht]
    exact (H.mem_cycles_iff i).1 z'.2 r'
  refine ⟨⟨z₀, hz₀⟩, Subtype.ext (Subtype.ext ?_)⟩
  refine Function.locallyFinsuppWithin.ext fun u' ↦ ?_
  change Z' (c (φ.onBase.base u')) = Z' u'
  exact φ.apply_eq_of_onBase_eq i z' (hc _)

/-- **The pullback of Vistoli cycles along a Morita map is bijective** (the atlas of `H` being
quasi-compact). -/
theorem onCycles_bijective (hH : H.Good) : Function.Bijective (φ.onCycles i) :=
  ⟨φ.onCycles_injective i, φ.onCycles_surjective i hH⟩

/-- Preimages of finite sets under the map of atlases are finite. -/
theorem finite_preimage (hH : H.Good) {A : Set G.base} (hA : A.Finite) :
    (φ.onBase.base ⁻¹' A).Finite := by
  have := hH.compactSpace_base
  exact finite_preimage_of_etale_of_compactSpace φ.onBase hA

end MoritaMap

/-! ## Pullback of invariant systems along a Morita map -/

namespace InvariantSystem

variable {H G : EtalePresentationGroupoid.{u}} {i : ℤ}

/-- **The pullback of an invariant system along a Morita map**: the value at `u'` is the image of
the value at `onBase u'` in `κ(u')`, and the support is the preimage of the support. -/
noncomputable def pullback (F : InvariantSystem G i) (φ : MoritaMap H G) (hH : H.Good) :
    InvariantSystem H i where
  support := (φ.finite_preimage hH F.support.finite_toSet).toFinset
  value := unitPull φ.onBase F.value
  mem_support_iff u' := by
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe, F.mem_support_iff, ne_eq,
      ne_eq, unitPull_eq_one_iff]
  dim_support u' hu := by
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe] at hu
    rw [φ.onBase_dim]
    exact F.dim_support _ hu
  invariant r' := by
    change unitPull H.src (unitPull φ.onBase F.value) r' =
      unitPull H.tgt (unitPull φ.onBase F.value) r'
    rw [← unitPull_comp, ← unitPull_comp, ← unitPull_congr φ.src_comm,
      ← unitPull_congr φ.tgt_comm, unitPull_comp, unitPull_comp,
      show unitPull G.src F.value = unitPull G.tgt F.value from funext F.unitPull_src_eq]

/-- The values of the pullback of an invariant system. -/
@[simp]
theorem pullback_value (F : InvariantSystem G i) (φ : MoritaMap H G) (hH : H.Good) :
    (F.pullback φ hH).value = unitPull φ.onBase F.value :=
  rfl

/-- The support of the pullback of an invariant system is the preimage of its support. -/
theorem mem_pullback_support (F : InvariantSystem G i) (φ : MoritaMap H G) (hH : H.Good)
    (u' : H.base) : u' ∈ (F.pullback φ hH).support ↔ φ.onBase.base u' ∈ F.support :=
  Set.Finite.mem_toFinset _

end InvariantSystem

/-! ## Descent of invariant systems along a Morita map -/

namespace MoritaMap

variable {H G : EtalePresentationGroupoid.{u}} (φ : MoritaMap H G) {i : ℤ}

/-- Every value of an invariant system of `H` descends to the residue field of the image
point (Galois descent (F2), whose hypothesis is the invariance under self-arrows). -/
theorem exists_descent (F' : InvariantSystem H i) (u₀ : H.base) :
    ∃ b : (G.base.residueField (φ.onBase.base u₀))ˣ,
      Units.map (φ.onBase.residueFieldMap u₀).hom.toMonoidHom b = F'.value u₀ := by
  obtain ⟨b, hb⟩ := φ.residue_descent u₀ (F'.value u₀ : H.base.residueField u₀) fun r' hs ht ↦ by
    rw [Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_inv,
      residueFieldCongr_hom_apply_family hs.symm F'.value,
      residueFieldCongr_hom_apply_family ht.symm F'.value]
    exact congrArg Units.val (F'.invariant r')
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact (F'.value u₀).ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, Units.ext hb⟩

/-- Transport of a descended value along the fibres of `onBase`, using (F1) and the invariance
of the system. -/
theorem descent_transport (F' : InvariantSystem H i) {u₁ u₂ : H.base}
    (h : φ.onBase.base u₂ = φ.onBase.base u₁) (b : (G.base.residueField (φ.onBase.base u₁))ˣ)
    (hb : Units.map (φ.onBase.residueFieldMap u₁).hom.toMonoidHom b = F'.value u₁) :
    Units.map (φ.onBase.residueFieldMap u₂).hom.toMonoidHom
      (Units.map (G.base.residueFieldCongr h).inv.hom.toMonoidHom b) = F'.value u₂ := by
  obtain ⟨r', hr, hs, ht, hcomp⟩ := φ.exists_arrow_over_identity u₁ u₂ h.symm
  subst hs ht
  apply units_map_residueFieldMap_injective H.tgt r'
  have hinv := F'.invariant r'
  rw [← hb] at hinv
  rw [← hinv]
  apply Units.ext
  have e1 := Scheme.residueFieldMap_comp H.src φ.onBase r'
  rw [hcomp, Scheme.residueFieldMap_comp] at e1
  have e2 := congrArg (fun f ↦ f.hom (b : G.base.residueField (φ.onBase.base (H.src.base r')))) e1
  beta_reduce at e2
  rw [Scheme.residueFieldCongr_inv]
  exact e2

/-- The descended family of units on the atlas of `G` attached to an invariant system of `H`. -/
noncomputable def descendValue (F' : InvariantSystem H i) (x : G.base) :
    (G.base.residueField x)ˣ :=
  Units.map (G.base.residueFieldCongr (φ.onBase_surjective x).choose_spec).hom.hom.toMonoidHom
    (φ.exists_descent F' (φ.onBase_surjective x).choose).choose

/-- The descended family pulls back to the values of the invariant system. -/
theorem unitPull_descendValue (F' : InvariantSystem H i) :
    unitPull φ.onBase (φ.descendValue F') = F'.value := by
  funext u'
  have h0 := (φ.onBase_surjective (φ.onBase.base u')).choose_spec
  have := φ.descent_transport F' h0.symm
    (φ.exists_descent F' (φ.onBase_surjective (φ.onBase.base u')).choose).choose
    (φ.exists_descent F' (φ.onBase_surjective (φ.onBase.base u')).choose).choose_spec
  rw [← this]
  rfl

/-- **Every invariant system of `H` is the pullback of an invariant system of `G`** along a
Morita map. -/
theorem exists_pullback_eq (hH : H.Good) (F' : InvariantSystem H i) :
    ∃ F : InvariantSystem G i, F.pullback φ hH = F' := by
  classical
  have hD := φ.unitPull_descendValue F'
  have hD' : ∀ u', unitPull φ.onBase (φ.descendValue F') u' = F'.value u' :=
    fun u' ↦ congrFun hD u'
  let F : InvariantSystem G i :=
    { support := F'.support.image φ.onBase.base
      value := φ.descendValue F'
      mem_support_iff := fun x ↦ by
        constructor
        · rintro hx
          obtain ⟨v', hv', rfl⟩ := Finset.mem_image.1 hx
          rw [ne_eq, ← unitPull_eq_one_iff, hD']
          exact (F'.mem_support_iff v').1 hv'
        · intro hx
          obtain ⟨u', rfl⟩ := φ.onBase_surjective x
          refine Finset.mem_image.2 ⟨u', (F'.mem_support_iff u').2 ?_, rfl⟩
          rw [← hD', ne_eq, unitPull_eq_one_iff]
          exact hx
      dim_support := fun x hx ↦ by
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.1 hx
        rw [← φ.onBase_dim]
        exact F'.dim_support v' hv'
      invariant := fun r ↦ by
        obtain ⟨r', -, -, rfl⟩ := φ.full r _ _ (φ.onBase_surjective (G.src.base r)).choose_spec
          (φ.onBase_surjective (G.tgt.base r)).choose_spec
        apply units_map_residueFieldMap_injective φ.onArrows r'
        change unitPull φ.onArrows (unitPull G.src (φ.descendValue F')) r' =
          unitPull φ.onArrows (unitPull G.tgt (φ.descendValue F')) r'
        rw [← unitPull_comp, ← unitPull_comp, unitPull_congr φ.src_comm,
          unitPull_congr φ.tgt_comm, unitPull_comp, unitPull_comp, hD]
        exact F'.invariant r' }
  exact ⟨F, InvariantSystem.ext_of_value hD⟩

end MoritaMap

/-! ## Étale pullback of divisors of invariant systems -/

namespace InvariantSystem

variable {H G : EtalePresentationGroupoid.{u}} {i : ℤ}

/-- The étale pullback of `divisorCycle` along an étale map of relative dimension zero from a
Noetherian scheme is the sum of the divisors of the pulled-back units over the preimage of the
support. -/
private theorem pullbackEtale_divisorCycle {R : Scheme.{u}} (F : InvariantSystem G i)
    (hG : G.Good) (s : R ⟶ G.base) [_root_.AlgebraicGeometry.Etale s]
    [_root_.AlgebraicGeometry.IsNoetherian R] (dimR : DimensionFunction R)
    (hdim : ∀ r, dimR r = G.baseDim (s.base r)) (hcovR : HomogeneityLocal.CovByDimension dimR)
    (hfin : (s.base ⁻¹' (F.support : Set G.base)).Finite) :
    AlgebraicCycle.pullbackEtale s F.divisorCycle =
      ∑ w' ∈ hfin.toFinset, pointDivisor dimR w' (unitPull s F.value w') := by
  have := hG.isNoetherian_base
  rw [divisorCycle, Finset.sum_congr rfl fun w _ ↦ pointDivisor_eq G.baseDim w (F.value w),
    Finset.sum_congr rfl fun w' _ ↦ pointDivisor_eq dimR w' (unitPull s F.value w')]
  exact pullbackEtale_sum_divisor_pointGenerator s G.baseDim dimR hdim hG.covByDimension_base
    hcovR F.support F.value

/-- **The divisor of an invariant system is a Vistoli cycle** (under the standing
hypotheses). -/
theorem divisor_mem_cycles (F : InvariantSystem G i) (hG : G.Good) : F.divisor ∈ G.cycles i := by
  have := hG.isNoetherian_arrows
  have hs := F.pullbackEtale_divisorCycle hG G.src G.arrowsDim G.src_dim
    hG.covByDimension_arrows (finite_preimage_of_etale_of_compactSpace G.src
      F.support.finite_toSet)
  have ht := F.pullbackEtale_divisorCycle hG G.tgt G.arrowsDim G.tgt_dim
    hG.covByDimension_arrows (finite_preimage_of_etale_of_compactSpace G.tgt
      F.support.finite_toSet)
  have heq : AlgebraicCycle.pullbackEtale G.src F.divisorCycle =
      AlgebraicCycle.pullbackEtale G.tgt F.divisorCycle := by
    rw [hs, ht]
    refine Finset.sum_congr ?_ fun r' _ ↦ by rw [F.unitPull_src_eq]
    ext r'
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe]
    exact F.mem_support_src_iff_tgt r'
  rw [EtalePresentationGroupoid.mem_cycles_iff, F.coe_divisor hG]
  intro r
  exact congrArg (fun c : AlgebraicCycle G.arrows ℚ ↦ c r) heq

/-- The cycle `divisorCycle` of the pullback of an invariant system along a Morita map is the
étale pullback of its `divisorCycle`. -/
theorem divisorCycle_pullback (F : InvariantSystem G i) (φ : MoritaMap H G) (hH : H.Good)
    (hG : G.Good) :
    (F.pullback φ hH).divisorCycle = AlgebraicCycle.pullbackEtale φ.onBase F.divisorCycle := by
  have := hH.isNoetherian_base
  rw [F.pullbackEtale_divisorCycle hG φ.onBase H.baseDim φ.onBase_dim hH.covByDimension_base
    (φ.finite_preimage hH F.support.finite_toSet)]
  rfl

/-- **The divisor of the pullback of an invariant system along a Morita map is the étale
pullback of its divisor.** -/
theorem divisor_pullback_eq_flatPullbackEtale (F : InvariantSystem G i) (φ : MoritaMap H G)
    (hH : H.Good)
    (hG : G.Good) :
    (F.pullback φ hH).divisor =
      cyclesOfDimension.flatPullbackEtale φ.onBase φ.onBase_dim F.divisor := by
  apply Subtype.ext
  change ((F.pullback φ hH).divisor : AlgebraicCycle H.base ℚ) =
    AlgebraicCycle.pullbackEtale φ.onBase (F.divisor : AlgebraicCycle G.base ℚ)
  rw [coe_divisor _ hH, coe_divisor _ hG, divisorCycle_pullback F φ hH hG]

end InvariantSystem

namespace EtalePresentationGroupoid

variable {G : EtalePresentationGroupoid.{u}} {i : ℤ}

/-- **Under the standing hypotheses the Vistoli relations are the span of the divisors of all
invariant systems.** -/
theorem vistoliRelations_eq_span (hG : G.Good) :
    G.vistoliRelations i = Submodule.span ℚ
      (Set.range fun F : InvariantSystem G i ↦
        (⟨F.divisor, F.divisor_mem_cycles hG⟩ : G.cycles i)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨F, hF⟩
    have hz : z = ⟨F.divisor, F.divisor_mem_cycles hG⟩ := Subtype.ext hF
    exact Submodule.subset_span ⟨F, hz.symm⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨F, rfl⟩
    exact mem_vistoliRelations_of_divisor _ F rfl

end EtalePresentationGroupoid

namespace MoritaMap

variable {H G : EtalePresentationGroupoid.{u}} (φ : MoritaMap H G) (i : ℤ)

/-- **The divisor of the pullback of an invariant system along a Morita map is the pullback of
its divisor.** -/
theorem divisor_pullback (hH : H.Good) (hG : G.Good) (F : InvariantSystem G i) :
    (F.pullback φ hH).divisor =
      ((φ.onCycles i ⟨F.divisor, F.divisor_mem_cycles hG⟩ : H.cycles i) :
        cyclesOfDimension H.base H.baseDim i) :=
  F.divisor_pullback_eq_flatPullbackEtale φ hH hG

/-- **A Morita map identifies the Vistoli relations.** -/
theorem map_vistoliRelations (hH : H.Good) (hG : G.Good) :
    Submodule.map (φ.onCycles i) (G.vistoliRelations i) = H.vistoliRelations i := by
  apply le_antisymm
  · rw [EtalePresentationGroupoid.vistoliRelations, Submodule.map_span_le]
    rintro z ⟨F, hF⟩
    refine EtalePresentationGroupoid.mem_vistoliRelations_of_divisor _ (F.pullback φ hH) ?_
    rw [coe_onCycles, hF, F.divisor_pullback_eq_flatPullbackEtale φ hH hG]
  · refine Submodule.span_le.2 ?_
    rintro z' ⟨F', hF'⟩
    obtain ⟨F, rfl⟩ := φ.exists_pullback_eq hH F'
    obtain ⟨z, rfl⟩ := φ.onCycles_surjective i hH z'
    refine Submodule.mem_map_of_mem
      (EtalePresentationGroupoid.mem_vistoliRelations_of_divisor z F ?_)
    apply φ.flatPullbackEtale_injective i
    rw [← coe_onCycles, hF', F.divisor_pullback_eq_flatPullbackEtale φ hH hG]

/-- **Morita invariance of the Vistoli Chow group**: a Morita map `H → G` of étale presentation
groupoids satisfying the standing hypotheses induces an isomorphism of Vistoli rational Chow
groups `A_i(G) ≃ A_i(H)`, given on classes by étale pullback along the map of atlases. -/
noncomputable def vistoliChowEquiv (hH : H.Good) (hG : G.Good) :
    G.vistoliChow i ≃ₗ[ℚ] H.vistoliChow i :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective (φ.onCycles i) (φ.onCycles_bijective i hH))
    (φ.map_vistoliRelations i hH hG)

/-- The Morita isomorphism sends the Vistoli class of a cycle to the class of its pullback. -/
@[simp]
theorem vistoliChowEquiv_mk (hH : H.Good) (hG : G.Good) (z : G.cycles i) :
    φ.vistoliChowEquiv i hH hG (G.vistoliQuotientMap i z) =
      H.vistoliQuotientMap i (φ.onCycles i z) :=
  rfl

end MoritaMap

end GromovWitten.AlgebraicGeometry.IntersectionTheory
