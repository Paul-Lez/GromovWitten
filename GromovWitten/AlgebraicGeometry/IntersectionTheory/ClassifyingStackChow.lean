/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.VistoliRelations
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperPushforwardCurve

/-!
# Vistoli Chow groups and degree of the groupoid `Γ_k ⇉ Spec k`

For a field `k` and a finite type `Γ` we build the étale presentation groupoid
`Γ_k ⇉ Spec k`, where `Γ_k = Spec (Γ → k)` is the disjoint union of `|Γ|` copies of `Spec k` and
both legs are the structure map `Spec (Γ → k) ⟶ Spec k`.  Mathematically this is the self-overlap
groupoid `Spec k ×_{BΓ} Spec k ⇉ Spec k` of the atlas `Spec k → BΓ = [Spec k / Γ]` (for a group
`Γ`).  **This identification is not made here**: `constantGroupoid` is a standalone
`EtalePresentationGroupoid`, not derived from the stack `classifyingStack`; relating the two is
left to a later round.  The construction uses only that `Γ` is a finite type (no group structure
is needed, since both legs of the groupoid coincide).

We compute its Vistoli Chow groups (`A_0 ≃ ℚ`, `A_i = 0` for `i ≠ 0`), define, for a general
étale presentation groupoid proper over `k`, a degree map on the dimension-zero Vistoli Chow group
normalised by the degree of the source leg, and show that the class of the point has degree
`1 / |Γ|` for `constantGroupoid`.

## Main results

* `ClassifyingStackChow.constantGroupoid k Γ`: the groupoid `Spec (Γ → k) ⇉ Spec k`.
* `ClassifyingStackChow.constantGroupoid_good`: it satisfies the standing hypotheses
  `EtalePresentationGroupoid.Good`.
* `ClassifyingStackChow.vistoliChow_zero_equiv : (constantGroupoid k Γ).vistoliChow 0 ≃ₗ[ℚ] ℚ`.
* `ClassifyingStackChow.subsingleton_vistoliChow_of_ne_zero`: `vistoliChow i` is trivial for
  `i ≠ 0`.
* `EtalePresentationGroupoid.IsOfDegree G d`: the source leg pushes the fundamental cycle of the
  arrow scheme to `d` times the fundamental cycle of the atlas; `IsOfDegree.unique`: for a
  nonempty atlas `d` is determined by `G`.
* `EtalePresentationGroupoid.vistoliChow_toSchemeChow`: the comparison map from the Vistoli Chow
  group to the Chow group of the atlas scheme (under `Good`).
* `EtalePresentationGroupoid.vistoliDegree`: `(1 / d) • deg ∘ vistoliChow_toSchemeChow` on
  `vistoliChow 0`.
* `ClassifyingStackChow.constantGroupoid_isOfDegree`: `constantGroupoid` has degree `|Γ|`.
* `ClassifyingStackChow.fundamentalClass` and `ClassifyingStackChow.vistoliDegree_fundamentalClass`:
  the class of the point has Vistoli degree `1 / |Γ|` for nonempty `Γ`
  (`natCard_mul_vistoliDegree_fundamentalClass`: `|Γ| · deg [pt] = 1`).
-/

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Order

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace ClassifyingStackChow

variable (k : Type u) [Field k] (Γ : Type u) [Finite Γ]

/-! ## The groupoid `Γ_k ⇉ Spec k` -/

/-- The arrow scheme `Γ_k = Spec (Γ → k)`, a disjoint union of `|Γ|` copies of `Spec k`. -/
noncomputable abbrev constantArrows : Scheme.{u} := Spec (CommRingCat.of (Γ → k))

/-- The structure map `Γ_k = Spec (Γ → k) ⟶ Spec k`. -/
noncomputable abbrev constantProjection :
    constantArrows k Γ ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Γ → k)))

/-- The structure map `Spec (Γ → k) ⟶ Spec k` is étale (`Γ → k` is a finite split `k`-algebra). -/
instance etale_constantProjection :
    _root_.AlgebraicGeometry.Etale (constantProjection k Γ) := by
  rw [HasRingHomProperty.Spec_iff (P := @_root_.AlgebraicGeometry.Etale)]
  exact RingHom.etale_algebraMap.2 inferInstance

variable {k Γ} in
/-- The specialisation order of `Spec (Γ → k)` is discrete: every point is closed. -/
theorem constantArrows_eq_of_le {x y : constantArrows k Γ} (h : x ≤ y) : x = y := by
  have : T1Space (constantArrows k Γ) := by
    change T1Space (PrimeSpectrum (Γ → k)); infer_instance
  exact (specializes_iff_eq.mp h).symm

/-- The dimension function of `Spec (Γ → k)`: identically zero. -/
noncomputable def constantArrowsDim : DimensionFunction (constantArrows k Γ) where
  toFun _ := 0
  nonnegative _ := le_rfl
  height_eq x := by
    simp only [Int.toNat_zero, Nat.cast_zero]
    rw [Order.height_eq_zero]
    intro y hy
    exact (constantArrows_eq_of_le hy).ge

/-- **The groupoid `Γ_k ⇉ Spec k`**: atlas `Spec k`, arrow scheme `Spec (Γ → k)`, both legs the
structure map, both dimension functions zero.  For a finite group `Γ` this is, mathematically,
the self-overlap groupoid of the atlas `Spec k → BΓ`; that identification with the stack
`classifyingStack` is **not** established here (it is to be made in a later round). -/
noncomputable abbrev constantGroupoid : EtalePresentationGroupoid.{u} where
  base := Spec (CommRingCat.of k)
  arrows := constantArrows k Γ
  baseDim := DimensionFunction.specField k
  arrowsDim := constantArrowsDim k Γ
  src := constantProjection k Γ
  tgt := constantProjection k Γ
  src_etale := inferInstance
  tgt_etale := inferInstance
  src_dim _ := rfl
  tgt_dim _ := rfl

/-- `constantGroupoid` satisfies the standing hypotheses `EtalePresentationGroupoid.Good`. -/
theorem constantGroupoid_good : (constantGroupoid k Γ).Good where
  compactSpace_base := inferInstance
  compactSpace_arrows := inferInstance
  isLocallyNoetherian_base := inferInstance
  isLocallyNoetherian_arrows := inferInstance
  covByDimension_base _ _ h := (h.1.ne (Subsingleton.elim _ _)).elim
  covByDimension_arrows _ _ h := (h.1.ne (constantArrows_eq_of_le h.1.le)).elim

/-! ## Vistoli Chow groups -/

/-- The dimension-zero Vistoli relations of `constantGroupoid` vanish: an invariant system of
dimension `1` has empty support, since every point of `Spec k` has dimension `0`. -/
theorem constantGroupoid_vistoliRelations_eq_bot :
    (constantGroupoid k Γ).vistoliRelations 0 = ⊥ := by
  refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
  rintro z ⟨F, hF⟩
  have hs : F.support = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun w hw ↦ ?_
    have := F.dim_support w hw
    simp at this
  have h0 : F.divisor = 0 := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.coe_injective
    funext x
    simp [InvariantSystem.divisor, InvariantSystem.divisorCycle, hs]
  change z = 0
  apply Subtype.ext
  rw [hF, h0]
  rfl

/-- **`A_0` of `Γ_k ⇉ Spec k` is `ℚ`**: the Vistoli Chow group in dimension zero is identified
with `ℚ` by evaluating a cycle at the unique point of `Spec k`. -/
noncomputable def vistoliChow_zero_equiv :
    (constantGroupoid k Γ).vistoliChow 0 ≃ₗ[ℚ] ℚ :=
  (((constantGroupoid k Γ).vistoliRelations 0).quotEquivOfEqBot
    (constantGroupoid_vistoliRelations_eq_bot k Γ)).trans
    ((LinearEquiv.ofTop _
      (EtalePresentationGroupoid.cycles_eq_top_of_src_eq_tgt (constantGroupoid k Γ) 0 rfl)).trans
      (PointChow.cyclesEquivRat k))

/-- **`A_i` of `Γ_k ⇉ Spec k` vanishes for `i ≠ 0`**: there are no nonzero cycles of dimension
`i ≠ 0` on `Spec k`. -/
theorem subsingleton_vistoliChow_of_ne_zero {i : ℤ} (hi : i ≠ 0) :
    Subsingleton ((constantGroupoid k Γ).vistoliChow i) := by
  have hc : Subsingleton (cyclesOfDimension (Spec (CommRingCat.of k))
      (DimensionFunction.specField k) i) := by
    refine ⟨fun a b ↦ Subtype.ext
      (Function.locallyFinsuppWithin.coe_injective (funext fun x ↦ ?_))⟩
    change (a : AlgebraicCycle _ ℚ) x = (b : AlgebraicCycle _ ℚ) x
    rw [a.2 x (by simpa using hi.symm), b.2 x (by simpa using hi.symm)]
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ b
  rw [Subsingleton.elim a b]

end ClassifyingStackChow

/-! ## Degree on the dimension-zero Vistoli Chow group -/

namespace EtalePresentationGroupoid

variable (G : EtalePresentationGroupoid.{u})

/-- **The groupoid has degree `d`**: the pushforward along the source leg of the fundamental
cycle of the arrow scheme is `d` times the fundamental cycle of the atlas (weights: the certified
dimension functions).  For the self-overlap groupoid of an étale atlas of a stack this `d` is the
degree of the atlas over the stack.  For a nonempty atlas `d` is determined by `G`
(`IsOfDegree.unique`). -/
def IsOfDegree [Nonempty G.base] [_root_.AlgebraicGeometry.IsLocallyNoetherian G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.arrows]
    [_root_.AlgebraicGeometry.QuasiCompact G.src] (d : ℚ) : Prop :=
  AlgebraicCycle.map G.src ⇑G.arrowsDim ⇑G.baseDim G.arrows.fundamentalCycle =
    d • G.base.fundamentalCycle

variable {G}

/-- A nonempty scheme has a maximal point for the specialisation order (the generic point of an
irreducible component). -/
theorem _root_.GromovWitten.AlgebraicGeometry.IntersectionTheory.exists_isMax_of_nonempty_scheme
    (X : Scheme.{u}) [Nonempty X] : ∃ x : X, IsMax x := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨Z, hZ, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure {x₀}) isIrreducible_singleton.closure
  let g : X := (genericPoints.ofComponent ⟨Z, hZ⟩).1
  have hg : closure {g} = Z := (genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩).def
  refine ⟨g, fun y hy ↦ ?_⟩
  -- `hy : y ⤳ g`, so `Z = closure {g} ⊆ closure {y}`, and maximality of `Z` gives equality.
  have hsub : Z ⊆ closure {y} := hg ▸ (specializes_iff_closure_subset.mp hy)
  have hy' : closure {y} ⊆ Z := hZ.2 isIrreducible_singleton.closure hsub
  change g ⤳ y
  rw [specializes_iff_mem_closure, hg]
  exact hy' (subset_closure rfl)

/-- **The degree of a groupoid with nonempty atlas is unique.** -/
theorem IsOfDegree.unique [Nonempty G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.arrows]
    [_root_.AlgebraicGeometry.QuasiCompact G.src] {d d' : ℚ} (h : G.IsOfDegree d)
    (h' : G.IsOfDegree d') : d = d' := by
  obtain ⟨x, hx⟩ := exists_isMax_of_nonempty_scheme G.base
  have hx' := congrArg (fun c : AlgebraicCycle G.base ℚ ↦ c x) (h.symm.trans h')
  simp only [Function.locallyFinsuppWithin.coe_rational_smul, Pi.smul_apply, smul_eq_mul,
    G.base.fundamentalCycle_apply_of_isMax x hx] at hx'
  have hpos : (0 : ℚ) < G.base.genericLength x := by
    exact_mod_cast G.base.genericLength_pos x hx
  exact mul_right_cancel₀ hpos.ne' hx'

/-- **The comparison map from the Vistoli Chow group to the Chow group of the atlas scheme**:
under the standing hypotheses every Vistoli relation is a rational equivalence on the atlas
(`vistoliRelations_le_relations`), so the inclusion of Vistoli cycles descends. -/
noncomputable def vistoliChow_toSchemeChow (hG : G.Good) (i : ℤ) :
    G.vistoliChow i →ₗ[ℚ]
      (RationalEquivalenceSystem.canonical (X := G.base) (dimension := G.baseDim)
        (i := i)).ChowGroup :=
  (G.vistoliRelations i).liftQ
    ((RationalEquivalenceSystem.canonical (X := G.base) (dimension := G.baseDim)
      (i := i)).quotientMap ∘ₗ (G.cycles i).subtype) (by
      intro z hz
      have hz' := vistoliRelations_le_relations hG hz
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact hz')

/-- `vistoliChow_toSchemeChow` sends the Vistoli class of a cycle to its rational-equivalence
class on the atlas. -/
@[simp]
theorem vistoliChow_toSchemeChow_mk (hG : G.Good) (i : ℤ) (z : G.cycles i) :
    vistoliChow_toSchemeChow hG i (G.vistoliQuotientMap i z) =
      (RationalEquivalenceSystem.canonical (X := G.base) (dimension := G.baseDim)
        (i := i)).quotientMap z :=
  rfl

variable {k : Type u} [Field k]

/-- **The Vistoli degree** of a dimension-zero class on an étale presentation groupoid whose atlas
is proper over a field `k` and which has degree `d` (`IsOfDegree`): the degree of its image in
`A_0` of the atlas, divided by `d`.  The hypothesis `_hd` only certifies the normalisation
constant, which is unique for the nonempty atlas (`IsOfDegree.unique`); it is not otherwise
used in the definition. -/
noncomputable def vistoliDegree (hG : G.Good) (sG : G.base ⟶ Spec (CommRingCat.of k))
    [IsProper sG] [CompactSpace G.base] [Nonempty G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.arrows]
    [_root_.AlgebraicGeometry.QuasiCompact G.src] {d : ℚ} (_hd : G.IsOfDegree d) :
    G.vistoliChow 0 →ₗ[ℚ] ℚ :=
  (1 / d) • (degreeChow sG G.baseDim ∘ₗ vistoliChow_toSchemeChow hG 0)

/-- The Vistoli degree of the class of a cycle `z` is `(1 / d) * ∑ₓ zₓ [κ(x) : k]`. -/
theorem vistoliDegree_mk (hG : G.Good) (sG : G.base ⟶ Spec (CommRingCat.of k))
    [IsProper sG] [CompactSpace G.base] [Nonempty G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.arrows]
    [_root_.AlgebraicGeometry.QuasiCompact G.src] {d : ℚ} (hd : G.IsOfDegree d)
    (z : G.cycles 0) :
    vistoliDegree hG sG hd (G.vistoliQuotientMap 0 z) =
      1 / d * ZeroCycleDegree.degree sG G.baseDim z :=
  rfl

end EtalePresentationGroupoid

/-! ## The degree of `Γ_k ⇉ Spec k` and of the class of the point -/

namespace ClassifyingStackChow

variable (k : Type u) [Field k] (Γ : Type u) [Finite Γ]

variable {k Γ} in
/-- Every point of `Spec (Γ → k)` is the image of the point of `Spec k` under the coordinate
inclusion `Spec k ⟶ Spec (Γ → k)` at some `γ`. -/
theorem exists_eq_specMap_eval (x : constantArrows k Γ) :
    ∃ (γ : Γ) (p : Spec (CommRingCat.of k)),
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Γ ↦ k) γ))).base p = x := by
  obtain ⟨⟨γ, p⟩, hp⟩ := (PrimeSpectrum.sigmaToPi_bijective (fun _ : Γ ↦ k)).2 x
  exact ⟨γ, p, hp⟩

variable {k Γ} in
/-- The structure map `Spec (Γ → k) ⟶ Spec k` has residue degree one at every point. -/
theorem residueDegree_constantProjection (x : constantArrows k Γ) :
    (constantProjection k Γ).residueDegree x = 1 := by
  obtain ⟨γ, p, rfl⟩ := exists_eq_specMap_eval x
  have h := residueDegree_comp
    (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Γ ↦ k) γ))) (constantProjection k Γ) p
  have hcomp : Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Γ ↦ k) γ)) ≫
      constantProjection k Γ = 𝟙 _ := by
    rw [constantProjection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Pi.evalRingHom (fun _ : Γ ↦ k) γ).comp (algebraMap k (Γ → k)) = RingHom.id k := by
      ext; rfl
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  rw [hcomp, Scheme.Hom.residueDegree_id,
    ProperPushforwardDivisor.residueDegree_eq_one_of_isOpenImmersion
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Γ ↦ k) γ))), mul_one] at h
  exact h.symm

/-- `Spec (Γ → k)` has exactly `|Γ|` points. -/
theorem natCard_constantArrows : Nat.card (constantArrows k Γ) = Nat.card Γ := by
  cases nonempty_fintype Γ
  change Nat.card (PrimeSpectrum (Γ → k)) = Nat.card Γ
  rw [← Nat.card_congr (PrimeSpectrum.sigmaToPiHomeo (fun _ : Γ ↦ k)).toEquiv, Nat.card_sigma]
  simp

/-- **`Γ_k ⇉ Spec k` has degree `|Γ|`**: the source leg pushes `[Γ_k] = ∑_γ [γ]` to
`|Γ| [Spec k]` (all residue degrees are one). -/
theorem constantGroupoid_isOfDegree :
    (constantGroupoid k Γ).IsOfDegree (Nat.card Γ) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  have hy : IsMax y := fun z _ ↦ (Subsingleton.elim z y).le
  have hfin : Finite (constantArrows k Γ) :=
    Finite.of_equiv _ (PrimeSpectrum.sigmaToPiHomeo (fun _ : Γ ↦ k)).toEquiv
  let _ := Fintype.ofFinite (constantArrows k Γ)
  have hpre : (constantProjection k Γ).base ⁻¹' {y} = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
  have hterm : ∀ x : constantArrows k Γ, (constantArrows k Γ).fundamentalCycle x *
      ((AlgebraicCycle.mapCoeff (constantProjection k Γ) ⇑(constantArrowsDim k Γ)
        ⇑(DimensionFunction.specField k) x : ℕ) : ℚ) = 1 := by
    intro x
    rw [(constantArrows k Γ).fundamentalCycle_apply_of_isMax_of_isReduced x
      (fun z hz ↦ (constantArrows_eq_of_le hz).ge)]
    simp [AlgebraicCycle.mapCoeff, residueDegree_constantProjection, constantArrowsDim]
  change ∑ᶠ x ∈ (constantProjection k Γ).base ⁻¹' {y}, _ = (Nat.card Γ : ℚ) *
    (Spec (CommRingCat.of k)).fundamentalCycle y
  rw [hpre, finsum_mem_univ,
    (Spec (CommRingCat.of k)).fundamentalCycle_apply_of_isMax_of_isReduced y hy]
  refine (finsum_congr hterm).trans ?_
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    natCard_constantArrows]
  simp

variable {k} in
/-- The identity of `Spec k`, viewed as a structure morphism, has residue degree one. -/
theorem residueDegree_id_specField (x : Spec (CommRingCat.of k)) :
    ZeroCycleDegree.residueDegree (𝟙 (Spec (CommRingCat.of k))) x = 1 := by
  have hspec : FiniteTypeDimension.specAlgebraMap (𝟙 (Spec (CommRingCat.of k))) =
      RingHom.id k := by
    ext c
    simp [FiniteTypeDimension.specAlgebraMap]
  have hbot : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  have hmax : x.asIdeal.IsMaximal := hbot ▸ Ideal.bot_isMaximal
  unfold ZeroCycleDegree.residueDegree
  let _ := (FiniteTypeDimension.residueMap (𝟙 (Spec (CommRingCat.of k))) x).toAlgebra
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  refine ⟨RingHom.injective _, fun b ↦ ?_⟩
  let e := Scheme.Spec.residueFieldIso (CommRingCat.of k) x
  obtain ⟨a, ha⟩ := Ideal.algebraMap_residueField_surjective x.asIdeal (e.hom b)
  refine ⟨a, ?_⟩
  apply e.commRingCatIsoToRingEquiv.injective
  change e.hom (FiniteTypeDimension.residueMap (𝟙 (Spec (CommRingCat.of k))) x a) = e.hom b
  rw [FiniteTypeDimension.residueFieldIso_residueMap, hspec, ← ha]
  rfl

/-- **The fundamental class** of `Γ_k ⇉ Spec k` in `A_0`: the Vistoli class of the cycle `[Spec k]`
(coefficient one at the unique point). -/
noncomputable def fundamentalClass : (constantGroupoid k Γ).vistoliChow 0 :=
  (constantGroupoid k Γ).vistoliQuotientMap 0
    ⟨PointChow.fundamentalCycle k, by
      rw [EtalePresentationGroupoid.cycles_eq_top_of_src_eq_tgt _ _ rfl]; trivial⟩

/-- Under `vistoliChow_zero_equiv` the fundamental class corresponds to `1`. -/
theorem vistoliChow_zero_equiv_fundamentalClass :
    vistoliChow_zero_equiv k Γ (fundamentalClass k Γ) = 1 :=
  PointChow.fundamentalCycle_apply k

/-- **The Vistoli degree of the point of `Γ_k ⇉ Spec k` is `1 / |Γ|`** (structure morphism the
identity of `Spec k`, normalisation `constantGroupoid_isOfDegree`).  `Γ` is assumed nonempty (as
for a group), so that `|Γ| ≠ 0`; see `natCard_mul_vistoliDegree_fundamentalClass`. -/
theorem vistoliDegree_fundamentalClass [Nonempty Γ] :
    EtalePresentationGroupoid.vistoliDegree (constantGroupoid_good k Γ)
        (𝟙 (Spec (CommRingCat.of k))) (constantGroupoid_isOfDegree k Γ)
        (fundamentalClass k Γ) = 1 / Nat.card Γ := by
  rw [fundamentalClass, EtalePresentationGroupoid.vistoliDegree_mk,
    ZeroCycleDegree.degree_apply,
    finsum_eq_single _ default (fun x hx ↦ absurd (Subsingleton.elim x default) hx)]
  change 1 / (Nat.card Γ : ℚ) * ((PointChow.fundamentalCycle k).1 default * _) = _
  rw [PointChow.fundamentalCycle_apply, residueDegree_id_specField]
  simp

/-- **`|Γ| · deg [pt] = 1`** for nonempty finite `Γ`: the Vistoli degree of the point is the
inverse of the (nonzero) order of `Γ`. -/
theorem natCard_mul_vistoliDegree_fundamentalClass [Nonempty Γ] :
    (Nat.card Γ : ℚ) * EtalePresentationGroupoid.vistoliDegree (constantGroupoid_good k Γ)
        (𝟙 (Spec (CommRingCat.of k))) (constantGroupoid_isOfDegree k Γ)
        (fundamentalClass k Γ) = 1 := by
  rw [vistoliDegree_fundamentalClass]
  have : (Nat.card Γ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  field_simp

end ClassifyingStackChow

end GromovWitten.AlgebraicGeometry.IntersectionTheory
