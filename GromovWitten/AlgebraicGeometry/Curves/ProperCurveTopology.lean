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
import GromovWitten.AlgebraicGeometry.ProjectiveLine
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
* `GromovWitten.AlgebraicGeometry.ProjectiveLine.instIsSeparatedStructureMap`: the projective
  line `ℙ¹_k` is separated over `k`.
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

section Separated

/-! ## Separatedness of a scheme glued from two affine charts

The diagonal of a morphism `w : Z ⟶ Spec R` is a closed immersion as soon as `Z` has an affine
open cover `Spec Sᵢ ⟶ Z` with affine pairwise intersections over which the multiplication maps
`Sᵢ ⊗[R] Sⱼ → Γ(Spec Sᵢ ∩ Spec Sⱼ)` are surjective.  The next lemma is the local input of this
criterion (the pieces of `IsZariskiLocalAtTarget.of_openCover` applied to the cover of
`Z ×_{Spec R} Z` by the products `Spec Sᵢ ×_{Spec R} Spec Sⱼ`), in the form in which the goals
of that reduction actually appear.  It is the affine-diagonal argument used by Mathlib for
`Proj`, phrased for an arbitrary gluing. -/

/-- **The affine-diagonal criterion, one piece.**  Let `u : Spec S ⟶ Z` and `v : Spec T ⟶ Z` be
two members of an open cover of a scheme `Z` over `Spec R`, and suppose that their intersection is
`Spec A`, i.e. that the square with sides `Spec.map φ`, `Spec.map ψ`, `u`, `v` is cartesian.  If
the induced ring map `F : S ⊗[R] T → A` is surjective, then the restriction of the diagonal of
`w : Z ⟶ Spec R` to `Spec S ×_{Spec R} Spec T` is a closed immersion. -/
lemma isClosedImmersion_pullback_snd_diagonal
    {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R T] {Z : Scheme.{u}} {w : Z ⟶ Spec (CommRingCat.of R)}
    {u : Spec (CommRingCat.of S) ⟶ Z} {v : Spec (CommRingCat.of T) ⟶ Z}
    (hu : u ≫ w = Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (hv : v ≫ w = Spec.map (CommRingCat.ofHom (algebraMap R T)))
    {φ : S →+* A} {ψ : T →+* A}
    (hsq : IsPullback (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom ψ)) u v)
    (F : S ⊗[R] T →+* A) (hF : Function.Surjective F)
    (hFl : F.comp Algebra.TensorProduct.includeLeftRingHom = φ)
    (hFr : F.comp (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom = ψ) :
    IsClosedImmersion (pullback.snd (pullback.diagonal w)
      (pullback.map (u ≫ w) (v ≫ w) w w u v (𝟙 _)
        (Category.comp_id _) (Category.comp_id _))) := by
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (f := (pullbackDiagonalMapIdIso u v w).inv) _).mp ?_
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    hsq.isoPullback.hom]
  set ι : Spec (CommRingCat.of (S ⊗[R] T)) ⟶ pullback (u ≫ w) (v ≫ w) :=
    (pullbackSpecIso R S T).inv ≫ (pullback.congrHom hu hv).inv with hιdef
  have hι1 : ι ≫ pullback.fst (u ≫ w) (v ≫ w) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    rw [hιdef, Category.assoc, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id,
      pullbackSpecIso_inv_fst]
  have hι2 : ι ≫ pullback.snd (u ≫ w) (v ≫ w) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom) := by
    rw [hιdef, Category.assoc, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id,
      pullbackSpecIso_inv_snd]
    rfl
  have hIso : IsIso ι := by rw [hιdef]; infer_instance
  have key : hsq.isoPullback.hom ≫ (pullbackDiagonalMapIdIso u v w).inv ≫
      pullback.snd (pullback.diagonal w) (pullback.map (u ≫ w) (v ≫ w) w w u v (𝟙 _)
        (Category.comp_id _) (Category.comp_id _)) =
      Spec.map (CommRingCat.ofHom F) ≫ ι := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hι1, pullbackDiagonalMapIdIso_inv_snd_fst, hsq.isoPullback_hom_fst, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hFl]
    · simp only [Category.assoc]
      rw [hι2, pullbackDiagonalMapIdIso_inv_snd_snd, hsq.isoPullback_hom_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hFr]
  rw [key]
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ ι).mpr
    (IsClosedImmersion.spec_of_surjective _ hF)

namespace ProjectiveLine

noncomputable section

variable (k : Type u) [Field k]

/-! ### The cover of `ℙ¹_k` by its two charts -/

/-- The two standard charts of `ℙ¹_k`, indexed by `Bool`. -/
abbrev chartMap : Bool → (chart k ⟶ scheme k)
  | false => chartZero k
  | true => chartOne k

/-- The open cover of `ℙ¹_k` by its two standard charts. -/
def chartCover : (scheme k).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun _ => chart k) (chartMap k)
    (fun x => by
      rcases mem_range_chart k x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy⟩
      · exact ⟨true, y, hy⟩)
    (fun b => by cases b <;> infer_instance)

/-- Both charts are morphisms of `k`-schemes. -/
lemma chartMap_comp_structureMap (b : Bool) :
    chartMap k b ≫ structureMap k =
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by
  cases b
  · exact chartZero_comp_structureMap k
  · exact chartOne_comp_structureMap k

/-! ### The intersection of the two charts is the overlap -/

/-- A point of the first chart whose image in `ℙ¹_k` lies in the second chart lies in the
overlap.  In the gluing diagram the only morphisms into `some 0` and `some 1` come from `none`. -/
lemma mem_range_overlapToChartZero_of_mem_range_chartOne {y : chart k}
    (hy : (chartZero k).base y ∈ Set.range (chartOne k).base) :
    y ∈ Set.range (overlapToChartZero k).base := by
  obtain ⟨y', hy'⟩ := hy
  obtain ⟨l, fi, fj, z, _, hzj⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := diagram k)).mp hy'
  cases fj with
  | id X => cases fi
  | init b =>
    cases fi with
    | init a =>
      rw [← hzj, map_init_zero]
      exact ⟨z, rfl⟩

/-- A point of the second chart whose image in `ℙ¹_k` lies in the first chart lies in the
overlap. -/
lemma mem_range_overlapToChartOne_of_mem_range_chartZero {y : chart k}
    (hy : (chartOne k).base y ∈ Set.range (chartZero k).base) :
    y ∈ Set.range (overlapToChartOne k).base := by
  obtain ⟨y', hy'⟩ := hy
  obtain ⟨l, fi, fj, z, _, hzj⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := diagram k)).mp hy'
  cases fj with
  | id X => cases fi
  | init b =>
    cases fi with
    | init a =>
      rw [← hzj, map_init_one]
      exact ⟨z, rfl⟩

/-- The preimage of the second chart in the first one is the overlap. -/
lemma preimage_opensRange_chartOne :
    (chartZero k) ⁻¹ᵁ (chartOne k).opensRange = (overlapToChartZero k).opensRange := by
  ext y
  constructor
  · exact fun h => mem_range_overlapToChartZero_of_mem_range_chartOne k h
  · rintro ⟨z, rfl⟩
    refine ⟨(overlapToChartOne k).base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, overlapToChartOne_comp,
      overlapToChartZero_comp]

/-- The preimage of the first chart in the second one is the overlap. -/
lemma preimage_opensRange_chartZero :
    (chartOne k) ⁻¹ᵁ (chartZero k).opensRange = (overlapToChartOne k).opensRange := by
  ext y
  constructor
  · exact fun h => mem_range_overlapToChartOne_of_mem_range_chartZero k h
  · rintro ⟨z, rfl⟩
    refine ⟨(overlapToChartZero k).base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, overlapToChartZero_comp,
      overlapToChartOne_comp]

/-- **The fibre product of the two charts of `ℙ¹_k` over `ℙ¹_k` is the overlap
`Spec k[t, t⁻¹]`.** -/
lemma isPullback_chartZero_chartOne :
    IsPullback (overlapToChartZero k) (overlapToChartOne k) (chartZero k) (chartOne k) :=
  AlgebraicGeometry.IsOpenImmersion.isPullback (overlapToChartZero k) (overlapToChartOne k)
    (chartZero k) (chartOne k)
    (by rw [overlapToChartOne_comp, overlapToChartZero_comp])
    (preimage_opensRange_chartZero k)

/-- The mirror image of `isPullback_chartZero_chartOne`. -/
lemma isPullback_chartOne_chartZero :
    IsPullback (overlapToChartOne k) (overlapToChartZero k) (chartOne k) (chartZero k) :=
  AlgebraicGeometry.IsOpenImmersion.isPullback (overlapToChartOne k) (overlapToChartZero k)
    (chartOne k) (chartZero k)
    (by rw [overlapToChartZero_comp, overlapToChartOne_comp])
    (preimage_opensRange_chartOne k)

/-- The fibre product of a chart with itself over `ℙ¹_k` is that chart, since the charts are
open immersions, hence monomorphisms. -/
lemma spec_map_ofHom_id : Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k))) =
    𝟙 (chart k) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]

/-- The fibre product of a chart of `ℙ¹_k` with itself is that chart. -/
lemma isPullback_chart_self (b : Bool) :
    IsPullback (Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k))))
      (Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k)))) (chartMap k b)
      (chartMap k b) := by
  rw [spec_map_ofHom_id]
  cases b
  · exact IsKernelPair.id_of_mono (chartZero k)
  · exact IsKernelPair.id_of_mono (chartOne k)

/-! ### The three surjective multiplication maps -/

/-- The transition map `k[s] → k[t,t⁻¹]` is a map of `k`-algebras. -/
lemma flipHom_algebraMap (a : k) :
    flipHom k (algebraMap k (Polynomial k) a) = algebraMap k (overlapRing k) a := by
  rw [IsScalarTower.algebraMap_apply k (Polynomial k) (overlapRing k), Polynomial.algebraMap_eq,
    flipHom_C]

/-- The transition map `k[s] → k[t,t⁻¹]`, `s ↦ t⁻¹`, as a `k`-algebra homomorphism. -/
def flipAlgHom : Polynomial k →ₐ[k] overlapRing k :=
  { flipHom k with commutes' := flipHom_algebraMap k }

/-- `flipAlgHom` is `flipHom`. -/
@[simp] lemma flipAlgHom_apply (p : Polynomial k) : flipAlgHom k p = flipHom k p := rfl

/-- Every element of `k[t,t⁻¹]` is of the form `p · (t⁻¹)ⁿ` with `p ∈ k[t]`. -/
lemma exists_eq_algebraMap_mul_tInv_pow (z : overlapRing k) :
    ∃ (p : Polynomial k) (n : ℕ),
      z = algebraMap (Polynomial k) (overlapRing k) p * (tInv k) ^ n := by
  obtain ⟨p, m, hm⟩ := IsLocalization.exists_mk'_eq (M := Submonoid.powers
    (Polynomial.X : Polynomial k)) (S := overlapRing k) z
  obtain ⟨n, hn⟩ := m.2
  have hn' : (m : Polynomial k) = (Polynomial.X : Polynomial k) ^ n := hn.symm
  refine ⟨p, n, ?_⟩
  have h1 : algebraMap (Polynomial k) (overlapRing k) ((Polynomial.X : Polynomial k) ^ n) *
      (tInv k) ^ n = 1 := by
    rw [map_pow, ← mul_pow, algebraMap_X_mul_tInv, one_pow]
  calc z = IsLocalization.mk' (overlapRing k) p m := hm.symm
    _ = IsLocalization.mk' (overlapRing k) p m *
        (algebraMap (Polynomial k) (overlapRing k) ((Polynomial.X : Polynomial k) ^ n) *
          (tInv k) ^ n) := by rw [h1, mul_one]
    _ = (algebraMap (Polynomial k) (overlapRing k) m *
        IsLocalization.mk' (overlapRing k) p m) * (tInv k) ^ n := by rw [hn']; ring
    _ = algebraMap (Polynomial k) (overlapRing k) p * (tInv k) ^ n := by
        rw [IsLocalization.mk'_spec']

/-- The multiplication map `k[t] ⊗_k k[t] → k[t]`, the comultiplication of the diagonal of a
single chart. -/
def diagHom : Polynomial k ⊗[k] Polynomial k →+* Polynomial k :=
  (Algebra.TensorProduct.lift (AlgHom.id k (Polynomial k)) (AlgHom.id k (Polynomial k))
    (fun _ _ => Commute.all _ _)).toRingHom

/-- The map `k[t] ⊗_k k[s] → k[t,t⁻¹]` given by `t ↦ t`, `s ↦ t⁻¹`. -/
def overlapHomLeft : Polynomial k ⊗[k] Polynomial k →+* overlapRing k :=
  (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k (Polynomial k) (overlapRing k))
    (flipAlgHom k) (fun _ _ => Commute.all _ _)).toRingHom

/-- The map `k[s] ⊗_k k[t] → k[t,t⁻¹]` given by `s ↦ t⁻¹`, `t ↦ t`. -/
def overlapHomRight : Polynomial k ⊗[k] Polynomial k →+* overlapRing k :=
  (Algebra.TensorProduct.lift (flipAlgHom k)
    (IsScalarTower.toAlgHom k (Polynomial k) (overlapRing k))
    (fun _ _ => Commute.all _ _)).toRingHom

/-- The multiplication map of a chart with itself is surjective. -/
lemma diagHom_surjective : Function.Surjective (diagHom k) :=
  fun a => ⟨a ⊗ₜ 1, by simp [diagHom]⟩

/-- `k[t,t⁻¹]` is generated over `k` by `t` and `t⁻¹`. -/
lemma overlapHomLeft_surjective : Function.Surjective (overlapHomLeft k) := by
  intro z
  obtain ⟨p, n, hz⟩ := exists_eq_algebraMap_mul_tInv_pow k z
  refine ⟨p ⊗ₜ ((Polynomial.X : Polynomial k) ^ n), ?_⟩
  rw [hz, overlapHomLeft]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
    IsScalarTower.coe_toAlgHom', flipAlgHom_apply, map_pow, flipHom_X]

/-- The mirror image of `overlapHomLeft_surjective`. -/
lemma overlapHomRight_surjective : Function.Surjective (overlapHomRight k) := by
  intro z
  obtain ⟨p, n, hz⟩ := exists_eq_algebraMap_mul_tInv_pow k z
  refine ⟨((Polynomial.X : Polynomial k) ^ n) ⊗ₜ p, ?_⟩
  rw [hz, overlapHomRight]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
    IsScalarTower.coe_toAlgHom', flipAlgHom_apply, map_pow, flipHom_X]
  rw [mul_comm]

/-- `diagHom` restricted to the left factor is the identity. -/
lemma diagHom_comp_includeLeft :
    (diagHom k).comp Algebra.TensorProduct.includeLeftRingHom = RingHom.id (Polynomial k) :=
  RingHom.ext fun p => by simp [diagHom]

/-- `diagHom` restricted to the right factor is the identity. -/
lemma diagHom_comp_includeRight :
    (diagHom k).comp (Algebra.TensorProduct.includeRight :
      Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k).toRingHom =
      RingHom.id (Polynomial k) :=
  RingHom.ext fun p => by simp [diagHom]

/-- `overlapHomLeft` restricted to the left factor is the localisation map. -/
lemma overlapHomLeft_comp_includeLeft :
    (overlapHomLeft k).comp Algebra.TensorProduct.includeLeftRingHom =
      algebraMap (Polynomial k) (overlapRing k) :=
  RingHom.ext fun p => by simp [overlapHomLeft]

/-- `overlapHomLeft` restricted to the right factor is the transition map. -/
lemma overlapHomLeft_comp_includeRight :
    (overlapHomLeft k).comp (Algebra.TensorProduct.includeRight :
      Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k).toRingHom = flipHom k :=
  RingHom.ext fun p => by simp [overlapHomLeft]

/-- `overlapHomRight` restricted to the left factor is the transition map. -/
lemma overlapHomRight_comp_includeLeft :
    (overlapHomRight k).comp Algebra.TensorProduct.includeLeftRingHom = flipHom k :=
  RingHom.ext fun p => by simp [overlapHomRight]

/-- `overlapHomRight` restricted to the right factor is the localisation map. -/
lemma overlapHomRight_comp_includeRight :
    (overlapHomRight k).comp (Algebra.TensorProduct.includeRight :
      Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k).toRingHom =
      algebraMap (Polynomial k) (overlapRing k) :=
  RingHom.ext fun p => by simp [overlapHomRight]

/-- **The projective line is separated over its base field.**  The diagonal of
`ℙ¹_k ⟶ Spec k` is a closed immersion because on each of the four products of charts the
comparison map of coordinate rings — `k[t] ⊗_k k[t] → k[t]` on the two diagonal pieces and
`k[t] ⊗_k k[s] → k[t,t⁻¹]`, `s ↦ t⁻¹`, on the two off-diagonal ones — is surjective. -/
instance instIsSeparatedStructureMap : IsSeparated (structureMap k) := by
  refine ⟨AlgebraicGeometry.IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeftRight (chartCover k) (chartCover k) _ _) ?_⟩
  rintro ⟨i, j⟩
  cases i <;> cases j
  · exact isClosedImmersion_pullback_snd_diagonal (chartMap_comp_structureMap k false)
      (chartMap_comp_structureMap k false) (isPullback_chart_self k false) (diagHom k)
      (diagHom_surjective k) (diagHom_comp_includeLeft k) (diagHom_comp_includeRight k)
  · exact isClosedImmersion_pullback_snd_diagonal (chartMap_comp_structureMap k false)
      (chartMap_comp_structureMap k true) (isPullback_chartZero_chartOne k) (overlapHomLeft k)
      (overlapHomLeft_surjective k) (overlapHomLeft_comp_includeLeft k)
      (overlapHomLeft_comp_includeRight k)
  · exact isClosedImmersion_pullback_snd_diagonal (chartMap_comp_structureMap k true)
      (chartMap_comp_structureMap k false) (isPullback_chartOne_chartZero k) (overlapHomRight k)
      (overlapHomRight_surjective k) (overlapHomRight_comp_includeLeft k)
      (overlapHomRight_comp_includeRight k)
  · exact isClosedImmersion_pullback_snd_diagonal (chartMap_comp_structureMap k true)
      (chartMap_comp_structureMap k true) (isPullback_chart_self k true) (diagHom k)
      (diagHom_surjective k) (diagHom_comp_includeLeft k) (diagHom_comp_includeRight k)

end

end ProjectiveLine

end Separated

end GromovWitten.AlgebraicGeometry
