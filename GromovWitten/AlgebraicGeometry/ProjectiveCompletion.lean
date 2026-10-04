/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.RelativeProj
import GromovWitten.AlgebraicGeometry.RelativeSpec
import GromovWitten.Algebra.PolynomialHomogenisation
import GromovWitten.AlgebraicGeometry.GradedVectorBundle
import GromovWitten.AlgebraicGeometry.ProjClosedImmersion

/-!
# The projective completion of a vector bundle

For a quasi-coherent graded algebra `𝒜` on a scheme `X` (`GradedAlgebraData`), the
homogenisation `𝒜[t]` (polynomials in `t` with `deg t = 1`, from
`GromovWitten.Algebra.PolynomialHomogenisation`) is again quasi-coherent graded algebra data, and
`Proj_X 𝒜[t]` is the projective completion.  For a graded vector bundle `E = Spec_X 𝒜`
(`GradedBundleData`) this is `P(E ⊕ 1)`: it is proper over `X`, contains `P(E) = Proj_X 𝒜` as the
closed locus `t = 0`, and contains `E` as the open complement `t ≠ 0`.

Along the way we develop functoriality of the relative `Proj` in the graded algebra data
(`RelativeProj.Hom`) and a gluing criterion for open immersions from a relative `Spec` into a
relative `Proj` whose affine pieces are basic opens `D₊(t_U)` (`RelativeProj.AwayChartData`).

## Main results

* `RelativeProj.Hom`, `RelativeProj.Hom.map`: a natural family of graded algebra maps
  `𝒜 U → ℬ U` (satisfying the irrelevant-ideal condition of `Proj.map`) induces
  `Proj_X ℬ → Proj_X 𝒜` over `X` (`Hom.map_toBase`), restricting to `Proj.map` over every affine
  open (`Hom.affineι_map`, `Hom.isPullback_map`); it is a closed immersion if all components are
  surjective (`Hom.map_isClosedImmersion`).
* `RelativeProj.AwayChartData`, `AwayChartData.map`: compatible identifications
  `(𝒢 U)_(t_U) ≅ 𝒜' U` with `t_U` of degree one glue to an open immersion
  `Spec_X 𝒜' → Proj_X 𝒢` over `X` (`AwayChartData.isOpenImmersion_map`,
  `AwayChartData.map_toBase`), whose image is the complement of the image of a morphism of
  relative `Proj`s as soon as this holds over every affine open
  (`AwayChartData.range_map_eq_compl`).
* `range_projMap_eq_compl_basicOpen`: the image of `Proj.map f` for a surjective graded map `f`
  with kernel `(t)` is the complement of `D₊(t)`.
* `GradedAlgebraData.homogenisation`, `GradedAlgebraData.projCompletionToBase_isProper`,
  `GradedAlgebraData.infinity` (a closed immersion), `GradedAlgebraData.openEmbedding` (an open
  immersion), `GradedAlgebraData.range_openEmbedding`.
* `GradedBundleData.projectiveCompletion`, `GradedBundleData.completionToBase` (proper),
  `GradedBundleData.infinityDivisor : P(E) ⟶ P(E ⊕ 1)` (a closed immersion over `X`),
  `GradedBundleData.bundleOpenEmbedding : E ⟶ P(E ⊕ 1)` (an open immersion over `X`), and
  `GradedBundleData.range_bundleOpenEmbedding`: the image of `E` is the complement of the image
  of `P(E)`.
* `GradedBundleData.chartProjIso`, `GradedBundleData.isPullback_chartProjIso`: over a
  trivialising chart `U`, `P(E ⊕ 1)` restricts to `Proj Γ(U)[x_i : i ∈ Option ι]`.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace HomogeneousLocalization

namespace GromovWitten.AlgebraicGeometry

open ProjBaseChange GlobalBlowup ReesBlowupOfEq

universe u

noncomputable section

/-! ### Generic lemmas on `Proj.map` -/

section ProjLemmas

variable {A S T : Type u} [CommRing A] [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
  {𝒜 : ℕ → Submodule A S} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule A T} [GradedAlgebra ℬ]

/-- `Away.map` sends the image of a degree-zero element to the image of its image. -/
theorem Away.map_fromZeroRingHom (f : 𝒜 →+*ᵍ ℬ) (s : S) (z : 𝒜 0) :
    Away.map f s (fromZeroRingHom 𝒜 _ z) = fromZeroRingHom ℬ _ ⟨f z, f.map_mem z.2⟩ := by
  apply val_injective
  change (map f _ (HomogeneousLocalization.mk ⟨0, z, 1, one_mem _⟩)).val =
    (HomogeneousLocalization.mk ⟨0, _, 1, one_mem _⟩).val
  rw [map_mk, val_mk, val_mk]
  congr 1
  exact Subtype.ext (map_one _)

set_option backward.isDefEq.respectTransparency false in
/-- A graded ring map compatible with the structure maps from the common base ring `A` commutes
with the structure morphisms of the `Proj`s to `Spec A`. -/
theorem projMap_projection (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜))
    (hcomm : ∀ a : A, f (algebraMap A S a) = algebraMap A T a) :
    Proj.map f hf ≫ projection 𝒜 = projection ℬ := by
  refine (Proj.mapAffineOpenCover _ hf).openCover.hom_ext _ _ ?_
  rintro ⟨⟨d, hd⟩, s, hs⟩
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [Proj.awayι_comp_map_assoc f hf hd s hs, projection, projection, Proj.awayι_toSpecZero_assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  change Away.map f s (fromZeroRingHom 𝒜 _ (algebraMap A (𝒜 0) a)) =
    fromZeroRingHom ℬ _ (algebraMap A (ℬ 0) a)
  rw [Away.map_fromZeroRingHom]
  congr 1
  exact Subtype.ext (hcomm a)

end ProjLemmas

section ProjLemmasEq

variable {A B S T : Type u} [CommRing A] [CommRing B] [CommRing S] [CommRing T] [Algebra A S]
  [Algebra B T] {𝒜 : ℕ → Submodule A S} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule B T}
  [GradedAlgebra ℬ]

variable {d : ℕ} (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜))

/-- The homogeneous localisation map at an element `s` and a chosen element `s'` equal to
`f s`. -/
abbrev awayMapOfEq (s : S) (s' : T) (hs' : f s = s') : Away 𝒜 s →+* Away ℬ s' :=
  HomogeneousLocalization.map f (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [hs']⟩)

/-- `Proj.awayι_comp_map` with the image of the element replaced by a propositionally equal
element. -/
theorem awayι_comp_projMap_of_eq (hd : 0 < d) (s : S) (hs : s ∈ 𝒜 d) (s' : T) (hs' : f s = s')
    (hs'' : s' ∈ ℬ d) :
    Proj.awayι ℬ s' hs'' hd ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom (awayMapOfEq f s s' hs')) ≫ Proj.awayι 𝒜 s hs hd := by
  subst hs'
  exact Proj.awayι_comp_map f hf hd s hs

/-- `awayMapOfEq` on a fraction. -/
theorem awayMapOfEq_mk (s : S) (s' : T) (hs' : f s = s') (hs : s ∈ 𝒜 d) (hs'' : s' ∈ ℬ d)
    (n : ℕ) (a : S) (ha : a ∈ 𝒜 (n • d)) :
    awayMapOfEq f s s' hs' (Away.mk 𝒜 hs n a ha) = Away.mk ℬ hs'' n (f a) (f.map_mem ha) := by
  subst hs'
  exact Away.map_mk f s hs n a ha

end ProjLemmasEq

section ProjRange

variable {A B : Type u} [CommRing A] [CommRing B] {σ τ : Type u} [SetLike σ A]
  [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ]

/-- The image of `Proj ℬ → Proj 𝒜` for a surjective graded ring map `f` whose kernel is the
ideal generated by `t` is the closed complement `V₊(t)` of the basic open `D₊(t)`. -/
theorem range_projMap_eq_compl_basicOpen (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜))
    (hsurj : Function.Surjective f) (t : A) (ht : f t = 0)
    (hker : RingHom.ker f.toRingHom ≤ Ideal.span {t}) :
    Set.range (Proj.map f hf) = ((Proj.basicOpen 𝒜 t : (Proj 𝒜).Opens) : Set (Proj 𝒜))ᶜ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ hy
    rw [SetLike.mem_coe, Proj.mem_basicOpen] at hy
    apply hy
    change f t ∈ y.asHomogeneousIdeal
    rw [ht]
    exact zero_mem _
  · intro hx
    have htx : t ∈ x.asHomogeneousIdeal := by
      simpa only [Set.mem_compl_iff, SetLike.mem_coe, Proj.mem_basicOpen, not_not] using hx
    have hk : RingHom.ker f.toRingHom ≤ x.asHomogeneousIdeal.toIdeal :=
      hker.trans (Ideal.span_le.mpr (by simpa using htx))
    have : x.asHomogeneousIdeal.toIdeal.IsPrime := ProjectiveSpectrum.isPrime x
    have hprime : (x.asHomogeneousIdeal.map f).toIdeal.IsPrime :=
      Ideal.map_isPrime_of_surjective (f := f.toRingHom) hsurj hk
    refine ⟨⟨x.asHomogeneousIdeal.map f, hprime, fun hle ↦ x.not_irrelevant_le ?_⟩, ?_⟩
    · rw [HomogeneousIdeal.irrelevant_le]
      intro i hi a ha
      have hfa : f a ∈ (x.asHomogeneousIdeal.map f).toIdeal :=
        hle (HomogeneousIdeal.mem_irrelevant_of_mem ℬ hi (f.map_mem ha))
      obtain ⟨b, hb, hfb⟩ :=
        Ideal.mem_image_of_mem_map_of_surjective f.toRingHom hsurj hfa
      have hab : a - b ∈ RingHom.ker f.toRingHom := by
        rw [RingHom.mem_ker, map_sub]
        exact sub_eq_zero.mpr hfb.symm
      have := x.asHomogeneousIdeal.toIdeal.add_mem (hk hab) hb
      rwa [sub_add_cancel] at this
    · change ProjectiveSpectrum.comap f hf _ = x
      ext1
      apply HomogeneousIdeal.toIdeal_injective
      change Ideal.comap f.toRingHom (Ideal.map f.toRingHom x.asHomogeneousIdeal.toIdeal) = _
      refine (Ideal.comap_map_of_surjective f.toRingHom hsurj _).trans (sup_eq_left.mpr ?_)
      exact le_trans (by rw [← RingHom.ker_eq_comap_bot]) hk

end ProjRange

section IrrelevantInverse

variable {A B : Type u} [CommRing A] [CommRing B] {σ τ : Type u} [SetLike σ A]
  [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ]

/-- A graded ring map with a graded right inverse satisfies the irrelevant-ideal condition of
`Proj.map`. -/
theorem irrelevant_le_map_of_rightInverse (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (h : ∀ b, f (g b) = b) :
    HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi b hb
  rw [← h b]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi (g.map_mem hb))

end IrrelevantInverse

/-! ### Local-at-target properties checked on a covering family of cartesian squares -/

/-- A property local on the target holds for a morphism if the target is covered by open
immersions whose base changes along the morphism satisfy the property. -/
theorem IsZariskiLocalAtTarget.of_isPullback_cover (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {Y Z : Scheme.{u}} (f : Y ⟶ Z) {I : Type u}
    {W V : I → Scheme.{u}} (ιZ : ∀ i, W i ⟶ Z) [∀ i, IsOpenImmersion (ιZ i)]
    (hcov : ⨆ i, (ιZ i).opensRange = ⊤) (ιY : ∀ i, V i ⟶ Y) (g : ∀ i, V i ⟶ W i)
    (h : ∀ i, IsPullback (g i) (ιY i) (ιZ i) f) (hP : ∀ i, P (g i)) : P f := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P)
    (fun i ↦ (ιZ i).opensRange) hcov).mpr fun i ↦ ?_
  rw [P.arrow_mk_iso_iff (morphismRestrictOpensRange f (ιZ i))]
  exact (P.arrow_mk_iso_iff (Arrow.isoMk (h i).flip.isoPullback
    (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id]
      exact (h i).flip.isoPullback_hom_snd))).mp (hP i)

/-- The range of the first projection of a cartesian square of schemes is the preimage of the
range of the opposite side. -/
theorem Scheme.range_fst_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  rw [← Scheme.Pullback.range_fst f g, ← h.isoPullback_hom_fst]
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨h.isoPullback.hom p, by rw [Scheme.Hom.comp_apply]⟩
  · rintro ⟨p, rfl⟩
    refine ⟨h.isoPullback.inv p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]

namespace RelativeProj

/- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
type of affine opens, as in `RelativeProj`. -/
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- An affine piece of a relative `Proj` lies over its affine open. -/
theorem affineι_toBase (𝒜 : GradedAlgebraData X) (U : X.affineOpens) :
    affineι X 𝒜 U ≫ toBase X 𝒜 =
      (projection (𝒜.grading U) ≫ (isAffineOpen X U).isoSpec.inv) ≫ U.1.ι :=
  (isPullback_affine X 𝒜 U).w.symm

/-! ### Morphisms of graded algebra data -/

/-- A morphism of quasi-coherent graded algebras `𝒜 → ℬ` on `X`: a family of graded algebra
maps `𝒜 U → ℬ U` over the section rings, natural in the affine open `U`, each satisfying the
irrelevant-ideal condition of `Proj.map`.  It induces `Proj_X ℬ → Proj_X 𝒜`.

Note that the argument order is opposite to `RelativeSpec.Hom`: there `Hom X 𝒜 ℬ` has components
`ℬ U → 𝒜 U` and induces `Spec_X 𝒜 ⟶ Spec_X ℬ`, whereas here `Hom 𝒜 ℬ` has components
`𝒜 U → ℬ U` (the direction of the ring maps) and induces `Proj_X ℬ ⟶ Proj_X 𝒜`. -/
structure Hom (𝒜 ℬ : GradedAlgebraData X) where
  /-- The components. -/
  app : ∀ U : X.affineOpens, 𝒜.grading U →+*ᵍ ℬ.grading U
  /-- The components are algebra maps over the section rings. -/
  commutes : ∀ (U : X.affineOpens) (a : Γ(X, U.1)),
    app U (algebraMap Γ(X, U.1) (𝒜.ring U) a) = algebraMap Γ(X, U.1) (ℬ.ring U) a
  /-- Naturality in the affine open. -/
  naturality : ∀ {U V : X.affineOpens} (h : U ≤ V),
    (app U).comp (𝒜.map h) = (ℬ.map h).comp (app V)
  /-- The irrelevant-ideal condition of `Proj.map`. -/
  irrelevant_le : ∀ U : X.affineOpens,
    HomogeneousIdeal.irrelevant (ℬ.grading U) ≤
      HomogeneousIdeal.map (app U) (HomogeneousIdeal.irrelevant (𝒜.grading U))

namespace Hom

variable {𝒜 ℬ : GradedAlgebraData X} (φ : Hom 𝒜 ℬ)

/-- The natural transformation of gluing functors induced by a morphism of graded algebra
data. -/
def gluingNatTrans : (gluingData X ℬ).functor ⟶ (gluingData X 𝒜).functor where
  app U := Proj.map (φ.app U) (φ.irrelevant_le U)
  naturality {U V} h := by
    change Proj.map (ℬ.map (leOfHom h)) _ ≫ Proj.map (φ.app V) (φ.irrelevant_le V) =
      Proj.map (φ.app U) (φ.irrelevant_le U) ≫ Proj.map (𝒜.map (leOfHom h)) _
    rw [← Proj.map_comp, ← Proj.map_comp, projMap_congr (φ.naturality (leOfHom h))]

/-- The morphism of relative `Proj`s induced by a morphism of graded algebra data. -/
def map : relativeProj X ℬ ⟶ relativeProj X 𝒜 := colimMap φ.gluingNatTrans

/-- On the affine pieces the induced morphism is `Proj.map`. -/
@[reassoc]
theorem affineι_map (U : X.affineOpens) :
    affineι X ℬ U ≫ φ.map = Proj.map (φ.app U) (φ.irrelevant_le U) ≫ affineι X 𝒜 U :=
  ι_colimMap φ.gluingNatTrans U

/-- The affine components lie over the section ring. -/
theorem projMap_app_projection (U : X.affineOpens) :
    Proj.map (φ.app U) (φ.irrelevant_le U) ≫ projection (𝒜.grading U) =
      projection (ℬ.grading U) :=
  projMap_projection _ _ (φ.commutes U)

/-- The induced morphism lies over `X`. -/
@[reassoc (attr := simp)]
theorem map_toBase : φ.map ≫ toBase X 𝒜 = toBase X ℬ := by
  apply colimit.hom_ext
  intro U
  change affineι X ℬ U ≫ φ.map ≫ toBase X 𝒜 = affineι X ℬ U ≫ toBase X ℬ
  rw [affineι_map_assoc, affineι_toBase, affineι_toBase,
    ← Category.assoc, ← Category.assoc, projMap_app_projection]

/-- Over every affine open, the induced morphism is the affine `Proj.map`. -/
theorem isPullback_map (U : X.affineOpens) :
    IsPullback (Proj.map (φ.app U) (φ.irrelevant_le U)) (affineι X ℬ U)
      (affineι X 𝒜 U) φ.map := by
  refine IsPullback.of_right ?_ (φ.affineι_map U).symm (isPullback_affine X 𝒜 U)
  rw [← Category.assoc, projMap_app_projection, map_toBase]
  exact isPullback_affine X ℬ U

/-- A property local on the target holds for the induced morphism as soon as it holds for all
the affine `Proj.map`s. -/
theorem property_map_of_forall (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ U : X.affineOpens, P (Proj.map (φ.app U) (φ.irrelevant_le U))) :
    P φ.map :=
  IsZariskiLocalAtTarget.of_isPullback_cover P φ.map (affineι X 𝒜)
    (iSup_opensRange_affineι X 𝒜) (affineι X ℬ) _ φ.isPullback_map h

/-- If all the affine `Proj.map`s are closed immersions, so is the induced morphism. -/
theorem map_isClosedImmersion_of_forall
    (h : ∀ U : X.affineOpens, IsClosedImmersion (Proj.map (φ.app U) (φ.irrelevant_le U))) :
    IsClosedImmersion φ.map :=
  φ.property_map_of_forall @IsClosedImmersion h

/-- A family of surjective graded algebra maps induces a closed immersion of relative `Proj`s. -/
theorem map_isClosedImmersion (h : ∀ U : X.affineOpens, Function.Surjective (φ.app U)) :
    IsClosedImmersion φ.map :=
  φ.map_isClosedImmersion_of_forall fun U ↦ isClosedImmersion_projMap _ (h U) _

end Hom

/-! ### Open immersions of a relative `Spec` onto basic opens `D₊(t)` -/

/-- Data identifying, over every affine open `U`, the algebra `𝒜 U` of a quasi-coherent algebra
with the degree-zero homogeneous localisation of `𝒢 U` at an element `t_U` of degree one,
compatibly with the structure maps and the transition maps (which send `t_V` to `t_U`). -/
structure AwayChartData (𝒜 : AlgebraData X) (𝒢 : GradedAlgebraData X) where
  /-- The degree-one element `t_U`. -/
  elem : ∀ U : X.affineOpens, 𝒢.ring U
  /-- `t_U` has degree one. -/
  elem_mem : ∀ U : X.affineOpens, elem U ∈ 𝒢.grading U 1
  /-- The transition maps send `t_V` to `t_U`. -/
  map_elem : ∀ {U V : X.affineOpens} (h : U ≤ V), 𝒢.map h (elem V) = elem U
  /-- The identification `(𝒢 U)_(t_U) ≅ 𝒜 U`. -/
  iso : ∀ U : X.affineOpens, Away (𝒢.grading U) (elem U) ≃+* 𝒜.ring U
  /-- The identification is compatible with the structure maps. -/
  iso_algebraMap : ∀ (U : X.affineOpens) (a : Γ(X, U.1)),
    iso U (fromZeroRingHom (𝒢.grading U) _ (algebraMap Γ(X, U.1) (𝒢.grading U 0) a)) =
      algebraMap Γ(X, U.1) (𝒜.ring U) a
  /-- The identification is compatible with the transition maps. -/
  naturality : ∀ {U V : X.affineOpens} (h : U ≤ V),
    (iso U).toRingHom.comp (awayMapOfEq (𝒢.map h) (elem V) (elem U) (map_elem h)) =
      (𝒜.map h).comp (iso V).toRingHom

namespace AwayChartData

variable {𝒜 : AlgebraData X} {𝒢 : GradedAlgebraData X} (D : AwayChartData 𝒜 𝒢)

/-- The chart `Spec (𝒜 U) ≅ D₊(t_U) ⊆ Proj (𝒢 U)`. -/
def chart (U : X.affineOpens) : Spec (.of (𝒜.ring U)) ⟶ Proj (𝒢.grading U) :=
  Spec.map (CommRingCat.ofHom (D.iso U).toRingHom) ≫
    Proj.awayι (𝒢.grading U) (D.elem U) (D.elem_mem U) one_pos

/-- The charts are open immersions. -/
instance isOpenImmersion_chart (U : X.affineOpens) : IsOpenImmersion (D.chart U) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (D.iso U).toRingHom)) := by
    rw [isIso_SpecMap_iff]
    exact (D.iso U).bijective
  unfold chart
  infer_instance

/-- The image of a chart is the basic open `D₊(t_U)`. -/
theorem range_chart (U : X.affineOpens) :
    Set.range (D.chart U) =
      (Proj.basicOpen (𝒢.grading U) (D.elem U) : Set (Proj (𝒢.grading U))) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (D.iso U).toRingHom)) := by
    rw [isIso_SpecMap_iff]
    exact (D.iso U).bijective
  change ((D.chart U).opensRange : Set (Proj (𝒢.grading U))) = _
  unfold chart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

/-- The charts are compatible with the transition maps. -/
theorem chart_comp_projMap {U V : X.affineOpens} (h : U ≤ V) :
    D.chart U ≫ Proj.map (𝒢.map h) (irrelevant_le X 𝒢 h) =
      Spec.map (CommRingCat.ofHom (𝒜.map h)) ≫ D.chart V := by
  rw [chart, chart, Category.assoc,
    awayι_comp_projMap_of_eq (𝒢.map h) _ one_pos (D.elem V) (D.elem_mem V) (D.elem U)
      (D.map_elem h) (D.elem_mem U), ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, D.naturality h]

/-- The charts lie over the section ring. -/
theorem chart_projection (U : X.affineOpens) :
    D.chart U ≫ projection (𝒢.grading U) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (𝒜.ring U))) := by
  rw [chart, projection, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  exact D.iso_algebraMap U a

/-- The charts form a cocone on the gluing functor of the relative `Spec`. -/
def cocone : Cocone (RelativeSpec.gluingData X 𝒜).functor where
  pt := relativeProj X 𝒢
  ι :=
    { app U := D.chart U ≫ affineι X 𝒢 U
      naturality {U V} h := by
        change Spec.map (CommRingCat.ofHom (𝒜.map (leOfHom h))) ≫ D.chart V ≫ affineι X 𝒢 V =
          (D.chart U ≫ affineι X 𝒢 U) ≫ 𝟙 _
        rw [Category.comp_id, affineι, affineι, ← colimit.w (gluingData X 𝒢).functor h,
          ← Category.assoc, ← Category.assoc]
        congr 1
        exact (D.chart_comp_projMap (leOfHom h)).symm }

/-- The induced morphism from the relative `Spec` to the relative `Proj`. -/
def map : RelativeSpec.relativeSpec X 𝒜 ⟶ relativeProj X 𝒢 :=
  colimit.desc _ D.cocone

/-- On the affine pieces the induced morphism is the chart. -/
@[reassoc]
theorem affineι_map (U : X.affineOpens) :
    RelativeSpec.affineι X 𝒜 U ≫ D.map = D.chart U ≫ affineι X 𝒢 U :=
  colimit.ι_desc _ _

/-- The induced morphism lies over `X`. -/
@[reassoc (attr := simp)]
theorem map_toBase : D.map ≫ toBase X 𝒢 = RelativeSpec.toBase X 𝒜 := by
  apply colimit.hom_ext
  intro U
  change RelativeSpec.affineι X 𝒜 U ≫ D.map ≫ toBase X 𝒢 =
    RelativeSpec.affineι X 𝒜 U ≫ RelativeSpec.toBase X 𝒜
  rw [affineι_map_assoc, affineι_toBase, RelativeSpec.affineι_toBase,
    ← Category.assoc, ← Category.assoc, chart_projection]

/-- Over every affine open, the induced morphism is the chart `Spec (𝒜 U) → Proj (𝒢 U)`. -/
theorem isPullback_map (U : X.affineOpens) :
    IsPullback (D.chart U) (RelativeSpec.affineι X 𝒜 U) (affineι X 𝒢 U) D.map := by
  refine IsPullback.of_right ?_ (D.affineι_map U).symm (isPullback_affine X 𝒢 U)
  rw [← Category.assoc, chart_projection, map_toBase]
  exact RelativeSpec.isPullback_affine X 𝒜 U

/-- The induced morphism is an open immersion. -/
instance isOpenImmersion_map : IsOpenImmersion D.map :=
  IsZariskiLocalAtTarget.of_isPullback_cover @IsOpenImmersion D.map (affineι X 𝒢)
    (iSup_opensRange_affineι X 𝒢) (RelativeSpec.affineι X 𝒜) _ D.isPullback_map
    fun U ↦ D.isOpenImmersion_chart U

/-- If, over every affine open, the chart `D₊(t_U)` is the complement of the image of the
affine `Proj.map` of a morphism of graded algebra data, then globally the image of the open
immersion of the relative `Spec` is the complement of the image of the induced morphism of
relative `Proj`s. -/
theorem range_map_eq_compl {ℬ : GradedAlgebraData X} (φ : Hom 𝒢 ℬ)
    (h : ∀ U : X.affineOpens,
      Set.range (D.chart U) = (Set.range (Proj.map (φ.app U) (φ.irrelevant_le U)))ᶜ) :
    Set.range D.map = (Set.range φ.map)ᶜ := by
  ext x
  have hx : x ∈ (⨆ U : X.affineOpens, (affineι X 𝒢 U).opensRange) := by
    rw [iSup_opensRange_affineι X 𝒢]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨y, rfl⟩ := hU
  have h1 := Scheme.range_fst_of_isPullback (D.isPullback_map U)
  have h2 := Scheme.range_fst_of_isPullback (φ.isPullback_map U)
  have e1 : y ∈ Set.range (D.chart U) ↔ affineι X 𝒢 U y ∈ Set.range D.map := by
    rw [h1]
    rfl
  have e2 : y ∈ Set.range (Proj.map (φ.app U) (φ.irrelevant_le U)) ↔
      affineι X 𝒢 U y ∈ Set.range φ.map := by
    rw [h2]
    rfl
  rw [Set.mem_compl_iff, ← e1, ← e2, h U, Set.mem_compl_iff]

end AwayChartData

end RelativeProj

/-! ### The homogenisation of a quasi-coherent graded algebra -/

namespace GradedAlgebraData

open GromovWitten.Algebra Polynomial RelativeProj

variable {X : Scheme.{u}} (𝒜 : GradedAlgebraData X)

/-- The homogenisation `𝒜[t]` of a quasi-coherent graded algebra: over an affine open `U` the
polynomial ring `(𝒜 U)[t]` graded by `deg t = 1`, with the transition maps `Polynomial.map`. -/
def homogenisation : GradedAlgebraData X where
  ring U := Polynomial (𝒜.ring U)
  commRing _ := inferInstance
  algebra _ := inferInstance
  grading U := homog (𝒜.grading U)
  gradedAlgebra _ := homog.gradedAlgebra
  map h := homogMap (𝒜.map h)
  map_id U := by
    rw [𝒜.map_id]
    exact homogMap_id
  map_comp hUV hVW := by
    rw [𝒜.map_comp]
    exact homogMap_comp _ _
  isBaseChange h := isGradedBaseChangeAlong_homog (𝒜.isBaseChange h)

/-- The degree-zero part of the homogenisation is of finite type. -/
instance finiteType_homogenisation [∀ U, Algebra.FiniteType (𝒜.grading U 0) (𝒜.ring U)]
    (U : X.affineOpens) :
    Algebra.FiniteType (𝒜.homogenisation.grading U 0) (𝒜.homogenisation.ring U) :=
  finiteType_homog_zero

/-- The projective completion `Proj_X 𝒜[t]` of a quasi-coherent graded algebra. -/
abbrev projCompletion : Scheme.{u} := relativeProj X 𝒜.homogenisation

/-- The structure morphism of the projective completion. -/
abbrev projCompletionToBase : 𝒜.projCompletion ⟶ X := toBase X 𝒜.homogenisation

/-- The projective completion is proper over `X` when `𝒜` is affine-locally of finite type over
its degree-zero part and has degree-zero part the section ring. -/
theorem projCompletionToBase_isProper [∀ U, Algebra.FiniteType (𝒜.grading U 0) (𝒜.ring U)]
    (h0 : ∀ U, Function.Bijective (algebraMap Γ(X, U.1) (𝒜.grading U 0))) :
    IsProper 𝒜.projCompletionToBase :=
  toBase_isProper X 𝒜.homogenisation fun U ↦ bijective_algebraMap_homog_zero (h0 U)

/-- The morphism of graded algebra data `𝒜[t] → 𝒜`, `t ↦ 0`. -/
def evalZeroHom : Hom 𝒜.homogenisation 𝒜 where
  app U := evalZeroGraded (𝒜.grading U)
  commutes U a := by
    change (algebraMap Γ(X, U.1) (𝒜.ring U)[X] a).coeff 0 = _
    rw [Polynomial.algebraMap_apply, Polynomial.coeff_C_zero]
  naturality h := evalZeroGraded_comp_homogMap (𝒜.map h)
  irrelevant_le _ := irrelevant_le_map_evalZeroGraded

/-- The closed embedding `Proj_X 𝒜 → Proj_X 𝒜[t]` at infinity (`t = 0`). -/
def infinity : relativeProj X 𝒜 ⟶ 𝒜.projCompletion := 𝒜.evalZeroHom.map

/-- The embedding at infinity is a closed immersion. -/
instance isClosedImmersion_infinity : IsClosedImmersion 𝒜.infinity :=
  𝒜.evalZeroHom.map_isClosedImmersion fun _ ↦ evalZeroGraded_surjective

/-- The embedding at infinity lies over `X`. -/
@[reassoc (attr := simp)]
theorem infinity_toBase : 𝒜.infinity ≫ 𝒜.projCompletionToBase = toBase X 𝒜 :=
  𝒜.evalZeroHom.map_toBase

/-- The chart data identifying `D₊(t) ⊆ Proj (𝒜 U)[t]` with `Spec (𝒜' U)`, for an algebra
data `𝒜'` whose rings are identified with those of `𝒜` compatibly with the structure and
transition maps. -/
def awayChartData (𝒜' : AlgebraData X) (e : ∀ U, 𝒜.ring U ≃+* 𝒜'.ring U)
    (he : ∀ U (a : Γ(X, U.1)), e U (algebraMap _ _ a) = algebraMap _ _ a)
    (hnat : ∀ {U V : X.affineOpens} (h : U ≤ V),
      (e U).toRingHom.comp (𝒜.map h).toRingHom = (𝒜'.map h).comp (e V).toRingHom) :
    AwayChartData 𝒜' 𝒜.homogenisation where
  elem _ := Polynomial.X
  elem_mem _ := X_mem_homog
  map_elem h := by
    change (Polynomial.X : (𝒜.ring _)[X]).map _ = Polynomial.X
    exact Polynomial.map_X _
  iso U := (dehomogenise (𝒜.grading U)).trans (e U)
  iso_algebraMap U a := by
    change e U (dehomogeniseAt (𝒜.grading U) Polynomial.X rfl
      (algebraMap (homog (𝒜.grading U) 0) _ (algebraMap Γ(X, U.1) _ a))) = _
    rw [dehomogeniseAt_algebraMap, he]
  naturality {U V} h := by
    refine RingHom.ext fun x ↦ ?_
    have hX : (Polynomial.X : (𝒜.ring V)[X]) ∈ homog (𝒜.grading V) 1 := X_mem_homog
    let x' : Away (homog (𝒜.grading V)) (Polynomial.X : (𝒜.ring V)[X]) := x
    obtain ⟨n, p, hp, hx⟩ := Away.mk_surjective (homog (𝒜.grading V)) hX x'
    obtain rfl : _ = x := hx
    change e U (dehomogenise _ (awayMapOfEq (homogMap (𝒜.map h)) _ _
      (by rw [homogMap_apply, Polynomial.map_X]) _)) =
      𝒜'.map h (e V (dehomogenise _ _))
    rw [awayMapOfEq_mk (homogMap (𝒜.map h)) _ _ _ X_mem_homog X_mem_homog, dehomogenise_mk,
      dehomogenise_mk, homogMap_apply, Polynomial.eval_one_map]
    exact congrArg (fun g : 𝒜.ring V →+* 𝒜'.ring U ↦ g (p.eval 1)) (hnat h)

/-- The image of `Proj (𝒜 U)` in `Proj (𝒜 U)[t]` is the complement of `D₊(t)`. -/
theorem range_projMap_evalZero (U : X.affineOpens) :
    Set.range (Proj.map (𝒜.evalZeroHom.app U) (𝒜.evalZeroHom.irrelevant_le U)) =
      ((Proj.basicOpen (𝒜.homogenisation.grading U) (Polynomial.X : (𝒜.ring U)[X]) :
        Set (Proj (𝒜.homogenisation.grading U))))ᶜ := by
  refine range_projMap_eq_compl_basicOpen _ _ evalZeroGraded_surjective _ ?_ ?_
  · change (Polynomial.X : (𝒜.ring U)[X]).coeff 0 = 0
    exact Polynomial.coeff_X_zero
  · intro p hp
    rw [RingHom.mem_ker] at hp
    exact Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr hp)

section OpenEmbedding

variable (𝒜' : AlgebraData X) (e : ∀ U, 𝒜.ring U ≃+* 𝒜'.ring U)
    (he : ∀ U (a : Γ(X, U.1)), e U (algebraMap _ _ a) = algebraMap _ _ a)
    (hnat : ∀ {U V : X.affineOpens} (h : U ≤ V),
      (e U).toRingHom.comp (𝒜.map h).toRingHom = (𝒜'.map h).comp (e V).toRingHom)

/-- The open embedding `Spec_X 𝒜' → Proj_X 𝒜[t]` onto the locus `t ≠ 0`. -/
def openEmbedding : RelativeSpec.relativeSpec X 𝒜' ⟶ 𝒜.projCompletion :=
  (𝒜.awayChartData 𝒜' e he @hnat).map

/-- The embedding of `Spec_X 𝒜'` is an open immersion. -/
instance isOpenImmersion_openEmbedding : IsOpenImmersion (𝒜.openEmbedding 𝒜' e he @hnat) :=
  AwayChartData.isOpenImmersion_map _

/-- The embedding of `Spec_X 𝒜'` lies over `X`. -/
@[reassoc (attr := simp)]
theorem openEmbedding_toBase :
    𝒜.openEmbedding 𝒜' e he @hnat ≫ 𝒜.projCompletionToBase = RelativeSpec.toBase X 𝒜' :=
  AwayChartData.map_toBase _

/-- The image of the open embedding is the complement of the image of the embedding at
infinity. -/
theorem range_openEmbedding :
    Set.range (𝒜.openEmbedding 𝒜' e he @hnat) = (Set.range 𝒜.infinity)ᶜ :=
  AwayChartData.range_map_eq_compl _ 𝒜.evalZeroHom fun U ↦ by
    rw [AwayChartData.range_chart, range_projMap_evalZero, compl_compl]
    rfl

end OpenEmbedding

end GradedAlgebraData

/-! ### The projective completion of a graded vector bundle -/

namespace GradedBundleData

open GromovWitten.Algebra RelativeProj

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : GradedBundleData X ι)

/-- The homogenised graded algebra `𝒜[t]` of a graded vector bundle with algebra of
functions `𝒜`; its relative `Proj` is `P(E ⊕ 1)`. -/
abbrev homogData : GradedAlgebraData X := 𝓔.toGradedAlgebraData.homogenisation

/-- The projective completion `P(E ⊕ 1) = Proj_X 𝒜[t]` of a graded vector bundle. -/
abbrev projectiveCompletion : Scheme.{u} := relativeProj X 𝓔.homogData

/-- The structure morphism `P(E ⊕ 1) → X`. -/
abbrev completionToBase : 𝓔.projectiveCompletion ⟶ X := toBase X 𝓔.homogData

/-- The homogenised algebra of a graded bundle is of finite type over degree zero. -/
instance finiteType_homogData (U : X.affineOpens) :
    Algebra.FiniteType (𝓔.homogData.grading U 0) (𝓔.homogData.ring U) :=
  have : Algebra.FiniteType Γ(X, U.1) (𝓔.toGradedAlgebraData.ring U) := 𝓔.finiteType U
  finiteType_homog_zero_of_finiteType

/-- The projective completion is proper over the base. -/
instance completionToBase_isProper : IsProper 𝓔.completionToBase :=
  toBase_isProper X 𝓔.homogData fun U ↦ bijective_algebraMap_homog_zero (𝓔.degreeZero U)

/-- The embedding at infinity `P(E) = Proj_X 𝒜 → P(E ⊕ 1)`, induced by `t ↦ 0`. -/
abbrev infinityDivisor : relativeProj X 𝓔.toGradedAlgebraData ⟶ 𝓔.projectiveCompletion :=
  𝓔.toGradedAlgebraData.infinity

/-- `P(E) → P(E ⊕ 1)` is a closed immersion. -/
instance isClosedImmersion_infinityDivisor : IsClosedImmersion 𝓔.infinityDivisor :=
  𝓔.toGradedAlgebraData.isClosedImmersion_infinity

/-- The embedding at infinity lies over `X`. -/
theorem infinityDivisor_toBase :
    𝓔.infinityDivisor ≫ 𝓔.completionToBase = toBase X 𝓔.toGradedAlgebraData :=
  𝓔.toGradedAlgebraData.infinity_toBase

/-- The open embedding of the total space `E = Spec_X 𝒜` into `P(E ⊕ 1)` as the locus
`t ≠ 0`. -/
def bundleOpenEmbedding : 𝓔.bundle.totalSpace ⟶ 𝓔.projectiveCompletion :=
  𝓔.toGradedAlgebraData.openEmbedding 𝓔.bundle.algebra (fun _ ↦ RingEquiv.refl _)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)

/-- The total space is an open subscheme of the projective completion. -/
instance isOpenImmersion_bundleOpenEmbedding : IsOpenImmersion 𝓔.bundleOpenEmbedding :=
  GradedAlgebraData.isOpenImmersion_openEmbedding _ _ _ _ _

/-- The open embedding of the total space lies over `X`. -/
@[reassoc (attr := simp)]
theorem bundleOpenEmbedding_toBase :
    𝓔.bundleOpenEmbedding ≫ 𝓔.completionToBase = 𝓔.bundle.proj :=
  GradedAlgebraData.openEmbedding_toBase _ _ _ _ _

/-- `E` is the complement of `P(E)` in `P(E ⊕ 1)`. -/
theorem range_bundleOpenEmbedding :
    Set.range 𝓔.bundleOpenEmbedding = (Set.range 𝓔.infinityDivisor)ᶜ :=
  GradedAlgebraData.range_openEmbedding _ _ _ _ _

/-! #### Charts over trivialising opens -/

section Chart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (j : 𝓔.bundle.J)

/-- The trivialisation over a chart as a graded ring map. -/
def trivGraded :
    𝓔.grading (𝓔.bundle.chart j) →+*ᵍ
      MvPolynomial.homogeneousSubmodule ι Γ(X, (𝓔.bundle.chart j).1) where
  toRingHom := (𝓔.bundle.triv j).toRingEquiv.toRingHom
  map_mem {n x} hx := by
    rw [← 𝓔.triv_graded j n]
    exact Submodule.mem_map_of_mem hx

/-- The inverse of the trivialisation over a chart as a graded ring map. -/
def trivGradedInv :
    MvPolynomial.homogeneousSubmodule ι Γ(X, (𝓔.bundle.chart j).1) →+*ᵍ
      𝓔.grading (𝓔.bundle.chart j) where
  toRingHom := (𝓔.bundle.triv j).symm.toRingEquiv.toRingHom
  map_mem {n y} hy := by
    rw [← 𝓔.triv_graded j n] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    change (𝓔.bundle.triv j).symm (𝓔.bundle.triv j x) ∈ _
    rwa [AlgEquiv.symm_apply_apply]

/-- The graded identification of `𝒜[t]` over a chart with `Γ(U)[x_i : i ∈ Option ι]`. -/
def chartGraded :
    𝓔.homogData.grading (𝓔.bundle.chart j) →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Option ι) Γ(X, (𝓔.bundle.chart j).1) :=
  (homogToOptionGraded Γ(X, (𝓔.bundle.chart j).1) ι).comp (homogMap (𝓔.trivGraded j))

/-- The inverse of `chartGraded`. -/
def chartGradedInv :
    MvPolynomial.homogeneousSubmodule (Option ι) Γ(X, (𝓔.bundle.chart j).1) →+*ᵍ
      𝓔.homogData.grading (𝓔.bundle.chart j) :=
  (homogMap (𝓔.trivGradedInv j)).comp (optionToHomogGraded Γ(X, (𝓔.bundle.chart j).1) ι)

/-- `trivGradedInv` is a right inverse of `trivGraded`. -/
theorem trivGraded_comp_trivGradedInv :
    (𝓔.trivGraded j).comp (𝓔.trivGradedInv j) = GradedRingHom.id _ :=
  GradedRingHom.ext fun y ↦ (𝓔.bundle.triv j).apply_symm_apply y

/-- `trivGradedInv` is a left inverse of `trivGraded`. -/
theorem trivGradedInv_comp_trivGraded :
    (𝓔.trivGradedInv j).comp (𝓔.trivGraded j) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x ↦ (𝓔.bundle.triv j).symm_apply_apply x

/-- `chartGradedInv` is a right inverse of `chartGraded`. -/
theorem chartGraded_comp_chartGradedInv :
    (𝓔.chartGraded j).comp (𝓔.chartGradedInv j) = GradedRingHom.id _ := by
  refine GradedRingHom.ext fun q ↦ ?_
  change homogEquivOption _ ι ((((homogEquivOption _ ι).symm q).map
    (𝓔.bundle.triv j).symm.toRingEquiv.toRingHom).map
      (𝓔.bundle.triv j).toRingEquiv.toRingHom) = q
  have h : (𝓔.bundle.triv j).toRingEquiv.toRingHom.comp
      (𝓔.bundle.triv j).symm.toRingEquiv.toRingHom = RingHom.id _ :=
    RingHom.ext fun y ↦ (𝓔.bundle.triv j).apply_symm_apply y
  rw [Polynomial.map_map, h, Polynomial.map_id, AlgEquiv.apply_symm_apply]

/-- `chartGradedInv` is a left inverse of `chartGraded`. -/
theorem chartGradedInv_comp_chartGraded :
    (𝓔.chartGradedInv j).comp (𝓔.chartGraded j) = GradedRingHom.id _ := by
  refine GradedRingHom.ext fun (p : Polynomial (𝓔.bundle.algebra.ring (𝓔.bundle.chart j))) ↦ ?_
  change ((homogEquivOption _ ι).symm (homogEquivOption _ ι
    (p.map (𝓔.bundle.triv j).toRingEquiv.toRingHom))).map
      (𝓔.bundle.triv j).symm.toRingEquiv.toRingHom = p
  have h : (𝓔.bundle.triv j).symm.toRingEquiv.toRingHom.comp
      (𝓔.bundle.triv j).toRingEquiv.toRingHom = RingHom.id _ :=
    RingHom.ext fun y ↦ (𝓔.bundle.triv j).symm_apply_apply y
  rw [AlgEquiv.symm_apply_apply, Polynomial.map_map, h, Polynomial.map_id]

/-- The piece of `P(E ⊕ 1)` over a trivialising chart `U` is the projective space
`Proj Γ(U)[x_i : i ∈ Option ι]`. -/
def chartProjIso :
    Proj (MvPolynomial.homogeneousSubmodule (Option ι) Γ(X, (𝓔.bundle.chart j).1)) ≅
      Proj (𝓔.homogData.grading (𝓔.bundle.chart j)) where
  hom := Proj.map (𝓔.chartGraded j)
    (irrelevant_le_map_of_rightInverse _ (𝓔.chartGradedInv j)
      fun q ↦ GradedRingHom.congr_fun (𝓔.chartGraded_comp_chartGradedInv j) q)
  inv := Proj.map (𝓔.chartGradedInv j)
    (irrelevant_le_map_of_rightInverse _ (𝓔.chartGraded j)
      fun p ↦ GradedRingHom.congr_fun (𝓔.chartGradedInv_comp_chartGraded j) p)
  hom_inv_id := by
    rw [← Proj.map_comp, projMap_congr (𝓔.chartGraded_comp_chartGradedInv j)]
    exact Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp, projMap_congr (𝓔.chartGradedInv_comp_chartGraded j)]
    exact Proj.map_id

/-- The inverse of `chartProjIso` lies over the section ring of the chart. -/
theorem chartProjIso_inv_projection :
    (𝓔.chartProjIso j).inv ≫
        projection (MvPolynomial.homogeneousSubmodule (Option ι) Γ(X, (𝓔.bundle.chart j).1)) =
      projection (𝓔.homogData.grading (𝓔.bundle.chart j)) := by
  refine projMap_projection _ _ fun a ↦ ?_
  change ((homogEquivOption _ ι).symm (algebraMap _ _ a)).map
    (𝓔.bundle.triv j).symm.toRingEquiv.toRingHom = algebraMap _ _ a
  rw [AlgEquiv.commutes, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply,
    Polynomial.map_C]
  congr 1
  exact (𝓔.bundle.triv j).symm.commutes a

/-- Over a trivialising chart `U`, `P(E ⊕ 1)` restricts to the projective space
`Proj Γ(U)[x_i : i ∈ Option ι]` over `U`. -/
theorem isPullback_chartProjIso :
    IsPullback
      (projection (MvPolynomial.homogeneousSubmodule (Option ι) Γ(X, (𝓔.bundle.chart j).1)) ≫
        (isAffineOpen X (𝓔.bundle.chart j)).isoSpec.inv)
      ((𝓔.chartProjIso j).hom ≫ affineι X 𝓔.homogData (𝓔.bundle.chart j))
      (𝓔.bundle.chart j).1.ι 𝓔.completionToBase := by
  refine (isPullback_affine X 𝓔.homogData (𝓔.bundle.chart j)).of_iso (𝓔.chartProjIso j).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp) (by simp)
  rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← Category.assoc,
    chartProjIso_inv_projection]

end Chart

end GradedBundleData

end

end GromovWitten.AlgebraicGeometry
