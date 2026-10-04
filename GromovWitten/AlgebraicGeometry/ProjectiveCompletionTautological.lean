/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.ProjectiveCompletionCharts
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleData

/-!
# The tautological line bundle `O(1)` on the projective completion `P(E ⊕ 1)`

For a graded vector bundle `𝓔 : GradedBundleData X ι` on a scheme `X` whose affine opens have
affine pairwise intersections (hypothesis `hX`, true e.g. for separated `X`; we do not develop
separatedness), we construct the tautological line bundle `O(1)` on the projective completion
`P(E ⊕ 1) = Proj_X 𝒜[t]` as a Čech cocycle (`LineBundleData`).

The cover is by the affine opens `D₊(x_a)`, `a = (j, i)`, where `j` runs over the trivialising
charts `U_j` of the bundle and `x_i` (`i : Option ι`, `x_none = t`) over the homogeneous
coordinates of `𝒜[t](U_j) ≅ Γ(U_j)[x_i : i ∈ Option ι]` (`chartGradedInv`).  Over the affine
open `U'' = U_j ∩ U_{j'}` both coordinates restrict to degree-one elements, the overlap
`D₊(x_a) ∩ D₊(x_b)` is the image of `D₊(x_a x_b) ⊆ Proj 𝒜[t](U'')`, and the transition unit is
the degree-zero fraction `x_b² / (x_a x_b) = x_b / x_a`.  The cocycle identity is checked in the
homogeneous localisation at `x_a x_b x_c` over the triple intersection.

The main tool is a description of the sections of the structure sheaf over the image of an open
immersion `ψ : Spec A ⟶ P` (`sectionsEquiv : Γ(P, range ψ) ≃+* A`), compatible with
restriction along a factorisation `ψ₂ = Spec α ≫ ψ₁` (`sectionsToRing_res`), together with a
calculus of the opens `D₊(f)` of the affine pieces of a relative `Proj` (`RelativeProj.awayChart`):
restriction to a smaller affine open of the base (`range_awayChart_inf_preimage`,
`awayChart_map`) and intersections (`range_awayChart_inf`).

## Main results

* `sectionsToRing`, `sectionsEquiv`, `sectionsToRing_res`: sections over the range of an open
  immersion from an affine scheme, and their restriction.
* `RelativeProj.awayChart`: the open immersion `Spec (𝒜 U)_(f) ⟶ Proj_X 𝒜` onto the image of
  `D₊(f)`, with `RelativeProj.projMap_affineι`, `RelativeProj.range_affineι`,
  `RelativeProj.affineι_mem_range_awayChart_iff`, `RelativeProj.awayChart_map`,
  `RelativeProj.awayChart_map_mul`, `RelativeProj.range_awayChart_inf_preimage`,
  `RelativeProj.range_awayChart_inf_same`, `RelativeProj.range_awayChart_inf`.
* `ratioUnit`: the unit `t / s = t² / (st)` of `(A)_(st)` for degree-one `s, t`.
* `GradedBundleData.tautological 𝓔 hX : LineBundleData 𝓔.projectiveCompletion`, the line bundle
  `O(1)`, with `GradedBundleData.tautological_U` (its opens are the images of the charts
  `GradedBundleData.tautChart`) and `GradedBundleData.tautological_g` (read through the chart
  `D₊(x_a x_b)` over `U_j ∩ U_{j'}`, the transition unit is `x_b² / (x_a x_b)`); the cocycle
  condition is `GradedBundleData.tautTransition_cocycle` and the covering property
  `GradedBundleData.exists_mem_tautOpen`.
* `GradedBundleData.range_tautChart`: the image of the chart `D₊(x_a)`, `a = (j, i)`, is the
  image of `D₊(X i) ⊆ Proj Γ(U_j)[x_k : k ∈ Option ι]` under `chartProjIso j` (comparison with
  the standard charts of `P(E ⊕ 1)`), and `GradedBundleData.opensRange_completionChart`: these
  are exactly the images of the charts `completionChart a` of `ProjectiveCompletionCharts`.

## Conventions

`LineBundleData` transforms coordinates by `coord_a = g a b * coord_b`
(`RationalSection.coord_eq_unitAt_mul_coord`; compare `O(D)` in `CartierLineBundle`, where
`g x y = r_x / r_y`).  With `g a b = x_b / x_a`, the coordinates `x_none / x_a` (one in each
chart) are compatible, i.e. they describe a section `x_none`, whose coordinates are regular
functions vanishing along the divisor at infinity: informally, this is `O(1)` and not its dual.
(The rational section `x_none` and its divisor are not formalised in this file.)
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace HomogeneousLocalization

namespace GromovWitten.AlgebraicGeometry

open ProjBaseChange GlobalBlowup ReesBlowupOfEq

universe u

noncomputable section

/-! ### Sections over the image of an open immersion from an affine scheme -/

section Sections

variable {P : Scheme.{u}} {A B : CommRingCat.{u}}

/-- An open containing the range of an open immersion pulls back to the whole source. -/
theorem top_le_preimage_of_opensRange_le {Y : Scheme.{u}} (ψ : Y ⟶ P) [IsOpenImmersion ψ]
    {O : P.Opens} (hO : ψ.opensRange ≤ O) : ⊤ ≤ ψ ⁻¹ᵁ O :=
  fun x _ ↦ hO ⟨x, rfl⟩

/-- For an open immersion `ψ : Spec A ⟶ P` and an open `O` of `P` containing its range, the ring
map `Γ(P, O) → A` given by pulling back along `ψ`. -/
def sectionsToRing (ψ : Spec A ⟶ P) [IsOpenImmersion ψ] (O : P.Opens) (hO : ψ.opensRange ≤ O) :
    Γ(P, O) →+* A :=
  (ψ.appLE O ⊤ (top_le_preimage_of_opensRange_le ψ hO) ≫ (Scheme.ΓSpecIso A).hom).hom

/-- `sectionsToRing` is compatible with restriction of sections: if `ψ₂ = Spec α ≫ ψ₁`, then
restricting from `O₁` to `O₂` and pulling back along `ψ₂` is pulling back along `ψ₁` followed
by `α`. -/
theorem sectionsToRing_res (ψ₁ : Spec A ⟶ P) (ψ₂ : Spec B ⟶ P) [IsOpenImmersion ψ₁]
    [IsOpenImmersion ψ₂] (α : A ⟶ B) (hψ : ψ₂ = Spec.map α ≫ ψ₁) {O₁ O₂ : P.Opens}
    (h₁ : ψ₁.opensRange ≤ O₁) (h₂ : ψ₂.opensRange ≤ O₂) (h : O₂ ≤ O₁) (s : Γ(P, O₁)) :
    sectionsToRing ψ₂ O₂ h₂ (P.presheaf.map (homOfLE h).op s) =
      α.hom (sectionsToRing ψ₁ O₁ h₁ s) := by
  subst hψ
  change (P.presheaf.map (homOfLE h).op ≫ (Spec.map α ≫ ψ₁).appLE O₂ ⊤ _ ≫
    (Scheme.ΓSpecIso B).hom).hom s = ((ψ₁.appLE O₁ ⊤ _ ≫ (Scheme.ΓSpecIso A).hom) ≫ α).hom s
  congr 1
  rw [Scheme.Hom.map_appLE_assoc, Category.assoc, ← Scheme.ΓSpecIso_naturality,
    ← Category.assoc]
  congr 2

/-- Over the range of an open immersion `ψ : Spec A ⟶ P`, `sectionsToRing` is bijective.
(Compare Mathlib's `IsOpenImmersion.ΓIsoTop ψ : Γ(Spec A, ⊤) ≅ Γ(P, ψ.opensRange)`; here the
map is the explicit `appLE` pullback, which is what `sectionsToRing_res` computes with.) -/
theorem sectionsToRing_bijective (ψ : Spec A ⟶ P) [IsOpenImmersion ψ] (O : P.Opens)
    (hO : ψ.opensRange = O) : Function.Bijective (sectionsToRing ψ O hO.le) := by
  subst hO
  have hpre : ψ ⁻¹ᵁ ψ.opensRange = ⊤ := by
    ext x
    simp
  have : IsIso (ψ.app ψ.opensRange) := Scheme.Hom.isIso_app ψ _ le_rfl
  have : IsIso (ψ.appLE ψ.opensRange ⊤ (top_le_preimage_of_opensRange_le ψ le_rfl)) := by
    change IsIso (ψ.app _ ≫ _)
    have : (homOfLE (top_le_preimage_of_opensRange_le ψ le_rfl)).op =
        (eqToHom hpre.symm).op := rfl
    rw [this]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (ψ.appLE ψ.opensRange ⊤ (top_le_preimage_of_opensRange_le ψ le_rfl) ≫ (Scheme.ΓSpecIso A).hom)

/-- Over the range of an open immersion `ψ : Spec A ⟶ P`, the sections of the structure sheaf
are `A`. -/
def sectionsEquiv (ψ : Spec A ⟶ P) [IsOpenImmersion ψ] (O : P.Opens) (hO : ψ.opensRange = O) :
    Γ(P, O) ≃+* A :=
  RingEquiv.ofBijective (sectionsToRing ψ O hO.le) (sectionsToRing_bijective ψ O hO)

/-- `sectionsEquiv` is `sectionsToRing`. -/
@[simp]
theorem sectionsEquiv_apply (ψ : Spec A ⟶ P) [IsOpenImmersion ψ] (O : P.Opens)
    (hO : ψ.opensRange = O) (s : Γ(P, O)) :
    sectionsEquiv ψ O hO s = sectionsToRing ψ O hO.le s :=
  rfl

end Sections

/-! ### Basic opens `D₊(f)` of the affine pieces of a relative `Proj` -/

section AwayRange

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜]

/-- A point of `Proj 𝒜` lies in the image of `Spec (A)_(f) ≅ D₊(f)` iff `f` does not lie in the
corresponding homogeneous prime. -/
theorem mem_range_awayι_iff (y : Proj 𝒜) (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    y ∈ Set.range (Proj.awayι 𝒜 f hf hd) ↔ f ∉ y.asHomogeneousIdeal := by
  have := congrArg (fun O : (Proj 𝒜).Opens ↦ (O : Set (Proj 𝒜))) (Proj.opensRange_awayι 𝒜 f hf hd)
  simp only [Scheme.Hom.coe_opensRange] at this
  rw [this]
  exact Iff.rfl

end AwayRange

namespace RelativeProj

/- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
type of affine opens, as in `RelativeProj`. -/
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (𝒜 : GradedAlgebraData X)

/-- The open immersion `Spec (𝒜 U)_(f) ≅ D₊(f) ⊆ Proj (𝒜 U) ⊆ Proj_X 𝒜` for a homogeneous
element `f` of positive degree of the graded algebra over an affine open `U`. -/
def awayChart (U : X.affineOpens) (f : 𝒜.ring U) {d : ℕ} (hf : f ∈ 𝒜.grading U d) (hd : 0 < d) :
    Spec (.of (Away (𝒜.grading U) f)) ⟶ relativeProj X 𝒜 :=
  Proj.awayι (𝒜.grading U) f hf hd ≫ affineι X 𝒜 U

/-- The charts `awayChart` are open immersions. -/
instance isOpenImmersion_awayChart (U : X.affineOpens) (f : 𝒜.ring U) {d : ℕ}
    (hf : f ∈ 𝒜.grading U d) (hd : 0 < d) : IsOpenImmersion (awayChart 𝒜 U f hf hd) := by
  unfold awayChart
  infer_instance

/-- The transition maps of graded algebra data preserve the degree. -/
theorem map_mem_grading {U V : X.affineOpens} (h : U ≤ V) {f : 𝒜.ring V} {d : ℕ}
    (hf : f ∈ 𝒜.grading V d) : 𝒜.map h f ∈ 𝒜.grading U d :=
  (𝒜.map h).map_mem hf

/-- The affine pieces of a relative `Proj` are compatible with the transition maps. -/
@[reassoc]
theorem projMap_affineι {U V : X.affineOpens} (h : U ≤ V) :
    Proj.map (𝒜.map h) (irrelevant_le X 𝒜 h) ≫ affineι X 𝒜 V = affineι X 𝒜 U :=
  colimit.w (gluingData X 𝒜).functor (homOfLE h)

/-- The affine piece over `U` is the preimage of `U`. -/
theorem range_affineι (U : X.affineOpens) :
    Set.range (affineι X 𝒜 U) = toBase X 𝒜 ⁻¹' (U.1 : Set X) := by
  rw [Scheme.range_fst_of_isPullback (isPullback_affine X 𝒜 U).flip, Scheme.Opens.range_ι]

/-- The affine pieces of a relative `Proj` embed injectively. -/
theorem affineι_injective (U : X.affineOpens) : Function.Injective (affineι X 𝒜 U) :=
  (affineι X 𝒜 U).isOpenEmbedding.injective

/-- A point of the affine piece over `U` lies in the image of `D₊(f)` iff `f` does not lie in
the corresponding homogeneous prime. -/
theorem affineι_mem_range_awayChart_iff (U : X.affineOpens) (y : Proj (𝒜.grading U))
    (f : 𝒜.ring U) {d : ℕ} (hf : f ∈ 𝒜.grading U d) (hd : 0 < d) :
    affineι X 𝒜 U y ∈ Set.range (awayChart 𝒜 U f hf hd) ↔ f ∉ y.asHomogeneousIdeal := by
  rw [← mem_range_awayι_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, affineι_injective 𝒜 U ?_⟩
    rw [← hz, awayChart, Scheme.Hom.comp_apply]
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [awayChart, Scheme.Hom.comp_apply]⟩

/-- The image of `D₊(f)` lies in the affine piece over `U`. -/
theorem range_awayChart_subset (U : X.affineOpens) (f : 𝒜.ring U) {d : ℕ}
    (hf : f ∈ 𝒜.grading U d) (hd : 0 < d) :
    Set.range (awayChart 𝒜 U f hf hd) ⊆ Set.range (affineι X 𝒜 U) := by
  rintro _ ⟨z, rfl⟩
  exact ⟨_, rfl⟩

/-- The points of the image of `D₊(f)` are the images of the homogeneous primes of `𝒜 U`
not containing `f`. -/
theorem mem_range_awayChart_iff (U : X.affineOpens) (f : 𝒜.ring U) {d : ℕ}
    (hf : f ∈ 𝒜.grading U d) (hd : 0 < d) (p : relativeProj X 𝒜) :
    p ∈ Set.range (awayChart 𝒜 U f hf hd) ↔
      ∃ y : Proj (𝒜.grading U), affineι X 𝒜 U y = p ∧ f ∉ y.asHomogeneousIdeal := by
  constructor
  · intro hp
    obtain ⟨y, rfl⟩ := range_awayChart_subset 𝒜 U f hf hd hp
    exact ⟨y, rfl, (affineι_mem_range_awayChart_iff 𝒜 U y f hf hd).mp hp⟩
  · rintro ⟨y, rfl, hy⟩
    exact (affineι_mem_range_awayChart_iff 𝒜 U y f hf hd).mpr hy

/-- The image of `D₊(f)` lies over `U`. -/
theorem range_awayChart_le_preimage (U : X.affineOpens) (f : 𝒜.ring U) {d : ℕ}
    (hf : f ∈ 𝒜.grading U d) (hd : 0 < d) :
    (awayChart 𝒜 U f hf hd).opensRange ≤ toBase X 𝒜 ⁻¹ᵁ U.1 := by
  intro p hp
  have := range_awayChart_subset 𝒜 U f hf hd hp
  rw [range_affineι] at this
  exact this

/-- Restricting `D₊(f)` to a smaller affine open `U ≤ V`: the chart of the image of `f` is the
chart of `f` precomposed with the map of homogeneous localisations. -/
theorem awayChart_map {U V : X.affineOpens} (h : U ≤ V) (f : 𝒜.ring V) {d : ℕ}
    (hf : f ∈ 𝒜.grading V d) (hd : 0 < d) :
    awayChart 𝒜 U (𝒜.map h f) (map_mem_grading 𝒜 h hf) hd =
      Spec.map (CommRingCat.ofHom (Away.map (𝒜.map h) f)) ≫ awayChart 𝒜 V f hf hd := by
  rw [awayChart, awayChart, ← projMap_affineι 𝒜 h, ← Category.assoc, Proj.awayι_comp_map,
    Category.assoc]

/-- The chart of `x = f|_U * g` is the chart of `f` precomposed with the restriction and
localisation map `(𝒜 V)_(f) → (𝒜 U)_(f|_U) → (𝒜 U)_(x)`. -/
theorem awayChart_map_mul {U V : X.affineOpens} (h : U ≤ V) (f : 𝒜.ring V) {d e : ℕ}
    (hf : f ∈ 𝒜.grading V d) (hd : 0 < d) (g : 𝒜.ring U) (hg : g ∈ 𝒜.grading U e)
    (x : 𝒜.ring U) (hx : x = 𝒜.map h f * g) (hxd : x ∈ 𝒜.grading U (d + e))
    (hde : 0 < d + e) :
    awayChart 𝒜 U x hxd hde =
      Spec.map (CommRingCat.ofHom ((awayMap (𝒜.grading U) hg hx).comp
        (Away.map (𝒜.map h) f))) ≫ awayChart 𝒜 V f hf hd := by
  have h1 := awayChart_map 𝒜 h f hf hd
  have h2 := Proj.SpecMap_awayMap_awayι (𝒜.grading U) (map_mem_grading 𝒜 h hf) hd hg hx
  calc awayChart 𝒜 U x hxd hde
      = Spec.map (CommRingCat.ofHom (awayMap (𝒜.grading U) hg hx)) ≫
          awayChart 𝒜 U (𝒜.map h f) (map_mem_grading 𝒜 h hf) hd := by
        rw [awayChart, awayChart, ← Category.assoc, h2]
    _ = _ := by
        rw [h1, ← Category.assoc, ← Spec.map_comp]
        rfl

/-- `D₊(f)` over `V`, intersected with the preimage of `U ≤ V`, is `D₊(f|_U)` over `U`. -/
theorem range_awayChart_inf_preimage {U V : X.affineOpens} (h : U ≤ V) (f : 𝒜.ring V) {d : ℕ}
    (hf : f ∈ 𝒜.grading V d) (hd : 0 < d) :
    (awayChart 𝒜 V f hf hd).opensRange ⊓ toBase X 𝒜 ⁻¹ᵁ U.1 =
      (awayChart 𝒜 U (𝒜.map h f) (map_mem_grading 𝒜 h hf) hd).opensRange := by
  ext p
  change p ∈ Set.range (awayChart 𝒜 V f hf hd) ∧ p ∈ toBase X 𝒜 ⁻¹' (U.1 : Set X) ↔
    p ∈ Set.range (awayChart 𝒜 U (𝒜.map h f) (map_mem_grading 𝒜 h hf) hd)
  rw [← range_affineι]
  constructor
  · rintro ⟨hp, y, rfl⟩
    rw [← projMap_affineι 𝒜 h, Scheme.Hom.comp_apply,
      affineι_mem_range_awayChart_iff] at hp
    exact (affineι_mem_range_awayChart_iff 𝒜 U y _ _ hd).mpr hp
  · intro hp
    refine ⟨?_, range_awayChart_subset 𝒜 U _ _ hd hp⟩
    rw [awayChart_map 𝒜 h f hf hd] at hp
    obtain ⟨z, hz⟩ := hp
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans hz⟩

/-- `D₊(a) ∩ D₊(b) = D₊(ab)` inside the relative `Proj`. -/
theorem range_awayChart_inf_same (U : X.affineOpens) (a b : 𝒜.ring U) {d e : ℕ}
    (ha : a ∈ 𝒜.grading U d) (hb : b ∈ 𝒜.grading U e) (hd : 0 < d) (he : 0 < e) :
    (awayChart 𝒜 U a ha hd).opensRange ⊓ (awayChart 𝒜 U b hb he).opensRange =
      (awayChart 𝒜 U (a * b) (SetLike.mul_mem_graded ha hb) (by omega)).opensRange := by
  ext p
  change p ∈ Set.range (awayChart 𝒜 U a ha hd) ∧ p ∈ Set.range (awayChart 𝒜 U b hb he) ↔
    p ∈ Set.range (awayChart 𝒜 U (a * b) (SetLike.mul_mem_graded ha hb) (by omega))
  constructor
  · rintro ⟨hpa, hpb⟩
    obtain ⟨y, rfl⟩ := range_awayChart_subset 𝒜 U a ha hd hpa
    rw [affineι_mem_range_awayChart_iff] at hpa hpb ⊢
    intro hab
    rcases y.isPrime.mem_or_mem hab with h | h
    · exact hpa h
    · exact hpb h
  · intro hp
    obtain ⟨y, rfl⟩ := range_awayChart_subset 𝒜 U _ _ _ hp
    rw [affineι_mem_range_awayChart_iff] at hp
    rw [affineι_mem_range_awayChart_iff, affineι_mem_range_awayChart_iff]
    exact ⟨fun h ↦ hp (Ideal.mul_mem_right _ _ h), fun h ↦ hp (Ideal.mul_mem_left _ _ h)⟩

/-- The intersection of `D₊(a)` over `U` and `D₊(b)` over `V` is `D₊(a|_W b|_W)` over an affine
open `W` with `W = U ∩ V`. -/
theorem range_awayChart_inf {U V W : X.affineOpens} (hWU : W ≤ U) (hWV : W ≤ V)
    (hW : U.1 ⊓ V.1 ≤ W.1) (a : 𝒜.ring U) (b : 𝒜.ring V) {d e : ℕ}
    (ha : a ∈ 𝒜.grading U d) (hb : b ∈ 𝒜.grading V e) (hd : 0 < d) (he : 0 < e) :
    (awayChart 𝒜 U a ha hd).opensRange ⊓ (awayChart 𝒜 V b hb he).opensRange =
      (awayChart 𝒜 W (𝒜.map hWU a * 𝒜.map hWV b)
        (SetLike.mul_mem_graded (map_mem_grading 𝒜 hWU ha) (map_mem_grading 𝒜 hWV hb))
        (by omega)).opensRange := by
  rw [← range_awayChart_inf_same 𝒜 W _ _ (map_mem_grading 𝒜 hWU ha) (map_mem_grading 𝒜 hWV hb)
    hd he, ← range_awayChart_inf_preimage 𝒜 hWU a ha hd,
    ← range_awayChart_inf_preimage 𝒜 hWV b hb he]
  have hU := range_awayChart_le_preimage 𝒜 U a ha hd
  have hV := range_awayChart_le_preimage 𝒜 V b hb he
  have hUV : toBase X 𝒜 ⁻¹ᵁ U.1 ⊓ toBase X 𝒜 ⁻¹ᵁ V.1 ≤ toBase X 𝒜 ⁻¹ᵁ W.1 :=
    fun p hp ↦ hW hp
  apply le_antisymm
  · exact le_inf (le_inf inf_le_left ((inf_le_inf hU hV).trans hUV))
      (le_inf inf_le_right ((inf_le_inf hU hV).trans hUV))
  · exact inf_le_inf inf_le_left inf_le_left

end RelativeProj

/-! ### The ratio unit `t / s` in `(A)_(st)` -/

section RatioUnit

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {𝒢 : ℕ → Submodule R S}
  [GradedAlgebra 𝒢]

/-- The square of a degree-one element has degree `1 • (1 + 1)`, the degree of a numerator
over the first power of a degree-two denominator. -/
theorem sq_mem_one_smul_two {t : S} (ht : t ∈ 𝒢 1) : t ^ 2 ∈ 𝒢 (1 • (1 + 1)) := by
  have := SetLike.pow_mem_graded 2 ht
  simpa using this

/-- For homogeneous elements `s, t` of degree one, the unit `t / s = t² / (st)` of the
homogeneous localisation `(A)_(st)`, with inverse `s / t = s² / (st)`. -/
def ratioUnit {s t : S} (hs : s ∈ 𝒢 1) (ht : t ∈ 𝒢 1) : (Away 𝒢 (s * t))ˣ where
  val := Away.mk 𝒢 (SetLike.mul_mem_graded hs ht) 1 (t ^ 2) (sq_mem_one_smul_two ht)
  inv := Away.mk 𝒢 (SetLike.mul_mem_graded hs ht) 1 (s ^ 2) (sq_mem_one_smul_two hs)
  val_inv := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk,
      HomogeneousLocalization.val_one, Localization.mk_mul, ← Localization.mk_one,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one]; ring⟩
  inv_val := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk,
      HomogeneousLocalization.val_one, Localization.mk_mul, ← Localization.mk_one,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one]; ring⟩

/-- The value of `ratioUnit` is the fraction `t² / (st)`. -/
theorem ratioUnit_val {s t : S} (hs : s ∈ 𝒢 1) (ht : t ∈ 𝒢 1) :
    (ratioUnit hs ht : Away 𝒢 (s * t)) =
      Away.mk 𝒢 (SetLike.mul_mem_graded hs ht) 1 (t ^ 2) (sq_mem_one_smul_two ht) :=
  rfl

/-- The ratio unit `s / s` is `1`. -/
theorem ratioUnit_self {s : S} (hs hs' : s ∈ 𝒢 1) : ratioUnit hs hs' = 1 := by
  apply Units.ext
  apply HomogeneousLocalization.val_injective
  rw [ratioUnit_val, Away.val_mk, Units.val_one, HomogeneousLocalization.val_one,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one]; ring⟩

end RatioUnit

/-! ### The tautological line bundle -/

namespace GradedBundleData

open RelativeProj IntersectionTheory

attribute [local instance] MvPolynomial.gradedAlgebra

/- As in `RelativeProj`, the index type of Mathlib's directed affine cover is definitionally,
but not reducibly, the type of affine opens. -/
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : GradedBundleData X ι)

/-- The index type of the standard affine cover of `P(E ⊕ 1)`: a trivialising chart `j` of the
bundle and a homogeneous coordinate `i : Option ι` (`none` being the extra coordinate `t`). -/
abbrev TautIndex : Type u := 𝓔.bundle.J × Option ι

/-- The homogeneous coordinate `x_i` over the trivialising chart `j`, a degree-one element of
the homogenised graded algebra `𝒜[t]` over `U_j` (the image of `X i` under `chartGradedInv`). -/
def homogCoord (j : 𝓔.bundle.J) (i : Option ι) : 𝓔.homogData.ring (𝓔.bundle.chart j) :=
  𝓔.chartGradedInv j (MvPolynomial.X i)

/-- The homogeneous coordinates have degree one. -/
theorem homogCoord_mem (j : 𝓔.bundle.J) (i : Option ι) :
    𝓔.homogCoord j i ∈ 𝓔.homogData.grading (𝓔.bundle.chart j) 1 :=
  (𝓔.chartGradedInv j).map_mem
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _))

/-- The coordinate `x_a` restricted to an affine open `V` contained in the chart of `a`. -/
def homogCoordAt (a : 𝓔.TautIndex) (V : X.affineOpens) (h : V ≤ 𝓔.bundle.chart a.1) :
    𝓔.homogData.ring V :=
  𝓔.homogData.map h (𝓔.homogCoord a.1 a.2)

/-- The restricted homogeneous coordinates have degree one. -/
theorem homogCoordAt_mem (a : 𝓔.TautIndex) (V : X.affineOpens) (h : V ≤ 𝓔.bundle.chart a.1) :
    𝓔.homogCoordAt a V h ∈ 𝓔.homogData.grading V 1 :=
  map_mem_grading _ h (𝓔.homogCoord_mem a.1 a.2)

/-- Restricting a restricted coordinate further is restricting it in one step. -/
theorem map_homogCoordAt (a : 𝓔.TautIndex) {U V : X.affineOpens} (h : U ≤ V)
    (hV : V ≤ 𝓔.bundle.chart a.1) :
    𝓔.homogData.map h (𝓔.homogCoordAt a V hV) = 𝓔.homogCoordAt a U (h.trans hV) := by
  rw [homogCoordAt, homogCoordAt, 𝓔.homogData.map_comp h hV]
  rfl

/-- The chart `D₊(x_a) ≅ Spec (𝒜[t](U_j))_(x_i)` of `P(E ⊕ 1)`, for `a = (j, i)`. -/
def tautChart (a : 𝓔.TautIndex) :
    Spec (.of (Away (𝓔.homogData.grading (𝓔.bundle.chart a.1)) (𝓔.homogCoord a.1 a.2))) ⟶
      𝓔.projectiveCompletion :=
  awayChart 𝓔.homogData (𝓔.bundle.chart a.1) (𝓔.homogCoord a.1 a.2)
    (𝓔.homogCoord_mem a.1 a.2) one_pos

/-- The charts `tautChart` are open immersions. -/
instance (a : 𝓔.TautIndex) : IsOpenImmersion (𝓔.tautChart a) := by
  unfold tautChart
  infer_instance

/-- The affine open `D₊(x_a)` of `P(E ⊕ 1)`. -/
def tautOpen (a : 𝓔.TautIndex) : 𝓔.projectiveCompletion.affineOpens :=
  ⟨(𝓔.tautChart a).opensRange, isAffineOpen_opensRange _⟩

variable (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

/-- The affine open `U_j ∩ U_{j'}` of `X` below two charts `a = (j, i)`, `b = (j', i')`. -/
def overlapBase (a b : 𝓔.TautIndex) : X.affineOpens :=
  ⟨(𝓔.bundle.chart a.1).1 ⊓ (𝓔.bundle.chart b.1).1, hX _ _⟩

/-- `U_j ∩ U_{j'} ≤ U_j`. -/
theorem overlapBase_le_left (a b : 𝓔.TautIndex) :
    𝓔.overlapBase hX a b ≤ 𝓔.bundle.chart a.1 :=
  (inf_le_left : (𝓔.bundle.chart a.1).1 ⊓ (𝓔.bundle.chart b.1).1 ≤ _)

/-- `U_j ∩ U_{j'} ≤ U_{j'}`. -/
theorem overlapBase_le_right (a b : 𝓔.TautIndex) :
    𝓔.overlapBase hX a b ≤ 𝓔.bundle.chart b.1 :=
  (inf_le_right : (𝓔.bundle.chart a.1).1 ⊓ (𝓔.bundle.chart b.1).1 ≤ _)

/-- The degree-two element `x_a x_b` over `U_j ∩ U_{j'}`. -/
def overlapElem (a b : 𝓔.TautIndex) : 𝓔.homogData.ring (𝓔.overlapBase hX a b) :=
  𝓔.homogCoordAt a _ (𝓔.overlapBase_le_left hX a b) *
    𝓔.homogCoordAt b _ (𝓔.overlapBase_le_right hX a b)

/-- `x_a x_b` has degree two. -/
theorem overlapElem_mem (a b : 𝓔.TautIndex) :
    𝓔.overlapElem hX a b ∈ 𝓔.homogData.grading (𝓔.overlapBase hX a b) (1 + 1) :=
  SetLike.mul_mem_graded (𝓔.homogCoordAt_mem a _ _) (𝓔.homogCoordAt_mem b _ _)

/-- The chart `D₊(x_a x_b)` over `U_j ∩ U_{j'}`, whose image is `D₊(x_a) ∩ D₊(x_b)`. -/
def overlapChart (a b : 𝓔.TautIndex) :
    Spec (.of (Away (𝓔.homogData.grading (𝓔.overlapBase hX a b)) (𝓔.overlapElem hX a b))) ⟶
      𝓔.projectiveCompletion :=
  awayChart 𝓔.homogData (𝓔.overlapBase hX a b) (𝓔.overlapElem hX a b)
    (𝓔.overlapElem_mem hX a b) (by norm_num)

/-- The overlap charts are open immersions. -/
instance (a b : 𝓔.TautIndex) : IsOpenImmersion (𝓔.overlapChart hX a b) := by
  unfold overlapChart
  infer_instance

/-- The image of `D₊(x_a x_b)` over `U_j ∩ U_{j'}` is `D₊(x_a) ∩ D₊(x_b)`. -/
theorem opensRange_overlapChart (a b : 𝓔.TautIndex) :
    (𝓔.overlapChart hX a b).opensRange =
      ((𝓔.tautOpen a : 𝓔.projectiveCompletion.Opens) ⊓ (𝓔.tautOpen b :)) :=
  (range_awayChart_inf 𝓔.homogData (𝓔.overlapBase_le_left hX a b)
    (𝓔.overlapBase_le_right hX a b) le_rfl _ _ (𝓔.homogCoord_mem a.1 a.2)
    (𝓔.homogCoord_mem b.1 b.2) one_pos one_pos).symm

/-- The transition unit `x_b / x_a` of `O(1)` on `D₊(x_a) ∩ D₊(x_b)`. -/
def tautTransition (a b : 𝓔.TautIndex) :
    Γ(𝓔.projectiveCompletion,
      (𝓔.tautOpen a : 𝓔.projectiveCompletion.Opens) ⊓ (𝓔.tautOpen b :))ˣ :=
  Units.map (sectionsEquiv (𝓔.overlapChart hX a b) _
      (𝓔.opensRange_overlapChart hX a b)).symm.toMonoidHom
    (ratioUnit (𝓔.homogCoordAt_mem a _ _) (𝓔.homogCoordAt_mem b _ _))

/-- Read through the chart `D₊(x_a x_b)`, the transition unit is `x_b² / (x_a x_b)`. -/
theorem sectionsToRing_tautTransition (a b : 𝓔.TautIndex) :
    sectionsToRing (𝓔.overlapChart hX a b) _ (𝓔.opensRange_overlapChart hX a b).le
        (𝓔.tautTransition hX a b : Γ(𝓔.projectiveCompletion, _)) =
      Away.mk _ (𝓔.overlapElem_mem hX a b) 1
        (𝓔.homogCoordAt b _ (𝓔.overlapBase_le_right hX a b) ^ 2)
        (sq_mem_one_smul_two (𝓔.homogCoordAt_mem b _ _)) :=
  (sectionsEquiv (𝓔.overlapChart hX a b) _ (𝓔.opensRange_overlapChart hX a b)).apply_symm_apply _

/-- The transition unit of a chart with itself is `1`. -/
theorem tautTransition_self (a : 𝓔.TautIndex) : 𝓔.tautTransition hX a a = 1 := by
  rw [tautTransition, ratioUnit_self, map_one]

/-- The affine open `U_j ∩ U_{j'} ∩ U_{j''}` of `X` below three charts. -/
def tripleBase (a b c : 𝓔.TautIndex) : X.affineOpens :=
  ⟨(𝓔.overlapBase hX a b).1 ⊓ (𝓔.bundle.chart c.1).1, hX _ _⟩

/-- `U_j ∩ U_{j'} ∩ U_{j''} ≤ U_j ∩ U_{j'}`. -/
theorem tripleBase_le_ab (a b c : 𝓔.TautIndex) :
    𝓔.tripleBase hX a b c ≤ 𝓔.overlapBase hX a b :=
  (inf_le_left : (𝓔.overlapBase hX a b).1 ⊓ (𝓔.bundle.chart c.1).1 ≤ _)

/-- `U_j ∩ U_{j'} ∩ U_{j''} ≤ U_{j'} ∩ U_{j''}`. -/
theorem tripleBase_le_bc (a b c : 𝓔.TautIndex) :
    𝓔.tripleBase hX a b c ≤ 𝓔.overlapBase hX b c :=
  fun _ hx ↦ ⟨hx.1.2, hx.2⟩

/-- `U_j ∩ U_{j'} ∩ U_{j''} ≤ U_j ∩ U_{j''}`. -/
theorem tripleBase_le_ac (a b c : 𝓔.TautIndex) :
    𝓔.tripleBase hX a b c ≤ 𝓔.overlapBase hX a c :=
  fun _ hx ↦ ⟨hx.1.1, hx.2⟩

/-- `U_j ∩ U_{j'} ∩ U_{j''} ≤ U_j`. -/
theorem tripleBase_le_a (a b c : 𝓔.TautIndex) :
    𝓔.tripleBase hX a b c ≤ 𝓔.bundle.chart a.1 :=
  (𝓔.tripleBase_le_ab hX a b c).trans (𝓔.overlapBase_le_left hX a b)

/-- `U_j ∩ U_{j'} ∩ U_{j''} ≤ U_{j'}`. -/
theorem tripleBase_le_b (a b c : 𝓔.TautIndex) :
    𝓔.tripleBase hX a b c ≤ 𝓔.bundle.chart b.1 :=
  (𝓔.tripleBase_le_ab hX a b c).trans (𝓔.overlapBase_le_right hX a b)

/-- `U_j ∩ U_{j'} ∩ U_{j''} ≤ U_{j''}`. -/
theorem tripleBase_le_c (a b c : 𝓔.TautIndex) :
    𝓔.tripleBase hX a b c ≤ 𝓔.bundle.chart c.1 :=
  (inf_le_right : (𝓔.overlapBase hX a b).1 ⊓ (𝓔.bundle.chart c.1).1 ≤ _)

/-- The degree-three element `x_a x_b x_c` over `U_j ∩ U_{j'} ∩ U_{j''}`. -/
def tripleElem (a b c : 𝓔.TautIndex) : 𝓔.homogData.ring (𝓔.tripleBase hX a b c) :=
  𝓔.homogData.map (𝓔.tripleBase_le_ab hX a b c) (𝓔.overlapElem hX a b) *
    𝓔.homogCoordAt c _ (𝓔.tripleBase_le_c hX a b c)

/-- `x_a x_b x_c` has degree three. -/
theorem tripleElem_mem (a b c : 𝓔.TautIndex) :
    𝓔.tripleElem hX a b c ∈ 𝓔.homogData.grading (𝓔.tripleBase hX a b c) (1 + 1 + 1) :=
  SetLike.mul_mem_graded (map_mem_grading _ _ (𝓔.overlapElem_mem hX a b))
    (𝓔.homogCoordAt_mem c _ _)

/-- `tripleElem` is the product of the three restricted coordinates. -/
theorem tripleElem_eq (a b c : 𝓔.TautIndex) :
    𝓔.tripleElem hX a b c = 𝓔.homogCoordAt a _ (𝓔.tripleBase_le_a hX a b c) *
      𝓔.homogCoordAt b _ (𝓔.tripleBase_le_b hX a b c) *
        𝓔.homogCoordAt c _ (𝓔.tripleBase_le_c hX a b c) := by
  rw [tripleElem, overlapElem, map_mul, map_homogCoordAt, map_homogCoordAt]

/-- `x_a x_b x_c` as the restriction of `x_a x_b` times `x_c`. -/
theorem tripleElem_eq_ab (a b c : 𝓔.TautIndex) :
    𝓔.tripleElem hX a b c = 𝓔.homogData.map (𝓔.tripleBase_le_ab hX a b c)
      (𝓔.overlapElem hX a b) * 𝓔.homogCoordAt c _ (𝓔.tripleBase_le_c hX a b c) :=
  rfl

/-- `x_a x_b x_c` as the restriction of `x_b x_c` times `x_a`. -/
theorem tripleElem_eq_bc (a b c : 𝓔.TautIndex) :
    𝓔.tripleElem hX a b c = 𝓔.homogData.map (𝓔.tripleBase_le_bc hX a b c)
      (𝓔.overlapElem hX b c) * 𝓔.homogCoordAt a _ (𝓔.tripleBase_le_a hX a b c) := by
  rw [tripleElem_eq, overlapElem, map_mul, map_homogCoordAt, map_homogCoordAt]
  ring

/-- `x_a x_b x_c` as the restriction of `x_a x_c` times `x_b`. -/
theorem tripleElem_eq_ac (a b c : 𝓔.TautIndex) :
    𝓔.tripleElem hX a b c = 𝓔.homogData.map (𝓔.tripleBase_le_ac hX a b c)
      (𝓔.overlapElem hX a c) * 𝓔.homogCoordAt b _ (𝓔.tripleBase_le_b hX a b c) := by
  rw [tripleElem_eq, overlapElem, map_mul, map_homogCoordAt, map_homogCoordAt]
  ring

/-- The chart `D₊(x_a x_b x_c)` over `U_j ∩ U_{j'} ∩ U_{j''}`. -/
def tripleChart (a b c : 𝓔.TautIndex) :
    Spec (.of (Away (𝓔.homogData.grading (𝓔.tripleBase hX a b c)) (𝓔.tripleElem hX a b c))) ⟶
      𝓔.projectiveCompletion :=
  awayChart 𝓔.homogData (𝓔.tripleBase hX a b c) (𝓔.tripleElem hX a b c)
    (𝓔.tripleElem_mem hX a b c) (by norm_num)

/-- The triple overlap charts are open immersions. -/
instance (a b c : 𝓔.TautIndex) : IsOpenImmersion (𝓔.tripleChart hX a b c) := by
  unfold tripleChart
  infer_instance

/-- The image of `D₊(x_a x_b x_c)` is the triple intersection of the `D₊(x_·)`. -/
theorem opensRange_tripleChart (a b c : 𝓔.TautIndex) :
    (𝓔.tripleChart hX a b c).opensRange =
      ((𝓔.tautOpen a : 𝓔.projectiveCompletion.Opens) ⊓ (𝓔.tautOpen b :)) ⊓ (𝓔.tautOpen c :) := by
  rw [← opensRange_overlapChart]
  exact (range_awayChart_inf 𝓔.homogData (𝓔.tripleBase_le_ab hX a b c)
    (𝓔.tripleBase_le_c hX a b c) le_rfl _ _ (𝓔.overlapElem_mem hX a b)
    (𝓔.homogCoord_mem c.1 c.2) (by norm_num) one_pos).symm

/-- The triple overlap chart factors through the overlap chart of `a, b`, via restriction
and localisation of homogeneous localisations. -/
theorem tripleChart_eq_ab (a b c : 𝓔.TautIndex) :
    𝓔.tripleChart hX a b c = Spec.map (CommRingCat.ofHom
      ((awayMap _ (𝓔.homogCoordAt_mem c _ (𝓔.tripleBase_le_c hX a b c))
          (𝓔.tripleElem_eq_ab hX a b c)).comp
        (Away.map (𝓔.homogData.map (𝓔.tripleBase_le_ab hX a b c)) (𝓔.overlapElem hX a b)))) ≫
      𝓔.overlapChart hX a b :=
  awayChart_map_mul _ _ _ _ _ _ _ _ _ _ _

/-- The triple overlap chart factors through the overlap chart of `b, c`. -/
theorem tripleChart_eq_bc (a b c : 𝓔.TautIndex) :
    𝓔.tripleChart hX a b c = Spec.map (CommRingCat.ofHom
      ((awayMap _ (𝓔.homogCoordAt_mem a _ (𝓔.tripleBase_le_a hX a b c))
          (𝓔.tripleElem_eq_bc hX a b c)).comp
        (Away.map (𝓔.homogData.map (𝓔.tripleBase_le_bc hX a b c)) (𝓔.overlapElem hX b c)))) ≫
      𝓔.overlapChart hX b c :=
  awayChart_map_mul _ _ _ _ _ _ _ _ _ _ _

/-- The triple overlap chart factors through the overlap chart of `a, c`. -/
theorem tripleChart_eq_ac (a b c : 𝓔.TautIndex) :
    𝓔.tripleChart hX a b c = Spec.map (CommRingCat.ofHom
      ((awayMap _ (𝓔.homogCoordAt_mem b _ (𝓔.tripleBase_le_b hX a b c))
          (𝓔.tripleElem_eq_ac hX a b c)).comp
        (Away.map (𝓔.homogData.map (𝓔.tripleBase_le_ac hX a b c)) (𝓔.overlapElem hX a c)))) ≫
      𝓔.overlapChart hX a c :=
  awayChart_map_mul _ _ _ _ _ _ _ _ _ _ _

/-- The cocycle condition for the transition units `x_b / x_a`. -/
theorem tautTransition_cocycle (a b c : 𝓔.TautIndex) :
    resUnit inf_le_left (𝓔.tautTransition hX a b) *
        resUnit (inf_le_inf inf_le_right (le_refl ((𝓔.tautOpen c :
          𝓔.projectiveCompletion.Opens)))) (𝓔.tautTransition hX b c) =
      resUnit (inf_le_inf inf_le_left (le_refl ((𝓔.tautOpen c :
          𝓔.projectiveCompletion.Opens)))) (𝓔.tautTransition hX a c) := by
  apply Units.ext
  apply (sectionsToRing_bijective (𝓔.tripleChart hX a b c) _
    (𝓔.opensRange_tripleChart hX a b c)).injective
  simp only [Units.val_mul, resUnit, Units.coe_map, map_mul, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  rw [sectionsToRing_res (𝓔.overlapChart hX a b) (𝓔.tripleChart hX a b c) _
      (𝓔.tripleChart_eq_ab hX a b c) (𝓔.opensRange_overlapChart hX a b).le,
    sectionsToRing_res (𝓔.overlapChart hX b c) (𝓔.tripleChart hX a b c) _
      (𝓔.tripleChart_eq_bc hX a b c) (𝓔.opensRange_overlapChart hX b c).le,
    sectionsToRing_res (𝓔.overlapChart hX a c) (𝓔.tripleChart hX a b c) _
      (𝓔.tripleChart_eq_ac hX a b c) (𝓔.opensRange_overlapChart hX a c).le,
    sectionsToRing_tautTransition, sectionsToRing_tautTransition, sectionsToRing_tautTransition]
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, Away.map_mk, awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, pow_one, map_pow, map_homogCoordAt]
  rw [tripleElem_eq]
  ring

omit hX in
/-- Comparison with the standard charts: the image of `D₊(x_a)`, `a = (j, i)`, is the image of
the basic open `D₊(X i)` of `Proj Γ(U_j)[x_k : k ∈ Option ι]` under the identification
`chartProjIso j` of the latter with the part of `P(E ⊕ 1)` over `U_j`. -/
theorem range_tautChart (a : 𝓔.TautIndex) :
    Set.range (𝓔.tautChart a) =
      Set.range (Proj.awayι (MvPolynomial.homogeneousSubmodule (Option ι)
          Γ(X, (𝓔.bundle.chart a.1).1)) (MvPolynomial.X a.2)
          ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _))
          one_pos ≫ (𝓔.chartProjIso a.1).hom ≫ affineι X 𝓔.homogData (𝓔.bundle.chart a.1)) := by
  have hX' : 𝓔.chartGraded a.1 (𝓔.homogCoord a.1 a.2) = MvPolynomial.X a.2 :=
    GradedRingHom.congr_fun (𝓔.chartGraded_comp_chartGradedInv a.1) _
  -- membership of `chartProjIso.hom w` in `D₊(x_a)` is membership of `w` in `D₊(X i)`
  have key : ∀ w, 𝓔.homogCoord a.1 a.2 ∉ ((𝓔.chartProjIso a.1).hom w).asHomogeneousIdeal ↔
      MvPolynomial.X a.2 ∉ w.asHomogeneousIdeal := by
    intro w
    rw [← hX']
    exact Iff.rfl
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    have hy := (affineι_mem_range_awayChart_iff 𝓔.homogData _
      ((Proj.awayι _ _ (𝓔.homogCoord_mem a.1 a.2) one_pos) z) _ _ one_pos).mp
      ⟨z, rfl⟩
    set y := (Proj.awayι _ _ (𝓔.homogCoord_mem a.1 a.2) one_pos) z
    have hw : (𝓔.chartProjIso a.1).hom ((𝓔.chartProjIso a.1).inv y) = y := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [← hw, key, ← mem_range_awayι_iff _ _
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _))
      one_pos] at hy
    obtain ⟨w, hw'⟩ := hy
    refine ⟨w, ?_⟩
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw', hw]
    rfl
  · rintro ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, tautChart,
      affineι_mem_range_awayChart_iff, key, ← mem_range_awayι_iff _ _
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _))
        one_pos]
    exact ⟨w, rfl⟩

omit hX in
/-- The opens `D₊(x_a)` of `tautological` are the images of the charts `completionChart a` of
`P(E ⊕ 1)` (the affine charts `completionCharts`). -/
theorem opensRange_completionChart (a : 𝓔.TautIndex) :
    (𝓔.completionChart a).opensRange = (𝓔.tautOpen a : 𝓔.projectiveCompletion.Opens) := by
  ext1
  change Set.range ((Spec.map (CommRingCat.ofHom (dehomAt _ a.2).toRingHom) ≫
    Proj.awayι _ (MvPolynomial.X a.2) (X_mem_homogeneousSubmodule_one a.2) one_pos) ≫
      (𝓔.chartProjIso a.1).hom ≫ affineι X 𝓔.homogData (𝓔.bundle.chart a.1)) =
    Set.range (𝓔.tautChart a)
  rw [range_tautChart, Category.assoc]
  exact congrArg (fun O : 𝓔.projectiveCompletion.Opens ↦ (O : Set 𝓔.projectiveCompletion))
    (Scheme.Hom.opensRange_comp_of_isIso _ _)

omit hX in
/-- The opens `D₊(x_a)` cover `P(E ⊕ 1)` (from the covering by the charts `completionChart`). -/
theorem exists_mem_tautOpen (p : 𝓔.projectiveCompletion) :
    ∃ a : 𝓔.TautIndex, p ∈ (𝓔.tautOpen a : 𝓔.projectiveCompletion.Opens) := by
  obtain ⟨k, hk⟩ := 𝓔.exists_mem_range_completionChart p
  exact ⟨k, 𝓔.opensRange_completionChart k ▸ hk⟩

/-- The tautological line bundle `O(1)` on the projective completion `P(E ⊕ 1)`, as a Čech
cocycle: on the cover by the affine opens `D₊(x_a)` (`a = (j, i)`: a trivialising chart `U_j`
of the bundle and a homogeneous coordinate `x_i`, `i : Option ι`), the transition unit between
the charts `a` and `b` is `x_b / x_a`, computed over the affine open `U_j ∩ U_{j'}` of `X`
(this is where the hypothesis `hX` that intersections of affine opens are affine is used).

With the convention of `LineBundleData` (coordinates transform by `coord_a = g a b * coord_b`),
the compatible family of coordinates `x_none / x_a` is regular in every chart; informally this is
`O(1)` and not its dual (see the module docstring). -/
def tautological : LineBundleData 𝓔.projectiveCompletion where
  J := 𝓔.TautIndex
  U := 𝓔.tautOpen
  covers := 𝓔.exists_mem_tautOpen
  g := 𝓔.tautTransition hX
  g_self := 𝓔.tautTransition_self hX
  g_cocycle := 𝓔.tautTransition_cocycle hX

/-- The index type of `tautological`. -/
@[simp]
theorem tautological_J : (𝓔.tautological hX).J = 𝓔.TautIndex :=
  rfl

/-- The opens of `tautological` are the images `D₊(x_a)` of the charts `tautChart a`. -/
theorem tautological_U (a : 𝓔.TautIndex) :
    ((𝓔.tautological hX).U a : 𝓔.projectiveCompletion.Opens) = (𝓔.tautChart a).opensRange :=
  rfl

/-- The transition units of `tautological`: read through the chart `D₊(x_a x_b)` of the overlap
over `U_j ∩ U_{j'}`, the transition unit between `a` and `b` is `x_b² / (x_a x_b) = x_b / x_a`. -/
theorem tautological_g (a b : 𝓔.TautIndex) :
    sectionsToRing (𝓔.overlapChart hX a b) _ (𝓔.opensRange_overlapChart hX a b).le
        ((𝓔.tautological hX).g a b).val =
      Away.mk _ (𝓔.overlapElem_mem hX a b) 1
        (𝓔.homogCoordAt b _ (𝓔.overlapBase_le_right hX a b) ^ 2)
        (sq_mem_one_smul_two (𝓔.homogCoordAt_mem b _ _)) :=
  𝓔.sectionsToRing_tautTransition hX a b

end GradedBundleData

end

end GromovWitten.AlgebraicGeometry
