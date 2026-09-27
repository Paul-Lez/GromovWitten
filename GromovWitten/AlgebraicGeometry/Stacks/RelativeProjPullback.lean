/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import Mathlib.RingTheory.GradedAlgebra.TensorProduct
import GromovWitten.AlgebraicGeometry.Stacks.RelativeProjStack

/-!
# Base change of a relative `Proj` along an affine test morphism

`RelativeProj.lean` glues the relative `Proj` of a quasi-coherent graded algebra
`𝒜 : GradedAlgebraData X` from the affine `Proj`s of the graded rings `𝒜.ring U`, and
`ProjBaseChange.lean` proves that `Proj` commutes with arbitrary base change *for an already
given* graded ring map exhibiting the target as a degreewise base change.  This file supplies
the missing construction: the degreewise base change itself.

For a graded algebra `𝒜` over `A` and any `A`-algebra `B`, the family
`fun i ↦ (𝒜 i).baseChange B` of `B`-submodules of `B ⊗[A] S` is a graded `B`-algebra
(`GradedAlgebra.baseChange`), and `Algebra.TensorProduct.includeRight` is a graded ring map
`𝒜 → (𝒜 · |>.baseChange B)` over `A → B` which is a base change in every degree
(`baseChangeHom_isBaseChange`); the key point is that each `𝒜 n` is an `A`-module direct summand
of `S`, so that `B ⊗[A] 𝒜 n → B ⊗[A] S` stays injective (`baseChange_subtype_injective`).
Feeding this into `ProjBaseChange.isPullback_map` gives the cartesian square
`isPullback_projMap_baseChange` of `Proj`s over the spectra of the base rings.

Pasting that square with the affine-chart square `RelativeProj.isPullback_affine` of the relative
`Proj` identifies the fibre product of `toBase X 𝒜` with an affine test morphism landing in a
chart: for `U : X.affineOpens` and a `Γ(X, U)`-algebra `B`, the `Proj` of the base-changed graded
algebra is the pullback of `toBase X 𝒜` along `chartHom X U B : Spec B ⟶ X`
(`isPullback_affine_chart`, `projPullbackIso`), and it carries the structure morphism
`projection` to `Spec B`.  This is the `Proj` analogue of `RelativeSpecStack`'s
`isPullback_relativeSpecPullback`, restricted to affine test objects factoring through one chart:
unlike the affine case there is no canonical graded algebra attached to the base change of
`toBase X 𝒜` over a general test scheme, so the pulled-back data is produced chart by chart.
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace GromovWitten.AlgebraicGeometry

open ProjBaseChange GlobalBlowup ReesBlowupOfEq

universe u

noncomputable section

namespace RelativeProjPullback

section Degreewise

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  (𝒜 : ℕ → Submodule A S) [GradedAlgebra 𝒜] (B : Type u) [CommRing B] [Algebra A B]

/-- The projection of a graded algebra onto its degree-`n` part, as a linear map. -/
def gradeProj (n : ℕ) : S →ₗ[A] 𝒜 n :=
  (DirectSum.component A ℕ (fun i ↦ (𝒜 i : Submodule A S)) n) ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

/-- The degree-`n` part of a graded algebra is an `A`-module direct summand. -/
theorem gradeProj_comp_subtype (n : ℕ) :
    (gradeProj 𝒜 n).comp (𝒜 n).subtype = LinearMap.id := by
  ext x
  simp [gradeProj]

/-- Base change preserves the injectivity of the inclusion of a graded piece, because that
inclusion is a split injection of `A`-modules. -/
theorem baseChange_subtype_injective (n : ℕ) :
    Function.Injective ((𝒜 n).subtype.baseChange B) := by
  have h1 : ((gradeProj 𝒜 n).baseChange B).comp ((𝒜 n).subtype.baseChange B) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, gradeProj_comp_subtype, LinearMap.baseChange_id]
  refine Function.LeftInverse.injective (g := (gradeProj 𝒜 n).baseChange B) fun x ↦ ?_
  simpa using LinearMap.congr_fun h1 x

/-- The graded ring map from a graded algebra to its base change along `A → B`. -/
def baseChangeGradedHom : 𝒜 →+*ᵍ (fun i ↦ (𝒜 i).baseChange B) where
  __ := (Algebra.TensorProduct.includeRight : S →ₐ[A] B ⊗[A] S).toRingHom
  map_mem hx := Submodule.tmul_mem_baseChange_of_mem 1 hx

/-- The base change of a graded algebra along `A → B`, as a graded map over the base rings. -/
def baseChangeHom : GradedHomOver 𝒜 (fun i ↦ (𝒜 i).baseChange B) where
  __ := baseChangeGradedHom 𝒜 B
  commutes' a := (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := S)).commutes a

omit [GradedAlgebra 𝒜] in
/-- In degree `n` the comparison map of `baseChangeHom` is the base change of the inclusion of
the degree-`n` part, up to the commutativity of the tensor product. -/
theorem baseChangeHom_degreeMap (n : ℕ) : (baseChangeHom 𝒜 B).degreeMap n
    = ((𝒜 n).subtype.baseChange B).restrictScalars A ∘ₗ
      (TensorProduct.comm A (𝒜 n) B).toLinearMap := by
  apply TensorProduct.ext'
  intro x b
  simp [GradedHomOver.degreeMap_tmul, baseChangeHom, baseChangeGradedHom,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- The tensor product exhibits `fun i ↦ (𝒜 i).baseChange B` as the degreewise base change of
`𝒜` along `A → B`. -/
theorem baseChangeHom_isBaseChange : (baseChangeHom 𝒜 B).IsBaseChange where
  injective n := by
    rw [baseChangeHom_degreeMap]
    exact (baseChange_subtype_injective 𝒜 B n).comp (TensorProduct.comm A (𝒜 n) B).injective
  range_eq n := by
    rw [baseChangeHom_degreeMap, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    rfl

/-- **`Proj` commutes with base change of the base ring.**  For any `A`-algebra `B`, the `Proj` of
the degreewise base change of `𝒜` to `B` is the base change of `Proj 𝒜` along
`Spec B ⟶ Spec A`. -/
theorem isPullback_projMap_baseChange :
    IsPullback (Proj.map (baseChangeHom 𝒜 B).toGradedRingHom
        (baseChangeHom_isBaseChange 𝒜 B).irrelevant_le)
      (projection (fun i ↦ (𝒜 i).baseChange B)) (projection 𝒜)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  isPullback_map (baseChangeHom 𝒜 B) (baseChangeHom_isBaseChange 𝒜 B)

end Degreewise

section Chart

/- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
type of affine opens, and the section ring of an affine open is only definitionally the carrier of
its bundled `CommRingCat`; as in `RelativeProj.lean`, the unifier is told not to respect
transparency in this section. -/
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u}) (𝒟 : GradedAlgebraData X) (U : X.affineOpens)
  (B : Type u) [CommRing B] [Algebra Γ(X, U.1) B]

/-- The degreewise base change to a `Γ(X, U)`-algebra `B` of the graded algebra which the data
`𝒟` assigns to the affine chart `U`: the graded ring whose `Proj` is the relative `Proj` of `𝒟`
pulled back to `Spec B`. -/
abbrev pullbackGrading : ℕ → Submodule B (B ⊗[Γ(X, U.1)] 𝒟.ring U) :=
  fun i ↦ (𝒟.grading U i).baseChange B

/-- The relative `Proj` of the pulled-back graded data over the affine test scheme `Spec B`. -/
abbrev projPullback : Scheme.{u} := Proj (pullbackGrading X 𝒟 U B)

/-- The comparison morphism from the pulled-back `Proj` to the relative `Proj` of `𝒟`. -/
def projPullbackFst : projPullback X 𝒟 U B ⟶ RelativeProj.relativeProj X 𝒟 :=
  Proj.map (baseChangeHom (𝒟.grading U) B).toGradedRingHom
      (baseChangeHom_isBaseChange (𝒟.grading U) B).irrelevant_le ≫
    RelativeProj.affineι X 𝒟 U

/-- The affine test morphism `Spec B ⟶ X` attached to a `Γ(X, U)`-algebra `B`: it factors
through the chart `U`. -/
def chartHom : Spec (CommRingCat.of B) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) B)) ≫
    (isAffineOpen X U).isoSpec.inv ≫ U.1.ι

/-- The affine-chart square of the relative `Proj`, with the chart identified with the spectrum
of its section ring. -/
theorem isPullback_projection_affineι :
    IsPullback (projection (𝒟.grading U)) (RelativeProj.affineι X 𝒟 U)
      ((isAffineOpen X U).isoSpec.inv ≫ U.1.ι) (RelativeProj.toBase X 𝒟) := by
  have h := (IsPullback.of_vert_isIso (fst := projection (𝒟.grading U))
    (snd := 𝟙 (Proj (𝒟.grading U))) (f := (isAffineOpen X U).isoSpec.inv)
    (g := projection (𝒟.grading U) ≫ (isAffineOpen X U).isoSpec.inv)
    ⟨by rw [Category.id_comp]⟩).paste_vert (RelativeProj.isPullback_affine X 𝒟 U)
  rwa [Category.id_comp] at h

/-- **The fibre of a relative `Proj` over an affine test object of a chart.**  For an affine
test scheme `Spec B` mapping into the chart `U` of `X`, the `Proj` of the base-changed graded
algebra `pullbackGrading`, with its structure morphism to `Spec B`, is the pullback of the
structure morphism `toBase X 𝒟` of the relative `Proj` along the test morphism. -/
theorem isPullback_affine_chart :
    IsPullback (projection (pullbackGrading X 𝒟 U B)) (projPullbackFst X 𝒟 U B)
      (chartHom X U B) (RelativeProj.toBase X 𝒟) :=
  (isPullback_projMap_baseChange (𝒟.grading U) B).flip.paste_vert
    (isPullback_projection_affineι X 𝒟 U)

/-- `isPullback_affine_chart` in the orientation of
`RelativeSpecStack.isPullback_relativeSpecPullback`: the comparison morphism to the relative
`Proj` and the structure morphism to the test object form a cartesian square over the test
morphism. -/
theorem isPullback_projPullbackFst :
    IsPullback (projPullbackFst X 𝒟 U B) (projection (pullbackGrading X 𝒟 U B))
      (RelativeProj.toBase X 𝒟) (chartHom X U B) :=
  (isPullback_affine_chart X 𝒟 U B).flip

/-- The pulled-back `Proj` is the scheme-theoretic fibre product of the relative `Proj` with the
affine test object. -/
def projPullbackIso :
    projPullback X 𝒟 U B ≅ Limits.pullback (chartHom X U B) (RelativeProj.toBase X 𝒟) :=
  (isPullback_affine_chart X 𝒟 U B).isoPullback

/-- Any property of morphisms of schemes which is stable under base change passes from the
structure morphism of the relative `Proj` to the structure morphism of the pulled-back `Proj`
over an affine test object. -/
theorem property_projection_pullbackGrading (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (h : P (RelativeProj.toBase X 𝒟)) :
    P (projection (pullbackGrading X 𝒟 U B)) :=
  MorphismProperty.of_isPullback (isPullback_affine_chart X 𝒟 U B).flip h

/-- The pulled-back `Proj` over an affine test object is proper over it, under the hypotheses
which make the relative `Proj` proper over `X`. -/
theorem isProper_projection_pullbackGrading
    [∀ V, Algebra.FiniteType (𝒟.grading V 0) (𝒟.ring V)]
    (h0 : ∀ V, Function.Bijective (algebraMap Γ(X, V.1) (𝒟.grading V 0))) :
    IsProper (projection (pullbackGrading X 𝒟 U B)) :=
  property_projection_pullbackGrading X 𝒟 U B
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u})
    (RelativeProj.toBase_isProper X 𝒟 h0)

/-- **The universal property of the pulled-back `Proj` in stack language.**  Lifts of the affine
test morphism `chartHom X U B` through the structure morphism of the relative `Proj` — that is,
objects of the fibre of `stackProj X 𝒟` over the test object — correspond to sections over
`Spec B` of the structure morphism of the `Proj` of the pulled-back graded data. -/
def liftEquivSection :
    {h : Spec (CommRingCat.of B) ⟶ RelativeProj.relativeProj X 𝒟 //
        h ≫ RelativeProj.toBase X 𝒟 = chartHom X U B} ≃
      {s : Spec (CommRingCat.of B) ⟶ projPullback X 𝒟 U B //
        s ≫ projection (pullbackGrading X 𝒟 U B) = 𝟙 (Spec (CommRingCat.of B))} where
  toFun h := ⟨(isPullback_affine_chart X 𝒟 U B).lift (𝟙 _) h.1
      (by rw [Category.id_comp]; exact h.2.symm),
    (isPullback_affine_chart X 𝒟 U B).lift_fst _ _ _⟩
  invFun s := ⟨s.1 ≫ projPullbackFst X 𝒟 U B, by
    rw [Category.assoc, ← (isPullback_affine_chart X 𝒟 U B).w, ← Category.assoc, s.2,
      Category.id_comp]⟩
  left_inv h := Subtype.ext ((isPullback_affine_chart X 𝒟 U B).lift_snd _ _ _)
  right_inv s := Subtype.ext <| by
    dsimp only
    exact (isPullback_affine_chart X 𝒟 U B).hom_ext (by simp [s.2]) (by simp)

end Chart

section TopChart

variable (X : Scheme.{u}) (𝒟 : GradedAlgebraData X) (U : X.affineOpens)

/-- The inclusion of the top open subscheme is an isomorphism. -/
theorem isIso_ι_top : IsIso ((⊤ : X.Opens).ι) := by
  rw [← Scheme.topIso_hom]
  infer_instance

/-- If an affine open of `X` is the whole of `X`, its chart is the whole relative `Proj`.  The
hypothesis is stated as `IsIso U.1.ι` rather than `U.1 = ⊤` because instance search cannot
elaborate `𝒟.grading ⟨⊤, _⟩` (the graded structure of a chart given by an anonymous constructor
is not found); `isIso_ι_top` provides the hypothesis for `U.1 = ⊤`. -/
theorem isIso_affineι (hU : IsIso U.1.ι) : IsIso (RelativeProj.affineι X 𝒟 U) :=
  (RelativeProj.isPullback_affine X 𝒟 U).isIso_snd_of_isIso hU

/-- For an affine base scheme, the relative `Proj` of a quasi-coherent graded algebra is the
affine `Proj` of its graded ring over the whole space. -/
def relativeProjIsoProjChart (hU : IsIso U.1.ι) :
    Proj (𝒟.grading U) ≅ RelativeProj.relativeProj X 𝒟 :=
  have := isIso_affineι X 𝒟 U hU
  asIso (RelativeProj.affineι X 𝒟 U)

/-- `relativeProjIsoProjChart` identifies the structure morphisms. -/
theorem relativeProjIsoProjChart_hom_comp (hU : IsIso U.1.ι) :
    (relativeProjIsoProjChart X 𝒟 U hU).hom ≫ RelativeProj.toBase X 𝒟 =
      (projection (𝒟.grading U) ≫ (isAffineOpen X U).isoSpec.inv) ≫ U.1.ι :=
  (RelativeProj.isPullback_affine X 𝒟 U).w.symm

end TopChart

section Coherence

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  (𝒜 : ℕ → Submodule A S) [GradedAlgebra 𝒜]

/-- Base changing a graded algebra along the identity of its base ring does not change its
`Proj`. -/
def projBaseChangeIdIso : Proj (fun i ↦ (𝒜 i).baseChange A) ≅ Proj 𝒜 :=
  (isPullback_projMap_baseChange 𝒜 A).isoIsPullback _ _ (by
    have h : Spec.map (CommRingCat.ofHom (algebraMap A A)) = 𝟙 (Spec (CommRingCat.of A)) := by
      rw [show CommRingCat.ofHom (algebraMap A A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id]
    rw [h]
    exact IsPullback.of_id_fst)

/-- `projBaseChangeIdIso` is a morphism over the base. -/
theorem projBaseChangeIdIso_hom_comp :
    (projBaseChangeIdIso 𝒜).hom ≫ projection 𝒜 = projection (fun i ↦ (𝒜 i).baseChange A) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

variable (B : Type u) [CommRing B] [Algebra A B] (C : Type u) [CommRing C] [Algebra A C]
  [Algebra B C] [IsScalarTower A B C]

/-- Base changing a graded algebra to `B` and then to `C` is, for `Proj`, the same as base
changing it directly to `C`: the two cartesian squares over `Spec A` paste. -/
theorem isPullback_projMap_baseChange_comp :
    IsPullback (Proj.map (baseChangeHom (fun i ↦ (𝒜 i).baseChange B) C).toGradedRingHom
          (baseChangeHom_isBaseChange (fun i ↦ (𝒜 i).baseChange B) C).irrelevant_le ≫
        Proj.map (baseChangeHom 𝒜 B).toGradedRingHom
          (baseChangeHom_isBaseChange 𝒜 B).irrelevant_le)
      (projection (fun i ↦ ((𝒜 i).baseChange B).baseChange C)) (projection 𝒜)
      (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
  have h := (isPullback_projMap_baseChange (fun i ↦ (𝒜 i).baseChange B) C).paste_horiz
    (isPullback_projMap_baseChange 𝒜 B)
  rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq] at h

/-- The iterated base change of a graded algebra has the same `Proj` as the direct base change. -/
def projBaseChangeCompIso :
    Proj (fun i ↦ ((𝒜 i).baseChange B).baseChange C) ≅ Proj (fun i ↦ (𝒜 i).baseChange C) :=
  (isPullback_projMap_baseChange_comp 𝒜 B C).isoIsPullback _ _
    (isPullback_projMap_baseChange 𝒜 C)

/-- `projBaseChangeCompIso` is a morphism over `Spec C`. -/
theorem projBaseChangeCompIso_hom_comp :
    (projBaseChangeCompIso 𝒜 B C).hom ≫ projection (fun i ↦ (𝒜 i).baseChange C) =
      projection (fun i ↦ ((𝒜 i).baseChange B).baseChange C) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

end Coherence

end RelativeProjPullback

end

end GromovWitten.AlgebraicGeometry
