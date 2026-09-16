/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Sections of scheme morphisms

This file records the scheme-theoretic diagonal square associated to a section.  In particular,
a section of a separated morphism is a closed immersion, while a section of an unramified
finite-type morphism is an open immersion.  The latter fact is the geometric input that isolates a
section as an open-and-closed component after choosing an étale coordinate.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X S A D : Scheme.{u}}

/-! ## Pullback squares from factorizations -/

/-- If `i` is a monomorphism and `f` factors through it as `g ≫ i`, then the square whose other
side is the identity of the source is Cartesian. -/
theorem isPullback_factorThrough_mono
    {Y Z : Scheme.{u}} (f : Z ⟶ X) (i : Y ⟶ X) [Mono i]
    (g : Z ⟶ Y) (h : g ≫ i = f) :
    IsPullback g (𝟙 Z) i f := by
  refine IsPullback.mk (toCommSq := ⟨by simpa using h⟩) ⟨?_⟩
  refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
  · intro t
    exact t.snd
  · intro t
    rw [← cancel_mono i]
    simpa only [Category.assoc, h] using t.condition.symm
  · intro t
    simp
  · intro t m _ hm
    simpa using hm

/-! ## One-dimensional standard-smooth coordinates -/

/-- The canonical identification of a one-variable multivariate polynomial ring with the ordinary
polynomial ring. -/
def finOneMvPolynomialEquivPolynomial (R : Type u) [CommRing R] :
    MvPolynomial (Fin 1) R ≃ₐ[R] Polynomial R :=
  MvPolynomial.uniqueAlgEquiv R (Fin 1)

/-- A standard-smooth ring map of relative dimension one admits an étale coordinate to an ordinary
polynomial ring in one variable.  This is the algebraic coordinate used for local graph divisors. -/
theorem exists_etale_polynomial_coordinate_of_isStandardSmoothOfRelativeDimension
    {R T : Type u} [CommRing R] [CommRing T]
    {f : R →+* T} (hf : f.IsStandardSmoothOfRelativeDimension 1) :
    ∃ g : Polynomial R →+* T,
      g.comp (algebraMap R (Polynomial R)) = f ∧ g.Etale := by
  obtain ⟨g, hgf, hg⟩ := hf.exists_etale_mvPolynomial
  let e : Polynomial R ≃+* MvPolynomial (Fin 1) R :=
    (finOneMvPolynomialEquivPolynomial R).symm.toRingEquiv
  refine ⟨g.comp e.toRingHom, ?_, RingHom.Etale.respectsIso.2 g e hg⟩
  calc
    (g.comp e.toRingHom).comp (algebraMap R (Polynomial R)) =
        g.comp MvPolynomial.C := by
      ext r
      simp [e, finOneMvPolynomialEquivPolynomial]
    _ = f := hgf

/-- Every point of a morphism smooth of relative dimension one has affine source and target
neighbourhoods whose section-ring map factors through an étale map from a polynomial ring. -/
theorem SmoothOfRelativeDimension.exists_affine_etale_polynomial_coordinate
    (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] (x : X) :
    ∃ (U : S.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U) (g : Polynomial Γ(S, U) →+* Γ(X, V)),
      g.comp (algebraMap Γ(S, U) (Polynomial Γ(S, U))) = (f.appLE U V e).hom ∧
        g.Etale := by
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  have hf' : RingHom.IsStandardSmoothOfRelativeDimension 1 (f.appLE U V e).hom := hf
  obtain ⟨g, hgf, hg⟩ :=
    exists_etale_polynomial_coordinate_of_isStandardSmoothOfRelativeDimension hf'
  exact ⟨U, hU, V, hV, hxV, e, g, hgf, hg⟩

/-- The map from the source of a morphism to its self-fibre-product associated to a section:
on points it is `x ↦ (s(f(x)), x)`. -/
def sectionToDiagonalBase (f : X ⟶ S) (s : S ⟶ X) (h : s ≫ f = 𝟙 S) :
    X ⟶ pullback f f :=
  pullback.lift (f ≫ s) (𝟙 X) (by simp [Category.assoc, h])

/-- The section square with the diagonal commutes. -/
lemma section_diagonal_comm (f : X ⟶ S) (s : S ⟶ X) (h : s ≫ f = 𝟙 S) :
    s ≫ pullback.diagonal f = s ≫ sectionToDiagonalBase f s h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
      sectionToDiagonalBase, pullback.lift_fst]
    rw [← Category.assoc, h, Category.id_comp]
  · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id,
      sectionToDiagonalBase, pullback.lift_snd]

/-- A section is the base change of the diagonal along `x ↦ (s(f(x)), x)`. -/
lemma section_isPullback_diagonal (f : X ⟶ S) (s : S ⟶ X) (h : s ≫ f = 𝟙 S) :
    IsPullback s s (pullback.diagonal f) (sectionToDiagonalBase f s h) := by
  refine IsPullback.mk (toCommSq := ⟨section_diagonal_comm f s h⟩) ⟨?_⟩
  refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
  · intro t
    exact t.fst ≫ f
  · intro t
    have hc₁ := congrArg (fun k ↦ k ≫ pullback.fst f f) t.condition
    have hc₂ := congrArg (fun k ↦ k ≫ pullback.snd f f) t.condition
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
      sectionToDiagonalBase, pullback.lift_fst] at hc₁
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id,
      sectionToDiagonalBase, pullback.lift_snd] at hc₂
    rw [← hc₂] at hc₁
    exact hc₁.symm
  · intro t
    have hc₁ := congrArg (fun k ↦ k ≫ pullback.fst f f) t.condition
    have hc₂ := congrArg (fun k ↦ k ≫ pullback.snd f f) t.condition
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
      sectionToDiagonalBase, pullback.lift_fst] at hc₁
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id,
      sectionToDiagonalBase, pullback.lift_snd] at hc₂
    rw [← hc₂] at hc₁
    exact hc₁.symm.trans hc₂
  · intro t m hfst _
    rw [← hfst, Category.assoc, h, Category.comp_id]

/-- A section of a separated morphism is a closed immersion. -/
theorem isClosedImmersion_of_section_of_separated
    (f : X ⟶ S) (s : S ⟶ X) [IsSeparated f] (h : s ≫ f = 𝟙 S) :
    IsClosedImmersion s := by
  have hcomp : IsClosedImmersion (s ≫ f) := by
    rw [h]
    infer_instance
  exact @IsClosedImmersion.of_comp _ _ _ s f hcomp inferInstance

/-- A section of a formally unramified finite-type morphism is an open immersion. -/
theorem isOpenImmersion_of_section_of_formallyUnramified
    (f : X ⟶ S) (s : S ⟶ X) [FormallyUnramified f] [LocallyOfFiniteType f]
    (h : s ≫ f = 𝟙 S) : IsOpenImmersion s := by
  exact MorphismProperty.of_isPullback (section_isPullback_diagonal f s h)
    (inferInstance : IsOpenImmersion (pullback.diagonal f))

/-- In particular, a section of an étale morphism is an open immersion. -/
theorem isOpenImmersion_of_section_of_etale
    (f : X ⟶ S) (s : S ⟶ X) [Etale f] (h : s ≫ f = 𝟙 S) :
    IsOpenImmersion s :=
  isOpenImmersion_of_section_of_formallyUnramified f s h

/-- A section of a separated étale morphism has clopen image.  This is the form used to
discard the other components of an étale neighbourhood while retaining the distinguished section. -/
theorem isClopen_range_of_section_of_separated_etale
    (f : X ⟶ S) (s : S ⟶ X) [Etale f] [IsSeparated f] (h : s ≫ f = 𝟙 S) :
    IsClopen (Set.range s) := by
  let hopen : IsOpenImmersion s := isOpenImmersion_of_section_of_etale f s h
  let hclosed : IsClosedImmersion s := isClosedImmersion_of_section_of_separated f s h
  exact ⟨(@Scheme.Hom.isClosedEmbedding _ _ s hclosed).isClosed_range,
    @IsOpenImmersion.isOpen_range _ _ s hopen⟩

/-! ## Sections induced on fibre products -/

/-- A compatible pair consisting of a map `s : S ⟶ X` and the identity of `S` lifts to the
fibre product `X ×_A S`. -/
def liftToPullback (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) (h : s ≫ q = t) :
    S ⟶ pullback q t :=
  pullback.lift s (𝟙 S) (by simpa using h)

@[reassoc (attr := simp)]
theorem liftToPullback_fst (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X)
    (h : s ≫ q = t) :
    liftToPullback q t s h ≫ pullback.fst q t = s :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem liftToPullback_snd (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X)
    (h : s ≫ q = t) :
    liftToPullback q t s h ≫ pullback.snd q t = 𝟙 S :=
  pullback.lift_snd _ _ _

/-- The induced section of the pullback of an étale morphism is an open immersion. -/
theorem isOpenImmersion_liftToPullback_of_etale
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q]
    (h : s ≫ q = t) :
    IsOpenImmersion (liftToPullback q t s h) :=
  isOpenImmersion_of_section_of_etale
    (pullback.snd q t) (liftToPullback q t s h) (liftToPullback_snd q t s h)

/-- If the coordinate map is separated, the induced pullback section is also a closed
immersion. -/
theorem isClosedImmersion_liftToPullback_of_separated
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [IsSeparated q]
    (h : s ≫ q = t) :
    IsClosedImmersion (liftToPullback q t s h) := by
  let hseparated : IsSeparated (pullback.snd q t) := by infer_instance
  exact @isClosedImmersion_of_section_of_separated _ _
    (pullback.snd q t) (liftToPullback q t s h) hseparated (liftToPullback_snd q t s h)

instance liftToPullback_isOpenImmersion
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q]
    (h : s ≫ q = t) :
    IsOpenImmersion (liftToPullback q t s h) :=
  isOpenImmersion_liftToPullback_of_etale q t s h

instance liftToPullback_isClosedImmersion
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [IsSeparated q]
    (h : s ≫ q = t) :
    IsClosedImmersion (liftToPullback q t s h) :=
  isClosedImmersion_liftToPullback_of_separated q t s h

/-- After pulling an étale separated coordinate map back along a compatible graph, the induced
section is a clopen component of the fibre product. -/
theorem isClopen_range_liftToPullback_of_separated_etale
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    (h : s ≫ q = t) :
    IsClopen (Set.range (liftToPullback q t s h)) := by
  let hopen : IsOpenImmersion (liftToPullback q t s h) :=
    isOpenImmersion_liftToPullback_of_etale q t s h
  let hclosed : IsClosedImmersion (liftToPullback q t s h) :=
    isClosedImmersion_liftToPullback_of_separated q t s h
  exact ⟨(@Scheme.Hom.isClosedEmbedding _ _ _ hclosed).isClosed_range,
    @IsOpenImmersion.isOpen_range _ _ _ hopen⟩

/-- The clopen component of an étale graph pullback selected by its compatible section. -/
def pullbackSectionComponent
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    (h : s ≫ q = t) : (pullback q t).Opens :=
  ⟨Set.range (liftToPullback q t s h),
    (isClopen_range_liftToPullback_of_separated_etale q t s h).isOpen⟩

/-- The distinguished pullback component is canonically isomorphic to the source of the
section. -/
def pullbackSectionComponentIso
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    (h : s ≫ q = t) :
    S ≅ (pullbackSectionComponent q t s h).toScheme := by
  let hopen : IsOpenImmersion (liftToPullback q t s h) :=
    isOpenImmersion_liftToPullback_of_etale q t s h
  exact @IsOpenImmersion.isoOfRangeEq _ _ _
    (liftToPullback q t s h) (pullbackSectionComponent q t s h).ι
      hopen inferInstance (by
        rw [Scheme.Opens.range_ι]
        rfl)

/-! ## Isolating a clopen component of a closed subscheme -/

/-- The open complement of the image of a closed immersion.  When the immersion is also open,
this is the complementary clopen component of its target. -/
def complementOfClosedImmersion (j : S ⟶ D) [IsClosedImmersion j] : D.Opens :=
  ⟨(Set.range j)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- If `j` is both open and closed, inclusion of its complementary component is a closed
immersion as well. -/
instance complementOfClosedImmersion_ι_isClosedImmersion
    (j : S ⟶ D) [IsOpenImmersion j] [IsClosedImmersion j] :
    IsClosedImmersion (complementOfClosedImmersion j).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact (IsOpenImmersion.isOpen_range j).isClosed_compl

/-- Remove from an ambient scheme all complementary components of a closed subscheme, retaining
the component selected by `j`. -/
def ambientOpenOfClopenComponent
    (i : D ⟶ X) (j : S ⟶ D) [IsClosedImmersion i]
    [IsOpenImmersion j] [IsClosedImmersion j] : X.Opens :=
  ⟨(Set.range ((complementOfClosedImmersion j).ι ≫ i))ᶜ,
    ((complementOfClosedImmersion j).ι ≫ i).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- Pulling the isolating ambient open back to the closed subscheme leaves exactly the selected
clopen component. -/
theorem preimage_ambientOpenOfClopenComponent
    (i : D ⟶ X) (j : S ⟶ D) [IsClosedImmersion i]
    [IsOpenImmersion j] [IsClosedImmersion j] :
    i ⁻¹ᵁ ambientOpenOfClopenComponent i j = j.opensRange := by
  ext x
  constructor
  · intro hx
    change i x ∉ Set.range ((complementOfClosedImmersion j).ι ≫ i) at hx
    change x ∈ Set.range j
    by_contra hxj
    let y : (complementOfClosedImmersion j).toScheme := ⟨x, hxj⟩
    apply hx
    exact ⟨y, rfl⟩
  · intro hx
    change x ∈ Set.range j at hx
    change i x ∉ Set.range ((complementOfClosedImmersion j).ι ≫ i)
    rintro ⟨y, hy⟩
    have hxy : x = (complementOfClosedImmersion j).ι y :=
      i.isClosedEmbedding.injective hy.symm
    obtain ⟨s, hs⟩ := hx
    exact y.property ⟨s, hs.trans hxy⟩

/-- The selected component maps into its isolating ambient open. -/
theorem range_comp_subset_ambientOpenOfClopenComponent
    (i : D ⟶ X) (j : S ⟶ D) [IsClosedImmersion i]
    [IsOpenImmersion j] [IsClosedImmersion j] :
    Set.range (j ≫ i) ⊆ ambientOpenOfClopenComponent i j := by
  rintro _ ⟨s, rfl⟩
  change i (j s) ∉ Set.range ((complementOfClosedImmersion j).ι ≫ i)
  rintro ⟨y, hy⟩
  have hEq : j s = (complementOfClosedImmersion j).ι y :=
    i.isClosedEmbedding.injective hy.symm
  exact y.property ⟨s, hEq⟩

/-- For a compatible section of an étale separated coordinate map and a closed graph in the
coordinate space, this open of `X` removes precisely the other components of the graph pullback. -/
def ambientOpenOfEtaleGraph
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    [IsClosedImmersion t] (h : s ≫ q = t) : X.Opens :=
  ambientOpenOfClopenComponent (pullback.fst q t) (liftToPullback q t s h)

/-- On the pulled-back graph, the isolating ambient open has exactly the distinguished section as
its inverse image. -/
theorem preimage_ambientOpenOfEtaleGraph
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    [IsClosedImmersion t] (h : s ≫ q = t) :
    pullback.fst q t ⁻¹ᵁ ambientOpenOfEtaleGraph q t s h =
      (liftToPullback q t s h).opensRange :=
  preimage_ambientOpenOfClopenComponent
    (pullback.fst q t) (liftToPullback q t s h)

/-- The original compatible section lands in the isolating ambient open. -/
theorem range_subset_ambientOpenOfEtaleGraph
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    [IsClosedImmersion t] (h : s ≫ q = t) :
    Set.range s ⊆ ambientOpenOfEtaleGraph q t s h := by
  rintro _ ⟨z, rfl⟩
  have hz := range_comp_subset_ambientOpenOfClopenComponent
    (pullback.fst q t) (liftToPullback q t s h)
      ⟨z, rfl⟩
  change s z ∈ (ambientOpenOfClopenComponent
    (pullback.fst q t) (liftToPullback q t s h) : Set X)
  simpa only [Scheme.Hom.comp_apply, liftToPullback_fst] using hz

/-- The compatible section, restricted to the ambient open which isolates its graph component. -/
def sectionToAmbientOpenOfEtaleGraph
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    [IsClosedImmersion t] (h : s ≫ q = t) :
    S ⟶ (ambientOpenOfEtaleGraph q t s h).toScheme :=
  IsOpenImmersion.lift (ambientOpenOfEtaleGraph q t s h).ι s
    (by
      rw [Scheme.Opens.range_ι]
      exact range_subset_ambientOpenOfEtaleGraph q t s h)

@[reassoc (attr := simp)]
theorem sectionToAmbientOpenOfEtaleGraph_ι
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    [IsClosedImmersion t] (h : s ≫ q = t) :
    sectionToAmbientOpenOfEtaleGraph q t s h ≫
      (ambientOpenOfEtaleGraph q t s h).ι = s :=
  IsOpenImmersion.lift_fac _ _ _

/-- The distinguished section is the whole inverse image of the pulled-back graph after passing to
the isolating ambient open. -/
def isolatedPullbackComponentIso
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    [IsClosedImmersion t] (h : s ≫ q = t) :
    S ≅ (pullback.fst q t ⁻¹ᵁ ambientOpenOfEtaleGraph q t s h).toScheme := by
  apply IsOpenImmersion.isoOfRangeEq
    (liftToPullback q t s h)
    (pullback.fst q t ⁻¹ᵁ ambientOpenOfEtaleGraph q t s h).ι
  rw [Scheme.Opens.range_ι, preimage_ambientOpenOfEtaleGraph]
  rfl

/-- Under the preceding isomorphism, the restricted graph-pullback immersion is exactly the
original section restricted to the isolating ambient open. -/
@[reassoc (attr := simp)]
theorem isolatedPullbackComponentIso_hom_restrict
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    [IsClosedImmersion t] (h : s ≫ q = t) :
    (isolatedPullbackComponentIso q t s h).hom ≫
        (pullback.fst q t ∣_ ambientOpenOfEtaleGraph q t s h) =
      sectionToAmbientOpenOfEtaleGraph q t s h := by
  rw [← cancel_mono (ambientOpenOfEtaleGraph q t s h).ι]
  rw [sectionToAmbientOpenOfEtaleGraph_ι]
  rw [Category.assoc, morphismRestrict_ι]
  rw [← Category.assoc]
  unfold isolatedPullbackComponentIso
  rw [IsOpenImmersion.isoOfRangeEq_hom_fac]
  exact liftToPullback_fst q t s h

/-- The isolated section remains a closed immersion into its ambient open. -/
instance sectionToAmbientOpenOfEtaleGraph_isClosedImmersion
    (q : X ⟶ A) (t : S ⟶ A) (s : S ⟶ X) [Etale q] [IsSeparated q]
    [IsClosedImmersion t] (h : s ≫ q = t) :
    IsClosedImmersion (sectionToAmbientOpenOfEtaleGraph q t s h) := by
  have hs : IsClosedImmersion s := by
    have hcomp : IsClosedImmersion (s ≫ q) := h ▸ (inferInstance : IsClosedImmersion t)
    exact @IsClosedImmersion.of_comp _ _ _ s q hcomp inferInstance
  have hcomp : IsClosedImmersion
      (sectionToAmbientOpenOfEtaleGraph q t s h ≫
        (ambientOpenOfEtaleGraph q t s h).ι) := by
    rw [sectionToAmbientOpenOfEtaleGraph_ι]
    exact hs
  exact @IsClosedImmersion.of_comp _ _ _
    (sectionToAmbientOpenOfEtaleGraph q t s h)
      (ambientOpenOfEtaleGraph q t s h).ι hcomp inferInstance

end

end GromovWitten.AlgebraicGeometry.Curves
