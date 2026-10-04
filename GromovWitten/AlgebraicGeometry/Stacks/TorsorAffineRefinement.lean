/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientStack
import GromovWitten.AlgebraicGeometry.Stacks.TorsorAffineCover
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Limits

/-!
# Affine refinement of fppf-local sections

Let `T = Spec A` be an affine scheme, `F` an fppf sheaf with a morphism `π : F ⟶ fppfYoneda T`,
and suppose `F` has a section over some fppf cover `c : V ⟶ T` (flat, locally of finite
presentation, surjective), as recorded by `FppfLocalSection`.  We show that the cover can be
replaced by a single *affine* one: there is a faithfully flat, finitely presented `A`-algebra `B`
and a section of `F` over `Spec B ⟶ Spec A`.

Proof: `c` is flat and locally of finite presentation, hence universally open
(`UniversallyOpen.of_flat`), so the images of the affine opens `Spec R_k ⟶ V` of
`V.affineOpenCover` are open in `T`; they cover `T` because `c` is surjective, and `T` is
quasi-compact, so finitely many, indexed by `K`, suffice.  Put `B := Π k : K, R_k`, so that
`Spec B ≅ ∐ₖ Spec R_k` (`sigmaSpec`).  The map `∐ₖ Spec R_k ⟶ T` is flat, locally of finite
presentation (both local on the source) and surjective, so `A ⟶ B` is faithfully flat and of
finite presentation.  The restrictions of the given section to the `Spec R_k` glue to a section
over `∐ₖ Spec R_k`, because the components of a coproduct of schemes form a Zariski (hence
fppf) cover with empty pairwise overlaps (`FppfSheaf.homOfSigma`).

## Main results

* `FppfSheaf.homOfSigma` : a family of morphisms `fppfYoneda.obj (X k) ⟶ F` into an fppf
  sheaf glues to a morphism `fppfYoneda.obj (∐ X) ⟶ F`; `FppfSheaf.sigmaι_homOfSigma` is its
  restriction property and `FppfSheaf.hom_ext_sigma` the corresponding uniqueness.
* `FppfLocalSection.exists_affineFaithfullyFlat` : an fppf-local section of `π : F ⟶ yoneda
  (Spec A)` yields a section over `Spec B ⟶ Spec A` for a faithfully flat, finitely presented
  `A`-algebra `B`.
* `FppfTorsor.exists_affineFaithfullyFlat_section` : the same for an fppf torsor over `Spec A`.
* `FppfTorsor.nonempty_torsorAffineTrivialisation` : for a torsor under an affine group
  `affineGroup R grp` over `Spec A`, the data `TorsorAffineTrivialisation P` of
  `Stacks/TorsorAffineCover.lean` always exists.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

section SigmaGluing

variable (F : FppfSheaf.{u}) {ι : Type u} (X : ι → Scheme.{u})

private lemma torsorRefinement_isSheaf (F : FppfSheaf.{u}) :
    Presieve.IsSheaf Scheme.fppfTopology F.obj :=
  (isSheaf_iff_isSheaf_of_type _ _).1 F.property

private lemma torsorRefinement_subsingleton_of_isEmpty (Z : Scheme.{u}) [IsEmpty Z] :
    Subsingleton (F.obj.obj (op Z)) := by
  have h := torsorRefinement_isSheaf F _
    (Z.bot_mem_grothendieckTopology (P := @Flat ⊓ @LocallyOfFinitePresentation))
  constructor
  intro a b
  exact h.isSeparatedFor.ext fun _ _ hf ↦ hf.elim

private lemma torsorRefinement_isSheafFor_sigma :
    Presieve.IsSheafFor F.obj (Presieve.ofArrows X (Sigma.ι X)) := by
  rw [Presieve.isSheafFor_iff_generate]
  apply torsorRefinement_isSheaf F
  exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _
    (sigmaOpenCover X).mem_grothendieckTopology

private lemma torsorRefinement_compatible (x : ∀ k, F.obj.obj (op (X k))) :
    Presieve.Arrows.Compatible F.obj (Sigma.ι X) x := by
  intro i j Z gi gj h
  by_cases hij : i = j
  · subst hij
    rw [cancel_mono] at h
    rw [h]
  · have : IsEmpty Z := isEmpty_of_commSq_sigmaι_of_ne ⟨h⟩ hij
    have := torsorRefinement_subsingleton_of_isEmpty F Z
    exact Subsingleton.elim _ _

private lemma torsorRefinement_existsUnique (x : ∀ k, F.obj.obj (op (X k))) :
    ∃! t : F.obj.obj (op (∐ X)), ∀ k, F.obj.map (Sigma.ι X k).op t = x k :=
  (Presieve.isSheafFor_arrows_iff _ _).1 (torsorRefinement_isSheafFor_sigma F X) x
    (torsorRefinement_compatible F X x)

/-- Gluing morphisms out of representable fppf sheaves along a coproduct of schemes: a family
of morphisms `s k : fppfYoneda.obj (X k) ⟶ F` into an fppf sheaf `F` induces a morphism
`fppfYoneda.obj (∐ X) ⟶ F` (the components `X k ⟶ ∐ X` form a Zariski, hence fppf, cover with
empty pairwise overlaps). -/
noncomputable def FppfSheaf.homOfSigma (s : ∀ k, fppfYoneda.obj (X k) ⟶ F) :
    fppfYoneda.obj (∐ X) ⟶ F :=
  Scheme.fppfTopology.yonedaEquiv.symm
    (torsorRefinement_existsUnique F X fun k ↦ Scheme.fppfTopology.yonedaEquiv (s k)).exists.choose

/-- The glued morphism `FppfSheaf.homOfSigma F s` restricts to `s k` on the `k`-th component. -/
@[reassoc (attr := simp)]
theorem FppfSheaf.sigmaι_homOfSigma (s : ∀ k, fppfYoneda.obj (X k) ⟶ F) (k : ι) :
    fppfYoneda.map (Sigma.ι X k) ≫ FppfSheaf.homOfSigma F X s = s k := by
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [← GrothendieckTopology.yonedaEquiv_naturality, FppfSheaf.homOfSigma,
    Equiv.apply_symm_apply]
  exact (torsorRefinement_existsUnique F X fun k ↦
    Scheme.fppfTopology.yonedaEquiv (s k)).exists.choose_spec k

/-- Two morphisms `fppfYoneda.obj (∐ X) ⟶ F` into an fppf sheaf agree as soon as they agree on
every component `X k`. -/
theorem FppfSheaf.hom_ext_sigma {φ ψ : fppfYoneda.obj (∐ X) ⟶ F}
    (h : ∀ k, fppfYoneda.map (Sigma.ι X k) ≫ φ = fppfYoneda.map (Sigma.ι X k) ≫ ψ) : φ = ψ := by
  apply Scheme.fppfTopology.yonedaEquiv.injective
  refine (torsorRefinement_existsUnique F X fun k ↦
    Scheme.fppfTopology.yonedaEquiv (fppfYoneda.map (Sigma.ι X k) ≫ φ)).unique ?_ ?_
  · intro k
    rw [GrothendieckTopology.yonedaEquiv_naturality]
  · intro k
    rw [GrothendieckTopology.yonedaEquiv_naturality, h]

end SigmaGluing

section Refinement

variable {A : Type u} [CommRing A] {F : FppfSheaf.{u}}
  {π : F ⟶ fppfYoneda.obj (Spec (CommRingCat.of A))}

/-- Affine refinement of an fppf-local section over an affine base: if `F` has a section over an
fppf cover of `Spec A` (lying over the cover), then it has a section over `Spec B ⟶ Spec A`
(lying over it) for some faithfully flat, finitely presented `A`-algebra `B`.  (In the proof,
`B` is a finite product of coordinate rings of affine opens of the given cover.) -/
theorem FppfLocalSection.exists_affineFaithfullyFlat
    (L : FppfLocalSection F (Spec (CommRingCat.of A)) π) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Module.FaithfullyFlat A B ∧ Algebra.FinitePresentation A B ∧
      ∃ s : fppfYoneda.obj (Spec (CommRingCat.of B)) ⟶ F,
        s ≫ π = fppfYoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  classical
  have := L.flat
  have := L.locallyOfFinitePresentation
  have := L.surjective
  let 𝒰 := L.coverScheme.affineOpenCover
  let U : 𝒰.I₀ → Set (Spec (CommRingCat.of A)) := fun k ↦ Set.range (𝒰.f k ≫ L.cover)
  have hUo : ∀ k, IsOpen (U k) := fun k ↦ (𝒰.f k ≫ L.cover).isOpenMap.isOpen_range
  have hUc : Set.univ ⊆ ⋃ k, U k := by
    intro t _
    obtain ⟨v, rfl⟩ := L.cover.surjective t
    obtain ⟨w, hw⟩ := 𝒰.covers v
    refine Set.mem_iUnion.2 ⟨𝒰.idx v, w, ?_⟩
    rw [Scheme.Hom.comp_apply, hw]
  obtain ⟨K, hK⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  let R : K → CommRingCat.{u} := fun k ↦ 𝒰.X k.1
  let g : ∀ k : K, Spec (R k) ⟶ Spec (CommRingCat.of A) := fun k ↦ 𝒰.f k.1 ≫ L.cover
  let h : Spec (CommRingCat.of (Π k, R k)) ⟶ Spec (CommRingCat.of A) :=
    inv (sigmaSpec R) ≫ Sigma.desc g
  let φ : CommRingCat.of A ⟶ CommRingCat.of (Π k, R k) := Spec.preimage h
  have hφ : Spec.map φ = h := Spec.map_preimage h
  let _ : Algebra A (Π k, R k) := φ.hom.toAlgebra
  have hflat : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have hlfp : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [hφ]
    have : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    have : LocallyOfFinitePresentation (Sigma.desc g) :=
      IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
    infer_instance
  have hsurj : Surjective (Spec.map φ) := by
    have : Surjective (sigmaSpec R ≫ Spec.map φ) := by
      rw [hφ, IsIso.hom_inv_id_assoc]
      refine Surjective.sigmaDesc_of_union_range_eq_univ ?_
      refine Set.eq_univ_of_univ_subset (hK.trans ?_)
      intro t ht
      simp only [Set.mem_iUnion] at ht ⊢
      obtain ⟨k, hk, ht⟩ := ht
      exact ⟨⟨k, hk⟩, ht⟩
    exact Surjective.of_comp (sigmaSpec R) (Spec.map φ)
  have hff : φ.hom.FaithfullyFlat :=
    (flat_and_surjective_SpecMap_iff φ).1 ⟨hflat, hsurj⟩
  have hfp : φ.hom.FinitePresentation := (LocallyOfFinitePresentation.SpecMap_iff φ).1 hlfp
  let s₀ : fppfYoneda.obj (∐ fun k ↦ Spec (R k)) ⟶ F :=
    FppfSheaf.homOfSigma F _ fun k ↦ fppfYoneda.map (𝒰.f k.1) ≫ L.localLift
  have hs₀ : s₀ ≫ π = fppfYoneda.map (Sigma.desc g) := by
    refine FppfSheaf.hom_ext_sigma _ _ fun k ↦ ?_
    rw [FppfSheaf.sigmaι_homOfSigma_assoc, Category.assoc, L.localLift_over, ← Functor.map_comp,
      ← Functor.map_comp, Sigma.ι_desc]
  refine ⟨Π k, R k, inferInstance, inferInstance, hff, hfp,
    fppfYoneda.map (inv (sigmaSpec R)) ≫ s₀, ?_⟩
  rw [Category.assoc, hs₀, ← Functor.map_comp]
  exact congrArg fppfYoneda.map hφ.symm

/-- An fppf torsor over an affine base `Spec A` has a section over `Spec B` for some faithfully
flat, finitely presented `A`-algebra `B`, lying over `Spec B ⟶ Spec A`. -/
theorem FppfTorsor.exists_affineFaithfullyFlat_section {G : AlgebraicSpaceGroup.{u}}
    (P : FppfTorsor G (Spec (CommRingCat.of A))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Module.FaithfullyFlat A B ∧ Algebra.FinitePresentation A B ∧
      ∃ s : fppfYoneda.obj (Spec (CommRingCat.of B)) ⟶ P.P,
        s ≫ P.projection = fppfYoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  P.locallyTrivial.exists_affineFaithfullyFlat

/-- Every fppf torsor under an affine group `affineGroup R grp` over an affine base `Spec A`
admits a `TorsorAffineTrivialisation` (an affine, faithfully flat, finitely presented cover
`Spec B ⟶ Spec A` with a section of the torsor over it). -/
theorem FppfTorsor.nonempty_torsorAffineTrivialisation {R : Type u} [CommRing R]
    {grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))}
    (P : FppfTorsor (affineGroup R grp) (Spec (CommRingCat.of A))) :
    Nonempty (TorsorAffineTrivialisation P) := by
  obtain ⟨B, _, _, _, _, s, hs⟩ := P.exists_affineFaithfullyFlat_section
  exact ⟨{ B := B, s := s, s_over := hs }⟩

end Refinement

end GromovWitten.AlgebraicGeometry
