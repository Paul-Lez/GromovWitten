/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import GromovWitten.CategoryTheory.HomologySequenceFunctor

/-!
# Homology cokernels of short exact complexes

If the middle complex has vanishing homology in degree `j`, the connecting morphism identifies
`coker(H_i(X₂) → H_i(X₃))` with `H_j(X₁)`.
-/

open CategoryTheory Limits

noncomputable section
universe u v w

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}
variable {S : ShortComplex (HomologicalComplex C c)}
variable (i j : ι) (hij : c.Rel i j)

/-- When `H_j(X₂) = 0`, the cokernel of `H_i(X₂) → H_i(X₃)` is `H_j(X₁)`. -/
def homologyCokernelIso (hS : S.ShortExact)
    (h : IsZero (S.X₂.homology j)) :
    cokernel (HomologicalComplex.homologyMap S.g i) ≅ S.X₁.homology j := by
  have : Epi (hS.δ i j hij) :=
    (hS.homology_exact₁ i j hij).epi_f (h.eq_of_tgt _ _)
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (hS.homology_exact₃ i j hij).gIsCokernel

/-- The homology cokernel isomorphism carries the cokernel projection to the connecting morphism. -/
@[reassoc]
lemma homologyCokernelIso_π (hS : S.ShortExact)
    (h : IsZero (S.X₂.homology j)) :
    cokernel.π (HomologicalComplex.homologyMap S.g i) ≫
      (homologyCokernelIso i j hij hS h).hom = hS.δ i j hij := by
  dsimp only [homologyCokernelIso]
  exact Cofork.IsColimit.π_desc (cokernelIsCokernel _)

set_option backward.isDefEq.respectTransparency false in
/-- The homology cokernel comparison is natural for a morphism of short exact complexes when the
middle homology vanishes in the target degree. -/
lemma homologyCokernelIso_naturality {T : ShortComplex (HomologicalComplex C c)}
    (φ : S ⟶ T) (i j : ι) (hij : c.Rel i j) (hS : S.ShortExact) (hT : T.ShortExact)
    (hS₂ : IsZero (S.X₂.homology j)) (hT₂ : IsZero (T.X₂.homology j)) :
    cokernel.map (HomologicalComplex.homologyMap S.g i)
        (HomologicalComplex.homologyMap T.g i)
        (HomologicalComplex.homologyMap φ.τ₂ i)
        (HomologicalComplex.homologyMap φ.τ₃ i)
        (by rw [← HomologicalComplex.homologyMap_comp,
          ← HomologicalComplex.homologyMap_comp, φ.comm₂₃]) ≫
      (homologyCokernelIso i j hij hT hT₂).hom =
    (homologyCokernelIso i j hij hS hS₂).hom ≫
      HomologicalComplex.homologyMap φ.τ₁ j := by
  apply (cancel_epi (cokernel.π (HomologicalComplex.homologyMap S.g i))).mp
  rw [cokernel.π_desc_assoc, Category.assoc, homologyCokernelIso_π,
    homologyCokernelIso_π_assoc]
  exact (HomologicalComplex.HomologySequence.δ_naturality φ hS hT i j hij).symm

set_option backward.isDefEq.respectTransparency false in
/-- The homology cokernel comparison is compatible with an exact functor. -/
lemma homologyCokernelIso_map {D : Type*} [Category* D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (hS : S.ShortExact)
    (hSF : (S.map (F.mapHomologicalComplex c)).ShortExact)
    (i j : ι) (hij : c.Rel i j)
    (hS₂ : IsZero (S.X₂.homology j))
    (hSF₂ : IsZero (((F.mapHomologicalComplex c).obj S.X₂).homology j)) :
    cokernel.map
        (HomologicalComplex.homologyMap (S.map (F.mapHomologicalComplex c)).g i)
        (F.map (HomologicalComplex.homologyMap S.g i))
        ((S.X₂.sc i).mapHomologyIso F).hom
        ((S.X₃.sc i).mapHomologyIso F).hom
        (ShortComplex.mapHomologyIso_hom_naturality
          ((HomologicalComplex.shortComplexFunctor C c i).map S.g) F) ≫
      cokernelComparison (HomologicalComplex.homologyMap S.g i) F ≫
        F.map (homologyCokernelIso i j hij hS hS₂).hom =
      (homologyCokernelIso i j hij hSF hSF₂).hom ≫
        ((S.X₁.sc j).mapHomologyIso F).hom := by
  apply (cancel_epi (cokernel.π
    (HomologicalComplex.homologyMap (S.map (F.mapHomologicalComplex c)).g i))).mp
  rw [cokernel.π_desc_assoc, Category.assoc, π_comp_cokernelComparison_assoc,
    ← F.map_comp, homologyCokernelIso_π]
  exact (HomologicalComplex.HomologySequence.map_δ F hS hSF i j hij).symm.trans
    (by simpa only [Category.assoc] using
      (congrArg (fun t => t ≫ ((S.X₁.sc j).mapHomologyIso F).hom)
        (homologyCokernelIso_π i j hij hSF hSF₂)).symm)

end CategoryTheory.ShortComplex.ShortExact
