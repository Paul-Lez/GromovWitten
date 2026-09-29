/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

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

end CategoryTheory.ShortComplex.ShortExact
