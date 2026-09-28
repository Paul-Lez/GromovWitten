/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.HomologySequence

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

end CategoryTheory.ShortComplex.ShortExact
