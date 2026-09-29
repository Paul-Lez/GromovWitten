/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.Flasque
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X : TopCat.{u}}

/-- Every abelian sheaf on a discrete space is flasque.

For an inclusion `U ≤ V`, the complement `V \\ U` is open and disjoint from `U`.
The sheaf condition identifies sections on `V` with the product of sections on
these two opens, so restriction to `U` is a split epimorphism. -/
theorem isFlasque_of_discreteTopology [DiscreteTopology X]
    (F : X.Sheaf AddCommGrpCat.{u}) : TopCat.Sheaf.IsFlasque F := by
  constructor
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro s
  let small : Opens X := V.unop
  let big : Opens X := U.unop
  let W : Opens X := big ⊓ ⟨(small : Set X)ᶜ,
    isOpen_compl_iff.mpr (isClosed_discrete _)⟩
  have hsmallW : small ⊓ W = ⊥ := by
    apply Opens.ext
    ext x
    change (x ∈ small ∧ x ∈ big ∧ x ∉ small) ↔ False
    tauto
  have hcover : small ⊔ W = big := by
    apply le_antisymm
    · exact sup_le i.unop.le (inf_le_left)
    · intro x hx
      rw [Opens.mem_sup]
      by_cases hxs : x ∈ small
      · exact Or.inl hxs
      · exact Or.inr ⟨hx, hxs⟩
  let hp := TopCat.Sheaf.isProductOfDisjoint F small W hsmallW
  let l₀ : F.1.obj (op small) ⟶ F.1.obj (op (small ⊔ W)) :=
    BinaryFan.IsLimit.lift hp (𝟙 _) 0
  let l : F.1.obj (op small) ⟶ F.1.obj (op big) :=
    l₀ ≫ F.1.map (eqToHom hcover.symm).op
  refine ⟨l.hom s, ?_⟩
  have hi : l₀ ≫ F.1.map (homOfLE le_sup_left : small ⟶ small ⊔ W).op = 𝟙 _ := by
    exact BinaryFan.IsLimit.lift_fst hp (𝟙 _) 0
  change (F.1.map i) (l.hom s) = s
  dsimp [l]
  have heq : (eqToHom hcover.symm).op ≫ i =
      (homOfLE le_sup_left : small ⟶ small ⊔ W).op := by
    apply Subsingleton.elim
  have hmap : F.1.map (eqToHom hcover.symm).op ≫ F.1.map i =
      F.1.map (homOfLE le_sup_left : small ⟶ small ⊔ W).op := by
    rw [← F.1.map_comp, heq]
  rw [← ConcreteCategory.comp_apply]
  change ((l₀ ≫ F.1.map (eqToHom hcover.symm).op) ≫ F.1.map i) s = s
  rw [Category.assoc, hmap, hi]
  rfl

/-- Pushforward preserves the flasque support term when its source is discrete. -/
theorem isFlasque_pushforward_of_discreteSource {A Y : TopCat.{u}}
    [DiscreteTopology A] (f : A ⟶ Y) (F : A.Sheaf AddCommGrpCat.{u}) :
    TopCat.Sheaf.IsFlasque
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) := by
  have : TopCat.Sheaf.IsFlasque F := isFlasque_of_discreteTopology F
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque F f

end GromovWitten.AlgebraicGeometry.SheafCohomology
