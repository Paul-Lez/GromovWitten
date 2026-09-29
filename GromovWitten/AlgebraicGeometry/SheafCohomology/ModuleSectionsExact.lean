/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleExact
import GromovWitten.AlgebraicGeometry.SheafCohomology.LocalVanishing

/-!
# Exactness of module short complexes from sections

Short exactness of a short complex of scheme modules can be checked after taking sections on every
open. The middle-exactness step uses the affine-open basis, together with stalkwise sheaf
exactness and the faithfulness of the underlying abelian-sheaf functor.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

universe u
noncomputable section

variable {S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A module short complex is short exact when every open-section complex is short exact. -/
lemma module_shortExact_of_sections_shortExact (A : ShortComplex S.Modules)
    (hA : ∀ W : S.Opens,
      (A.map (moduleToSheafAb S ⋙ sections W)).ShortExact) :
    A.ShortExact := by
  have hexact : (A.map (moduleToSheafAb S)).Exact := by
    apply exact_of_sections_basis (A.map (moduleToSheafAb S)) S.isBasis_affineOpens
    intro W hW
    have hW' := hA W
    change ((A.map (moduleToSheafAb S)).map (sections W)).Exact
    exact hW'.exact
  have hmonoS : Mono ((moduleToSheafAb S).map A.f) := by
    have hmonoP : Mono ((TopCat.Sheaf.forget AddCommGrpCat S).map
        ((moduleToSheafAb S).map A.f)) := by
      apply (NatTrans.mono_iff_mono_app _).mpr
      intro W
      change Mono (((A.map (moduleToSheafAb S)).map (sections W.unop)).f)
      exact (hA W.unop).mono_f
    exact (TopCat.Sheaf.forget AddCommGrpCat S).mono_of_mono_map hmonoP
  have hepiS : Epi ((moduleToSheafAb S).map A.g) := by
    have hepiP : Epi ((TopCat.Sheaf.forget AddCommGrpCat S).map
        ((moduleToSheafAb S).map A.g)) := by
      apply (NatTrans.epi_iff_epi_app _).mpr
      intro W
      change Epi (((A.map (moduleToSheafAb S)).map (sections W.unop)).g)
      exact (hA W.unop).epi_g
    exact (TopCat.Sheaf.forget AddCommGrpCat S).epi_of_epi_map hepiP
  have hmono : Mono A.f := (moduleToSheafAb S).mono_of_mono_map hmonoS
  have hepi : Epi A.g := (moduleToSheafAb S).epi_of_epi_map hepiS
  exact { exact := (A.exact_map_iff_of_faithful (moduleToSheafAb S)).mp hexact
          mono_f := hmono, epi_g := hepi }

end
end GromovWitten.AlgebraicGeometry.SheafCohomology
