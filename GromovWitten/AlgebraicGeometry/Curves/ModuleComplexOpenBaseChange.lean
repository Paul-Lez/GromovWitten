/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.ComplexBaseChangeHomotopy
import GromovWitten.AlgebraicGeometry.Curves.ModuleOpenBaseChange

/-!
# Open base change for module complexes

The ordinary open base-change isomorphism lifts degreewise to the generic
cochain-complex base-change map.
-/

open CategoryTheory Limits HomologicalComplex
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves
open CategoryTheory.NatTrans
open Scheme.Modules

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Pullback to the preimage of an open is compatible with the open
base-change map on cochain complexes. -/
lemma moduleComplexBaseChange_open_isIso
    (s : X ⟶ S) (U : S.Opens) {K : CochainComplex X.Modules ℕ} :
    IsIso (complexBaseChangeMap (Scheme.Modules.pushforward s)
      (Scheme.Modules.pullback U.ι)
      (Scheme.Modules.pullback (s ⁻¹ᵁ U).ι)
      (Scheme.Modules.pushforward (s ∣_ U))
      (modulePushforwardBaseChangeNatTrans s U.ι (s ⁻¹ᵁ U).ι (s ∣_ U)
        (isPullback_morphismRestrict s U).flip)
      (K := K) (J :=
        ((Scheme.Modules.pullback (s ⁻¹ᵁ U).ι).mapHomologicalComplex (.up ℕ)).obj K)
      (𝟙 _)) := by
  let α := modulePushforwardBaseChangeNatTrans s U.ι (s ⁻¹ᵁ U).ι (s ∣_ U)
    (isPullback_morphismRestrict s U).flip
  let β := complexBaseChangeMap (Scheme.Modules.pushforward s)
    (Scheme.Modules.pullback U.ι)
    (Scheme.Modules.pullback (s ⁻¹ᵁ U).ι)
    (Scheme.Modules.pushforward (s ∣_ U)) (K := K)
    (J := ((Scheme.Modules.pullback (s ⁻¹ᵁ U).ι).mapHomologicalComplex (.up ℕ)).obj K)
    α (𝟙 _)
  change IsIso β
  let _ : ∀ n : ℕ, IsIso (β.f n) := by
    intro n
    change IsIso (α.app (K.X n) ≫
      (Scheme.Modules.pushforward (s ∣_ U)).map (𝟙 _))
    rw [(Scheme.Modules.pushforward (s ∣_ U)).map_id]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components β

end GromovWitten.AlgebraicGeometry.Curves
