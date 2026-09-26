/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Sites.Stack

/-!
# Regular-function comparisons for continuous site functors

This helper constructs the structure-sheaf isomorphism from a continuous functor and a
comparison of its underlying-scheme functors. Continuity is an explicit hypothesis of this
general helper; the geometric continuity theorems for stack-site inclusions remain separate.
-/

open CategoryTheory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Sites

namespace RingedSite

universe w v s

/-- The regular-function sheaf is functorial under an identification of the underlying-scheme
functor.  The comparison is the whiskering of the actual natural isomorphism; no equality of site
categories is used. -/
noncomputable def inducedRegularFunctionsCommRingSheafIso
    {C : Type v} [Category.{w} C] {D : Type v} [Category.{w} D]
    (F : C ⥤ D) (p : D ⥤ _root_.AlgebraicGeometry.Scheme.{s})
    (q : C ⥤ _root_.AlgebraicGeometry.Scheme.{s})
    (Kq Kp : GrothendieckTopology _root_.AlgebraicGeometry.Scheme.{s})
    (hq : Presheaf.IsSheaf Kq regularFunctionsCommRingPresheaf)
    (hp : Presheaf.IsSheaf Kp regularFunctionsCommRingPresheaf)
    (hcont : F.IsContinuous (q.inducedTopology Kq) (p.inducedTopology Kp))
    (e : F ⋙ p ≅ q) :
    (F.sheafPushforwardContinuous CommRingCat.{s + 1}
      (q.inducedTopology Kq) (p.inducedTopology Kp)).obj
      (inducedRegularFunctionsCommRingSheaf p
        Kp hp) ≅ inducedRegularFunctionsCommRingSheaf q Kq hq := by
  letI := hcont
  dsimp [Functor.sheafPushforwardContinuous,
    inducedRegularFunctionsCommRingSheaf]
  let α : (F ⋙ p).op ⋙ regularFunctionsCommRingPresheaf ⟶
      q.op ⋙ regularFunctionsCommRingPresheaf :=
    Functor.whiskerRight (NatIso.op e.symm).hom regularFunctionsCommRingPresheaf
  let β : q.op ⋙ regularFunctionsCommRingPresheaf ⟶
      (F ⋙ p).op ⋙ regularFunctionsCommRingPresheaf :=
    Functor.whiskerRight (NatIso.op e).hom regularFunctionsCommRingPresheaf
  exact {
    hom := ⟨α⟩
    inv := ⟨β⟩
    hom_inv_id := by ext; simp [α, β]
    inv_hom_id := by ext; simp [α, β] }

end RingedSite

end GromovWitten.AlgebraicGeometry.Sites
