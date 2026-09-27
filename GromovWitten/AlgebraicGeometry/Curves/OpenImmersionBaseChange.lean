/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeTransport
import GromovWitten.AlgebraicGeometry.Curves.HigherOpenBaseChange

/-!
# Base change along open immersions

Factoring an open immersion through its image reduces its canonical ordinary
base-change map to open restriction and base change along an isomorphism.
Open pullback preserves flasque resolutions, so the canonical higher comparison
is invertible in every degree for arbitrary sheaves of modules.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {X S T Z : Scheme.{u}}

private lemma openBaseChange_paste_congr
    {U V : Scheme.{u}} (f : X ⟶ S) (b : U ⟶ S) (p : V ⟶ X) (g : V ⟶ U)
    (c : T ⟶ U) (q : Z ⟶ V) (k : Z ⟶ T)
    (h₁ : IsPullback p g f b) (h₂ : IsPullback q k g c)
    (b' : T ⟶ S) (p' : Z ⟶ X) (hb : c ≫ b = b') (hp : q ≫ p = p')
    (h' : IsPullback p' k f b') (M : X.Modules)
    [IsIso ((modulePushforwardBaseChangeNatTrans f b p g h₁).app M)]
    [IsIso ((modulePushforwardBaseChangeNatTrans g c q k h₂).app
      ((Scheme.Modules.pullback p).obj M))] :
    IsIso ((modulePushforwardBaseChangeNatTrans f b' p' k h').app M) := by
  subst b'
  subst p'
  exact moduleBaseChange_paste_isIso f b p g c q k h₁ h₂ M

/-- Canonical module base change along any open immersion is invertible. -/
lemma moduleBaseChange_isIso_of_isOpenImmersion
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [IsOpenImmersion b] (M : X.Modules) :
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  let U := b.opensRange
  let e := b.isoOpensRange
  have hb : e.hom ≫ U.ι = b := Scheme.Hom.isoOpensRange_hom_ι b
  let h₁ := (isPullback_morphismRestrict f U).flip
  have h' : IsPullback p g f (e.hom ≫ U.ι) := hb.symm ▸ h
  let q := h₁.lift p (g ≫ e.hom) (by rw [h'.w, Category.assoc])
  have h₂ : IsPullback q g (f ∣_ U) e.hom := h'.of_right' h₁
  have : IsIso ((modulePushforwardBaseChangeNatTrans (f ∣_ U) e.hom q g h₂).app
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :=
    moduleBaseChange_isIso_of_isIso_base _ _ _ _ _ _
  exact openBaseChange_paste_congr f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
    e.hom q g h₁ h₂ b p hb (h₁.lift_fst _ _ _) h M

set_option backward.isDefEq.respectTransparency false in
/-- Canonical higher base change along any open immersion is invertible in every degree. -/
lemma moduleFlatHigherBaseChange_isIso_of_isOpenImmersion
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [IsOpenImmersion b] (M : X.Modules) (n : ℕ) :
    IsIso ((moduleFlatHigherBaseChangeNatTrans f b p g h n).app M) := by
  have : IsOpenImmersion p :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance
  let α := modulePushforwardBaseChangeNatTrans f b p g h
  have : IsIso α := (NatTrans.isIso_iff_isIso_app α).mpr
    (fun N => moduleBaseChange_isIso_of_isOpenImmersion f b p g h N)
  have : IsIso ((NatTrans.rightDerived α n).app M) := by
    change IsIso ((NatIso.rightDerivedIso (asIso α) n).hom.app M)
    infer_instance
  have := moduleOpenPullback_rightDerivedPrecomp_isIso p g M n
  change IsIso (((Functor.rightDerivedCompExactNatIso (Scheme.Modules.pullback b)
      (Scheme.Modules.pushforward f) n).inv.app M) ≫
      (NatTrans.rightDerived α n).app M ≫
      (Functor.rightDerivedPrecompComparison (Scheme.Modules.pullback p)
        (Scheme.Modules.pushforward g) n).app M)
  infer_instance

end
end GromovWitten.AlgebraicGeometry.Curves
