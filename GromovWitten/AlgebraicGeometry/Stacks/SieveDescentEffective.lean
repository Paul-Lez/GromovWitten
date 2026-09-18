/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.SieveDescentData
import GromovWitten.AlgebraicGeometry.Stacks.TorsorStack

/-!
# Effectivity of fppf descent for sheaves of sets, bundled form

`Stacks/SieveDescentData.lean` glues a sieve-indexed descent datum of fppf sheaves into a single
fppf sheaf `A` over `S` and identifies, for every member `f : X ⟶ S` of the covering sieve and
every `b : W ⟶ X`, the sections of `sheaf f hf` over `W` lying over `b` with the sections of `A`
lying over `b ≫ f` (`SieveDescent.exists_glue_fibrewise`).

This file assembles those bijections into the bundled statement of `Stacks/TorsorStack.lean`:
the structure `SheafDescentInput`, whose single field says that every descent datum
`SheafDescentDatum S R` along an fppf covering sieve `R` of `S` comes from a sheaf
`A ⟶ fppfYoneda.obj S` by base change, compatibly with the transition isomorphisms of the datum.
The main theorem `sheafDescentInput` proves that structure unconditionally, so that the
effectivity hypothesis used by the descent theory of `[U/G]` becomes a theorem.

## Construction

For a member `f : X ⟶ S` of the sieve, a section `x` of `sheaf f hf` over `W` determines the
section `sectionTot` of the total presheaf over `W` lying over `base (prj f hf) x ≫ f`; composing
with the comparison morphism `Φ : tot ⟶ A.obj` produced by `exists_glue_fibrewise` gives a map on
sections which is natural (`sectionTot_res`, itself a consequence of the key cocycle identity
`toTotHom_trans`) and therefore glues to a morphism `glueHom : sheaf f hf ⟶ A`
(`SheafGluing.PartialHom.glue` for the maximal sieve on `X`).  It lies over `S`
(`glueHom_comp`), hence lifts to `glueLift : sheaf f hf ⟶ pullback π (fppfYoneda.map f)`, and
that lift is an isomorphism (`isIso_glueLift`) because it is bijective on sections, by the
fibrewise bijections of `exists_glue_fibrewise`.  Compatibility with the transition isomorphisms
(`glueHom_trans`) is again the cocycle identity `toTotHom_trans`.

## Main declarations

* `SieveDescentEffective.toTotHom_trans`: the cocycle identity in the form needed here --
  transporting a section along `h = g ≫ f` agrees with transporting it first along `g` and then
  along `f`.
* `SieveDescentEffective.sectionTot_eq`, `sectionTot_res`, `sectionTot_injective`,
  `exists_sectionTot_eq`: the elementary properties of `SieveDescent.sectionTot` used below --
  a recognition criterion, naturality in `W`, injectivity and surjectivity.
* `SieveDescentEffective.glueHom`, `glueHom_app`, `glueHom_comp`, `glueHom_trans`: the glued
  morphism `sheaf f hf ⟶ A` attached to a member of the sieve, its values on sections, the fact
  that it lies over `S`, and its compatibility with the transition isomorphisms.
* `SieveDescentEffective.glueLift`, `isIso_glueLift`: the induced morphism to the base change of
  `A` along `f`, and the proof that it is an isomorphism.
* `sheafDescentInput`: **every fppf descent datum of sheaves of sets along a covering sieve is
  effective**, i.e. the structure `SheafDescentInput` of `Stacks/TorsorStack.lean` holds.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace GromovWitten.AlgebraicGeometry

open GromovWitten.SheafGluing _root_.AlgebraicGeometry

universe u

namespace SieveDescentEffective

open GromovWitten.AlgebraicGeometry.SieveDescent

/-- Two sections of a fibre product of fppf sheaves agree as soon as their two projections
agree. -/
lemma pullback_section_ext {P₁ P₂ P₃ : FppfSheaf.{u}} (p : P₁ ⟶ P₃) (q : P₂ ⟶ P₃)
    {W : Scheme.{u}} {s t : (pullback p q).obj.obj (op W)}
    (h1 : (pullback.fst p q).hom.app (op W) s = (pullback.fst p q).hom.app (op W) t)
    (h2 : (pullback.snd p q).hom.app (op W) s = (pullback.snd p q).hom.app (op W) t) :
    s = t := by
  refine Scheme.fppfTopology.yonedaEquiv.symm.injective (pullback.hom_ext ?_ ?_)
  · rw [GrothendieckTopology.yonedaEquiv_symm_naturality_right,
      GrothendieckTopology.yonedaEquiv_symm_naturality_right, h1]
  · rw [GrothendieckTopology.yonedaEquiv_symm_naturality_right,
      GrothendieckTopology.yonedaEquiv_symm_naturality_right, h2]

variable {S : Scheme.{u}}

/-- The base of a section for a structure morphism composed with a representable morphism. -/
lemma base_comp_yoneda {P : FppfSheaf.{u}} {X : Scheme.{u}} (p : P ⟶ fppfYoneda.obj X)
    (f : X ⟶ S) {W : Scheme.{u}} (x : P.obj.obj (op W)) :
    base (p ≫ fppfYoneda.map f) x = base p x ≫ f := by
  have h1 : Scheme.fppfTopology.yonedaEquiv.symm (base p x) ≫ fppfYoneda.map f
      = fppfYoneda.map (base p x ≫ f) := by
    rw [SieveDescent.yonedaEquiv_symm_map, ← CategoryTheory.Functor.map_comp]
  have h2 := congrArg Scheme.fppfTopology.yonedaEquiv h1
  rw [GrothendieckTopology.yonedaEquiv_comp, Equiv.apply_symm_apply,
    GrothendieckTopology.yonedaEquiv_yoneda_map] at h2
  exact h2

variable {R : Sieve S}
  {sheaf : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f → FppfSheaf.{u}}
  {prj : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f), sheaf f hf ⟶ fppfYoneda.obj X}
  (tr : ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (_hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h),
    sheaf h hh' ≅ pullback (prj f hf) (fppfYoneda.map g))
  (trp : ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h),
    (tr f g h hh hf hh').hom ≫ pullback.snd (prj f hf) (fppfYoneda.map g) = prj h hh')
  (trt : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (k : Z ⟶ Y) (h : Y ⟶ S)
    (q : Z ⟶ S) (hh : g ≫ f = h) (hq : k ≫ h = q) (hf : R.arrows f) (hh' : R.arrows h)
    (hq' : R.arrows q),
    (tr h k q hq hh' hq').hom ≫ pullback.fst (prj h hh') (fppfYoneda.map k) ≫
        (tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g) =
      (tr f (k ≫ g) q (by rw [Category.assoc, hh, hq]) hf hq').hom ≫
        pullback.fst (prj f hf) (fppfYoneda.map (k ≫ g)))

/-- Congruence of `SieveDescent.toTotHom` in the section argument. -/
lemma toTotHom_congr_arg {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    {α α' : fppfYoneda.obj W ⟶ sheaf f hf} (hαα : α = α')
    (hα : α ≫ prj f hf = fppfYoneda.map b) (hα' : α' ≫ prj f hf = fppfYoneda.map b)
    {c : W ⟶ S} (hc : R.arrows c) (e : b ≫ f = c) :
    toTotHom tr f hf b α hα hc e = toTotHom tr f hf b α' hα' hc e := by
  subst hαα
  rfl

include trp in
/-- The transport of a section along a transition isomorphism lies over the refined base. -/
lemma trans_fst_proj {X Y W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (g : Y ⟶ X)
    (h : Y ⟶ S) (hh : g ≫ f = h) (hh' : R.arrows h) (b : W ⟶ Y)
    (α : fppfYoneda.obj W ⟶ sheaf h hh') (hα : α ≫ prj h hh' = fppfYoneda.map b) :
    (α ≫ (tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g)) ≫ prj f hf =
      fppfYoneda.map (b ≫ g) := by
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc ((tr f g h hh hf hh').hom) _ _,
    trp f g h hh hf hh', ← Category.assoc, hα, ← CategoryTheory.Functor.map_comp]

include trp trt in
/-- **The cocycle identity, transport form.**  Transporting a section of `sheaf h hh'` lying over
`b : W ⟶ Y` to the member `q` of the sieve is the same as first transporting it along the
transition isomorphism attached to `g ≫ f = h` and then transporting the result. -/
lemma toTotHom_trans {X Y W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (g : Y ⟶ X)
    (h : Y ⟶ S) (hh : g ≫ f = h) (hh' : R.arrows h) (b : W ⟶ Y)
    (α : fppfYoneda.obj W ⟶ sheaf h hh') (hα : α ≫ prj h hh' = fppfYoneda.map b)
    {q : W ⟶ S} (hq' : R.arrows q) (e : b ≫ h = q) (e' : (b ≫ g) ≫ f = q) :
    toTotHom tr h hh' b α hα hq' e =
      toTotHom tr f hf (b ≫ g)
        (α ≫ (tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g))
        (trans_fst_proj tr trp f hf g h hh hh' b α hα) hq' e' := by
  refine (cancel_mono (tr h b q e hh' hq').hom).mp (pullback.hom_ext ?_ ?_)
  · -- the components in `sheaf h hh'`
    simp only [Category.assoc]
    rw [toTotHom_fst tr h hh' b α hα hq' e]
    refine (cancel_mono (tr f g h hh hf hh').hom).mp (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc]
      rw [trt f g b h q hh e hf hh' hq']
      exact (toTotHom_fst tr f hf (b ≫ g) _
        (trans_fst_proj tr trp f hf g h hh hh' b α hα) hq' e').symm
    · simp only [Category.assoc]
      have l1 : α ≫ (tr f g h hh hf hh').hom ≫ pullback.snd (prj f hf) (fppfYoneda.map g)
          = fppfYoneda.map b := by rw [trp f g h hh hf hh', hα]
      have l2 : (tr h b q e hh' hq').hom ≫ pullback.fst (prj h hh') (fppfYoneda.map b) ≫
            (tr f g h hh hf hh').hom ≫ pullback.snd (prj f hf) (fppfYoneda.map g)
          = prj q hq' ≫ fppfYoneda.map b := by
        rw [trp f g h hh hf hh', pullback.condition, ← Category.assoc,
          trp h b q e hh' hq']
      rw [l1, l2, ← Category.assoc, toTotHom_proj tr trp f hf (b ≫ g) _
        (trans_fst_proj tr trp f hf g h hh hh' b α hα) hq' e', Category.id_comp]
  · simp only [Category.assoc]
    rw [trp h b q e hh' hq', toTotHom_proj tr trp h hh' b α hα hq' e,
      toTotHom_proj tr trp f hf (b ≫ g) _ (trans_fst_proj tr trp f hf g h hh hh' b α hα)
        hq' e']

include trp in
/-- **Recognition criterion for `SieveDescent.sectionTot`.**  A section of the total presheaf
lying over the member `c` of the sieve is the one attached to a section of `sheaf f hf` as soon
as its associated morphism is the transport of that section. -/
lemma sectionTot_eq {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (y : {y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b})
    (hα : Scheme.fppfTopology.yonedaEquiv.symm y.1 ≫ prj f hf = fppfYoneda.map b)
    (c : {c : W ⟶ S // R.arrows c}) (e : b ≫ f = c.1) (ξ : Fib sheaf prj W c)
    (hξ : fibHom ξ = toTotHom tr f hf b (Scheme.fppfTopology.yonedaEquiv.symm y.1) hα c.2 e) :
    sectionTot tr trp f hf b y = ⟨c, ξ⟩ := by
  obtain ⟨c, hc⟩ := c
  dsimp only at e hξ
  subst e
  refine congrArg (Sigma.mk _) (fib_ext ?_)
  rw [fibHom_fibOfHom]
  exact hξ.symm

include trp in
/-- The morphism attached to the section of the total presheaf determined by a section of
`sheaf f hf`. -/
lemma fibHom_sectionTot {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (y : {y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b})
    (hα : Scheme.fppfTopology.yonedaEquiv.symm y.1 ≫ prj f hf = fppfYoneda.map b) :
    fibHom (sectionTot tr trp f hf b y).2 =
      toTotHom tr f hf b (Scheme.fppfTopology.yonedaEquiv.symm y.1) hα
        (R.downward_closed hf b) rfl :=
  fibHom_fibOfHom _ _ (toTotHom_proj tr trp f hf b _ hα (R.downward_closed hf b) rfl)

include trp in
/-- Congruence of `SieveDescent.sectionTot` in the base of the section. -/
lemma sectionTot_congr {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) {b b' : W ⟶ X}
    (hb : b = b') (y : {y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b})
    (y' : {y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b'}) (hy : y.1 = y'.1) :
    sectionTot tr trp f hf b y = sectionTot tr trp f hf b' y' := by
  subst hb
  obtain rfl : y = y' := Subtype.ext hy
  rfl

include trp trt in
/-- The restriction of a fibre element whose associated morphism is the transport of a section
of `sheaf f hf`. -/
lemma fibHom_resAux_eq {X V W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (u : V ⟶ W)
    (b : W ⟶ X) (ξ₀ : Fib sheaf prj W ⟨b ≫ f, R.downward_closed hf b⟩)
    (α : fppfYoneda.obj W ⟶ sheaf f hf) (hα : α ≫ prj f hf = fppfYoneda.map b)
    (hα' : (fppfYoneda.map u ≫ α) ≫ prj f hf = fppfYoneda.map (u ≫ b))
    (hfib : fibHom ξ₀ = toTotHom tr f hf b α hα (R.downward_closed hf b) rfl) :
    fibHom (resAux tr trp u ⟨b ≫ f, R.downward_closed hf b⟩
        (R.downward_closed (R.downward_closed hf b) u) rfl ξ₀)
      = toTotHom tr f hf (u ≫ b) (fppfYoneda.map u ≫ α) hα'
          (R.downward_closed (R.downward_closed hf b) u) (Category.assoc u b f) := by
  have hres1 : (fppfYoneda.map u ≫ fibHom ξ₀) ≫ prj (b ≫ f) (R.downward_closed hf b)
      = fppfYoneda.map u := by rw [Category.assoc, fibHom_comp, Category.comp_id]
  have hres2 : (fppfYoneda.map u ≫ toTotHom tr f hf b α hα (R.downward_closed hf b) rfl) ≫
      prj (b ≫ f) (R.downward_closed hf b) = fppfYoneda.map u := by
    rw [Category.assoc, toTotHom_proj tr trp f hf b α hα (R.downward_closed hf b) rfl,
      Category.comp_id]
  refine Eq.trans (fibHom_resAux tr trp u ⟨b ≫ f, R.downward_closed hf b⟩
    (R.downward_closed (R.downward_closed hf b) u) rfl ξ₀) ?_
  refine Eq.trans (toTotHom_congr_arg tr (b ≫ f) (R.downward_closed hf b) u
    (congrArg (fun m => fppfYoneda.map u ≫ m) hfib) hres1 hres2
    (R.downward_closed (R.downward_closed hf b) u) rfl) ?_
  refine Eq.trans (toTotHom_trans tr trp trt f hf b (b ≫ f) rfl (R.downward_closed hf b) u
    _ hres2 (R.downward_closed (R.downward_closed hf b) u) rfl (Category.assoc u b f)) ?_
  refine toTotHom_congr_arg tr f hf (u ≫ b) ?_ _ _ _ _
  rw [Category.assoc, toTotHom_fst]

include trt in
/-- **Naturality of `SieveDescent.sectionTot`.**  Restricting the section of the total presheaf
attached to a section of `sheaf f hf` is the section attached to the restriction. -/
lemma sectionTot_res {X V W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (u : V ⟶ W)
    (b : W ⟶ X) (y : {y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b}) :
    (tot tr trp trt).map u.op (sectionTot tr trp f hf b y) =
      sectionTot tr trp f hf (u ≫ b)
        ⟨(sheaf f hf).obj.map u.op y.1, by rw [base_map, y.2]⟩ := by
  have hα0 : Scheme.fppfTopology.yonedaEquiv.symm y.1 ≫ prj f hf = fppfYoneda.map b := by
    rw [yonedaEquiv_symm_comp_prj, y.2]
  have hα1 : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm y.1) ≫ prj f hf
      = fppfYoneda.map (u ≫ b) := by
    rw [Category.assoc, hα0, ← CategoryTheory.Functor.map_comp]
  obtain ⟨ξ₀, hξ₀, hfib⟩ : ∃ ξ₀ : Fib sheaf prj W ⟨b ≫ f, R.downward_closed hf b⟩,
      sectionTot tr trp f hf b y = ⟨⟨b ≫ f, R.downward_closed hf b⟩, ξ₀⟩ ∧
        fibHom ξ₀ = toTotHom tr f hf b (Scheme.fppfTopology.yonedaEquiv.symm y.1) hα0
          (R.downward_closed hf b) rfl :=
    ⟨(sectionTot tr trp f hf b y).2, rfl, fibHom_sectionTot tr trp f hf b y hα0⟩
  rw [hξ₀]
  have h1 : (tot tr trp trt).map u.op
        (⟨⟨b ≫ f, R.downward_closed hf b⟩, ξ₀⟩ :
          Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c)
      = ⟨⟨u ≫ b ≫ f, R.downward_closed (R.downward_closed hf b) u⟩,
          resAux tr trp u ⟨b ≫ f, R.downward_closed hf b⟩
            (R.downward_closed (R.downward_closed hf b) u) rfl ξ₀⟩ := rfl
  rw [h1]
  refine (sectionTot_eq tr trp f hf (u ≫ b) _ ?_
    ⟨u ≫ b ≫ f, R.downward_closed (R.downward_closed hf b) u⟩ (Category.assoc u b f) _ ?_).symm
  · rw [yonedaEquiv_symm_comp_prj, base_map, y.2]
  · refine Eq.trans (fibHom_resAux_eq tr trp trt f hf u b ξ₀
      (Scheme.fppfTopology.yonedaEquiv.symm y.1) hα0 hα1 hfib) ?_
    refine toTotHom_congr_arg tr f hf (u ≫ b) ?_ _ _ _ _
    rw [GrothendieckTopology.yonedaEquiv_symm_naturality_left]

include trt in
/-- The section of the total presheaf attached to a section of `sheaf f hf` determines that
section. -/
lemma sectionTot_injective {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (y₁ y₂ : {y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b})
    (hy : sectionTot tr trp f hf b y₁ = sectionTot tr trp f hf b y₂) : y₁ = y₂ := by
  have h3 := ev_congr tr (b ≫ f) (R.downward_closed hf b) hy (𝟙 W)
    (by rw [sectionTot_fst tr trp, Category.id_comp])
    (by rw [sectionTot_fst tr trp, Category.id_comp])
  rw [ev_sectionTot tr trp trt f hf b y₁, ev_sectionTot tr trp trt f hf b y₂] at h3
  refine Subtype.ext (Scheme.fppfTopology.yonedaEquiv.symm.injective ?_)
  have e1 := fromTotHom_toTotHom tr f hf b (Scheme.fppfTopology.yonedaEquiv.symm y₁.1)
    (by rw [yonedaEquiv_symm_comp_prj, y₁.2]) (R.downward_closed hf b) (rfl : b ≫ f = b ≫ f)
  have e2 := fromTotHom_toTotHom tr f hf b (Scheme.fppfTopology.yonedaEquiv.symm y₂.1)
    (by rw [yonedaEquiv_symm_comp_prj, y₂.2]) (R.downward_closed hf b) (rfl : b ≫ f = b ≫ f)
  exact (e1.symm.trans
    (congrArg (fromTotHom tr f hf b (R.downward_closed hf b) rfl) h3)).trans e2

include trp in
/-- Every section of the total presheaf lying over `b ≫ f` comes from a section of
`sheaf f hf` lying over `b`. -/
lemma exists_sectionTot_eq {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (z : Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c) (hz : z.1.1 = b ≫ f) :
    ∃ y : {y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b},
      sectionTot tr trp f hf b y = z := by
  obtain ⟨⟨c₀, hc₀⟩, ξ₀⟩ := z
  obtain rfl : c₀ = b ≫ f := hz
  have hsplit := fromTotHom_comp_prj tr trp f hf b hc₀ rfl _ (fibHom_comp ξ₀)
  refine ⟨⟨Scheme.fppfTopology.yonedaEquiv (fromTotHom tr f hf b hc₀ rfl (fibHom ξ₀)), ?_⟩, ?_⟩
  · rw [base, ← GrothendieckTopology.yonedaEquiv_comp, hsplit,
      GrothendieckTopology.yonedaEquiv_yoneda_map]
  · refine sectionTot_eq tr trp f hf b _ ?_ ⟨b ≫ f, hc₀⟩ rfl ξ₀ ?_
    · rw [Equiv.symm_apply_apply]
      exact hsplit
    · refine Eq.trans ?_ (toTotHom_congr_arg tr f hf b (Equiv.symm_apply_apply _ _).symm
        hsplit _ hc₀ rfl)
      exact (toTotHom_fromTotHom tr trp f hf b hc₀ rfl _ (fibHom_comp ξ₀)).symm

variable {A : FppfSheaf.{u}} {π : A ⟶ fppfYoneda.obj S} (Φ : tot tr trp trt ⟶ A.obj)

/-- The partially defined morphism from `sheaf f hf` to the glued sheaf: a section is sent to
the image under `Φ` of the associated section of the total presheaf. -/
noncomputable def glueData {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    PartialHom (prj f hf) A (⊤ : Sieve X) where
  app {W} x := Φ.app (op W) (sectionTot tr trp f hf (base (prj f hf) x.1) ⟨x.1, rfl⟩)
  naturality {V W} u x := by
    refine Eq.trans (nat_apply Φ u.op _).symm ?_
    rw [sectionTot_res tr trp trt f hf u]
    exact congrArg (Φ.app (op V))
      (sectionTot_congr tr trp f hf (base_map (prj f hf) u x.1).symm
        ⟨(sheaf f hf).obj.map u.op x.1, by rw [base_map]⟩
        ⟨(sheaf f hf).obj.map u.op x.1, rfl⟩ rfl)

/-- The morphism from `sheaf f hf` to the glued sheaf attached to a member of the sieve. -/
noncomputable def glueHom {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) : sheaf f hf ⟶ A :=
  (glueData tr trp trt Φ f hf).glue (Scheme.fppfTopology.top_mem X)

/-- The value of `glueHom` on a section. -/
lemma glueHom_app {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f)
    (x : (sheaf f hf).obj.obj (op W)) :
    (glueHom tr trp trt Φ f hf).hom.app (op W) x =
      Φ.app (op W) (sectionTot tr trp f hf (base (prj f hf) x) ⟨x, rfl⟩) :=
  (glueData tr trp trt Φ f hf).glue_app (Scheme.fppfTopology.top_mem X)
    ⟨x, Sieve.top_apply _⟩

variable (hΦbase : ∀ (W : Scheme.{u}) (z : Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c),
  base π (Φ.app (op W) z) = z.1.1)

include hΦbase in
/-- `glueHom` is a morphism over `S`. -/
lemma glueHom_comp {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    glueHom tr trp trt Φ f hf ≫ π = prj f hf ≫ fppfYoneda.map f := by
  refine hom_ext_of_sieve (prj f hf) (Scheme.fppfTopology.top_mem X) fun W x => ?_
  change base π ((glueHom tr trp trt Φ f hf).hom.app (op W) x.1) =
    base (prj f hf ≫ fppfYoneda.map f) x.1
  rw [glueHom_app, hΦbase W _, base_comp_yoneda]
  exact sectionTot_fst tr trp f hf _ _

include trt in
/-- **Compatibility of the glued morphisms with the transition isomorphisms.** -/
lemma glueHom_trans {X Y : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (g : Y ⟶ X) (h : Y ⟶ S)
    (hh : g ≫ f = h) (hh' : R.arrows h) :
    glueHom tr trp trt Φ h hh' = (tr f g h hh hf hh').hom ≫
      pullback.fst (prj f hf) (fppfYoneda.map g) ≫ glueHom tr trp trt Φ f hf := by
  refine hom_ext_of_sieve (prj h hh') (Scheme.fppfTopology.top_mem Y) fun W x => ?_
  have hbase : base (prj f hf)
      (((tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g)).hom.app
        (op W) x.1) = base (prj h hh') x.1 ≫ g := by
    have h1 : ((tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g)) ≫
        prj f hf = prj h hh' ≫ fppfYoneda.map g := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, trp f g h hh hf hh']
    have h2 := congrArg (fun m : sheaf h hh' ⟶ fppfYoneda.obj X => base m x.1) h1
    exact h2.trans (base_comp_yoneda (prj h hh') g x.1)
  have hα0 : Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ prj h hh'
      = fppfYoneda.map (base (prj h hh') x.1) := by rw [yonedaEquiv_symm_comp_prj]
  have hα1 : Scheme.fppfTopology.yonedaEquiv.symm
        (((tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g)).hom.app
          (op W) x.1) ≫ prj f hf
      = fppfYoneda.map (base (prj h hh') x.1 ≫ g) := by
    rw [yonedaEquiv_symm_comp_prj, hbase]
  obtain ⟨ξ₀, hξ₀, hfib⟩ : ∃ ξ₀ : Fib sheaf prj W
        ⟨base (prj h hh') x.1 ≫ h, R.downward_closed hh' _⟩,
      sectionTot tr trp h hh' (base (prj h hh') x.1) ⟨x.1, rfl⟩
          = ⟨⟨base (prj h hh') x.1 ≫ h, R.downward_closed hh' _⟩, ξ₀⟩ ∧
        fibHom ξ₀ = toTotHom tr h hh' (base (prj h hh') x.1)
          (Scheme.fppfTopology.yonedaEquiv.symm x.1) hα0 (R.downward_closed hh' _) rfl :=
    ⟨_, rfl, fibHom_sectionTot tr trp h hh' (base (prj h hh') x.1) ⟨x.1, rfl⟩ hα0⟩
  have key : sectionTot tr trp f hf (base (prj h hh') x.1 ≫ g)
        ⟨((tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g)).hom.app
          (op W) x.1, hbase⟩
      = ⟨⟨base (prj h hh') x.1 ≫ h, R.downward_closed hh' _⟩, ξ₀⟩ := by
    refine sectionTot_eq tr trp f hf (base (prj h hh') x.1 ≫ g) _ hα1
      ⟨base (prj h hh') x.1 ≫ h, R.downward_closed hh' _⟩ (by rw [Category.assoc, hh]) ξ₀ ?_
    rw [hfib]
    refine Eq.trans (toTotHom_trans tr trp trt f hf g h hh hh' (base (prj h hh') x.1) _
      hα0 (R.downward_closed hh' _) rfl (by rw [Category.assoc, hh])) ?_
    refine toTotHom_congr_arg tr f hf _ ?_ _ _ _ _
    rw [GrothendieckTopology.yonedaEquiv_symm_naturality_right]
  change (glueHom tr trp trt Φ h hh').hom.app (op W) x.1 =
    (glueHom tr trp trt Φ f hf).hom.app (op W)
      (((tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g)).hom.app
        (op W) x.1)
  rw [glueHom_app, glueHom_app]
  exact congrArg (Φ.app (op W)) ((hξ₀.trans key.symm).trans
    (sectionTot_congr tr trp f hf hbase.symm
      ⟨((tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g)).hom.app
        (op W) x.1, hbase⟩
      ⟨((tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g)).hom.app
        (op W) x.1, rfl⟩ rfl))

include hΦbase in
/-- The comparison morphism from `sheaf f hf` to the base change of the glued sheaf along a
member `f` of the sieve. -/
noncomputable def glueLift {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    sheaf f hf ⟶ pullback π (fppfYoneda.map f) :=
  pullback.lift (glueHom tr trp trt Φ f hf) (prj f hf) (glueHom_comp tr trp trt Φ hΦbase f hf)

include hΦbase in
/-- The first projection of `glueLift` is `glueHom`. -/
lemma glueLift_fst {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    glueLift tr trp trt Φ hΦbase f hf ≫ pullback.fst π (fppfYoneda.map f) =
      glueHom tr trp trt Φ f hf :=
  pullback.lift_fst _ _ _

include hΦbase in
/-- The second projection of `glueLift` is the structure morphism of `sheaf f hf`. -/
lemma glueLift_snd {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    glueLift tr trp trt Φ hΦbase f hf ≫ pullback.snd π (fppfYoneda.map f) = prj f hf :=
  pullback.lift_snd _ _ _

variable (hΦbij : ∀ (W : Scheme.{u}) (c : W ⟶ S), R.arrows c →
  (∀ z z' : Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c,
      z.1.1 = c → z'.1.1 = c → Φ.app (op W) z = Φ.app (op W) z' → z = z') ∧
    ∀ a : A.obj.obj (op W), base π a = c →
      ∃ z : Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c, z.1.1 = c ∧ Φ.app (op W) z = a)

include hΦbase hΦbij in
/-- **The comparison morphism is an isomorphism.**  Both injectivity and surjectivity on
sections come from the fibrewise bijections of `SieveDescent.exists_glue_fibrewise`. -/
theorem isIso_glueLift {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    IsIso (glueLift tr trp trt Φ hΦbase f hf) := by
  refine isIso_of_sections (prj f hf) (pullback.snd π (fppfYoneda.map f))
    (Scheme.fppfTopology.top_mem X) _ (glueLift_snd tr trp trt Φ hΦbase f hf) fun W y => ?_
  obtain ⟨b, hb⟩ : ∃ b, base (pullback.snd π (fppfYoneda.map f)) y.1 = b := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, (pullback.fst π (fppfYoneda.map f)).hom.app (op W) y.1 = a := ⟨_, rfl⟩
  have hab : base π a = b ≫ f := by
    rw [← ha, ← hb]
    exact (congrArg (fun m : pullback π (fppfYoneda.map f) ⟶ fppfYoneda.obj S => base m y.1)
      (pullback.condition (f := π) (g := fppfYoneda.map f))).trans
      (base_comp_yoneda (pullback.snd π (fppfYoneda.map f)) f y.1)
  have hfstapp : ∀ x : (sheaf f hf).obj.obj (op W),
      (pullback.fst π (fppfYoneda.map f)).hom.app (op W)
          ((glueLift tr trp trt Φ hΦbase f hf).hom.app (op W) x) =
        (glueHom tr trp trt Φ f hf).hom.app (op W) x := fun x =>
    congrArg (fun m : sheaf f hf ⟶ A => m.hom.app (op W) x)
      (glueLift_fst tr trp trt Φ hΦbase f hf)
  have hsndapp : ∀ x : (sheaf f hf).obj.obj (op W),
      (pullback.snd π (fppfYoneda.map f)).hom.app (op W)
          ((glueLift tr trp trt Φ hΦbase f hf).hom.app (op W) x) = base (prj f hf) x := fun x =>
    congrArg (fun m : sheaf f hf ⟶ fppfYoneda.obj X => m.hom.app (op W) x)
      (glueLift_snd tr trp trt Φ hΦbase f hf)
  obtain ⟨z, hz1, hz2⟩ := (hΦbij W (b ≫ f) (R.downward_closed hf b)).2 a hab
  obtain ⟨y₀, hy₀⟩ := exists_sectionTot_eq tr trp f hf b z hz1
  refine ⟨y₀.1, ?_, ?_⟩
  · refine pullback_section_ext π (fppfYoneda.map f) ?_ ?_
    · rw [hfstapp, glueHom_app]
      refine Eq.trans (congrArg (Φ.app (op W))
        (sectionTot_congr tr trp f hf y₀.2 ⟨y₀.1, rfl⟩ y₀ rfl)) ?_
      rw [hy₀]
      exact hz2.trans ha.symm
    · rw [hsndapp]
      exact y₀.2.trans hb.symm
  · intro x hx
    have hbx : base (prj f hf) x = b := by
      rw [← hsndapp x, hx]
      exact hb
    have hax : (glueHom tr trp trt Φ f hf).hom.app (op W) x = a := by
      rw [← hfstapp x, hx]
      exact ha
    have h1 : Φ.app (op W) (sectionTot tr trp f hf b ⟨x, hbx⟩) = a := by
      refine Eq.trans (congrArg (Φ.app (op W))
        (sectionTot_congr tr trp f hf hbx.symm ⟨x, hbx⟩ ⟨x, rfl⟩ rfl)) ?_
      rw [← glueHom_app]
      exact hax
    have h2 : sectionTot tr trp f hf b ⟨x, hbx⟩ = z :=
      (hΦbij W (b ≫ f) (R.downward_closed hf b)).1 _ _ (sectionTot_fst tr trp f hf b _) hz1
        (h1.trans hz2.symm)
    exact congrArg Subtype.val
      (sectionTot_injective tr trp trt f hf b ⟨x, hbx⟩ y₀ (h2.trans hy₀.symm))

end SieveDescentEffective

/-- **Effectivity of fppf descent for sheaves of sets.**  Every descent datum for fppf sheaves
along an fppf covering sieve of `S` is the base change of a single fppf sheaf over `S`,
compatibly with the transition isomorphisms of the datum.

This discharges the hypothesis `SheafDescentInput` of `Stacks/TorsorStack.lean`, the only
sheaf-theoretic input to effectiveness of descent for the quotient prestack `[U/G]`. -/
theorem sheafDescentInput : SheafDescentInput.{u} := by
  refine ⟨fun S R hR D => ?_⟩
  obtain ⟨A, π, Φ, hΦbase, hΦbij⟩ :=
    SieveDescent.exists_glue_fibrewise D.trans D.trans_proj D.trans_trans hR
  have hiso : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
      IsIso (SieveDescentEffective.glueLift D.trans D.trans_proj D.trans_trans Φ hΦbase f hf) :=
    fun f hf => SieveDescentEffective.isIso_glueLift D.trans D.trans_proj D.trans_trans Φ
      hΦbase hΦbij f hf
  refine ⟨A, π, fun {X} f hf => @asIso _ _ _ _ _ (hiso f hf), fun {X} f hf => ?_,
    fun {X Y} f g h hh hf hh' => ?_⟩
  · exact SieveDescentEffective.glueLift_snd D.trans D.trans_proj D.trans_trans Φ hΦbase f hf
  · rw [show ((@asIso _ _ _ _ _ (hiso h hh')).hom ≫ pullback.fst π (fppfYoneda.map h)) =
      SieveDescentEffective.glueHom D.trans D.trans_proj D.trans_trans Φ h hh' from
      SieveDescentEffective.glueLift_fst D.trans D.trans_proj D.trans_trans Φ hΦbase h hh']
    rw [show ((@asIso _ _ _ _ _ (hiso f hf)).hom ≫ pullback.fst π (fppfYoneda.map f)) =
      SieveDescentEffective.glueHom D.trans D.trans_proj D.trans_trans Φ f hf from
      SieveDescentEffective.glueLift_fst D.trans D.trans_proj D.trans_trans Φ hΦbase f hf]
    exact SieveDescentEffective.glueHom_trans D.trans D.trans_proj D.trans_trans Φ
      f hf g h hh hh'

end GromovWitten.AlgebraicGeometry
