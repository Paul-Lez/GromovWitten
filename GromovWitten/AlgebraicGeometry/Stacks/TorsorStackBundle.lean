/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorStackMathlib
import GromovWitten.AlgebraicGeometry.Stacks.GroupoidValued

/-!
# `[U/G]` is a stack for Mathlib's `Pseudofunctor.IsStack`, and its bundling

`Stacks/TorsorStackDescent.lean` proves descent of morphisms for the quotient prestack
`[U/G] = ActionTorsor.pullbackPseudofunctor G U` in the repository formulation with explicit
data (`ActionTorsor.existsUnique_hom_of_torsorHomFamily`), and
`Stacks/TorsorStackEffective.lean` together with `Stacks/TorsorStackCover.lean` proves
effectiveness of descent of objects along an arbitrary fppf covering sieve
(`ActionTorsor.exists_torsor_of_torsorDescentDatum'`).  `Stacks/TorsorStackMathlib.lean` removes
the Lean *kernel* wall that blocked the comparison with Mathlib's `Pseudofunctor.IsStack`.

This file carries out that comparison.  Its main results are

* `ActionTorsor.isPrestack_pullbackPseudofunctor` —
  `Pseudofunctor.IsPrestack Scheme.fppfTopology (pullbackPseudofunctor G U)`;
* `ActionTorsor.essSurj_toDescentData` — essential surjectivity of `Pseudofunctor.toDescentData`
  along every fppf covering sieve;
* `ActionTorsor.isStack_pullbackPseudofunctor` —
  `Pseudofunctor.IsStack Scheme.fppfTopology (pullbackPseudofunctor G U)`;
* `ActionTorsor.quotientStack G U` and `ActionTorsor.classifyingStack G`, the quotient stack
  `[U/G]` and the classifying stack `BG = [pt/G]` bundled as stacks in groupoids.

## The proof-irrelevance discipline

`Pseudofunctor.DescentData.hom`, `Pseudofunctor.DescentData.Hom.comm`,
`Pseudofunctor.LocallyDiscreteOpToCat.pullHom` and the fields `pullHom_hom`, `hom_self`,
`hom_comp` of `DescentData` all take the factorisation equations as (auto-parameter) arguments
and use them *computationally*, through `Pseudofunctor.mapComp'`.  At
`pullbackPseudofunctor G U` the Lean kernel does not identify two copies of such a term that
differ only in those proof arguments (measured in `Stacks/TorsorStackMathlib.lean`: a
deterministic timeout, against milliseconds when the proofs agree).  Every use of that API in
this file therefore goes through a *generic* restatement with the proofs as explicit arguments —
`descentData_comm_of_proofs` (from `Stacks/TorsorStackMathlib.lean`), and the new
`pullHom_eq_mapComp'`, `descentData_pullHom_of_proofs`, `descentData_hom_comp_of_proofs`,
`descentData_hom_self_of_proofs` — all proved at an arbitrary pseudofunctor, where nothing can
unfold and proof irrelevance applies immediately.

The same discipline explains the shape of the proofs: the algebraic steps are isolated in
purely categorical lemmas with explicit data (`descent_cocycle_aux`, `descent_key_aux`,
`conj_proj_aux`, `comm_left_aux`, `comm_right_aux`), because `rw` frequently fails on goals
mentioning `D.obj i` for a descent datum `D` ("the target expression is not type-correct under
the `implicit` transparency level").

## Universes: why `FppfStack` does not apply

`GromovWitten.AlgebraicGeometry.FppfStack` of `Stacks/Algebraic.lean` is
`StackInGroupoids.{u, u, u + 1, u} Scheme.{u} Scheme.fppfTopology`, i.e. its fibres are
`Cat.{u, u}`-categories; this is what represented stacks need.  The fibres of `[U/G]` are the
groupoids `ActionTorsor G U T`, which live one universe higher (`Cat.{u + 1, u + 1}`, as
recorded in `ActionTorsor.pullbackPseudofunctor`), so `[U/G]` is *not* an `FppfStack` for
purely size reasons.  `LargeFppfStack` below is the corresponding
`StackInGroupoids.{u, u + 1, u + 1, u + 1}`, and this is where `quotientStack` and
`classifyingStack` live.  Making `Stacks/Algebraic.lean` universe-polymorphic in the fibres
would identify the two notions; that file is not modified here.

## Main declarations

* `GromovWitten.AlgebraicGeometry.ActionTorsor.descentDataHom_compat`
* `GromovWitten.AlgebraicGeometry.ActionTorsor.fullyFaithfulToDescentData`
* `GromovWitten.AlgebraicGeometry.ActionTorsor.isPrestack_pullbackPseudofunctor`
* `GromovWitten.AlgebraicGeometry.ActionTorsor.descentTrans`,
  `torsorDescentDatumOfDescentData`
* `GromovWitten.AlgebraicGeometry.ActionTorsor.essSurj_toDescentData`
* `GromovWitten.AlgebraicGeometry.ActionTorsor.isStack_pullbackPseudofunctor`
* `GromovWitten.AlgebraicGeometry.LargeFppfStack`
* `GromovWitten.AlgebraicGeometry.ActionTorsor.quotientStack`,
  `ActionTorsor.classifyingStack`
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open CategoryTheory.Bicategory
open scoped CategoryTheory.MonoidalCategory
open Opposite
open _root_.AlgebraicGeometry
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace GromovWitten.AlgebraicGeometry

universe u v

section Generic

variable {C : Type*} [Category* C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u}}
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- **`pullHom` with the two coherence proofs as explicit data.**  `pullHom` is defined by the
displayed composite, but with the two `mapComp'` coherence equations discharged by `aesop`;
recording the identity generically makes it usable with *any* proofs of those equations, which
is essential because comparing two such proofs at `pullbackPseudofunctor G U` makes the kernel
diverge (see the module docstring). -/
theorem pullHom_eq_mapComp' ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂)
    (e₁ : f₁.op.toLoc ≫ g.op.toLoc = gf₁.op.toLoc)
    (e₂ : f₂.op.toLoc ≫ g.op.toLoc = gf₂.op.toLoc) :
    pullHom φ g gf₁ gf₂ h₁ h₂ =
      (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc e₁).hom.toNatTrans.app M₁ ≫
        (F.map g.op.toLoc).toFunctor.map φ ≫
          (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc e₂).inv.toNatTrans.app M₂ :=
  rfl

/-- `Pseudofunctor.DescentData.pullHom_hom` with all factorisation proofs explicit. -/
theorem descentData_pullHom_of_proofs (D : F.DescentData f) ⦃Y' Y : C⦄ (g : Y' ⟶ Y)
    (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q') ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (h₁ : gf₁ ≫ f i₁ = q')
    (h₂ : gf₂ ≫ f i₂ = q') :
    pullHom (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂ = D.hom q' gf₁ gf₂ h₁ h₂ :=
  D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂

/-- `Pseudofunctor.DescentData.hom_comp` with all factorisation proofs explicit and unrelated
on the two sides. -/
theorem descentData_hom_comp_of_proofs (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S)
    ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
    (h₁ h₁' : f₁ ≫ f i₁ = q) (h₂ h₂' : f₂ ≫ f i₂ = q) (h₃ h₃' : f₃ ≫ f i₃ = q) :
    D.hom q f₁ f₂ h₁ h₂ ≫ D.hom q f₂ f₃ h₂' h₃ = D.hom q f₁ f₃ h₁' h₃' :=
  D.hom_comp q f₁ f₂ f₃ h₁ h₂ h₃

/-- `Pseudofunctor.DescentData.hom_self` with both factorisation proofs explicit. -/
theorem descentData_hom_self_of_proofs (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄
    (g : Y ⟶ X i) (h h' : g ≫ f i = q) : D.hom q g g h h' = 𝟙 _ :=
  D.hom_self q g h

end Generic

/-- The algebraic core of the cocycle condition for the descent datum attached to a Mathlib
descent datum: in any category, the identity follows from the `hom_comp` relation `h1`, the
`pullHom_hom` relation `h2`, the two projection formulas `h3` and `h4` for the pseudofunctorial
comparison cells, the naturality `h5` of the projection and the invertibility `h6` of the
comparison with a base change along an identity. -/
theorem descent_cocycle_aux {C : Type*} [Category C]
    {Aq PidQ PkAh PkgAf Ah PidY PgAf Af Pkky Pkg : C}
    (eQ : Aq ⟶ PidQ) (u1 : PidQ ⟶ PkAh) (u2 : PkAh ⟶ PkgAf) (u3 : PidQ ⟶ PkgAf)
    (pAhk : PkAh ⟶ Ah) (eY : Ah ⟶ PidY) (eY' : PidY ⟶ Ah) (ψ : PidY ⟶ PgAf)
    (pAfg : PgAf ⟶ Af) (pAfkg : PkgAf ⟶ Af) (mY : PkAh ⟶ Pkky) (w : Pkky ⟶ Pkg)
    (nF : Pkg ⟶ PkgAf) (ppidY : Pkky ⟶ PidY) (ppg : Pkg ⟶ PgAf)
    (h1 : u1 ≫ u2 = u3) (h2 : u2 = mY ≫ w ≫ nF) (h3 : nF ≫ pAfkg = ppg ≫ pAfg)
    (h4 : mY ≫ ppidY ≫ eY' = pAhk) (h5 : ppidY ≫ ψ = w ≫ ppg)
    (h6 : ∀ {W : C} (z : PidY ⟶ W), eY' ≫ eY ≫ z = z) :
    (eQ ≫ u1) ≫ pAhk ≫ (eY ≫ ψ) ≫ pAfg = (eQ ≫ u3) ≫ pAfkg := by
  rw [← h1, h2, ← h4]
  simp only [Category.assoc]
  rw [h6, reassoc_of% h5, h3]

/-- The algebraic core of the comparison of the transition arrow `D.hom q f₁ f₂` of a descent
datum with the gluing isomorphisms, for a general pair of factorisations: split off the
factorisation through the identity (`hs2`), use the comparison for the two halves (`hF`) and
cancel the resulting identity (`hid`). -/
theorem descent_key_aux {C : Type*} [Category C] {A Bq P₂ Nb : C}
    (x : A ⟶ P₂) (c : A ⟶ Bq) (b₂ : Bq ⟶ P₂) (b₁ : Bq ⟶ A) (t₂ : P₂ ⟶ Nb) (t₁ : A ⟶ Nb)
    (hs2 : x = c ≫ b₂) (hF : b₂ ≫ t₂ = b₁ ≫ t₁) (hid : c ≫ b₁ = 𝟙 A) :
    x ≫ t₂ = t₁ := by
  rw [hs2, Category.assoc, hF, ← Category.assoc, hid, Category.id_comp]

/-- Conjugating an equality of arrows by a base-changed isomorphism: the algebraic step behind
`ActionTorsor.hom_ext_proj_iso`. -/
theorem conj_proj_aux {C : Type*} [Category C] {P A' B' Q Z Nb : C} (αh βh : P ⟶ A')
    (mh : A' ⟶ B') (pB : B' ⟶ Q) (pA : A' ⟶ Z) (ν : Z ⟶ Q) (pN : Q ⟶ Nb)
    (hm : mh ≫ pB = pA ≫ ν) (hab : αh ≫ pA ≫ ν ≫ pN = βh ≫ pA ≫ ν ≫ pN) :
    (αh ≫ mh) ≫ pB ≫ pN = (βh ≫ mh) ≫ pB ≫ pN := by
  rw [Category.assoc, Category.assoc, reassoc_of% hm]
  exact hab

/-- The algebraic core of the left-hand side of the compatibility of the gluing isomorphisms
with the transition arrows of a descent datum. -/
theorem comm_left_aux {C : Type*} [Category C] {A B₁ P₂ Q₁ Z₁ Nb : C}
    (m₁ : A ⟶ B₁) (d : B₁ ⟶ P₂) (t₂ : P₂ ⟶ Nb) (pA1 : B₁ ⟶ Q₁) (n1 : Q₁ ⟶ Z₁) (pN1 : Z₁ ⟶ Nb)
    (pf : A ⟶ Z₁) (eh : Z₁ ⟶ Q₁) (hK : d ≫ t₂ = pA1 ≫ n1 ≫ pN1) (hm : pf ≫ eh = m₁ ≫ pA1)
    (hinv : ∀ {V : C} (z : Z₁ ⟶ V), eh ≫ n1 ≫ z = z) :
    (m₁ ≫ d) ≫ t₂ = pf ≫ pN1 := by
  rw [Category.assoc, hK, ← Category.assoc, ← hm, Category.assoc, hinv]

/-- The algebraic core of the right-hand side of the compatibility of the gluing isomorphisms
with the transition arrows of a descent datum. -/
theorem comm_right_aux {C : Type*} [Category C] {A B₂ Q₂ Z₂ Nb R₂ : C} (o : A ⟶ R₂)
    (m₂ : R₂ ⟶ B₂) (pA2 : B₂ ⟶ Q₂) (n2 : Q₂ ⟶ Z₂) (pN2 : Z₂ ⟶ Nb) (pf2 : R₂ ⟶ Z₂)
    (eh2 : Z₂ ⟶ Q₂) (pf1 : A ⟶ Nb) (hm : pf2 ≫ eh2 = m₂ ≫ pA2)
    (hinv : ∀ {V : C} (z : Z₂ ⟶ V), eh2 ≫ n2 ≫ z = z) (ho : o ≫ pf2 ≫ pN2 = pf1) :
    (o ≫ m₂) ≫ pA2 ≫ n2 ≫ pN2 = pf1 := by
  rw [Category.assoc, ← reassoc_of% hm, hinv, ho]

namespace ActionTorsor

section Prestack

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {S : Scheme.{u}}
variable {ι : Type v} {X : ι → Scheme.{u}}

/-- **A morphism of Mathlib descent data for `[U/G]` satisfies the compatibility required of an
`ActionTorsor.TorsorHomFamily`.**  The compatibility equation of `Pseudofunctor.DescentData.Hom`
is used through `descentData_comm_of_proofs`, never through `Pseudofunctor.DescentData.Hom.comm`
itself: the latter carries `cat_disch`-generated factorisation proofs which the kernel cannot
compare with the ones occurring in `ActionTorsor.ofObj_hom_proj`. -/
theorem descentDataHom_compat (fam : ∀ i, X i ⟶ S) {M N : ActionTorsor G U S}
    (φ : Pseudofunctor.DescentData.ofObj (F := pullbackPseudofunctor G U) (f := fam) M ⟶
      Pseudofunctor.DescentData.ofObj (f := fam) N)
    {i₁ i₂ : ι} (g : X i₁ ⟶ X i₂) (hh : g ≫ fam i₂ = fam i₁) :
    (φ.hom i₁).iso.hom ≫ proj N (fam i₁) =
      relBaseChange M.projection (fam i₂) g (fam i₁) hh ≫
        (φ.hom i₂).iso.hom ≫ proj N (fam i₂) := by
  have hepi : Epi (proj (pullbackObj (fam i₁) M) (𝟙 (X i₁))) := inferInstance
  have hcomm := descentData_comm_of_proofs φ (i₁ := i₁) (i₂ := i₂) (fam i₁) (𝟙 (X i₁)) g
    (Category.id_comp _) (Category.id_comp _) hh hh
  have hsplit := (fibre_comp_iso_hom _ _).symm.trans
    ((congrArg (fun z ↦ (Hom.iso z).hom) hcomm).trans (fibre_comp_iso_hom _ _))
  have hA1 : proj (pullbackObj (fam i₁) M) (𝟙 (X i₁)) ≫ (φ.hom i₁).iso.hom =
      (((pullbackPseudofunctor G U).map (𝟙 (X i₁)).op.toLoc).toFunctor.map
        (φ.hom i₁)).iso.hom ≫ proj (pullbackObj (fam i₁) N) (𝟙 (X i₁)) :=
    proj_comp_map (𝟙 (X i₁)) (φ.hom i₁)
  have hA2 : proj (pullbackObj (fam i₂) M) g ≫ (φ.hom i₂).iso.hom =
      (((pullbackPseudofunctor G U).map g.op.toLoc).toFunctor.map (φ.hom i₂)).iso.hom ≫
        proj (pullbackObj (fam i₂) N) g :=
    proj_comp_map g (φ.hom i₂)
  exact descent_compat_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA1 hA2
    (ofObj_hom_proj N fam g hh) (ofObj_hom_proj M fam g hh) hsplit
    (relBaseChange_fst N.projection (fam i₂) g (fam i₁) hh) hepi

/-- The descent datum for morphisms attached to a morphism of Mathlib descent data along the
canonical family of arrows of a sieve. -/
noncomputable def torsorHomFamilyOfDescentDataHom {R : Sieve S} {M N : ActionTorsor G U S}
    (φ : Pseudofunctor.DescentData.ofObj (F := pullbackPseudofunctor G U)
        (f := fun i : R.arrows.category ↦ i.obj.hom) M ⟶
      Pseudofunctor.DescentData.ofObj (f := fun i : R.arrows.category ↦ i.obj.hom) N) :
    TorsorHomFamily M N R where
  hom f hf := φ.hom ⟨Over.mk f, hf⟩
  compat f g h hh hf hh' :=
    descentDataHom_compat _ φ (i₁ := ⟨Over.mk h, hh'⟩) (i₂ := ⟨Over.mk f, hf⟩) g hh

/-- **Descent of morphisms for `[U/G]`**: along every fppf covering sieve, the functor
`Pseudofunctor.toDescentData` of the quotient prestack is fully faithful. -/
noncomputable def fullyFaithfulToDescentData {R : Sieve S} (hR : R ∈ fppfJ.{u} S) :
    ((pullbackPseudofunctor G U).toDescentData
      (fun i : R.arrows.category ↦ i.obj.hom)).FullyFaithful where
  preimage {_ _} φ := (torsorHomFamilyOfDescentDataHom φ).glueHom hR
  map_preimage {_ N} φ := by
    refine Pseudofunctor.DescentData.hom_ext ?_
    intro i
    refine (pullbackFunctor_map_eq_iff i.obj.hom _ (φ.hom i)).2 ?_
    exact (torsorHomFamilyOfDescentDataHom φ).proj_glueSheafHom hR i.obj.hom i.property
  preimage_map {_ _} ψ := by
    refine hom_ext_of_cover_torsor hR ?_
    intro Y f hf
    exact ((torsorHomFamilyOfDescentDataHom _).proj_glueSheafHom hR f hf).trans
      (((pullbackFunctor_map_eq_iff f ψ _).1 rfl).symm)

/-- Descent of morphisms for `[U/G]` in Mathlib's formulation, for a single covering sieve. -/
theorem isPrestackFor_of_mem_fppfJ {R : Sieve S} (hR : R ∈ fppfJ.{u} S) :
    (pullbackPseudofunctor G U).IsPrestackFor R.arrows :=
  ⟨⟨fullyFaithfulToDescentData hR⟩⟩

/-- **The quotient prestack `[U/G]` is a prestack for the big fppf topology**: for every scheme
`S` and all `M N : ActionTorsor G U S`, the presheaf on `Over S` sending `p : T ⟶ S` to the type
of arrows `p^* M ⟶ p^* N` is a sheaf for the induced topology `fppfJ.over S`. -/
instance isPrestack_pullbackPseudofunctor (G : AlgebraicSpaceGroup.{u})
    (U : AlgebraicSpaceAction G) :
    (pullbackPseudofunctor G U).IsPrestack fppfJ.{u} :=
  Pseudofunctor.IsPrestack.of_isPrestackFor fun _ _ hR ↦ isPrestackFor_of_mem_fppfJ hR

end Prestack

section EssSurj

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {S : Scheme.{u}}
variable {R : Sieve S}

/-- The identity of a fibre of `[U/G]`, read on the underlying sheaf isomorphism. -/
theorem fibre_id_iso_hom {T : Scheme.{u}}
    (P : ((pullbackPseudofunctor G U).obj ⟨Opposite.op T⟩ : Cat.{u + 1, u + 1})) :
    (Hom.iso (𝟙 P)).hom = 𝟙 _ :=
  rfl

/-- The transition arrow of the repository-level descent datum attached to a Mathlib descent
datum `D` for `[U/G]`: the arrow `D.hom` for the factorisations `𝟙 ≫ h = h` and `g ≫ f = h`,
preceded by the inverse of the comparison for a base change along an identity. -/
noncomputable def descentTrans
    (D : (pullbackPseudofunctor G U).DescentData (fun i : R.arrows.category ↦ i.obj.hom))
    {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h) :
    D.obj ⟨Over.mk h, hh'⟩ ⟶ pullbackObj g (D.obj ⟨Over.mk f, hf⟩) :=
  (pullbackIdIsoApp (D.obj ⟨Over.mk h, hh'⟩)).inv ≫
    D.hom (i₁ := ⟨Over.mk h, hh'⟩) (i₂ := ⟨Over.mk f, hf⟩) h (𝟙 Y) g (Category.id_comp h) hh

/-- `ActionTorsor.descentTrans`, read on the underlying sheaf isomorphisms. -/
theorem descentTrans_iso_hom
    (D : (pullbackPseudofunctor G U).DescentData (fun i : R.arrows.category ↦ i.obj.hom))
    {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h) :
    (Hom.iso (descentTrans D f g h hh hf hh')).hom =
      (Hom.iso (pullbackIdIsoApp (D.obj ⟨Over.mk h, hh'⟩)).inv).hom ≫
        (Hom.iso (D.hom (i₁ := ⟨Over.mk h, hh'⟩) (i₂ := ⟨Over.mk f, hf⟩) h (𝟙 Y) g
          (Category.id_comp h) hh)).hom :=
  fibre_comp_iso_hom _ _

/-- **The cocycle condition for `ActionTorsor.descentTrans`.**  All the Mathlib `DescentData`
API is used through the generic explicit-proof restatements; the algebra is
`descent_cocycle_aux`. -/
theorem descentTrans_cocycle
    (D : (pullbackPseudofunctor G U).DescentData (fun i : R.arrows.category ↦ i.obj.hom))
    {X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (k : Z ⟶ Y) (h : Y ⟶ S) (q : Z ⟶ S)
    (hh : g ≫ f = h) (hq : k ≫ h = q) (hkg : (k ≫ g) ≫ f = q)
    (hf : R.arrows f) (hh' : R.arrows h) (hq' : R.arrows q) :
    (Hom.iso (descentTrans D h k q hq hh' hq')).hom ≫ proj (D.obj ⟨Over.mk h, hh'⟩) k ≫
        (Hom.iso (descentTrans D f g h hh hf hh')).hom ≫ proj (D.obj ⟨Over.mk f, hf⟩) g =
      (Hom.iso (descentTrans D f (k ≫ g) q hkg hf hq')).hom ≫
        proj (D.obj ⟨Over.mk f, hf⟩) (k ≫ g) := by
  have e₁ : (𝟙 Y).op.toLoc ≫ k.op.toLoc = k.op.toLoc := by simp
  have e₂ : g.op.toLoc ≫ k.op.toLoc = (k ≫ g).op.toLoc := by simp
  have hYid : (Hom.iso (pullbackIdIsoApp (D.obj ⟨Over.mk h, hh'⟩)).hom).hom ≫
      (Hom.iso (pullbackIdIsoApp (D.obj ⟨Over.mk h, hh'⟩)).inv).hom = 𝟙 _ :=
    (fibre_comp_iso_hom _ _).symm.trans
      ((congrArg (fun z ↦ (Hom.iso z).hom)
        (pullbackIdIsoApp (D.obj ⟨Over.mk h, hh'⟩)).hom_inv_id).trans (fibre_id_iso_hom _))
  have hA := descentData_pullHom_of_proofs D (i₁ := ⟨Over.mk h, hh'⟩) (i₂ := ⟨Over.mk f, hf⟩)
    k h q hq (𝟙 Y) g (Category.id_comp h) hh k (k ≫ g) (Category.comp_id k) rfl hq hkg
  have hB := pullHom_eq_mapComp' (F := pullbackPseudofunctor G U)
    (D.hom (i₁ := ⟨Over.mk h, hh'⟩) (i₂ := ⟨Over.mk f, hf⟩) h (𝟙 Y) g (Category.id_comp h) hh)
    k k (k ≫ g) (Category.comp_id k) rfl e₁ e₂
  have h2a := hA.symm.trans hB
  have h1 := congrArg (fun z ↦ (Hom.iso z).hom)
    (descentData_hom_comp_of_proofs D (i₁ := ⟨Over.mk q, hq'⟩) (i₂ := ⟨Over.mk h, hh'⟩)
      (i₃ := ⟨Over.mk f, hf⟩) q (𝟙 Z) k (k ≫ g) (Category.id_comp q) (Category.id_comp q)
      hq hq hkg hkg)
  rw [fibre_comp_iso_hom] at h1
  have h2 := congrArg (fun z ↦ (Hom.iso z).hom) h2a
  rw [fibre_comp_iso_hom, fibre_comp_iso_hom] at h2
  have h3 := mapComp'_inv_app_proj (D.obj ⟨Over.mk f, hf⟩) g k (k ≫ g) rfl e₂
  have h4 := mapComp'_hom_app_proj (D.obj ⟨Over.mk h, hh'⟩) (𝟙 Y) k k (Category.comp_id k) e₁
  have h5 := proj_comp_map k (D.hom (i₁ := ⟨Over.mk h, hh'⟩) (i₂ := ⟨Over.mk f, hf⟩) h (𝟙 Y) g
    (Category.id_comp h) hh)
  have h6 : ∀ {W : FppfSheaf.{u}}
      (z : (pullbackObj (𝟙 Y) (D.obj ⟨Over.mk h, hh'⟩)).P ⟶ W),
      (Hom.iso (pullbackIdIsoApp (D.obj ⟨Over.mk h, hh'⟩)).hom).hom ≫
        (Hom.iso (pullbackIdIsoApp (D.obj ⟨Over.mk h, hh'⟩)).inv).hom ≫ z = z := by
    intro W z
    rw [← Category.assoc, hYid, Category.id_comp]
  rw [descentTrans_iso_hom, descentTrans_iso_hom, descentTrans_iso_hom]
  exact descent_cocycle_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6

/-- **The repository-level descent datum attached to a Mathlib descent datum for `[U/G]`.** -/
noncomputable def torsorDescentDatumOfDescentData
    (D : (pullbackPseudofunctor G U).DescentData (fun i : R.arrows.category ↦ i.obj.hom)) :
    TorsorDescentDatum G U S R where
  torsor f hf := D.obj ⟨Over.mk f, hf⟩
  trans f g h hh hf hh' := descentTrans D f g h hh hf hh'
  cocycle f g k h q hh hq hf hh' hq' := descentTrans_cocycle D f g k h q hh hq _ hf hh' hq'

/-- Two arrows into a base-changed equivariant torsor agree as soon as they agree after the
projection: the `pullback.snd` components agree automatically, because arrows of `[U/G]` live
over the base. -/
theorem hom_ext_pullback {X Y : Scheme.{u}} {A : ActionTorsor G U X} {P : ActionTorsor G U Y}
    (b : Y ⟶ X) (α β : P ⟶ pullbackObj b A)
    (hab : (Hom.iso α).hom ≫ proj A b = (Hom.iso β).hom ≫ proj A b) : α = β :=
  Hom.ext _ _ (Limits.pullback.hom_ext hab (α.over.trans β.over.symm))

/-- `ActionTorsor.hom_ext_pullback` for a twice base-changed equivariant torsor. -/
theorem hom_ext_proj₂ {W X Y : Scheme.{u}} {N : ActionTorsor G U X} {P : ActionTorsor G U W}
    (b : Y ⟶ X) (c : W ⟶ Y) (α β : P ⟶ pullbackObj c (pullbackObj b N))
    (hab : (Hom.iso α).hom ≫ proj₂ N b c = (Hom.iso β).hom ≫ proj₂ N b c) : α = β := by
  refine hom_ext_pullback c α β (Limits.pullback.hom_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc]
    exact hab
  · rw [Category.assoc, Category.assoc, Limits.pullback.condition, ← Category.assoc,
      ← Category.assoc, α.over, β.over]

/-- An isomorphism of a fibre of `[U/G]`, read on the underlying sheaves, cancels. -/
theorem iso_inv_hom_proj {T : Scheme.{u}} {P Q : ActionTorsor G U T} (ι : P ≅ Q)
    {V : FppfSheaf.{u}} (z : Q.P ⟶ V) :
    (Hom.iso ι.inv).hom ≫ (Hom.iso ι.hom).hom ≫ z = z := by
  have h : (Hom.iso ι.inv).hom ≫ (Hom.iso ι.hom).hom = 𝟙 Q.P :=
    (fibre_comp_iso_hom _ _).symm.trans
      ((congrArg (fun w ↦ (Hom.iso w).hom) ι.inv_hom_id).trans (fibre_id_iso_hom _))
  rw [← Category.assoc, h, Category.id_comp]

/-- Two arrows into the base change of an equivariant torsor which is *identified* with a base
change of `N` agree as soon as they agree after projecting all the way down to `N`. -/
theorem hom_ext_proj_iso {W X Y : Scheme.{u}} {A : ActionTorsor G U Y} {N : ActionTorsor G U X}
    {P : ActionTorsor G U W} (b : Y ⟶ X) (c : W ⟶ Y) (ν : A ≅ pullbackObj b N)
    (α β : P ⟶ pullbackObj c A)
    (hab : (Hom.iso α).hom ≫ proj A c ≫ (Hom.iso ν.hom).hom ≫ proj N b =
      (Hom.iso β).hom ≫ proj A c ≫ (Hom.iso ν.hom).hom ≫ proj N b) : α = β := by
  refine (cancel_mono (((pullbackPseudofunctor G U).map c.op.toLoc).toFunctor.map ν.hom)).1 ?_
  refine hom_ext_proj₂ b c _ _ ?_
  exact (congrArg (fun w ↦ w ≫ proj₂ N b c) (fibre_comp_iso_hom α _)).trans
    ((conj_proj_aux _ _ _ _ _ _ _ (proj_comp_map c ν.hom).symm hab).trans
      (congrArg (fun w ↦ w ≫ proj₂ N b c) (fibre_comp_iso_hom β _)).symm)

/-- The composite of the two pseudofunctorial comparison cells occurring in the transition arrow
of `Pseudofunctor.DescentData.ofObj N`, read on the iterated projections to `N`.  This is
`ActionTorsor.mapComp'_pair_proj` for a general pair of factorisations. -/
theorem mapComp'_pair_proj₂ (N : ActionTorsor G U S) {X₁ X₂ W : Scheme.{u}} (b₁ : X₁ ⟶ S)
    (b₂ : X₂ ⟶ S) (f₁ : W ⟶ X₁) (f₂ : W ⟶ X₂) (q : W ⟶ S) (h₁ : f₁ ≫ b₁ = q)
    (h₂ : f₂ ≫ b₂ = q) (e₁ : b₁.op.toLoc ≫ f₁.op.toLoc = q.op.toLoc)
    (e₂ : b₂.op.toLoc ≫ f₂.op.toLoc = q.op.toLoc) :
    (Hom.iso (((pullbackPseudofunctor G U).mapComp' b₁.op.toLoc f₁.op.toLoc q.op.toLoc
          e₁).inv.toNatTrans.app N ≫
        ((pullbackPseudofunctor G U).mapComp' b₂.op.toLoc f₂.op.toLoc q.op.toLoc
          e₂).hom.toNatTrans.app N)).hom ≫ proj₂ N b₂ f₂ = proj₂ N b₁ f₁ := by
  rw [fibre_comp_iso_hom]
  exact Eq.trans (Category.assoc _ _ _)
    (Eq.trans (congrArg (fun z ↦ _ ≫ z) (mapComp'_hom_app_proj N b₂ f₂ q h₂ e₂))
      (mapComp'_inv_app_proj N b₁ f₁ q h₁ e₁))

/-- The transition arrow of `Pseudofunctor.DescentData.ofObj N`, read on the iterated
projections to `N`, for a general pair of factorisations. -/
theorem ofObj_hom_proj₂ {κ : Type v} {Xf : κ → Scheme.{u}} (fam : ∀ i, Xf i ⟶ S)
    (N : ActionTorsor G U S) {W : Scheme.{u}} (q : W ⟶ S) {i₁ i₂ : κ}
    (f₁ : W ⟶ Xf i₁) (f₂ : W ⟶ Xf i₂) (h₁ : f₁ ≫ fam i₁ = q) (h₂ : f₂ ≫ fam i₂ = q) :
    (Hom.iso ((Pseudofunctor.DescentData.ofObj (F := pullbackPseudofunctor G U) (f := fam)
        N).hom q f₁ f₂ h₁ h₂)).hom ≫ proj₂ N (fam i₂) f₂ = proj₂ N (fam i₁) f₁ :=
  mapComp'_pair_proj₂ N (fam i₁) (fam i₂) f₁ f₂ q h₁ h₂ _ _

/-- **The gluing isomorphisms produced by effective descent are compatible with the transition
arrows of the descent datum, for an arbitrary pair of factorisations** — not only for the pairs
`(𝟙, g)` in which the compatibility is given. -/
theorem descentData_hom_proj_eps
    (D : (pullbackPseudofunctor G U).DescentData (fun i : R.arrows.category ↦ i.obj.hom))
    (N : ActionTorsor G U S)
    (ε : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
      D.obj ⟨Over.mk f, hf⟩ ≅ pullbackObj f N)
    (hε : ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
      (hf : R.arrows f) (hh' : R.arrows h),
      (Hom.iso (ε h hh').hom).hom ≫ proj N h =
        (Hom.iso (descentTrans D f g h hh hf hh')).hom ≫ proj (D.obj ⟨Over.mk f, hf⟩) g ≫
          (Hom.iso (ε f hf).hom).hom ≫ proj N f)
    {X₁ X₂ W : Scheme.{u}} (b₁ : X₁ ⟶ S) (b₂ : X₂ ⟶ S) (hb₁ : R.arrows b₁) (hb₂ : R.arrows b₂)
    (q : W ⟶ S) (hq' : R.arrows q) (f₁ : W ⟶ X₁) (f₂ : W ⟶ X₂)
    (h₁ : f₁ ≫ b₁ = q) (h₂ : f₂ ≫ b₂ = q) :
    (Hom.iso (D.hom (i₁ := ⟨Over.mk b₁, hb₁⟩) (i₂ := ⟨Over.mk b₂, hb₂⟩) q f₁ f₂ h₁ h₂)).hom ≫
        proj (D.obj ⟨Over.mk b₂, hb₂⟩) f₂ ≫ (Hom.iso (ε b₂ hb₂).hom).hom ≫ proj N b₂ =
      proj (D.obj ⟨Over.mk b₁, hb₁⟩) f₁ ≫ (Hom.iso (ε b₁ hb₁).hom).hom ≫ proj N b₁ := by
  have hepi : Epi (Hom.iso (pullbackIdIsoApp (D.obj ⟨Over.mk q, hq'⟩)).inv).hom := inferInstance
  have E₁ := hε b₁ f₁ q h₁ hb₁ hq'
  have E₂ := hε b₂ f₂ q h₂ hb₂ hq'
  rw [descentTrans_iso_hom] at E₁ E₂
  have hF := (cancel_epi (Hom.iso (pullbackIdIsoApp (D.obj ⟨Over.mk q, hq'⟩)).inv).hom).1
    ((Category.assoc _ _ _).symm.trans (E₂.symm.trans (E₁.trans (Category.assoc _ _ _))))
  have hid := (fibre_comp_iso_hom _ _).symm.trans
    ((congrArg (fun z ↦ (Hom.iso z).hom)
      ((descentData_hom_comp_of_proofs D (i₁ := ⟨Over.mk b₁, hb₁⟩) (i₂ := ⟨Over.mk q, hq'⟩)
          (i₃ := ⟨Over.mk b₁, hb₁⟩) q f₁ (𝟙 W) f₁ h₁ h₁ (Category.id_comp q)
          (Category.id_comp q) h₁ h₁).trans
        (descentData_hom_self_of_proofs D (i := ⟨Over.mk b₁, hb₁⟩) q f₁ h₁ h₁))).trans
      (fibre_id_iso_hom _))
  have hsplit := (descentData_hom_comp_of_proofs D (i₁ := ⟨Over.mk b₁, hb₁⟩)
      (i₂ := ⟨Over.mk q, hq'⟩) (i₃ := ⟨Over.mk b₂, hb₂⟩) q f₁ (𝟙 W) f₂
      h₁ h₁ (Category.id_comp q) (Category.id_comp q) h₂ h₂).symm
  have hs2 := (congrArg (fun z ↦ (Hom.iso z).hom) hsplit).trans (fibre_comp_iso_hom _ _)
  exact descent_key_aux _ _ _ _ _ _ hs2 hF hid

/-- `ActionTorsor.descentData_hom_proj_eps`, stated for the canonical indexing of a covering
sieve. -/
theorem descentData_hom_proj_eps'
    (D : (pullbackPseudofunctor G U).DescentData (fun i : R.arrows.category ↦ i.obj.hom))
    (N : ActionTorsor G U S)
    (ε : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
      D.obj ⟨Over.mk f, hf⟩ ≅ pullbackObj f N)
    (hε : ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
      (hf : R.arrows f) (hh' : R.arrows h),
      (Hom.iso (ε h hh').hom).hom ≫ proj N h =
        (Hom.iso (descentTrans D f g h hh hf hh')).hom ≫ proj (D.obj ⟨Over.mk f, hf⟩) g ≫
          (Hom.iso (ε f hf).hom).hom ≫ proj N f)
    {W : Scheme.{u}} (q : W ⟶ S) (hq' : R.arrows q) {i₁ i₂ : R.arrows.category}
    (f₁ : W ⟶ i₁.obj.left) (f₂ : W ⟶ i₂.obj.left) (h₁ : f₁ ≫ i₁.obj.hom = q)
    (h₂ : f₂ ≫ i₂.obj.hom = q) :
    (Hom.iso (D.hom q f₁ f₂ h₁ h₂)).hom ≫ proj (D.obj i₂) f₂ ≫
        (Hom.iso (ε i₂.obj.hom i₂.property).hom).hom ≫ proj N i₂.obj.hom =
      proj (D.obj i₁) f₁ ≫ (Hom.iso (ε i₁.obj.hom i₁.property).hom).hom ≫
        proj N i₁.obj.hom :=
  descentData_hom_proj_eps D N ε hε i₁.obj.hom i₂.obj.hom i₁.property i₂.property q hq' f₁ f₂
    h₁ h₂

/-- **Effectiveness of fppf descent for `[U/G]` in Mathlib's formulation**: the functor
`Pseudofunctor.toDescentData` attached to an fppf covering sieve is essentially surjective. -/
theorem essSurj_toDescentData (hR : R ∈ fppfJ.{u} S) :
    ((pullbackPseudofunctor G U).toDescentData
      (fun i : R.arrows.category ↦ i.obj.hom)).EssSurj where
  mem_essImage D := by
    obtain ⟨N, ε, hε⟩ := exists_torsor_of_torsorDescentDatum' hR
      (torsorDescentDatumOfDescentData D)
    refine ⟨N, ⟨Pseudofunctor.DescentData.isoMk (fun i ↦ (ε i.obj.hom i.property).symm) ?_⟩⟩
    intro W q i₁ i₂ f₁ f₂ hf₁ hf₂
    have hq' : R.arrows q := hf₁ ▸ R.downward_closed i₁.property f₁
    refine hom_ext_proj_iso i₂.obj.hom f₂ (ε i₂.obj.hom i₂.property) _ _ ?_
    exact (comm_left_aux _ _ _ _ _ _ _ _
      (descentData_hom_proj_eps' D N ε hε q hq' f₁ f₂ _ _)
      (proj_comp_map f₁ (ε i₁.obj.hom i₁.property).inv)
      (fun z ↦ iso_inv_hom_proj (ε i₁.obj.hom i₁.property) z)).trans
      (comm_right_aux _ _ _ _ _ _ _ _ (proj_comp_map f₂ (ε i₂.obj.hom i₂.property).inv)
        (fun z ↦ iso_inv_hom_proj (ε i₂.obj.hom i₂.property) z)
        (ofObj_hom_proj₂ (fun i : R.arrows.category ↦ i.obj.hom) N q f₁ f₂ _ _)).symm

end EssSurj

/-- **The quotient prestack `[U/G]` is a stack for the big fppf topology**, in Mathlib's
formulation: descent of morphisms (`ActionTorsor.isPrestack_pullbackPseudofunctor`) together
with effectiveness of descent of objects (`ActionTorsor.essSurj_toDescentData`). -/
instance isStack_pullbackPseudofunctor (G : AlgebraicSpaceGroup.{u})
    (U : AlgebraicSpaceAction G) :
    (pullbackPseudofunctor G U).IsStack fppfJ.{u} where
  toIsPrestack := isPrestack_pullbackPseudofunctor G U
  essSurj_of_sieve _ hR := essSurj_toDescentData hR

/-- **Descent for `[U/G]` along a single fppf covering sieve**: the functor
`Pseudofunctor.toDescentData` is an equivalence onto the category of descent data. -/
theorem isStackFor_of_mem_fppfJ {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}
    {S : Scheme.{u}} {R : Sieve S} (hR : R ∈ fppfJ.{u} S) :
    (pullbackPseudofunctor G U).IsStackFor R.arrows :=
  Pseudofunctor.isStackFor' _ R hR

end ActionTorsor

/-- Groupoid-valued stacks on the big fppf site of schemes whose fibres are one universe larger
than those allowed by `GromovWitten.AlgebraicGeometry.FppfStack`.  The fibres of the quotient
stack `[U/G]` are the groupoids `ActionTorsor G U T`, which are `Cat.{u + 1, u + 1}`-categories,
so this is the home of `ActionTorsor.quotientStack`; see the module docstring. -/
abbrev LargeFppfStack :=
  StackInGroupoids.{u, u + 1, u + 1, u + 1} Scheme.{u} fppfJ.{u}

namespace ActionTorsor

/-- **The quotient stack `[U/G]`**, bundled: the pseudofunctor of equivariant fppf torsors,
its groupoid-valuedness, and the fppf stack condition. -/
noncomputable def quotientStack (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) :
    LargeFppfStack.{u} where
  toPseudofunctor := pullbackPseudofunctor G U
  isGroupoidValued := inferInstance
  isStack := isStack_pullbackPseudofunctor G U

/-- **The classifying stack `BG = [pt/G]`**, bundled. -/
noncomputable def classifyingStack (G : AlgebraicSpaceGroup.{u}) : LargeFppfStack.{u} :=
  quotientStack G (AlgebraicSpaceAction.pointAction G)

/-- The fibre of the quotient stack `[U/G]` over a scheme `T` is the groupoid of equivariant
`G`-torsors over `T`. -/
theorem quotientStack_fiber (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (T : Scheme.{u}) :
    (quotientStack G U).toPseudofunctor.obj ⟨op T⟩ = Cat.of (ActionTorsor G U T) :=
  rfl

/-- The fibre of the classifying stack `BG` over a scheme `T` is the groupoid of equivariant
`G`-torsors over `T` with target the one-point `G`-space. -/
theorem classifyingStack_fiber (G : AlgebraicSpaceGroup.{u}) (T : Scheme.{u}) :
    (classifyingStack G).toPseudofunctor.obj ⟨op T⟩ =
      Cat.of (ActionTorsor G (AlgebraicSpaceAction.pointAction G) T) :=
  rfl

end ActionTorsor

end GromovWitten.AlgebraicGeometry
