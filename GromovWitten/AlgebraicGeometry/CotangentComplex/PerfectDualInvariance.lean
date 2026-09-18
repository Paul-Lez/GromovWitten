/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectDual

/-!
# Homotopy invariance of the termwise dual, and the dual of a perfect object

This file completes `CotangentComplex/PerfectDual.lean` on the point that was left open
there: the termwise dual `dualComplex` of a cochain complex of `R`-modules is a homotopy
functor, hence it descends to the homotopy category, hence the dual of a *perfect object* of
`DerivedCategory (ModuleCat R)` does not depend on the chosen strictly perfect representative.

Everything below is a construction or a theorem; there is no `sorry` and no new axiom.

## Main definitions

* `dualHomotopy` : the transpose of a homotopy, with the sign `(-1)^i` which the sign
  convention of `dualComplex` forces.
* `dualHomotopyEquiv` : the dual of a homotopy equivalence.
* `dualFunctor` : the induced contravariant functor on the homotopy category of cochain
  complexes of `R`-modules.
* `dualIso` : the isomorphism `Q (K'^∨) ≅ Q (K^∨)` induced by an isomorphism `Q K ≅ Q K'` of
  strictly perfect complexes in the derived category.
* `IsPerfect.rep`, `IsPerfect.dualObject` : a chosen strictly perfect representative of a
  perfect object and the dual perfect object it defines.

## Main results

* `dualHomotopy`, `dualHomotopyEquiv`, `eq_of_homotopy_dualComplexMap` : **homotopy invariance
  of the termwise dual**.
* `exists_homotopyEquiv_of_derivedIso` : an isomorphism `Q K ≅ Q L` of strictly perfect
  complexes in the derived category is `Q` of a homotopy equivalence `K ≃ L`.
* `quasiIso_dualComplexMap` : the dual of a quasi-isomorphism of strictly perfect complexes is
  a quasi-isomorphism.
* `dualIso_hom_eq`, `dualIso_refl`, `dualIso_trans` : the induced comparison isomorphism is
  independent of the chosen chain map and is compatible with composition, so it is coherent.
* `IsPerfect.dualObjectIso` : **representative independence**; every strictly perfect
  representative of `E` dualises to the same object of the derived category up to a canonical
  isomorphism.
* `IsPerfect.isPerfect_dualObject`, `IsPerfect.bidualObjectIso` : the dual of a perfect object
  is perfect, and the double dual is canonically isomorphic to the original object.
* `IsPerfect.rank_dualComplex_rep` : the rank of the chosen representative is preserved by the
  dual.  The full statement `rank (dualObject h) = rank E` needs invariance of `rank` under
  homotopy equivalence (`RankHomotopyInvariant`), which is an explicit hypothesis of
  `IsPerfect.rank_eq_of_rep` and `IsPerfect.rank_dualObject`; see the discussion below.
* `bidualityIso_naturality` : the biduality isomorphism of complexes of finite free modules is
  natural, so the double dual of a chain map is its conjugate.
* `dualMap`, `dualMap_dualMap`, `dualDerivedHomEquiv`, `dualPairingSymmEquiv` : the dual of a
  derived morphism, the identification of its double dual with the biduality conjugate, and
  **full faithfulness of duality** on strictly perfect complexes,
  `(Q K ⟶ Q L) ≃ (Q (L^∨) ⟶ Q (K^∨))`, together with the symmetry
  `(Q K ⟶ Q (L^∨)) ≃ (Q L ⟶ Q (K^∨))` of the duality pairing.

## What is not proved

The alternating sum `rank` is *not* shown here to be invariant under homotopy equivalence of
strictly perfect complexes.  That statement is equivalent to the vanishing of `rank` on a
contractible bounded complex of finite free modules, i.e. to the Euler characteristic formula
`rank K = ∑ (-1)^i rank Hⁱ(K)`, which is not available in Mathlib and which is not developed
here.  Consequently the numerical invariant `IsPerfect.rank` is defined through the chosen
representative and the two theorems asserting that it is well defined and preserved by the dual
carry `RankHomotopyInvariant R` as an explicit hypothesis.  Everything else in this file is
unconditional.

The identification of the cohomology of the dual complex with Ext groups against the base ring,
`Hⁱ(K^∨) ≅ Hom_D(Q K, Q(R)⟦i⟧)`, is also not carried out: what is proved here of the
`RHom(-, R)` formalism is its functoriality and full faithfulness (`dualDerivedHomEquiv`), not
the computation of its cohomology, which would need the cycles/boundaries description of the
homology of a complex of modules together with the shift conventions for the single-complex
functor.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

/-! ## Additivity of the transpose -/

/-- The transpose of a sum of morphisms is the sum of the transposes. -/
theorem dualHom_add {M N : ModuleCat.{u} R} (g h : M ⟶ N) :
    dualHom (g + h) = dualHom g + dualHom h := by
  ext φ x
  simp [dualHom]

/-! ## The dual of a homotopy -/

section DualHomotopy

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

set_option backward.isDefEq.respectTransparency false in
/-- The transposed family of a homotopy: the component in bidegree `(i, j)` of the dual
homotopy is the transpose of the component in bidegree `(-j, -i)`, twisted by the sign
`(-1)^i` which compensates the sign convention of `dualComplex`. -/
noncomputable def dualHomotopyHom {f g : K ⟶ L} (H : Homotopy f g) (i j : ℤ) :
    (dualComplex L).X i ⟶ (dualComplex K).X j :=
  (i.negOnePow : ℤ) • dualHom (H.hom (-j) (-i))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem dualHomotopyHom_eq {f g : K ⟶ L} (H : Homotopy f g) (i j : ℤ) :
    dualHomotopyHom H i j = (i.negOnePow : ℤ) • dualHom (H.hom (-j) (-i)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Homotopy invariance of the termwise dual.**  A homotopy between two morphisms of cochain
complexes transposes to a homotopy between the two dual morphisms.  The sign `(-1)^i` on the
components is exactly what the sign `(-1)^{i+1}` in the differential of `dualComplex`
requires. -/
noncomputable def dualHomotopy {f g : K ⟶ L} (H : Homotopy f g) :
    Homotopy (dualComplexMap f) (dualComplexMap g) where
  hom := dualHomotopyHom H
  zero i j hij := by
    have hne : ¬ (ComplexShape.up ℤ).Rel (-i) (-j) := by
      intro hr
      refine hij ?_
      have h1 : (-i) + 1 = -j := hr
      change j + 1 = i
      omega
    rw [dualHomotopyHom_eq, H.zero _ _ hne, dualHom_zero, smul_zero]
  comm i := by
    have hrel₁ : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    have hrel₂ : (ComplexShape.up ℤ).Rel (i - 1) i := by
      change i - 1 + 1 = i
      omega
    have hrelK : (ComplexShape.up ℤ).Rel (-i) (-(i - 1)) := by
      change -i + 1 = -(i - 1)
      omega
    have hrelL : (ComplexShape.up ℤ).Rel (-(i + 1)) (-i) := by
      change -(i + 1) + 1 = -i
      omega
    have key := H.comm (-i)
    rw [dNext_eq H.hom hrelK, prevD_eq H.hom hrelL] at key
    rw [dNext_eq _ hrel₁, prevD_eq _ hrel₂, dualHomotopyHom_eq, dualHomotopyHom_eq,
      dualComplex_d L i (i + 1) rfl, dualComplex_d K (i - 1) i (by omega)]
    change dualHom (f.f (-i)) = _
    rw [key, dualHom_add, dualHom_add]
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← dualHom_comp,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← dualHom_comp,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
    abel

set_option backward.isDefEq.respectTransparency false in
/-- Homotopic morphisms of complexes have equal duals in the homotopy category. -/
theorem eq_of_homotopy_dualComplexMap {f g : K ⟶ L} (H : Homotopy f g) :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map (dualComplexMap f) =
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map
        (dualComplexMap g) :=
  HomotopyCategory.eq_of_homotopy _ _ (dualHomotopy H)

set_option backward.isDefEq.respectTransparency false in
/-- **The dual of a homotopy equivalence is a homotopy equivalence**, in the opposite
direction. -/
noncomputable def dualHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv (dualComplex L) (dualComplex K) where
  hom := dualComplexMap e.hom
  inv := dualComplexMap e.inv
  homotopyHomInvId :=
    ((Homotopy.ofEq (dualComplexMap_comp e.inv e.hom).symm).trans
      (dualHomotopy e.homotopyInvHomId)).trans (Homotopy.ofEq (dualComplexMap_id L))
  homotopyInvHomId :=
    ((Homotopy.ofEq (dualComplexMap_comp e.hom e.inv).symm).trans
      (dualHomotopy e.homotopyHomInvId)).trans (Homotopy.ofEq (dualComplexMap_id K))

@[simp]
theorem dualHomotopyEquiv_hom (e : HomotopyEquiv K L) :
    (dualHomotopyEquiv e).hom = dualComplexMap e.hom :=
  rfl

/-- The dual of a homotopy equivalence, as a morphism property: `dualComplexMap` preserves
homotopy equivalences. -/
theorem homotopyEquivalences_dualComplexMap {φ : K ⟶ L}
    (hφ : HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ) φ) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (dualComplexMap φ) := by
  obtain ⟨e, he⟩ := hφ
  exact ⟨dualHomotopyEquiv e, by rw [dualHomotopyEquiv_hom, he]⟩

end DualHomotopy

/-! ## The dual functor on the homotopy category -/

section DualFunctor

/-- The dual of a cochain complex, viewed as a functor into the opposite of the homotopy
category; this is the covariant form of the contravariant dual, and it is the functor that is
lifted to the homotopy category below. -/
noncomputable def dualComplexFunctorOp :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤
      (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))ᵒᵖ where
  obj K := Opposite.op ((HomotopyCategory.quotient _ _).obj (dualComplex K))
  map φ := ((HomotopyCategory.quotient _ _).map (dualComplexMap φ)).op
  map_id K := by
    rw [dualComplexMap_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp φ ψ := by
    rw [dualComplexMap_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- The dual as a functor from the homotopy category to its opposite.  It exists because
`dualComplexMap` sends homotopic morphisms to homotopic morphisms. -/
noncomputable def dualHomotopyFunctorOp :
    HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤
      (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))ᵒᵖ :=
  CategoryTheory.Quotient.lift _ dualComplexFunctorOp (by
    rintro K L f g ⟨H⟩
    exact congrArg Quiver.Hom.op (eq_of_homotopy_dualComplexMap H))

/-- **The dual as a contravariant functor on the homotopy category** of cochain complexes of
`R`-modules.  It sends the class of a complex `K` to the class of `K^∨` and the class of a
morphism `φ` to the class of `φ^∨`. -/
noncomputable def dualFunctor :
    (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))ᵒᵖ ⥤
      HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) :=
  dualHomotopyFunctorOp.leftOp

@[simp]
theorem dualFunctor_obj (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    dualFunctor.obj (Opposite.op ((HomotopyCategory.quotient _ _).obj K)) =
      (HomotopyCategory.quotient _ _).obj (dualComplex K) :=
  rfl

@[simp]
theorem dualFunctor_map {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) :
    dualFunctor.map ((HomotopyCategory.quotient _ _).map φ).op =
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map
        (dualComplexMap φ) :=
  rfl

end DualFunctor

/-! ## Quasi-isomorphisms of strictly perfect complexes are homotopy equivalences -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

/-- A strictly perfect complex is K-projective: it is a bounded above complex of projective
modules. -/
theorem IsStrictlyPerfect.isKProjective (hK : IsStrictlyPerfect K) : K.IsKProjective := by
  obtain ⟨a, b, hab⟩ := hK.bounded
  exact Modules.Derived.isKProjective_of_isStrictlyPerfect hK hab

/-- **A quasi-isomorphism of strictly perfect complexes is a homotopy equivalence.**  Both
complexes are K-projective, so Mathlib's criterion applies. -/
theorem homotopyEquivalences_of_quasiIso (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (φ : K ⟶ L) (hφ : QuasiIso φ) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ) φ := by
  have _ := hK.isKProjective
  have _ := hL.isKProjective
  exact (CochainComplex.IsKProjective.quasiIso_iff φ).1 hφ

/-- **The dual of a quasi-isomorphism of strictly perfect complexes is a
quasi-isomorphism.**  This is the derived-category form of homotopy invariance of the termwise
dual: the quasi-isomorphism is upgraded to a homotopy equivalence, which is then dualised. -/
theorem quasiIso_dualComplexMap (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (φ : K ⟶ L) (hφ : QuasiIso φ) : QuasiIso (dualComplexMap φ) := by
  have h := homotopyEquivalences_dualComplexMap
    (homotopyEquivalences_of_quasiIso hK hL φ hφ)
  have h2 := homotopyEquivalences_le_quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) _ h
  rwa [HomologicalComplex.mem_quasiIso_iff] at h2

/-- The dual of a morphism inducing an isomorphism in the derived category again induces an
isomorphism in the derived category. -/
theorem isIso_Q_map_dualComplexMap (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    {φ : K ⟶ L} (hφ : IsIso (DerivedCategory.Q.map φ)) :
    IsIso (DerivedCategory.Q.map (dualComplexMap φ)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_dualComplexMap hK hL φ ((DerivedCategory.isIso_Q_map_iff_quasiIso _ φ).1 hφ))

/-- **Every isomorphism of strictly perfect complexes in the derived category comes from a
homotopy equivalence.**  The isomorphism is realised by a chain map through K-projectivity, and
that chain map is a quasi-isomorphism between K-projective complexes, hence a homotopy
equivalence. -/
theorem exists_homotopyEquiv_of_derivedIso (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    ∃ f : HomotopyEquiv K L, DerivedCategory.Q.map f.hom = e.hom := by
  obtain ⟨φ, hφ⟩ := exists_chainMap_of_derivedMap hK e.hom
  have hiso : IsIso (DerivedCategory.Q.map φ) := by
    rw [hφ]
    exact e.isIso_hom
  obtain ⟨f, hf⟩ := homotopyEquivalences_of_quasiIso hK hL φ
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ φ).1 hiso)
  exact ⟨f, by rw [hf, hφ]⟩

/-- Two chain maps out of a strictly perfect complex with the same image in the derived
category have duals with the same image in the derived category.  This is what makes the
induced comparison isomorphism `dualIso` independent of all choices. -/
theorem Q_map_dualComplexMap_congr (hK : IsStrictlyPerfect K) {φ ψ : K ⟶ L}
    (h : DerivedCategory.Q.map φ = DerivedCategory.Q.map ψ) :
    DerivedCategory.Q.map (dualComplexMap φ) = DerivedCategory.Q.map (dualComplexMap ψ) := by
  have _ := hK.isKProjective
  have key : ∀ χ : K ⟶ L,
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map χ) =
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app K ≫
          DerivedCategory.Q.map χ ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app L := by
    intro χ
    have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality χ
    rw [Functor.comp_map] at hnat
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hq : (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map φ =
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map ψ := by
    refine (CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L)).injective ?_
    rw [key φ, key ψ, h]
  exact DerivedCategory.Q_map_eq_of_homotopy _
    (dualHomotopy (HomotopyCategory.homotopyOfEq _ _ hq))

/-- A chain map realising a given morphism of the derived category out of a strictly perfect
complex; it exists by K-projectivity and a choice is fixed once and for all here. -/
noncomputable def derivedChainMap (hK : IsStrictlyPerfect K)
    (u : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) : K ⟶ L :=
  (exists_chainMap_of_derivedMap hK u).choose

@[simp]
theorem Q_map_derivedChainMap (hK : IsStrictlyPerfect K)
    (u : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.map (derivedChainMap hK u) = u :=
  (exists_chainMap_of_derivedMap hK u).choose_spec

/-- A chain map realising a given isomorphism of the derived category between strictly perfect
complexes. -/
noncomputable abbrev derivedIsoChainMap (hK : IsStrictlyPerfect K)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) : K ⟶ L :=
  derivedChainMap hK e.hom

@[simp]
theorem Q_map_derivedIsoChainMap (hK : IsStrictlyPerfect K)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.map (derivedIsoChainMap hK e) = e.hom :=
  Q_map_derivedChainMap hK e.hom

/-- **The comparison isomorphism of duals.**  An isomorphism `Q K ≅ Q L` between strictly
perfect complexes induces an isomorphism `Q (L^∨) ≅ Q (K^∨)` of the duals; it is the image of
the dual of any chain map realising the given isomorphism. -/
noncomputable def dualIso (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.obj (dualComplex L) ≅ DerivedCategory.Q.obj (dualComplex K) :=
  have : IsIso (DerivedCategory.Q.map (dualComplexMap (derivedIsoChainMap hK e))) :=
    isIso_Q_map_dualComplexMap hK hL (by
      rw [Q_map_derivedIsoChainMap]
      exact e.isIso_hom)
  asIso (DerivedCategory.Q.map (dualComplexMap (derivedIsoChainMap hK e)))

theorem dualIso_hom (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    (dualIso hK hL e).hom =
      DerivedCategory.Q.map (dualComplexMap (derivedIsoChainMap hK e)) :=
  rfl

/-- **The comparison isomorphism does not depend on the chosen chain map**: any chain map
realising `e` computes it. -/
theorem dualIso_hom_eq (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) {φ : K ⟶ L}
    (hφ : DerivedCategory.Q.map φ = e.hom) :
    (dualIso hK hL e).hom = DerivedCategory.Q.map (dualComplexMap φ) := by
  rw [dualIso_hom]
  exact Q_map_dualComplexMap_congr hK (by rw [Q_map_derivedIsoChainMap, hφ])

/-- The comparison isomorphism attached to the identity is the identity. -/
theorem dualIso_refl (hK : IsStrictlyPerfect K) :
    dualIso hK hK (Iso.refl (DerivedCategory.Q.obj K)) = Iso.refl _ := by
  refine Iso.ext ?_
  rw [dualIso_hom_eq hK hK (Iso.refl _) (φ := 𝟙 K) (by simp), dualComplexMap_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **The comparison isomorphisms compose**, contravariantly.  Together with `dualIso_refl`
this says that the dual of a perfect object is canonical up to a coherent isomorphism. -/
theorem dualIso_trans (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (hM : IsStrictlyPerfect M) (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L)
    (e' : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj M) :
    dualIso hK hM (e ≪≫ e') = dualIso hL hM e' ≪≫ dualIso hK hL e := by
  refine Iso.ext ?_
  rw [dualIso_hom_eq hK hM (e ≪≫ e')
      (φ := derivedIsoChainMap hK e ≫ derivedIsoChainMap hL e')
      (by rw [CategoryTheory.Functor.map_comp, Q_map_derivedIsoChainMap,
        Q_map_derivedIsoChainMap]; rfl),
    dualComplexMap_comp, CategoryTheory.Functor.map_comp]
  rfl

end Derived

/-! ## The dual of a perfect object -/

section DualObject

attribute [local instance] HasDerivedCategory.standard

variable {E : DerivedCategory (ModuleCat.{u} R)}

namespace IsPerfect

/-- A chosen strictly perfect representative of a perfect object. -/
noncomputable def rep (h : IsPerfect E) : CochainComplex (ModuleCat.{u} R) ℤ := h.choose

/-- The chosen representative of a perfect object is strictly perfect. -/
theorem rep_isStrictlyPerfect (h : IsPerfect E) : IsStrictlyPerfect h.rep := h.choose_spec.1

/-- The chosen representative of a perfect object represents it. -/
noncomputable def repIso (h : IsPerfect E) : DerivedCategory.Q.obj h.rep ≅ E :=
  h.choose_spec.2.some

/-- **The dual of a perfect object**: the image in the derived category of the termwise dual of
a chosen strictly perfect representative.  By `dualObjectIso` below it is independent of the
representative up to a canonical isomorphism. -/
noncomputable def dualObject (h : IsPerfect E) : DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q.obj (dualComplex h.rep)

/-- **The dual of a perfect object is perfect.** -/
theorem isPerfect_dualObject (h : IsPerfect E) : IsPerfect h.dualObject :=
  isPerfect_Q h.rep_isStrictlyPerfect.dual

/-- **Representative independence of the dual.**  Every strictly perfect representative of `E`
has a dual canonically isomorphic to `dualObject h`. -/
noncomputable def dualObjectIso (h : IsPerfect E) {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (f : DerivedCategory.Q.obj K ≅ E) :
    DerivedCategory.Q.obj (dualComplex K) ≅ h.dualObject :=
  dualIso h.rep_isStrictlyPerfect hK (h.repIso ≪≫ f.symm)

/-- **Representative independence, symmetric form.**  Any two strictly perfect representatives
of the same object of the derived category have isomorphic duals. -/
theorem nonempty_dualComplex_iso {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hK' : IsStrictlyPerfect K')
    (f : DerivedCategory.Q.obj K ≅ E) (f' : DerivedCategory.Q.obj K' ≅ E) :
    Nonempty (DerivedCategory.Q.obj (dualComplex K) ≅
      DerivedCategory.Q.obj (dualComplex K')) :=
  ⟨dualIso hK' hK (f' ≪≫ f.symm)⟩

/-- **Biduality for perfect objects**: the dual of the dual of a perfect object is canonically
isomorphic to the object itself. -/
noncomputable def bidualObjectIso (h : IsPerfect E) :
    h.isPerfect_dualObject.dualObject ≅ E :=
  (dualIso h.isPerfect_dualObject.rep_isStrictlyPerfect h.rep_isStrictlyPerfect.dual
      h.isPerfect_dualObject.repIso).symm ≪≫
    (DerivedCategory.Q.mapIso (bidualityIso h.rep_isStrictlyPerfect.finiteFree)).symm ≪≫
      h.repIso

/-- The rank of a perfect object, computed on the chosen strictly perfect representative.
Invariance of this number under a change of representative is `rank_eq_of_rep`, which is
conditional on `RankHomotopyInvariant`. -/
noncomputable def rank (h : IsPerfect E) : ℤ := PerfectComplex.rank h.rep

/-- **The rank of the dual of the chosen representative**: unconditionally, the termwise dual of
the chosen representative has the same rank as the object. -/
theorem rank_dualComplex_rep [Nontrivial R] (h : IsPerfect E) :
    PerfectComplex.rank (dualComplex h.rep) = h.rank :=
  h.rep_isStrictlyPerfect.rank_dual

end IsPerfect

/-- Invariance of the alternating sum of ranks under homotopy equivalence of strictly perfect
complexes.  This is the Euler characteristic statement `rank K = ∑ (-1)ⁱ rank Hⁱ(K)`; it is not
proved here and not available in Mathlib, so it appears as an explicit hypothesis of the two
statements below that need it. -/
def RankHomotopyInvariant (R : Type u) [CommRing R] : Prop :=
  ∀ {K L : CochainComplex (ModuleCat.{u} R) ℤ}, IsStrictlyPerfect K → IsStrictlyPerfect L →
    HomotopyEquiv K L → PerfectComplex.rank K = PerfectComplex.rank L

/-- **Under `RankHomotopyInvariant`, the rank of a perfect object is well defined**: it can be
computed on any strictly perfect representative. -/
theorem IsPerfect.rank_eq_of_rep (hinv : RankHomotopyInvariant R) (h : IsPerfect E)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    (f : DerivedCategory.Q.obj K ≅ E) : PerfectComplex.rank K = h.rank := by
  obtain ⟨g, -⟩ := exists_homotopyEquiv_of_derivedIso hK h.rep_isStrictlyPerfect
    (f ≪≫ h.repIso.symm)
  exact hinv hK h.rep_isStrictlyPerfect g

/-- **Under `RankHomotopyInvariant`, the dual of a perfect object has the same rank.** -/
theorem IsPerfect.rank_dualObject [Nontrivial R] (hinv : RankHomotopyInvariant R)
    (h : IsPerfect E) : h.isPerfect_dualObject.rank = h.rank := by
  rw [← IsPerfect.rank_eq_of_rep hinv h.isPerfect_dualObject h.rep_isStrictlyPerfect.dual
    (Iso.refl _)]
  exact h.rank_dualComplex_rep

end DualObject

/-! ## Naturality of biduality and full faithfulness of the dual -/

section Biduality

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Comparison of the terms of a complex along an equality of degrees is natural in the
complex. -/
theorem Hom_f_comp_XIsoOfEq_hom (φ : K ⟶ L) {i j : ℤ} (h : i = j) :
    φ.f i ≫ (L.XIsoOfEq h).hom = (K.XIsoOfEq h).hom ≫ φ.f j := by
  subst h
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **Biduality is natural.**  Conjugating a morphism of complexes of finite free modules by the
biduality isomorphisms gives its double dual. -/
theorem bidualityIso_naturality (hK : ∀ i : ℤ, IsFiniteFree (K.X i))
    (hL : ∀ i : ℤ, IsFiniteFree (L.X i)) (φ : K ⟶ L) :
    φ ≫ (bidualityIso hL).hom =
      (bidualityIso hK).hom ≫ dualComplexMap (dualComplexMap φ) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  simp only [HomologicalComplex.comp_f, bidualityIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f, unitsZSMulIso_hom, bidualityXIso,
    Iso.trans_hom, evalIso_hom, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
    dualComplexMap_f]
  congr 1
  rw [← Category.assoc, Hom_f_comp_XIsoOfEq_hom φ (neg_neg i).symm, Category.assoc,
    evalHom_naturality]

end Biduality

section DualHom

attribute [local instance] HasDerivedCategory.standard

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- **The dual of a morphism of the derived category** between strictly perfect complexes: the
image of the dual of any chain map realising it. -/
noncomputable def dualMap (hK : IsStrictlyPerfect K)
    (u : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.obj (dualComplex L) ⟶ DerivedCategory.Q.obj (dualComplex K) :=
  DerivedCategory.Q.map (dualComplexMap (derivedChainMap hK u))

/-- The dual of a derived morphism is computed by any chain map realising it. -/
theorem dualMap_eq (hK : IsStrictlyPerfect K)
    {u : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L} {φ : K ⟶ L}
    (hφ : DerivedCategory.Q.map φ = u) :
    dualMap hK u = DerivedCategory.Q.map (dualComplexMap φ) :=
  Q_map_dualComplexMap_congr hK (by rw [Q_map_derivedChainMap, hφ])

/-- **The double dual of a derived morphism is its conjugate by the biduality
isomorphisms.** -/
theorem dualMap_dualMap (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (u : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    dualMap hL.dual (dualMap hK u) =
      (DerivedCategory.Q.mapIso (bidualityIso hK.finiteFree)).inv ≫ u ≫
        (DerivedCategory.Q.mapIso (bidualityIso hL.finiteFree)).hom := by
  have hφ : DerivedCategory.Q.map (derivedChainMap hK u) = u := Q_map_derivedChainMap hK u
  rw [dualMap_eq hL.dual (dualMap_eq hK hφ).symm]
  have hnat := congrArg DerivedCategory.Q.map
    (bidualityIso_naturality hK.finiteFree hL.finiteFree (derivedChainMap hK u))
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hφ] at hnat
  rw [eq_comm, Iso.inv_comp_eq]
  simpa using hnat

/-- Dualising derived morphisms out of a strictly perfect complex is injective. -/
theorem dualMap_injective (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    Function.Injective
      (dualMap hK : (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) → _) := by
  intro u v huv
  have h := congrArg (dualMap hL.dual) huv
  rw [dualMap_dualMap hK hL, dualMap_dualMap hK hL] at h
  have h2 := (cancel_epi (DerivedCategory.Q.mapIso (bidualityIso hK.finiteFree)).inv).1 h
  exact (cancel_mono (DerivedCategory.Q.mapIso (bidualityIso hL.finiteFree)).hom).1 h2

/-- **Duality is fully faithful on strictly perfect complexes**: the termwise dual induces a
bijection between derived morphisms `Q K ⟶ Q L` and derived morphisms
`Q (L^∨) ⟶ Q (K^∨)`.  This is the derived-category form of the statement that
`RHom(-, R)` is an anti-equivalence on perfect complexes. -/
noncomputable def dualDerivedHomEquiv (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) ≃
      (DerivedCategory.Q.obj (dualComplex L) ⟶ DerivedCategory.Q.obj (dualComplex K)) where
  toFun u := dualMap hK u
  invFun v := (DerivedCategory.Q.mapIso (bidualityIso hK.finiteFree)).hom ≫
    dualMap hL.dual v ≫ (DerivedCategory.Q.mapIso (bidualityIso hL.finiteFree)).inv
  left_inv u := by
    simp [dualMap_dualMap hK hL]
  right_inv v := by
    refine dualMap_injective hL.dual hK.dual ?_
    simp [dualMap_dualMap hK hL]

@[simp]
theorem dualDerivedHomEquiv_apply (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (u : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    dualDerivedHomEquiv hK hL u = dualMap hK u :=
  rfl

/-- **Symmetry of the duality pairing**: derived morphisms `Q K ⟶ Q (L^∨)` correspond to
derived morphisms `Q L ⟶ Q (K^∨)`.  This is the perfect-complex form of the symmetry of
`RHom(E ⊗ F, R)`. -/
noncomputable def dualPairingSymmEquiv (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (dualComplex L)) ≃
      (DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj (dualComplex K)) :=
  (dualDerivedHomEquiv hK hL.dual).trans
    (Iso.homCongr (DerivedCategory.Q.mapIso (bidualityIso hL.finiteFree)).symm (Iso.refl _))

end DualHom

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
