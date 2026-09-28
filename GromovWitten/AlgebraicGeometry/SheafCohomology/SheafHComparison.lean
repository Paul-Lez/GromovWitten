/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.OpenRestriction
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Comparison of `Sheaf.H` with derived global sections

The sheaf cohomology functor in Mathlib is Ext from the constant free abelian
sheaf on `ULift ℤ`.  This file identifies that Ext model with the homology of
the global-sections complex of an injective resolution.  The latter is also the
model used by the right-derived global-sections API.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.ShortComplex
open CochainComplex HomComplex Opposite TopologicalSpace
noncomputable section

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

universe u v w

variable {X : TopCat.{u}}

def isoToAddEquiv {A B : AddCommGrpCat.{u}} (e : A ≅ B) : (↑A : Type u) ≃+ (↑B : Type u) := by
  let f : (↑A : Type u) →+ (↑B : Type u) := ConcreteCategory.hom e.hom
  exact AddEquiv.ofBijective f (ConcreteCategory.bijective_of_isIso e.hom)

private def homComplexPostcomp {C : Type v} [Category.{w, v} C] [Preadditive C]
    {K L M : CochainComplex C ℤ} (φ : L ⟶ M) : K.HomComplex L ⟶ K.HomComplex M :=
  HomologicalComplex.Hom.mk
    (fun n => AddCommGrpCat.ofHom
      { toFun := fun z => z.comp (Cochain.ofHom φ) (add_zero n)
        map_add' := by intro x y; simp
        map_zero' := by simp })
    (by
      intro i j hij
      ext z
      change δ i j ((show Cochain K L i from z).comp (Cochain.ofHom φ) (add_zero i)) =
        (δ i j (show Cochain K L i from z)).comp (Cochain.ofHom φ) (add_zero j)
      exact δ_comp_ofHom (show Cochain K L i from z) φ j)

private def cohomologyPostcomp {C : Type v} [Category.{w, v} C] [Preadditive C]
    {K L M : CochainComplex C ℤ} {n : ℤ} (φ : L ⟶ M) :
    HomComplex.CohomologyClass K L n →+ HomComplex.CohomologyClass K M n :=
  HomComplex.CohomologyClass.descAddMonoidHom
    { toFun := fun z => HomComplex.CohomologyClass.mk (z.postcomp φ)
      map_zero' := by rw [show (0 : Cocycle K L n).postcomp φ = 0 by ext; simp]; simp
      map_add' := by intro x y; congr 1; ext; simp }
    (by
      intro z hz
      change HomComplex.CohomologyClass.mk (z.postcomp φ) = 0
      rw [HomComplex.CohomologyClass.mk_eq_zero_iff]
      rcases hz with ⟨m, hm, β, hβ⟩
      refine ⟨m, hm, β.comp (Cochain.ofHom φ) (add_zero m), ?_⟩
      exact (δ_comp_ofHom β φ n).trans
        (congrArg (fun z => z.comp (Cochain.ofHom φ) (add_zero n)) hβ))

private lemma homologyAddEquiv_postcomp {C : Type v} [Category.{w, v} C] [Preadditive C]
    {K L M : CochainComplex C ℤ} {n : ℤ} (φ : L ⟶ M) (z : (K.HomComplex L).homology n) :
    cohomologyPostcomp φ ((HomComplex.homologyAddEquiv K L n) z) =
      (HomComplex.homologyAddEquiv K M n)
        (HomologicalComplex.homologyMap (homComplexPostcomp φ) n z) := by
  obtain ⟨z, rfl⟩ := (HomComplex.homologyAddEquiv K L n).symm.surjective z
  rw [AddEquiv.apply_symm_apply]
  obtain ⟨z, rfl⟩ := HomComplex.CohomologyClass.mk_surjective z
  let S₁ := (K.HomComplex L).sc n
  let S₂ := (K.HomComplex M).sc n
  let h₁ := HomComplex.leftHomologyData K L n
  let h₂ := HomComplex.leftHomologyData K M n
  let ψ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
    (homComplexPostcomp (K := K) (L := L) (M := M) φ)
  have hcycles :
      cyclesMap' ψ h₁ h₂ =
        AddCommGrpCat.ofHom
          { toFun := fun z : Cocycle K L n => z.postcomp φ
            map_zero' := by ext; simp
            map_add' := by intro x y; ext; simp } := by
    apply (cancel_mono h₂.i).1
    ext z
    change (cyclesMap' ψ h₁ h₂ ≫ h₂.i).hom z =
      (h₁.i ≫ ψ.τ₂).hom z
    rw [cyclesMap'_i]
  have hleft : leftHomologyMap' ψ h₁ h₂ =
      AddCommGrpCat.ofHom (cohomologyPostcomp φ) := by
    apply (cancel_epi h₁.π).1
    rw [leftHomologyπ_naturality']
    rw [hcycles]
    rfl
  have hnat := LeftHomologyData.leftHomologyIso_hom_naturality ψ h₁ h₂
  let z₁ : h₁.H := HomComplex.CohomologyClass.mk z
  change (cohomologyPostcomp φ) (HomComplex.CohomologyClass.mk z) =
    (h₂.homologyIso.hom).hom
      ((ConcreteCategory.hom (homologyMap ψ))
        ((h₁.homologyIso.inv).hom z₁))
  have hh := congrArg (fun q => q
      ((h₁.homologyIso.inv).hom z₁)) hnat
  change (h₁.homologyIso.hom ≫ leftHomologyMap' ψ h₁ h₂).hom _ = _ at hh
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at hh
  change (ConcreteCategory.hom (leftHomologyMap' ψ h₁ h₂))
      ((ConcreteCategory.hom h₁.homologyIso.hom)
        ((ConcreteCategory.hom h₁.homologyIso.inv) z₁)) = _ at hh
  rw [Iso.inv_hom_id_apply h₁.homologyIso z₁] at hh
  rw [hleft] at hh
  exact hh

private lemma extAddEquivCohomologyClass_naturality
    {C : Type v} [Category.{w, v} C] [Abelian C] [HasExt C]
    {Y Y' : C} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
    {X : C} (f : Y ⟶ Y') (ψ : I.Hom J f) (n : ℕ) (x : Ext X Y n) :
    cohomologyPostcomp ψ.hom' (I.extAddEquivCohomologyClass x) =
      J.extAddEquivCohomologyClass (x.comp (Ext.mk₀ f) (add_zero n)) := by
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (n + 1) rfl
  rw [InjectiveResolution.extMk_comp_mk₀ a (n + 1) rfl ha ψ]
  change cohomologyPostcomp ψ.hom'
      (I.extEquivCohomologyClass (I.extMk a (n + 1) rfl ha)) =
    J.extEquivCohomologyClass (J.extMk (a ≫ ψ.hom.f n) (n + 1) rfl _)
  rw [InjectiveResolution.extEquivCohomologyClass_extMk,
    InjectiveResolution.extEquivCohomologyClass_extMk]
  dsimp [cohomologyPostcomp, HomComplex.CohomologyClass.descAddMonoidHom]
  change HomComplex.CohomologyClass.mk
      ((Cocycle.fromSingleMk _ _ _ _ _).postcomp ψ.hom') = _
  congr 1
  apply HomComplex.Cocycle.ext
  change
    (Cochain.fromSingleMk
        (a ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv)
        (show (0 : ℤ) + (n : ℤ) = (n : ℤ) by simp)).comp
      (Cochain.ofHom ψ.hom') (add_zero (n : ℤ)) =
    Cochain.fromSingleMk
      ((a ≫ ψ.hom.f n) ≫ (J.cochainComplexXIso (n : ℤ) n rfl).inv)
      (show (0 : ℤ) + (n : ℤ) = (n : ℤ) by simp)
  rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp]
  congr 1
  rw [ψ.hom'_f (n : ℤ) n rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private noncomputable def integerSectionsChainIso
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) :
    ((CochainComplex.singleFunctor
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) 0).obj
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
          (AddCommGrpCat.of (ULift ℤ)))).HomComplex I.cochainComplex ≅
      (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (op (⊤ : Opens X))).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex := by
  let A := AddCommGrpCat.of (ULift ℤ)
  let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop
  let C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat
  let cA : C := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A
  let K := (CochainComplex.singleFunctor C 0).obj cA
  let L := I.cochainComplex
  let S := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (op (⊤ : Opens X))
  let P := S.mapHomologicalComplex (.up ℤ)
  let Q := P.obj L
  let eEquiv (n : ℤ) : Cochain K L n ≃+ S.obj (L.X n) := by
    let h : (0 : ℤ) + n = n := by simp
    let e₁ := CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := cA) (K := L) h
    let e₂ :=
      adj.homAddEquiv A (L.X n)
    let e₃ := AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X n))
    exact (e₁.trans e₂).trans e₃
  let eComponent (n : ℤ) : (K.HomComplex L).X n ≅ Q.X n := (eEquiv n).toAddCommGrpIso
  exact HomologicalComplex.Hom.isoOfComponents eComponent (by
    intro i j hij
    dsimp [K, Q, P, eComponent]
    ext x
    obtain ⟨f, rfl⟩ :=
      (CochainComplex.HomComplex.Cochain.fromSingleEquiv
        (X := cA) (K := L) (show (0 : ℤ) + i = i by simp)).symm.surjective x
    let eᵢ := eEquiv i
    let eⱼ := eEquiv j
    let x := (Cochain.fromSingleEquiv (X := cA) (K := L)
      (show (0 : ℤ) + i = i by simp)).symm f
    change S.map (L.d i j) (eᵢ x) = eⱼ ((K.HomComplex L).d i j x)
    apply eⱼ.symm.injective
    have hr : eⱼ.symm (eⱼ ((K.HomComplex L).d i j x)) = (K.HomComplex L).d i j x :=
      eⱼ.symm_apply_apply _
    rw [hr]
    apply (Cochain.fromSingleEquiv (X := cA) (K := L)
      (show (0 : ℤ) + j = j by simp)).injective
    change
      (Cochain.fromSingleEquiv (X := cA) (K := L)
        (show (0 : ℤ) + j = j by simp))
        ((eEquiv j).symm (S.map (L.d i j) (eEquiv i x))) =
      (Cochain.fromSingleEquiv (X := cA) (K := L)
        (show (0 : ℤ) + j = j by simp)) ((K.HomComplex L).d i j x)
    have hfrom (y : S.obj (L.X j)) :
        (Cochain.fromSingleEquiv (X := cA) (K := L)
          (show (0 : ℤ) + j = j by simp)) ((eEquiv j).symm y) =
          (adj.homEquiv A (L.X j)).symm
            ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j))).symm y) := by
      let h : (0 : ℤ) + j = j := by simp
      let a := CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := cA) (K := L) h
      let b : (cA ⟶ L.X j) ≃+ (A ⟶ S.obj (L.X j)) :=
        adj.homAddEquiv A (L.X j)
      let c := AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j))
      change a (((a.trans b).trans c).symm y) = b.symm (c.symm y)
      rw [show ((a.trans b).trans c).symm y = a.symm (b.symm (c.symm y)) by rfl]
      simp
    rw [hfrom]
    have hdelta :
        (Cochain.fromSingleEquiv (X := cA) (K := L)
          (show (0 : ℤ) + j = j by simp)) ((K.HomComplex L).d i j x) = f ≫ L.d i j := by
      change (Cochain.fromSingleEquiv (X := cA) (K := L)
        (show (0 : ℤ) + j = j by simp))
          (CochainComplex.HomComplex.δ i j
            (Cochain.fromSingleMk (p := 0) (q := i) (n := i) f
              (show (0 : ℤ) + i = i by simp))) = f ≫ L.d i j
      rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk f
        (show (0 : ℤ) + i = i by simp) j j (show (0 : ℤ) + j = j by simp)]
      exact (Cochain.fromSingleEquiv (X := cA) (K := L)
        (show (0 : ℤ) + j = j by simp)).apply_symm_apply (f ≫ L.d i j)
    rw [hdelta]
    have hi : eEquiv i x =
        (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X i)))
          (adj.homEquiv A (L.X i) f) := by
      let h : (0 : ℤ) + i = i := by simp
      let a := CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := cA) (K := L) h
      let b : (cA ⟶ L.X i) ≃+ (A ⟶ S.obj (L.X i)) :=
        adj.homAddEquiv A (L.X i)
      let c := AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X i))
      change ((a.trans b).trans c) (a.symm f) = c (b f)
      rw [AddEquiv.trans_apply, AddEquiv.trans_apply, a.apply_symm_apply]
    rw [hi]
    change (adj.homEquiv A (L.X j)).symm
      ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j))).symm
        (S.map (L.d i j)
          ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X i)))
            (adj.homEquiv A (L.X i) f)))) =
      f ≫ L.d i j
    have hc :
        (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j))).symm
          (S.map (L.d i j)
            ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X i)))
              (adj.homEquiv A (L.X i) f))) =
          (adj.homEquiv A (L.X i) f) ≫
            S.map (L.d i j) := by
      apply (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j))).injective
      simp only [AddEquiv.apply_symm_apply]
      change
        (S.map (L.d i j))
            ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X i)))
              (adj.homEquiv A (L.X i) f)) =
          (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j)))
            ((adj.homEquiv A (L.X i) f) ≫ S.map (L.d i j))
      exact ConcreteCategory.congr_hom
        ((AddCommGrpCat.coyonedaObjIsoForget.hom.naturality (S.map (L.d i j))).symm) _
    rw [hc]
    have hnat :=
      adj.homEquiv_naturality_right_symm (adj.homEquiv A (L.X i) f) (L.d i j)
    rw [(adj.homEquiv A (L.X i)).symm_apply_apply f] at hnat
    exact hnat)

private lemma integerSectionsChainIso_naturality
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    {f : F ⟶ G} (ψ : I.Hom J f) :
    homComplexPostcomp ψ.hom' ≫ (integerSectionsChainIso J).hom =
      (integerSectionsChainIso I).hom ≫
        (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
          (op (⊤ : Opens X))).mapHomologicalComplex (.up ℤ)).map ψ.hom' := by
  apply HomologicalComplex.Hom.ext
  funext n
  let A := AddCommGrpCat.of (ULift ℤ)
  let C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat
  let cA : C := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A
  let K := (CochainComplex.singleFunctor C 0).obj cA
  let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop
  let S := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (op (⊤ : Opens X))
  let eI (k : ℤ) : Cochain K I.cochainComplex k ≃+
      S.obj (I.cochainComplex.X k) := by
    let h : (0 : ℤ) + k = k := by simp
    exact ((Cochain.fromSingleEquiv (X := cA) (K := I.cochainComplex) h).trans
      (adj.homAddEquiv A (I.cochainComplex.X k))).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (I.cochainComplex.X k)))
  let eJ (k : ℤ) : Cochain K J.cochainComplex k ≃+
      S.obj (J.cochainComplex.X k) := by
    let h : (0 : ℤ) + k = k := by simp
    exact ((Cochain.fromSingleEquiv (X := cA) (K := J.cochainComplex) h).trans
      (adj.homAddEquiv A (J.cochainComplex.X k))).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (J.cochainComplex.X k)))
  change (homComplexPostcomp ψ.hom').f n ≫ (eJ n).toAddCommGrpIso.hom =
    (eI n).toAddCommGrpIso.hom ≫
      ((S.mapHomologicalComplex (.up ℤ)).map ψ.hom').f n
  ext z
  change eJ n ((homComplexPostcomp ψ.hom').f n z) =
    S.map (ψ.hom'.f n) (eI n z)
  obtain ⟨a, rfl⟩ :=
    (Cochain.fromSingleEquiv (X := cA) (K := I.cochainComplex)
      (show (0 : ℤ) + n = n by simp)).symm.surjective z
  change eJ n
      ((Cochain.fromSingleMk a (show (0 : ℤ) + n = n by simp)).comp
        (Cochain.ofHom ψ.hom') (add_zero n)) = _
  rw [← Cochain.fromSingleMk_postcomp]
  dsimp [eI, eJ]
  rw [Cochain.fromSingleEquiv_fromSingleMk, AddEquiv.apply_symm_apply]
  change
    (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (J.cochainComplex.X n)))
        (adj.homEquiv A (J.cochainComplex.X n) (a ≫ ψ.hom'.f n)) =
      S.map (ψ.hom'.f n)
        ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (I.cochainComplex.X n)))
          (adj.homEquiv A (I.cochainComplex.X n) a))
  rw [adj.homEquiv_naturality_right]
  exact ConcreteCategory.congr_hom
    (AddCommGrpCat.coyonedaObjIsoForget.hom.naturality (S.map (ψ.hom'.f n))) _

private lemma restrictionHomologyIso_naturality
    {C : Type v} [Category.{w, v} C] [Abelian C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {K L : HomologicalComplex C c'} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff]
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
    (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k') :
    HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap φ e) j ≫
        (L.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom =
      (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom ≫
        HomologicalComplex.homologyMap φ j' := by
  have hcycles :
      HomologicalComplex.cyclesMap (HomologicalComplex.restrictionMap φ e) j ≫
          (L.restrictionCyclesIso e j k hk hj' hk' hk'').hom =
        (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫
          HomologicalComplex.cyclesMap φ j' := by
    apply (cancel_mono (L.iCycles j')).mp
    simp only [Category.assoc, HomologicalComplex.restrictionCyclesIso_hom_iCycles,
      HomologicalComplex.cyclesMap_i]
    rw [← Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.restrictionMap_f' φ e hj']
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [HomologicalComplex.restrictionCyclesIso_hom_iCycles_assoc]
  apply (cancel_epi ((K.restriction e).homologyπ j)).mp
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    HomologicalComplex.homologyπ_restrictionHomologyIso_hom, ← Category.assoc, hcycles,
    Category.assoc, ← HomologicalComplex.homologyπ_naturality]
  simp only [HomologicalComplex.homologyπ_restrictionHomologyIso_hom_assoc]

noncomputable def natSectionsRestrictionIso
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) :
    (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).restriction
        ComplexShape.embeddingUpNat ≅
      ((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex := by
  let S := sections (⊤ : Opens X)
  let Q := (S.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let K := (S.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e := ComplexShape.embeddingUpNat
  let R := Q.restriction e
  let cApp (n : ℕ) : R.X n ≅ K.X n :=
    Q.restrictionXIso e rfl ≪≫ S.mapIso (I.cochainComplexXIso (e.f n) n (by rfl))
  let cIso : R ≅ K := HomologicalComplex.Hom.isoOfComponents cApp (by
    intro i j hij
    change
      (Q.restrictionXIso e (show e.f i = e.f i by rfl) ≪≫
          S.mapIso (I.cochainComplexXIso (e.f i) i (by rfl))).hom ≫ K.d i j =
        R.d i j ≫
          (Q.restrictionXIso e (show e.f j = e.f j by rfl) ≪≫
            S.mapIso (I.cochainComplexXIso (e.f j) j (by rfl))).hom
    rw [HomologicalComplex.restriction_d_eq Q e rfl rfl]
    change
      (Q.restrictionXIso e (show e.f i = e.f i by rfl)).hom ≫
          ((S.mapIso (I.cochainComplexXIso (e.f i) i (by rfl))).hom ≫ K.d i j) =
        (Q.restrictionXIso e (show e.f i = e.f i by rfl)).hom ≫
          (Q.d (e.f i) (e.f j) ≫
            (Q.restrictionXIso e (show e.f j = e.f j by rfl)).inv ≫
              (Q.restrictionXIso e (show e.f j = e.f j by rfl)).hom ≫
              (S.mapIso (I.cochainComplexXIso (e.f j) j (by rfl))).hom)
    refine (cancel_epi (Q.restrictionXIso e (show e.f i = e.f i by rfl)).hom).mp ?_
    change
      S.map (I.cochainComplexXIso (e.f i) i (by rfl)).hom ≫ S.map (I.cocomplex.d i j) =
        S.map (I.cochainComplex.d (e.f i) (e.f j)) ≫
          S.map (I.cochainComplexXIso (e.f j) j (by rfl)).hom
    rw [← S.map_comp, ← S.map_comp]
    rw [InjectiveResolution.cochainComplex_d I (e.f i) (e.f j) i j (by rfl) (by rfl)]
    simp)
  exact cIso

private lemma natSectionsRestrictionIso_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    {f : F ⟶ G} (ψ : I.Hom J f) :
    HomologicalComplex.restrictionMap
        (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℤ)).map ψ.hom')
        ComplexShape.embeddingUpNat ≫
      (natSectionsRestrictionIso J).hom =
    (natSectionsRestrictionIso I).hom ≫
      (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).map ψ.hom) := by
  apply HomologicalComplex.Hom.ext
  funext n
  let S := sections (⊤ : Opens X)
  change S.map (ψ.hom'.f (n : ℤ)) ≫
      S.map (J.cochainComplexXIso (n : ℤ) n rfl).hom =
    S.map (I.cochainComplexXIso (n : ℤ) n rfl).hom ≫ S.map (ψ.hom.f n)
  rw [ψ.hom'_f (n : ℤ) n rfl]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]

/-- Ext sheaf cohomology is computed by global sections of an injective resolution.

This is the chain-level comparison used to connect Mathlib's `Sheaf.H` API with
the right-derived global-sections API. -/
noncomputable def sheafHInjectiveResolutionAddEquiv
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (n : ℕ) :
    Sheaf.H F n ≃+
      ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (op (⊤ : Opens X))).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology
        (n : ℤ) := by
  let A := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))
  let C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat
  let K := (CochainComplex.singleFunctor C 0).obj A
  let H := K.HomComplex I.cochainComplex
  let e := integerSectionsChainIso I
  exact (I.extAddEquivCohomologyClass (X := A) (Y := F) (n := n)).trans
      (CochainComplex.HomComplex.homologyAddEquiv K I.cochainComplex (n : ℤ)).symm |>.trans
      (isoToAddEquiv (HomologicalComplex.homologyMapIso e (n : ℤ)))

private lemma sheafHInjectiveResolutionAddEquiv_naturality
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    {f : F ⟶ G} (ψ : I.Hom J f) (n : ℕ) (x : Sheaf.H F n) :
    sheafHInjectiveResolutionAddEquiv J n (Sheaf.H.map f n x) =
      (HomologicalComplex.homologyMap
        ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
          (op (⊤ : Opens X))).mapHomologicalComplex (.up ℤ)).map ψ.hom') (n : ℤ))
        (sheafHInjectiveResolutionAddEquiv I n x) := by
  let A := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))
  let C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat
  let K := (CochainComplex.singleFunctor C 0).obj A
  let eI := HomComplex.homologyAddEquiv K I.cochainComplex (n : ℤ)
  let eJ := HomComplex.homologyAddEquiv K J.cochainComplex (n : ℤ)
  let y := eI.symm (I.extAddEquivCohomologyClass x)
  have hc : eJ.symm (J.extAddEquivCohomologyClass (Sheaf.H.map f n x)) =
      HomologicalComplex.homologyMap (homComplexPostcomp ψ.hom') (n : ℤ) y := by
    apply eJ.injective
    rw [AddEquiv.apply_symm_apply]
    change _ = (HomComplex.homologyAddEquiv K J.cochainComplex (n : ℤ)) _
    rw [← homologyAddEquiv_postcomp]
    change _ = cohomologyPostcomp ψ.hom'
      (eI (eI.symm (I.extAddEquivCohomologyClass x)))
    rw [AddEquiv.apply_symm_apply]
    exact (extAddEquivCohomologyClass_naturality I J f ψ n x).symm
  have hn := congrArg (fun φ => HomologicalComplex.homologyMap φ (n : ℤ))
    (integerSectionsChainIso_naturality I J ψ)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hn
  change (HomologicalComplex.homologyMap (integerSectionsChainIso J).hom (n : ℤ))
      (eJ.symm (J.extAddEquivCohomologyClass (Sheaf.H.map f n x))) = _
  rw [hc]
  exact ConcreteCategory.congr_hom hn y

private def restrictionNatSuccHomologyIso
    {C : Type v} [Category.{w, v} C] [Abelian C]
    (K : CochainComplex C ℤ) (n : ℕ) :
    (K.restriction ComplexShape.embeddingUpNat).homology (n + 1) ≅
      K.homology (n + 1 : ℤ) :=
  K.restrictionHomologyIso ComplexShape.embeddingUpNat n (n + 1) (n + 2)
    (by simp [CochainComplex.prev_nat_succ]) (by simp [CochainComplex.next])
    rfl rfl rfl
    (by
      simp only [CochainComplex.prev]
      rw [ComplexShape.embeddingUpNat_f, ComplexShape.embeddingUpNat_f]
      norm_num)
    (by
      simp only [CochainComplex.next]
      rw [ComplexShape.embeddingUpNat_f, ComplexShape.embeddingUpNat_f]
      norm_num [Nat.cast_add]
      abel)

private lemma restrictionNatSuccHomologyIso_naturality
    {C : Type v} [Category.{w, v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        (HomologicalComplex.restrictionMap φ ComplexShape.embeddingUpNat) (n + 1) ≫
      (restrictionNatSuccHomologyIso L n).hom =
    (restrictionNatSuccHomologyIso K n).hom ≫
      HomologicalComplex.homologyMap φ (n + 1 : ℤ) := by
  apply restrictionHomologyIso_naturality

private def integerSectionsToDerivedIso
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) :
    (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology
        (n + 1 : ℤ) ≅ ((sections (⊤ : Opens X)).rightDerived (n + 1)).obj F :=
  (restrictionNatSuccHomologyIso _ n).symm ≪≫
    HomologicalComplex.homologyMapIso (natSectionsRestrictionIso I) (n + 1) ≪≫
      (I.isoRightDerivedObj (sections (⊤ : Opens X)) (n + 1)).symm

set_option backward.isDefEq.respectTransparency false in
private lemma integerSectionsToDerivedIso_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    {f : F ⟶ G} (ψ : I.Hom J f) (n : ℕ) :
    (integerSectionsToDerivedIso I n).hom ≫
      ((sections (⊤ : Opens X)).rightDerived (n + 1)).map f =
    HomologicalComplex.homologyMap
        (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℤ)).map ψ.hom')
        (n + 1 : ℤ) ≫ (integerSectionsToDerivedIso J n).hom := by
  let S := sections (⊤ : Opens X)
  let φ := (S.mapHomologicalComplex (.up ℤ)).map ψ.hom'
  let QI := (S.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let QJ := (S.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let eI := restrictionNatSuccHomologyIso QI n
  let eJ := restrictionNatSuccHomologyIso QJ n
  have hR := restrictionNatSuccHomologyIso_naturality φ n
  have hRi : eI.inv ≫ HomologicalComplex.homologyMap
        (HomologicalComplex.restrictionMap φ ComplexShape.embeddingUpNat) (n + 1) =
      HomologicalComplex.homologyMap φ (n + 1 : ℤ) ≫ eJ.inv := by
    apply (cancel_epi eI.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← hR]
    change HomologicalComplex.homologyMap
        (HomologicalComplex.restrictionMap φ ComplexShape.embeddingUpNat) (n + 1) =
      HomologicalComplex.homologyMap
        (HomologicalComplex.restrictionMap φ ComplexShape.embeddingUpNat) (n + 1) ≫ eJ.hom ≫ eJ.inv
    rw [Iso.hom_inv_id, Category.comp_id]
  have hN := congrArg (fun φ => HomologicalComplex.homologyMap φ (n + 1))
    (natSectionsRestrictionIso_naturality I J ψ)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hN
  have hD := InjectiveResolution.isoRightDerivedObj_inv_naturality f I J ψ.hom
    ψ.ι_f_zero_comp_hom_f_zero S (n + 1)
  change (I.isoRightDerivedObj S (n + 1)).inv ≫ (S.rightDerived (n + 1)).map f =
    HomologicalComplex.homologyMap ((S.mapHomologicalComplex (.up ℕ)).map ψ.hom) (n + 1) ≫
      (J.isoRightDerivedObj S (n + 1)).inv at hD
  have hN' := congrArg (fun z => eI.inv ≫ z ≫ (J.isoRightDerivedObj S (n + 1)).inv) hN
  have hRi' := congrArg (fun z => z ≫
    HomologicalComplex.homologyMap (natSectionsRestrictionIso J).hom (n + 1) ≫
      (J.isoRightDerivedObj S (n + 1)).inv) hRi
  change (eI.inv ≫ HomologicalComplex.homologyMap (natSectionsRestrictionIso I).hom (n + 1) ≫
      (I.isoRightDerivedObj S (n + 1)).inv) ≫ (S.rightDerived (n + 1)).map f =
    HomologicalComplex.homologyMap φ (n + 1 : ℤ) ≫
      (eJ.inv ≫ HomologicalComplex.homologyMap (natSectionsRestrictionIso J).hom (n + 1) ≫
        (J.isoRightDerivedObj S (n + 1)).inv)
  simp only [Category.assoc] at hN' hRi' ⊢
  rw [hD, ← hN', hRi']

/-- In positive degree, the Ext model of sheaf cohomology is the actual right-derived
global-sections object.  The integer-indexed injective-resolution complex is first
transported to the natural-indexed complex used by `rightDerived`. -/
noncomputable def sheafHRightDerivedSectionsAddEquiv
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (n : ℕ) :
    F.H (n + 1) ≃+
      (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj F : Type u) := by
  exact (sheafHInjectiveResolutionAddEquiv (InjectiveResolution.of F) (n + 1)).trans
    (isoToAddEquiv (integerSectionsToDerivedIso (InjectiveResolution.of F) n))

theorem sheafHRightDerivedSectionsAddEquiv_naturality
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (n : ℕ) (x : F.H (n + 1)) :
    sheafHRightDerivedSectionsAddEquiv (F := G) n (Sheaf.H.map f (n + 1) x) =
      ((sections (⊤ : Opens X)).rightDerived (n + 1)).map f
        (sheafHRightDerivedSectionsAddEquiv (F := F) n x) := by
  let I := InjectiveResolution.of F
  let J := InjectiveResolution.of G
  let ψ : I.Hom J f :=
    ⟨InjectiveResolution.desc f J I,
      congrArg (fun φ => φ.f 0) (InjectiveResolution.desc_commutes f J I)⟩
  have hH := sheafHInjectiveResolutionAddEquiv_naturality I J ψ (n + 1) x
  have hD := integerSectionsToDerivedIso_naturality I J ψ n
  change (integerSectionsToDerivedIso J n).hom
      (sheafHInjectiveResolutionAddEquiv J (n + 1)
        (Sheaf.H.map f (n + 1) x)) = _
  rw [hH]
  exact (ConcreteCategory.congr_hom hD
    (sheafHInjectiveResolutionAddEquiv I (n + 1) x)).symm

/-- In degree zero, `Sheaf.H.equiv₀` and the zero-th right-derived comparison
identify Ext sheaf cohomology with ordinary global sections. -/
noncomputable def sheafHRightDerivedSectionsAddEquiv_zero
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} :
    F.H 0 ≃+
      (((sections (⊤ : Opens X)).rightDerived 0).obj F : Type u) := by
  let _ : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat X) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat))
  let _ : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op (⊤ : Opens X))) := by
    infer_instance
  let _ : PreservesFiniteLimits (sections (⊤ : Opens X)) := by
    unfold sections
    infer_instance
  let e₀ := Sheaf.H.equiv₀ F isTerminalTop
  let e₁ := isoToAddEquiv
    ((Functor.rightDerivedZeroIsoSelf (sections (⊤ : Opens X))).app F).symm
  exact e₀.trans e₁

theorem sheafHRightDerivedSectionsAddEquiv_zero_naturality
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (x : F.H 0) :
    sheafHRightDerivedSectionsAddEquiv_zero (F := G) (Sheaf.H.map f 0 x) =
      ((sections (⊤ : Opens X)).rightDerived 0).map f
        (sheafHRightDerivedSectionsAddEquiv_zero (F := F) x) := by
  let S := sections (⊤ : Opens X)
  let _ : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat X) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat))
  let _ : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op (⊤ : Opens X))) := by
    infer_instance
  let _ : PreservesFiniteLimits (sections (⊤ : Opens X)) := by
    unfold sections
    infer_instance
  let τ := Functor.rightDerivedZeroIsoSelf S
  dsimp [sheafHRightDerivedSectionsAddEquiv_zero]
  change ConcreteCategory.hom (τ.inv.app G)
      (Sheaf.H.equiv₀ G isTerminalTop (Sheaf.H.map f 0 x)) =
    ConcreteCategory.hom ((S.rightDerived 0).map f)
      (ConcreteCategory.hom (τ.inv.app F)
        (Sheaf.H.equiv₀ F isTerminalTop x))
  rw [← Sheaf.H.equiv₀_naturality isTerminalTop f x]
  exact ConcreteCategory.congr_hom (τ.inv.naturality f)
    (Sheaf.H.equiv₀ F isTerminalTop x)

/-- Vanishing of actual derived global sections implies vanishing of `Sheaf.H` in
positive degree. -/
theorem isZero_sheafH_of_isZero_rightDerivedSections
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (n : ℕ)
    (h : IsZero (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj F)) :
    IsZero (AddCommGrpCat.of (F.H (n + 1))) := by
  let e := sheafHRightDerivedSectionsAddEquiv (F := F) n
  let ei : AddCommGrpCat.of (F.H (n + 1)) ≅
      AddCommGrpCat.of (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj F) :=
    e.toAddCommGrpIso
  exact IsZero.of_iso h ei

/-- Vanishing of positive Ext-based sheaf cohomology implies vanishing of the
corresponding derived global sections. -/
lemma isZero_rightDerivedSections_of_isZero_sheafH
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (n : ℕ)
    (h : IsZero (AddCommGrpCat.of (F.H (n + 1)))) :
    IsZero (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj F) := by
  exact IsZero.of_iso h (sheafHRightDerivedSectionsAddEquiv (F := F) n).toAddCommGrpIso.symm

end GromovWitten.AlgebraicGeometry.SheafCohomology
