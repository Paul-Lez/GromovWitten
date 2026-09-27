/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
open CochainComplex HomComplex Opposite TopologicalSpace
noncomputable section

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

universe u

variable {X : TopCat.{u}}

def isoToAddEquiv {A B : AddCommGrpCat.{u}} (e : A ≅ B) : (↑A : Type u) ≃+ (↑B : Type u) := by
  let f : (↑A : Type u) →+ (↑B : Type u) := ConcreteCategory.hom e.hom
  exact AddEquiv.ofBijective f (ConcreteCategory.bijective_of_isIso e.hom)

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
    let e₂ := (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homAddEquiv A (L.X n)
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
          ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv A (L.X j)).symm
            ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j))).symm y) := by
      let h : (0 : ℤ) + j = j := by simp
      let a := CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := cA) (K := L) h
      let b : (cA ⟶ L.X j) ≃+ (A ⟶ S.obj (L.X j)) :=
        (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homAddEquiv A (L.X j)
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
      exact (Cochain.fromSingleEquiv (X := cA) (K := L) (show (0 : ℤ) + j = j by simp)).apply_symm_apply (f ≫ L.d i j)
    rw [hdelta]
    have hi : eEquiv i x =
        (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X i)))
          ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv A (L.X i) f) := by
      let h : (0 : ℤ) + i = i := by simp
      let a := CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := cA) (K := L) h
      let b : (cA ⟶ L.X i) ≃+ (A ⟶ S.obj (L.X i)) :=
        (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homAddEquiv A (L.X i)
      let c := AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X i))
      change ((a.trans b).trans c) (a.symm f) = c (b f)
      rw [AddEquiv.trans_apply, AddEquiv.trans_apply, a.apply_symm_apply]
    rw [hi]
    change ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv A (L.X j)).symm
      ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j))).symm
        (S.map (L.d i j)
          ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X i)))
            ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv A (L.X i) f)))) =
      f ≫ L.d i j
    have hc :
        (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j))).symm
          (S.map (L.d i j)
            ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X i)))
              ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv A (L.X i) f))) =
          ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv A (L.X i) f) ≫
            S.map (L.d i j) := by
      apply (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j))).injective
      simp only [AddEquiv.apply_symm_apply]
      change
        (S.map (L.d i j))
            ((AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X i)))
              ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv A (L.X i) f)) =
          (AddCommGrpCat.uliftZMultiplesAddEquiv (S.obj (L.X j)))
            (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv A (L.X i) f) ≫ S.map (L.d i j))
      exact ConcreteCategory.congr_hom
        ((AddCommGrpCat.coyonedaObjIsoForget.hom.naturality (S.map (L.d i j))).symm) _
    rw [hc]
    have hnat :=
      (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv_naturality_right_symm
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv A (L.X i) f) (L.d i j)
    rw [((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv A
      (L.X i)).symm_apply_apply f] at hnat
    exact hnat)

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

/-- Ext sheaf cohomology is computed by global sections of an injective resolution.

This is the chain-level comparison used to connect Mathlib's `Sheaf.H` API with
the right-derived global-sections API. -/
noncomputable def sheafHInjectiveResolutionAddEquiv
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (n : ℕ) :
    Sheaf.H F n ≃+
      ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (op (⊤ : Opens X))).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology (n : ℤ) := by
  let A := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))
  let C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat
  let K := (CochainComplex.singleFunctor C 0).obj A
  let H := K.HomComplex I.cochainComplex
  let e := integerSectionsChainIso I
  exact (I.extAddEquivCohomologyClass (X := A) (Y := F) (n := n)).trans
      (CochainComplex.HomComplex.homologyAddEquiv K I.cochainComplex (n : ℤ)).symm |>.trans
      (isoToAddEquiv (HomologicalComplex.homologyMapIso e (n : ℤ)))

/-- In positive degree, the Ext model of sheaf cohomology is the actual right-derived
global-sections object.  The integer-indexed injective-resolution complex is first
transported to the natural-indexed complex used by `rightDerived`. -/
noncomputable def sheafHRightDerivedSectionsAddEquiv
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (n : ℕ) :
    F.H (n + 1) ≃+
      (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj F : Type u) := by
  let J : InjectiveResolution
      (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) F :=
    InjectiveResolution.of F
  have ht (k : ℕ) :
      @Injective (TopCat.Sheaf AddCommGrpCat X)
        (TopCat.instCategorySheaf AddCommGrpCat X) (J.cocomplex.X k) := by
    exact J.injective k
  let Jtop : InjectiveResolution (C := TopCat.Sheaf AddCommGrpCat X) F :=
    { cocomplex := J.cocomplex
      injective := ht
      ι := J.ι
      quasiIso := J.quasiIso }
  let Sg := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (op (⊤ : Opens X))
  let St := sections (⊤ : Opens X)
  let Qg := (Sg.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let Qt := (St.mapHomologicalComplex (.up ℤ)).obj Jtop.cochainComplex
  let eQ : Qg ≅ Qt := HomologicalComplex.Hom.isoOfComponents (fun k => Iso.refl _) (by
    intro i j hij
    rfl)
  let eR := natSectionsRestrictionIso Jtop
  have hi : (ComplexShape.up ℕ).prev (n + 1) = n := by
    simp [CochainComplex.prev_nat_succ]
  have hk : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by
    simp [CochainComplex.next]
  have hi' : ComplexShape.embeddingUpNat.f n = (n : ℤ) := by rfl
  have hj' : ComplexShape.embeddingUpNat.f (n + 1) = (n + 1 : ℤ) := by rfl
  have hk' : ComplexShape.embeddingUpNat.f (n + 2) = (n + 2 : ℤ) := by rfl
  have hi'' :
      (ComplexShape.up ℤ).prev (ComplexShape.embeddingUpNat.f (n + 1)) =
        ComplexShape.embeddingUpNat.f n := by
    simp only [CochainComplex.prev]
    rw [ComplexShape.embeddingUpNat_f, ComplexShape.embeddingUpNat_f]
    norm_num
  have hk'' :
      (ComplexShape.up ℤ).next (ComplexShape.embeddingUpNat.f (n + 1)) =
        ComplexShape.embeddingUpNat.f (n + 2) := by
    simp only [CochainComplex.next]
    rw [ComplexShape.embeddingUpNat_f, ComplexShape.embeddingUpNat_f]
    norm_num [Nat.cast_add]
    abel
  let eRH := HomologicalComplex.restrictionHomologyIso Qt ComplexShape.embeddingUpNat
    n (n + 1) (n + 2) hi hk hi' hj' hk' hi'' hk''
  have hK (k : ℕ) : TopCat.Sheaf.IsFlasque (Jtop.cocomplex.X k) := by
    let _ := TopCat.Sheaf.isFlasque_of_injective X (Jtop.cocomplex.X k)
    infer_instance
  letI := Jtop.quasiIso
  let hD := flasqueResolutionSectionsTopIso X Jtop.ι hK (n + 1)
  let h1 := sheafHInjectiveResolutionAddEquiv J (n + 1)
  let h2 := isoToAddEquiv (HomologicalComplex.homologyMapIso eQ (n + 1 : ℤ))
  let h3 := isoToAddEquiv eRH
  let h4 := isoToAddEquiv (HomologicalComplex.homologyMapIso eR (n + 1))
  let h5 := isoToAddEquiv hD.symm
  exact h1.trans h2 |>.trans h3.symm |>.trans h4 |>.trans h5

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

end GromovWitten.AlgebraicGeometry.SheafCohomology
