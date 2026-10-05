/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.MappingCoconeFunctor
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Topology.Category.TopCat.Opens


/-!
# Complexes from finite open covers

A finite list of opens defines an augmented complex of module presheaves by iterated
Mayer–Vietoris mapping cocones. The construction is functorial in the input complex and can
be evaluated at any open. For input concentrated in degree zero, a list of length `n` gives
a complex supported in degrees `0, …, n - 1`.

The list need not cover the space. The comparison with derived sections for an affine cover
is proved separately; this file constructs the complex, its maps, and its degree bounds.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite CochainComplex.HomComplex

universe u v

namespace GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

open CochainComplex

variable {X : TopCat.{u}} {R : Type v} [Ring R]

abbrev Presheaves (X : TopCat.{u}) (R : Type v) [Ring R] :=
  (Opens X)ᵒᵖ ⥤ ModuleCat R

abbrev PresheafComplex (X : TopCat.{u}) (R : Type v) [Ring R] :=
  CochainComplex (Presheaves X R) ℤ

noncomputable def opensInfFunctor (U : Opens X) : Opens X ⥤ Opens X where
  obj V := V ⊓ U
  map f := homOfLE (inf_le_inf_right U f.le)
  map_id _ := by apply Subsingleton.elim
  map_comp _ _ := by apply Subsingleton.elim

noncomputable def opensInfOp (U : Opens X) : (Opens X)ᵒᵖ ⥤ (Opens X)ᵒᵖ :=
  (opensInfFunctor U).op

noncomputable def opensInfNatTrans (U : Opens X) : 𝟭 (Opens X)ᵒᵖ ⟶ opensInfOp U where
  app V := (Opens.infLELeft V.unop U).op
  naturality _ _ _ := by apply Subsingleton.elim

noncomputable def restrictionFunctor (U : Opens X) : Presheaves X R ⥤ Presheaves X R :=
  (Functor.whiskeringLeft _ _ _).obj (opensInfOp U)

noncomputable def restrictionNatTrans (U : Opens X) :
    𝟭 (Presheaves X R) ⟶ restrictionFunctor U where
  app P := (Functor.leftUnitor P).inv ≫
    Functor.whiskerRight (opensInfNatTrans U) P
  naturality P Q f := by
    ext V x
    exact congrArg (fun g => g x)
      (f.naturality ((Opens.infLELeft V.unop U).op)).symm

noncomputable instance restrictionFunctor_additive (U : Opens X) :
    (restrictionFunctor (X := X) (R := R) U).Additive where
  map_add := by
    intro P Q f g
    ext V
    rfl

noncomputable def restrictionComplexFunctor (U : Opens X) :
    PresheafComplex X R ⥤ PresheafComplex X R :=
  (restrictionFunctor U).mapHomologicalComplex (ComplexShape.up ℤ)

noncomputable def restrictionComplexNatTrans (U : Opens X) :
    𝟭 (PresheafComplex X R) ⟶ restrictionComplexFunctor U :=
  (Functor.mapHomologicalComplexIdIso (Presheaves X R) (ComplexShape.up ℤ)).inv ≫
    NatTrans.mapHomologicalComplex (restrictionNatTrans U) (ComplexShape.up ℤ)

private lemma mappingCoconeMap_congr {K₁ L₁ K₂ L₂ : PresheafComplex X R}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂}
    (h : φ₁ ≫ b = a ≫ φ₂) (h' : φ₁ ≫ b' = a' ≫ φ₂)
    (ha : a = a') (hb : b = b') :
    mappingCoconeMap φ₁ φ₂ a b h = mappingCoconeMap φ₁ φ₂ a' b' h' := by
  subst a'
  subst b'
  rfl

private lemma mappingCoconeMap_id' {K L : PresheafComplex X R} (φ : K ⟶ L)
    (comm : φ ≫ 𝟙 L = 𝟙 K ≫ φ) :
    mappingCoconeMap φ φ (𝟙 K) (𝟙 L) comm = 𝟙 _ := by
  rw [mappingCoconeMap_congr φ φ comm (by simp) rfl rfl]
  exact mappingCoconeMap_id φ

private lemma biprod_map_comp {A₁ A₂ B₁ B₂ C₁ C₂ : PresheafComplex X R}
    (f₁ : A₁ ⟶ B₁) (f₂ : B₁ ⟶ C₁) (g₁ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) :
    biprod.map (f₁ ≫ f₂) (g₁ ≫ g₂) =
      biprod.map f₁ g₁ ≫ biprod.map f₂ g₂ := by
  apply biprod.hom_ext
  · simp [Category.assoc]
  · simp [Category.assoc]

structure AugmentedCechComplex (F : PresheafComplex X R) where
  complex : PresheafComplex X R
  augmentation : F ⟶ complex

/-- Evaluate a complex of module presheaves at each open, retaining the restriction maps. -/
noncomputable def evaluatePresheafComplex (K : PresheafComplex X R) :
    (Opens X)ᵒᵖ ⥤ CochainComplex (ModuleCat R) ℤ where
  obj V :=
    ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj V).mapHomologicalComplex
      (ComplexShape.up ℤ) |>.obj K
  map f :=
    (NatTrans.mapHomologicalComplex
      ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).map f) (ComplexShape.up ℤ)).app K
  map_id V := by
    simp
  map_comp f g := by
    simp

/-- Evaluate a morphism of complexes of presheaves naturally at every open. -/
noncomputable def evaluatePresheafComplexMap {K L : PresheafComplex X R} (φ : K ⟶ L) :
    evaluatePresheafComplex K ⟶ evaluatePresheafComplex L where
  app V :=
    ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj V).mapHomologicalComplex
      (ComplexShape.up ℤ) |>.map φ
  naturality _ _ f :=
    (NatTrans.mapHomologicalComplex_naturality
      ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).map f) φ).symm

noncomputable def finiteCechConsData (F : PresheafComplex X R) (U : Opens X)
    (tailData : AugmentedCechComplex F) : AugmentedCechComplex F := by
  let restrict := restrictionComplexFunctor (X := X) (R := R) U
  let resF := (restrictionComplexNatTrans (X := X) (R := R) U).app F
  let resB := (restrictionComplexNatTrans (X := X) (R := R) U).app tailData.complex
  let A := restrict.obj F ⊞ tailData.complex
  let φ : A ⟶ restrict.obj tailData.complex := biprod.desc
    (restrict.map tailData.augmentation) (-resB)
  let α : F ⟶ A := biprod.lift resF tailData.augmentation
  have hres : tailData.augmentation ≫ resB = resF ≫ restrict.map tailData.augmentation := by
    simpa only [Functor.id_map] using
      (restrictionComplexNatTrans (X := X) (R := R) U).naturality tailData.augmentation
  have hzero : α ≫ φ = 0 := by
    simp only [α, φ, biprod.lift_desc]
    simp [hres]
  have hαφ : CochainComplex.HomComplex.δ (-1) 0 0 +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ φ) = 0 := by
    simp [hzero]
  exact ⟨CochainComplex.mappingCocone φ, CochainComplex.mappingCocone.lift φ α 0 hαφ⟩

noncomputable def finiteCechData (F : PresheafComplex X R) :
    List (Opens X) → AugmentedCechComplex F
  | [] => ⟨HomologicalComplex.zero, 0⟩
  | U :: tail => finiteCechConsData F U (finiteCechData F tail)

/-- Recursive maps are constructed together with the augmentation identity used at the next step. -/
structure FiniteCechMapData {F G : PresheafComplex X R} (f : F ⟶ G)
    (U : List (Opens X)) where
  hom : (finiteCechData F U).complex ⟶ (finiteCechData G U).complex
  augmentation_natural :
    (finiteCechData F U).augmentation ≫ hom = f ≫ (finiteCechData G U).augmentation

noncomputable def finiteCechMapData {F G : PresheafComplex X R} (f : F ⟶ G) :
    (U : List (Opens X)) → FiniteCechMapData f U
  | [] => ⟨0, by cat_disch⟩
  | U :: tail => by
      let tailF := finiteCechData F tail
      let tailG := finiteCechData G tail
      let tailMap := finiteCechMapData f tail
      let stepF := finiteCechConsData F U tailF
      let stepG := finiteCechConsData G U tailG
      let restrict := restrictionComplexFunctor (X := X) (R := R) U
      let resF := (restrictionComplexNatTrans (X := X) (R := R) U).app F
      let resG := (restrictionComplexNatTrans (X := X) (R := R) U).app G
      let resTailF := (restrictionComplexNatTrans (X := X) (R := R) U).app tailF.complex
      let resTailG := (restrictionComplexNatTrans (X := X) (R := R) U).app tailG.complex
      let AF := restrict.obj F ⊞ tailF.complex
      let AG := restrict.obj G ⊞ tailG.complex
      let φF : AF ⟶ restrict.obj tailF.complex :=
        biprod.desc (restrict.map tailF.augmentation) (-resTailF)
      let φG : AG ⟶ restrict.obj tailG.complex :=
        biprod.desc (restrict.map tailG.augmentation) (-resTailG)
      let αF : F ⟶ AF := biprod.lift resF tailF.augmentation
      let αG : G ⟶ AG := biprod.lift resG tailG.augmentation
      let aMap : AF ⟶ AG := biprod.map (restrict.map f) tailMap.hom
      let bMap : restrict.obj tailF.complex ⟶ restrict.obj tailG.complex :=
        restrict.map tailMap.hom
      have hresAlpha : f ≫ resG = resF ≫ restrict.map f := by
        simpa only [Functor.id_map] using
          (restrictionComplexNatTrans (X := X) (R := R) U).naturality f
      have hresF : tailF.augmentation ≫ resTailF =
          resF ≫ restrict.map tailF.augmentation := by
        simpa only [Functor.id_map] using
          (restrictionComplexNatTrans (X := X) (R := R) U).naturality tailF.augmentation
      have hresG : tailG.augmentation ≫ resTailG =
          resG ≫ restrict.map tailG.augmentation := by
        simpa only [Functor.id_map] using
          (restrictionComplexNatTrans (X := X) (R := R) U).naturality tailG.augmentation
      have hresTail : tailMap.hom ≫ resTailG = resTailF ≫ restrict.map tailMap.hom := by
        simpa only [Functor.id_map] using
          (restrictionComplexNatTrans (X := X) (R := R) U).naturality tailMap.hom
      have hsq : φF ≫ bMap = aMap ≫ φG := by
        apply biprod.hom_ext'
        · calc
            biprod.inl ≫ φF ≫ bMap =
                restrict.map tailF.augmentation ≫ restrict.map tailMap.hom := by
              simp [φF, bMap]
            _ = restrict.map (tailF.augmentation ≫ tailMap.hom) :=
              (Functor.map_comp restrict _ _).symm
            _ = restrict.map (f ≫ tailG.augmentation) := by rw [tailMap.augmentation_natural]
            _ = restrict.map f ≫ restrict.map tailG.augmentation := Functor.map_comp _ _ _
            _ = biprod.inl ≫ aMap ≫ φG := by simp [aMap, φG]
        · calc
            biprod.inr ≫ φF ≫ bMap = -resTailF ≫ restrict.map tailMap.hom := by
              simp [φF, bMap]
            _ = -(resTailF ≫ restrict.map tailMap.hom) := by simp
            _ = -(tailMap.hom ≫ resTailG) := by rw [← hresTail]
            _ = tailMap.hom ≫ (-resTailG) := by simp
            _ = biprod.inr ≫ aMap ≫ φG := by simp [aMap, φG]
      have hAlpha : αF ≫ aMap = f ≫ αG := by
        apply biprod.hom_ext
        · simpa [αF, aMap, αG, Category.assoc, biprod.lift_fst, biprod.map_fst] using
            hresAlpha.symm
        · simpa [αF, aMap, αG, Category.assoc, biprod.lift_snd, biprod.map_snd] using
            tailMap.augmentation_natural
      have hzeroF : αF ≫ φF = 0 := by
        simp only [αF, φF, biprod.lift_desc]
        simp [hresF]
      have hzeroG : αG ≫ φG = 0 := by
        simp only [αG, φG, biprod.lift_desc]
        simp [hresG]
      have hLiftF : CochainComplex.HomComplex.δ (-1) 0 0 +
          CochainComplex.HomComplex.Cochain.ofHom (αF ≫ φF) = 0 := by simp [hzeroF]
      have hLiftG : CochainComplex.HomComplex.δ (-1) 0 0 +
          CochainComplex.HomComplex.Cochain.ofHom (αG ≫ φG) = 0 := by simp [hzeroG]
      have hAugMap :
          (finiteCechConsData F U tailF).augmentation ≫
              mappingCoconeMap φF φG aMap bMap hsq =
            f ≫ (finiteCechConsData G U tailG).augmentation := by
        apply HomologicalComplex.hom_ext
        intro i
        rw [HomologicalComplex.comp_f]
        change ((CochainComplex.mappingCocone.lift φF αF 0 hLiftF).f i ≫
            (mappingCoconeMap φF φG aMap bMap hsq).f i) =
          (f ≫ (CochainComplex.mappingCocone.lift φG αG 0 hLiftG)).f i
        rw [HomologicalComplex.comp_f,
          mappingCocone_lift_zero_factors_inl φF αF hLiftF i, Category.assoc,
          mappingCocone_inl_map φF φG aMap bMap hsq i, ← Category.assoc,
          ← HomologicalComplex.comp_f, hAlpha,
          HomologicalComplex.comp_f,
          mappingCocone_lift_zero_factors_inl φG αG hLiftG i,
          Category.assoc]
      refine ⟨mappingCoconeMap φF φG aMap bMap hsq, ?_⟩
      simpa [finiteCechData, finiteCechConsData, tailF, tailG] using hAugMap

noncomputable def finiteCechMap {F G : PresheafComplex X R} (f : F ⟶ G)
    (U : List (Opens X)) :
    (finiteCechData F U).complex ⟶ (finiteCechData G U).complex :=
  (finiteCechMapData f U).hom

lemma finiteCechMap_augmentation_natural {F G : PresheafComplex X R}
    (f : F ⟶ G) (U : List (Opens X)) :
    (finiteCechData F U).augmentation ≫ finiteCechMap f U =
      f ≫ (finiteCechData G U).augmentation :=
  (finiteCechMapData f U).augmentation_natural

lemma finiteCechConsSquare (U : Opens X) {F G : PresheafComplex X R}
    (f : F ⟶ G) (tailF : AugmentedCechComplex F) (tailG : AugmentedCechComplex G)
    (t : tailF.complex ⟶ tailG.complex)
    (ht : tailF.augmentation ≫ t = f ≫ tailG.augmentation) :
    let restrict := restrictionComplexFunctor (X := X) (R := R) U
    let AF := restrict.obj F ⊞ tailF.complex
    let AG := restrict.obj G ⊞ tailG.complex
    let φF : AF ⟶ restrict.obj tailF.complex := biprod.desc
      (restrict.map tailF.augmentation)
      (-((restrictionComplexNatTrans (X := X) (R := R) U).app tailF.complex))
    let φG : AG ⟶ restrict.obj tailG.complex := biprod.desc
      (restrict.map tailG.augmentation)
      (-((restrictionComplexNatTrans (X := X) (R := R) U).app tailG.complex))
    let a : AF ⟶ AG := biprod.map (restrict.map f) t
    let b : restrict.obj tailF.complex ⟶ restrict.obj tailG.complex := restrict.map t
    φF ≫ b = a ≫ φG := by
  dsimp only
  let restrict := restrictionComplexFunctor (X := X) (R := R) U
  let resTailF := (restrictionComplexNatTrans (X := X) (R := R) U).app tailF.complex
  let resTailG := (restrictionComplexNatTrans (X := X) (R := R) U).app tailG.complex
  let AF := restrict.obj F ⊞ tailF.complex
  let AG := restrict.obj G ⊞ tailG.complex
  let φF : AF ⟶ restrict.obj tailF.complex :=
    biprod.desc (restrict.map tailF.augmentation) (-resTailF)
  let φG : AG ⟶ restrict.obj tailG.complex :=
    biprod.desc (restrict.map tailG.augmentation) (-resTailG)
  let a : AF ⟶ AG := biprod.map (restrict.map f) t
  let b : restrict.obj tailF.complex ⟶ restrict.obj tailG.complex := restrict.map t
  have hresTail : t ≫ resTailG = resTailF ≫ restrict.map t := by
    simpa only [Functor.id_map] using
      (restrictionComplexNatTrans (X := X) (R := R) U).naturality t
  apply biprod.hom_ext'
  · calc
      biprod.inl ≫ φF ≫ b = restrict.map tailF.augmentation ≫ restrict.map t := by
        simp [φF, b]
      _ = restrict.map (tailF.augmentation ≫ t) :=
        (Functor.map_comp restrict _ _).symm
      _ = restrict.map (f ≫ tailG.augmentation) := congrArg (restrict.map) ht
      _ = restrict.map f ≫ restrict.map tailG.augmentation := Functor.map_comp _ _ _
      _ = biprod.inl ≫ a ≫ φG := by simp [a, φG]
  · calc
      biprod.inr ≫ φF ≫ b = -resTailF ≫ restrict.map t := by simp [φF, b]
      _ = -(resTailF ≫ restrict.map t) := by simp
      _ = -(t ≫ resTailG) := by rw [← hresTail]
      _ = t ≫ (-resTailG) := by simp
      _ = biprod.inr ≫ a ≫ φG := by simp [a, φG]

lemma finiteCechMap_id (F : PresheafComplex X R) (U : List (Opens X)) :
    finiteCechMap (𝟙 F) U = 𝟙 ((finiteCechData F U).complex) := by
  induction U with
  | nil =>
      exact (HomologicalComplex.isZero_zero).eq_of_src _ _
  | cons U tail ih =>
      let tailF := finiteCechData F tail
      let tailMap := finiteCechMapData (𝟙 F) tail
      let restrict := restrictionComplexFunctor (X := X) (R := R) U
      let AF := restrict.obj F ⊞ tailF.complex
      let φ : AF ⟶ restrict.obj tailF.complex := biprod.desc
        (restrict.map tailF.augmentation)
        (-((restrictionComplexNatTrans (X := X) (R := R) U).app tailF.complex))
      let aMap : AF ⟶ AF := biprod.map (restrict.map (𝟙 F)) tailMap.hom
      let bMap : restrict.obj tailF.complex ⟶ restrict.obj tailF.complex :=
        restrict.map tailMap.hom
      have ih' : (finiteCechMapData (𝟙 F) tail).hom =
          𝟙 tailF.complex := by
        simpa only [finiteCechMap] using ih
      have ha : aMap = 𝟙 AF := by
        dsimp [aMap]
        rw [ih']
        apply biprod.hom_ext
        · rw [biprod.map_fst]
          exact (Category.id_comp _).symm
        · rw [biprod.map_snd]
          exact (Category.id_comp _).symm
      have hb : bMap = 𝟙 (restrict.obj tailF.complex) := by
        dsimp [bMap]
        rw [ih']
        simp
      have hsq : φ ≫ bMap = aMap ≫ φ := by rw [ha, hb]; simp
      change mappingCoconeMap φ φ aMap bMap hsq = 𝟙 (CochainComplex.mappingCocone φ)
      rw [mappingCoconeMap_congr φ φ hsq (by simp) ha hb]
      exact mappingCoconeMap_id φ

lemma finiteCechMap_comp {F G H : PresheafComplex X R}
    (f : F ⟶ G) (g : G ⟶ H) (U : List (Opens X)) :
    finiteCechMap (f ≫ g) U = finiteCechMap f U ≫ finiteCechMap g U := by
  induction U with
  | nil => cat_disch
  | cons U tail ih =>
      have ih' : (finiteCechMapData (f ≫ g) tail).hom =
          (finiteCechMapData f tail).hom ≫ (finiteCechMapData g tail).hom := by
        simpa only [finiteCechMap] using ih
      let tailF := finiteCechData F tail
      let tailG := finiteCechData G tail
      let tailH := finiteCechData H tail
      let tailFG := finiteCechMapData (f ≫ g) tail
      let tailFF := finiteCechMapData f tail
      let tailGG := finiteCechMapData g tail
      let restrict := restrictionComplexFunctor (X := X) (R := R) U
      let AF := restrict.obj F ⊞ tailF.complex
      let AG := restrict.obj G ⊞ tailG.complex
      let AH := restrict.obj H ⊞ tailH.complex
      let φF : AF ⟶ restrict.obj tailF.complex := biprod.desc
        (restrict.map tailF.augmentation)
        (-((restrictionComplexNatTrans (X := X) (R := R) U).app tailF.complex))
      let φG : AG ⟶ restrict.obj tailG.complex := biprod.desc
        (restrict.map tailG.augmentation)
        (-((restrictionComplexNatTrans (X := X) (R := R) U).app tailG.complex))
      let φH : AH ⟶ restrict.obj tailH.complex := biprod.desc
        (restrict.map tailH.augmentation)
        (-((restrictionComplexNatTrans (X := X) (R := R) U).app tailH.complex))
      let aFG : AF ⟶ AH := biprod.map (restrict.map (f ≫ g)) tailFG.hom
      let bFG : restrict.obj tailF.complex ⟶ restrict.obj tailH.complex :=
        restrict.map tailFG.hom
      let aF : AF ⟶ AG := biprod.map (restrict.map f) tailFF.hom
      let bF : restrict.obj tailF.complex ⟶ restrict.obj tailG.complex :=
        restrict.map tailFF.hom
      let aG : AG ⟶ AH := biprod.map (restrict.map g) tailGG.hom
      let bG : restrict.obj tailG.complex ⟶ restrict.obj tailH.complex :=
        restrict.map tailGG.hom
      have hFG : φF ≫ bFG = aFG ≫ φH := by
        exact finiteCechConsSquare U (f ≫ g) tailF tailH tailFG.hom
          tailFG.augmentation_natural
      have hF : φF ≫ bF = aF ≫ φG := by
        exact finiteCechConsSquare U f tailF tailG tailFF.hom
          tailFF.augmentation_natural
      have hG : φG ≫ bG = aG ≫ φH := by
        exact finiteCechConsSquare U g tailG tailH tailGG.hom
          tailGG.augmentation_natural
      have ha : aFG = aF ≫ aG := by
        dsimp [aFG, aF, aG]
        rw [Functor.map_comp, ih']
        exact biprod_map_comp (restrict.map f) (restrict.map g)
          tailFF.hom tailGG.hom
      have hb : bFG = bF ≫ bG := by
        dsimp [bFG, bF, bG]
        rw [ih', Functor.map_comp]
      change mappingCoconeMap φF φH aFG bFG hFG =
        mappingCoconeMap φF φG aF bF hF ≫ mappingCoconeMap φG φH aG bG hG
      rw [mappingCoconeMap_congr φF φH hFG (by
        calc
          φF ≫ (bF ≫ bG) = (φF ≫ bF) ≫ bG := by simp [Category.assoc]
          _ = (aF ≫ φG) ≫ bG := congrArg (fun k => k ≫ bG) hF
          _ = aF ≫ (φG ≫ bG) := by simp [Category.assoc]
          _ = aF ≫ (aG ≫ φH) := congrArg (fun k => aF ≫ k) hG
          _ = (aF ≫ aG) ≫ φH := by simp [Category.assoc]) ha hb]
      exact mappingCoconeMap_comp φF φG φH aF bF hF aG bG hG

noncomputable def finiteCechFunctor (U : List (Opens X)) :
    PresheafComplex X R ⥤ PresheafComplex X R where
  obj F := (finiteCechData F U).complex
  map f := finiteCechMap f U
  map_id F := finiteCechMap_id F U
  map_comp f g := finiteCechMap_comp f g U

/-- The recursively defined complex has no terms below zero or above the cover length,
provided the input is concentrated in degree zero. -/
lemma finiteCechData_bounded_support (F : PresheafComplex X R)
    (hF : ∀ i : ℤ, i ≠ 0 → IsZero (F.X i)) (U : List (Opens X)) :
    ∀ i : ℤ, i < 0 ∨ (U.length : ℤ) ≤ i →
      IsZero ((finiteCechData F U).complex.X i) := by
  induction U with
  | nil =>
      intro i hi
      simpa [finiteCechData, HomologicalComplex.zero] using
        (isZero_zero (Presheaves X R))
  | cons U tail ih =>
      let tailData := finiteCechData F tail
      let restrict := restrictionComplexFunctor (X := X) (R := R) U
      let A := restrict.obj F ⊞ tailData.complex
      let φ : A ⟶ restrict.obj tailData.complex := biprod.desc
        (restrict.map tailData.augmentation)
        (-((restrictionComplexNatTrans (X := X) (R := R) U).app tailData.complex))
      intro i hi
      change IsZero ((CochainComplex.mappingCocone φ).X i)
      have hTailI : i < 0 ∨ (tail.length : ℤ) ≤ i := by
        rcases hi with hiNeg | hiLarge
        · exact Or.inl hiNeg
        · right
          have hLen : (tail.length : ℤ) + 1 ≤ i := by
            simpa using hiLarge
          omega
      have hTailPrev : i - 1 < 0 ∨ (tail.length : ℤ) ≤ i - 1 := by
        rcases hi with hiNeg | hiLarge
        · exact Or.inl (by omega)
        · right
          have hLen : (tail.length : ℤ) + 1 ≤ i := by
            simpa using hiLarge
          omega
      have hiNe : i ≠ 0 := by
        rcases hi with hiNeg | hiLarge
        · omega
        · have hLen : (tail.length : ℤ) + 1 ≤ i := by
            simpa using hiLarge
          omega
      have hB_i : IsZero (tailData.complex.X i) := ih i hTailI
      have hB_prev : IsZero (tailData.complex.X (i - 1)) := ih (i - 1) hTailPrev
      have hFres : IsZero ((restrict.obj F).X i) := by
        change IsZero ((restrictionFunctor (X := X) (R := R) U).obj (F.X i))
        exact Functor.map_isZero _ (hF i hiNe)
      have hA : IsZero (A.X i) := by
        refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso
          (restrict.obj F) tailData.complex i)
        rw [biprod_isZero_iff]
        exact ⟨hFres, hB_i⟩
      have hD : IsZero ((restrict.obj tailData.complex).X (i - 1)) := by
        change IsZero ((restrictionFunctor (X := X) (R := R) U).obj
          (tailData.complex.X (i - 1)))
        exact Functor.map_isZero _ hB_prev
      have hCone : IsZero ((CochainComplex.mappingCone φ).X (i - 1)) := by
        rw [CochainComplex.mappingCone.isZero_X_iff]
        simpa using And.intro hA hD
      dsimp only [CochainComplex.mappingCocone]
      exact IsZero.of_iso hCone
        (CochainComplex.shiftFunctorObjXIso (CochainComplex.mappingCone φ)
          (-1) i (i - 1) (by omega))

/-- The finite-cover Čech complex, viewed as a functor of the varying open. -/
noncomputable def finiteCechComplex (F : PresheafComplex X R) (U : List (Opens X)) :
    (Opens X)ᵒᵖ ⥤ CochainComplex (ModuleCat R) ℤ :=
  evaluatePresheafComplex (finiteCechData F U).complex

/-- The augmentation to the finite-cover Čech complex, evaluated naturally on every open. -/
noncomputable def finiteCechAugmentation (F : PresheafComplex X R)
    (U : List (Opens X)) :
    evaluatePresheafComplex F ⟶ finiteCechComplex F U :=
  evaluatePresheafComplexMap (finiteCechData F U).augmentation

end GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
