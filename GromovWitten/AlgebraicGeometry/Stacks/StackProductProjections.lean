/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.StackProducts

/-! # Projection formulas for products of stacks

These formulas retain the pseudofunctorial pullback comparisons while reducing their two
components to the corresponding comparisons in the factors.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false

variable {X Y : FppfStack.{u}} {R S T : Scheme.{u}}

/-- The comparison in a product over the terminal stack is uniquely determined, so every
product object is equal to the pair of its components.  This does not identify any arrows
in either factor. -/
theorem stackProdObj_components (p : StackFiber (stackProduct X Y).pullback T) :
    stackProdObj (CategoricalPullback.fst p) (CategoricalPullback.snd p) = p := by
  rcases p with ⟨x, y, e⟩
  have he : e = Iso.refl _ := by
    apply Iso.ext
    exact (terminalStack_hom_subsingleton _ _).elim _ _
  cases he
  rfl

@[simp]
theorem stackProduct_pullback_map_fst (f : S ⟶ T)
    {p q : StackFiber (stackProduct X Y).pullback T} (a : p ⟶ q) :
    ((stackPullback (stackProduct X Y).pullback f).map a).fst =
      (stackPullback X f).map a.fst := rfl

@[simp]
theorem stackProduct_pullback_map_snd (f : S ⟶ T)
    {p q : StackFiber (stackProduct X Y).pullback T} (a : p ⟶ q) :
    ((stackPullback (stackProduct X Y).pullback f).map a).snd =
      (stackPullback Y f).map a.snd := rfl

@[simp]
theorem stackProduct_pullbackComp_hom_fst (f : R ⟶ S) (g : S ⟶ T)
    (p : StackFiber (stackProduct X Y).pullback T) :
    ((stackPullbackCompIso (stackProduct X Y).pullback f g p).hom).fst =
      (stackPullbackCompIso X f g (CategoricalPullback.fst p)).hom := rfl

@[simp]
theorem stackProduct_pullbackComp_hom_snd (f : R ⟶ S) (g : S ⟶ T)
    (p : StackFiber (stackProduct X Y).pullback T) :
    ((stackPullbackCompIso (stackProduct X Y).pullback f g p).hom).snd =
      (stackPullbackCompIso Y f g (CategoricalPullback.snd p)).hom := rfl

@[simp]
theorem stackProduct_pullbackEq_hom_fst {f g : S ⟶ T} (h : f = g)
    (p : StackFiber (stackProduct X Y).pullback T) :
    ((stackPullbackObjIsoOfEq (stackProduct X Y).pullback h p).hom).fst =
      (stackPullbackObjIsoOfEq X h (CategoricalPullback.fst p)).hom := by
  subst g
  rfl

@[simp]
theorem stackProduct_pullbackEq_hom_snd {f g : S ⟶ T} (h : f = g)
    (p : StackFiber (stackProduct X Y).pullback T) :
    ((stackPullbackObjIsoOfEq (stackProduct X Y).pullback h p).hom).snd =
      (stackPullbackObjIsoOfEq Y h (CategoricalPullback.snd p)).hom := by
  subst g
  rfl

@[simp]
theorem stackProdObjIso_hom_fst {x x' : StackFiber X T} {y y' : StackFiber Y T}
    (a : x ≅ x') (b : y ≅ y') : (stackProdObjIso a b).hom.fst = a.hom := rfl

@[simp]
theorem stackProdObjIso_hom_snd {x x' : StackFiber X T} {y y' : StackFiber Y T}
    (a : x ≅ x') (b : y ≅ y') : (stackProdObjIso a b).hom.snd = b.hom := rfl

@[simp]
theorem stackPullback_stackProdObj_hom_fst (f : S ⟶ T)
    (x : StackFiber X T) (y : StackFiber Y T) :
    (stackPullback_stackProdObj f x y).hom.fst = 𝟙 _ := rfl

@[simp]
theorem stackPullback_stackProdObj_hom_snd (f : S ⟶ T)
    (x : StackFiber X T) (y : StackFiber Y T) :
    (stackPullback_stackProdObj f x y).hom.snd = 𝟙 _ := rfl

@[simp]
theorem stackIdentity_naturality_hom_app (f : S ⟶ T) (x : StackFiber X T) :
    ((Pseudofunctor.StrongTrans.id X.toPseudofunctor).naturality
      ⟨f.op⟩).hom.toNatTrans.app x = 𝟙 _ := by
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp

@[simp]
theorem stackDiagonal_app_map_fst {x y : StackFiber X T} (a : x ⟶ y) :
    (((stackDiagonal X).appFunctor T).map a).fst = a := rfl

@[simp]
theorem stackDiagonal_app_map_snd {x y : StackFiber X T} (a : x ⟶ y) :
    (((stackDiagonal X).appFunctor T).map a).snd = a := rfl

@[simp]
theorem stackDiagonal_naturality_hom_fst (f : S ⟶ T) (x : StackFiber X T) :
    (((Cat.Hom.toNatIso ((stackDiagonal X).naturality ⟨f.op⟩)).app x).hom).fst =
      𝟙 _ := by
  change (((StackTwoPullback.canonicalLiftNaturality X.toTerminal X.toTerminal
    (relativeDiagonalCone X.toTerminal) ⟨f.op⟩).hom.app x).fst) = 𝟙 _
  rw [StackTwoPullback.canonicalLiftNaturality_hom_app_fst]
  exact stackIdentity_naturality_hom_app f x

@[simp]
theorem stackDiagonal_naturality_hom_snd (f : S ⟶ T) (x : StackFiber X T) :
    (((Cat.Hom.toNatIso ((stackDiagonal X).naturality ⟨f.op⟩)).app x).hom).snd =
      𝟙 _ := by
  change (((StackTwoPullback.canonicalLiftNaturality X.toTerminal X.toTerminal
    (relativeDiagonalCone X.toTerminal) ⟨f.op⟩).hom.app x).snd) = 𝟙 _
  rw [StackTwoPullback.canonicalLiftNaturality_hom_app_snd]
  exact stackIdentity_naturality_hom_app f x

/-- The first component of the comparison induced by the diagonal. -/
theorem stackDiagonal_inducedComparison_hom_fst (map : R ⟶ T)
    (object : StackFiber X R) (p : StackFiber (stackSelfProduct X).pullback T)
    (universal : ((stackDiagonal X).appFunctor R).obj object ≅
      (stackPullback (stackSelfProduct X).pullback map).obj p)
    (l : S ⟶ R) (z : StackFiber X S) (a : z ≅ (stackPullback X l).obj object) :
    (stackMorphismInducedComparison (stackDiagonal X) map object p universal l z a).hom.fst =
      a.hom ≫ (stackPullback X l).map universal.hom.fst ≫
        (stackPullbackCompIso X l map (CategoricalPullback.fst p)).hom := by
  change (a.hom ≫ (𝟙 _ ≫ 𝟙 _)) ≫
    ((stackPullback X l).map universal.hom.fst ≫
      (stackPullbackCompIso X l map (CategoricalPullback.fst p)).hom) = _
  simp only [Category.comp_id]

/-- The second component of the comparison induced by the diagonal. -/
theorem stackDiagonal_inducedComparison_hom_snd (map : R ⟶ T)
    (object : StackFiber X R) (p : StackFiber (stackSelfProduct X).pullback T)
    (universal : ((stackDiagonal X).appFunctor R).obj object ≅
      (stackPullback (stackSelfProduct X).pullback map).obj p)
    (l : S ⟶ R) (z : StackFiber X S) (a : z ≅ (stackPullback X l).obj object) :
    (stackMorphismInducedComparison (stackDiagonal X) map object p universal l z a).hom.snd =
      a.hom ≫ (stackPullback X l).map universal.hom.snd ≫
        (stackPullbackCompIso X l map (CategoricalPullback.snd p)).hom := by
  change (a.hom ≫ (𝟙 _ ≫ 𝟙 _)) ≫
    ((stackPullback X l).map universal.hom.snd ≫
      (stackPullbackCompIso X l map (CategoricalPullback.snd p)).hom) = _
  simp only [Category.comp_id]

/-- Product extensionality uses exactly the supplied first component. -/
theorem stackProd_ext_hom_fst {Z : FppfStack.{u}}
    (h k : StackHom Z (stackProduct X Y).pullback)
    (hfst : StackIso2 (Pseudofunctor.StrongTrans.vcomp h (stackProdFst X Y))
      (Pseudofunctor.StrongTrans.vcomp k (stackProdFst X Y)))
    (hsnd : StackIso2 (Pseudofunctor.StrongTrans.vcomp h (stackProdSnd X Y))
      (Pseudofunctor.StrongTrans.vcomp k (stackProdSnd X Y)))
    (z : StackFiber Z T) :
    (((stackProd_ext h k hfst hsnd).appIso T).hom.app z).fst =
      (hfst.appIso T).hom.app z := by
  change ((hfst.appIso T).hom.app z ≫ 𝟙 _) ≫ (𝟙 _ ≫ 𝟙 _) = _
  simp only [Category.comp_id]

/-- Product extensionality uses exactly the supplied second component. -/
theorem stackProd_ext_hom_snd {Z : FppfStack.{u}}
    (h k : StackHom Z (stackProduct X Y).pullback)
    (hfst : StackIso2 (Pseudofunctor.StrongTrans.vcomp h (stackProdFst X Y))
      (Pseudofunctor.StrongTrans.vcomp k (stackProdFst X Y)))
    (hsnd : StackIso2 (Pseudofunctor.StrongTrans.vcomp h (stackProdSnd X Y))
      (Pseudofunctor.StrongTrans.vcomp k (stackProdSnd X Y)))
    (z : StackFiber Z T) :
    (((stackProd_ext h k hfst hsnd).appIso T).hom.app z).snd =
      (hsnd.appIso T).hom.app z := by
  change ((hsnd.appIso T).hom.app z ≫ 𝟙 _) ≫ (𝟙 _ ≫ 𝟙 _) = _
  simp only [Category.comp_id]

@[simp]
theorem stackProdMap_app_map_fst {X Y X' Y' : FppfStack.{u}}
    (f : StackHom X X') (g : StackHom Y Y') (T : Scheme.{u})
    {p q : StackFiber (stackProduct X Y).pullback T} (a : p ⟶ q) :
    (((stackProdMap f g).appFunctor T).map a).fst = (f.appFunctor T).map a.fst := rfl

@[simp]
theorem stackProdMap_app_map_snd {X Y X' Y' : FppfStack.{u}}
    (f : StackHom X X') (g : StackHom Y Y') (T : Scheme.{u})
    {p q : StackFiber (stackProduct X Y).pullback T} (a : p ⟶ q) :
    (((stackProdMap f g).appFunctor T).map a).snd = (g.appFunctor T).map a.snd := rfl

@[simp]
theorem stackProdMap_fst_hom_app {X Y X' Y' : FppfStack.{u}}
    (f : StackHom X X') (g : StackHom Y Y') (T : Scheme.{u})
    (p : StackFiber (stackProduct X Y).pullback T) :
    ((stackProdMap_fst f g).appIso T).hom.app p = 𝟙 _ := rfl

@[simp]
theorem stackProdMap_snd_hom_app {X Y X' Y' : FppfStack.{u}}
    (f : StackHom X X') (g : StackHom Y Y') (T : Scheme.{u})
    (p : StackFiber (stackProduct X Y).pullback T) :
    ((stackProdMap_snd f g).appIso T).hom.app p = 𝟙 _ := rfl

end GromovWitten.AlgebraicGeometry
