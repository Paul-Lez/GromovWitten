/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.StackFibreProducts
import GromovWitten.AlgebraicGeometry.Stacks.BilimitComparison

/-!
# Coherence of cone stacks

`ConeStack` (in `Cones/Stack.lean`) records the five comparison isomorphisms of the contraction
action, but not the higher coherence laws relating them.  Those laws are exactly what is needed
to transport a cone structure through a two-pullback, and they were hypotheses of
`ConeStack.baseChange` and `ConeStack.prod` in `Cones/StackFibreProducts.lean`.  This file
isolates them intrinsically and discharges those hypotheses.

## Main definitions and results

* `ConeStack.IsCoherent C`: the five intrinsic laws, each an equation of arrows in a fibre of the
  base stack, saying that `contractionOneIso`, `contractionMulIso`, `contractionZeroIso`,
  `contractionVertexIso` and `contractionPullbackIso` project, through
  `contractionProjectionIso` (and, for the zero law, through the section comparison
  `vertexProjectionIso`, and for the reindexing law through the strong-naturality cell
  `ConeStack.projectionNaturality` of the projection), to the expected comparisons.  No pentagon
  or triangle law beyond these five is needed for the constructions below.
* `ConeStack.BaseChangeCoherence.of_isCoherent` and `ConeStack.ProdCoherence.of_isCoherent`:
  a coherent cone stack (resp. a pair of coherent cone stacks) satisfies all the coherence
  hypotheses of `baseChange` (resp. `prod`), so `ConeStack.baseChangeOfCoherent` and
  `ConeStack.prodOfCoherent` are unconditional.
* `ConeStack.isCoherent_baseChange`: base change preserves coherence — for the base change the
  projection comparison is an identity, so all five laws degenerate to identities — hence
  `ConeStack.isCoherent_baseChangeOfCoherent`: iterated base changes stay unconditional.
* `ConeStack.isCoherent_zeroConeStack`, `isCoherent_zeroAbelianConeStack`,
  `isCoherent_zeroVectorBundleStack`: the concrete cone stacks of `Cones/Stack.lean` are
  coherent.

## Infrastructure

`StackIso2.symm_appIso_hom_app` and `whiskerRight_appIso_hom_app` (with the `associator` and
`whiskerLeft` components of `Stacks/BilimitComparison.lean`) compute the fibre components of the
bicategorical operations on stack 2-cells (the unitors and `trans` are already in
`Stacks/TwoPullback.lean`), and `StackHom.naturalityIso` packages the strong-naturality cell of a
stack morphism as a natural isomorphism of fibres.
`ConeStack.baseChange_stackPullback_obj_iso_hom`, `prod_stackPullback_obj_iso_hom`,
`baseChangeVertex_obj_iso_hom` and `prodVertex_obj_iso_hom` compute the comparison isomorphisms of
the points of the two-pullback constructions.

Because the fibres of a two-pullback stack are only definitionally (not syntactically) the
categorical pullbacks, `simp` and `rw` are frequently unusable inside these goals; the small
abstract lemmas `idComp_id`, `idComp_idComp_id`, `idComp_idComp_id_mapId`, `idIdComp`,
`idCompCompId`, `comp_map_id`, `law_reassoc`, `assoc_cancel_inv_hom`, `prod_mul_law`,
`prod_zero_law` and `prod_pullback_law` are stated in an arbitrary category so that they can be
applied through definitional unfolding.

## What is not done

Coherence of a fibre product (`IsCoherent (prod C D hp)`) is not proved here; only its base
change counterpart is.  The five laws are not shown to be independent, and no coherence theorem
("all diagrams commute") is attempted.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

/-! ### Fibre components of the bicategorical operations on stack 2-cells -/

namespace StackIso2

variable {X Y : FppfStack.{u}} {p q : StackHom X Y}

/-- The fibre components of the inverse of an invertible stack 2-cell. -/
@[simp]
theorem symm_appIso_hom_app (e : StackIso2 p q) (T : Scheme.{u}) (x : StackFiber X T) :
    ((e.symm).appIso T).hom.app x = (e.appIso T).inv.app x :=
  rfl

/-- The fibre components of a right whiskering are the images of the components of the
2-cell. -/
@[simp]
theorem whiskerRight_appIso_hom_app {Z : FppfStack.{u}} (e : StackIso2 p q)
    (r : StackHom Y Z) (T : Scheme.{u}) (x : StackFiber X T) :
    ((StackIso2.whiskerRight e r).appIso T).hom.app x =
      (StackHom.appFunctor r T).map ((e.appIso T).hom.app x) :=
  rfl

end StackIso2

namespace StackHom

/-- The strong-naturality cell of a morphism of stacks, as a natural isomorphism between the two
composites of pullback and the morphism on fibres. -/
noncomputable def naturalityIso {X Y : FppfStack.{u}} (q : StackHom X Y) {S T : Scheme.{u}}
    (h : S ⟶ T) :
    stackPullback X h ⋙ StackHom.appFunctor q S ≅
      StackHom.appFunctor q T ⋙ stackPullback Y h :=
  Cat.Hom.toNatIso (q.naturality (Quiver.Hom.toLoc h.op))

end StackHom

namespace ConeStack

variable {base : FppfStack.{u}} {O : FppfScalarRings.{u}}

/-- The strong-naturality cell of the projection of a cone stack, as a natural isomorphism
between the two composites of pullback and projection on fibres. -/
noncomputable def projectionNaturality (C : ConeStack base O) {S T : Scheme.{u}} (h : S ⟶ T) :
    stackPullback C.total h ⋙ StackHom.appFunctor C.projection S ≅
      StackHom.appFunctor C.projection T ⋙ stackPullback base h :=
  StackHom.naturalityIso C.projection h

/-! ### The intrinsic coherence laws of a cone stack -/

/-- The higher coherence laws of the contraction data of a cone stack which `ConeStack` itself
does not encode: each of the five comparison isomorphisms of the contraction must be compatible
with the comparison `contractionProjectionIso` expressing that contraction lies over the base
(and, for `contractionZeroIso`, with the section property of the vertex).

Every law is an equation between arrows of a fibre of the base stack, stated intrinsically in
terms of `C`.  They are exactly what is needed to transport the contraction structure through
two-pullbacks, see `BaseChangeCoherence.of_isCoherent` and `ProdCoherence.of_isCoherent`.  No
pentagon or triangle law beyond these five is used. -/
structure IsCoherent (C : ConeStack base O) : Prop where
  /-- Contracting by one projects to the projection comparison. -/
  one (T : Scheme.{u}) (x : StackFiber C.total T) :
    (StackHom.appFunctor C.projection T).map ((C.contractionOneIso T).hom.app x) =
      (C.contractionProjectionIso T 1).hom.app x
  /-- Contracting by a product projects to the composite of the projection comparisons. -/
  mul (T : Scheme.{u}) (r s : O.ring T) (x : StackFiber C.total T) :
    (StackHom.appFunctor C.projection T).map ((C.contractionMulIso T r s).hom.app x) ≫
        (C.contractionProjectionIso T r).hom.app ((C.contraction T s).obj x) ≫
          (C.contractionProjectionIso T s).hom.app x =
      (C.contractionProjectionIso T (r * s)).hom.app x
  /-- Contracting by zero projects, through the section property of the vertex, to the
  projection comparison. -/
  zero (T : Scheme.{u}) (x : StackFiber C.total T) :
    (StackHom.appFunctor C.projection T).map ((C.contractionZeroIso T).hom.app x) ≫
        (C.vertexProjectionIso.appIso T).hom.app
          ((StackHom.appFunctor C.projection T).obj x) =
      (C.contractionProjectionIso T 0).hom.app x
  /-- Contracting the vertex projects to the projection comparison. -/
  vertex (T : Scheme.{u}) (r : O.ring T) (b : StackFiber base T) :
    (StackHom.appFunctor C.projection T).map ((C.contractionVertexIso T r).hom.app b) =
      (C.contractionProjectionIso T r).hom.app ((StackHom.appFunctor C.vertex T).obj b)
  /-- Contracting commutes with reindexing compatibly with the projection comparison and the
  strong-naturality cell of the projection. -/
  pullback {S T : Scheme.{u}} (h : S ⟶ T) (r : O.ring T) (x : StackFiber C.total T) :
    (StackHom.appFunctor C.projection S).map ((C.contractionPullbackIso h r).hom.app x) ≫
        (C.contractionProjectionIso S (O.pullback h r)).hom.app
            ((stackPullback C.total h).obj x) ≫
          (C.projectionNaturality h).hom.app x =
      (C.projectionNaturality h).hom.app ((C.contraction T r).obj x) ≫
        (stackPullback base h).map ((C.contractionProjectionIso T r).hom.app x)

/-- Cancelling an inverse against its isomorphism inside a composite.  Stated abstractly for
use through definitional unfolding. -/
theorem assoc_cancel_inv_hom {W : Type*} [Category W] {a b c d : W} (u : a ⟶ b) (v : b ⟶ c)
    (e : d ≅ c) : (u ≫ v ≫ e.inv) ≫ e.hom = u ≫ v := by
  simp

/-- Two identities compose to an identity.  Stated abstractly for use through definitional
unfolding. -/
theorem idComp_id {W : Type*} [Category W] (a : W) : 𝟙 a ≫ 𝟙 a = 𝟙 a := by
  simp

/-- Three identities compose to an identity.  Stated abstractly for use through definitional
unfolding. -/
theorem idComp_idComp_id {W : Type*} [Category W] (a : W) : 𝟙 a ≫ 𝟙 a ≫ 𝟙 a = 𝟙 a := by
  simp

/-- The identity-only instance of the reindexing coherence law.  Stated abstractly for use
through definitional unfolding. -/
theorem idComp_idComp_id_mapId {W V : Type*} [Category W] [Category V] (F : W ⥤ V) (a : W) :
    𝟙 (F.obj a) ≫ 𝟙 (F.obj a) ≫ 𝟙 (F.obj a) = 𝟙 (F.obj a) ≫ F.map (𝟙 a) := by
  simp

/-- The multiplication law of a fibre product, abstractly. -/
theorem prod_mul_law {W : Type*} [Category W] {a b c d e g k m : W}
    {dC : a ⟶ b} {A : b ⟶ c} {B : c ⟶ d} (α : d ⟶ e) {cRS : a ⟶ d}
    (es : g ≅ e) (er : k ≅ g) (ers : m ≅ e) {dD : m ⟶ k}
    (hC : dC ≫ A ≫ B = cRS) (hD : dD ≫ er.hom ≫ es.hom = ers.hom) :
    dC ≫ A ≫ (B ≫ α ≫ es.inv) ≫ er.inv = (cRS ≫ α ≫ ers.inv) ≫ dD := by
  have hinv : ers.inv ≫ dD = es.inv ≫ er.inv := by
    rw [Iso.inv_comp_eq, ← hD]
    simp
  calc dC ≫ A ≫ (B ≫ α ≫ es.inv) ≫ er.inv
      = (dC ≫ A ≫ B) ≫ α ≫ es.inv ≫ er.inv := by simp
    _ = cRS ≫ α ≫ es.inv ≫ er.inv := by rw [hC]
    _ = cRS ≫ α ≫ ers.inv ≫ dD := by rw [hinv]
    _ = (cRS ≫ α ≫ ers.inv) ≫ dD := by simp

/-- The zero law of a fibre product, abstractly. -/
theorem prod_zero_law {W : Type*} [Category W] {a b c d e g k : W}
    {uC : a ⟶ b} (ECs : b ≅ c) {FC : a ⟶ c} (α : c ≅ d) {uD : e ⟶ g} (EDq : g ≅ d)
    (FD : e ≅ d) {w : g ⟶ k} (EDs : k ≅ c) {wtot : e ⟶ k}
    (hsplit : wtot = uD ≫ w)
    (hC : uC ≫ ECs.hom = FC) (hD : uD ≫ EDq.hom = FD.hom)
    (hnat : w ≫ EDs.hom = EDq.hom ≫ α.inv) :
    uC ≫ ECs.hom ≫ EDs.inv = (FC ≫ α.hom ≫ FD.inv) ≫ wtot := by
  subst hsplit
  have h1₀ : FD.inv ≫ uD = EDq.inv := by
    rw [Iso.inv_comp_eq, ← hD]
    simp
  have h1 : ∀ {z : W} (t : g ⟶ z), FD.inv ≫ uD ≫ t = EDq.inv ≫ t := by
    intro z t
    rw [← Category.assoc, h1₀]
  have h2 : EDq.inv ≫ w = α.inv ≫ EDs.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat]
    simp
  calc uC ≫ ECs.hom ≫ EDs.inv = (uC ≫ ECs.hom) ≫ EDs.inv := by simp
    _ = FC ≫ EDs.inv := by rw [hC]
    _ = (FC ≫ α.hom ≫ FD.inv) ≫ uD ≫ w := by
        simp only [Category.assoc, h1 w, h2]
        simp

/-- The reindexing law of a fibre product, abstractly. -/
theorem prod_pullback_law {W : Type*} [Category W] {a b c d e g k l n m : W}
    {PC : a ⟶ b} (GC : b ≅ c) (NC : c ≅ d) (M : d ⟶ e) (ND : g ≅ e) (GD : k ≅ g)
    {NC' : a ⟶ l} {MC : l ⟶ d} (MD : n ≅ e) (ND' : m ≅ n) {PD : m ⟶ k} {Mtot : l ⟶ n}
    (hsplit : Mtot = MC ≫ M ≫ MD.inv)
    (hC : PC ≫ GC.hom ≫ NC.hom = NC' ≫ MC)
    (hD : PD ≫ GD.hom ≫ ND.hom = ND'.hom ≫ MD.hom) :
    PC ≫ GC.hom ≫ (NC.hom ≫ M ≫ ND.inv) ≫ GD.inv =
      (NC' ≫ Mtot ≫ ND'.inv) ≫ PD := by
  subst hsplit
  have key : MD.inv ≫ ND'.inv ≫ PD = ND.inv ≫ GD.inv := by
    have h1 : ND'.hom ≫ MD.hom ≫ ND.inv ≫ GD.inv = PD := by
      rw [← Category.assoc, ← hD]
      simp
    rw [← h1]
    simp
  calc PC ≫ GC.hom ≫ (NC.hom ≫ M ≫ ND.inv) ≫ GD.inv
      = (PC ≫ GC.hom ≫ NC.hom) ≫ M ≫ ND.inv ≫ GD.inv := by simp
    _ = (NC' ≫ MC) ≫ M ≫ ND.inv ≫ GD.inv := by rw [hC]
    _ = (NC' ≫ (MC ≫ M ≫ MD.inv) ≫ ND'.inv) ≫ PD := by
        simp only [Category.assoc, key]

/-- Reassociation of a three-fold composite along a law of the shape used by the coherence
axioms.  It is stated abstractly so that it can be used through definitional unfolding. -/
theorem law_reassoc {W : Type*} [Category W] {a b c d x e g : W} {p : a ⟶ b} {q : b ⟶ c}
    {n : c ⟶ d} {n' : a ⟶ x} {u : x ⟶ d} (h : p ≫ q ≫ n = n' ≫ u) (m : d ⟶ e) (k : e ⟶ g) :
    p ≫ q ≫ n ≫ m ≫ k = n' ≫ (u ≫ m) ≫ k := by
  calc p ≫ q ≫ n ≫ m ≫ k = (p ≫ q ≫ n) ≫ m ≫ k := by simp
    _ = (n' ≫ u) ≫ m ≫ k := by rw [h]
    _ = n' ≫ (u ≫ m) ≫ k := by simp

/-- Composing with the image of an identity, in any category.  It is stated abstractly so that
it can be used through definitional unfolding. -/
theorem comp_map_id {W V : Type*} [Category W] [Category V] (F : W ⥤ V) {a : W} {c : V}
    (v : c ⟶ F.obj a) : v ≫ F.map (𝟙 a) = v := by
  simp

/-- An arrow surrounded by identities, in any category.  It is stated abstractly so that it can
be used through definitional unfolding, where rewriting is blocked by the category instances of
the fibres. -/
theorem idCompCompId {W : Type*} [Category W] {a b : W} (v : a ⟶ b) :
    𝟙 a ≫ v ≫ 𝟙 b ≫ 𝟙 b = v := by
  simp

/-- A composite of identities with one arrow, in any category.  It is stated abstractly so
that it can be used through definitional unfolding, where rewriting is blocked by the
category instances of the fibres. -/
theorem idIdComp {W : Type*} [Category W] {a b : W} (v : a ⟶ b) :
    (𝟙 a ≫ 𝟙 a) ≫ 𝟙 a ≫ v = v ≫ 𝟙 b := by
  simp

/-! ### The zero cone stack is coherent -/

/-- The zero cone stack, whose contraction is the identity functor and whose comparisons are
unitors, satisfies all the coherence laws. -/
theorem isCoherent_zeroConeStack (base : FppfStack.{u}) (O : FppfScalarRings.{u}) :
    IsCoherent (zeroConeStack base O) where
  one T x := rfl
  mul T r s x := by
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  zero T x := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  vertex T r b := rfl
  pullback := by
    intro S T h r x
    convert idIdComp (((zeroConeStack base O).projectionNaturality h).hom.app x) using 1 <;>
      first
        | rfl
        | exact heq_of_eq (congrArg
            (fun m => ((zeroConeStack base O).projectionNaturality h).hom.app x ≫ m)
            ((stackPullback base h).map_id _))

/-- The underlying cone stack of the zero abelian cone stack is coherent. -/
theorem isCoherent_zeroAbelianConeStack (base : FppfStack.{u}) (O : FppfScalarRings.{u}) :
    IsCoherent (zeroAbelianConeStack base O).toConeStack :=
  isCoherent_zeroConeStack base O

/-- The underlying cone stack of the rank-zero vector-bundle stack is coherent. -/
theorem isCoherent_zeroVectorBundleStack (X : AlgebraicStack.{u}) :
    IsCoherent (zeroVectorBundleStack X).toAbelianConeStack.toConeStack :=
  isCoherent_zeroConeStack X.toStack canonicalFppfScalarRings

/-! ### Fibre formulas for the two-pullback constructions -/

variable {base' : FppfStack.{u}}

/-- The comparison isomorphism of a point of a base-changed cone stack after reindexing. -/
theorem baseChange_stackPullback_obj_iso_hom (C : ConeStack base O) (f : StackHom base' base)
    {S T : Scheme.{u}} (h : S ⟶ T) (p : StackFiber (baseChangeTotal C f) T) :
    (CategoricalPullback.iso ((stackPullback (baseChangeTotal C f) h).obj p)).hom =
      (C.projectionNaturality h).hom.app (CategoricalPullback.fst p) ≫
        (stackPullback base h).map (CategoricalPullback.iso p).hom ≫
          (StackHom.naturalityIso f h).inv.app (CategoricalPullback.snd p) :=
  rfl

/-- The comparison isomorphism of a point of a fibre product of cone stacks after
reindexing. -/
theorem prod_stackPullback_obj_iso_hom (C D : ConeStack base O)
    {S T : Scheme.{u}} (h : S ⟶ T) (p : StackFiber (prodTotal C D) T) :
    (CategoricalPullback.iso ((stackPullback (prodTotal C D) h).obj p)).hom =
      (C.projectionNaturality h).hom.app (CategoricalPullback.fst p) ≫
        (stackPullback base h).map (CategoricalPullback.iso p).hom ≫
          (D.projectionNaturality h).inv.app (CategoricalPullback.snd p) :=
  rfl

/-- The comparison isomorphism of a vertex point of a base-changed cone stack. -/
@[simp]
theorem baseChangeVertex_obj_iso_hom (C : ConeStack base O) (f : StackHom base' base)
    (T : Scheme.{u}) (b : StackFiber base' T) :
    (CategoricalPullback.iso ((StackHom.appFunctor (baseChangeVertex C f) T).obj b)).hom =
      (C.vertexProjectionIso.appIso T).hom.app ((StackHom.appFunctor f T).obj b) := by
  change ((baseChangeVertexCone C f).comparison.appIso T).hom.app b = _
  simp only [baseChangeVertexCone, StackTwoPullback.trans_appIso_hom_app,
    StackIso2.associator_appIso_hom_app, StackIso2.whiskerLeft_appIso_hom_app,
    StackTwoPullback.rightUnitor_appIso_hom_app, StackIso2.symm_appIso_hom_app,
    StackTwoPullback.leftUnitor_appIso_inv_app]
  exact idCompCompId _

/-- The comparison isomorphism of a vertex point of a fibre product of cone stacks. -/
@[simp]
theorem prodVertex_obj_iso_hom (C D : ConeStack base O) (T : Scheme.{u})
    (b : StackFiber base T) :
    (CategoricalPullback.iso ((StackHom.appFunctor (prodVertex C D) T).obj b)).hom =
      (C.vertexProjectionIso.appIso T).hom.app b ≫
        (D.vertexProjectionIso.appIso T).inv.app b := by
  change ((prodVertexCone C D).comparison.appIso T).hom.app b = _
  simp only [prodVertexCone, StackTwoPullback.trans_appIso_hom_app,
    StackIso2.symm_appIso_hom_app]

/-! ### Coherent cone stacks have unconditional base changes and fibre products -/

/-- A coherent cone stack satisfies all the coherence hypotheses used by `baseChange`. -/
theorem BaseChangeCoherence.of_isCoherent {C : ConeStack base O} (hC : IsCoherent C)
    (f : StackHom base' base) : BaseChangeCoherence C f where
  one := hC.one
  mul := hC.mul
  vertex T r b := by
    dsimp [baseChangeContraction]
    simp only [hC.vertex T r ((StackHom.appFunctor f T).obj b)]
    exact (comp_map_id (StackHom.appFunctor f T) _).symm
  zero T p := by
    have hnat : (StackHom.appFunctor C.projection T).map
          ((StackHom.appFunctor C.vertex T).map (CategoricalPullback.iso p).hom) ≫
            (C.vertexProjectionIso.appIso T).hom.app ((StackHom.appFunctor f T).obj
              ((StackHom.appFunctor (baseChangeProjection C f) T).obj p)) =
          (C.vertexProjectionIso.appIso T).hom.app
              ((StackHom.appFunctor C.projection T).obj (CategoricalPullback.fst p)) ≫
            (CategoricalPullback.iso p).hom :=
      (C.vertexProjectionIso.appIso T).hom.naturality (CategoricalPullback.iso p).hom
    have h0 := hC.zero T (CategoricalPullback.fst p)
    dsimp [baseChangeContraction]
    simp only [Functor.map_comp, baseChangeVertex_obj_iso_hom]
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => (StackHom.appFunctor C.projection T).map
      ((C.contractionZeroIso T).hom.app (CategoricalPullback.fst p)) ≫ m) hnat).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun m => m ≫ (CategoricalPullback.iso p).hom) h0).trans ?_
    exact (comp_map_id (StackHom.appFunctor f T) _).symm
  pullback := by
    intro S T h r p
    have hpb := hC.pullback h r (CategoricalPullback.fst p)
    refine (law_reassoc hpb _ _).trans ?_
    refine (congrArg (fun z => (C.projectionNaturality h).hom.app
        ((C.contraction T r).obj (CategoricalPullback.fst p)) ≫ z ≫
        (StackHom.naturalityIso f h).inv.app (CategoricalPullback.snd p))
      (Functor.map_comp (stackPullback base h) ((C.contractionProjectionIso T r).hom.app
        (CategoricalPullback.fst p)) (CategoricalPullback.iso p).hom).symm).trans ?_
    exact (comp_map_id (StackHom.appFunctor f S) _).symm

/-- The base change of a coherent cone stack, with no coherence hypothesis. -/
noncomputable def baseChangeOfCoherent {C : ConeStack base O} (hC : IsCoherent C)
    (f : StackHom base' base) : ConeStack base' O :=
  baseChange C f (BaseChangeCoherence.of_isCoherent hC f)


/-- A coherent pair of cone stacks satisfies the coherence hypotheses of `prod` for the two
laws which only involve the unit and the vertex. -/
theorem prodCoherence_one {C D : ConeStack base O} (hC : IsCoherent C) (hD : IsCoherent D)
    (T : Scheme.{u}) (p : StackFiber (prodTotal C D) T) :
    (StackHom.appFunctor C.projection T).map
          ((C.contractionOneIso T).app (CategoricalPullback.fst p)).hom ≫
        (CategoricalPullback.iso p).hom =
      (CategoricalPullback.iso ((prodContraction C D T 1).obj p)).hom ≫
        (StackHom.appFunctor D.projection T).map
          ((D.contractionOneIso T).app (CategoricalPullback.snd p)).hom := by
  refine (congrArg (fun m => m ≫ (CategoricalPullback.iso p).hom)
    (hC.one T (CategoricalPullback.fst p))).trans ?_
  refine Eq.trans ?_
    (congrArg (fun m => _ ≫ m) (hD.one T (CategoricalPullback.snd p))).symm
  exact (assoc_cancel_inv_hom _ _ _).symm

/-- The vertex law of the fibre product follows from the vertex laws of the two factors. -/
theorem prodCoherence_vertex {C D : ConeStack base O} (hC : IsCoherent C) (hD : IsCoherent D)
    (T : Scheme.{u}) (r : O.ring T) (b : StackFiber base T) :
    (StackHom.appFunctor C.projection T).map ((C.contractionVertexIso T r).app b).hom ≫
        (CategoricalPullback.iso ((StackHom.appFunctor (prodVertex C D) T).obj b)).hom =
      (CategoricalPullback.iso ((StackHom.appFunctor (prodVertex C D) T ⋙
          prodContraction C D T r).obj b)).hom ≫
        (StackHom.appFunctor D.projection T).map
          ((D.contractionVertexIso T r).app b).hom := by
  refine (congrArg (fun m => m ≫ (CategoricalPullback.iso
    ((StackHom.appFunctor (prodVertex C D) T).obj b)).hom) (hC.vertex T r b)).trans ?_
  refine Eq.trans ?_ (congrArg (fun m => _ ≫ m) (hD.vertex T r b)).symm
  exact (assoc_cancel_inv_hom _ _ _).symm


/-- The multiplication law of the fibre product follows from the multiplication laws of the two
factors. -/
theorem prodCoherence_mul {C D : ConeStack base O} (hC : IsCoherent C) (hD : IsCoherent D)
    (T : Scheme.{u}) (r s : O.ring T) (p : StackFiber (prodTotal C D) T) :
    (StackHom.appFunctor C.projection T).map
          ((C.contractionMulIso T r s).app (CategoricalPullback.fst p)).hom ≫
        (CategoricalPullback.iso
          ((prodContraction C D T s ⋙ prodContraction C D T r).obj p)).hom =
      (CategoricalPullback.iso ((prodContraction C D T (r * s)).obj p)).hom ≫
        (StackHom.appFunctor D.projection T).map
          ((D.contractionMulIso T r s).app (CategoricalPullback.snd p)).hom :=
  prod_mul_law (CategoricalPullback.iso p).hom
    ((D.contractionProjectionIso T s).app (CategoricalPullback.snd p))
    ((D.contractionProjectionIso T r).app
      ((D.contraction T s).obj (CategoricalPullback.snd p)))
    ((D.contractionProjectionIso T (r * s)).app (CategoricalPullback.snd p))
    (hC.mul T r s (CategoricalPullback.fst p))
    (hD.mul T r s (CategoricalPullback.snd p))

/-- The zero law of the fibre product follows from the zero laws of the two factors and the
naturality of the section comparison of the second one. -/
theorem prodCoherence_zero {C D : ConeStack base O} (hC : IsCoherent C) (hD : IsCoherent D)
    (T : Scheme.{u}) (p : StackFiber (prodTotal C D) T) :
    (StackHom.appFunctor C.projection T).map
          ((C.contractionZeroIso T).app (CategoricalPullback.fst p)).hom ≫
        (CategoricalPullback.iso ((StackHom.appFunctor (prodVertex C D) T).obj
          ((StackHom.appFunctor (prodProjection C D) T).obj p))).hom =
      (CategoricalPullback.iso ((prodContraction C D T 0).obj p)).hom ≫
        (StackHom.appFunctor D.projection T).map
          (((D.contractionZeroIso T).app (CategoricalPullback.snd p)).trans
            ((StackHom.appFunctor D.vertex T).mapIso (CategoricalPullback.iso p).symm)).hom :=
  prod_zero_law
    ((C.vertexProjectionIso.appIso T).app
      ((StackHom.appFunctor (prodProjection C D) T).obj p))
    (CategoricalPullback.iso p)
    ((D.vertexProjectionIso.appIso T).app
      ((StackHom.appFunctor D.projection T).obj (CategoricalPullback.snd p)))
    ((D.contractionProjectionIso T 0).app (CategoricalPullback.snd p))
    ((D.vertexProjectionIso.appIso T).app
      ((StackHom.appFunctor (prodProjection C D) T).obj p))
    (Functor.map_comp _ _ _)
    (hC.zero T (CategoricalPullback.fst p))
    (hD.zero T (CategoricalPullback.snd p))
    ((D.vertexProjectionIso.appIso T).hom.naturality (CategoricalPullback.iso p).inv)

/-- The reindexing law of the fibre product follows from the reindexing laws of the two
factors. -/
theorem prodCoherence_pullback {C D : ConeStack base O} (hC : IsCoherent C) (hD : IsCoherent D)
    {S T : Scheme.{u}} (h : S ⟶ T) (r : O.ring T) (p : StackFiber (prodTotal C D) T) :
    (StackHom.appFunctor C.projection S).map
          ((C.contractionPullbackIso h r).app (CategoricalPullback.fst p)).hom ≫
        (CategoricalPullback.iso ((stackPullback (prodTotal C D) h ⋙
          prodContraction C D S (O.pullback h r)).obj p)).hom =
      (CategoricalPullback.iso ((prodContraction C D T r ⋙
          stackPullback (prodTotal C D) h).obj p)).hom ≫
        (StackHom.appFunctor D.projection S).map
          ((D.contractionPullbackIso h r).app (CategoricalPullback.snd p)).hom := by
  refine prod_pullback_law
    ((C.contractionProjectionIso S (O.pullback h r)).app
      ((stackPullback C.total h).obj (CategoricalPullback.fst p)))
    ((C.projectionNaturality h).app (CategoricalPullback.fst p))
    ((stackPullback base h).map (CategoricalPullback.iso p).hom)
    ((D.projectionNaturality h).app (CategoricalPullback.snd p))
    ((D.contractionProjectionIso S (O.pullback h r)).app
      ((stackPullback D.total h).obj (CategoricalPullback.snd p)))
    ((stackPullback base h).mapIso
      ((D.contractionProjectionIso T r).app (CategoricalPullback.snd p)))
    ((D.projectionNaturality h).app ((D.contraction T r).obj (CategoricalPullback.snd p)))
    ((Functor.map_comp _ _ _).trans (congrArg (fun z => _ ≫ z) (Functor.map_comp _ _ _)))
    (hC.pullback h r (CategoricalPullback.fst p))
    (hD.pullback h r (CategoricalPullback.snd p))

/-- A pair of coherent cone stacks satisfies all the coherence hypotheses used by `prod`. -/
theorem ProdCoherence.of_isCoherent {C D : ConeStack base O} (hC : IsCoherent C)
    (hD : IsCoherent D) : ProdCoherence C D where
  one := prodCoherence_one hC hD
  mul := prodCoherence_mul hC hD
  vertex := prodCoherence_vertex hC hD
  zero := prodCoherence_zero hC hD
  pullback := prodCoherence_pullback hC hD

/-- The fibre product of two coherent cone stacks, with no coherence hypothesis. -/
noncomputable def prodOfCoherent {C D : ConeStack base O} (hC : IsCoherent C)
    (hD : IsCoherent D) : ConeStack base O :=
  prod C D (ProdCoherence.of_isCoherent hC hD)

/-- Coherence is inherited by base change: the base-changed cone stack has an identity
projection comparison, so all five laws reduce to identities. -/
theorem isCoherent_baseChange {C : ConeStack base O} (f : StackHom base' base)
    (hc : BaseChangeCoherence C f) : IsCoherent (baseChange C f hc) where
  one _ _ := rfl
  vertex _ _ _ := rfl
  mul T r s p := idComp_idComp_id _
  zero T p := idComp_id _
  pullback := by
    intro S T h r p
    exact idComp_idComp_id_mapId (stackPullback base' h) _

/-- The base change of a coherent cone stack is coherent, so iterated base changes stay
unconditional. -/
theorem isCoherent_baseChangeOfCoherent {C : ConeStack base O} (hC : IsCoherent C)
    (f : StackHom base' base) : IsCoherent (baseChangeOfCoherent hC f) :=
  isCoherent_baseChange f (BaseChangeCoherence.of_isCoherent hC f)


end ConeStack

end GromovWitten.AlgebraicGeometry
