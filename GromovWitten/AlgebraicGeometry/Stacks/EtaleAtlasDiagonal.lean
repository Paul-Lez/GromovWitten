/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.DiagonalComparison
import GromovWitten.AlgebraicGeometry.Stacks.StackProducts
import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent
import GromovWitten.AlgebraicGeometry.Morphisms.Unramified

/-!
# An étale atlas gives an unramified diagonal, unconditionally

`Stacks.StackProducts` proves the Deligne--Mumford diagonal criterion
(`stackDiagonal_unramified_of_etaleAtlas`) from an étale surjective chart `A` under the extra
hypothesis `A.HasUnramifiedIsom`, the statement that every isomorphism scheme of a pair of chart
objects is representable by a scheme unramified over the base.  This file proves that hypothesis
is automatic: it always holds for an étale surjective chart.

The construction avoids the stack-bicategorical route considered in the docstrings of
`Stacks.StackProducts` (2-cartesianness of the self-overlap square, which would need a genuinely
new bicategorical bilimit).  Instead it stays entirely at the level of
`StackChart.PullbackPresentation`, i.e. honest scheme pullbacks:

* `A.IsRepresentable` applied to `A`'s own tautological object over `A.scheme` produces an
  honest scheme `P.space` representing the self-overlap of `A` with itself; if `A` is étale
  surjective its first projection `P.fst : P.space ⟶ A.scheme` is étale, hence unramified.
* For arbitrary `a b : S ⟶ A.scheme`, the ordinary scheme pullback of `(a, b) : S ⟶ A.scheme ⨯
  A.scheme` against `(P.fst, P.snd) : P.space ⟶ A.scheme ⨯ A.scheme` is a `DiagonalPresentation`
  of `stackDiagonal X` at `(A.obj S a, A.obj S b)`, whose structure map to `S` is unramified
  because it is a base change of `(P.fst, P.snd)`, which is unramified because its own
  postcomposition with either product projection is `P.fst` or (up to symmetry) unramified.

This gives `StackChart.hasUnramifiedIsom_of_isEtaleSurjective`, hence the unconditional forward
direction of the Deligne--Mumford diagonal criterion,
`DeligneMumfordStack.stackDiagonal_unramified'` and
`AlgebraicStack.stackDiagonal_unramified_of_etaleChart`.

All the constructions of this file are parameterised by `hA : A.IsRepresentable` only (étale
surjectivity is used solely in `selfOverlapScheme_fst_prop` and its consequences), which makes
them available for the **converse** criterion, where the chart is merely smooth:
`StackChart.selfOverlapPair_unramified_of_stackDiagonal_unramified` deduces, from
`(stackDiagonal X).Unramified`, that `(P.fst, P.snd) : P.space ⟶ A.scheme ⨯ A.scheme` is
unramified, by identifying `P.space` with the isomorphism scheme of the pair
`(prod.fst, prod.snd)` over `A.scheme ⨯ A.scheme` and using that unramifiedness of the diagonal
does not depend on the chosen presentation.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackChart

variable {X : FppfStack.{u}} (A : StackChart X)

/-! ## Naturality of the chart pullback comparison under composition -/

set_option backward.isDefEq.respectTransparency false in
/-- **`objPullbackIso` is compatible with a further test-scheme pullback.**  Pulling back
`A.objPullbackIso g k` along a further map `m` and correcting through
`A.inducedComparison`/`stackPullbackCompIso` recovers `A.objPullbackIso (m ≫ g) k` up to
reassociation.  This is the naturality square underlying `A.map`'s pseudonaturality, isolated
here because it is used repeatedly below and is not otherwise recorded in `Stacks.Algebraic`. -/
theorem objPullbackIso_comp {U T S : Scheme.{u}} (g : U ⟶ T) (k : T ⟶ A.scheme) (m : S ⟶ U) :
    A.inducedComparison g (g ≫ k) (A.objPullbackIso g k) m =
      (A.objIsoOfEq (Category.assoc m g k).symm).trans (A.objPullbackIso (m ≫ g) k) := by
  apply Iso.ext
  have h := Pseudofunctor.StrongTrans.naturality_comp_hom_app
    A.map ⟨g.op⟩ ⟨m.op⟩ (Discrete.mk (ULift.up k))
  dsimp [representedStack, StackInGroupoids.ofSheafOfTypes,
    Pseudofunctor.ofPresheafOfTypes, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete, typeToCat] at h
  let gop : LocallyDiscrete.mk (Opposite.op T) ⟶
      LocallyDiscrete.mk (Opposite.op U) := ⟨g.op⟩
  let mop : LocallyDiscrete.mk (Opposite.op U) ⟶
      LocallyDiscrete.mk (Opposite.op S) := ⟨m.op⟩
  let mgop : LocallyDiscrete.mk (Opposite.op T) ⟶
      LocallyDiscrete.mk (Opposite.op S) := ⟨(m ≫ g).op⟩
  have hop : gop ≫ mop = mgop := rfl
  change (A.map.naturality (gop ≫ mop)).hom.toNatTrans.app (Discrete.mk (ULift.up k)) = _ at h
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  simp only [inducedComparison, objIsoOfEq, objPullbackIso, Iso.trans_hom,
    Functor.mapIso, Category.assoc, Iso.refl_hom, Category.id_comp]
  exact h.symm

/-- A restatement of `objPullbackIso_comp` with `inducedComparison` unfolded, isolating the
pulled-back naturality iso on one side. -/
theorem mapIso_objPullbackIso_comp {U T S : Scheme.{u}} (g : U ⟶ T) (k : T ⟶ A.scheme)
    (m : S ⟶ U) :
    ((A.objPullbackIso m (g ≫ k)).trans
        ((stackPullback X m).mapIso (A.objPullbackIso g k))).trans
          (stackPullbackCompIso X m g (A.obj T k)) =
      (A.objIsoOfEq (Category.assoc m g k).symm).trans (A.objPullbackIso (m ≫ g) k) :=
  A.objPullbackIso_comp g k m

/-- Solving `mapIso_objPullbackIso_comp` for the isolated pulled-back naturality iso. -/
theorem mapIso_objPullbackIso {U T S : Scheme.{u}} (g : U ⟶ T) (k : T ⟶ A.scheme)
    (m : S ⟶ U) :
    ((stackPullback X m).mapIso (A.objPullbackIso g k)).trans
        (stackPullbackCompIso X m g (A.obj T k)) =
      (A.objPullbackIso m (g ≫ k)).symm.trans
        ((A.objIsoOfEq (Category.assoc m g k).symm).trans (A.objPullbackIso (m ≫ g) k)) := by
  apply Iso.ext
  have h := congrArg Iso.hom (A.mapIso_objPullbackIso_comp g k m)
  simp only [Iso.trans_hom, Category.assoc] at h
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The morphism-level (`.hom`) form of `mapIso_objPullbackIso`, solved for the pulled-back
naturality map alone. -/
theorem objPullbackIso_mapIso_hom {U T S : Scheme.{u}} (g : U ⟶ T) (k : T ⟶ A.scheme)
    (m : S ⟶ U) :
    (stackPullback X m).map (A.objPullbackIso g k).hom =
      (A.objPullbackIso m (g ≫ k)).inv ≫ (A.objIsoOfEq (Category.assoc m g k).symm).hom ≫
        (A.objPullbackIso (m ≫ g) k).hom ≫ (stackPullbackCompIso X m g (A.obj T k)).inv := by
  have h := congrArg Iso.hom (A.mapIso_objPullbackIso g k m)
  simp only [Iso.trans_hom, Iso.symm_hom] at h
  rw [← cancel_mono (stackPullbackCompIso X m g (A.obj T k)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h

/-- The morphism-level (`.inv`) counterpart of `objPullbackIso_mapIso_hom`. -/
theorem objPullbackIso_mapIso_inv {U T S : Scheme.{u}} (g : U ⟶ T) (k : T ⟶ A.scheme)
    (m : S ⟶ U) :
    (stackPullback X m).map (A.objPullbackIso g k).inv =
      (stackPullbackCompIso X m g (A.obj T k)).hom ≫ (A.objPullbackIso (m ≫ g) k).inv ≫
        (A.objIsoOfEq (Category.assoc m g k).symm).inv ≫ (A.objPullbackIso m (g ≫ k)).hom := by
  rw [← cancel_epi ((stackPullback X m).map (A.objPullbackIso g k).hom)]
  rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    A.objPullbackIso_mapIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- `objIsoOfEq` telescopes along a chain of equalities. -/
theorem objIsoOfEq_trans {V : Scheme.{u}} {f g h : V ⟶ A.scheme} (h1 : f = g) (h2 : g = h) :
    (A.objIsoOfEq h1).trans (A.objIsoOfEq h2) = A.objIsoOfEq (h1.trans h2) := by
  subst h1; subst h2; simp [objIsoOfEq]

/-- `objIsoOfEq` commutes with taking the reverse equality. -/
theorem objIsoOfEq_symm {V : Scheme.{u}} {f g : V ⟶ A.scheme} (h : f = g) :
    (A.objIsoOfEq h).symm = A.objIsoOfEq h.symm := by
  subst h; simp [objIsoOfEq]

/-- The `.inv` of `objIsoOfEq` is the `.hom` of the reversed equality. -/
theorem objIsoOfEq_inv_eq_symm_hom {V : Scheme.{u}} {f g : V ⟶ A.scheme} (h : f = g) :
    (A.objIsoOfEq h).inv = (A.objIsoOfEq h.symm).hom :=
  congrArg Iso.hom (A.objIsoOfEq_symm h)

/-- `objIsoOfEq` telescopes at the morphism level. -/
theorem objIsoOfEq_trans_hom {V : Scheme.{u}} {f g h : V ⟶ A.scheme} (h1 : f = g) (h2 : g = h) :
    (A.objIsoOfEq h1).hom ≫ (A.objIsoOfEq h2).hom = (A.objIsoOfEq (h1.trans h2)).hom :=
  congrArg Iso.hom (A.objIsoOfEq_trans h1 h2)

/-- **Naturality of `stackPullbackCompIso`** in the underlying object of the fibre. -/
theorem stackPullbackCompIso_naturality {R S T : Scheme.{u}} (g : R ⟶ S) (f : S ⟶ T)
    {x y : StackFiber X T} (k : x ⟶ y) :
    (stackPullback X g).map ((stackPullback X f).map k) ≫ (stackPullbackCompIso X g f y).hom =
      (stackPullbackCompIso X g f x).hom ≫ (stackPullback X (g ≫ f)).map k :=
  (Cat.Hom.toNatIso (X.toPseudofunctor.mapComp ⟨f.op⟩ ⟨g.op⟩)).symm.hom.naturality k

/-- Associativity-friendly form of `stackPullbackCompIso_naturality`. -/
theorem stackPullbackCompIso_naturality_assoc {R S T : Scheme.{u}} (g : R ⟶ S) (f : S ⟶ T)
    {x y : StackFiber X T} (k : x ⟶ y) {W : StackFiber X R}
    (w : (stackPullback X (g ≫ f)).obj y ⟶ W) :
    (stackPullback X g).map ((stackPullback X f).map k) ≫
        (stackPullbackCompIso X g f y).hom ≫ w =
      (stackPullbackCompIso X g f x).hom ≫ (stackPullback X (g ≫ f)).map k ≫ w := by
  rw [← Category.assoc, stackPullbackCompIso_naturality, Category.assoc]

/-- `stackPullbackCompIso_naturality_assoc` with the leading `stackPullbackCompIso`-inverse
cancelled against its own naturality square. -/
theorem stackPullbackCompIso_naturality_left_inv_assoc {R S T : Scheme.{u}} (g : R ⟶ S)
    (f : S ⟶ T) {x y : StackFiber X T} (k : x ⟶ y) {W : StackFiber X R}
    (w : (stackPullback X (g ≫ f)).obj y ⟶ W) :
    (stackPullbackCompIso X g f x).inv ≫ (stackPullback X g).map ((stackPullback X f).map k) ≫
        (stackPullbackCompIso X g f y).hom ≫ w =
      (stackPullback X (g ≫ f)).map k ≫ w := by
  rw [stackPullbackCompIso_naturality_assoc, Iso.inv_hom_id_assoc]

/-- Associativity-friendly form of `objIsoOfEq_trans_hom`. -/
theorem objIsoOfEq_trans_hom_assoc {V : Scheme.{u}} {f g h : V ⟶ A.scheme} (h1 : f = g)
    (h2 : g = h) {W : StackFiber X V} (k : A.obj V h ⟶ W) :
    (A.objIsoOfEq h1).hom ≫ (A.objIsoOfEq h2).hom ≫ k =
      (A.objIsoOfEq (h1.trans h2)).hom ≫ k := by
  rw [← Category.assoc, A.objIsoOfEq_trans_hom]

/-- **`objIsoOfEq` is compatible with a further test-scheme pullback.** -/
theorem objIsoOfEq_pullback {V V' : Scheme.{u}} {r s : V ⟶ A.scheme} (h : r = s) (m : V' ⟶ V) :
    (A.objPullbackIso m r).trans
        (((stackPullback X m).mapIso (A.objIsoOfEq h)).trans (A.objPullbackIso m s).symm) =
      A.objIsoOfEq (congrArg (m ≫ ·) h) := by
  subst h
  simp [objIsoOfEq]

/-- The morphism-level, associativity-friendly form of `objIsoOfEq_pullback`, matchable as a
rewrite regardless of what follows in a longer composite. -/
theorem objIsoOfEq_pullback_hom_assoc {V V' : Scheme.{u}} {r s : V ⟶ A.scheme} (h : r = s)
    (m : V' ⟶ V) {W : StackFiber X V'} (f : A.obj V' (m ≫ s) ⟶ W) :
    (A.objPullbackIso m r).hom ≫ (stackPullback X m).map (A.objIsoOfEq h).hom ≫
        (A.objPullbackIso m s).inv ≫ f =
      (A.objIsoOfEq (congrArg (m ≫ ·) h)).hom ≫ f := by
  have h' := congrArg Iso.hom (A.objIsoOfEq_pullback h m)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at h'
  calc (A.objPullbackIso m r).hom ≫ (stackPullback X m).map (A.objIsoOfEq h).hom ≫
        (A.objPullbackIso m s).inv ≫ f
      = ((A.objPullbackIso m r).hom ≫ (stackPullback X m).map (A.objIsoOfEq h).hom ≫
          (A.objPullbackIso m s).inv) ≫ f := by simp only [Category.assoc]
    _ = (A.objIsoOfEq (congrArg (m ≫ ·) h)).hom ≫ f := by rw [h']

/-! ## The self-overlap of a chart, as an honest scheme -/

/-- The tautological object of a chart over its own scheme. -/
noncomputable abbrev tautObj : StackFiber X A.scheme := A.obj A.scheme (𝟙 A.scheme)

variable (hA : A.IsRepresentable)

/-- **The self-overlap of a representable chart, represented by an honest scheme.**
Applying representability to the chart's own tautological object gives a scheme whose two
projections to `A.scheme` are both `A.scheme`-valued; for an étale surjective chart the first
one is étale surjective (`selfOverlapScheme_fst_prop`). -/
noncomputable def selfOverlapScheme : A.PullbackPresentation A.scheme A.tautObj :=
  (hA.1 A.scheme A.tautObj).some

/-- The first projection of the self-overlap scheme of an étale surjective chart is étale and
surjective. -/
theorem selfOverlapScheme_fst_prop (hAe : A.IsEtaleSurjective) :
    (_root_.AlgebraicGeometry.Etale ⊓ _root_.AlgebraicGeometry.Surjective)
      (A.selfOverlapScheme hA).fst :=
  hAe.2 A.scheme A.tautObj (A.selfOverlapScheme hA)

/-- The first projection of the self-overlap scheme of an étale surjective chart is
unramified. -/
theorem selfOverlapScheme_fst_unramified (hAe : A.IsEtaleSurjective) :
    Unramified (A.selfOverlapScheme hA).fst := by
  have he : _root_.AlgebraicGeometry.Etale (A.selfOverlapScheme hA).fst :=
    (A.selfOverlapScheme_fst_prop hA hAe).1
  exact unramified_of_etale _

/-- The canonical isomorphism between the chart objects at the two self-overlap projections. -/
noncomputable def selfOverlapScheme_baseIso :
    A.obj (A.selfOverlapScheme hA).space (A.selfOverlapScheme hA).fst ≅
      A.obj (A.selfOverlapScheme hA).space (A.selfOverlapScheme hA).snd :=
  (A.identityObjectPullbackComparison (A.selfOverlapScheme hA).fst).trans
    (A.selfOverlapScheme hA).comparison.symm

/-! ## The isomorphism scheme of a pair of chart objects -/

variable {S : Scheme.{u}} (a b : S ⟶ A.scheme)

/-- The pairing of two chart maps into the ordinary scheme product `A.scheme ⨯ A.scheme`. -/
noncomputable abbrev isomPair : S ⟶ A.scheme ⨯ A.scheme := prod.lift a b

/-- The pairing of the self-overlap scheme's two projections. -/
noncomputable abbrev selfOverlapPair :
    (A.selfOverlapScheme hA).space ⟶ A.scheme ⨯ A.scheme :=
  prod.lift (A.selfOverlapScheme hA).fst (A.selfOverlapScheme hA).snd

/-- **The isomorphism scheme of a pair of chart objects.**  The ordinary scheme pullback of the
pair `(a, b)` against the self-overlap pairing. -/
noncomputable abbrev isomScheme : Scheme.{u} :=
  pullback (A.isomPair a b) (A.selfOverlapPair hA)

/-- Structure map of the isomorphism scheme to the base. -/
noncomputable abbrev isomScheme_map : A.isomScheme hA a b ⟶ S :=
  pullback.fst (A.isomPair a b) (A.selfOverlapPair hA)

/-- Comparison map of the isomorphism scheme to the self-overlap scheme. -/
noncomputable abbrev isomScheme_toOverlap :
    A.isomScheme hA a b ⟶ (A.selfOverlapScheme hA).space :=
  pullback.snd (A.isomPair a b) (A.selfOverlapPair hA)

theorem isomScheme_condition :
    A.isomScheme_map hA a b ≫ A.isomPair a b =
      A.isomScheme_toOverlap hA a b ≫ A.selfOverlapPair hA :=
  pullback.condition

/-- The isomorphism scheme's structure map agrees with `a` after passing through the
self-overlap scheme's first leg. -/
theorem isomScheme_fst_eq :
    A.isomScheme_map hA a b ≫ a =
      A.isomScheme_toOverlap hA a b ≫ (A.selfOverlapScheme hA).fst := by
  have h := congrArg (fun q => q ≫ (Limits.prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme))
    (A.isomScheme_condition hA a b)
  simpa only [Category.assoc, isomPair, selfOverlapPair, prod.lift_fst] using h

/-- The isomorphism scheme's structure map agrees with `b` after passing through the
self-overlap scheme's second leg. -/
theorem isomScheme_snd_eq :
    A.isomScheme_map hA a b ≫ b =
      A.isomScheme_toOverlap hA a b ≫ (A.selfOverlapScheme hA).snd := by
  have h := congrArg (fun q => q ≫ (Limits.prod.snd : A.scheme ⨯ A.scheme ⟶ A.scheme))
    (A.isomScheme_condition hA a b)
  simpa only [Category.assoc, isomPair, selfOverlapPair, prod.lift_snd] using h

/-- **The comparison isomorphism attached to any pair of maps into the self-overlap scheme
matching `a`, `b`.**  Generalizes the universal isomorphism `isomScheme_universalIso`'s formula
to an arbitrary base map `p` and comparison map `q`; specializing `(p, q) :=
(isomScheme_map, isomScheme_toOverlap)` recovers it (`isomScheme_universalIso_eq`), and its
naturality under a further pullback is handled uniformly by `pairIso_pullback` below. -/
noncomputable def pairIso {V : Scheme.{u}} (p : V ⟶ S) (q : V ⟶ (A.selfOverlapScheme hA).space)
    (hp : p ≫ a = q ≫ (A.selfOverlapScheme hA).fst)
    (hq : p ≫ b = q ≫ (A.selfOverlapScheme hA).snd) :
    (stackPullback X p).obj (A.obj S a) ≅ (stackPullback X p).obj (A.obj S b) :=
  (A.objPullbackIso p a).symm
    |>.trans (A.objIsoOfEq hp)
    |>.trans (A.objPullbackIso q (A.selfOverlapScheme hA).fst)
    |>.trans ((stackPullback X q).mapIso (A.selfOverlapScheme_baseIso hA))
    |>.trans (A.objPullbackIso q (A.selfOverlapScheme hA).snd).symm
    |>.trans (A.objIsoOfEq hq.symm)
    |>.trans (A.objPullbackIso p b)

/-- **Naturality of `pairIso` under a further pullback.**  Pulling back the isomorphism
`pairIso p q hp hq` along `m` and correcting through `stackPullbackCompIso` recovers the
isomorphism `pairIso (m ≫ p) (m ≫ q) _ _` built directly at the composite maps. -/
theorem pairIso_pullback {V V' : Scheme.{u}} (p : V ⟶ S)
    (q : V ⟶ (A.selfOverlapScheme hA).space)
    (hp : p ≫ a = q ≫ (A.selfOverlapScheme hA).fst)
    (hq : p ≫ b = q ≫ (A.selfOverlapScheme hA).snd) (m : V' ⟶ V) :
    (stackPullbackCompIso X m p (A.obj S a)).symm.trans
        (((stackPullback X m).mapIso (A.pairIso hA a b p q hp hq)).trans
          (stackPullbackCompIso X m p (A.obj S b))) =
      A.pairIso hA a b (m ≫ p) (m ≫ q)
        (by rw [Category.assoc, hp, ← Category.assoc])
        (by rw [Category.assoc, hq, ← Category.assoc]) := by
  apply Iso.ext
  simp only [pairIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [A.objPullbackIso_mapIso_inv p a m,
    A.objPullbackIso_mapIso_hom q (A.selfOverlapScheme hA).fst m,
    A.objPullbackIso_mapIso_inv q (A.selfOverlapScheme hA).snd m,
    A.objPullbackIso_mapIso_hom p b m]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  congr 1
  rw [A.objIsoOfEq_pullback_hom_assoc hp m, A.objIsoOfEq_pullback_hom_assoc hq.symm m,
    A.objIsoOfEq_inv_eq_symm_hom, A.objIsoOfEq_inv_eq_symm_hom,
    A.objIsoOfEq_trans_hom_assoc, A.objIsoOfEq_trans_hom_assoc,
    A.objIsoOfEq_trans_hom_assoc, A.objIsoOfEq_trans_hom_assoc,
    stackPullbackCompIso_naturality_left_inv_assoc]

/-- **Reindexing `pairIso` along equalities of its scheme-map arguments.**  Correcting through
`stackPullbackObjIsoOfEq` on both sides transports `pairIso p q hp hq` to `pairIso p' q' hp'
hq'` whenever `p = p'` and `q = q'`; stated this way (rather than by substitution) it applies
uniformly even when `p`, `q` were built from data that depends on the very map being
identified. -/
theorem pairIso_reindex {V : Scheme.{u}} {p p' : V ⟶ S}
    {q q' : V ⟶ (A.selfOverlapScheme hA).space}
    (hp : p ≫ a = q ≫ (A.selfOverlapScheme hA).fst)
    (hq : p ≫ b = q ≫ (A.selfOverlapScheme hA).snd)
    (hp' : p' ≫ a = q' ≫ (A.selfOverlapScheme hA).fst)
    (hq' : p' ≫ b = q' ≫ (A.selfOverlapScheme hA).snd)
    (hpp' : p = p') (hqq' : q = q') :
    (stackPullbackObjIsoOfEq X hpp' (A.obj S a)).symm.trans
        ((A.pairIso hA a b p q hp hq).trans (stackPullbackObjIsoOfEq X hpp' (A.obj S b))) =
      A.pairIso hA a b p' q' hp' hq' := by
  subst hpp'
  subst hqq'
  apply Iso.ext
  simp only [stackPullbackObjIsoOfEq, Iso.trans_hom, Iso.refl_symm, Iso.refl_hom,
    Category.id_comp, Category.comp_id]

/-- **The universal isomorphism represented by the isomorphism scheme.** -/
noncomputable def isomScheme_universalIso :
    (stackPullback X (A.isomScheme_map hA a b)).obj (A.obj S a) ≅
      (stackPullback X (A.isomScheme_map hA a b)).obj (A.obj S b) :=
  A.pairIso hA a b (A.isomScheme_map hA a b) (A.isomScheme_toOverlap hA a b)
    (A.isomScheme_fst_eq hA a b) (A.isomScheme_snd_eq hA a b)

variable {S' : Scheme.{u}} (f : S' ⟶ S)
  (e : (stackPullback X f).obj (A.obj S a) ≅ (stackPullback X f).obj (A.obj S b))

/-- The comparison isomorphism a test map and comparison induce for the self-overlap scheme. -/
noncomputable def isomScheme_lift_comparison :
    A.obj S' (f ≫ b) ≅ (stackPullback X (f ≫ a)).obj A.tautObj :=
  (A.objPullbackIso f b)
    |>.trans e.symm
    |>.trans (A.objPullbackIso f a).symm
    |>.trans (A.identityObjectPullbackComparison (f ≫ a))

/-- The induced map from the test scheme into the self-overlap scheme. -/
noncomputable def isomScheme_lift_toOverlap : S' ⟶ (A.selfOverlapScheme hA).space :=
  (A.selfOverlapScheme hA).lift (f ≫ a) (f ≫ b) (A.isomScheme_lift_comparison a b f e)

theorem isomScheme_lift_toOverlap_fst :
    A.isomScheme_lift_toOverlap hA a b f e ≫ (A.selfOverlapScheme hA).fst = f ≫ a :=
  (A.selfOverlapScheme hA).lift_fst _ _ _

theorem isomScheme_lift_toOverlap_snd :
    A.isomScheme_lift_toOverlap hA a b f e ≫ (A.selfOverlapScheme hA).snd = f ≫ b :=
  (A.selfOverlapScheme hA).lift_snd _ _ _

theorem isomScheme_lift_condition :
    f ≫ A.isomPair a b = A.isomScheme_lift_toOverlap hA a b f e ≫ A.selfOverlapPair hA := by
  apply prod.hom_ext
  · simp only [isomPair, selfOverlapPair, Category.assoc, prod.lift_fst,
      A.isomScheme_lift_toOverlap_fst hA a b f e]
  · simp only [isomPair, selfOverlapPair, Category.assoc, prod.lift_snd,
      A.isomScheme_lift_toOverlap_snd hA a b f e]

/-- **Universal lift into the isomorphism scheme.** -/
noncomputable def isomScheme_lift : S' ⟶ A.isomScheme hA a b :=
  pullback.lift f (A.isomScheme_lift_toOverlap hA a b f e) (A.isomScheme_lift_condition hA a b f e)

theorem isomScheme_lift_map :
    A.isomScheme_lift hA a b f e ≫ A.isomScheme_map hA a b = f :=
  pullback.lift_fst _ _ _

theorem isomScheme_lift_toOverlap_eq :
    A.isomScheme_lift hA a b f e ≫ A.isomScheme_toOverlap hA a b =
      A.isomScheme_lift_toOverlap hA a b f e :=
  pullback.lift_snd _ _ _

/-- `identityObjectPullbackComparison` transported along an equality of the underlying map. -/
theorem identityObjectPullbackComparison_congr {V : Scheme.{u}} {k1 k2 : V ⟶ A.scheme}
    (h : k1 = k2) :
    (A.objIsoOfEq h).symm.trans
        ((A.identityObjectPullbackComparison k1).trans (stackPullbackObjIsoOfEq X h A.tautObj)) =
      A.identityObjectPullbackComparison k2 := by
  subst h
  simp [objIsoOfEq, stackPullbackObjIsoOfEq]

/-- `inducedComparison` unfolds to `objPullbackIso`/`mapIso`/`stackPullbackCompIso`. -/
theorem inducedComparison_eq {T U : Scheme.{u}} (fst : U ⟶ T) (snd : U ⟶ A.scheme)
    {x : StackFiber X T} (universal : A.obj U snd ≅ (stackPullback X fst).obj x)
    {S'' : Scheme.{u}} (m : S'' ⟶ U) :
    A.inducedComparison fst snd universal m =
      ((A.objPullbackIso m snd).trans ((stackPullback X m).mapIso universal)).trans
        (stackPullbackCompIso X m fst x) := rfl

/-- **Base case for the isomorphism scheme's universal isomorphism.**  Evaluated at the very
test map `f` and comparison `e` used to construct the lift, `pairIso` recovers `e` itself. -/
theorem pairIso_base :
    A.pairIso hA a b f (A.isomScheme_lift_toOverlap hA a b f e)
      (A.isomScheme_lift_toOverlap_fst hA a b f e).symm
      (A.isomScheme_lift_toOverlap_snd hA a b f e).symm = e := by
  obtain ⟨fst_eq, snd_eq, heq0⟩ := (A.selfOverlapScheme hA).lift_compatible (f ≫ a) (f ≫ b)
    (A.isomScheme_lift_comparison a b f e)
  have heq : (A.objIsoOfEq (A.isomScheme_lift_toOverlap_snd hA a b f e)).symm.trans
      ((A.inducedComparison (A.selfOverlapScheme hA).fst (A.selfOverlapScheme hA).snd
          (A.selfOverlapScheme hA).comparison (A.isomScheme_lift_toOverlap hA a b f e)).trans
        (stackPullbackObjIsoOfEq X (A.isomScheme_lift_toOverlap_fst hA a b f e) A.tautObj)) =
      A.isomScheme_lift_comparison a b f e := by exact heq0
  have heq' := congrArg Iso.hom heq
  simp only [inducedComparison_eq, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc] at heq'
  have hcomp_hom : (stackPullback X (A.isomScheme_lift_toOverlap hA a b f e)).map
      (A.selfOverlapScheme hA).comparison.hom =
      (A.objPullbackIso (A.isomScheme_lift_toOverlap hA a b f e)
          (A.selfOverlapScheme hA).snd).inv ≫
        (A.objIsoOfEq (A.isomScheme_lift_toOverlap_snd hA a b f e)).hom ≫
        (A.isomScheme_lift_comparison a b f e).hom ≫
        (stackPullbackObjIsoOfEq X (A.isomScheme_lift_toOverlap_fst hA a b f e) A.tautObj).inv ≫
        (stackPullbackCompIso X (A.isomScheme_lift_toOverlap hA a b f e)
          (A.selfOverlapScheme hA).fst A.tautObj).inv := by
    rw [← cancel_epi ((A.objIsoOfEq (A.isomScheme_lift_toOverlap_snd hA a b f e)).inv ≫
        (A.objPullbackIso (A.isomScheme_lift_toOverlap hA a b f e)
          (A.selfOverlapScheme hA).snd).hom)]
    rw [← cancel_mono ((stackPullbackCompIso X (A.isomScheme_lift_toOverlap hA a b f e)
        (A.selfOverlapScheme hA).fst A.tautObj).hom ≫
        (stackPullbackObjIsoOfEq X (A.isomScheme_lift_toOverlap_fst hA a b f e)
          A.tautObj).hom)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    rw [← heq']
  have hcomp_inv : (stackPullback X (A.isomScheme_lift_toOverlap hA a b f e)).map
      (A.selfOverlapScheme hA).comparison.inv =
      (stackPullbackCompIso X (A.isomScheme_lift_toOverlap hA a b f e)
          (A.selfOverlapScheme hA).fst A.tautObj).hom ≫
        (stackPullbackObjIsoOfEq X (A.isomScheme_lift_toOverlap_fst hA a b f e) A.tautObj).hom ≫
        (A.isomScheme_lift_comparison a b f e).inv ≫
        (A.objIsoOfEq (A.isomScheme_lift_toOverlap_snd hA a b f e)).inv ≫
        (A.objPullbackIso (A.isomScheme_lift_toOverlap hA a b f e)
          (A.selfOverlapScheme hA).snd).hom := by
    rw [← cancel_epi ((stackPullback X (A.isomScheme_lift_toOverlap hA a b f e)).map
        (A.selfOverlapScheme hA).comparison.hom)]
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      hcomp_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  apply Iso.ext
  simp only [pairIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    selfOverlapScheme_baseIso, Functor.map_comp, Category.assoc, hcomp_inv]
  simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  have hpieces : ∀ {W : StackFiber X S'}
      (w : (stackPullback X
        (A.isomScheme_lift_toOverlap hA a b f e ≫ (A.selfOverlapScheme hA).fst)).obj
          A.tautObj ⟶ W),
      (A.objPullbackIso (A.isomScheme_lift_toOverlap hA a b f e)
          (A.selfOverlapScheme hA).fst).hom ≫
        (stackPullback X (A.isomScheme_lift_toOverlap hA a b f e)).map
            (A.identityObjectPullbackComparison (A.selfOverlapScheme hA).fst).hom ≫
          (stackPullbackCompIso X (A.isomScheme_lift_toOverlap hA a b f e)
            (A.selfOverlapScheme hA).fst A.tautObj).hom ≫ w =
        (A.identityObjectPullbackComparison
          (A.isomScheme_lift_toOverlap hA a b f e ≫ (A.selfOverlapScheme hA).fst)).hom ≫ w := by
    intro W w
    have h := congrArg Iso.hom (A.inducedComparison_identityObjectPullbackComparison
      (A.selfOverlapScheme hA).fst (A.isomScheme_lift_toOverlap hA a b f e))
    simp only [inducedComparison_eq, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] at h
    calc (A.objPullbackIso (A.isomScheme_lift_toOverlap hA a b f e)
            (A.selfOverlapScheme hA).fst).hom ≫
          (stackPullback X (A.isomScheme_lift_toOverlap hA a b f e)).map
              (A.identityObjectPullbackComparison (A.selfOverlapScheme hA).fst).hom ≫
            (stackPullbackCompIso X (A.isomScheme_lift_toOverlap hA a b f e)
              (A.selfOverlapScheme hA).fst A.tautObj).hom ≫ w
        = ((A.objPullbackIso (A.isomScheme_lift_toOverlap hA a b f e)
              (A.selfOverlapScheme hA).fst).hom ≫
            (stackPullback X (A.isomScheme_lift_toOverlap hA a b f e)).map
                (A.identityObjectPullbackComparison (A.selfOverlapScheme hA).fst).hom ≫
              (stackPullbackCompIso X (A.isomScheme_lift_toOverlap hA a b f e)
                (A.selfOverlapScheme hA).fst A.tautObj).hom) ≫ w := by simp only [Category.assoc]
      _ = (A.identityObjectPullbackComparison
            (A.isomScheme_lift_toOverlap hA a b f e ≫ (A.selfOverlapScheme hA).fst)).hom ≫ w := by
          rw [h]
  have hcongr : ∀ {W : StackFiber X S'} (w : (stackPullback X (f ≫ a)).obj A.tautObj ⟶ W),
      (A.objIsoOfEq (A.isomScheme_lift_toOverlap_fst hA a b f e).symm).hom ≫
        (A.identityObjectPullbackComparison
            (A.isomScheme_lift_toOverlap hA a b f e ≫ (A.selfOverlapScheme hA).fst)).hom ≫
          (stackPullbackObjIsoOfEq X (A.isomScheme_lift_toOverlap_fst hA a b f e)
            A.tautObj).hom ≫ w =
        (A.identityObjectPullbackComparison (f ≫ a)).hom ≫ w := by
    intro W w
    have h := congrArg Iso.hom (A.identityObjectPullbackComparison_congr
      (A.isomScheme_lift_toOverlap_fst hA a b f e))
    simp only [Iso.trans_hom, Iso.symm_hom] at h
    rw [← A.objIsoOfEq_inv_eq_symm_hom (A.isomScheme_lift_toOverlap_fst hA a b f e)]
    calc (A.objIsoOfEq (A.isomScheme_lift_toOverlap_fst hA a b f e)).inv ≫
          (A.identityObjectPullbackComparison
              (A.isomScheme_lift_toOverlap hA a b f e ≫ (A.selfOverlapScheme hA).fst)).hom ≫
            (stackPullbackObjIsoOfEq X (A.isomScheme_lift_toOverlap_fst hA a b f e)
              A.tautObj).hom ≫ w
        = ((A.objIsoOfEq (A.isomScheme_lift_toOverlap_fst hA a b f e)).inv ≫
            (A.identityObjectPullbackComparison
                (A.isomScheme_lift_toOverlap hA a b f e ≫ (A.selfOverlapScheme hA).fst)).hom ≫
              (stackPullbackObjIsoOfEq X (A.isomScheme_lift_toOverlap_fst hA a b f e)
                A.tautObj).hom) ≫ w := by simp only [Category.assoc]
      _ = (A.identityObjectPullbackComparison (f ≫ a)).hom ≫ w := by rw [h]
  rw [hpieces, hcongr]
  simp only [isomScheme_lift_comparison, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- **General (unconditional) classification identity.**  For any candidate `k` matching `a`,
`b` after composing with `f`, the self-overlap's own classifying equation at `k` computes
exactly `isomScheme_lift_comparison` evaluated at `pairIso hA a b f k _ _`.  This is the
identity underlying both `pairIso_base` and the uniqueness direction
`isomScheme_lift_eq_of_classifies`. -/
theorem pairIso_classifies {k : S' ⟶ (A.selfOverlapScheme hA).space}
    (fst_eq : k ≫ (A.selfOverlapScheme hA).fst = f ≫ a)
    (snd_eq : k ≫ (A.selfOverlapScheme hA).snd = f ≫ b) :
    (A.objIsoOfEq snd_eq).symm.trans
        ((A.inducedComparison (A.selfOverlapScheme hA).fst (A.selfOverlapScheme hA).snd
            (A.selfOverlapScheme hA).comparison k).trans
          (stackPullbackObjIsoOfEq X fst_eq A.tautObj)) =
      A.isomScheme_lift_comparison a b f
        (A.pairIso hA a b f k fst_eq.symm snd_eq.symm) := by
  have hPcomp : (A.selfOverlapScheme hA).comparison =
      (A.selfOverlapScheme_baseIso hA).symm.trans
        (A.identityObjectPullbackComparison (A.selfOverlapScheme hA).fst) := by
    apply Iso.ext
    simp [selfOverlapScheme_baseIso]
  have hcomp_hom : (stackPullback X k).map (A.selfOverlapScheme hA).comparison.hom =
      (stackPullback X k).map (A.selfOverlapScheme_baseIso hA).inv ≫
        (stackPullback X k).map (A.identityObjectPullbackComparison
          (A.selfOverlapScheme hA).fst).hom := by
    rw [hPcomp]
    simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.map_comp]
  have hpieces : ∀ {W : StackFiber X S'}
      (w : (stackPullback X (k ≫ (A.selfOverlapScheme hA).fst)).obj A.tautObj ⟶ W),
      (stackPullback X k).map
            (A.identityObjectPullbackComparison (A.selfOverlapScheme hA).fst).hom ≫
          (stackPullbackCompIso X k (A.selfOverlapScheme hA).fst A.tautObj).hom ≫ w =
        (A.objPullbackIso k (A.selfOverlapScheme hA).fst).inv ≫
          (A.identityObjectPullbackComparison (k ≫ (A.selfOverlapScheme hA).fst)).hom ≫ w := by
    intro W w
    have h := congrArg Iso.hom (A.inducedComparison_identityObjectPullbackComparison
      (A.selfOverlapScheme hA).fst k)
    simp only [inducedComparison_eq, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] at h
    rw [← cancel_epi (A.objPullbackIso k (A.selfOverlapScheme hA).fst).hom]
    calc (A.objPullbackIso k (A.selfOverlapScheme hA).fst).hom ≫
          ((stackPullback X k).map
              (A.identityObjectPullbackComparison (A.selfOverlapScheme hA).fst).hom ≫
            (stackPullbackCompIso X k (A.selfOverlapScheme hA).fst A.tautObj).hom ≫ w)
        = ((A.objPullbackIso k (A.selfOverlapScheme hA).fst).hom ≫
            (stackPullback X k).map
                (A.identityObjectPullbackComparison (A.selfOverlapScheme hA).fst).hom ≫
              (stackPullbackCompIso X k (A.selfOverlapScheme hA).fst A.tautObj).hom) ≫ w := by
            simp only [Category.assoc]
      _ = (A.identityObjectPullbackComparison (k ≫ (A.selfOverlapScheme hA).fst)).hom ≫ w := by
          rw [h]
      _ = (A.objPullbackIso k (A.selfOverlapScheme hA).fst).hom ≫
            ((A.objPullbackIso k (A.selfOverlapScheme hA).fst).inv ≫
              (A.identityObjectPullbackComparison (k ≫ (A.selfOverlapScheme hA).fst)).hom ≫
                w) := by
          simp only [Iso.hom_inv_id_assoc]
  have hcongr :
      (A.identityObjectPullbackComparison (k ≫ (A.selfOverlapScheme hA).fst)).hom ≫
          (stackPullbackObjIsoOfEq X fst_eq A.tautObj).hom =
        (A.objIsoOfEq fst_eq.symm).inv ≫ (A.identityObjectPullbackComparison (f ≫ a)).hom := by
    have h := congrArg Iso.hom (A.identityObjectPullbackComparison_congr fst_eq)
    simp only [Iso.trans_hom, Iso.symm_hom] at h
    have hsymm : (A.objIsoOfEq fst_eq.symm).inv = (A.objIsoOfEq fst_eq).hom :=
      (congrArg Iso.inv (A.objIsoOfEq_symm fst_eq)).symm
    rw [hsymm]
    calc (A.identityObjectPullbackComparison (k ≫ (A.selfOverlapScheme hA).fst)).hom ≫
          (stackPullbackObjIsoOfEq X fst_eq A.tautObj).hom
        = (A.objIsoOfEq fst_eq).hom ≫ (A.objIsoOfEq fst_eq).inv ≫
            (A.identityObjectPullbackComparison (k ≫ (A.selfOverlapScheme hA).fst)).hom ≫
              (stackPullbackObjIsoOfEq X fst_eq A.tautObj).hom := by
            simp only [Iso.hom_inv_id_assoc]
      _ = (A.objIsoOfEq fst_eq).hom ≫
            ((A.objIsoOfEq fst_eq).inv ≫
              (A.identityObjectPullbackComparison (k ≫ (A.selfOverlapScheme hA).fst)).hom ≫
                (stackPullbackObjIsoOfEq X fst_eq A.tautObj).hom) := rfl
      _ = (A.objIsoOfEq fst_eq).hom ≫ (A.identityObjectPullbackComparison (f ≫ a)).hom := by
          rw [h]
  apply Iso.ext
  simp only [inducedComparison_eq, isomScheme_lift_comparison, pairIso, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    hcomp_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [hpieces, hcongr]

/-- **`stackDiagonal X` is classified, at the isomorphism scheme's own universal lift, by
`e`.** The scheme-level content of `DiagonalPresentation.lift_compatible`. -/
theorem isomScheme_lift_compatible :
    DiagonalClassifies X (A.isomScheme_map hA a b) (A.isomScheme_universalIso hA a b) f e
      (A.isomScheme_lift hA a b f e) := by
  refine ⟨A.isomScheme_lift_map hA a b f e, ?_⟩
  change (stackPullbackObjIsoOfEq X (A.isomScheme_lift_map hA a b f e) (A.obj S a)).symm.trans
      ((stackPullbackIso X (A.isomScheme_lift hA a b f e) (A.isomScheme_map hA a b)
          (A.isomScheme_universalIso hA a b)).trans
        (stackPullbackObjIsoOfEq X (A.isomScheme_lift_map hA a b f e) (A.obj S b))) = e
  rw [show stackPullbackIso X (A.isomScheme_lift hA a b f e) (A.isomScheme_map hA a b)
        (A.isomScheme_universalIso hA a b) =
      (stackPullbackCompIso X (A.isomScheme_lift hA a b f e) (A.isomScheme_map hA a b)
          (A.obj S a)).symm.trans
        (((stackPullback X (A.isomScheme_lift hA a b f e)).mapIso
            (A.isomScheme_universalIso hA a b)).trans
          (stackPullbackCompIso X (A.isomScheme_lift hA a b f e) (A.isomScheme_map hA a b)
            (A.obj S b))) from Iso.trans_assoc _ _ _]
  rw [isomScheme_universalIso,
    A.pairIso_pullback hA a b (A.isomScheme_map hA a b) (A.isomScheme_toOverlap hA a b)
      (A.isomScheme_fst_eq hA a b) (A.isomScheme_snd_eq hA a b) (A.isomScheme_lift hA a b f e),
    A.pairIso_reindex hA a b (hp := _) (hq := _)
      (hp' := (A.isomScheme_lift_toOverlap_fst hA a b f e).symm)
      (hq' := (A.isomScheme_lift_toOverlap_snd hA a b f e).symm)
      (A.isomScheme_lift_map hA a b f e) (A.isomScheme_lift_toOverlap_eq hA a b f e)]
  exact A.pairIso_base hA a b f e

/-- **`DiagonalPresentation.lift_unique`, transported to the scheme-level content.**  Any
competitor classifying the same data agrees with the universal lift after checking equality of
its two legs. -/
theorem isomScheme_lift_eq_of_classifies (g : S' ⟶ A.isomScheme hA a b)
    (compatible : DiagonalClassifies X (A.isomScheme_map hA a b)
      (A.isomScheme_universalIso hA a b) f e g) :
    g = A.isomScheme_lift hA a b f e := by
  obtain ⟨map_eq, hg⟩ := compatible
  have hfst2 : (g ≫ A.isomScheme_toOverlap hA a b) ≫ (A.selfOverlapScheme hA).fst = f ≫ a := by
    rw [Category.assoc, ← A.isomScheme_fst_eq hA a b, ← Category.assoc, map_eq]
  have hsnd2 : (g ≫ A.isomScheme_toOverlap hA a b) ≫ (A.selfOverlapScheme hA).snd = f ≫ b := by
    rw [Category.assoc, ← A.isomScheme_snd_eq hA a b, ← Category.assoc, map_eq]
  have hpk : A.pairIso hA a b f (g ≫ A.isomScheme_toOverlap hA a b) hfst2.symm hsnd2.symm = e := by
    have hg' := hg
    rw [show diagonalInducedIso X (A.isomScheme_map hA a b) (A.isomScheme_universalIso hA a b)
          g = (stackPullbackCompIso X g (A.isomScheme_map hA a b) (A.obj S a)).symm.trans
            (((stackPullback X g).mapIso (A.isomScheme_universalIso hA a b)).trans
              (stackPullbackCompIso X g (A.isomScheme_map hA a b) (A.obj S b)))
        from Iso.trans_assoc _ _ _] at hg'
    rw [isomScheme_universalIso,
      A.pairIso_pullback hA a b (A.isomScheme_map hA a b) (A.isomScheme_toOverlap hA a b)
        (A.isomScheme_fst_eq hA a b) (A.isomScheme_snd_eq hA a b) g,
      A.pairIso_reindex hA a b (hp := _) (hq := _) (hp' := hfst2.symm) (hq' := hsnd2.symm)
        map_eq rfl] at hg'
    exact hg'
  have htoOverlap : A.Classifies (A.selfOverlapScheme hA).fst (A.selfOverlapScheme hA).snd
      (A.selfOverlapScheme hA).comparison (f ≫ a) (f ≫ b)
      (A.isomScheme_lift_comparison a b f e) (g ≫ A.isomScheme_toOverlap hA a b) :=
    ⟨hfst2, hsnd2, hpk ▸ A.pairIso_classifies hA a b f hfst2 hsnd2⟩
  apply pullback.hom_ext
  · rw [map_eq, A.isomScheme_lift_map]
  · rw [(A.selfOverlapScheme hA).lift_unique (f ≫ a) (f ≫ b)
      (A.isomScheme_lift_comparison a b f e) (g ≫ A.isomScheme_toOverlap hA a b) htoOverlap,
      A.isomScheme_lift_toOverlap_eq]
    rfl

/-- **The isomorphism scheme, packaged as a `DiagonalPresentation` of `stackDiagonal X`.** -/
noncomputable def isomDiagonalPresentation : DiagonalPresentation X S (A.obj S a) (A.obj S b) where
  space := A.isomScheme hA a b
  map := A.isomScheme_map hA a b
  universalIso := A.isomScheme_universalIso hA a b
  lift f e := A.isomScheme_lift hA a b f e
  lift_map f e := A.isomScheme_lift_map hA a b f e
  lift_compatible f e := A.isomScheme_lift_compatible hA a b f e
  lift_unique f e g h := A.isomScheme_lift_eq_of_classifies hA a b f e g h

/-- The pairing of the self-overlap scheme's two projections is unramified: its postcomposition
with the first product projection is the (étale, hence unramified) first leg of the
self-overlap scheme. -/
theorem selfOverlapPair_unramified (hAe : A.IsEtaleSurjective) :
    Unramified (A.selfOverlapPair hA) := by
  have h : A.selfOverlapPair hA ≫ (Limits.prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme) =
      (A.selfOverlapScheme hA).fst := prod.lift_fst _ _
  have hfst : Unramified (A.selfOverlapScheme hA).fst :=
    A.selfOverlapScheme_fst_unramified hA hAe
  have : Unramified (A.selfOverlapPair hA ≫ (Limits.prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme)) :=
    h ▸ hfst
  exact Unramified.of_comp (A.selfOverlapPair hA)
    (Limits.prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme)

/-- **The structure map of the isomorphism scheme is unramified.**  It is a base change of the
unramified pairing `selfOverlapPair`. -/
theorem isomScheme_map_unramified (hAe : A.IsEtaleSurjective) :
    Unramified (A.isomScheme_map hA a b) := by
  have := A.selfOverlapPair_unramified hA hAe
  exact inferInstance

/-! ## The converse: an unramified diagonal makes the self-overlap pairing unramified -/

/-- The isomorphism scheme of the pair `(prod.fst, prod.snd)` over `A.scheme ⨯ A.scheme` is the
self-overlap scheme itself: its comparison map to the self-overlap is an isomorphism, because it
is a base change of the identity `prod.lift prod.fst prod.snd = 𝟙`. -/
theorem isIso_isomScheme_toOverlap_prod :
    IsIso (A.isomScheme_toOverlap hA (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme) prod.snd) := by
  have hid : A.isomPair (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme) prod.snd =
      𝟙 (A.scheme ⨯ A.scheme) := prod.lift_fst_snd
  have hsq := IsPullback.of_hasPullback
    (A.isomPair (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme) prod.snd) (A.selfOverlapPair hA)
  have : IsIso (A.isomPair (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme) prod.snd) := by
    rw [hid]; infer_instance
  exact hsq.isIso_snd_of_isIso

/-- The structure map of the isomorphism scheme of `(prod.fst, prod.snd)` factors as the
(invertible) comparison map followed by the self-overlap pairing. -/
theorem isomScheme_map_prod_eq :
    A.isomScheme_map hA (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme) prod.snd =
      A.isomScheme_toOverlap hA (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme) prod.snd ≫
        A.selfOverlapPair hA := by
  have h := A.isomScheme_condition hA (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme) prod.snd
  rw [show A.isomPair (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme) prod.snd =
    𝟙 (A.scheme ⨯ A.scheme) from prod.lift_fst_snd, Category.comp_id] at h
  exact h

/-- **The converse direction of the Deligne--Mumford diagonal criterion, at the level of the
self-overlap pairing.**  If the diagonal of `X` is representably unramified, then the pairing
`(P.fst, P.snd) : P.space ⟶ A.scheme ⨯ A.scheme` of the two projections of the self-overlap of
*any* representable chart `A` is unramified.

The proof identifies the self-overlap scheme with the isomorphism scheme of the pair
`(prod.fst, prod.snd)` over `A.scheme ⨯ A.scheme`, whose structure map is unramified because the
isomorphism scheme is a presentation of `stackDiagonal X` there
(`isomDiagonalPresentation`) and unramifiedness of the diagonal is independent of the chosen
presentation (`StackMorphismPresentation.property_iff_of_presentation`).  In contrast to
`selfOverlapPair_unramified` no étaleness of the chart is used. -/
theorem selfOverlapPair_unramified_of_stackDiagonal_unramified
    (h : (stackDiagonal X).Unramified) : Unramified (A.selfOverlapPair hA) := by
  have hrespects : MorphismProperty.RespectsIso (@Unramified : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨⟨q, hq⟩⟩ := (StackHom.hasRepresentableProperty_iff_raw
    (@Unramified : MorphismProperty Scheme.{u})).1 h (A.scheme ⨯ A.scheme)
    (selfProdObj (A.obj (A.scheme ⨯ A.scheme) prod.fst)
      (A.obj (A.scheme ⨯ A.scheme) prod.snd))
  have key : Unramified (A.isomScheme_map hA
      (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme) prod.snd) :=
    (q.property_iff_of_presentation (@Unramified : MorphismProperty Scheme.{u})
      (A.isomDiagonalPresentation hA (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme)
        prod.snd).toStackMorphismPresentation).1 hq
  rw [A.isomScheme_map_prod_eq hA] at key
  have := A.isIso_isomScheme_toOverlap_prod hA
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@Unramified : MorphismProperty Scheme.{u}) _ _).1 key

/-- **An étale surjective chart's isomorphism schemes are unramified over the base,
unconditionally.**  This removes the hypothesis `HasUnramifiedIsom` from
`stackDiagonal_unramified_of_etaleAtlas`. -/
theorem hasUnramifiedIsom_of_isEtaleSurjective (hAe : A.IsEtaleSurjective) :
    A.HasUnramifiedIsom := by
  intro S a b
  have hrep : A.IsRepresentable :=
    A.isRepresentable_of_hasRepresentableProperty _ hAe
  exact ⟨(A.isomDiagonalPresentation hrep a b).toStackMorphismPresentation,
    A.isomScheme_map_unramified hrep a b hAe⟩

end StackChart

/-- **The Deligne--Mumford diagonal criterion, unconditionally.**  Every Deligne--Mumford
stack has representably unramified diagonal: no hypothesis on the chart's isomorphism schemes
is needed, since it always holds for an étale surjective chart
(`StackChart.hasUnramifiedIsom_of_isEtaleSurjective`). -/
theorem DeligneMumfordStack.stackDiagonal_unramified' (Z : DeligneMumfordStack.{u}) :
    (stackDiagonal Z.toStack).Unramified :=
  Z.stackDiagonal_unramified_of_chartIsom (fun c hc => c.hasUnramifiedIsom_of_isEtaleSurjective hc)

/-- **The Deligne--Mumford diagonal criterion for a general algebraic stack with an étale
surjective chart.** -/
theorem AlgebraicStack.stackDiagonal_unramified_of_etaleChart (X : AlgebraicStack.{u})
    (A : StackChart X.toStack) (hA : A.IsEtaleSurjective) :
    (stackDiagonal X.toStack).Unramified :=
  stackDiagonal_unramified_of_etaleAtlas A hA X.stackDiagonal_isRepresentable
    (A.hasUnramifiedIsom_of_isEtaleSurjective hA)

end GromovWitten.AlgebraicGeometry
