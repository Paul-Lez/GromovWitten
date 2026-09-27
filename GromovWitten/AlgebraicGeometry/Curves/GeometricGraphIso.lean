/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.GeometricDualGraph

open CategoryTheory AlgebraicGeometry
open scoped Sym2

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X Y : Scheme.{u}} {K : Type u} [Field K]
  {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)}
  (e : X ≅ Y) (he : e.hom ≫ g = f)

private theorem component_mem_transport (C : Component X) (x : X) :
    e.hom x ∈ (irreducibleComponentsEquivOfSchemeIso e C : Set Y) ↔ x ∈ (C : Set X) := by
  rw [← mem_irreducibleComponentsEquivOfSchemeIso_symm]
  simp

include he in
theorem loopEdges_mem_iso (x : X) : e.hom x ∈ loopEdges g ↔ x ∈ loopEdges f := by
  have he' : e.inv ≫ f = g := by rw [← he]; simp
  constructor
  · rintro ⟨hx, hall⟩
    refine ⟨?_, ?_⟩
    · simpa using nodeSet_mem_of_iso e.symm he' hx
    · intro C D hC hD
      apply (irreducibleComponentsEquivOfSchemeIso e).injective
      exact hall _ _ ((component_mem_transport e C x).mpr hC)
        ((component_mem_transport e D x).mpr hD)
  · rintro ⟨hx, hall⟩
    refine ⟨nodeSet_mem_of_iso e he hx, ?_⟩
    intro C D hC hD
    let cv := irreducibleComponentsEquivOfSchemeIso e
    apply cv.symm.injective
    exact hall (cv.symm C) (cv.symm D) hC hD

def loopEdgesEquivOfIso : loopEdges f ≃ loopEdges g :=
  e.schemeIsoToHomeo.toEquiv.subtypeEquiv (fun x ↦ (loopEdges_mem_iso e he x).symm)

private def sym2Equiv {A B : Type*} (c : A ≃ B) : Sym2 A ≃ Sym2 B where
  toFun := Sym2.map c
  invFun := Sym2.map c.symm
  left_inv z := by
    induction z using Sym2.ind
    simp
  right_inv z := by
    induction z using Sym2.ind
    simp

private theorem multiEdges_mem_iso (x : X) (p : Sym2 (Component X)) :
    (e.hom x, Sym2.map (irreducibleComponentsEquivOfSchemeIso e) p) ∈
      multiEdges (X := Y) ↔ (x, p) ∈ multiEdges (X := X) := by
  let cv := irreducibleComponentsEquivOfSchemeIso e
  change (¬ (Sym2.map cv p).IsDiag ∧ _) ↔ (¬ p.IsDiag ∧ _)
  rw [Sym2.isDiag_map cv.injective]
  apply and_congr_right
  intro _
  constructor
  · intro h C hC
    exact (component_mem_transport e C x).mp
      (h (cv C) (Sym2.mem_map.mpr ⟨C, hC, rfl⟩))
  · intro h C hC
    obtain ⟨D, hD, rfl⟩ := Sym2.mem_map.mp hC
    exact (component_mem_transport e D x).mpr (h D hD)

def multiEdgesEquivOfIso : multiEdges (X := X) ≃ multiEdges (X := Y) :=
  (e.schemeIsoToHomeo.toEquiv.prodCongr
    (sym2Equiv (irreducibleComponentsEquivOfSchemeIso e))).subtypeEquiv
      (fun x ↦ (multiEdges_mem_iso e x.1 x.2).symm)

def edgesEquivOfIso : Edge f ≃ Edge g :=
  (loopEdgesEquivOfIso e he).sumCongr (multiEdgesEquivOfIso e)

@[simp] theorem edgePoint_edgesEquivOfIso (a : Edge f) :
    edgePoint g (edgesEquivOfIso e he a) = e.hom (edgePoint f a) := by
  cases a <;> rfl

theorem endpoints_edgesEquivOfIso (a : Edge f) :
    s(endpoint g (edgesEquivOfIso e he a) 0, endpoint g (edgesEquivOfIso e he a) 1) =
      s(irreducibleComponentsEquivOfSchemeIso e (endpoint f a 0),
        irreducibleComponentsEquivOfSchemeIso e (endpoint f a 1)) := by
  cases a with
  | inl a =>
    simp only [edgesEquivOfIso, Equiv.sumCongr_apply, endpoint_inl]
    have hh : componentOf (e.hom a.val) =
        irreducibleComponentsEquivOfSchemeIso e (componentOf a.val) := by
      apply (loopEdges_mem_iso e he a.val).mpr a.property |>.2
      · exact mem_componentOf _
      · exact (component_mem_transport e _ _).mpr (mem_componentOf _)
    change s(componentOf (e.hom a.val), componentOf (e.hom a.val)) = _
    rw [hh]
  | inr a =>
    change s(endpoint g (Sum.inr (multiEdgesEquivOfIso e a)) 0,
      endpoint g (Sum.inr (multiEdgesEquivOfIso e a)) 1) = _
    rw [endpoint_inr]
    change Sym2.map (irreducibleComponentsEquivOfSchemeIso e) a.val.2 = _
    rw [← endpoint_inr (f := f) a]
    rfl

end
end GromovWitten.AlgebraicGeometry.Curves
