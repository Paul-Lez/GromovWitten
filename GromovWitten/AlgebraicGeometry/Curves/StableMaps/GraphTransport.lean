/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.DecoratedGraph
import Mathlib.Data.Sym.Sym2

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry.Curves

universe u v

private theorem finTwo_perm_of_pair_eq {A : Type*} (a b : Fin 2 → A)
    (h : s(a 0, a 1) = s(b 0, b 1)) :
    ∃ e : Fin 2 ≃ Fin 2, ∀ i, a (e i) = b i := by
  rcases (Sym2.mk_eq_mk_iff (p := (a 0, a 1)) (q := (b 0, b 1))).mp h with h | h
  · refine ⟨Equiv.refl _, ?_⟩
    intro i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · refine ⟨Equiv.swap 0 1, ?_⟩
    intro i
    fin_cases i
    · simpa using congrArg Prod.snd h
    · simpa using congrArg Prod.fst h

namespace DualGraph

theorem valence_eq_of_endpoint_pairs (G : DualGraph.{u}) (H : DualGraph.{v})
    (cv : G.Vertex ≃ H.Vertex) (ce : G.Edge ≃ H.Edge)
    (hp : ∀ e, s(H.endpoint (ce e) 0, H.endpoint (ce e) 1) =
      s(cv (G.endpoint e 0), cv (G.endpoint e 1))) (x : G.Vertex) :
    H.valence (cv x) = G.valence x := by
  classical
  choose perm hperm using fun e ↦ finTwo_perm_of_pair_eq
    (H.endpoint (ce e)) (fun i ↦ cv (G.endpoint e i)) (hp e)
  let eh : G.HalfEdge ≃ H.HalfEdge :=
    (Equiv.prodCongrRight perm).trans (ce.prodCongr (Equiv.refl _))
  symm
  unfold valence
  apply Finset.card_equiv eh
  intro h
  unfold incident
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, HalfEdge.vertex]
  change G.endpoint h.1 h.2 = x ↔ H.endpoint (ce h.1) (perm h.1 h.2) = cv x
  rw [hperm]
  exact cv.injective.eq_iff.symm

end DualGraph

namespace StableMaps.DecoratedGraph

theorem markingCount_eq_of_equivs (G : DecoratedGraph.{u}) (H : DecoratedGraph.{v})
    (cv : G.toDualGraph.Vertex ≃ H.toDualGraph.Vertex) (cl : G.Leg ≃ H.Leg)
    (hl : ∀ l, H.legVertex (cl l) = cv (G.legVertex l)) (x : G.toDualGraph.Vertex) :
    H.markingCount (cv x) = G.markingCount x := by
  classical
  symm
  unfold markingCount
  apply Finset.card_equiv cl
  intro l
  unfold markingsAt
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, hl]
  exact cv.injective.eq_iff.symm

theorem logCanonicalDegree_eq_of_endpoint_pairs
    (G : DecoratedGraph.{u}) (H : DecoratedGraph.{v})
    (cv : G.toDualGraph.Vertex ≃ H.toDualGraph.Vertex)
    (ce : G.toDualGraph.Edge ≃ H.toDualGraph.Edge) (cl : G.Leg ≃ H.Leg)
    (hp : ∀ e, s(H.toDualGraph.endpoint (ce e) 0, H.toDualGraph.endpoint (ce e) 1) =
      s(cv (G.toDualGraph.endpoint e 0), cv (G.toDualGraph.endpoint e 1)))
    (hl : ∀ l, H.legVertex (cl l) = cv (G.legVertex l))
    (hg : ∀ x, H.toDualGraph.genus (cv x) = G.toDualGraph.genus x)
    (x : G.toDualGraph.Vertex) : H.logCanonicalDegree (cv x) = G.logCanonicalDegree x := by
  unfold logCanonicalDegree specialFlagCount
  rw [hg, DualGraph.valence_eq_of_endpoint_pairs G.toDualGraph H.toDualGraph cv ce hp,
    markingCount_eq_of_equivs G H cv cl hl]

theorem isStable_iff_of_endpoint_pairs
    (G : DecoratedGraph.{u}) (H : DecoratedGraph.{v})
    (cv : G.toDualGraph.Vertex ≃ H.toDualGraph.Vertex)
    (ce : G.toDualGraph.Edge ≃ H.toDualGraph.Edge) (cl : G.Leg ≃ H.Leg)
    (hp : ∀ e, s(H.toDualGraph.endpoint (ce e) 0, H.toDualGraph.endpoint (ce e) 1) =
      s(cv (G.toDualGraph.endpoint e 0), cv (G.toDualGraph.endpoint e 1)))
    (hl : ∀ l, H.legVertex (cl l) = cv (G.legVertex l))
    (hg : ∀ x, H.toDualGraph.genus (cv x) = G.toDualGraph.genus x)
    (hd : ∀ x, H.degree (cv x) = G.degree x) : H.IsStable ↔ G.IsStable := by
  constructor
  · intro h x hx
    have hh := h (cv x) (by rwa [hd])
    rwa [logCanonicalDegree_eq_of_endpoint_pairs G H cv ce cl hp hl hg x] at hh
  · intro h x hx
    obtain ⟨y, rfl⟩ := cv.surjective x
    rw [logCanonicalDegree_eq_of_endpoint_pairs G H cv ce cl hp hl hg]
    exact h y (by rwa [hd] at hx)

end StableMaps.DecoratedGraph

end GromovWitten.AlgebraicGeometry.Curves
