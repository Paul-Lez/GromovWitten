# Issue 51: the full cotangent complex

Upstream: https://github.com/Paul-Lez/GromovWitten/issues/51

This branch is based on `d31abfc6a80148596ca5b1300d06396626aabb7f`.

## Verified construction

- `SimplicialResolution.lean` constructs the actual polynomial free/forgetful
  adjunction and its comonad. It defines iterated powers, faces, degeneracies,
  and augmentation, and proves naturality, the face-face identity, the two
  counit cancellation identities, and face/augmentation compatibility.
- `AllDegree.lean` constructs `S ⊗[P_n] Ω[P_n/R]` from the actual iterated
  polynomial algebras, linearizes the algebra faces, and proves their
  all-degree face-face identity. The maps come from the universal derivation
  and tensor product, with a generator formula and extensionality theorem.
- `Augmentation.lean` constructs compatible maps from every term to `Ω[S/R]`
  and proves surjectivity. The algebra augmentations have explicit preimages
  obtained by taking polynomial variables recursively.

- `ChainComplex.lean` constructs the alternating differential and proves its
  square is zero by a finite sign-pairing argument. It constructs the actual
  chain complex, its extension to a nonpositive cochain complex, its image in
  the derived category, and a chain augmentation to `Ω[S/R]` in degree zero.

## Remaining scope

These results do not identify homology with the naive presentation complex,
prove resolution independence, or establish the Jacobi--Zariski distinguished
triangle, derived base change, localization, or the requested geometric
criteria. `Full.lean` in the baseline remains a two-term construction.

The pinned Mathlib has no equivalence from `SimplexCategoryGenRel` to
`SimplexCategory`. Accordingly, the comonad core does not claim to have
constructed a `SimplicialObject` through that nonexistent equivalence. The
alternating chain complex here is constructed directly from the proved
face-face identities.

## Review

Four distinct `gpt-5.6-luna` agents at `xhigh` were assigned polynomial
construction, comonad laws, differential linearization, and chain-complex
tasks. The orchestrator independently reviewed and repaired proofs and added
the augmentation results. All Lean/Lake commands use a shared build lock and
two Lean threads.

## Validation

The complete default `/tmp/gw-issue-build build` passed with warnings treated
as errors (8,983 jobs). The public umbrella imports all four new modules.
Central construction and proof declarations were audited with `#print axioms`;
they use only `propext`, `Classical.choice`, and `Quot.sound`. No new
`sorry`, `admit`, custom axioms, `native_decide`, or warning suppression is used.
