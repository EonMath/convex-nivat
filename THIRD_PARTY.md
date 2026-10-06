# Third-party code and attribution

This project combines original `ConvexNivat` formalization work with two
separately pinned Lean developments. Their identities and scopes must remain
distinct.

## Nivat infrastructure

Source: [boonsuan/nivat](https://github.com/boonsuan/nivat), revision
[`4e3614024227acd273c3e8ab41df92c2709e5ab0`](https://github.com/boonsuan/nivat/tree/4e3614024227acd273c3e8ab41df92c2709e5ab0).

The following seven files were transplanted byte-for-byte, retaining their
`Nivat` module names within the release category directories:

- [Basic.lean](Foundations/Nivat/Core/Basic.lean)
- [Patterns.lean](Foundations/Nivat/Core/Patterns.lean)
- [BoundedDifferences.lean](Foundations/Nivat/Core/BoundedDifferences.lean)
- [Action.lean](Algebra/Nivat/Algebra/Action.lean)
- [LowComplexity.lean](Algebra/Nivat/Algebra/LowComplexity.lean)
- [RationalScaling.lean](Algebra/Nivat/Algebra/RationalScaling.lean)
- [ProductDifferences.lean](Algebra/Nivat/Algebra/ProductDifferences.lean)

They provide configuration/pattern infrastructure, Laurent actions, rational
annihilators, coefficient clearing and product-of-differences results. The
project adapters bridge them to the paper's integer annihilator and
decomposition contracts. This adoption does not import the upstream final
rectangular Nivat theorem.

License: **MIT**, copyright **2026 Boon Suan Ho**. The exact upstream notice
is retained in [THIRD_PARTY_LICENSE](THIRD_PARTY_LICENSE). This notice applies
to the copied `Nivat` files; it does not license all other project code.

## Independent convex-Nivat provider

Source: [Rogerhu12/convex-nivat-lean](https://github.com/Rogerhu12/convex-nivat-lean),
revision
[`5674e77aabc7235b733b7111ad71c18b3fe5c74b`](https://github.com/Rogerhu12/convex-nivat-lean/tree/5674e77aabc7235b733b7111ad71c18b3fe5c74b).

The historical transplant comprised **219 mathematical modules under
`NivatTrial/` plus the unchanged `NivatTrial.lean` root module**. This reduced
release retains the 219 mathematical modules in `vendor/nivat-trial/` and
omits the upstream root wrapper.
[EXTERNAL_NIVAT_PROVENANCE.json](EXTERNAL_NIVAT_PROVENANCE.json) records the
219 shipped files, their relative paths, individual hashes and exact upstream
revision. Upstream audit scaffolds, Python checkers and CI were outside the
production transplant.

Its endpoint is
`NivatTrial.TheoremB.periodic_of_low_convex_complexity`. The accepted project
bridge uses that independently checked theorem in the final convex-Nivat
route. The provider was compiled under this project's pinned Lean and Mathlib
versions, and its consumed proofs were audited for transitive axioms. Review
of that exact endpoint does not confer verbatim source-lemma credit on every
intermediate provider declaration.

**License status:** the exact pinned upstream tree contains no license or
copyright permission file, and its README supplies no license grant. No
upstream open-source license is asserted for `NivatTrial` here. The unrelated
MIT notice for `boonsuan/nivat` must not be presented as its license.

The upstream README credits implementation and internal reviews to Codex
agents under the submitter's direction. This repository credits the provider
as reused formalization work. Its use is an alternative proof route; it does
not claim to reconstruct every step of Colle's original geometric proof.

## Libraries and mathematical sources

The build uses [Lean 4](https://github.com/leanprover/lean4) and
[Mathlib](https://github.com/leanprover-community/mathlib4), fetched as package
dependencies with their upstream licenses. `lean-toolchain` and
`lake-manifest.json` pin the exact versions. This development's adopted
provider was checked with Lean `v4.35.0-rc3` and Mathlib revision
`3f6737de4761ec7bf368491fe9faccc991ebd6ca`.

The main supplied mathematical source is the Apex Intelligence manuscript of
12 September 2026, identified by hash in [SOURCE_ISSUES.md](SOURCE_ISSUES.md).
Kari-Szabados, Colle, Szabados and Morse-Hedlund are mathematical source
attributions, not licenses for the copied Lean files. The final source
contracts are proved rather than retained as unproved external assumptions.
