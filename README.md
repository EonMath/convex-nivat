# Convex Nivat formalization

A Lean 4 formalization of *The Convex Nivat Conjecture: A Complexity Lower Bound
for Star Configurations, and a Reduction from Low Convex Complexity to Star
Configurations* (Apex Intelligence, 12 September 2026).

Start with [MainTheorem.lean](MainTheorem.lean), the single public entry point.
The headline theorem is **`ConvexNivat.convexNivat`**, Theorem B / 8.18.

## Main theorem

Let `ξ : ℤ² → A` be a configuration over any finite alphabet. If some nonempty
finite lattice-convex set `S` satisfies

**Pξ(S) ≤ |S|,**

then `ξ` has a nonzero global period: there is `v ≠ 0` such that
`ξ(z + v) = ξ(z)` for every lattice point `z`.
Here `Pξ(S)` counts all patterns occurring on translates of `S`, and
lattice-convex means that `S` contains exactly the lattice points of its real
convex hull. Periodicity means one nonzero period, not necessarily two
independent periods.

The declaration and its rectangular corollary are in
[OriginalMain.lean](convex-nivat/Reduction/ConvexNivat/OriginalMain.lean).
For an `n × k` rectangle with `n,k ≥ 1`, the condition is `Pξ(n,k) ≤ nk`.

```lean
import MainTheorem

#check ConvexNivat.convexNivat
#check ConvexNivat.nivatRectangles
```

## Supporting mathematics

The development retains the paper's 49 precise original results in sections
0–8 and Appendix D. [The result index](docs/PAPER_RESULTS.md) maps the source
headings to their Lean declarations. Introductory aliases, definitions and
supporting helper lemmas are counted separately from those results.

- **Star configurations:** Theorem A / 7.3, `ConvexNivat.theoremT`, proves
  `Pθ(S) ≥ |S| + 1` for every nonempty finite lattice-convex window of a star
  configuration. See [the proof](convex-nivat/Star/ConvexNivat/MainTheorem.lean).
- **Algebra and spectrum:** Laurent difference operators, annihilators,
  exceptional spectra, Newton polygons and affine dimension bounds.
- **Geometry and dynamics:** lattice convexity, zonotopes, sectors, orbit
  closures, nonexpansive directions and periodicity propagation.
- **Two periodic components:** Appendix D's finite-field convex theorem and
  its finite-range abelian-group version are retained. Appendix D supplies
  a result used in Proposition 8.14.

The final convex-Nivat proof uses the independently verified `NivatTrial`
provider through [ExternalNivatAdapters.lean](convex-nivat/Reduction/ExternalNivatAdapters.lean).
The star proof and intermediate paper statements are also retained. In
particular, the exact 8.7 minimal-counterexample contract is discharged using
the provider's full theorem. This is an alternative proof route; the repository
does not claim to reconstruct Colle's original geometric proof.

## Source layout

All mathematical code is collected under [convex-nivat/](convex-nivat/),
with subdirectories grouped by mathematical subject. Lake preserves the existing Lean
module names through the source-directory configuration, so declaration and
import identities remain stable.

| Directory | Contents |
| --- | --- |
| [Foundations/](convex-nivat/Foundations/) | Configurations, finite patterns, lattice and period definitions. |
| [Algebra/](convex-nivat/Algebra/) | Laurent actions, finite differences, annihilators and decomposition. |
| [Spectral/](convex-nivat/Spectral/) | Fourier spectra, cyclotomic arguments, polynomial quotients and dimension bounds. |
| [Geometry/](convex-nivat/Geometry/) | Lattice convexity, zonotopes and polygon geometry. |
| [Star/](convex-nivat/Star/) | Star configurations, sector arguments, observables and Theorem A. |
| [Dynamics/](convex-nivat/Dynamics/) | Orbit closures, nonexpansive directions, periodicity propagation and two-component results. |
| [Reduction/](convex-nivat/Reduction/) | Paper reduction interfaces, external-provider adapter and the main theorem. |
| [vendor/nivat-trial/](convex-nivat/vendor/nivat-trial/) | Pinned independent convex-Nivat proof provider. |

The release omits 150 modules outside the retained source-result import
closure, including unused Colle reconstruction routes and experimental
scaffolds. The 447 retained original modules keep their complete source text.
No helper inside a retained module was deleted merely because a text search
found no reference: attributes, instances and proof automation can use such
helpers implicitly. `lake build` reaches every retained mathematical module.

## Build and verification

Install [elan](https://github.com/leanprover/elan) and Git, then run:

```sh
git clone git@github.com:EonMath/convex-nivat.git
cd convex-nivat
lake exe cache get
lake build
lake env lean tools/Verify.lean
```

The toolchain is pinned to **Lean 4.35.0-rc3**, and Mathlib to revision
`3f6737de4761ec7bf368491fe9faccc991ebd6ca`. The committed Lake manifest fixes
transitive package revisions. All dependencies are obtained from their pinned
repositories; no original workspace, absolute local source path or prebuilt
project artifact is required.

The release was built from source on 6 October 2026: all 448 mathematical
modules passed, using cached Mathlib dependencies and freshly compiling every
project and vendored module. The build took about 15 minutes on the development
machine; smaller CI runners can take longer. The 9,110 project declarations,
including private and generated declarations, passed the axiom audit. All 765
retained historical statement guards passed. The complete kernel types and
proof values of the main theorem, rectangular corollary and star theorem match
the accepted pre-cleanup versions. Remaining diagnostics are inherited linter
warnings, not proof holes.

`MainTheorem` is the default Lake target. The verification tool checks the
transitive axioms of project and vendored declarations. The accepted base is
`propext`, `Classical.choice` and `Quot.sound`; cited results are proved, not
left as additional mathematical axioms. Verification is performed locally;
automatic GitHub Actions runs are disabled.

## Official Comparator

[Lean's official Comparator](https://github.com/leanprover/comparator) is
available through [tools/comparator](tools/comparator/). It checks the convex
Nivat theorem, its rectangular corollary and the star-configuration theorem
against a separately compiled specification, checks permitted axioms, and
replays the solution dependencies through the Lean kernel.

After the ordinary build, run on Linux with a working systemd user session:

```sh
python3 tools/comparator/run.py
```

The runner builds hash-pinned Comparator, `lean4export` and Landrun versions
matching Lean 4.35.0-rc3, then invokes the real sandbox. Generated tools remain
under the ignored `.lake/` directory. See [the tool guide](tools/comparator/README.md)
for prerequisites, trust boundaries and verification results.

The local official comparator run passed all three interfaces; the
[recorded result](tools/comparator/verification.json) includes exact input and
tool hashes and a rejected negative control.

`Challenge.lean` intentionally contains three specification placeholders and
imports only the shared definitions. It is excluded from the default proof
build. `Solution.lean` supplies all three proofs without placeholders and does
not import the challenge. The original mathematical library remains unchanged.

## Source issues

[SOURCE_ISSUES.md](SOURCE_ISSUES.md) records one confirmed invalid inference
in Appendix C.3: nonvanishing for one operator factor does not prove
nonvanishing for the full product. The general nonextension assertion in
Remark 3.1′ has a separately proved witness, retained in this repository.

Appendix B's seven announcements omit exact statements and are expressly
outside the proof chain. Appendix C's original experiment scripts and outputs
were not supplied to this development, so those exact runs are not claimed
as reproduced. These limitations do not supply assumptions or outstanding
proof obligations for the main theorem. Historical translation defects are
listed separately from manuscript findings.

## References and attribution

The supplied manuscript is identified by SHA-256
`7fd67831155f4226c010fd6af32de558b76643771e6be12dea4eebafa21745a8`.
The PDF is not required for compilation.

[THIRD_PARTY.md](THIRD_PARTY.md) records the exact revisions and distinct
license status of the reused `Nivat` and `NivatTrial` sources. The latter's
shipped files and hashes are listed in
[EXTERNAL_NIVAT_PROVENANCE.json](EXTERNAL_NIVAT_PROVENANCE.json).
Lean and Mathlib retain their upstream licenses.

To cite this formalization, refer to
[EonMath/convex-nivat](https://github.com/EonMath/convex-nivat), specifying the
commit used.
