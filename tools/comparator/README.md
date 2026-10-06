# Official Comparator

This directory integrates [leanprover/comparator](https://github.com/leanprover/comparator)
with the project's pinned Lean 4.35.0-rc3 toolchain. The checked interfaces are:

- `ConvexNivatComparator.convexNivat`, proved by `ConvexNivat.convexNivat`;
- `ConvexNivatComparator.nivatRectangles`, proved by `ConvexNivat.nivatRectangles`;
- `ConvexNivatComparator.theoremT`, proved by `ConvexNivat.theoremT`.

## Run locally

Use Linux with Landlock support, an unprivileged account, a working systemd
user session, Python 3.12 or newer, elan/Lake on `PATH`, and a C compiler.
Network access is needed for the first tool installation. On Linux x86-64,
the bootstrap downloads a hash-pinned Go toolchain; on other architectures,
install Go 1.24 or newer yourself.

From the repository root:

```sh
lake exe cache get
lake build
python3 tools/comparator/run.py
```

The runner installs tools in `.lake/comparator-tools/`, then invokes the
official comparator with real Landrun under a systemd user unit with
`RestrictAddressFamilies=~AF_UNIX`. A nonzero exit indicates failure. It does
not substitute a fake sandbox. The final success message is
`Your solution is okay!`.

For a separate tool cache:

```sh
python3 tools/comparator/run.py --cache /path/to/comparator-cache
```

The optional `--project` and `--config` flags select a project and comparator
configuration. The selected project's Lean version must match the pinned
toolchain. The bootstrap verifies downloaded archives and cached executable
hashes. Source revisions and archive digests are recorded in [pins.json](pins.json).
No tool binaries or generated proof exports are tracked by Git.

## What is checked

[Challenge.lean](Challenge.lean) is the trusted specification. Its only project
import is `ConvexNivat.Core`, which defines configurations, pattern complexity,
lattice convexity, periodicity and star configurations using Mathlib. It does
not import theorem providers. Its three deliberate `sorry` terms describe the
obligations for Comparator and do not enter the ordinary proof library.

[Solution.lean](Solution.lean) is compiled independently. It has exactly the
same three statement headers and proves them using the accepted mathematical
development. It never imports Challenge. The two modules use the same fully
qualified declaration names, so they must not be imported together.

[comparator.json](comparator.json) permits only `propext`, `Quot.sound` and
`Classical.choice`. The official tool compares the declarations needed to state
the challenge with the solution environment, checks solution axiom dependencies
and replays the solution in Lean's kernel. NanoDa or another external kernel is
not enabled. This is an additional check of the three named theorem interfaces;
[Verify.lean](../Verify.lean) separately audits all retained project declarations.

Both checking modules are separate, non-default Lake targets. Plain `lake build`
continues to build `MainTheorem`; neither the main entry nor Solution imports
the intentional Challenge placeholders. Comparator checks Lean statements and
their dependencies; agreement of those statements with the manuscript remains
the separately reviewed formalization boundary.

## Local validation

On 6 October 2026, the pinned official comparator checked all three theorem
interfaces and returned `Your solution is okay!` with exit status 0. The run
used the published runner, real Landrun and the systemd restriction described
above. The combined Solution also passed compilation, zero-placeholder scanning,
the classical-base axiom audit and all three frozen statement guards.

The matching upstream smoke example succeeded; a mismatch example was rejected
with a nonzero exit. The sandbox denied an attempted write outside its allowed
location. The project check reused the previously accepted compiled mathematical
dependencies in an isolated copy of the exact source/configuration layout;
this is not an additional fresh build of every mathematical module.

[verification.json](verification.json) records the checked input hashes, exact
tool revisions and executable hashes, successful result and negative-control
rejection. It describes this recorded run; rerun the command after source changes.
The unchanged mathematical source files and dependency pins are individually
bound by [source-hashes.json](source-hashes.json), copied from the sealed local
baseline. Those files match repository commit
`cacaa2761050714b7f211976c046f0062e428f1b`.

## Tool provenance

The bootstrap downloads exact upstream source revisions instead of adding the
tool implementation as a dependency of the mathematical library:

- [Comparator](https://github.com/leanprover/comparator) `fd5d5bcf14177b187f66d4502071268d877887c3`;
- [lean4export](https://github.com/leanprover/lean4export) `66f1fb4bc256072069767fce52d39480e4524869`;
- [Landrun](https://github.com/Zouuup/landrun) `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`.

Upstream license files are preserved in [licenses/](licenses/) and in the
downloaded source trees. The bootstrap
changes Comparator's exporter dependency location to the separately pinned
local checkout; its Lean implementation is unchanged. GitHub Actions remains
disabled: these commands are intended for local verification.
