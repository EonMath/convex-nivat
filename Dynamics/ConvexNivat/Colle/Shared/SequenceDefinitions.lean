import ConvexNivat.Colle.Shared.Definitions

namespace ConvexNivat.Colle
noncomputable section

structure AlternatingWindows (ξ xper : Configuration ℤ) {S : Finset Lattice}
    {m : ℕ} (C : AntipodalEdgeCycle S m) (i : ℤ) where
  B : ℕ → Finset Lattice
  A : ℕ → Finset Lattice
  shift : ℕ → Lattice
  normalise : ℕ → ℕ
  anchor : Lattice
  B_enveloped : ∀ j, EnvelopedWindow S (B j)
  A_enveloped : ∀ j, EnvelopedWindow S (A j)
  boundary : ∀ j, AlignedBoundary C (A j)
  base_in_maximal : ∀ j, B j ⊆ A j
  nesting : ∀ j, A j ⊆ B (j + 1)
  positioned : ∀ j, ∀ z ∈ supportRow (B j) (C.direction i), det (C.direction i) z = -1
  exhaustion : ∀ j, ∀ z ∈ integerSquare j, -1 ≤ det (C.direction i) z → z ∈ B j
  maximal : ∀ j, maximalAgreementWindow S (B j) (A j) (C.direction i)
    (translate (shift j) ξ) xper
  mismatch : ∀ j, ¬ AgreesOn (translate (shift j) ξ) xper (halfStrip (B j) (C.direction i))
  terminal : ∀ j, (boundary j).vertex (i + 1) -
    (normalise j : ℤ) • C.direction i = anchor
  first_normalise : normalise 0 = 0

def AlternatingWindows.normalised {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) : Finset Lattice :=
  windowTranslate (W.A j) (-((W.normalise j : ℤ) • C.direction i))

def AlternatingWindows.normalisedBase {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) : Finset Lattice :=
  windowTranslate (W.B j) (-((W.normalise j : ℤ) • C.direction i))

def AlternatingWindows.shiftedField {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) : Configuration ℤ :=
  translate (W.shift j + (W.normalise j : ℤ) • C.direction i) ξ

structure GrowingSubsequence {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) where
  subsequence : ℕ → ℕ
  strict : StrictMono subsequence
  phase : ℕ
  J : ℤ
  lower : i + 1 ≤ J
  upper : J ≤ i + (m : ℤ) - 1
  same_phase : ∀ j, translate ((W.normalise (subsequence j) : ℤ) • C.direction i) xper =
    translate ((phase : ℤ) • C.direction i) xper
  earlier_fixed : ∀ d : ℤ, i + 1 ≤ d → d < J →
    ∃ L : ℕ, ∀ j, (W.boundary (subsequence j)).length d = L
  growing : StrictMono (fun j => (W.boundary (subsequence j)).length J)
  nested : ∀ j, W.normalised (subsequence j) ⊆ W.normalised (subsequence (j + 1))

def normalisedUnion {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) : Set Lattice :=
  ⋃ j, (W.normalised (G.subsequence j) : Set Lattice)

def backwardSaturationCandidate (A : Finset Lattice) (d : Lattice)
    (U : Set Lattice) : Set Lattice := saturateRay (A : Set Lattice) (-d) ∩ U

end
end ConvexNivat.Colle
