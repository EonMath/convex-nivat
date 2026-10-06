import ConvexNivat.Colle.Shared.SequenceDefinitions

namespace ConvexNivat.Colle
noncomputable section

structure NormalisedWindowLimit {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) where
  field : Configuration ℤ
  index : ℕ → ℕ
  strict : StrictMono index
  orbit : field ∈ OrbitClosure ξ
  converges : PointwiseLimit (fun j => W.shiftedField (G.subsequence (index j))) field
  agrees_union : AgreesOn field (translate ((G.phase : ℤ) • C.direction i) xper)
    (normalisedUnion W G)
  same_union : (⋃ j, (W.normalised (G.subsequence (index j)) : Set Lattice)) =
    normalisedUnion W G

end
end ConvexNivat.Colle
