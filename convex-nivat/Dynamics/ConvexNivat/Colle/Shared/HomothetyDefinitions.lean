import ConvexNivat.Colle.Definitions

namespace ConvexNivat.Colle
noncomputable section

def positionedHomothetyVertices {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice) (N : ℕ) : Finset Lattice :=
  S.image (fun z => e + (2 * (N + 1 : ℕ) : ℤ) • z -
    (N + 1 : ℕ) • (C.vertex i + C.vertex (i + 1)))

def positionedHomothetyWindow {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice) (N : ℕ) : Finset Lattice :=
  convexLatticeWindow (positionedHomothetyVertices C i e N)

end
end ConvexNivat.Colle
