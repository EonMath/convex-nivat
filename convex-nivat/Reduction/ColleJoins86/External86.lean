import ColleJoins86.Joins86

namespace ConvexNivat

/-- Source 8.6. Colle [2], DCDS 43 (2023), no.12, 4299–4327,
Theorem 1.9, printed p.4303, published PDF SHA-256
9ac0a0ef5eeadde742273d3005043b1842d3d012d23465c8ef9db1c7cafc4a1a.
Publisher PDF: https://www.aimsciences.org/data/article/export-pdf?id=64d0bdbfc1eef70e1f920310.
Opposite oriented normals encode ±ℓ. "Fully periodic" on
the whole plane is equivalent here to global double periodicity. -/
theorem external8_6_obligation (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hann : HasNontrivialIntegerAnnihilator ξ)
    (hexpansive : ∀ n : RealPlane, n ≠ 0 →
      ¬ OneSidedNonexpansive ξ n ∨ ¬ OneSidedNonexpansive ξ (-n)) :
    DoublyPeriodic ξ := by
  exact Colle.colle_theorem1_9 ξ A hA hann hexpansive

/-- The explicit "in particular" clause of source 8.6, same provenance. -/
theorem external8_6_both_directions_obligation (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hann : HasNontrivialIntegerAnnihilator ξ)
    (haperiodic : ¬ Periodic ξ) :
    ∃ n : RealPlane, OneSidedNonexpansive ξ n ∧ OneSidedNonexpansive ξ (-n) := by
  exact Colle.colle_theorem1_9_opposite_pair ξ A hA hann haperiodic

end ConvexNivat
