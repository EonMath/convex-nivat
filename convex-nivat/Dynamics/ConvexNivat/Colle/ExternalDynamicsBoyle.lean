import ConvexNivat.ExternalDynamicsHelpers.BoyleLind
import ConvexNivat.ExternalDynamicsHelpers.BoyleLindConstruction

namespace ConvexNivat.Colle
open ConvexNivat.ExternalDynamicsHelpers

theorem boyleLind_infinite_orbit_nonexpansive_line (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (hinfinite : (OrbitClosure ξ).Infinite) :
    ∃ n : RealPlane, NonexpansiveLine ξ n := by
  classical
  by_contra hn
  have hexp : ∀ n ∈ unitNormals, ¬ NonexpansiveLine ξ n := by
    intro n _ h
    exact hn ⟨n, h⟩
  obtain ⟨r, t, hr, ht, hcode⟩ := boyleLind_lemma3_5 ξ A hA unitNormals
    unitNormals_compact (fun _ h => h) hexp
  obtain ⟨R₀, hR₀, hgrowth⟩ := uniform_box_code_large_ball_growth ξ r t hr ht hcode
  exact hinfinite (finite_ball_code_orbit_finite ξ A hA R₀
    (large_ball_codes_entire_plane ξ R₀ hgrowth))

theorem not_double_has_nonexpansive_line (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (hnotdouble : ¬ DoublyPeriodic ξ) :
    ∃ n : RealPlane, NonexpansiveLine ξ n := by
  apply boyleLind_infinite_orbit_nonexpansive_line ξ A hA
  exact fun hfinite => hnotdouble ((finite_orbitClosure_iff_doublyPeriodic ξ A hA).mp hfinite)

end ConvexNivat.Colle
