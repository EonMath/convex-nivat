import ConvexNivat.Colle.RegionArcSweeps
import ConvexNivat.Colle.RegionArcCompatibility
import ConvexNivat.Colle.Shared.LocalLimitPatch
import ConvexNivat.Colle.Shared.Sweeps

namespace ConvexNivat.Colle
noncomputable section

private theorem seed_radius_mono {v w : Lattice} (P : Region v w)
    (n R Q t : ℕ) (hRQ : R ≤ Q) : regionalSeed P n R t ⊆ regionalSeed P n Q t := by
  intro z hz
  rcases hz with hz | ⟨hz, ht⟩
  · exact Or.inl hz
  · refine Or.inr ⟨hz, ?_⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_image.mpr
    refine ⟨q, ?_, rfl⟩
    change q ∈ integerSquare Q
    change q ∈ integerSquare R at hq
    rcases q with ⟨qx, qy⟩
    simp only [integerSquare, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hq ⊢
    have hcast : (R : ℤ) ≤ Q := by exact_mod_cast hRQ
    omega

private theorem claim3_7_from_finite_sweep (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (S : Finset Lattice) (hS : GeneratingSet ξ S)
    (v w : Lattice) (P : Region v w) (hweak : WeaklyEnveloped S P)
    (hcompat : RegionCompatibleArc S P)
    (ϑ xper : Configuration ℤ) (hϑ : ϑ ∈ OrbitClosure ξ)
    (hxper : xper ∈ OrbitClosure ξ)
    (hperiod : ∃ k : ℤ, k ≠ 0 ∧ HasPeriod xper (k • v))
    (n : ℕ) (hagrees : AgreesOn ϑ xper (P.enlargement n))
    (hdisagrees : ¬ AgreesOn ϑ xper (P.enlargement (n + 1)))
    (hsweep : ∃ R T : ℕ, ∀ t ≥ T, ∀ F : Finset Lattice,
      (F : Set Lattice) ⊆ P.enlargement (n + 1) →
        HasFiniteSweep S (regionalSeed P n R t) F) :
    ∀ x : Configuration ℤ, SubsequentialTranslateLimit ϑ w x → ¬ DoublyPeriodic x := by
  intro x hx hdouble
  obtain ⟨s, hs, hlimit⟩ := hx
  obtain ⟨a, ha, hper⟩ := hperiod
  obtain ⟨R, T, hfill⟩ := hsweep
  obtain ⟨b, hb, hab, hxb, R₀, hpatch⟩ :=
    local_limit_common_period_patch ξ ϑ xper x S hS P hweak hϑ hxper
      a ha hper n hagrees s hs hlimit hdouble
  obtain ⟨j, hj, hlocal, hseed⟩ := hpatch (max R R₀) (le_max_right _ _) T
  have hseedR : AgreesOn ϑ xper (regionalSeed P n R (s j)) := by
    intro z hz
    exact hseed z (seed_radius_mono P n R (max R R₀) (s j) (le_max_left _ _) hz)
  apply hdisagrees
  intro z hz
  obtain ⟨steps, hvalid, hcovered⟩ := hfill (s j) hj {z} (by
    intro q hq
    have he : q = z := Finset.mem_singleton.mp hq
    simpa only [he] using hz)
  exact generating_one_point_and_finite_sweep ξ ϑ xper S hS hϑ hxper
    (regionalSeed P n R (s j)) steps hvalid hseedR z
      (hcovered (Finset.mem_singleton_self z))

theorem colle_claim3_7_with_arc (ξ : Configuration ℤ) (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (S : Finset Lattice) (hS : GeneratingSet ξ S) (v w : Lattice)
    (P : Region v w) (hweak : WeaklyEnveloped S P) (hcompat : RegionCompatibleArc S P)
    (ϑ xper : Configuration ℤ) (hϑ : ϑ ∈ OrbitClosure ξ)
    (hxper : xper ∈ OrbitClosure ξ)
    (hperiod : ∃ k : ℤ, k ≠ 0 ∧ HasPeriod xper (k • v))
    (n : ℕ) (hagrees : AgreesOn ϑ xper (P.enlargement n))
    (hdisagrees : ¬ AgreesOn ϑ xper (P.enlargement (n + 1))) :
    ∀ x : Configuration ℤ, SubsequentialTranslateLimit ϑ w x → ¬ DoublyPeriodic x := by
  exact claim3_7_from_finite_sweep ξ A hA S hS v w P hweak hcompat ϑ xper
    hϑ hxper hperiod n hagrees hdisagrees
    (enlarged_region_finite_seed_sweep ξ S hS P hweak hcompat n)

end
end ConvexNivat.Colle
