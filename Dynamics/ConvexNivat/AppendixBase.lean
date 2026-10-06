import ConvexNivat.ReductionAlgebra
import ConvexNivat.ReductionRows

namespace ConvexNivat
open scoped BigOperators

/-- D.3: a strip of height at least Δ is sufficient; the resulting period is
q h₁, not merely the primitive q u. -/
theorem lemmaD_3 (p : ℕ) (hp : p.Prime) (θ₁ θ₂ : Configuration (ZMod p))
    (u h₁ h₂ : Lattice) (hu : Primitive u) (c₁ : ℤ) (hc₁ : 1 ≤ c₁)
    (hh₁ : h₁ = c₁ • u) (hperiod₁ : HasPeriod θ₁ h₁)
    (hperiod₂ : HasPeriod θ₂ h₂) (hΔ : 0 < det u h₂)
    (a b q : ℤ) (hwidth : det u h₂ ≤ b - a) (hq : 1 ≤ q)
    (hstrip : ∀ z ∈ latticeStrip u a b,
      θ₁ (z + q • u) + θ₂ (z + q • u) = θ₁ z + θ₂ z) :
    HasPeriod (fun z => θ₁ z + θ₂ z) (q • h₁)  := by
  let θ : Configuration (ZMod p) := fun z => θ₁ z + θ₂ z
  have hstripN : ∀ n : ℕ, ∀ z ∈ latticeStrip u a b,
      θ (z + (n : ℤ) • (q • u)) = θ z := by
    intro n
    induction n with
    | zero => intro z hz; simp
    | succ n ih =>
      intro z hz
      have hz' : z + (n : ℤ) • (q • u) ∈ latticeStrip u a b := by
        simpa only [smul_smul] using strip_invariant u a b ((n : ℤ) * q) z hz
      calc
        θ (z + ((n + 1 : ℕ) : ℤ) • (q • u)) =
            θ ((z + (n : ℤ) • (q • u)) + q • u) := by
          congr 1
          simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_assoc]
        _ = θ (z + (n : ℤ) • (q • u)) := hstrip _ hz'
        _ = θ z := ih z hz
  have hstripH : ∀ z ∈ latticeStrip u a b, θ (z + q • h₁) = θ z := by
    intro z hz
    have hc : (c₁.toNat : ℤ) = c₁ := Int.toNat_of_nonneg (by omega)
    simpa only [hc, hh₁, smul_smul, mul_comm c₁ q] using hstripN c₁.toNat z hz
  let ψ : Configuration (ZMod p) := fun z => θ (z + q • h₁) - θ z
  have hψeq : ∀ z, ψ z = θ₂ (z + q • h₁) - θ₂ z := by
    intro z
    dsimp [ψ, θ]
    rw [(hasPeriod_zsmul θ₁ h₁ hperiod₁ q) z]
    abel
  have hpψ : HasPeriod ψ h₂ := by
    intro z
    rw [hψeq, hψeq]
    have ht := (hasPeriod_translate_iff θ₂ (q • h₁) h₂).mpr hperiod₂ z
    dsimp [translate] at ht
    rw [ht, hperiod₂ z]
  intro z
  let δ := det u h₂
  let r := det u z - a
  let n := -(r / δ)
  have hδ : 0 < δ := hΔ
  have hm₀ : 0 ≤ r % δ := Int.emod_nonneg r (ne_of_gt hδ)
  have hm₁ : r % δ < δ := Int.emod_lt_of_pos r hδ
  have hrow : det u (z + n • h₂) = a + r % δ := by
    change height u (z + n • h₂) = a + r % δ
    rw [height_add, height_zsmul]
    dsimp [height, n, r, δ]
    have he := Int.emod_add_mul_ediv (det u z - a) (det u h₂)
    nlinarith
  have hz : z + n • h₂ ∈ latticeStrip u a b := by
    change a ≤ det u (z + n • h₂) ∧ det u (z + n • h₂) ≤ b
    rw [hrow]
    have hwidth' : δ ≤ b - a := hwidth
    omega
  apply sub_eq_zero.mp
  change ψ z = 0
  calc
    ψ z = ψ (z + n • h₂) := ((hasPeriod_zsmul ψ h₂ hpψ n) z).symm
    _ = 0 := sub_eq_zero.mpr (hstripH _ hz)


/-- D.5 producer: deleting one extreme row preserves lattice convexity. -/
theorem delete_extreme_row_convex (u : Lattice) (B : Finset Lattice)
    (hB : B.Nonempty) (hconvex : LatticeConvex B) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) :
    LatticeConvex (B \ extremeRow σ u B hB)  := by
  let T := B \ extremeRow σ u B hB
  let f : RealPlane → ℝ := fun x => realDet (embed u) x
  have hlinear : IsLinearMap ℝ f := by
    constructor
    · intro x y; simp [f, realDet]; ring
    · intro c x; simp [f, realDet]; ring
  have hcast : ∀ z, f (embed z) = (det u z : ℝ) := by
    intro z
    simp [f, realDet, embed, det]
  have hsub : T ⊆ B := Finset.sdiff_subset
  have hhull : windowHull T ⊆ windowHull B := by
    apply convexHull_mono
    exact Set.image_mono (by exact_mod_cast hsub)
  intro z
  constructor
  · intro hz
    have hzB : z ∈ B := (hconvex z).mp (hhull hz)
    have hnot : z ∉ extremeRow σ u B hB := by
      rcases hσ with rfl | rfl
      · have hhalf : windowHull T ⊆ {x | f x < (rowMaximum u B hB : ℝ)} := by
          apply convexHull_min _ (convex_halfSpace_lt hlinear _)
          rintro _ ⟨w, hw, rfl⟩
          have hw' := Finset.mem_sdiff.mp hw
          have hle : det u w ≤ rowMaximum u B hB := Finset.le_sup' _ hw'.1
          have hne : det u w ≠ rowMaximum u B hB := by
            intro he
            exact hw'.2 (Finset.mem_filter.mpr ⟨hw'.1, by simpa [extremeRow] using he⟩)
          change f (embed w) < _
          rw [hcast]
          exact_mod_cast lt_of_le_of_ne hle hne
        intro he
        have hr : det u z = rowMaximum u B hB := by
          simpa [extremeRow] using (Finset.mem_filter.mp he).2
        have hlt := hhalf hz
        change f (embed z) < _ at hlt
        rw [hcast, hr] at hlt
        exact lt_irrefl _ hlt
      · have hhalf : windowHull T ⊆ {x | (rowMinimum u B hB : ℝ) < f x} := by
          apply convexHull_min _ (convex_halfSpace_gt hlinear _)
          rintro _ ⟨w, hw, rfl⟩
          have hw' := Finset.mem_sdiff.mp hw
          have hle : rowMinimum u B hB ≤ det u w := Finset.inf'_le _ hw'.1
          have hne : rowMinimum u B hB ≠ det u w := by
            intro he
            exact hw'.2 (Finset.mem_filter.mpr ⟨hw'.1, by simpa [extremeRow] using he.symm⟩)
          change _ < f (embed w)
          rw [hcast]
          exact_mod_cast lt_of_le_of_ne hle hne
        intro he
        have hr : det u z = rowMinimum u B hB := by
          simpa [extremeRow] using (Finset.mem_filter.mp he).2
        have hlt := hhalf hz
        change _ < f (embed z) at hlt
        rw [hcast, hr] at hlt
        exact lt_irrefl _ hlt
    exact Finset.mem_sdiff.mpr ⟨hzB, hnot⟩
  · intro hz
    exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩


end ConvexNivat
