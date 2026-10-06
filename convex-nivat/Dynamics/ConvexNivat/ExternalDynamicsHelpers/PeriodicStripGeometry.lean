import ConvexNivat.ExternalDynamicsHelpers.PeriodicStripCore
import ConvexNivat.CoreLattice

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

theorem lattice_strip_finite_period_representatives (v h : Lattice)
    (hv : v ≠ 0) (hh : h ≠ 0) (hparallel : det v h = 0) (a b : ℤ) :
    ∃ B : Finset Lattice, (B : Set Lattice) ⊆ latticeStrip v a b ∧
      ∀ z ∈ latticeStrip v a b, ∃ q ∈ B, ∃ j : ℤ, z = q + j • h := by
  classical
  have hcoord : ∃ c : Lattice → ℤ, c h ≠ 0 ∧
      (∀ z j, c (z - j • h) = c z - j * c h) ∧
      Function.Injective (fun z => (c z, det v z)) := by
    by_cases hh1 : h.1 = 0
    · have hh2 : h.2 ≠ 0 := by intro e; exact hh (Prod.ext hh1 e)
      have hv1 : v.1 = 0 := by
        dsimp [det] at hparallel
        rw [hh1, mul_zero, sub_zero] at hparallel
        exact (mul_eq_zero.mp hparallel).resolve_right hh2
      have hv2 : v.2 ≠ 0 := by intro e; exact hv (Prod.ext hv1 e)
      refine ⟨Prod.snd, hh2, fun z j => by simp, ?_⟩
      intro z z' he
      have h2 := congrArg Prod.fst he
      have hd := congrArg Prod.snd he
      dsimp [det] at h2 hd
      apply Prod.ext _ h2
      apply mul_left_cancel₀ hv2
      simp only [hv1, zero_mul, zero_sub] at hd
      omega
    · have hv1 : v.1 ≠ 0 := by
        intro e
        have hv2 : v.2 = 0 := by
          dsimp [det] at hparallel
          rw [e, zero_mul, zero_sub] at hparallel
          exact (mul_eq_zero.mp (neg_eq_zero.mp hparallel)).resolve_right hh1
        exact hv (Prod.ext e hv2)
      refine ⟨Prod.fst, hh1, fun z j => by simp, ?_⟩
      intro z z' he
      have h1 := congrArg Prod.fst he
      have hd := congrArg Prod.snd he
      dsimp [det] at h1 hd
      apply Prod.ext h1
      apply mul_left_cancel₀ hv1
      rw [h1] at hd
      omega
  obtain ⟨c, hc, hsub, hinj⟩ := hcoord
  let C : Set Lattice := (fun z => (c z, det v z)) ⁻¹'
    (Set.Ico 0 |c h| ×ˢ Set.Icc a b)
  have hC : C.Finite := Set.Finite.preimage hinj.injOn
    ((Set.finite_Ico _ _).prod (Set.finite_Icc _ _))
  refine ⟨hC.toFinset, ?_, ?_⟩
  · intro q hq
    exact ((hC.mem_toFinset.mp hq) : _ ∧ _).2
  · intro z hz
    let j : ℤ := c z / c h
    let q : Lattice := z - j • h
    have hqdet : det v q = det v z := by
      change v.1 * (z.2 - j * h.2) - v.2 * (z.1 - j * h.1) = det v z
      calc
        _ = det v z - j * det v h := by dsimp [det]; ring
        _ = det v z := by rw [hparallel]; ring
    have hqc : c q = c z % c h := by
      rw [show q = z - j • h from rfl, hsub]
      dsimp [j]
      have hh := Int.emod_add_ediv_mul (c z) (c h)
      omega
    refine ⟨q, hC.mem_toFinset.mpr ?_, j, by dsimp [q]; abel⟩
    change (0 ≤ c q ∧ c q < |c h|) ∧ a ≤ det v q ∧ det v q ≤ b
    rw [hqc, hqdet]
    exact ⟨⟨Int.emod_nonneg _ hc, Int.emod_lt_abs _ hc⟩, hz⟩

theorem periodic_strip_convex_coding_window (ξ : Configuration ℤ)
    (h v : Lattice) (hh : h ≠ 0) (hv : Primitive v)
    (hperiod : HasPeriod ξ h) (hparallel : det v h = 0)
    (a b : ℤ) (hab : a ≤ b) (D : Finset Lattice)
    (hD : (D : Set Lattice) ⊆ latticeStrip v a b) :
    ∃ B : Finset Lattice, B.Nonempty ∧ LatticeConvex B ∧ D ⊆ B ∧
      (B : Set Lattice) ⊆ latticeStrip v a b ∧
      WindowCodes ξ B (latticeStrip v a b) := by
  classical
  obtain ⟨R, hR, hreps⟩ := lattice_strip_finite_period_representatives v h
    (primitive_ne_zero v hv) hh hparallel a b
  obtain ⟨z₀, hz₀⟩ := primitive_height_surjective v hv a
  change det v z₀ = a at hz₀
  let V := insert z₀ (D ∪ R)
  let B := convexLatticeWindow V
  have hVB : V ⊆ B := by
    intro z hz
    exact (lattice_windowHull_finite V).mem_toFinset.mpr
      (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)
  have hBV : windowHull B = windowHull V := by
    apply Set.Subset.antisymm
    · apply convexHull_min _ (convex_convexHull ℝ _)
      rintro _ ⟨z, hz, rfl⟩
      exact (lattice_windowHull_finite V).mem_toFinset.mp hz
    · exact convexHull_mono (Set.image_mono hVB)
  have hBconv : LatticeConvex B := by
    intro z
    rw [hBV]
    exact (lattice_windowHull_finite V).mem_toFinset.symm
  have hVstrip : (V : Set Lattice) ⊆ latticeStrip v a b := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨hz₀.ge, hz₀.le.trans hab⟩
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact hD hz
      · exact hR hz
  let ℓ : RealPlane →ₗ[ℝ] ℝ :=
    { toFun := fun x => (v.1 : ℝ) * x.2 - (v.2 : ℝ) * x.1
      map_add' := by intros; dsimp; ring
      map_smul' := by intros; dsimp; ring }
  have hℓ (z : Lattice) : ℓ (embed z) = (det v z : ℝ) := by
    dsimp [ℓ, embed, det]
    push_cast
    rfl
  have hHull : windowHull V ⊆ ℓ ⁻¹' Set.Icc (a : ℝ) (b : ℝ) := by
    apply convexHull_min _ ((convex_Icc _ _).linear_preimage ℓ)
    rintro _ ⟨z, hz, rfl⟩
    change (a : ℝ) ≤ ℓ (embed z) ∧ ℓ (embed z) ≤ (b : ℝ)
    rw [hℓ]
    exact ⟨by exact_mod_cast (hVstrip hz).1, by exact_mod_cast (hVstrip hz).2⟩
  refine ⟨B, ⟨z₀, hVB (Finset.mem_insert_self _ _)⟩, hBconv, ?_, ?_, ?_⟩
  · intro z hz
    exact hVB (Finset.mem_insert_of_mem (Finset.mem_union_left R hz))
  · intro z hz
    have he := hHull ((lattice_windowHull_finite V).mem_toFinset.mp hz)
    change (a : ℝ) ≤ ℓ (embed z) ∧ ℓ (embed z) ≤ (b : ℝ) at he
    rw [hℓ] at he
    exact ⟨by exact_mod_cast he.1, by exact_mod_cast he.2⟩
  · apply periodic_representatives_code_strip ξ h hperiod v a b B
    intro z hz
    obtain ⟨q, hq, j, he⟩ := hreps z hz
    exact ⟨q, hVB (Finset.mem_insert_of_mem (Finset.mem_union_right D hq)), j, he⟩

end
end ConvexNivat.ExternalDynamicsHelpers
