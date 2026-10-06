import ConvexNivat.ReductionDefinitions
import ConvexNivat.CoreLattice

namespace ConvexNivat

private theorem row_basis_decomposition (v k z : Lattice) (hvk : det v k = 1) :
    z = (det z k) • v + (det v z) • k := by
  have h : (det v k) • z = (det z k) • v + (det v z) • k := by
    ext <;> simp [det] <;> ring
  simpa only [hvk, one_smul] using h

private theorem row_coordinate_add (v k w : Lattice) (hvk : det v k = 1) (j : ℤ) :
    det (w + j • v) k = det w k + j := by
  have h : det (w + j • v) k = det w k + j * det v k := by
    simp [det]
    ring
  simpa [hvk] using h

private theorem row_difference (v k w z : Lattice) (hvk : det v k = 1)
    (hrow : det v z = det v w) : z = w + (det z k - det w k) • v := by
  calc
    z = det z k • v + det v z • k := row_basis_decomposition v k z hvk
    _ = (det w k • v + det v w • k) + (det z k - det w k) • v := by
      rw [hrow, sub_smul]
      abel
    _ = w + (det z k - det w k) • v := by rw [← row_basis_decomposition v k w hvk]

private theorem row_intermediate_mem (S : Finset Lattice) (hS : LatticeConvex S)
    (v w : Lattice) (m n : ℤ) (hw : w ∈ S) (hm : w + m • v ∈ S)
    (hn0 : 0 ≤ n) (hnm : n ≤ m) : w + n • v ∈ S := by
  by_cases hm0 : m = 0
  · have hn : n = 0 := by omega
    simpa [hn] using hw
  have hmpos : 0 < m := by omega
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hnr : 0 ≤ (n : ℝ) := by exact_mod_cast hn0
  have hnmr : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  apply (hS _).mp
  have hw' : embed w ∈ windowHull S := subset_convexHull ℝ _ ⟨w, hw, rfl⟩
  have hm' : embed (w + m • v) ∈ windowHull S :=
    subset_convexHull ℝ _ ⟨w + m • v, hm, rfl⟩
  have hc := (convex_convexHull ℝ (embed '' (S : Set Lattice))) hw' hm'
    (sub_nonneg.mpr ((div_le_one₀ hmr).mpr hnmr)) (div_nonneg hnr hmr.le)
    (show (1 - (n : ℝ) / m) + (n : ℝ) / m = 1 by ring)
  have heq : (1 - (n : ℝ) / m) • embed w + ((n : ℝ) / m) • embed (w + m • v) =
      embed (w + n • v) := by
    ext <;> simp [embed] <;> field_simp <;> ring
  rwa [heq] at hc

theorem row_is_consecutive (v : Lattice) (hv : Primitive v)
    (S : Finset Lattice) (hS : LatticeConvex S) (t : ℤ)
    (hne : (S.filter (fun z => det v z = t)).Nonempty) :
    ∃ w : Lattice, det v w = t ∧
      ∀ z, z ∈ S ∧ det v z = t ↔
        ∃ j : ℕ, j < (S.filter (fun z => det v z = t)).card ∧ z = w + (j : ℤ) • v := by
  obtain ⟨k, hk⟩ := primitive_height_surjective v hv 1
  change det v k = 1 at hk
  let T := S.filter (fun z => det v z = t)
  let F := T.image (fun z => det z k)
  have hT : T.Nonempty := hne
  have hF : F.Nonempty := Finset.image_nonempty.mpr hT
  let a := F.min' hF
  let b := F.max' hF
  have hab : a ≤ b := Finset.min'_le_max' F hF
  obtain ⟨w, hwT, hwa⟩ := Finset.mem_image.mp (Finset.min'_mem F hF)
  obtain ⟨u, huT, hub⟩ := Finset.mem_image.mp (Finset.max'_mem F hF)
  have hw : w ∈ S ∧ det v w = t := Finset.mem_filter.mp hwT
  have hu : u ∈ S ∧ det v u = t := Finset.mem_filter.mp huT
  have hudiff : u = w + (b - a) • v := by
    simpa only [hwa, hub] using row_difference v k w u hk (hu.2.trans hw.2.symm)
  have hfull : F = Finset.Icc a b := by
    ext r
    constructor
    · intro hr
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le F r hr, Finset.le_max' F r hr⟩
    · intro hr
      rcases Finset.mem_Icc.mp hr with ⟨har, hrb⟩
      have hmem : w + (r - a) • v ∈ S :=
        row_intermediate_mem S hS v w (b - a) (r - a) hw.1 (hudiff ▸ hu.1)
          (by omega) (by omega)
      have hrow : det v (w + (r - a) • v) = t := by
        change height v (w + (r - a) • v) = t
        rw [height_add, height_zsmul, height_self, mul_zero, add_zero]
        exact hw.2
      exact Finset.mem_image.mpr ⟨w + (r - a) • v,
        Finset.mem_filter.mpr ⟨hmem, hrow⟩, by rw [row_coordinate_add v k w hk, hwa]; ring⟩
  have hinj : Set.InjOn (fun z => det z k) (T : Set Lattice) := by
    intro z hz u hu hzu
    change det z k = det u k at hzu
    have hzrow := (Finset.mem_filter.mp hz).2
    have hurow := (Finset.mem_filter.mp hu).2
    rw [row_basis_decomposition v k z hk, row_basis_decomposition v k u hk, hzu, hzrow, hurow]
  have hcard : (T.card : ℤ) = b + 1 - a := by
    rw [← Finset.card_image_of_injOn hinj]
    change (F.card : ℤ) = b + 1 - a
    rw [hfull, Int.card_Icc_of_le a b (by omega)]
  refine ⟨w, hw.2, ?_⟩
  intro z
  constructor
  · intro hz
    have hzT : z ∈ T := Finset.mem_filter.mpr hz
    have hzF : det z k ∈ F := Finset.mem_image.mpr ⟨z, hzT, rfl⟩
    have haz : a ≤ det z k := Finset.min'_le F _ hzF
    have hzb : det z k ≤ b := Finset.le_max' F _ hzF
    refine ⟨(det z k - a).toNat, ?_, ?_⟩
    · have hcast : ((det z k - a).toNat : ℤ) = det z k - a := Int.toNat_of_nonneg (by omega)
      change (det z k - a).toNat < T.card
      omega
    · rw [Int.toNat_of_nonneg (by omega)]
      simpa only [hwa] using row_difference v k w z hk (hz.2.trans hw.2.symm)
  · rintro ⟨j, hj, rfl⟩
    have hjZ : (j : ℤ) < T.card := by exact_mod_cast hj
    have hmem := row_intermediate_mem S hS v w (b - a) j hw.1 (hudiff ▸ hu.1)
      (by omega) (by omega)
    refine ⟨hmem, ?_⟩
    change height v (w + (j : ℤ) • v) = t
    rw [height_add, height_zsmul, height_self, mul_zero, add_zero]
    exact hw.2

end ConvexNivat
