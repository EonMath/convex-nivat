import ConvexNivat.ReductionRows
import ConvexNivat.CorePatterns
namespace ConvexNivat
private theorem d_basis (u v z : Lattice) (h : det u v = 1) :
    z = det z v • u + det u z • v := by
  have he : det u v • z = det z v • u + det u z • v := by
    ext <;> simp [det] <;> ring
  simpa only [h, one_smul] using he
private theorem d_embed_add (z w : Lattice) : embed (z+w) = embed z+embed w := by
  ext <;> simp [embed]
private theorem d_embed_smul (r : ℤ) (z : Lattice) : embed (r • z) = (r : ℝ) • embed z := by
  ext <;> simp [embed, smul_eq_mul]
private theorem d_row_bound (u : Lattice) (hu : Primitive u)
    (B : Finset Lattice) (hB : B.Nonempty) (hconvex : LatticeConvex B)
    (n : ℕ)
    (hlo : n ≤ (B.filter (fun z => det u z = rowMinimum u B hB)).card)
    (hhi : n ≤ (B.filter (fun z => det u z = rowMaximum u B hB)).card)
    (t : ℤ) (hmin : rowMinimum u B hB ≤ t) (hmax : t ≤ rowMaximum u B hB) :
    n-1 ≤ (B.filter (fun z => det u z = t)).card := by
  classical
  by_cases hn : n ≤ 1
  · omega
  have hnpos : 0 < n := by omega
  have hL : (B.filter (fun z => det u z = rowMinimum u B hB)).Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hH : (B.filter (fun z => det u z = rowMaximum u B hB)).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨wL, hwL, henumL⟩ := row_is_consecutive u hu B hconvex _ hL
  obtain ⟨wH, hwH, henumH⟩ := row_is_consecutive u hu B hconvex _ hH
  have hmemL : wL ∈ B := ((henumL wL).mpr ⟨0, by omega, by simp⟩).1
  have hmemH : wH ∈ B := ((henumH wH).mpr ⟨0, by omega, by simp⟩).1
  have hrightL : wL + ((n-1 : ℕ) : ℤ) • u ∈ B :=
    ((henumL _).mpr ⟨n-1, by omega, rfl⟩).1
  have hrightH : wH + ((n-1 : ℕ) : ℤ) • u ∈ B :=
    ((henumH _).mpr ⟨n-1, by omega, rfl⟩).1
  by_cases hrow : rowMinimum u B hB = rowMaximum u B hB
  · have ht : t = rowMinimum u B hB := by omega
    rw [ht]
    omega
  obtain ⟨v, hv⟩ := primitive_height_surjective u hu 1
  change det u v = 1 at hv
  let lo := rowMinimum u B hB
  let hi := rowMaximum u B hB
  let rho : ℝ := ((t : ℝ) - lo) / ((hi : ℝ) - lo)
  have hwidth : 0 < (hi : ℝ) - lo := by
    have : lo < hi := by dsimp [lo, hi]; omega
    exact_mod_cast sub_pos.mpr this
  have hrho0 : 0 ≤ rho := div_nonneg (by exact_mod_cast sub_nonneg.mpr hmin) hwidth.le
  have hrho1 : rho ≤ 1 := (div_le_one₀ hwidth).mpr (by exact_mod_cast sub_le_sub_right hmax lo)
  let c : ℝ := (1-rho) * (det wL v : ℝ) + rho * (det wH v : ℝ)
  let L : RealPlane := (1-rho) • embed wL + rho • embed wH
  let R : RealPlane := (1-rho) • embed (wL + ((n-1 : ℕ) : ℤ) • u) +
    rho • embed (wH + ((n-1 : ℕ) : ℤ) • u)
  have hrhosum : (1-rho)+rho=1 := by ring
  have hLm : L ∈ windowHull B := (convex_convexHull ℝ (embed '' (B : Set Lattice)))
    (subset_convexHull ℝ _ ⟨wL,hmemL,rfl⟩)
    (subset_convexHull ℝ _ ⟨wH,hmemH,rfl⟩) (by linarith) hrho0 hrhosum
  have hRm : R ∈ windowHull B := (convex_convexHull ℝ (embed '' (B : Set Lattice)))
    (subset_convexHull ℝ _ ⟨_,hrightL,rfl⟩)
    (subset_convexHull ℝ _ ⟨_,hrightH,rfl⟩) (by linarith) hrho0 hrhosum
  have hLcoord : L = c • embed u + (t : ℝ) • embed v := by
    have hwl := congrArg embed (d_basis u v wL hv)
    have hwh := congrArg embed (d_basis u v wH hv)
    simp only [d_embed_add, d_embed_smul, hwL, hwH] at hwl hwh
    have he : (1-rho) * (lo : ℝ) + rho * (hi : ℝ) = t := by
      dsimp [rho]
      field_simp
      ring
    dsimp [L]
    rw [hwl,hwh]
    change (1-rho) • ((det wL v : ℝ) • embed u + (lo : ℝ) • embed v) +
      rho • ((det wH v : ℝ) • embed u + (hi : ℝ) • embed v) = _
    simp only [smul_add, smul_smul]
    rw [add_add_add_comm, ← add_smul, ← add_smul, he]
  have hRcoord : R = (c + (n-1 : ℕ)) • embed u + (t : ℝ) • embed v := by
    have he : R = L + ((n-1 : ℕ) : ℝ) • embed u := by
      dsimp only [R, L]
      simp only [d_embed_add,d_embed_smul,Int.cast_natCast,smul_add,smul_smul]
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] <;> ring
    calc
      _ = L + ((n-1 : ℕ) : ℝ) • embed u := he
      _ = _ := by
        rw [hLcoord]
        ext <;> simp [smul_eq_mul] <;> ring
  let f : Fin (n-1) → Lattice := fun j => (⌈c⌉ + (j : ℕ)) • u + t • v
  have hmaps : ∀ j, f j ∈ B.filter (fun z => det u z = t) := by
    intro j
    have hj0 : 0 ≤ (j.val : ℝ) := by positivity
    have hjlt : (j.val : ℝ) < ((n-1 : ℕ) : ℝ) := by exact_mod_cast j.isLt
    have hj1 : (j.val : ℝ) ≤ ((n-1 : ℕ) : ℝ) - 1 := by
      have hle : j.val + 1 ≤ n-1 := by omega
      have : (j.val : ℝ) + 1 ≤ ((n-1 : ℕ) : ℝ) := by exact_mod_cast hle
      linarith
    have hn1 : (0 : ℝ) < (n-1 : ℕ) := by exact_mod_cast (show 0 < n-1 by omega)
    have hc0 := Int.le_ceil c
    have hc1 := Int.ceil_lt_add_one c
    let α : ℝ := ((⌈c⌉ : ℝ) + (j.val : ℝ) - c) / (n-1 : ℕ)
    have hα0 : 0 ≤ α := div_nonneg (by linarith) hn1.le
    have hα1 : α ≤ 1 := (div_le_one₀ hn1).mpr (by linarith)
    have hm := (convex_convexHull ℝ (embed '' (B : Set Lattice))) hLm hRm
      (sub_nonneg.mpr hα1) hα0 (show (1-α)+α=1 by ring)
    have heq : (1-α) • L + α • R = embed (f j) := by
      rw [hLcoord,hRcoord]
      dsimp [f]
      simp only [d_embed_add,d_embed_smul,Int.cast_add,Int.cast_natCast]
      have he : (1-α)*c + α*(c+(n-1 : ℕ)) = (⌈c⌉ : ℝ) + j.val := by
        dsimp [α]
        field_simp
        ring
      simp only [smul_add, smul_smul]
      rw [add_add_add_comm, ← add_smul, ← add_smul,he]
      have ht : (1-α)*(t : ℝ)+α*(t : ℝ)=(t : ℝ) := by ring
      rw [ht]
    refine Finset.mem_filter.mpr ⟨(hconvex _).mp (heq ▸ hm), ?_⟩
    change height u (f j) = t
    dsimp [f]
    rw [height_add,height_zsmul,height_zsmul,height_self,mul_zero,zero_add]
    change t * det u v = t
    rw [hv,mul_one]
  have hinj : Function.Injective f := by
    intro i j he
    have he' := congrArg (fun z => det z v) he
    have hd : ∀ j, det (f j) v = ⌈c⌉ + (j.val : ℤ) := by
      intro j
      have hx : det (f j) v = (⌈c⌉ + (j.val : ℤ)) * det u v + t * det v v := by
        dsimp [f,det]
        ring
      rw [hx,hv]
      have hvv : det v v = 0 := by dsimp [det]; ring
      simp [hvv]
    rw [hd,hd] at he'
    apply Fin.ext
    omega
  have hc := Finset.card_le_card (show (Finset.univ.image f) ⊆ B.filter (fun z => det u z=t) by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j,hj,rfl⟩
    exact hmaps j)
  simpa only [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin] using hc
theorem intermediate_row_cardinality (u : Lattice) (hu : Primitive u)
    (B : Finset Lattice) (hB : B.Nonempty) (hconvex : LatticeConvex B)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (hsmall : (extremeRow σ u B hB).card ≤ (extremeRow (-σ) u B hB).card)
    (t : ℤ) (hmin : rowMinimum u B hB ≤ t) (hmax : t ≤ rowMaximum u B hB) :
    (extremeRow σ u B hB).card - 1 ≤ (B.filter (fun z => det u z = t)).card := by
  rcases hσ with rfl | rfl
  · apply d_row_bound u hu B hB hconvex _ _ _ t hmin hmax
    · simpa [extremeRow] using hsmall
    · simp [extremeRow]
  · apply d_row_bound u hu B hB hconvex _ _ _ t hmin hmax
    · simp [extremeRow]
    · simpa [extremeRow] using hsmall
end ConvexNivat
