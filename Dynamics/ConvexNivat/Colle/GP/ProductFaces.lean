import ConvexNivat.Colle.GP.Definitions
import ConvexNivat.Geometry.ZonotopeBasic

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

private theorem product_dot_sum {m : ℕ} (v : Fin m → RealPlane)
    (t : Fin m → ℝ) (n : RealPlane) :
    realDot (∑ i, t i • v i) n = ∑ i, t i * realDot (v i) n := by
  simp only [realDot, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem reflected_factor_hull_integral_zonotope (m : ℕ) (h : Fin m → Lattice)
    (Z : IntegralZonotope m) (hZ : ∀ i, -h i = (Z.degree i : ℤ) • Z.direction i) :
    reflectedFactorHull m h = Z.carrier := by
  have he (i : Fin m) : embed (-h i) = (Z.degree i : ℝ) • embed (Z.direction i) := by
    rw [hZ i]
    ext <;> simp [embed, zsmul_eq_mul]
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨fun i => t i * (Z.degree i : ℝ), fun i => ⟨mul_nonneg (ht i).1
      (Nat.cast_nonneg _), ?_⟩, ?_⟩
    · nlinarith [(ht i).2, Nat.cast_nonneg (α := ℝ) (Z.degree i)]
    · simpa only [he, smul_smul] using hx
  · rintro ⟨t, ht, hx⟩
    have hp (i : Fin m) : (0 : ℝ) < Z.degree i := Nat.cast_pos.mpr (Z.degree_pos i)
    refine ⟨fun i => t i / (Z.degree i : ℝ), fun i =>
      ⟨div_nonneg (ht i).1 (hp i).le, (div_le_one (hp i)).mpr (ht i).2⟩, ?_⟩
    simpa only [he, smul_smul, div_mul_cancel₀ _ (hp _).ne'] using hx

theorem zonotope_exposed_face_parameter_classification (m : ℕ) (h : Fin m → Lattice)
    (n : RealPlane) (hn : n ≠ 0) :
    {x | x ∈ reflectedFactorHull m h ∧
      ∀ y ∈ reflectedFactorHull m h, realDot x n ≤ realDot y n} =
    {x | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
      (∀ i, realDot (embed (-h i)) n < 0 → t i = 1) ∧
      (∀ i, 0 < realDot (embed (-h i)) n → t i = 0) ∧
      x = ∑ i, t i • embed (-h i)} := by
  classical
  let c : Fin m → ℝ := fun i => realDot (embed (-h i)) n
  let s : Fin m → ℝ := fun i => if c i < 0 then 1 else 0
  have hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1 := by
    intro i
    dsimp [s]
    split_ifs <;> norm_num
  have hlow (t : Fin m → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (i : Fin m) :
      s i * c i ≤ t i * c i := by
    dsimp [s]
    split_ifs with hc
    · nlinarith [(ht i).2]
    · nlinarith [(ht i).1, le_of_not_gt hc]
  ext x
  constructor
  · rintro ⟨⟨t, ht, hx⟩, hmin⟩
    have hmin' := hmin (∑ i, s i • embed (-h i)) ⟨s, hs, rfl⟩
    rw [hx, product_dot_sum, product_dot_sum] at hmin'
    change (∑ i, t i * c i) ≤ ∑ i, s i * c i at hmin'
    have he : (∑ i, s i * c i) = ∑ i, t i * c i :=
      le_antisymm (Finset.sum_le_sum fun i _ => hlow t ht i) hmin'
    have hi : ∀ i, s i * c i = t i * c i :=
      fun i => (Finset.sum_eq_sum_iff_of_le (fun j _ => hlow t ht j)).mp he i
        (Finset.mem_univ i)
    refine ⟨t, ht, ?_, ?_, hx⟩
    · intro i hc
      have hh := hi i
      dsimp [s] at hh
      rw [if_pos hc] at hh
      nlinarith
    · intro i hc
      have hh := hi i
      dsimp [s] at hh
      rw [if_neg (not_lt_of_ge hc.le)] at hh
      nlinarith
  · rintro ⟨t, ht, hneg, hpos, hx⟩
    refine ⟨⟨t, ht, hx⟩, ?_⟩
    rintro y ⟨u, hu, rfl⟩
    rw [hx, product_dot_sum, product_dot_sum]
    apply Finset.sum_le_sum
    intro i hi
    rcases lt_trichotomy (c i) 0 with hc | hc | hc
    · rw [hneg i hc]
      change 1 * c i ≤ u i * c i
      nlinarith [(hu i).2]
    · change t i * c i ≤ u i * c i
      simp [hc]
    · rw [hpos i hc]
      change 0 * c i ≤ u i * c i
      nlinarith [(hu i).1]

theorem nonparallel_factor_unique_tangent (m : ℕ) (h : Fin m → Lattice)
    (hpair : Pairwise (fun i j => Nonparallel (h i) (h j)))
    (n : RealPlane) (hn : n ≠ 0) :
    ∀ i j, realDot (embed (h i)) n = 0 → realDot (embed (h j)) n = 0 → i = j := by
  intro i j hi hj
  by_contra hij
  have hd : (det (h i) (h j) : ℝ) ≠ 0 := by exact_mod_cast hpair hij
  apply hn
  apply Prod.ext
  · have he : (det (h i) (h j) : ℝ) * n.1 = 0 := by
      dsimp [realDot, embed] at hi hj
      dsimp [det]
      push_cast
      nlinarith [congrArg (fun t : ℝ => t * ((h j).2 : ℝ)) hi,
        congrArg (fun t : ℝ => t * ((h i).2 : ℝ)) hj]
    exact (mul_eq_zero.mp he).resolve_left hd
  · have he : (det (h i) (h j) : ℝ) * n.2 = 0 := by
      dsimp [realDot, embed] at hi hj
      dsimp [det]
      push_cast
      nlinarith [congrArg (fun t : ℝ => t * ((h j).1 : ℝ)) hi,
        congrArg (fun t : ℝ => t * ((h i).1 : ℝ)) hj]
    exact (mul_eq_zero.mp he).resolve_left hd

end
end ConvexNivat.Colle
