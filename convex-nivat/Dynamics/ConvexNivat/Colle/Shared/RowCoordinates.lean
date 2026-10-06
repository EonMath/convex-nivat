import ConvexNivat.Colle.Shared.Definitions
import ConvexNivat.Geometry.Triangulation.Coordinates
import ConvexNivat.Geometry.Basic

namespace ConvexNivat.Colle
noncomputable section

private theorem row_expansion (v e z : Lattice) (he : det v e = 1) :
    z = det z e • v + det v z • e := by
  change v.1 * e.2 - v.2 * e.1 = 1 at he
  apply Prod.ext
  · change z.1 = (z.1 * e.2 - z.2 * e.1) * v.1 +
        (v.1 * z.2 - v.2 * z.1) * e.1
    linear_combination -z.1 * he
  · change z.2 = (z.1 * e.2 - z.2 * e.1) * v.2 +
        (v.1 * z.2 - v.2 * z.1) * e.2
    linear_combination -z.2 * he

private theorem det_coordinates_left (v e : Lattice) (he : det v e = 1)
    (s r : ℤ) : det (s • v + r • e) e = s := by
  change v.1 * e.2 - v.2 * e.1 = 1 at he
  change (s * v.1 + r * e.1) * e.2 - (s * v.2 + r * e.2) * e.1 = s
  linear_combination s * he

private theorem det_coordinates_right (v e : Lattice) (he : det v e = 1)
    (s r : ℤ) : det v (s • v + r • e) = r := by
  change v.1 * e.2 - v.2 * e.1 = 1 at he
  change v.1 * (s * v.2 + r * e.2) - v.2 * (s * v.1 + r * e.1) = r
  linear_combination r * he

theorem primitive_row_coordinates (v : Lattice) (hv : Primitive v) :
    (∃ e : Lattice, det v e = 1 ∧ ∀ z : Lattice,
      ∃! sr : ℤ × ℤ, z = sr.1 • v + sr.2 • e ∧ sr.2 = det v z) ∧
    (∀ p q : Lattice, det v p = det v q ↔ ∃ k : ℤ, q = p + k • v) ∧
    (∀ p : Lattice, ∀ a b : ℤ, a ≤ b → ∀ z : Lattice,
      embed z ∈ segment ℝ (embed (p + a • v)) (embed (p + b • v)) ↔
        ∃ k : ℤ, a ≤ k ∧ k ≤ b ∧ z = p + k • v) := by
  obtain ⟨e, he⟩ := primitive_height_surjective v hv 1
  change det v e = 1 at he
  have hrow (p q : Lattice) : det v p = det v q ↔ ∃ k : ℤ, q = p + k • v := by
    constructor
    · intro hpq
      refine ⟨det q e - det p e, ?_⟩
      calc
        q = det q e • v + det v q • e := row_expansion v e q he
        _ = (det p e • v + det v p • e) + (det q e - det p e) • v := by
          rw [hpq, sub_smul]
          abel
        _ = p + (det q e - det p e) • v := by
          exact congrArg (fun r => r + (det q e - det p e) • v)
            (row_expansion v e p he).symm
    · rintro ⟨k, rfl⟩
      change height v p = height v (p + k • v)
      rw [height_add, height_zsmul, height_self, mul_zero, add_zero]
  refine ⟨⟨e, he, ?_⟩, hrow, ?_⟩
  · intro z
    refine ⟨(det z e, det v z), ⟨row_expansion v e z he, rfl⟩, ?_⟩
    intro sr hsr
    apply Prod.ext
    · have hh := congrArg (fun q => det q e) hsr.1
      rw [det_coordinates_left v e he] at hh
      exact hh.symm
    · exact hsr.2
  · intro p a b hab z
    rcases PolygonTriangulation.real_determinant_and_embedding_algebra with
      ⟨haddl, haddr, hsml, hsmr, hself, _, hemb, _⟩
    have hzsmul (n : ℤ) (u : Lattice) : embed (n • u) = (n : ℝ) • embed u := by
      ext <;> simp [embed, smul_eq_mul]
    constructor
    · intro hz
      rw [segment_eq_image] at hz
      obtain ⟨t, ht, hz⟩ := hz
      have hzline : embed z = embed p + ((1-t)*(a:ℝ)+t*(b:ℝ)) • embed v := by
        calc
          embed z = (1-t) • embed (p+a•v) + t • embed (p+b•v) := hz.symm
          _ = _ := by
            rw [embed_add, embed_add, hzsmul, hzsmul]
            ext <;> simp [smul_eq_mul] <;> ring
      have hr := congrArg (realDet (embed v)) hzline
      rw [hemb, haddr, hsmr, hself, mul_zero, add_zero, hemb] at hr
      have hrowz : det v p = det v z := by exact_mod_cast hr.symm
      obtain ⟨k, hk⟩ := (hrow p z).mp hrowz
      have hcoord := congrArg (fun q => realDet q (embed e)) hzline
      simp only [hk, embed_add, hzsmul, haddl, hsml, hemb, he, Int.cast_one,
        mul_one] at hcoord
      have hkr : (k:ℝ) = (1-t)*(a:ℝ)+t*(b:ℝ) := by linarith
      have habR : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
      have hka : (a:ℝ) ≤ (k:ℝ) := by
        nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr habR)]
      have hkb : (k:ℝ) ≤ (b:ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr habR)]
      exact ⟨k, by exact_mod_cast hka, by exact_mod_cast hkb, hk⟩
    · rintro ⟨k, hak, hkb, rfl⟩
      by_cases heq : a=b
      · have hka : k=a := by omega
        subst k
        subst b
        exact left_mem_segment ℝ _ _
      have habR : (a:ℝ) < (b:ℝ) := by exact_mod_cast (lt_of_le_of_ne hab heq)
      rw [segment_eq_image]
      refine ⟨((k:ℝ)-(a:ℝ))/((b:ℝ)-(a:ℝ)), ?_, ?_⟩
      · constructor
        · exact div_nonneg (by exact_mod_cast sub_nonneg.mpr hak) (by linarith)
        · apply (div_le_one (by linarith : 0 < (b:ℝ)-(a:ℝ))).mpr
          exact_mod_cast sub_le_sub_right hkb a
      · rw [embed_add, embed_add, embed_add, hzsmul, hzsmul, hzsmul]
        ext <;> simp [smul_eq_mul]
        all_goals field_simp [ne_of_gt (sub_pos.mpr habR)]
        all_goals ring


end
end ConvexNivat.Colle
