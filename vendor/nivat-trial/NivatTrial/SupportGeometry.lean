import NivatTrial.QuotientSupport

/-! The complete support bound for the projector blocks in Lemma 5.2. -/

namespace NivatTrial.SupportGeometry

open NivatTrial.Algebra NivatTrial.Divisibility NivatTrial.CoefficientField
open NivatTrial.QuotientFactors NivatTrial.QuotientIdeals NivatTrial.QuotientSupport
open NivatTrial.Zonotope
open scoped Classical Pointwise

noncomputable section

theorem real_coordinates (v w z : G) (hdet : det v w ≠ 0) :
    (longitudinalCoordinate v w z : ℝ) • embed v +
      (transverseCoordinate v w z : ℝ) • embed w = embed z := by
  have hd : (det v w : ℝ) ≠ 0 := by exact_mod_cast hdet
  apply Prod.ext <;>
    simp only [longitudinalCoordinate, transverseCoordinate, Rat.cast_div,
      Rat.cast_intCast, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      embed, smul_eq_mul] <;>
    field_simp [hd] <;> simp [det] <;> ring

variable {ι : Type*} [Fintype ι]

theorem block_coefficients (v : ι → G) (d : ι → ℕ) (i j : ι)
    (hdet : det (v i) (-v j) ≠ 0) {e : G}
    (he : e ∈ blockFinset (v i) (-v j) hdet (d i) (d j)) :
    ∃ a b : ℝ, (0 ≤ a ∧ a ≤ d i) ∧ (0 ≤ b ∧ b ≤ d j) ∧
      a • embed (v i) - b • embed (v j) = embed e := by
  have hb := blockFinset_coordinate_bounds (v i) (-v j) hdet (d i) (d j) he
  refine ⟨longitudinalCoordinate (v i) (-v j) e,
    transverseCoordinate (v i) (-v j) e,
    ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2.1.le⟩,
    ⟨by exact_mod_cast hb.2.2.1, by exact_mod_cast hb.2.2.2.le⟩, ?_⟩
  simpa only [embed_neg, smul_neg, sub_eq_add_neg] using real_coordinates (v i) (-v j) e hdet

/-- Every exponent of `Eᵢⱼ Yᵉ` is in the actual real difference zonotope.
The missing positive `i` segment and negative `j` segment are filled exactly
by the corresponding coefficients of the fundamental-domain block. -/
theorem projector_support (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) (hij : i ≠ j)
    (hdet : det (v i) (-v j) ≠ 0) (e : G)
    (he : e ∈ blockFinset (v i) (-v j) hdet (S i).card (S j).card)
    (z : G) (hz : z ∈ (projector v S i j * AddMonoidAlgebra.single e 1).coeff.support) :
    embed z ∈ zonotope (fun k => (S k).card • v k) -
      zonotope (fun k => (S k).card • v k) := by
  obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp
    (AddMonoidAlgebra.support_coeff_mul_single_subset (projector v S i j) 1 e hz)
  subst z
  obtain ⟨x, hx, y, hy, hu_eq⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset (aCofactor v S i) (cCofactor v S j) hu)
  subst u
  obtain ⟨a, ha, hax⟩ := support_prod_directional v (fun k => aFactor (v k) (S k))
    (fun k => (S k).card) (fun k _ hk => aFactor_support (v k) (S k) hk)
    (Finset.univ.erase i) x hx
  obtain ⟨b, hb, hby⟩ := support_prod_directional (fun k => -v k)
    (fun k => cFactor (v k) (S k)) (fun k => (S k).card)
    (fun k _ hk => cFactor_support (v k) (S k) hk) (Finset.univ.erase j) y hy
  obtain ⟨s, t, hs, ht, hest⟩ := block_coefficients v (fun k => (S k).card) i j hdet he
  apply (scaled_diff_mem v (fun k => (S k).card) _).mpr
  refine ⟨fun k => (a k - b k) + ((if k = i then s else 0) - (if k = j then t else 0)), ?_, ?_⟩
  · intro k
    have hak := ha k
    have hbk := hb k
    by_cases hki : k = i
    · subst k
      simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ite_false] at hak
      simp only [ite_true, if_neg hij]
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, if_pos hij] at hbk
      constructor <;> linarith
    · by_cases hkj : k = j
      · subst k
        simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ite_false] at hbk
        simp only [if_neg hki, ite_true]
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, if_pos hki] at hak
        constructor <;> linarith
      · simp only [if_neg hki, if_neg hkj]
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, if_pos hki] at hak
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, if_pos hkj] at hbk
        constructor <;> linarith
  · change coeffPoint v (fun k => (a k - b k) +
      ((if k = i then s else 0) - (if k = j then t else 0))) = _
    rw [coeffPoint_add, coeffPoint_sub, hax]
    have hby' : coeffPoint v b = -embed y := by
      have hn : coeffPoint (fun k => -v k) b = -coeffPoint v b := by
        simp [coeffPoint, embed_neg, smul_neg, Finset.sum_neg_distrib]
      rw [hn] at hby
      exact eq_neg_of_add_eq_zero_left (by rw [← hby]; abel)
    have hst : coeffPoint v (fun k => (if k = i then s else 0) -
        (if k = j then t else 0)) = embed e := by
      simpa [coeffPoint, sub_smul, Finset.sum_sub_distrib] using hest
    rw [hby', hst, embed_add, embed_add]
    abel

end

end NivatTrial.SupportGeometry
