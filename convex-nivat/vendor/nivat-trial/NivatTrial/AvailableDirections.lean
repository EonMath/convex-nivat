import NivatTrial.Geometry

/-! The available-direction lemma, using a rational slope order instead of angles.
All directions have been oriented toward a common interior vector g. -/

namespace NivatTrial.AvailableDirections

open NivatTrial.Geometry
open scoped Classical

def score (v g : Lattice) : ℚ :=
  ((v.1 : ℚ) * g.1 + (v.2 : ℚ) * g.2) / (det v g : ℚ)

theorem norm_sq_pos {v g : Lattice} (hv : 0 < det v g) :
    0 < (g.1 : ℚ)^2 + (g.2 : ℚ)^2 := by
  have hg : g.1 ≠ 0 ∨ g.2 ≠ 0 := by
    by_contra h
    push_neg at h
    simp [det, h.1, h.2] at hv
  rcases hg with h | h
  · have h' : (g.1 : ℚ) ≠ 0 := by exact_mod_cast h
    nlinarith [sq_pos_of_ne_zero h', sq_nonneg (g.2 : ℚ)]
  · have h' : (g.2 : ℚ) ≠ 0 := by exact_mod_cast h
    nlinarith [sq_pos_of_ne_zero h', sq_nonneg (g.1 : ℚ)]

theorem score_lt_iff {v w g : Lattice} (hv : 0 < det v g) (hw : 0 < det w g) :
    score v g < score w g ↔ 0 < det v w := by
  have hv' : (0 : ℚ) < det v g := by exact_mod_cast hv
  have hw' : (0 : ℚ) < det w g := by exact_mod_cast hw
  have hn := norm_sq_pos hv
  have hid : ((w.1 : ℚ)*g.1+(w.2 : ℚ)*g.2)*(det v g : ℚ) -
      ((v.1 : ℚ)*g.1+(v.2 : ℚ)*g.2)*(det w g : ℚ) =
      ((g.1 : ℚ)^2+(g.2 : ℚ)^2)*(det v w : ℚ) := by
    simp [det]
    ring
  rw [score, score, div_lt_div_iff₀ hv' hw']
  constructor
  · intro h
    have hd : (0 : ℚ) < det v w := by nlinarith
    exact_mod_cast hd
  · intro h
    have hd : (0 : ℚ) < det v w := by exact_mod_cast h
    have hm := mul_pos hn hd
    nlinarith

theorem score_ne_of_det_ne {v w g : Lattice} (hv : 0 < det v g)
    (hw : 0 < det w g) (hvw : det v w ≠ 0) : score v g ≠ score w g := by
  rcases lt_or_gt_of_ne hvw with h | h
  · have h' : 0 < det w v := by rw [det_swap]; omega
    exact ne_of_gt ((score_lt_iff hw hv).mpr h')
  · exact ne_of_lt ((score_lt_iff hv hw).mpr h)

/-- There is a direction which moves one unresolved component to its far side,
fixes another component, and moves all other unresolved components to their known side. -/
theorem available_direction {ι : Type*} [Fintype ι] [Nontrivial ι]
    (v : ι → Lattice) (g : Lattice) (hpos : ∀ i, 0 < det (v i) g)
    (hdet : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (O : Finset ι) (hO : O.Nonempty) :
    ∃ b ∈ O, ∃ c : ι, c ≠ b ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      det (v b) (ε • v c) < 0 ∧
      ∀ j ∈ O, j ≠ b → j ≠ c → 0 < det (v j) (ε • v c) := by
  classical
  obtain ⟨b, hb, hmin⟩ := O.exists_min_image (fun i => score (v i) g) hO
  by_cases hsingle : O = {b}
  · obtain ⟨c, hcb⟩ := exists_ne b
    have hbc := hdet b c hcb.symm
    rcases lt_or_gt_of_ne hbc with hneg | hplus
    · refine ⟨b, hb, c, hcb, 1, Or.inl rfl, by simpa using hneg, ?_⟩
      intro j hj hjb hjc
      have : j = b := by simpa [hsingle] using hj
      exact (hjb this).elim
    · refine ⟨b, hb, c, hcb, -1, Or.inr rfl, ?_, ?_⟩
      · simpa using neg_neg_of_pos hplus
      · intro j hj hjb hjc
        have : j = b := by simpa [hsingle] using hj
        exact (hjb this).elim
  · have hother : ∃ j ∈ O, j ≠ b := by
      by_contra hn
      apply hsingle
      push_neg at hn
      ext j
      simp only [Finset.mem_singleton]
      exact ⟨fun hj => hn j hj, fun he => he ▸ hb⟩
    let C := Finset.univ.filter (fun i => score (v b) g < score (v i) g)
    have hC : C.Nonempty := by
      obtain ⟨j, hj, hjb⟩ := hother
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact lt_of_le_of_ne (hmin j hj)
        (score_ne_of_det_ne (hpos b) (hpos j) (hdet b j hjb.symm))
    obtain ⟨c, hc, hcmin⟩ := C.exists_min_image (fun i => score (v i) g) hC
    have hbc : score (v b) g < score (v c) g := (Finset.mem_filter.mp hc).2
    have hcb : c ≠ b := by intro he; subst c; exact lt_irrefl _ hbc
    refine ⟨b, hb, c, hcb, -1, Or.inr rfl, ?_, ?_⟩
    · have hd := (score_lt_iff (hpos b) (hpos c)).mp hbc
      simpa using neg_neg_of_pos hd
    · intro j hj hjb hjc
      have hbj : score (v b) g < score (v j) g :=
        lt_of_le_of_ne (hmin j hj)
          (score_ne_of_det_ne (hpos b) (hpos j) (hdet b j hjb.symm))
      have hjC : j ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbj⟩
      have hcj : score (v c) g < score (v j) g :=
        lt_of_le_of_ne (hcmin j hjC)
          (score_ne_of_det_ne (hpos c) (hpos j) (hdet c j hjc.symm))
      have hd := (score_lt_iff (hpos c) (hpos j)).mp hcj
      simpa [det_swap (v j) (v c)] using hd

end NivatTrial.AvailableDirections
