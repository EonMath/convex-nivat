import NivatTrial.ColleHalfStripEnvelope
import NivatTrial.ColleEnvelopeExpansion

/-! Exact geometry of one forward expansion. Long faces parallel to u
make the two translated windows overlap on every real cross-section.
Consequently the directional hull creates no points beyond their union,
even when u is not primitive. -/

namespace NivatTrial.ColleStepExpansionGeometry

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.RegionGeometry
open NivatTrial.ColleGenerating NivatTrial.ColleEnvelopeGeometry
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleHalfStripEnvelope NivatTrial.ColleEnvelopeTranslation
open NivatTrial.ColleEnvelopeExpansion NivatTrial.Nonexpansive
open scoped Classical
noncomputable section

theorem mem_stepExpansion_iff (D T : Finset Lattice) (u z : Lattice)
    (hT : T.Nonempty) :
    z ∈ stepExpansion D (T : Set Lattice) u ↔
      ∀ d ∈ D, lowerSupport T d + min 0 (det d u) ≤ det d z := by
  constructor
  · intro hz d hd
    apply hz d hd
    intro w hw
    rcases hw with hw | hw
    · have hb := lowerSupport_le hw d
      have hm := min_le_left (0:ℤ) (det d u)
      omega
    · have hb := lowerSupport_le (show w-u ∈ T from hw) d
      rw [det_sub_right] at hb
      have hm := min_le_right (0:ℤ) (det d u)
      omega
  · intro hz d hd t ht
    obtain ⟨w, hw, he⟩ := lowerSupport_attained T hT d
    have ht0 := ht w (Or.inl hw)
    have ht1 := ht (w+u) (Or.inr (show w+u ∈ recenter (T : Set Lattice) (-u) by
      simpa [recenter] using hw))
    rw [he] at ht0
    rw [det_add_right, he] at ht1
    have hbound := hz d hd
    by_cases hdu : 0 ≤ det d u
    · rw [min_eq_left hdu] at hbound
      omega
    · rw [min_eq_right (by omega : det d u ≤ 0)] at hbound
      omega

/-- A long-faced envelope and its one-step translate already have a convex,
directionally closed union. -/
theorem stepExpansion_eq_union (D T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hclosed : IsEnvelope D (T : Set Lattice))
    (hfaces : LongFaces D (T : Set Lattice))
    (hu0 : u ≠ 0) (hu : u ∈ D) (hnu : -u ∈ D) :
    stepExpansion D (T : Set Lattice) u =
      (T : Set Lattice) ∪ recenter (T : Set Lattice) (-u) := by
  apply Set.Subset.antisymm _ (subset_supportHull D _)
  intro z hz
  have hzsupport := (mem_stepExpansion_iff D T u z hT).mp hz
  have hzforward : ∀ d ∈ D, 0 ≤ det d u → lowerSupport T d ≤ det d z := by
    intro d hd hdu
    simpa only [min_eq_left hdu, add_zero] using hzsupport d hd
  obtain ⟨q, hq, hqu, hqz⟩ :=
    exists_segment_in_realEnvelope D T u hT hfaces hu hnu z hzforward
  obtain ⟨t, ht⟩ := exists_real_parallel u hu0 (embed z) q hqz.symm
  have hmem (w : Lattice) (hw : embed w ∈ realEnvelope D (lowerSupport T)) : w ∈ T := by
    change w ∈ (T : Set Lattice)
    rw [hclosed.eq_finite_envelope hT]
    exact (embed_mem_realEnvelope D _ w).mp hw
  by_cases ht1 : t ≤ 1
  · left
    apply hmem z
    intro d hd
    by_cases hdu : 0 ≤ det d u
    · rw [linearScore_embed_det]
      exact_mod_cast hzforward d hd hdu
    · have hdu' : (det d u : ℝ) ≤ 0 := by exact_mod_cast le_of_lt (lt_of_not_ge hdu)
      have hh := hqu d hd
      rw [map_add, linearScore_embed_det] at hh
      rw [ht, map_add, map_smul, smul_eq_mul, linearScore_embed_det]
      nlinarith
  · right
    change z-u ∈ T
    apply hmem (z-u)
    intro d hd
    by_cases hdu : det d u ≤ 0
    · have hh := hzsupport d hd
      rw [min_eq_right hdu] at hh
      rw [linearScore_embed_det, det_sub_right]
      exact_mod_cast (show lowerSupport T d ≤ det d z-det d u by omega)
    · have hdu' : (0:ℝ) ≤ (det d u : ℝ) := by exact_mod_cast le_of_lt (lt_of_not_ge hdu)
      have hh := hq d hd
      rw [embed_sub, ht, map_sub, map_add, map_smul, smul_eq_mul,
        linearScore_embed_det]
      nlinarith

theorem union_translate_isEnvelope (D T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hclosed : IsEnvelope D (T : Set Lattice))
    (hfaces : LongFaces D (T : Set Lattice))
    (hu0 : u ≠ 0) (hu : u ∈ D) (hnu : -u ∈ D) :
    IsEnvelope D ((T : Set Lattice) ∪ recenter (T : Set Lattice) (-u)) := by
  rw [← stepExpansion_eq_union D T u hT hclosed hfaces hu0 hu hnu]
  exact supportHull_idempotent D _

/-- Every genuinely new site of the expansion lies exactly one u-step
past an old site. This is an exact integer statement, not a distance bound. -/
theorem predecessor_mem_of_new_step (D T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hclosed : IsEnvelope D (T : Set Lattice))
    (hfaces : LongFaces D (T : Set Lattice))
    (hu0 : u ≠ 0) (hu : u ∈ D) (hnu : -u ∈ D)
    {z : Lattice} (hz : z ∈ stepExpansion D (T : Set Lattice) u)
    (hznot : z ∉ T) : z-u ∈ T := by
  rw [stepExpansion_eq_union D T u hT hclosed hfaces hu0 hu hnu] at hz
  exact hz.resolve_left hznot

/-- Maximality supplies an actual defective next value of an old site. -/
theorem maximal_agreement_has_step_defect {A : Type*}
    (D T : Finset Lattice) (Q : Set Lattice) (u : Lattice)
    (x p : Lattice → A) (hT : T.Nonempty)
    (hclosed : IsEnvelope D (T : Set Lattice))
    (hfaces : LongFaces D (T : Set Lattice))
    (hu0 : u ≠ 0) (hu : u ∈ D) (hnu : -u ∈ D)
    (hQ : IsEnvelope D Q) (hTQ : (T : Set Lattice) ⊆ Q)
    (hforward : ForwardInvariant Q u) (hxp : AgreeOn x p (T : Set Lattice))
    (hmax : ∀ S : Set Lattice, (T : Set Lattice) ⊆ S → S ⊆ Q → IsEnvelope D S →
      LongFaces D S → AgreeOn x p S → S = (T : Set Lattice))
    (hnew : ∃ z ∈ T, z+u ∉ T) :
    ∃ c ∈ T, c+u ∈ Q ∧ c+u ∉ T ∧ x (c+u) ≠ p (c+u) := by
  obtain ⟨z, hz, hzQ, hznot, hbad⟩ := defect_in_stepExpansion D (T : Set Lattice)
    Q u x p hQ hTQ hforward hfaces hxp hmax hnew
  have hc := predecessor_mem_of_new_step D T u hT hclosed hfaces hu0 hu hnu hz hznot
  exact ⟨z-u, hc, by simpa using hzQ, by simpa using hznot, by simpa using hbad⟩

end
end NivatTrial.ColleStepExpansionGeometry
