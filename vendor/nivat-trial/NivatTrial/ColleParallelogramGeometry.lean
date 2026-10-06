import NivatTrial.ColleZonotopePlacement
import NivatTrial.ColleBalancedRows
import NivatTrial.ColleParallelogramRows

/-! The actual parallelogram in Colle's Claim 4.2.  The first direction is
horizontal; the second direction may have any positive vertical component.
The half-open first cell retains every residue class of horizontal rows. -/

namespace NivatTrial.ColleParallelogramGeometry

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.LatticePolygon
open NivatTrial.ColleLongFaces NivatTrial.ColleZonotopePlacement
open NivatTrial.ColleGenerating NivatTrial.ColleAmbiguity
open NivatTrial.ColleEnvelopeGeometry
open NivatTrial.BalancedWindows
open scoped Classical
noncomputable section

theorem horizontal_longFaces_of_edge_cards (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : IsLatticeConvex S) (L : ℕ)
    (hbot : L < (bottomEdge S).card) (htop : L < (topEdge S).card) :
    LongFaces {((L : ℤ), 0), -((L : ℤ), 0)} (S : Set Lattice) := by
  obtain ⟨l, hl⟩ := row_run hconv (lower S) (bottomEdge_nonempty hS)
  obtain ⟨r, hr⟩ := row_run hconv (upper S) (topEdge_nonempty hS)
  have hb (j : ℕ) (hj : j ≤ L) : (l + (j : ℤ), lower S) ∈ S := by
    apply row_subset S (lower S)
    rw [hl]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by exact lt_of_le_of_lt hj hbot), rfl⟩
  have ht (j : ℕ) (hj : j ≤ L) : (r + (j : ℤ), upper S) ∈ S := by
    apply row_subset S (upper S)
    rw [hr]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by exact lt_of_le_of_lt hj htop), rfl⟩
  intro d hd z hz hmin
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · refine ⟨(l, lower S), by simpa using hb 0 (Nat.zero_le _), ?_, ?_⟩
    · simpa using hb L le_rfl
    · have hh := hmin (l, lower S) (by simpa using hb 0 (Nat.zero_le _))
      have hh' := lower_le_of_mem hz
      simp only [det, zero_mul, sub_zero] at *
      nlinarith
  · refine ⟨(r + L, upper S), ht L le_rfl, ?_, ?_⟩
    · simpa using ht 0 (Nat.zero_le _)
    · have hh := hmin (r, upper S) (by simpa using ht 0 (Nat.zero_le _))
      have hh' := le_upper_of_mem hz
      simp only [det, Prod.fst_neg, Prod.snd_neg, neg_zero, zero_mul, sub_zero] at *
      nlinarith

/-- The two horizontal extreme edges provide the inward translate of every
point on a transverse exposed edge. -/
theorem support_translate_left_mem (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : IsLatticeConvex S) (L : ℕ)
    (hbot : L < (bottomEdge S).card) (htop : L < (topEdge S).card)
    (k a : Lattice) (hk : 0 < k.2) (ha : a ∈ S)
    (hmin : ∀ z ∈ S, det k a ≤ det k z) : a - ((L : ℤ),0) ∈ S := by
  by_cases hL : L = 0
  · simpa only [hL, Nat.cast_zero, show ((0 : ℤ), 0) = (0 : Lattice) from rfl, sub_zero] using ha
  have hfaces := horizontal_longFaces_of_edge_cards S hS hconv L hbot htop
  have hnfaces : LongFaces {-((L : ℤ),0), -(-((L : ℤ),0))} (S : Set Lattice) := by
    simpa [Finset.pair_comm] using hfaces
  have hdet : 0 < det k (-((L : ℤ),0)) := by
    simp only [det, Prod.fst_neg, Prod.snd_neg, neg_zero, mul_zero, zero_sub, mul_neg, neg_neg]
    exact mul_pos hk (by exact_mod_cast Nat.pos_of_ne_zero hL)
  simpa only [sub_eq_add_neg] using
    support_inward_step S (-((L : ℤ),0)) k a hS hconv hnfaces ha hmin hdet

/-- Four genuine corners fill the whole lattice parallelogram, including
nonprimitive second directions. -/
theorem mem_parallelogram_of_bounds (S : Finset Lattice)
    (hconv : IsLatticeConvex S) (a k : Lattice) (m L : ℕ)
    (hm : 0 < m) (hk : 0 < k.2)
    (ha : a ∈ S) (hb : a + m • k ∈ S)
    (hal : a - ((L : ℤ),0) ∈ S) (hbl : a + m • k - ((L : ℤ),0) ∈ S)
    (z : Lattice) (hylo : a.2 ≤ z.2) (hyhi : z.2 ≤ a.2 + (m : ℤ)*k.2)
    (hdlo : det k a ≤ det k z) (hdhi : det k z ≤ det k a + (L : ℤ)*k.2) : z ∈ S := by
  let r : ℝ := ((z.2 : ℝ) - (a.2 : ℝ)) / (k.2 : ℝ)
  have hkR : (0 : ℝ) < k.2 := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hr0 : 0 ≤ r := div_nonneg (by exact_mod_cast sub_nonneg.mpr hylo) hkR.le
  have hrm : r ≤ m := (div_le_iff₀ hkR).mpr (by exact_mod_cast (show z.2-a.2 ≤ (m : ℤ)*k.2 by omega))
  have hreq : r * (k.2 : ℝ) = (z.2 : ℝ) - (a.2 : ℝ) := div_mul_cancel₀ _ (ne_of_gt hkR)
  have hratio : r / (m : ℝ) * (m : ℝ) = r := div_mul_cancel₀ _ (ne_of_gt hmR)
  have hinter (v : Lattice) (hv : v ∈ S) (hvk : v + m • k ∈ S) :
      embed v + r • embed k ∈ windowHull S := by
    have hvk' : embed v + (m : ℝ) • embed k ∈ windowHull S := by
      simpa only [embed_add, embed_nsmul] using mem_windowHull_of_mem S hvk
    have h := (windowHull_convex S).add_smul_mem (mem_windowHull_of_mem S hv) hvk'
      (t := r / (m : ℝ)) ⟨div_nonneg hr0 hmR.le, (div_le_one hmR).mpr hrm⟩
    simpa only [smul_smul, hratio] using h
  have hright := hinter a ha hb
  have hleft := hinter (a-((L : ℤ),0)) hal (by convert hbl using 1; abel)
  have hright' : ((a.1 : ℝ) + r*(k.1 : ℝ), (z.2 : ℝ)) ∈ windowHull S := by
    convert hright using 1
    ext <;> simp [embed, smul_eq_mul]
    linarith
  have hleft' : ((a.1 : ℝ) + r*(k.1 : ℝ) - (L : ℝ), (z.2 : ℝ)) ∈ windowHull S := by
    convert hleft using 1
    ext <;> simp [embed, smul_eq_mul]
    · ring
    · linarith
  have hdloR : (k.1 : ℝ)*(a.2 : ℝ) - (k.2 : ℝ)*(a.1 : ℝ) ≤
      (k.1 : ℝ)*(z.2 : ℝ) - (k.2 : ℝ)*(z.1 : ℝ) := by exact_mod_cast hdlo
  have hdhiR : (k.1 : ℝ)*(z.2 : ℝ) - (k.2 : ℝ)*(z.1 : ℝ) ≤
      (k.1 : ℝ)*(a.2 : ℝ) - (k.2 : ℝ)*(a.1 : ℝ) + (L : ℝ)*(k.2 : ℝ) := by exact_mod_cast hdhi
  apply (hconv z).mp
  apply horizontal_between (windowHull_convex S) hleft' hright'
  · nlinarith [congrArg (fun s : ℝ => s * (k.1 : ℝ)) hreq]
  · nlinarith [congrArg (fun s : ℝ => s * (k.1 : ℝ)) hreq]

def firstCell (a k : Lattice) (L : ℕ) (z : Lattice) : Prop :=
  a.2 ≤ z.2 ∧ z.2 < a.2+k.2 ∧ det k a < det k z ∧
    det k z ≤ det k a+(L : ℤ)*k.2

def cellAnchors (S : Finset Lattice) (a k : Lattice) (L : ℕ) : Finset Lattice :=
  S.filter (firstCell a k L)

/-- The cell and its next m-1 translates lie in the original window with
the actual k-support face removed. -/
theorem firstCell_run_mem_supportBase (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : IsLatticeConvex S) (a k : Lattice) (m L : ℕ)
    (hm : 0 < m) (hk : 0 < k.2)
    (hbot : L < (bottomEdge S).card) (htop : L < (topEdge S).card)
    (ha : a ∈ S) (hb : a+m•k ∈ S) (hmin : ∀ z ∈ S, det k a ≤ det k z)
    (z : Lattice) (hz : firstCell a k L z) (j : ℕ) (hj : j < m) :
    z + j • k ∈ supportBase S (embed k) := by
  have hal := support_translate_left_mem S hS hconv L hbot htop k a hk ha hmin
  have hbmin : ∀ z ∈ S, det k (a+m•k) ≤ det k z := by
    simpa only [det_add_right, det_nsmul_right, det_self, mul_zero, add_zero] using hmin
  have hbl := support_translate_left_mem S hS hconv L hbot htop k (a+m•k) hk hb hbmin
  have heq : det k (z+j•k) = det k z := by
    simp only [det_add_right, det_nsmul_right, det_self, mul_zero, add_zero]
  have hy : (z+j•k).2 = z.2+(j : ℤ)*k.2 := by simp [nsmul_eq_mul]
  have hj' : (j : ℤ)+1 ≤ m := by exact_mod_cast hj
  have hmem : z+j•k ∈ S := by
    apply mem_parallelogram_of_bounds S hconv a k m L hm hk ha hb hal hbl
    · rw [hy]
      have hnn : (0 : ℤ) ≤ j := by positivity
      nlinarith [hz.1]
    · rw [hy]; nlinarith [hz.2.1]
    · rw [heq]; exact hz.2.2.1.le
    · rw [heq]; exact hz.2.2.2
  refine Finset.mem_sdiff.mpr ⟨hmem, ?_⟩
  intro hface
  have hh := (Finset.mem_filter.mp hface).2 a ha
  have hlt : NivatTrial.Nonexpansive.score (embed k) a <
      NivatTrial.Nonexpansive.score (embed k) (z+j•k) := by
    change linearScore (embed k) (embed a) < linearScore (embed k) (embed (z+j•k))
    rw [linearScore_embed_det, linearScore_embed_det, heq]
    exact_mod_cast hz.2.2.1
  exact (not_lt_of_ge hh) hlt

theorem mem_cellAnchors_iff (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : IsLatticeConvex S) (a k : Lattice) (m L : ℕ)
    (hm : 0 < m) (hk : 0 < k.2)
    (hbot : L < (bottomEdge S).card) (htop : L < (topEdge S).card)
    (ha : a ∈ S) (hb : a+m•k ∈ S) (hmin : ∀ z ∈ S, det k a ≤ det k z)
    (z : Lattice) : z ∈ cellAnchors S a k L ↔ firstCell a k L z := by
  rw [cellAnchors, Finset.mem_filter, and_iff_right_iff_imp]
  intro hz
  have hh := firstCell_run_mem_supportBase S hS hconv a k m L hm hk hbot htop
    ha hb hmin z hz 0 hm
  exact supportBase_subset S (embed k) (by simpa using hh)

/-- The actual cell anchors furnish all horizontal seed rows, with one
common translate index for the whole block. -/
theorem cellAnchors_cover_high_rows (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : IsLatticeConvex S) (a k : Lattice) (m L : ℕ)
    (hm : 0 < m) (hk : 0 < k.2)
    (hbot : L < (bottomEdge S).card) (htop : L < (topEdge S).card)
    (ha : a ∈ S) (hb : a+m•k ∈ S) (hmin : ∀ z ∈ S, det k a ≤ det k z)
    (N : ℕ) (t : ℤ) (ht : a.2+(N : ℤ)*k.2 ≤ t) :
    ∃ l n : ℤ, (N : ℤ) ≤ n ∧ ∀ j : Fin L,
      ∃ w ∈ cellAnchors S a k L, (l+(j : ℤ),t) = w+n•k := by
  obtain ⟨l,n,hn,hseed⟩ :=
    ColleParallelogramRows.consecutive_points_on_high_row a k hk L N t ht
  refine ⟨l,n,hn,?_⟩
  intro j
  obtain ⟨w,hw,he⟩ := hseed j
  refine ⟨w,?_,he⟩
  apply (mem_cellAnchors_iff S hS hconv a k m L hm hk hbot htop ha hb hmin w).mpr
  exact hw

end
end NivatTrial.ColleParallelogramGeometry
