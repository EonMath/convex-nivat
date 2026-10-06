import ConvexNivat.Colle.Shared.Definitions
import ConvexNivat.Colle.Shared.CycleAlignment
import ConvexNivat.Colle.RegionGeometry
import ConvexNivat.ReductionRows
import Mathlib.Algebra.Ring.Periodic

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

private theorem saturation_sum_representation {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (B : Finset Lattice) (k : ℕ)
    (z : Lattice) : z ∈ saturationChain C i B k ↔
      ∃ g ∈ B, ∃ a : Fin (k + 1) → ℕ,
        z = g + (a 0 : ℤ) • C.direction i +
          ∑ j : Fin k, (a j.succ : ℤ) • C.direction (i - (j.val + 1 : ℤ)) := by
  induction k generalizing z with
  | zero =>
    simp only [saturationChain, halfStrip, Set.mem_setOf_eq, Fin.sum_univ_zero, add_zero]
    constructor
    · rintro ⟨g, hg, t, ht⟩
      exact ⟨g, hg, fun _ => t, ht⟩
    · rintro ⟨g, hg, a, ha⟩
      exact ⟨g, hg, a 0, ha⟩
  | succ k ih =>
    change (∃ y ∈ saturationChain C i B k, ∃ t : ℕ,
      z = y + (t : ℤ) • C.direction (i - (k + 1 : ℕ))) ↔ _
    constructor
    · rintro ⟨y, hy, t, rfl⟩
      obtain ⟨g, hg, a, rfl⟩ := (ih y).mp hy
      refine ⟨g, hg, Fin.snoc a t, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc,
        Fin.succ_castSucc, Fin.succ_last, Nat.cast_add, Nat.cast_one,
        Fin.snoc_apply_zero, add_assoc]
    · rintro ⟨g, hg, a, rfl⟩
      refine ⟨g + (a 0 : ℤ) • C.direction i +
        ∑ j : Fin k, (a j.castSucc.succ : ℤ) • C.direction (i - (j.val + 1 : ℤ)),
        (ih _).mpr ⟨g, hg, fun j => a j.castSucc, ?_⟩,
        a (Fin.last (k + 1)), ?_⟩
      · simp only [Fin.succ_castSucc, Fin.castSucc_zero]
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_last, Fin.val_castSucc, Fin.succ_last,
          Nat.cast_add, Nat.cast_one, add_assoc]

private theorem sat_predecessor_turn {v w : Lattice} (P : Region v w) :
    0 < det P.predecessor w := by
  unfold Region.predecessor
  split
  · apply P.second_turn
    dsimp
    omega
  · exact P.turn_positive

private theorem sat_predecessor_support {v w : Lattice} (P : Region v w)
    (g : Lattice) (hg : g ∈ P.lattice) :
    0 ≤ det P.predecessor (g - P.secondAnchor) := by
  unfold Region.predecessor
  split
  · rename_i hcount
    let j : Fin P.boundedCount :=
      ⟨P.boundedCount - 1, Nat.sub_lt hcount Nat.zero_lt_one⟩
    have hanchor : P.vertex j.succ = P.secondAnchor := by
      congr 1
      apply Fin.ext
      dsimp [j]
      omega
    obtain ⟨t, ht, heq⟩ := P.bounded_length j
    have hs := P.bounded_support j (embed g) hg
    have hs' : 0 ≤ det (P.boundedDirection j) (g - P.vertex j.castSucc) := by
      dsimp [realDet, embed] at hs
      simp only [det, Prod.fst_sub, Prod.snd_sub]
      exact_mod_cast hs
    rw [hanchor] at heq
    have heq' : P.secondAnchor = P.vertex j.castSucc + t • P.boundedDirection j :=
      by simpa [add_comm] using (sub_eq_iff_eq_add.mp heq)
    change 0 ≤ det (P.boundedDirection j) (g - P.secondAnchor)
    rw [heq']
    convert hs' using 1 <;> simp [det, smul_eq_mul] <;> ring
  · rename_i hcount
    have hc : P.boundedCount = 0 := by omega
    have hanchor : P.firstAnchor = P.secondAnchor := by
      unfold Region.firstAnchor Region.secondAnchor
      congr 1
      apply Fin.ext
      exact hc.symm
    have hs := P.first_support (embed g) hg
    rw [← hanchor]
    dsimp [realDet, embed] at hs
    simp only [det, Prod.fst_sub, Prod.snd_sub, Region.firstAnchor]
    exact_mod_cast hs

private theorem sat_second_ray_mem {v w : Lattice} (P : Region v w)
    (t : ℝ) (ht : 0 ≤ t) : embed P.secondAnchor + t • embed w ∈ P.carrier := by
  apply P.closed.frontier_subset
  rw [P.boundary_eq]
  exact Or.inl (Or.inr ⟨t, ht, rfl⟩)

private theorem sat_predecessor_inside {v w : Lattice} (P : Region v w)
    (g : Lattice) (hg : g ∈ P.lattice) (t : ℕ)
    (hrow : det w P.secondAnchor ≤ det w (g + (t : ℤ) • P.predecessor)) :
    g + (t : ℤ) • P.predecessor ∈ P.lattice := by
  let p := embed P.predecessor
  let q := embed w
  let b := embed P.secondAnchor
  let x := embed g
  let D := realDet p q
  let h := realDet q (x - b)
  have hD : 0 < D := by
    have hh : (0 : ℝ) < (det P.predecessor w : ℝ) := by
      exact_mod_cast sat_predecessor_turn P
    simpa [D, p, q, realDet, embed, det] using hh
  have hsup := P.second_support x hg
  change 0 ≤ h at hsup
  have hh : (t : ℝ) * D ≤ h := by
    have hh : (0 : ℝ) ≤ (det w (g + (t : ℤ) • P.predecessor) -
        det w P.secondAnchor : ℤ) := by exact_mod_cast sub_nonneg.mpr hrow
    dsimp [D, h, p, q, x, b, realDet, embed, det] at *
    push_cast at hh
    nlinarith
  by_cases ht : t = 0
  · simpa [ht] using hg
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hhpos : 0 < h := lt_of_lt_of_le (mul_pos htpos hD) hh
  let r := h / D
  have hrpos : 0 < r := div_pos hhpos hD
  have ht_r : (t : ℝ) ≤ r := (le_div_iff₀ hD).mpr hh
  let y := x + r • p
  have hy : y = b + (realDet p (x - b) / D) • q := by
    have hrD : r * D = h := div_mul_cancel₀ _ (ne_of_gt hD)
    have hDne : D ≠ 0 := ne_of_gt hD
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    all_goals
      field_simp
      dsimp [y, h, D, realDet] at *
      first | linear_combination p.1 * hrD | linear_combination p.2 * hrD
  have hpy : 0 ≤ realDet p (x - b) := by
    have hh : (0 : ℝ) ≤ (det P.predecessor (g - P.secondAnchor) : ℝ) := by
      exact_mod_cast sat_predecessor_support P g hg
    simpa [p, x, b, realDet, embed, det] using hh
  have hymem : y ∈ P.carrier := by
    rw [hy]
    exact sat_second_ray_mem P _ (div_nonneg hpy hD.le)
  have halpha : (t : ℝ) / r ≤ 1 := (div_le_one₀ hrpos).mpr ht_r
  have hm := P.convex hg hymem (sub_nonneg.mpr halpha)
    (div_nonneg (Nat.cast_nonneg t) hrpos.le) (by ring :
      1 - (t : ℝ) / r + (t : ℝ) / r = 1)
  have heq : (1 - (t : ℝ) / r) • x + ((t : ℝ) / r) • y =
      embed (g + (t : ℤ) • P.predecessor) := by
    dsimp [y, x, p]
    ext <;> simp [embed, smul_eq_mul] <;> field_simp <;> ring
  change embed (g + (t : ℤ) • P.predecessor) ∈ P.carrier
  exact heq ▸ hm

private theorem region_enlargement_union_eq_saturation {v w : Lattice}
    (P : Region v w) : (⋃ n, P.enlargement n) = saturateRay P.lattice P.predecessor := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, g, hg, t, heq, _⟩ := Set.mem_iUnion.mp hz
    exact ⟨g, hg, t, heq⟩
  · rintro ⟨g, hg, t, rfl⟩
    by_cases hrow : det w P.secondAnchor ≤ det w (g + (t : ℤ) • P.predecessor)
    · apply Set.mem_iUnion.mpr
      exact ⟨0, g, hg, t, rfl, Or.inl (sat_predecessor_inside P g hg t hrow)⟩
    · let n := (det w P.secondAnchor - det w (g + (t : ℤ) • P.predecessor)).toNat
      apply Set.mem_iUnion.mpr
      refine ⟨n, g, hg, t, rfl, Or.inr ⟨?_, by omega⟩⟩
      dsimp [n]
      rw [Int.toNat_of_nonneg (by omega)]
      omega


private theorem sat_convex_shift_interval (U : Set RealPlane) (hU : Convex ℝ U)
    (z u : RealPlane) : Convex ℝ {r : ℝ | z - r • u ∈ U} := by
  intro a ha b hb c d hc hd hcd
  have hm := hU ha hb hc hd hcd
  change z - (c * a + d * b) • u ∈ U
  convert hm using 1
  ext <;> simp [smul_eq_mul]
  · linear_combination -z.1 * hcd
  · linear_combination -z.2 * hcd

private theorem sat_integer_shift (U : Set RealPlane) (hU : Convex ℝ U)
    (z u : RealPlane) (r a : ℝ) (hr : 0 ≤ r)
    (hseed : z - r • u ∈ U) (ha : z - a • u ∈ U)
    (ha1 : z - (a + 1) • u ∈ U) :
    ∃ n : ℕ, z - (n : ℝ) • u ∈ U := by
  have hc := (sat_convex_shift_interval U hU z u).ordConnected
  by_cases hapos : 0 ≤ a
  · refine ⟨⌈a⌉₊, ?_⟩
    exact hc.out ha ha1 ⟨Nat.le_ceil a, (Nat.ceil_lt_add_one hapos).le⟩
  · refine ⟨0, ?_⟩
    exact hc.out ha hseed ⟨by simpa using le_of_not_ge hapos, by simpa using hr⟩

private theorem sat_real_basis (u e x : RealPlane) (hue : realDet u e = 1) :
    x = realDet x e • u + realDet u x • e := by
  have he : realDet u e • x = realDet x e • u + realDet u x • e := by
    ext <;> simp [realDet, smul_eq_mul] <;> ring
  simpa [hue] using he

private theorem sat_one_ray_no_holes (U : Set RealPlane) (hU : Convex ℝ U)
    (u : Lattice) (hu : Primitive u)
    (hwide : ∀ x ∈ U, ∃ y ∈ U, y + embed u ∈ U ∧
      realDet (embed u) y = realDet (embed u) x) :
    saturateRay (embed ⁻¹' U) u =
      embed ⁻¹' {x | ∃ y ∈ U, ∃ r : ℝ, 0 ≤ r ∧ x = y + r • embed u} := by
  ext z
  constructor
  · rintro ⟨g, hg, n, rfl⟩
    refine ⟨embed g, hg, (n : ℝ), Nat.cast_nonneg n, ?_⟩
    ext <;> simp [embed, smul_eq_mul]
  · rintro ⟨x, hx, r, hr, hz⟩
    obtain ⟨y, hy, hy1, hyrow⟩ := hwide x hx
    obtain ⟨e, he⟩ := primitive_height_surjective u hu 1
    change det u e = 1 at he
    have heR : realDet (embed u) (embed e) = 1 := by
      have hh : (det u e : ℝ) = 1 := by exact_mod_cast he
      simpa [realDet, embed, det] using hh
    have hzrow : realDet (embed u) (embed z) = realDet (embed u) y := by
      rw [hz]
      simp only [realDet, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] at *
      nlinarith
    let a := realDet (embed z) (embed e) - realDet y (embed e)
    have hyform : embed z - a • embed u = y := by
      rw [sat_real_basis (embed u) (embed e) (embed z) heR,
        sat_real_basis (embed u) (embed e) y heR, hzrow]
      dsimp [a]
      module
    have hy1form : embed z - (a - 1) • embed u = y + embed u := by
      rw [← hyform]
      module
    have hs : embed z - r • embed u ∈ U := by rw [hz]; simpa using hx
    obtain ⟨n, hn⟩ := sat_integer_shift U hU (embed z) (embed u) r (a - 1) hr
      hs (by simpa only [hy1form] using hy1) (by
        rw [sub_add_cancel, hyform]
        exact hy)
    refine ⟨z - (n : ℤ) • u, ?_, n, by abel⟩
    change embed (z - (n : ℤ) • u) ∈ U
    convert hn using 1
    ext <;> simp [embed, smul_eq_mul]

private theorem sat_hull_mem (B : Finset Lattice) (g : Lattice) (hg : g ∈ B) :
    embed g ∈ windowHull B := subset_convexHull ℝ _ ⟨g, hg, rfl⟩

private theorem sat_support_rows (B : Finset Lattice) (hB : B.Nonempty) (u : Lattice) :
    supportRow B u = B.filter (fun z => det u z = rowMinimum u B hB) ∧
    supportRow B (-u) = B.filter (fun z => det u z = rowMaximum u B hB) := by
  have hheight : ∀ v z : Lattice, realDot (embed z) (normal v) = (det v z : ℝ) := by
    intros
    simp [realDot, embed, normal, det]
    ring
  have hn : ∀ z, det (-u) z = -det u z := by intro z; simp [det]; ring
  constructor
  · ext z
    simp only [supportRow, supportFace, Finset.mem_filter, hheight]
    constructor
    · rintro ⟨hz, hm⟩
      refine ⟨hz, le_antisymm ?_ (Finset.inf'_le _ hz)⟩
      apply Finset.le_inf'
      intro q hq
      exact_mod_cast hm q hq
    · rintro ⟨hz, hr⟩
      refine ⟨hz, ?_⟩
      intro q hq
      rw [hr]
      exact_mod_cast (Finset.inf'_le (det u) hq)
  · ext z
    simp only [supportRow, supportFace, Finset.mem_filter, hheight, hn]
    constructor
    · rintro ⟨hz, hm⟩
      refine ⟨hz, le_antisymm (Finset.le_sup' _ hz) ?_⟩
      apply Finset.sup'_le
      intro q hq
      have hh : -(det u z) ≤ -(det u q) := by exact_mod_cast hm q hq
      omega
    · rintro ⟨hz, hr⟩
      refine ⟨hz, ?_⟩
      intro q hq
      rw [hr]
      exact_mod_cast (neg_le_neg (Finset.le_sup' (det u) hq))

private theorem sat_hull_height_bounds (B : Finset Lattice) (hB : B.Nonempty)
    (u : Lattice) (x : RealPlane) (hx : x ∈ windowHull B) :
    (rowMinimum u B hB : ℝ) ≤ realDet (embed u) x ∧
      realDet (embed u) x ≤ (rowMaximum u B hB : ℝ) := by
  have hl : IsLinearMap ℝ (fun x : RealPlane => realDet (embed u) x) := by
    constructor
    · intro a b; simp [realDet]; ring
    · intro a b; simp [realDet, smul_eq_mul]; ring
  constructor
  · apply convexHull_min (t := {x | (rowMinimum u B hB : ℝ) ≤ realDet (embed u) x})
      ?_ (convex_halfSpace_ge hl _) hx
    rintro _ ⟨z, hz, rfl⟩
    change (rowMinimum u B hB : ℝ) ≤ realDet (embed u) (embed z)
    have hh : (rowMinimum u B hB : ℝ) ≤ (det u z : ℝ) := by
      exact_mod_cast Finset.inf'_le (det u) hz
    simpa [realDet, embed, det] using hh
  · apply convexHull_min (t := {x | realDet (embed u) x ≤ (rowMaximum u B hB : ℝ)})
      ?_ (convex_halfSpace_le hl _) hx
    rintro _ ⟨z, hz, rfl⟩
    change realDet (embed u) (embed z) ≤ (rowMaximum u B hB : ℝ)
    have hh : (det u z : ℝ) ≤ (rowMaximum u B hB : ℝ) := by
      exact_mod_cast Finset.le_sup' (det u) hz
    simpa [realDet, embed, det] using hh

private theorem sat_window_fibres_wide (B : Finset Lattice) (hB : B.Nonempty)
    (hconv : LatticeConvex B) (u : Lattice) (hu : Primitive u)
    (hlo : 2 ≤ (supportRow B u).card) (hhi : 2 ≤ (supportRow B (-u)).card) :
    ∀ x ∈ windowHull B, ∃ y ∈ windowHull B, y + embed u ∈ windowHull B ∧
      realDet (embed u) y = realDet (embed u) x := by
  classical
  obtain ⟨hlorow, hhirow⟩ := sat_support_rows B hB u
  rw [hlorow] at hlo
  rw [hhirow] at hhi
  obtain ⟨gL, hgL, henumL⟩ := row_is_consecutive u hu B hconv _
    (Finset.card_pos.mp (by omega : 0 < (B.filter (fun z => det u z = rowMinimum u B hB)).card))
  obtain ⟨gH, hgH, henumH⟩ := row_is_consecutive u hu B hconv _
    (Finset.card_pos.mp (by omega : 0 < (B.filter (fun z => det u z = rowMaximum u B hB)).card))
  have hLm : gL ∈ B := ((henumL _).mpr ⟨0, by omega, by simp⟩).1
  have hHm : gH ∈ B := ((henumH _).mpr ⟨0, by omega, by simp⟩).1
  have hLplus : gL + u ∈ B := ((henumL _).mpr ⟨1, by omega, by simp⟩).1
  have hHplus : gH + u ∈ B := ((henumH _).mpr ⟨1, by omega, by simp⟩).1
  intro x hx
  obtain ⟨hmin, hmax⟩ := sat_hull_height_bounds B hB u x hx
  let lo := rowMinimum u B hB
  let hi := rowMaximum u B hB
  let c := realDet (embed u) x
  change (lo : ℝ) ≤ c at hmin
  change c ≤ (hi : ℝ) at hmax
  by_cases heq : lo = hi
  · refine ⟨embed gL, sat_hull_mem B gL hLm, ?_, ?_⟩
    · convert sat_hull_mem B (gL + u) hLplus using 1
      ext <;> simp [embed]
    · have hg : realDet (embed u) (embed gL) = (lo : ℝ) := by
        simpa [realDet, embed, det] using congrArg (fun n : ℤ => (n : ℝ)) hgL
      rw [hg]
      change (lo : ℝ) = c
      rw [← heq] at hmax
      exact le_antisymm hmin hmax
  have hlt : (lo : ℝ) < hi := by
    have hle : (lo : ℝ) ≤ hi := hmin.trans hmax
    have hne : (lo : ℝ) ≠ hi := by exact_mod_cast heq
    exact lt_of_le_of_ne hle hne
  let r := (c - lo) / ((hi : ℝ) - lo)
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hmin) (sub_pos.mpr hlt).le
  have hr1 : r ≤ 1 := (div_le_one₀ (sub_pos.mpr hlt)).mpr (by linarith)
  let y := (1 - r) • embed gL + r • embed gH
  have hc := convex_convexHull ℝ (embed '' (B : Set Lattice))
  refine ⟨y, hc (sat_hull_mem B gL hLm) (sat_hull_mem B gH hHm)
    (sub_nonneg.mpr hr1) hr0 (by ring), ?_, ?_⟩
  · have hh := hc (sat_hull_mem B (gL + u) hLplus) (sat_hull_mem B (gH + u) hHplus)
      (sub_nonneg.mpr hr1) hr0 (by ring : 1 - r + r = 1)
    have he : y + embed u = (1 - r) • embed (gL + u) + r • embed (gH + u) := by
      ext <;> simp [y, embed, smul_eq_mul] <;> ring
    rw [he]
    exact hh
  · have hloR : realDet (embed u) (embed gL) = (lo : ℝ) := by
      simpa [realDet, embed, det] using congrArg (fun n : ℤ => (n : ℝ)) hgL
    have hhiR : realDet (embed u) (embed gH) = (hi : ℝ) := by
      simpa [realDet, embed, det] using congrArg (fun n : ℤ => (n : ℝ)) hgH
    have hr : r * ((hi : ℝ) - lo) = c - lo :=
      div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hlt))
    change realDet (embed u) y = c
    dsimp [y, realDet] at *
    nlinarith


private theorem sat_cycle_direction_mem {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) : C.direction i ∈ edgeDirections S := by
  have hp : 0 < 2 * (m : ℤ) := by have hh := C.at_least_two; omega
  have hi0 := Int.emod_nonneg i (ne_of_gt hp)
  have hi1 := Int.emod_lt_of_pos i hp
  let j : Fin (2 * m) := ⟨(i % (2 * (m : ℤ))).toNat, by omega⟩
  apply (C.covers _).mpr
  refine ⟨j, ?_⟩
  have hper : Function.Periodic C.direction (2 * (m : ℤ)) := C.direction_periodic
  have hh := hper.sub_int_mul_eq (x := i) (i / (2 * (m : ℤ)))
  have hj : (j.val : ℤ) = i % (2 * (m : ℤ)) := Int.toNat_of_nonneg hi0
  rw [hj]
  simpa [Int.emod_def, mul_comm] using hh

private theorem sat_enveloped_edges {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hB : EnvelopedWindow S B) :
    edgeDirections B = edgeDirections S := by
  have hs : edgeDirections S = Set.range (fun j : Fin (2 * m) => C.direction (j.val : ℤ)) := by
    ext v
    exact C.covers v
  apply Set.eq_of_subset_of_ncard_le
  · intro v hv
    exact (hB.2.2.2.1 v hv).1
  · exact hB.2.2.2.2.ge
  · rw [hs]
    exact Set.finite_range _

private theorem sat_cycle_window_fibres {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hB : EnvelopedWindow S B) (j : ℤ) :
    ∀ x ∈ windowHull B, ∃ y ∈ windowHull B, y + embed (C.direction j) ∈ windowHull B ∧
      realDet (embed (C.direction j)) y = realDet (embed (C.direction j)) x := by
  have hplus : C.direction j ∈ edgeDirections B := by
    rw [sat_enveloped_edges C hB]
    exact sat_cycle_direction_mem C j
  have hminus : -C.direction j ∈ edgeDirections B := by
    rw [sat_enveloped_edges C hB, ← C.antipodal j]
    exact sat_cycle_direction_mem C _
  exact sat_window_fibres_wide B hB.1 hB.2.1 _ (C.primitive j) hplus.2.2 hminus.2.2

private def satRealRay (U : Set RealPlane) (u : Lattice) : Set RealPlane :=
  {x | ∃ y ∈ U, ∃ r : ℝ, 0 ≤ r ∧ x = y + r • embed u}

private theorem sat_real_ray_convex (U : Set RealPlane) (hU : Convex ℝ U)
    (u : Lattice) : Convex ℝ (satRealRay U u) := by
  rintro _ ⟨x, hx, r, hr, rfl⟩ _ ⟨y, hy, s, hs, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hU hx hy ha hb hab, a * r + b * s,
    add_nonneg (mul_nonneg ha hr) (mul_nonneg hb hs), ?_⟩
  simp only [smul_add, smul_smul, add_smul]
  abel

private theorem sat_real_ray_fibres (U : Set RealPlane) (u v : Lattice)
    (hwide : ∀ x ∈ U, ∃ y ∈ U, y + embed v ∈ U ∧
      realDet (embed v) y = realDet (embed v) x) :
    ∀ x ∈ satRealRay U u, ∃ y ∈ satRealRay U u,
      y + embed v ∈ satRealRay U u ∧
        realDet (embed v) y = realDet (embed v) x := by
  rintro _ ⟨x, hx, r, hr, rfl⟩
  obtain ⟨y, hy, hy1, hyrow⟩ := hwide x hx
  refine ⟨y + r • embed u, ⟨y, hy, r, hr, rfl⟩,
    ⟨y + embed v, hy1, r, hr, by abel⟩, ?_⟩
  dsimp [realDet] at *
  nlinarith

private def satRealChain {S : Finset Lattice} {m : ℕ} (C : AntipodalEdgeCycle S m)
    (i : ℤ) (B : Finset Lattice) : ℕ → Set RealPlane
  | 0 => satRealRay (windowHull B) (C.direction i)
  | k + 1 => satRealRay (satRealChain C i B k) (C.direction (i - (k + 1 : ℕ)))

private theorem sat_real_chain_convex {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (B : Finset Lattice) (k : ℕ) :
    Convex ℝ (satRealChain C i B k) := by
  induction k with
  | zero => exact sat_real_ray_convex _ (convex_convexHull ℝ _) _
  | succ k ih => exact sat_real_ray_convex _ ih _

private theorem sat_real_chain_fibres {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B) (k : ℕ) (j : ℤ) :
    ∀ x ∈ satRealChain C i B k, ∃ y ∈ satRealChain C i B k,
      y + embed (C.direction j) ∈ satRealChain C i B k ∧
        realDet (embed (C.direction j)) y = realDet (embed (C.direction j)) x := by
  induction k with
  | zero => exact sat_real_ray_fibres _ _ _ (sat_cycle_window_fibres C hB j)
  | succ k ih => exact sat_real_ray_fibres _ _ _ ih

private theorem sat_chain_no_holes {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B) (k : ℕ) :
    saturationChain C i B k = embed ⁻¹' satRealChain C i B k := by
  induction k with
  | zero =>
    have hBset : (B : Set Lattice) = embed ⁻¹' windowHull B := by
      ext z
      exact (hB.2.1 z).symm
    change saturateRay (B : Set Lattice) (C.direction i) = _
    rw [hBset]
    exact sat_one_ray_no_holes _ (convex_convexHull ℝ _) _ (C.primitive i)
      (sat_cycle_window_fibres C hB i)
  | succ k ih =>
    change saturateRay (saturationChain C i B k) _ = _
    rw [ih]
    exact sat_one_ray_no_holes _ (sat_real_chain_convex C i B k) _ (C.primitive _)
      (sat_real_chain_fibres C i hB k _)


private theorem sat_cone_zero (p q : Lattice) : (0 : RealPlane) ∈ twoRayCone p q :=
  ⟨0, 0, le_rfl, le_rfl, by simp⟩

private theorem sat_cone_smul {p q : Lattice} {x : RealPlane} (hx : x ∈ twoRayCone p q)
    (r : ℝ) (hr : 0 ≤ r) : r • x ∈ twoRayCone p q := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  exact ⟨r * a, r * b, mul_nonneg hr ha, mul_nonneg hr hb, by
    simp only [smul_add, smul_smul]⟩

private theorem sat_cone_add {p q : Lattice} {x y : RealPlane}
    (hx : x ∈ twoRayCone p q) (hy : y ∈ twoRayCone p q) : x + y ∈ twoRayCone p q := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  obtain ⟨c, d, hc, hd, rfl⟩ := hy
  exact ⟨a + c, b + d, add_nonneg ha hc, add_nonneg hb hd, by module⟩

private theorem sat_real_ray_inclusion (U : Set RealPlane) (u : Lattice) : U ⊆ satRealRay U u := by
  intro x hx
  exact ⟨x, hx, 0, le_rfl, by simp⟩

private theorem sat_real_chain_mono {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (B : Finset Lattice) :
    Monotone (satRealChain C i B) := by
  apply monotone_nat_of_le_succ
  intro n
  exact sat_real_ray_inclusion _ _

private theorem sat_hull_subset_real_chain {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (B : Finset Lattice) (k : ℕ) :
    windowHull B ⊆ satRealChain C i B k :=
  (sat_real_ray_inclusion _ _).trans (sat_real_chain_mono C i B (Nat.zero_le k))

private theorem sat_real_chain_subset_hull {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (B : Finset Lattice) (p q : Lattice)
    (k : ℕ) (hfirst : embed (C.direction i) ∈ twoRayCone p q)
    (hrays : ∀ n : ℕ, 1 ≤ n → n ≤ k → embed (C.direction (i - (n : ℤ))) ∈ twoRayCone p q) :
    satRealChain C i B k ⊆ finiteRayHull B p q := by
  induction k with
  | zero =>
    rintro _ ⟨x, hx, r, hr, rfl⟩
    exact ⟨x, hx, r • embed (C.direction i), sat_cone_smul hfirst r hr, rfl⟩
  | succ k ih =>
    rintro _ ⟨x, hx, r, hr, rfl⟩
    obtain ⟨y, hy, c, hc, rfl⟩ := ih (fun n hn hnk => hrays n hn (hnk.trans (Nat.le_succ k))) hx
    refine ⟨y, hy, c + r • embed (C.direction (i - (k + 1 : ℕ))),
      sat_cone_add hc (sat_cone_smul (hrays (k + 1) (by omega) le_rfl) r hr), ?_⟩
    abel

private theorem sat_endpoint_hull_subset_chain {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (B : Finset Lattice) (k : ℕ) (hk : 1 ≤ k) :
    finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ))) ⊆ satRealChain C i B k := by
  rintro _ ⟨x, hx, c, ⟨a, b, ha, hb, rfl⟩, rfl⟩
  have hfirst : x + a • embed (C.direction i) ∈ satRealChain C i B 0 := ⟨x, hx, a, ha, rfl⟩
  have hk' : k = (k - 1) + 1 := by omega
  rw [hk']
  refine ⟨x + a • embed (C.direction i),
    sat_real_chain_mono C i B (Nat.zero_le (k - 1)) hfirst, b, hb, ?_⟩
  simp only [← hk', Nat.cast_add, Nat.cast_one]
  abel

private theorem sat_chain_hull_from_cone_membership {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B)
    (k : ℕ) (hk : 1 ≤ k)
    (hcone : ∀ n : ℕ, 1 ≤ n → n ≤ k → embed (C.direction (i - (n : ℤ))) ∈
      twoRayCone (C.direction i) (C.direction (i - (k : ℤ)))) :
    saturationChain C i B k = embed ⁻¹'
      finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ))) := by
  rw [sat_chain_no_holes C i hB k]
  congr 1
  apply Set.Subset.antisymm
  · apply sat_real_chain_subset_hull C i B _ _ k
    · exact ⟨1, 0, by norm_num, le_rfl, by simp⟩
    · exact hcone
  · exact sat_endpoint_hull_subset_chain C i B k hk

private theorem sat_real_cone_coordinates (p q x : RealPlane)
    (hD : realDet p q ≠ 0) :
    x = (realDet x q / realDet p q) • p + (realDet p x / realDet p q) • q := by
  ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  all_goals
    field_simp
    dsimp [realDet]
    ring

private theorem sat_cone_mem_of_clockwise_dets (p q d : Lattice)
    (hpq : det p q < 0) (hdq : det d q ≤ 0) (hpd : det p d ≤ 0) :
    embed d ∈ twoRayCone p q := by
  have hpqR : realDet (embed p) (embed q) < 0 := by
    have h : (det p q : ℝ) < 0 := by exact_mod_cast hpq
    simpa [realDet, embed, det] using h
  have hdqR : realDet (embed d) (embed q) ≤ 0 := by
    have h : (det d q : ℝ) ≤ 0 := by exact_mod_cast hdq
    simpa [realDet, embed, det] using h
  have hpdR : realDet (embed p) (embed d) ≤ 0 := by
    have h : (det p d : ℝ) ≤ 0 := by exact_mod_cast hpd
    simpa [realDet, embed, det] using h
  exact ⟨realDet (embed d) (embed q) / realDet (embed p) (embed q),
    realDet (embed p) (embed d) / realDet (embed p) (embed q),
    div_nonneg_of_nonpos hdqR hpqR.le, div_nonneg_of_nonpos hpdR hpqR.le,
    sat_real_cone_coordinates _ _ _ (ne_of_lt hpqR)⟩

private theorem sat_cycle_antipodal_sub {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) :
    C.direction (i - (m : ℤ)) = -C.direction i := by
  have h := C.antipodal (i - (m : ℤ))
  rw [sub_add_cancel] at h
  exact neg_eq_iff_eq_neg.mp h.symm

private theorem sat_real_chain_height_le {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : B.Nonempty) (k : ℕ)
    (hsign : ∀ n : ℕ, 1 ≤ n → n ≤ k →
      det (C.direction i) (C.direction (i - (n : ℤ))) ≤ 0) :
    ∀ x ∈ satRealChain C i B k,
      realDet (embed (C.direction i)) x ≤ (rowMaximum (C.direction i) B hB : ℝ) := by
  induction k with
  | zero =>
    rintro _ ⟨x, hx, r, hr, rfl⟩
    have hb := (sat_hull_height_bounds B hB (C.direction i) x hx).2
    convert hb using 1 <;> simp [realDet, smul_eq_mul] <;> ring
  | succ k ih =>
    rintro _ ⟨x, hx, r, hr, rfl⟩
    have hb := ih (fun n hn hnk => hsign n hn (hnk.trans (Nat.le_succ k))) x hx
    have hd := hsign (k + 1) (by omega) le_rfl
    have hdR : realDet (embed (C.direction i))
        (embed (C.direction (i - (k + 1 : ℕ)))) ≤ 0 := by
      have hh : (det (C.direction i) (C.direction (i - (k + 1 : ℕ))) : ℝ) ≤ 0 := by
        exact_mod_cast hd
      simpa [realDet, embed, det] using hh
    have hmul := mul_nonpos_of_nonneg_of_nonpos hr hdR
    simp only [realDet, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at *
    nlinarith

private theorem sat_halfplane_subset_last {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : B.Nonempty)
    (hturn : det (C.direction i) (C.direction (i - 1)) < 0) :
    {x : RealPlane | realDet (embed (C.direction i)) x ≤
      (rowMaximum (C.direction i) B hB : ℝ)} ⊆ satRealChain C i B m := by
  intro x hx
  obtain ⟨g, hg, hmax⟩ := Finset.exists_mem_eq_sup' hB (det (C.direction i))
  have hgmax : realDet (embed (C.direction i)) (embed g) =
      (rowMaximum (C.direction i) B hB : ℝ) := by
    have hh : (det (C.direction i) g : ℝ) = (rowMaximum (C.direction i) B hB : ℝ) := by
      exact_mod_cast hmax.symm
    simpa [realDet, embed, det] using hh
  let p := embed (C.direction i)
  let q := embed (C.direction (i - 1))
  let d := x - embed g
  let D := realDet p q
  have hD : D < 0 := by
    have hh : (det (C.direction i) (C.direction (i - 1)) : ℝ) < 0 := by
      exact_mod_cast hturn
    simpa [D, p, q, realDet, embed, det] using hh
  have hpd : realDet p d ≤ 0 := by
    change realDet (embed (C.direction i)) x ≤ _ at hx
    dsimp [p, d, realDet] at *
    linarith
  let a := realDet d q / D
  let b := realDet p d / D
  have hb : 0 ≤ b := div_nonneg_of_nonpos hpd hD.le
  have hd : d = a • p + b • q :=
    sat_real_cone_coordinates p q d (ne_of_lt hD)
  have hdecomp : x = embed g + (max a 0) • p + b • q + (max (-a) 0) • (-p) := by
    have hsplit : max a 0 - max (-a) 0 = a := by
      by_cases ha : 0 ≤ a
      · rw [max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]; ring
      · rw [max_eq_right (le_of_not_ge ha), max_eq_left (by linarith)]; ring
    have hcoeff : max a 0 = a + max (-a) 0 := by linarith
    rw [hcoeff, add_smul]
    rw [smul_neg]
    have hx' : x = embed g + (a • p + b • q) := by
      rw [← hd]
      dsimp [d]
      abel
    rw [hx']
    abel
  have hbase : embed g + max a 0 • p ∈ satRealChain C i B 0 :=
    ⟨embed g, sat_hull_mem B g hg, max a 0, le_max_right _ _, rfl⟩
  have hstep : embed g + max a 0 • p + b • q ∈ satRealChain C i B 1 := by
    exact ⟨_, hbase, b, hb, by simp [q]⟩
  have hm := C.at_least_two
  have hmlast : m = (m - 1) + 1 := by omega
  rw [show satRealChain C i B m = satRealChain C i B ((m - 1) + 1) from
    congrArg (satRealChain C i B) hmlast]
  refine ⟨embed g + max a 0 • p + b • q,
    sat_real_chain_mono C i B (by omega : 1 ≤ m - 1) hstep,
    max (-a) 0, le_max_right _ _, ?_⟩
  rw [← hmlast, sat_cycle_antipodal_sub]
  simpa [p, embed] using hdecomp

private theorem sat_last_halfplane_from_dets {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B)
    (hturn : det (C.direction i) (C.direction (i - 1)) < 0)
    (hsign : ∀ n : ℕ, 1 ≤ n → n ≤ m →
      det (C.direction i) (C.direction (i - (n : ℤ))) ≤ 0) :
    saturationChain C i B m = {z | det (C.direction i) z ≤
      rowMaximum (C.direction i) B hB.1} ∧
    (saturationChain C i B m).Nonempty ∧
    (∀ z : Lattice, det (C.direction i) z ≤ rowMaximum (C.direction i) B hB.1 →
      ∃ g ∈ B, ∃ a : Fin (m + 1) → ℕ,
        z = g + (a 0 : ℤ) • C.direction i +
          ∑ j : Fin m, (a j.succ : ℤ) • C.direction (i - (j.val + 1 : ℤ))) := by
  have heq : saturationChain C i B m = {z | det (C.direction i) z ≤
      rowMaximum (C.direction i) B hB.1} := by
    rw [sat_chain_no_holes C i hB m]
    ext z
    constructor
    · intro hz
      have hh := sat_real_chain_height_le C i hB.1 m hsign (embed z) hz
      have hh' : (det (C.direction i) z : ℝ) ≤
          (rowMaximum (C.direction i) B hB.1 : ℝ) := by
        simpa [realDet, embed, det] using hh
      exact_mod_cast hh'
    · intro hz
      apply sat_halfplane_subset_last C i hB.1 hturn
      have hh : (det (C.direction i) z : ℝ) ≤
          (rowMaximum (C.direction i) B hB.1 : ℝ) := by exact_mod_cast hz
      simpa [realDet, embed, det] using hh
  refine ⟨heq, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hB.1
    exact ⟨g, heq.symm ▸ (Finset.le_sup' (det (C.direction i)) hg)⟩
  · intro z hz
    apply (saturation_sum_representation C i B m z).mp
    rw [heq]
    exact hz

private theorem sat_region_union_from_boundary {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (k : ℕ)
    (P : Region (-C.direction i) (C.direction (i - (k : ℤ))))
    (hlattice : P.lattice = saturationChain C i B k)
    (hpred : P.predecessor = C.direction (i - (k : ℤ) - 1)) :
    (⋃ n, P.enlargement n) = saturationChain C i B (k + 1) := by
  rw [region_enlargement_union_eq_saturation, hlattice, hpred]
  congr 2
  push_cast
  ring

private theorem sat_segment_ray_initial (a b u : Lattice) (L : ℕ)
    (hedge : b - a = (L : ℤ) • u) {z : Lattice}
    (hz : embed z ∈ segment ℝ (embed a) (embed b)) :
    ∃ t : ℝ, 0 ≤ t ∧ embed z = embed a + t • embed u := by
  obtain ⟨r, s, hr, hs, hrs, hz⟩ := hz
  have hb : embed b = embed a + (L : ℝ) • embed u := by
    have heq : b = a + (L : ℤ) • u := by rw [← hedge]; abel
    rw [heq]
    ext <;> simp [embed, smul_eq_mul]
  refine ⟨s * L, mul_nonneg hs (Nat.cast_nonneg _), ?_⟩
  rw [← hz, hb]
  ext <;> simp [smul_eq_mul]
  · linear_combination (embed a).1 * hrs
  · linear_combination (embed a).2 * hrs

private theorem sat_segment_ray_terminal (a b u : Lattice) (L : ℕ)
    (hedge : b - a = (L : ℤ) • u) {z : Lattice}
    (hz : embed z ∈ segment ℝ (embed a) (embed b)) :
    ∃ t : ℝ, 0 ≤ t ∧ embed z = embed b - t • embed u := by
  obtain ⟨r, s, hr, hs, hrs, hz⟩ := hz
  have ha : embed a = embed b - (L : ℝ) • embed u := by
    have heq : a = b - (L : ℤ) • u := by rw [← hedge]; abel
    rw [heq]
    ext <;> simp [embed, smul_eq_mul]
  refine ⟨r * L, mul_nonneg hr (Nat.cast_nonneg _), ?_⟩
  rw [← hz, ha]
  ext <;> simp [smul_eq_mul]
  · linear_combination (embed b).1 * hrs
  · linear_combination (embed b).2 * hrs

private theorem sat_weakly_enveloped_of_edges {S B : Finset Lattice}
    (hB : EnvelopedWindow S B) {v w : Lattice} (P : Region v w)
    (hedges : ∀ d E, P.BoundaryEdge d E → d ∈ edgeDirections B ∧
      (supportRow B d : Set Lattice) ⊆ E) : WeaklyEnveloped S P := by
  intro d E hE
  obtain ⟨hd, hrow⟩ := hedges d E hE
  obtain ⟨hsource, hcard⟩ := hB.2.2.2.1 d hd
  refine ⟨hsource, ?_⟩
  calc
    ((supportRow S d).card : ℕ∞) ≤ (supportRow B d).card := by exact_mod_cast hcard
    _ = (supportRow B d : Set Lattice).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ E.encard := Set.encard_mono hrow

private theorem sat_retained_boundary_weakly_enveloped {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B)
    (A : AlignedBoundary C B) (k : ℕ) (hkm : k < m)
    (P : Region (-C.direction i) (C.direction (i - (k : ℤ))))
    (hcount : P.boundedCount = m - k - 1)
    (hvertex : ∀ j : Fin (P.boundedCount + 1),
      P.vertex j = A.vertex (i - (m : ℤ) + 1 + (j.val : ℤ)))
    (hdir : ∀ j : Fin P.boundedCount,
      P.boundedDirection j = C.direction (i - (m : ℤ) + 1 + (j.val : ℤ))) :
    WeaklyEnveloped S P := by
  have hfirst : P.firstAnchor = A.vertex (i - (m : ℤ) + 1) := by
    simpa [Region.firstAnchor] using hvertex ⟨0, Nat.zero_lt_succ _⟩
  have hsecond : P.secondAnchor = A.vertex (i - (k : ℤ)) := by
    have heq : i - (m : ℤ) + 1 + (P.boundedCount : ℤ) = i - (k : ℤ) := by omega
    simpa [Region.secondAnchor, heq] using hvertex ⟨P.boundedCount, Nat.lt_succ_self _⟩
  have hmem : ∀ j, C.direction j ∈ edgeDirections B := by
    intro j
    rw [A.edge_eq_source]
    exact sat_cycle_direction_mem C j
  apply sat_weakly_enveloped_of_edges hB P
  intro d E hE
  rcases hE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · rw [← sat_cycle_antipodal_sub C i]
      exact hmem _
    · intro z hz
      have hz' : z ∈ supportRow B (C.direction (i - (m : ℤ))) := by
        simpa [sat_cycle_antipodal_sub C i] using hz
      have hs := (A.segment_eq (i - (m : ℤ)) z).mp hz'
      obtain ⟨t, ht, heq⟩ := sat_segment_ray_terminal _ _ _ _ (A.edge_eq _) hs
      exact ⟨t, ht, by simpa [hfirst, sat_cycle_antipodal_sub C i] using heq⟩
  · refine ⟨hmem _, ?_⟩
    intro z hz
    have hs := (A.segment_eq (i - (k : ℤ)) z).mp hz
    obtain ⟨t, ht, heq⟩ := sat_segment_ray_initial _ _ _ _ (A.edge_eq _) hs
    exact ⟨t, ht, by simpa [hsecond] using heq⟩
  · rw [hdir]
    refine ⟨hmem _, ?_⟩
    intro z hz
    have hs := (A.segment_eq (i - (m : ℤ) + 1 + (j.val : ℤ)) z).mp hz
    change embed z ∈ segment ℝ (embed (P.vertex j.castSucc)) (embed (P.vertex j.succ))
    rw [hvertex, hvertex]
    simpa [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, add_assoc] using hs

private theorem sat_retained_boundary_predecessor {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (A : AlignedBoundary C B)
    (k : ℕ) (hkm : k < m)
    (P : Region (-C.direction i) (C.direction (i - (k : ℤ))))
    (hcount : P.boundedCount = m - k - 1)
    (hdir : ∀ j : Fin P.boundedCount,
      P.boundedDirection j = C.direction (i - (m : ℤ) + 1 + (j.val : ℤ))) :
    P.predecessor = C.direction (i - (k : ℤ) - 1) := by
  unfold Region.predecessor
  split
  · rw [hdir]
    congr 1
    dsimp
    omega
  · rw [← sat_cycle_antipodal_sub C i]
    congr 1
    omega

private theorem sat_hull_from_ordered_determinants {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B)
    (horder : ∀ j : ℤ, ∀ n : ℕ, 0 < n → n < m →
      0 < det (C.direction (j - (n : ℤ))) (C.direction j))
    (k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    saturationChain C i B k = embed ⁻¹'
      finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ))) := by
  have hswap (v w : Lattice) : det v w = -det w v := by simp [det]; ring
  apply sat_chain_hull_from_cone_membership C i hB k hk
  intro n hn hnk
  by_cases heq : n = k
  · subst n
    exact ⟨0, 1, le_rfl, by norm_num, by simp⟩
  have hkn : 0 < k - n := by omega
  have hdiff : i - (n : ℤ) - ((k - n : ℕ) : ℤ) = i - (k : ℤ) := by omega
  have hqd := horder (i - (n : ℤ)) (k - n) hkn (by omega)
  rw [hdiff] at hqd
  apply sat_cone_mem_of_clockwise_dets
  · rw [hswap]
    exact neg_neg_of_pos (horder i k (by omega) hkm)
  · rw [hswap]
    exact (neg_neg_of_pos hqd).le
  · rw [hswap]
    exact (neg_neg_of_pos (horder i n (by omega) (by omega))).le

private theorem sat_last_from_ordered_determinants {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B)
    (horder : ∀ j : ℤ, ∀ n : ℕ, 0 < n → n < m →
      0 < det (C.direction (j - (n : ℤ))) (C.direction j)) :
    saturationChain C i B m = {z | det (C.direction i) z ≤
      rowMaximum (C.direction i) B hB.1} ∧
    (saturationChain C i B m).Nonempty ∧
    (∀ z : Lattice, det (C.direction i) z ≤ rowMaximum (C.direction i) B hB.1 →
      ∃ g ∈ B, ∃ a : Fin (m + 1) → ℕ,
        z = g + (a 0 : ℤ) • C.direction i +
          ∑ j : Fin m, (a j.succ : ℤ) • C.direction (i - (j.val + 1 : ℤ))) := by
  have hswap (v w : Lattice) : det v w = -det w v := by simp [det]; ring
  apply sat_last_halfplane_from_dets C i hB
  · rw [hswap]
    exact neg_neg_of_pos (horder i 1 (by omega) (by have hm := C.at_least_two; omega))
  · intro n hn hnm
    by_cases heq : n = m
    · subst n
      rw [sat_cycle_antipodal_sub]
      simp [det, mul_comm]
    · rw [hswap]
      exact (neg_neg_of_pos (horder i n (by omega) (by omega))).le

private theorem sat_region_from_retained_boundary {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B)
    (horder : ∀ j : ℤ, ∀ n : ℕ, 0 < n → n < m →
      0 < det (C.direction (j - (n : ℤ))) (C.direction j))
    (A : AlignedBoundary C B) (k : ℕ) (hk : 1 ≤ k) (hkm : k < m)
    (P : Region (-C.direction i) (C.direction (i - (k : ℤ))))
    (hcarrier : P.carrier = finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ))))
    (hcount : P.boundedCount = m - k - 1)
    (hvertex : ∀ j : Fin (P.boundedCount + 1),
      P.vertex j = A.vertex (i - (m : ℤ) + 1 + (j.val : ℤ)))
    (hdir : ∀ j : Fin P.boundedCount,
      P.boundedDirection j = C.direction (i - (m : ℤ) + 1 + (j.val : ℤ))) :
    P.lattice = saturationChain C i B k ∧ WeaklyEnveloped S P ∧
      P.predecessor = C.direction (i - (k : ℤ) - 1) ∧
      (⋃ n, P.enlargement n) = saturationChain C i B (k + 1) := by
  have hlattice : P.lattice = saturationChain C i B k := by
    rw [Region.lattice, hcarrier, sat_hull_from_ordered_determinants C i hB horder k hk hkm]
  have hpred := sat_retained_boundary_predecessor C i A k hkm P hcount hdir
  exact ⟨hlattice, sat_retained_boundary_weakly_enveloped C i hB A k hkm P hcount hvertex hdir,
    hpred, sat_region_union_from_boundary C i k P hlattice hpred⟩

private theorem sat_ordered_det_nonneg {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m)
    (horder : ∀ j : ℤ, ∀ n : ℕ, 0 < n → n < m →
      0 < det (C.direction (j - (n : ℤ))) (C.direction j))
    (a b : ℤ) (hab : a ≤ b) (hbm : b ≤ a + (m : ℤ)) :
    0 ≤ det (C.direction a) (C.direction b) := by
  let n := (b - a).toNat
  have hn : (n : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  by_cases hn0 : n = 0
  · have heq : a = b := by omega
    rw [heq]
    simp [det, mul_comm]
  by_cases hnm : n = m
  · have heq : b = a + (m : ℤ) := by omega
    rw [heq, C.antipodal]
    simp [det, mul_comm]
  have h := horder b n (by omega) (by omega)
  have heq : b - (n : ℤ) = a := by omega
  rw [heq] at h
  exact h.le

private theorem sat_cone_halfplanes (p q : Lattice)
    (hD : realDet (embed p) (embed q) < 0) :
    twoRayCone p q = {x | realDet (embed p) x ≤ 0 ∧ realDet x (embed q) ≤ 0} := by
  ext x
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    constructor
    · have h := mul_nonpos_of_nonneg_of_nonpos hb hD.le
      dsimp [realDet] at *
      nlinarith
    · have h := mul_nonpos_of_nonneg_of_nonpos ha hD.le
      dsimp [realDet] at *
      nlinarith
  · rintro ⟨hp, hq⟩
    exact ⟨realDet x (embed q) / realDet (embed p) (embed q),
      realDet (embed p) x / realDet (embed p) (embed q),
      div_nonneg_of_nonpos hq hD.le, div_nonneg_of_nonpos hp hD.le,
      sat_real_cone_coordinates _ _ _ (ne_of_lt hD)⟩

private theorem sat_ray_hull_closed (B : Finset Lattice) (p q : Lattice)
    (hD : realDet (embed p) (embed q) < 0) : IsClosed (finiteRayHull B p q) := by
  have hcone : IsClosed (twoRayCone p q) := by
    rw [sat_cone_halfplanes p q hD]
    have hp : Continuous (fun x : RealPlane => realDet (embed p) x) := by
      unfold realDet
      fun_prop
    have hq : Continuous (fun x : RealPlane => realDet x (embed q)) := by
      unfold realDet
      fun_prop
    exact (isClosed_le hp continuous_const).inter (isClosed_le hq continuous_const)
  have hB : IsCompact (windowHull B) :=
    ((Finset.finite_toSet B).image embed).isCompact_convexHull ℝ
  convert hcone.add_left_of_isCompact hB using 1
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Set.mem_add.mpr ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

private theorem sat_ray_hull_convex (B : Finset Lattice) (p q : Lattice) :
    Convex ℝ (finiteRayHull B p q) := by
  rintro _ ⟨x, hx, u, hu, rfl⟩ _ ⟨y, hy, v, hv, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, (convex_convexHull ℝ _) hx hy ha hb hab,
    a • u + b • v, sat_cone_add (sat_cone_smul hu a ha) (sat_cone_smul hv b hb),
    by module⟩

private theorem sat_ray_hull_area (B : Finset Lattice)
    (hB : (interior (windowHull B)).Nonempty) (p q : Lattice) :
    (interior (finiteRayHull B p q)).Nonempty := by
  apply hB.mono
  apply interior_mono
  intro x hx
  exact ⟨x, hx, 0, sat_cone_zero p q, by simp⟩

private theorem sat_ray_hull_support (B : Finset Lattice) (p q d a : Lattice)
    (hsupport : ∀ x ∈ windowHull B, 0 ≤ realDet (embed d) (x - embed a))
    (hp : 0 ≤ det d p) (hq : 0 ≤ det d q) :
    ∀ x ∈ finiteRayHull B p q, 0 ≤ realDet (embed d) (x - embed a) := by
  rintro _ ⟨x, hx, c, ⟨s, t, hs, ht, rfl⟩, rfl⟩
  have h := hsupport x hx
  have hpR : (0 : ℝ) ≤ realDet (embed d) (embed p) := by
    have hh : (0 : ℝ) ≤ (det d p : ℝ) := by exact_mod_cast hp
    simpa [realDet, embed, det] using hh
  have hqR : (0 : ℝ) ≤ realDet (embed d) (embed q) := by
    have hh : (0 : ℝ) ≤ (det d q : ℝ) := by exact_mod_cast hq
    simpa [realDet, embed, det] using hh
  have hspos := mul_nonneg hs hpR
  have htpos := mul_nonneg ht hqR
  dsimp [realDet] at *
  nlinarith

private theorem sat_retained_support {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m)
    (horder : ∀ j : ℤ, ∀ n : ℕ, 0 < n → n < m →
      0 < det (C.direction (j - (n : ℤ))) (C.direction j))
    (A : AlignedBoundary C B) (i : ℤ) (k : ℕ) (hkm : k < m)
    (j : ℤ) (hjlo : i - (m : ℤ) ≤ j) (hjhi : j ≤ i - (k : ℤ)) :
    ∀ x ∈ finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ))),
      0 ≤ realDet (embed (C.direction j)) (x - embed (A.vertex j)) := by
  apply sat_ray_hull_support
  · intro x hx
    rw [A.hull_eq] at hx
    exact hx j
  · exact sat_ordered_det_nonneg C horder j i (by omega) (by omega)
  · exact sat_ordered_det_nonneg C horder j (i - (k : ℤ)) hjhi (by omega)

private theorem sat_frontier_active {J : Type} [Fintype J]
    (d a : J → Lattice) (x : RealPlane)
    (hx : x ∈ frontier {y | ∀ j, 0 ≤ realDet (embed (d j)) (y - embed (a j))}) :
    ∃ j, realDet (embed (d j)) (x - embed (a j)) = 0 := by
  have hcont : ∀ j, Continuous (fun y : RealPlane =>
      realDet (embed (d j)) (y - embed (a j))) := by
    intro j
    unfold realDet
    fun_prop
  have hclosed : IsClosed {y : RealPlane | ∀ j, 0 ≤ realDet (embed (d j)) (y - embed (a j))} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun j => isClosed_le continuous_const (hcont j))
  have hmem : ∀ j, 0 ≤ realDet (embed (d j)) (x - embed (a j)) :=
    hclosed.frontier_subset hx
  by_contra hnone
  push_neg at hnone
  have hopen : IsOpen {y : RealPlane | ∀ j, 0 < realDet (embed (d j)) (y - embed (a j))} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const (hcont j))
  have hxin : x ∈ interior {y | ∀ j, 0 ≤ realDet (embed (d j)) (y - embed (a j))} := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hopen.mem_nhds (fun j => lt_of_le_of_ne (hmem j) (Ne.symm (hnone j))))
    intro y hy j
    exact (hy j).le
  exact hx.2 hxin

private theorem sat_det_zero_line (d a : Lattice) (hd : Primitive d) (x : RealPlane)
    (hzero : realDet (embed d) (x - embed a) = 0) :
    ∃ t : ℝ, x = embed a + t • embed d := by
  obtain ⟨e, he⟩ := primitive_height_surjective d hd 1
  have heR : realDet (embed d) (embed e) = 1 := by
    have hh : (det d e : ℝ) = 1 := by exact_mod_cast he
    simpa [realDet, embed, det] using hh
  have h := sat_real_basis (embed d) (embed e) (x - embed a) heR
  rw [hzero, zero_smul, add_zero] at h
  exact ⟨realDet (x - embed a) (embed e), by rw [← h]; abel⟩

private theorem sat_active_segment (u d w a b : Lattice) (hd : Primitive d)
    (L : ℕ) (hedge : b - a = (L : ℤ) • d)
    (hleft : 0 < det u d) (hright : 0 < det d w)
    (x : RealPlane) (hx : realDet (embed d) (x - embed a) = 0)
    (hxu : 0 ≤ realDet (embed u) (x - embed a))
    (hxw : 0 ≤ realDet (embed w) (x - embed b)) :
    x ∈ segment ℝ (embed a) (embed b) := by
  obtain ⟨t, hxt⟩ := sat_det_zero_line d a hd x hx
  have hb : embed b = embed a + (L : ℝ) • embed d := by
    have heq : b = a + (L : ℤ) • d := by rw [← hedge]; abel
    rw [heq]
    ext <;> simp [embed, smul_eq_mul]
  have hleftR : 0 < realDet (embed u) (embed d) := by
    have h : (0 : ℝ) < (det u d : ℝ) := by exact_mod_cast hleft
    simpa [realDet, embed, det] using h
  have hrightR : 0 < realDet (embed d) (embed w) := by
    have h : (0 : ℝ) < (det d w : ℝ) := by exact_mod_cast hright
    simpa [realDet, embed, det] using h
  have ht : 0 ≤ t := by
    rw [hxt] at hxu
    have hprod : 0 ≤ t * realDet (embed u) (embed d) := by
      convert hxu using 1 <;> simp [realDet, smul_eq_mul] <;> ring
    exact nonneg_of_mul_nonneg_left hprod hleftR
  have htL : t ≤ L := by
    rw [hxt, hb] at hxw
    have hprod : 0 ≤ ((L : ℝ) - t) * realDet (embed d) (embed w) := by
      convert hxw using 1 <;> simp [realDet, smul_eq_mul] <;> ring
    have h := nonneg_of_mul_nonneg_left hprod hrightR
    linarith
  by_cases hL : L = 0
  · have ht0 : t = 0 := by simp [hL] at htL; linarith
    rw [hxt, ht0, zero_smul, add_zero]
    exact left_mem_segment ℝ _ _
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  refine ⟨1 - t / L, t / L, sub_nonneg.mpr ((div_le_one₀ hLpos).mpr htL),
    div_nonneg ht hLpos.le, by ring, ?_⟩
  rw [hb, hxt]
  ext <;> simp [smul_eq_mul] <;> field_simp <;> ring

private theorem sat_active_first_ray (d w a : Lattice) (hd : Primitive d)
    (hturn : 0 < det d w) (x : RealPlane)
    (hx : realDet (embed d) (x - embed a) = 0)
    (hsupport : 0 ≤ realDet (embed w) (x - embed a)) :
    ∃ t : ℝ, 0 ≤ t ∧ x = embed a - t • embed d := by
  obtain ⟨t, hxt⟩ := sat_det_zero_line d a hd x hx
  have hD : 0 < realDet (embed d) (embed w) := by
    have hh : (0 : ℝ) < (det d w : ℝ) := by exact_mod_cast hturn
    simpa [realDet, embed, det] using hh
  have ht : 0 ≤ -t := by
    rw [hxt] at hsupport
    have hprod : 0 ≤ -t * realDet (embed d) (embed w) := by
      convert hsupport using 1 <;> simp [realDet, smul_eq_mul] <;> ring
    exact nonneg_of_mul_nonneg_left hprod hD
  exact ⟨-t, ht, by rw [hxt]; module⟩

private theorem sat_active_second_ray (u d a : Lattice) (hd : Primitive d)
    (hturn : 0 < det u d) (x : RealPlane)
    (hx : realDet (embed d) (x - embed a) = 0)
    (hsupport : 0 ≤ realDet (embed u) (x - embed a)) :
    ∃ t : ℝ, 0 ≤ t ∧ x = embed a + t • embed d := by
  obtain ⟨t, hxt⟩ := sat_det_zero_line d a hd x hx
  have hD : 0 < realDet (embed u) (embed d) := by
    have hh : (0 : ℝ) < (det u d : ℝ) := by exact_mod_cast hturn
    simpa [realDet, embed, det] using hh
  have ht : 0 ≤ t := by
    rw [hxt] at hsupport
    have hprod : 0 ≤ t * realDet (embed u) (embed d) := by
      convert hsupport using 1 <;> simp [realDet, smul_eq_mul] <;> ring
    exact nonneg_of_mul_nonneg_left hprod hD
  exact ⟨t, ht, hxt⟩

private theorem sat_support_not_interior (U : Set RealPlane) (d a : Lattice)
    (hd : Primitive d)
    (hsupport : ∀ y ∈ U, 0 ≤ realDet (embed d) (y - embed a))
    (x : RealPlane) (hzero : realDet (embed d) (x - embed a) = 0) :
    x ∉ interior U := by
  obtain ⟨e, he⟩ := primitive_height_surjective d hd 1
  have heR : realDet (embed d) (embed e) = 1 := by
    have hh : (det d e : ℝ) = 1 := by exact_mod_cast he
    simpa [realDet, embed, det] using hh
  intro hx
  have hcont : Continuous (fun t : ℝ => x - t • embed e) := by fun_prop
  have hopen : IsOpen ((fun t : ℝ => x - t • embed e) ⁻¹' interior U) :=
    isOpen_interior.preimage hcont
  have hzero_mem : (0 : ℝ) ∈ (fun t : ℝ => x - t • embed e) ⁻¹' interior U := by
    simpa using hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero_mem)
  have hm : r / 2 ∈ Metric.ball (0 : ℝ) r := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith
  have h := hsupport (x - (r / 2) • embed e) (interior_subset (hball hm))
  have heval : realDet (embed d) (x - (r / 2) • embed e - embed a) = -r / 2 := by
    calc
      _ = realDet (embed d) (x - embed a) - (r / 2) * realDet (embed d) (embed e) := by
        simp [realDet, smul_eq_mul]
        ring
      _ = -r / 2 := by rw [hzero, heR]; ring
  rw [heval] at h
  linarith

private theorem sat_support_shift (d a b : Lattice) (L : ℕ)
    (h : b - a = (L : ℤ) • d) (x : RealPlane) :
    realDet (embed d) (x - embed a) = realDet (embed d) (x - embed b) := by
  have heq : b = a + (L : ℤ) • d := by rw [← h]; abel
  rw [heq]
  simp [realDet, embed, smul_eq_mul]
  ring

private def satCutSet (D A : ℤ → Lattice) (s : ℤ) (n : ℕ) : Set RealPlane :=
  {x | ∀ j : Fin (n + 2), 0 ≤ realDet (embed (D (s + (j.val : ℤ))))
    (x - embed (A (s + (j.val : ℤ))))}

private theorem sat_cut_frontier_subset (D A : ℤ → Lattice) (L : ℤ → ℕ)
    (hprim : ∀ j, Primitive (D j))
    (hedge : ∀ j, A (j + 1) - A j = (L j : ℤ) • D j)
    (hturn : ∀ j, 0 < det (D j) (D (j + 1))) (s : ℤ) (n : ℕ) :
    frontier (satCutSet D A s n) ⊆
      {x | ∃ t : ℝ, 0 ≤ t ∧ x = embed (A (s + 1)) - t • embed (D s)} ∪
      {x | ∃ t : ℝ, 0 ≤ t ∧ x = embed (A (s + (n + 1 : ℕ))) + t • embed (D (s + (n + 1 : ℕ)))} ∪
      {x | ∃ j : Fin n, x ∈ segment ℝ (embed (A (s + 1 + (j.val : ℤ))))
        (embed (A (s + 1 + (j.val : ℤ) + 1)))} := by
  intro x hx
  have hclosed : IsClosed (satCutSet D A s n) := by
    unfold satCutSet
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro j
    have hc : Continuous (fun x : RealPlane => realDet (embed (D (s + (j.val : ℤ))))
        (x - embed (A (s + (j.val : ℤ))))) := by unfold realDet; fun_prop
    exact isClosed_le continuous_const hc
  have hmem := hclosed.frontier_subset hx
  obtain ⟨j, hj⟩ := sat_frontier_active
    (fun j : Fin (n + 2) => D (s + (j.val : ℤ)))
    (fun j : Fin (n + 2) => A (s + (j.val : ℤ))) x hx
  by_cases hj0 : j.val = 0
  · apply Or.inl ∘ Or.inl
    have hnext := hmem ⟨1, by omega⟩
    have hz : realDet (embed (D s)) (x - embed (A (s + 1))) = 0 := by
      simpa [hj0, sat_support_shift (D s) (A s) (A (s + 1)) (L s) (hedge s) x] using hj
    exact sat_active_first_ray (D s) (D (s + 1)) (A (s + 1)) (hprim s) (hturn s) x hz
      (by simpa using hnext)
  by_cases hjlast : j.val = n + 1
  · apply Or.inl ∘ Or.inr
    let a := s + (n : ℤ)
    have hprev := hmem ⟨n, by omega⟩
    have hsup : 0 ≤ realDet (embed (D a)) (x - embed (A (a + 1))) := by
      rw [← sat_support_shift (D a) (A a) (A (a + 1)) (L a) (hedge a) x]
      exact hprev
    have hz : realDet (embed (D (a + 1))) (x - embed (A (a + 1))) = 0 := by
      simpa [a, hjlast, Nat.cast_add, Nat.cast_one, add_assoc] using hj
    simpa [a, Nat.cast_add, Nat.cast_one, add_assoc] using
      sat_active_second_ray (D a) (D (a + 1)) (A (a + 1)) (hprim _) (hturn a) x hz hsup
  · apply Or.inr
    let r : Fin n := ⟨j.val - 1, by omega⟩
    refine ⟨r, ?_⟩
    let a := s + (j.val : ℤ)
    have ha : s + ((j.val - 1 : ℕ) : ℤ) + 1 = a := by dsimp [a]; omega
    have hleft := hmem ⟨j.val - 1, by omega⟩
    have hright := hmem ⟨j.val + 1, by omega⟩
    have hleft' : 0 ≤ realDet (embed (D (a - 1))) (x - embed (A a)) := by
      have hrel : s + ((j.val - 1 : ℕ) : ℤ) = a - 1 := by omega
      rw [hrel] at hleft
      have he := hedge (a - 1)
      rw [sub_add_cancel] at he
      rw [← sat_support_shift (D (a - 1)) (A (a - 1)) (A a) (L (a - 1)) he x]
      exact hleft
    have hright' : 0 ≤ realDet (embed (D (a + 1))) (x - embed (A (a + 1))) := by
      simpa [a, Nat.cast_add, Nat.cast_one, add_assoc] using hright
    have hturn' : 0 < det (D (a - 1)) (D a) := by simpa using hturn (a - 1)
    have hseg := sat_active_segment (D (a - 1)) (D a) (D (a + 1)) (A a) (A (a + 1))
      (hprim a) (L a) (hedge a) hturn' (hturn a) x hj hleft' hright'
    have hidx : s + 1 + (r.val : ℤ) = a := by dsimp [r, a]; omega
    simpa [hidx] using hseg

private theorem sat_cut_retract (D A : ℤ → Lattice) (s : ℤ) (n : ℕ)
    (hprim : ∀ j, Primitive (D j)) (u : RealPlane)
    (hpos : ∀ j : Fin (n + 2), 0 < realDet (embed (D (s + (j.val : ℤ)))) u)
    (x : RealPlane) (hx : x ∈ satCutSet D A s n) :
    ∃ y ∈ frontier (satCutSet D A s n), ∃ t : ℝ, 0 ≤ t ∧ x = y + t • u := by
  let H (j : Fin (n + 2)) := realDet (embed (D (s + (j.val : ℤ))))
    (x - embed (A (s + (j.val : ℤ))))
  let V (j : Fin (n + 2)) := realDet (embed (D (s + (j.val : ℤ)))) u
  obtain ⟨j, hj⟩ := Finite.exists_min (fun j : Fin (n + 2) => H j / V j)
  let t := H j / V j
  have ht : 0 ≤ t := div_nonneg (hx j) (hpos j).le
  let y := x - t • u
  have heval (l : Fin (n + 2)) :
      realDet (embed (D (s + (l.val : ℤ)))) (y - embed (A (s + (l.val : ℤ)))) =
        H l - t * V l := by
    simp [H, V, y, realDet, smul_eq_mul]
    ring
  have hymem : y ∈ satCutSet D A s n := by
    intro l
    rw [heval]
    have hle : t * V l ≤ H l := (le_div_iff₀ (hpos l)).mp (hj l)
    linarith
  have hzero : realDet (embed (D (s + (j.val : ℤ))))
      (y - embed (A (s + (j.val : ℤ)))) = 0 := by
    rw [heval]
    dsimp [t]
    rw [div_mul_cancel₀ _ (ne_of_gt (hpos j)), sub_self]
  refine ⟨y, (mem_frontier_iff_notMem_interior hymem).mpr ?_, t, ht, ?_⟩
  · exact sat_support_not_interior (satCutSet D A s n) (D (s + (j.val : ℤ)))
      (A (s + (j.val : ℤ))) (hprim _) (fun z hz => hz j) y hzero
  · dsimp [y]
    abel

private theorem sat_aligned_vertex_mem {S B : Finset Lattice} {m : ℕ}
    {C : AntipodalEdgeCycle S m} (A : AlignedBoundary C B) (j : ℤ) : A.vertex j ∈ B := by
  exact (Finset.mem_filter.mp (A.initial j)).1

private theorem sat_ordered_det_positive {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m)
    (horder : ∀ j : ℤ, ∀ n : ℕ, 0 < n → n < m →
      0 < det (C.direction (j - (n : ℤ))) (C.direction j))
    (a b : ℤ) (hab : a < b) (hbm : b < a + (m : ℤ)) :
    0 < det (C.direction a) (C.direction b) := by
  let n := (b - a).toNat
  have hn : (n : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have h := horder b n (by omega) (by omega)
  have heq : b - (n : ℤ) = a := by omega
  simpa [heq] using h

private theorem sat_retained_cut_eq {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m)
    (horder : ∀ j : ℤ, ∀ n : ℕ, 0 < n → n < m →
      0 < det (C.direction (j - (n : ℤ))) (C.direction j))
    (A : AlignedBoundary C B) (i : ℤ) (k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    satCutSet C.direction A.vertex (i - (m : ℤ)) (m - k - 1) =
      finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ))) := by
  let n := m - k - 1
  let s := i - (m : ℤ)
  have hlast : s + (n + 1 : ℕ) = i - (k : ℤ) := by dsimp [s, n]; omega
  have hstart : C.direction s = -C.direction i := sat_cycle_antipodal_sub C i
  have hturn : ∀ j, 0 < det (C.direction j) (C.direction (j + 1)) := by
    intro j
    apply sat_ordered_det_positive C horder <;> have hm := C.at_least_two <;> omega
  have hinc : finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ))) ⊆
      satCutSet C.direction A.vertex s n := by
    intro x hx j
    exact sat_retained_support C horder A i k hkm (s + (j.val : ℤ))
      (by dsimp [s]; omega) (by have hj := j.isLt; dsimp [s, n] at *; omega) x hx
  have hboundary : frontier (satCutSet C.direction A.vertex s n) ⊆
      finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ))) := by
    intro x hx
    have hb := sat_cut_frontier_subset C.direction A.vertex A.length C.primitive A.edge_eq hturn s n hx
    rcases hb with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨j, hj⟩
    · refine ⟨embed (A.vertex (s + 1)), sat_hull_mem B _ (sat_aligned_vertex_mem A _),
        t • embed (C.direction i), ⟨t, 0, ht, le_rfl, by simp⟩, ?_⟩
      rw [hstart]
      simp [embed, smul_neg, sub_eq_add_neg]
    · rw [hlast]
      exact ⟨embed (A.vertex (i - (k : ℤ))), sat_hull_mem B _ (sat_aligned_vertex_mem A _),
        t • embed (C.direction (i - (k : ℤ))), ⟨0, t, le_rfl, ht, by simp⟩, rfl⟩
    · have hseg := (convex_convexHull ℝ (embed '' (B : Set Lattice))).segment_subset
        (sat_hull_mem B _ (sat_aligned_vertex_mem A _))
        (sat_hull_mem B _ (sat_aligned_vertex_mem A _)) hj
      exact ⟨x, hseg, 0, sat_cone_zero _ _, by simp⟩
  apply Set.Subset.antisymm ?_ hinc
  intro x hx
  let u := embed (C.direction i) + embed (C.direction (i - (k : ℤ)))
  have hpos : ∀ j : Fin (n + 2), 0 < realDet (embed (C.direction (s + (j.val : ℤ)))) u := by
    intro j
    let a := s + (j.val : ℤ)
    have hlo : s ≤ a := by dsimp [a]; omega
    have hhi : a ≤ i - (k : ℤ) := by have hj := j.isLt; dsimp [a, s, n] at *; omega
    have hp : 0 ≤ det (C.direction a) (C.direction i) :=
      sat_ordered_det_nonneg C horder a i (by dsimp [s] at *; omega) (by dsimp [s] at *; omega)
    have hq : 0 ≤ det (C.direction a) (C.direction (i - (k : ℤ))) :=
      sat_ordered_det_nonneg C horder a (i - (k : ℤ)) hhi (by dsimp [s] at *; omega)
    have hsum : 0 < det (C.direction a) (C.direction i) +
        det (C.direction a) (C.direction (i - (k : ℤ))) := by
      by_cases heq : a = i - (k : ℤ)
      · have hh := sat_ordered_det_positive C horder a i (by omega) (by omega)
        omega
      · have hh := sat_ordered_det_positive C horder a (i - (k : ℤ)) (by omega)
          (by dsimp [s] at *; omega)
        omega
    have hsumR : (0 : ℝ) < (det (C.direction a) (C.direction i) : ℝ) +
        (det (C.direction a) (C.direction (i - (k : ℤ))) : ℝ) := by exact_mod_cast hsum
    convert hsumR using 1 <;> simp [u, a, realDet, embed, det] <;> ring
  obtain ⟨y, hy, t, ht, rfl⟩ := sat_cut_retract C.direction A.vertex s n C.primitive u hpos x hx
  obtain ⟨z, hz, c, hc, rfl⟩ := hboundary hy
  refine ⟨z, hz, c + t • u, sat_cone_add hc ?_, by abel⟩
  exact ⟨t, t, ht, ht, by simp [u, smul_add]⟩

private theorem sat_cut_frontier_eq (D A : ℤ → Lattice) (L : ℤ → ℕ)
    (hprim : ∀ j, Primitive (D j))
    (hedge : ∀ j, A (j + 1) - A j = (L j : ℤ) • D j)
    (hturn : ∀ j, 0 < det (D j) (D (j + 1))) (s : ℤ) (n : ℕ)
    (hboundary :
      {x | ∃ t : ℝ, 0 ≤ t ∧ x = embed (A (s + 1)) - t • embed (D s)} ∪
      {x | ∃ t : ℝ, 0 ≤ t ∧ x = embed (A (s + (n + 1 : ℕ))) + t • embed (D (s + (n + 1 : ℕ)))} ∪
      {x | ∃ j : Fin n, x ∈ segment ℝ (embed (A (s + 1 + (j.val : ℤ))))
        (embed (A (s + 1 + (j.val : ℤ) + 1)))} ⊆ satCutSet D A s n) :
    frontier (satCutSet D A s n) =
      {x | ∃ t : ℝ, 0 ≤ t ∧ x = embed (A (s + 1)) - t • embed (D s)} ∪
      {x | ∃ t : ℝ, 0 ≤ t ∧ x = embed (A (s + (n + 1 : ℕ))) + t • embed (D (s + (n + 1 : ℕ)))} ∪
      {x | ∃ j : Fin n, x ∈ segment ℝ (embed (A (s + 1 + (j.val : ℤ))))
        (embed (A (s + 1 + (j.val : ℤ) + 1)))} := by
  apply Set.Subset.antisymm (sat_cut_frontier_subset D A L hprim hedge hturn s n)
  intro x hx
  apply (mem_frontier_iff_notMem_interior (hboundary hx)).mpr
  rcases hx with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨j, hj⟩
  · apply sat_support_not_interior (satCutSet D A s n) (D s) (A s) (hprim s)
      (fun y hy => by simpa using hy ⟨0, by omega⟩)
    rw [sat_support_shift (D s) (A s) (A (s + 1)) (L s) (hedge s)]
    simp [realDet, smul_eq_mul]
    ring
  · apply sat_support_not_interior (satCutSet D A s n)
      (D (s + (n + 1 : ℕ))) (A (s + (n + 1 : ℕ))) (hprim _)
      (fun y hy => hy ⟨n + 1, by omega⟩)
    simp [realDet, smul_eq_mul]
    ring
  · let a := s + 1 + (j.val : ℤ)
    apply sat_support_not_interior (satCutSet D A s n) (D a) (A a) (hprim a)
      (fun y hy => by simpa [a, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hy ⟨j.val + 1, by omega⟩) x
    obtain ⟨r, t, hr, ht, hrt, hxt⟩ := hj
    have hb : embed (A (a + 1)) = embed (A a) + (L a : ℝ) • embed (D a) := by
      have hh : A (a + 1) = A a + (L a : ℤ) • D a := by rw [← hedge a]; abel
      rw [hh]
      ext <;> simp [embed, smul_eq_mul]
    change r • embed (A a) + t • embed (A (a + 1)) = x at hxt
    rw [← hxt, hb]
    have heq : r • embed (A a) + t • (embed (A a) + (L a : ℝ) • embed (D a)) -
        embed (A a) = (t * L a) • embed (D a) := by
      rw [smul_add, ← add_assoc, ← add_smul, hrt, one_smul, smul_smul]
      abel
    rw [heq]
    simp [realDet, smul_eq_mul]
    ring

private theorem sat_retained_region_exists {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m)
    (horder : ∀ j : ℤ, ∀ n : ℕ, 0 < n → n < m →
      0 < det (C.direction (j - (n : ℤ))) (C.direction j))
    (hB : EnvelopedWindow S B) (A : AlignedBoundary C B) (i : ℤ)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    ∃ P : Region (-C.direction i) (C.direction (i - (k : ℤ))),
      P.carrier = finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ))) ∧
      P.boundedCount = m - k - 1 ∧
      (∀ j : Fin (P.boundedCount + 1),
        P.vertex j = A.vertex (i - (m : ℤ) + 1 + (j.val : ℤ))) ∧
      (∀ j : Fin P.boundedCount,
        P.boundedDirection j = C.direction (i - (m : ℤ) + 1 + (j.val : ℤ))) := by
  let n := m - k - 1
  let s := i - (m : ℤ)
  let U := finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ)))
  have hlast : s + (n + 1 : ℕ) = i - (k : ℤ) := by dsimp [s, n]; omega
  have hfirst : C.direction s = -C.direction i := sat_cycle_antipodal_sub C i
  have hturn : ∀ j, 0 < det (C.direction j) (C.direction (j + 1)) := by
    intro j
    apply sat_ordered_det_positive C horder <;> have hm := C.at_least_two <;> omega
  have hcut : satCutSet C.direction A.vertex s n = U :=
    sat_retained_cut_eq C horder A i k hk hkm
  have hD : realDet (embed (C.direction i)) (embed (C.direction (i - (k : ℤ)))) < 0 := by
    have hp := horder i k (by omega) hkm
    have hswap : det (C.direction i) (C.direction (i - (k : ℤ))) =
        -det (C.direction (i - (k : ℤ))) (C.direction i) := by simp [det]; ring
    have h : (det (C.direction i) (C.direction (i - (k : ℤ))) : ℝ) < 0 := by
      exact_mod_cast (show det (C.direction i) (C.direction (i - (k : ℤ))) < 0 by omega)
    simpa [realDet, embed, det] using h
  have hbnd := sat_cut_frontier_eq C.direction A.vertex A.length C.primitive A.edge_eq hturn s n
  have hbnd' : frontier U =
      {x | ∃ t : ℝ, 0 ≤ t ∧ x = embed (A.vertex (s + 1)) - t • embed (C.direction s)} ∪
      {x | ∃ t : ℝ, 0 ≤ t ∧ x = embed (A.vertex (s + (n + 1 : ℕ))) +
        t • embed (C.direction (s + (n + 1 : ℕ)))} ∪
      {x | ∃ j : Fin n, x ∈ segment ℝ (embed (A.vertex (s + 1 + (j.val : ℤ))))
        (embed (A.vertex (s + 1 + (j.val : ℤ) + 1)))} := by
    rw [← hcut]
    apply hbnd
    intro x hx
    rw [hcut]
    rcases hx with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨j, hj⟩
    · refine ⟨embed (A.vertex (s + 1)), sat_hull_mem B _ (sat_aligned_vertex_mem A _),
        t • embed (C.direction i), ⟨t, 0, ht, le_rfl, by simp⟩, ?_⟩
      rw [hfirst]
      simp [embed, smul_neg, sub_eq_add_neg]
    · rw [hlast]
      exact ⟨embed (A.vertex (i - (k : ℤ))), sat_hull_mem B _ (sat_aligned_vertex_mem A _),
        t • embed (C.direction (i - (k : ℤ))), ⟨0, t, le_rfl, ht, by simp⟩, rfl⟩
    · have hs := (convex_convexHull ℝ (embed '' (B : Set Lattice))).segment_subset
        (sat_hull_mem B _ (sat_aligned_vertex_mem A _))
        (sat_hull_mem B _ (sat_aligned_vertex_mem A _)) hj
      exact ⟨_, hs, 0, sat_cone_zero _ _, by simp⟩
  let P : Region (-C.direction i) (C.direction (i - (k : ℤ))) := {
    carrier := U
    closed := sat_ray_hull_closed B _ _ hD
    convex := sat_ray_hull_convex B _ _
    interior_nonempty := sat_ray_hull_area B hB.2.2.1 _ _
    first_primitive := hfirst ▸ C.primitive s
    second_primitive := C.primitive _
    turn_positive := by
      have hh := sat_ordered_det_positive C horder s (i - (k : ℤ))
        (by dsimp [s]; omega) (by dsimp [s]; omega)
      simpa [hfirst] using hh
    boundedCount := n
    vertex := fun j => A.vertex (s + 1 + (j.val : ℤ))
    boundedDirection := fun j => C.direction (s + 1 + (j.val : ℤ))
    bounded_primitive := fun j => C.primitive _
    bounded_length := by
      intro j
      refine ⟨A.length (s + 1 + (j.val : ℤ)), ?_, ?_⟩
      · exact_mod_cast A.length_positive _
      · simpa [Nat.cast_add, Nat.cast_one, add_assoc] using A.edge_eq (s + 1 + (j.val : ℤ))
    first_turn := by
      intro j hj
      simpa [hj, ← hfirst] using hturn s
    bounded_turn := by
      intro j l hjl
      simpa [hjl, Nat.cast_add, Nat.cast_one, add_assoc] using hturn (s + 1 + (j.val : ℤ))
    second_turn := by
      intro j hj
      have heq : i - (k : ℤ) = s + 1 + (j.val : ℤ) + 1 := by dsimp [s, n] at *; omega
      rw [heq]
      exact hturn _
    first_support := by
      intro x hx
      have hh := sat_retained_support C horder A i k hkm s (by rfl) (by dsimp [s]; omega) x hx
      rw [sat_support_shift (C.direction s) (A.vertex s) (A.vertex (s + 1)) (A.length s) (A.edge_eq s) x,
        hfirst] at hh
      simpa using hh
    second_support := by
      intro x hx
      have hh := sat_retained_support C horder A i k hkm (i - (k : ℤ)) (by omega) le_rfl x hx
      have heq : s + 1 + (n : ℤ) = i - (k : ℤ) := by dsimp [s, n]; omega
      simpa [heq] using hh
    bounded_support := by
      intro j x hx
      exact sat_retained_support C horder A i k hkm (s + 1 + (j.val : ℤ))
        (by dsimp [s]; omega) (by have hj := j.isLt; dsimp [s, n] at *; omega) x hx
    boundary_eq := by
      rw [hlast, hfirst] at hbnd'
      have heq : s + 1 + (n : ℤ) = i - (k : ℤ) := by dsimp [s, n]; omega
      simpa [heq, Nat.cast_add, Nat.cast_one, add_assoc] using hbnd'
  }
  exact ⟨P, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

private theorem sat_region_from_ordered_aligned_boundary {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B)
    (horder : ∀ j : ℤ, ∀ n : ℕ, 0 < n → n < m →
      0 < det (C.direction (j - (n : ℤ))) (C.direction j))
    (A : AlignedBoundary C B) (k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    ∃ P : Region (-C.direction i) (C.direction (i - (k : ℤ))),
      P.lattice = saturationChain C i B k ∧ WeaklyEnveloped S P ∧
      P.predecessor = C.direction (i - (k : ℤ) - 1) ∧
      (⋃ n, P.enlargement n) = saturationChain C i B (k + 1) := by
  obtain ⟨P, hcarrier, hcount, hvertex, hdir⟩ :=
    sat_retained_region_exists C horder hB A i k hk hkm
  exact ⟨P, sat_region_from_retained_boundary C i hB horder A k hk hkm
    P hcarrier hcount hvertex hdir⟩

namespace SaturationCycleOrder

private theorem sat_parallel_multiple (u : Lattice) (hu : Primitive u)
    (v : Lattice) (hdet : det u v = 0) : ∃ k : ℤ, v = k • u := by
  obtain ⟨e, he⟩ := primitive_height_surjective u hu 1
  change det u e = 1 at he
  refine ⟨det v e, ?_⟩
  have h : (det u e) • v = (det v e) • u + (det u v) • e := by
    ext <;> simp [det] <;> ring
  simpa only [he, hdet, zero_smul, add_zero, one_smul] using h


private theorem row_mem (S : Finset Lattice) (u a : Lattice) :
    a ∈ supportRow S u ↔ a ∈ S ∧ ∀ z ∈ S, det u a ≤ det u z := by
  simp only [supportRow,supportFace,Finset.mem_filter,normal_height]
  constructor
  · rintro ⟨ha,hh⟩
    refine ⟨ha,?_⟩
    intro z hz
    exact_mod_cast hh z hz
  · rintro ⟨ha,hh⟩
    refine ⟨ha,?_⟩
    intro z hz
    exact_mod_cast hh z hz

private theorem support_det_nonneg {S : Finset Lattice} {u a z : Lattice}
    (ha : a ∈ supportRow S u) (hz : z ∈ S) : 0 ≤ det u (z-a) := by
  have hh := ((row_mem S u a).mp ha).2 z hz
  have he : det u (z-a)=det u z-det u a := by simp [det]; ring
  rw [he]
  omega

private theorem support_pair_forbids_middle {S : Finset Lattice} {u v w a : Lattice}
    (hu : a ∈ supportRow S u) (hv : a ∈ supportRow S v)
    (huv : 0 < det u v) (huw : 0 < det u w) (hwv : 0 < det w v) :
    w ∉ edgeDirections S := by
  intro hw
  have hz_eq : ∀ z ∈ supportRow S w, z=a := by
    intro z hz
    have hzS := ((row_mem S w z).mp hz).1
    have hu0 := support_det_nonneg hu hzS
    have hv0 := support_det_nonneg hv hzS
    have hw0 : det w (z-a) ≤ 0 := by
      have hh := ((row_mem S w z).mp hz).2 a ((row_mem S u a).mp hu).1
      have he : det w (z-a)=det w z-det w a := by simp [det]; ring
      rw [he]
      omega
    have hid : det u v * det w (z-a) =
        det w v * det u (z-a)+det u w * det v (z-a) := by simp [det]; ring
    have huz : det u (z-a)=0 := by nlinarith [mul_nonneg huw.le hv0]
    have hvz : det v (z-a)=0 := by nlinarith [mul_nonneg hwv.le hu0]
    have hcoord1 : det u v * (z-a).1 =
        v.1 * det u (z-a)-u.1 * det v (z-a) := by simp [det]; ring
    have hcoord2 : det u v * (z-a).2 =
        v.2 * det u (z-a)-u.2 * det v (z-a) := by simp [det]; ring
    rw [huz,hvz,mul_zero,mul_zero,sub_self] at hcoord1 hcoord2
    have h1 := (mul_eq_zero.mp hcoord1).resolve_left huv.ne'
    have h2 := (mul_eq_zero.mp hcoord2).resolve_left huv.ne'
    exact sub_eq_zero.mp (Prod.ext h1 h2)
  have hcard : (supportRow S w).card ≤ 1 := Finset.card_le_one.mpr
    (fun z hz q hq => (hz_eq z hz).trans (hz_eq q hq).symm)
  have hh := hw.2.2
  omega

private theorem periodic_mod {α : Type*} (f : ℤ → α) (n : ℕ)
    (hn : 0 < n) (hf : ∀ j, f (j+(n : ℤ))=f j) (j : ℤ) : f (j % n)=f j := by
  have hp : Function.Periodic f (n : ℤ) := hf
  have h := hp.int_mul (j/(n : ℤ)) (j % (n : ℤ))
  simpa only [Int.cast_id,Int.emod_add_ediv_mul] using h.symm


private theorem cycle_direction_mem {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (j : ℤ) : C.direction j ∈ edgeDirections S := by
  have hm := C.at_least_two
  have hj0 : 0 ≤ j % (2*m : ℕ) := Int.emod_nonneg _ (by omega)
  have hjlt : j % (2*m : ℕ) < (2*m : ℕ) := Int.emod_lt_of_pos _ (by omega)
  let k : Fin (2*m) := ⟨(j % (2*m : ℕ)).toNat,(Int.toNat_lt hj0).mpr hjlt⟩
  apply (C.covers _).mpr
  refine ⟨k,?_⟩
  change C.direction ((j % (2*m : ℕ)).toNat : ℤ)=C.direction j
  rw [Int.toNat_of_nonneg hj0]
  exact periodic_mod C.direction (2*m) (by omega) (by simpa using C.direction_periodic) j

private theorem cycle_direction_inj_between {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) {i j : ℤ} (hij : i < j) (hji : j < i+2*m) :
    C.direction i ≠ C.direction j := by
  have hm := C.at_least_two
  have hmod : ∀ k : ℤ, 0 ≤ k % (2*m : ℕ) ∧ k % (2*m : ℕ) < (2*m : ℕ) := by
    intro k
    exact ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩
  let index (k : ℤ) : Fin (2*m) := ⟨(k % (2*m : ℕ)).toNat,(Int.toNat_lt (hmod k).1).mpr (hmod k).2⟩
  have he (k : ℤ) : C.direction ((index k).val : ℤ)=C.direction k := by
    change C.direction ((k % (2*m : ℕ)).toNat : ℤ)=C.direction k
    rw [Int.toNat_of_nonneg (hmod k).1]
    exact periodic_mod C.direction (2*m) (by omega) (by simpa using C.direction_periodic) k
  intro h
  have hi : index i=index j := C.distinct ((he i).trans (h.trans (he j).symm))
  have hrem : i % (2*m : ℕ)=j % (2*m : ℕ) := by
    have hv := congrArg (fun k : Fin (2*m) => (k.val : ℤ)) hi
    simpa only [index,Int.toNat_of_nonneg (hmod i).1,Int.toNat_of_nonneg (hmod j).1] using hv
  have hdvd : (2*m : ℤ) ∣ j-i := by
    apply Int.dvd_of_emod_eq_zero
    have h' := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hrem.symm
    simpa using h'
  have hpos : 0 < j-i := by omega
  have hlt : j-i < 2*m := by omega
  have hle := Int.le_of_dvd hpos hdvd
  omega


private theorem primitive_parallel_eq_or_neg (u v : Lattice)
    (hu : Primitive u) (hv : Primitive v) (hdet : det u v=0) : v=u ∨ v= -u := by
  obtain ⟨k,hk⟩ := sat_parallel_multiple u hu v hdet
  have hg : k.natAbs=1 := by
    have h := hv
    rw [hk] at h
    change Int.gcd (k*u.1) (k*u.2)=1 at h
    rw [Int.gcd_mul_left,show Int.gcd u.1 u.2=1 from hu,mul_one] at h
    exact h
  have hkpm : k=1 ∨ k= -1 := by omega
  rcases hkpm with h | h
  · left; simpa [h] using hk
  · right; simpa [h] using hk

private theorem cycle_half_det_ne_zero {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) {i j : ℤ} (hij : i < j) (hji : j < i+m) :
    det (C.direction i) (C.direction j) ≠ 0 := by
  have hm := C.at_least_two
  intro hzero
  rcases primitive_parallel_eq_or_neg _ _ (C.primitive i) (C.primitive j) hzero with he | he
  · exact cycle_direction_inj_between C hij (by omega) he.symm
  · have hianti : C.direction j=C.direction (i+m) := by rw [C.antipodal]; exact he
    exact cycle_direction_inj_between C hji (by omega) hianti

private theorem cycle_turn_positive {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) :
    0 < det (C.direction i) (C.direction (i+1)) := by
  have hm := C.at_least_two
  have hn := support_det_nonneg (C.terminal_mem i)
    (((row_mem S _ _).mp (C.terminal_mem (i+1))).1)
  obtain ⟨k,hk,hedge⟩ := C.edge_length (i+1)
  rw [hedge] at hn
  have he : det (C.direction i) (k • C.direction (i+1)) =
      k * det (C.direction i) (C.direction (i+1)) := by simp [det]; ring
  rw [he] at hn
  have hnon : 0 ≤ det (C.direction i) (C.direction (i+1)) := by nlinarith
  exact lt_of_le_of_ne hnon (Ne.symm (cycle_half_det_ne_zero C (by omega) (by omega)))

private theorem cycle_nat_half_order {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (n : ℕ) (hn : 0 < n) (hnm : n < m) :
    0 < det (C.direction i) (C.direction (i+n)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n
      simpa using cycle_turn_positive C i
    have hprev := ih (by omega) (by omega)
    have hnext := cycle_turn_positive C (i+n)
    have hne : det (C.direction i) (C.direction (i+(n+1 : ℕ))) ≠ 0 :=
      cycle_half_det_ne_zero C (by omega) (by exact_mod_cast (show (i : ℤ)+(n+1 : ℕ) < i+m by omega))
    by_contra! hnon
    have hneg : det (C.direction i) (C.direction (i+(n+1 : ℕ))) < 0 :=
      lt_of_le_of_ne hnon hne
    have h1 : 0 < det (C.direction (i+n)) (C.direction (i+m)) := by
      rw [C.antipodal]
      have he : det (C.direction (i+n)) (-C.direction i)=
          det (C.direction i) (C.direction (i+n)) := by simp [det]; ring
      rw [he]
      exact hprev
    have h2 : 0 < det (C.direction (i+m)) (C.direction (i+(n+1 : ℕ))) := by
      rw [C.antipodal]
      have he : det (-C.direction i) (C.direction (i+(n+1 : ℕ))) =
          -det (C.direction i) (C.direction (i+(n+1 : ℕ))) := by simp [det]; ring
      rw [he]
      omega
    have hforbid := support_pair_forbids_middle (C.terminal_mem (i+n))
      (C.initial_mem (i+n+1)) hnext h1
      (by simpa [Nat.cast_add,Nat.cast_one,add_assoc] using h2)
    exact hforbid (cycle_direction_mem C (i+m))

private theorem cycle_half_order {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i j : ℤ) (hij : i < j) (hji : j < i+m) :
    0 < det (C.direction i) (C.direction j) := by
  have h := cycle_nat_half_order C i (j-i).toNat (by omega) (by omega)
  have hj : i+((j-i).toNat : ℤ)=j := by omega
  rwa [hj] at h


end SaturationCycleOrder

private theorem sat_cycle_order {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (j : ℤ) (n : ℕ) (hn : 0 < n) (hnm : n < m) :
    0 < det (C.direction (j - (n : ℤ))) (C.direction j) := by
  apply SaturationCycleOrder.cycle_half_order C (j - (n : ℤ)) j <;> omega

theorem saturation_exact_minkowski_hull {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    saturationChain C i B k = embed ⁻¹'
      finiteRayHull B (C.direction i) (C.direction (i - (k : ℤ))) := by
  exact sat_hull_from_ordered_determinants C i hB (sat_cycle_order C) k hk hkm

theorem saturation_last_halfplane_geometry {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B) :
    saturationChain C i B m = {z | det (C.direction i) z ≤
      rowMaximum (C.direction i) B hB.1} ∧
    (saturationChain C i B m).Nonempty ∧
    (∀ z : Lattice, det (C.direction i) z ≤ rowMaximum (C.direction i) B hB.1 →
      ∃ g ∈ B, ∃ a : Fin (m + 1) → ℕ,
        z = g + (a 0 : ℤ) • C.direction i +
          ∑ j : Fin m, (a j.succ : ℤ) • C.direction (i - (j.val + 1 : ℤ))) := by
  exact sat_last_from_ordered_determinants C i hB (sat_cycle_order C)

theorem saturation_region_and_row_union {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    ∃ P : Region (-C.direction i) (C.direction (i - (k : ℤ))),
      P.lattice = saturationChain C i B k ∧ WeaklyEnveloped S P ∧
      P.predecessor = C.direction (i - (k : ℤ) - 1) ∧
      (⋃ n, P.enlargement n) = saturationChain C i B (k + 1) := by
  obtain ⟨A⟩ := (enveloped_boundary_aligned_cycle C hB).1
  exact sat_region_from_ordered_aligned_boundary C i hB (sat_cycle_order C) A k hk hkm

end
end ConvexNivat.Colle
