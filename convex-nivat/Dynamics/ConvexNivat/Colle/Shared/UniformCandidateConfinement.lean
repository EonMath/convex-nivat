import ConvexNivat.Colle.Shared.FiniteSweepLocalisation

namespace ConvexNivat.Colle
noncomputable section

local macro "paidRowLength" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.cycle_row_length))
local macro "paidCycleOrder" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.SaturationSteps).num 0 ++ `ConvexNivat.Colle.sat_cycle_order))
local macro "paidDetNonneg" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.SaturationSteps).num 0 ++ `ConvexNivat.Colle.sat_ordered_det_nonneg))
local macro "paidRepresentative" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcUnion).num 0 ++ `ConvexNivat.Colle.arc_periodic_representative))
local macro "paidSupportDet" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.support_det_nonneg))

private theorem finite_residual_step {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S)
    (D : AlignedBoundary C B) (j : ℤ) :
    ∃ a : ℤ, 0 ≤ a ∧
      (D.vertex (j + 1) - C.vertex (j + 1)) - (D.vertex j - C.vertex j) =
        a • C.direction j := by
  obtain ⟨ls, hls, hs⟩ := C.edge_length j
  have hcard := paidRowLength C hS j ls (by omega) hs
  have hbound := D.source_length_le j
  have hle : ls ≤ (D.length j : ℤ) := by
    have hb : ((supportRow S (C.direction j)).card : ℤ) ≤ (D.length j : ℤ) + 1 := by
      exact_mod_cast hbound
    omega
  refine ⟨(D.length j : ℤ) - ls, by omega, ?_⟩
  calc
    _ = (D.vertex (j + 1) - D.vertex j) - (C.vertex (j + 1) - C.vertex j) := by abel
    _ = _ := by rw [D.edge_eq, hs, sub_smul]

private theorem finite_residual_support {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S)
    (D : AlignedBoundary C B) (i j : ℤ) :
    0 ≤ det (C.direction i)
      ((D.vertex j - C.vertex j) - (D.vertex i - C.vertex i)) := by
  let H : ℕ → ℤ := fun k => det (C.direction i)
    (D.vertex (i + (k : ℤ)) - C.vertex (i + (k : ℤ)))
  have hstep (k : ℕ) : ∃ a : ℤ, 0 ≤ a ∧
      H (k + 1) - H k = a * det (C.direction i) (C.direction (i + (k : ℤ))) := by
    obtain ⟨a, ha, he⟩ := finite_residual_step C hS D (i + k)
    refine ⟨a, ha, ?_⟩
    have hh := congrArg (det (C.direction i)) he
    dsimp [H]
    convert hh using 1 <;> simp [det] <;> ring
  have hfirst : ∀ k : ℕ, k ≤ m → H 0 ≤ H k := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      obtain ⟨a, ha, he⟩ := hstep k
      have hd := paidDetNonneg C (paidCycleOrder C) i (i + k) (by omega) (by omega)
      have hnon := mul_nonneg ha hd
      have hh := ih (by omega)
      omega
  have hsecond : ∀ a b : ℕ, m ≤ a → a ≤ b → b ≤ 2 * m → H b ≤ H a := by
    intro a b hma hab
    induction b, hab using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ b hab ih =>
      intro hb
      obtain ⟨r, hr, he⟩ := hstep b
      have hd := paidDetNonneg C (paidCycleOrder C) (i + m) (i + b)
        (by omega) (by omega)
      rw [C.antipodal] at hd
      have hneg : det (C.direction i) (C.direction (i + b)) ≤ 0 := by
        have heq : det (-(C.direction i)) (C.direction (i + b)) =
            -det (C.direction i) (C.direction (i + b)) := by simp [det]; ring
        rw [heq] at hd
        omega
      have hnon := mul_nonpos_of_nonneg_of_nonpos hr hneg
      have hh := ih (by omega)
      omega
  have hperiod : H (2 * m) = H 0 := by
    dsimp [H]
    simp only [Nat.cast_mul, Nat.cast_ofNat, D.vertex_periodic, C.vertex_periodic,
      Nat.cast_zero, add_zero]
  let r : ℤ := (j - i) % (2 * (m : ℤ))
  have hm := C.at_least_two
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrlt : r < 2 * (m : ℤ) := Int.emod_lt_of_pos _ (by omega)
  have hrN : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
  have hh : H 0 ≤ H r.toNat := by
    by_cases h : r.toNat ≤ m
    · exact hfirst _ h
    · have hh := hsecond r.toNat (2 * m) (by omega) (by omega) le_rfl
      rwa [hperiod] at hh
  have hd := paidRepresentative D.vertex (2 * (m : ℤ)) D.vertex_periodic i j
  have hc := paidRepresentative C.vertex (2 * (m : ℤ)) C.vertex_periodic i j
  rw [hd, hc]
  have he : det (C.direction i)
      ((D.vertex (i + r) - C.vertex (i + r)) - (D.vertex i - C.vertex i)) =
      H r.toNat - H 0 := by
    dsimp [H]
    rw [hrN]
    simp [det]
    ring
  change 0 ≤ det (C.direction i)
      ((D.vertex (i + r) - C.vertex (i + r)) - (D.vertex i - C.vertex i))
  rw [he]
  omega

private theorem finite_vertex_source_fit {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S) (hB : LatticeConvex B)
    (D : AlignedBoundary C B) (j : ℤ) :
    ∀ q ∈ S, D.vertex j + (q - C.vertex j) ∈ B := by
  intro q hq
  apply (hB _).mp
  rw [D.hull_eq]
  intro i
  have hs := paidSupportDet (C.initial_mem i) hq
  have hr := finite_residual_support C hS D i j
  have he : det (C.direction i) (D.vertex j + (q - C.vertex j) - D.vertex i) =
      det (C.direction i) (q - C.vertex i) +
      det (C.direction i) ((D.vertex j - C.vertex j) - (D.vertex i - C.vertex i)) := by
    simp [det]
    ring
  have hi : 0 ≤ det (C.direction i) (D.vertex j + (q - C.vertex j) - D.vertex i) := by
    rw [he]
    exact add_nonneg hs hr
  have heR : realDet (embed (C.direction i))
      (embed (D.vertex j + (q - C.vertex j)) - embed (D.vertex i)) =
      (det (C.direction i) (D.vertex j + (q - C.vertex j) - D.vertex i) : ℝ) := by
    simp [realDet, embed, det]
  rw [heR]
  exact_mod_cast hi


local macro "paidNormalHull" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcUnion).num 0 ++ `ConvexNivat.Colle.arc_normalised_hull_support))
local macro "paidNormalConvex" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcUnion).num 0 ++ `ConvexNivat.Colle.arc_normalised_lattice_convex))
local macro "paidFixedVertex" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcUnion).num 0 ++ `ConvexNivat.Colle.arc_fixed_vertex))
local macro "paidInitialVertex" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcUnion).num 0 ++ `ConvexNivat.Colle.arc_initial_vertex))
local macro "paidNormalVertex" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcUnion).num 0 ++ `ConvexNivat.Colle.arc_normalised_vertex_mem))
local macro "paidSecondSupport" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_second_support))
local macro "paidSecondRay" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_second_ray_mem))

private theorem normalised_mem_support_iff {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) (z : Lattice) :
    z ∈ W.normalised j ↔ ∀ r : ℤ,
      det (C.direction r) ((W.boundary j).vertex r - (W.normalise j : ℤ) • C.direction i) ≤
        det (C.direction r) z := by
  rw [← (paidNormalConvex W j z), paidNormalHull W j (embed z)]
  apply forall_congr'
  intro r
  have he : realDet (embed (C.direction r))
      (embed z - embed ((W.boundary j).vertex r - (W.normalise j : ℤ) • C.direction i)) =
      (det (C.direction r) z - det (C.direction r)
        ((W.boundary j).vertex r - (W.normalise j : ℤ) • C.direction i) : ℤ) := by
    simp [realDet, embed, det]
    ring
  rw [he]
  exact_mod_cast (sub_nonneg : 0 ≤ det (C.direction r) z - det (C.direction r)
    ((W.boundary j).vertex r - (W.normalise j : ℤ) • C.direction i) ↔ _)

private theorem normalised_fixed_support {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (r : ℤ) (hr0 : i ≤ r) (hrJ : r ≤ G.J) (j : ℕ) :
    det (C.direction r) ((W.boundary (G.subsequence j)).vertex r -
      (W.normalise (G.subsequence j) : ℤ) • C.direction i) =
    det (C.direction r) ((W.boundary (G.subsequence 0)).vertex r -
      (W.normalise (G.subsequence 0) : ℤ) • C.direction i) := by
  by_cases he : r = i
  · subst r
    rw [paidInitialVertex W (G.subsequence j), paidInitialVertex W (G.subsequence 0)]
    simp [det]
    ring
  · rw [paidFixedVertex W G r (by omega) hrJ j]

private theorem candidate_old_region_recovery {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (j : ℕ) (z : Lattice) (hzP : z ∈ normalisedUnion W G)
    (hzback : z ∈ saturateRay (W.normalised (G.subsequence j) : Set Lattice)
      (-C.direction (G.J + 1)))
    (hzforward : z ∈ halfStrip (W.normalised (G.subsequence j)) (C.direction i)) :
    z ∈ W.normalised (G.subsequence j) := by
  apply (normalised_mem_support_iff W _ z).mpr
  have hlo := G.lower
  have hhi := G.upper
  have hm := C.at_least_two
  have hbound : ∀ r : ℤ, i ≤ r → r < i + 2 * (m : ℤ) →
      det (C.direction r) ((W.boundary (G.subsequence j)).vertex r -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i) ≤ det (C.direction r) z := by
    intro r hri hrend
    by_cases hr : r ≤ G.J
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hzP
      have hs := (normalised_mem_support_iff W (G.subsequence k) z).mp hk r
      rw [normalised_fixed_support W G r hri hr k] at hs
      rw [normalised_fixed_support W G r hri hr j]
      exact hs
    · by_cases hrm : r ≤ i + (m : ℤ)
      · obtain ⟨g, hg, t, he⟩ := hzback
        have hs := (normalised_mem_support_iff W _ g).mp hg r
        have hd := paidDetNonneg C (paidCycleOrder C) (G.J + 1) r (by omega) (by omega)
        have hid : det (C.direction r) z = det (C.direction r) g +
            (t : ℤ) * det (C.direction (G.J + 1)) (C.direction r) := by
          rw [he]
          simp [det]
          ring
        rw [hid]
        exact hs.trans (le_add_of_nonneg_right (mul_nonneg (by omega) hd))
      · obtain ⟨g, hg, t, he⟩ := hzforward
        have hs := (normalised_mem_support_iff W _ g).mp hg r
        have hd := paidDetNonneg C (paidCycleOrder C) r (i + 2 * (m : ℤ)) (by omega) (by omega)
        rw [C.direction_periodic] at hd
        have hid : det (C.direction r) z = det (C.direction r) g +
            (t : ℤ) * det (C.direction r) (C.direction i) := by
          rw [he]
          simp [det]
          ring
        rw [hid]
        exact hs.trans (le_add_of_nonneg_right (mul_nonneg (by omega) hd))
  intro r
  have hd := paidRepresentative C.direction (2 * (m : ℤ)) C.direction_periodic i r
  have hv := paidRepresentative (W.boundary (G.subsequence j)).vertex (2 * (m : ℤ))
    (W.boundary (G.subsequence j)).vertex_periodic i r
  rw [hd, hv]
  apply hbound
  · have := Int.emod_nonneg (r - i) (show 2 * (m : ℤ) ≠ 0 by omega)
    omega
  · have := Int.emod_lt_of_pos (r - i) (show 0 < 2 * (m : ℤ) by omega)
    omega

private theorem normalised_terminal_height {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G) (j : ℕ) :
    det (C.direction G.J) ((W.boundary (G.subsequence j)).vertex G.J -
      (W.normalise (G.subsequence j) : ℤ) • C.direction i) =
      det (C.direction G.J) P.secondAnchor := by
  have ha : P.secondAnchor ∈ P.lattice := by simpa using paidSecondRay P 0 le_rfl
  have hav := paidNormalVertex W (G.subsequence j) G.J
  have havP : (W.boundary (G.subsequence j)).vertex G.J -
      (W.normalise (G.subsequence j) : ℤ) • C.direction i ∈ P.lattice := by
    rw [hP]
    exact Set.mem_iUnion.mpr ⟨j, hav⟩
  have hs := paidSecondSupport P havP
  rw [hP] at ha
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
  have ht := (normalised_mem_support_iff W _ _).mp hk G.J
  have hlo : i ≤ G.J := by have := G.lower; omega
  rw [normalised_fixed_support W G G.J hlo le_rfl k] at ht
  rw [normalised_fixed_support W G G.J hlo le_rfl j] at hs ⊢
  omega


local macro "paidEnlargementAbove" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.Enlargement).num 0 ++ `ConvexNivat.Colle.eg_enlargement_above))
local macro "paidEnlargementLower" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.Enlargement).num 0 ++ `ConvexNivat.Colle.eg_enlargement_lower))
local macro "paidCycleTurn" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.cycle_turn_positive))
local macro "paidCycleHalfOrder" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.cycle_half_order))
local macro "paidRowMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.row_mem))

private theorem finite_collar_positive_bands {v w : Lattice} (P : Region v w)
    (n : ℕ) (S : Finset Lattice) (b : Lattice) {M : ℕ}
    (direction : Fin M → Lattice) (threshold : Fin M → ℤ) :
    ∃ K : Finset Lattice, (K : Set Lattice) ⊆ P.enlargement n ∧
      ∀ z ∈ P.enlargement n, z ∉ P.lattice →
      (∃ r : Fin M, 0 < det (direction r) w ∧
        ∃ q ∈ S, det (direction r) (z + (q - b)) < threshold r) → z ∈ K := by
  classical
  obtain ⟨endpoint, hend⟩ := (enlargement_integer_collar P n).1
  let F : Finset Lattice := (Finset.Icc 1 n).biUnion fun h =>
    Finset.univ.biUnion fun r : Fin M => S.biUnion fun q =>
      (Finset.range ((threshold r - det (direction r) (endpoint h + (q - b))).toNat + 1)).image
        (fun a : ℕ => endpoint h + (a : ℤ) • w)
  let K := F.filter (· ∈ P.enlargement n)
  refine ⟨K, ?_, ?_⟩
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro z hz hzP hbad
    obtain ⟨r, hr, q, hq, hbad⟩ := hbad
    have hlow := paidEnlargementLower P n z hz
    have hhigh : det w z < det w P.secondAnchor := by
      by_contra! hn
      exact hzP (paidEnlargementAbove P n z hz hn)
    let h := (det w P.secondAnchor - det w z).toNat
    have hh0 : 0 < h := by dsimp [h]; omega
    have hhn : h ≤ n := by dsimp [h]; omega
    have hheight : det w z = det w P.secondAnchor - (h : ℤ) := by dsimp [h]; omega
    obtain ⟨a, ha⟩ := ((hend h hh0 hhn).2 z hheight).mp hz
    have hdet : det (direction r) (z + (q - b)) =
        det (direction r) (endpoint h + (q - b)) + (a : ℤ) * det (direction r) w := by
      rw [ha]
      simp [det]
      ring
    have haBound : a < (threshold r - det (direction r) (endpoint h + (q - b))).toNat + 1 := by
      rw [hdet] at hbad
      have ha0 : (0 : ℤ) ≤ a := by omega
      have hr1 : 1 ≤ det (direction r) w := by omega
      have ht : (a : ℤ) ≤ threshold r - det (direction r) (endpoint h + (q - b)) := by
        nlinarith
      omega
    apply Finset.mem_filter.mpr
    refine ⟨?_, hz⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨h, Finset.mem_Icc.mpr ⟨hh0, hhn⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨r, Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hq, Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr haBound, ha.symm⟩⟩

private theorem normalised_terminal_source_fit {ξ xper : Configuration ℤ}
    {S : Finset Lattice} (hS : LatticeConvex S) {m : ℕ}
    {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) (J : ℤ) :
    ∀ q ∈ S, (W.boundary j).vertex (J + 1) -
      (W.normalise j : ℤ) • C.direction i + (q - C.vertex (J + 1)) ∈ W.normalised j := by
  intro q hq
  have hfit := finite_vertex_source_fit C hS (W.A_enveloped j).2.1 (W.boundary j) (J + 1) q hq
  apply Finset.mem_image.mpr
  refine ⟨_, hfit, ?_⟩
  abel

private theorem normalised_cap_companion_support {ξ xper : Configuration ℤ}
    {S : Finset Lattice} (hS : LatticeConvex S) {m : ℕ}
    {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G) (j : ℕ)
    (z : Lattice) (hzheight : det (C.direction G.J) z < det (C.direction G.J) P.secondAnchor)
    (hzback : z ∈ saturateRay (W.normalised (G.subsequence j) : Set Lattice)
      (-C.direction (G.J + 1)))
    (r : ℤ) (hr0 : G.J + 1 ≤ r) (hrm : r ≤ G.J + (m : ℤ))
    (q : Lattice) (hq : q ∈ S) :
    det (C.direction r) ((W.boundary (G.subsequence j)).vertex r -
      (W.normalise (G.subsequence j) : ℤ) • C.direction i) ≤
      det (C.direction r) (z + (q - C.vertex (G.J + 1))) := by
  let w := C.direction G.J
  let d := C.direction (G.J + 1)
  let a := (W.boundary (G.subsequence j)).vertex (G.J + 1) -
    (W.normalise (G.subsequence j) : ℤ) • C.direction i
  have haheight : det w a = det w P.secondAnchor := by
    have he := (W.boundary (G.subsequence j)).edge_eq G.J
    have hd : det w ((W.boundary (G.subsequence j)).vertex (G.J + 1) -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i) =
        det w ((W.boundary (G.subsequence j)).vertex G.J -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i) := by
      have hh := congrArg (det w) he
      dsimp [w] at *
      simp [det] at hh ⊢
      linear_combination hh
    exact hd.trans (normalised_terminal_height W G P hP j)
  have hw : det w (z - a) ≤ 0 := by
    have he : det w (z - a) = det w z - det w a := by simp [det]; ring
    rw [he, haheight]
    exact (sub_neg.mpr hzheight).le
  have hd : 0 ≤ det d (z - a) := by
    obtain ⟨g, hg, t, he⟩ := hzback
    have hs := (normalised_mem_support_iff W _ g).mp hg (G.J + 1)
    have hz : det d z = det d g := by rw [he]; dsimp [d]; simp [det]; ring
    have hid : det d (z - a) = det d z - det d a := by simp [det]; ring
    rw [hid, hz]
    exact sub_nonneg.mpr hs
  have hrd : det (C.direction r) d ≤ 0 := by
    have hh := paidDetNonneg C (paidCycleOrder C) (G.J + 1) r hr0 (by omega)
    have he : det (C.direction r) d = -det d (C.direction r) := by simp [det]; ring
    rw [he]
    change 0 ≤ det d (C.direction r) at hh
    omega
  have hwr := paidDetNonneg C (paidCycleOrder C) G.J r (by omega) hrm
  change 0 ≤ det w (C.direction r) at hwr
  have hD : 0 < det w d := paidCycleTurn C G.J
  have hpos : 0 ≤ det (C.direction r) (z - a) := by
    have hid : det w d * det (C.direction r) (z - a) =
        det (C.direction r) d * det w (z - a) +
        det w (C.direction r) * det d (z - a) := by simp [det]; ring
    have h1 := mul_nonneg_of_nonpos_of_nonpos hrd hw
    have h2 := mul_nonneg hwr hd
    nlinarith
  have hfit := normalised_terminal_source_fit hS W (G.subsequence j) G.J q hq
  have hs := (normalised_mem_support_iff W _ _).mp hfit r
  have he : det (C.direction r) (z + (q - C.vertex (G.J + 1))) =
      det (C.direction r) (a + (q - C.vertex (G.J + 1))) +
      det (C.direction r) (z - a) := by simp [det]; ring
  rw [he]
  exact hs.trans (le_add_of_nonneg_right hpos)


private theorem aligned_mem_support_iff {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hB : LatticeConvex B)
    (D : AlignedBoundary C B) (z : Lattice) :
    z ∈ B ↔ ∀ r : ℤ, det (C.direction r) (D.vertex r) ≤ det (C.direction r) z := by
  rw [← hB z, D.hull_eq]
  apply forall_congr'
  intro r
  have he : realDet (embed (C.direction r)) (embed z - embed (D.vertex r)) =
      (det (C.direction r) z - det (C.direction r) (D.vertex r) : ℤ) := by
    simp [realDet, embed, det]
    ring
  rw [he]
  exact_mod_cast (sub_nonneg : 0 ≤ det (C.direction r) z - det (C.direction r) (D.vertex r) ↔ _)

local macro "paidLiteralUnion" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FiniteSweepLocalisation).num 0 ++ `ConvexNivat.Colle.literal_candidates_union))
local macro "paidFiniteCapture" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FiniteSweepLocalisation).num 0 ++ `ConvexNivat.Colle.finite_subset_eventual_capture))
local macro "paidTerminalSweep" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FiniteSweepLocalisation).num 0 ++ `ConvexNivat.Colle.cycle_terminal_confined_sweep))

private theorem source_candidate_terminal_placements_confined (ξ xper : Configuration ℤ)
    (alphabet : Finset ℤ) (halphabet : ∀ z, ξ z ∈ alphabet)
    (S : Finset Lattice) (hS : GeneratingSet ξ S)
    (m : ℕ) (C : AntipodalEdgeCycle S m) (i : ℤ)
    (hxper : xper ∈ OrbitClosure ξ)
    (hperiod : ∃ a : ℤ, a ≠ 0 ∧ HasPeriod xper (a • C.direction i))
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G)
    (hcarrier : P.carrier = closedRealHull (normalisedUnion W G))
    (hweak : WeaklyEnveloped S P) (harc : RegionCompleteArc C i G.J P)
    (hanchor : det (C.direction i) P.firstAnchor = -1)
    (L : NormalisedWindowLimit W G)
    (hall : ∀ r : ℕ, AgreesOn L.field
      (translate ((G.phase : ℤ) • C.direction i) xper) (P.enlargement r))
    (n' : ℕ) (E : ℕ → Finset Lattice) (j₀ : ℕ)
    (hliteral : ∀ j, (E j : Set Lattice) = backwardSaturationCandidate
      (W.normalised (G.subsequence (L.index j))) (C.direction (G.J + 1))
      (P.enlargement n'))
    (hgeometry : ∀ j ≥ j₀, EnvelopedWindow S (E j) ∧
      W.normalised (G.subsequence (L.index j)) ⊂ E j ∧
      (E j : Set Lattice) ⊆ halfStrip
        (W.normalisedBase (G.subsequence (L.index j))) (C.direction i)) :
    ∃ k : ℕ, j₀ ≤ k ∧ ∀ j ≥ k, ∀ z ∈ E j,
      z ∉ ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
        (E k : Set Lattice)) →
      ∀ q ∈ S.erase (C.vertex (G.J + 1)),
        z + (q - C.vertex (G.J + 1)) ∈ E j := by
  classical
  obtain ⟨hmono, hUnion⟩ := paidLiteralUnion W G P hP harc L n' E hliteral
  obtain ⟨D₀⟩ := (enveloped_boundary_aligned_cycle C (hgeometry j₀ le_rfl).1).1
  let directions : Fin (2 * m) → Lattice := fun r => C.direction (G.J + (r.val : ℤ))
  let thresholds : Fin (2 * m) → ℤ := fun r =>
    det (directions r) (D₀.vertex (G.J + (r.val : ℤ)))
  obtain ⟨K, hK, hbadK⟩ := finite_collar_positive_bands P n' S
    (C.vertex (G.J + 1)) directions thresholds
  obtain ⟨k₀, hk₀⟩ := paidFiniteCapture hmono K (by rw [hUnion]; exact hK)
  let k := max j₀ k₀
  have hj₀k : j₀ ≤ k := le_max_left _ _
  have hKk : K ⊆ E k := hk₀ k (le_max_right _ _)
  refine ⟨k, hj₀k, ?_⟩
  intro j hj z hz hzU q hq
  have hj₀ : j₀ ≤ j := hj₀k.trans hj
  obtain ⟨hEj, hstrict, hstrip⟩ := hgeometry j hj₀
  have hAE := (Finset.ssubset_iff_subset_ne.mp hstrict).1
  obtain ⟨D⟩ := (enveloped_boundary_aligned_cycle C hEj).1
  have hzbackP : z ∈ backwardSaturationCandidate
      (W.normalised (G.subsequence (L.index j))) (C.direction (G.J + 1)) (P.enlargement n') := by
    rw [← hliteral j]
    exact hz
  have hzP : z ∉ P.lattice := by
    intro hzP
    have hzforward : z ∈ halfStrip (W.normalised (G.subsequence (L.index j))) (C.direction i) := by
      obtain ⟨g, hg, t, he⟩ := hstrip hz
      refine ⟨g, ?_, t, he⟩
      exact Finset.image_subset_image (W.base_in_maximal _) hg
    apply hzU
    exact Or.inl (candidate_old_region_recovery W G (L.index j) z (hP ▸ hzP)
      hzbackP.1 hzforward)
  have hzheight : det (C.direction G.J) z < det (C.direction G.J) P.secondAnchor := by
    by_contra! hn
    exact hzP (paidEnlargementAbove P n' z hzbackP.2 hn)
  have hzK : z ∉ K := fun hzK => hzU (Or.inr (hKk hzK))
  let y := z + (q - C.vertex (G.J + 1))
  apply (aligned_mem_support_iff C hEj.2.1 D y).mpr
  have hsupport : ∀ r : ℤ, G.J ≤ r → r < G.J + 2 * (m : ℤ) →
      det (C.direction r) (D.vertex r) ≤ det (C.direction r) y := by
    intro r hr0 hrend
    by_cases he : r = G.J
    · subst r
      have hzsup := (aligned_mem_support_iff C hEj.2.1 D z).mp hz G.J
      have hqS := Finset.mem_of_mem_erase hq
      have hoff := paidSupportDet (C.terminal_mem G.J) hqS
      have hid : det (C.direction G.J) y = det (C.direction G.J) z +
          det (C.direction G.J) (q - C.vertex (G.J + 1)) := by dsimp [y]; simp [det]; ring
      rw [hid]
      exact hzsup.trans (le_add_of_nonneg_right hoff)
    · by_cases hrm : r ≤ G.J + (m : ℤ)
      · have hcap := normalised_cap_companion_support hS.2.1 W G P hP (L.index j)
          z hzheight hzbackP.1 r (by omega) hrm q (Finset.mem_of_mem_erase hq)
        have hvertex := paidNormalVertex W (G.subsequence (L.index j)) r
        have hvertexE := hAE hvertex
        have hs := (aligned_mem_support_iff C hEj.2.1 D _).mp hvertexE r
        exact hs.trans hcap
      · have hpos := paidCycleHalfOrder C r (G.J + 2 * (m : ℤ)) hrend (by omega)
        rw [C.direction_periodic] at hpos
        let R : Fin (2 * m) := ⟨(r - G.J).toNat, by omega⟩
        have hR : G.J + (R.val : ℤ) = r := by dsimp [R]; omega
        by_contra! hfail
        have hD₀ : D₀.vertex r ∈ E j₀ := (Finset.mem_filter.mp (D₀.initial r)).1
        have hD₀j := hmono hj₀ hD₀
        have hthreshold := (aligned_mem_support_iff C hEj.2.1 D _).mp hD₀j r
        apply hzK
        apply hbadK z hzbackP.2 hzP
        refine ⟨R, ?_, q, Finset.mem_of_mem_erase hq, ?_⟩
        · dsimp [directions]
          rw [hR]
          exact hpos
        · dsimp [thresholds, directions]
          rw [hR]
          exact hfail.trans_le hthreshold
  intro r
  have hd := paidRepresentative C.direction (2 * (m : ℤ)) C.direction_periodic G.J r
  have hv := paidRepresentative D.vertex (2 * (m : ℤ)) D.vertex_periodic G.J r
  rw [hd, hv]
  apply hsupport
  · have hm := C.at_least_two
    have := Int.emod_nonneg (r - G.J) (show 2 * (m : ℤ) ≠ 0 by omega)
    omega
  · have hm := C.at_least_two
    have := Int.emod_lt_of_pos (r - G.J) (show 0 < 2 * (m : ℤ) by omega)
    omega


private theorem source_candidate_fixed_seed_sweep (ξ xper : Configuration ℤ)
    (alphabet : Finset ℤ) (halphabet : ∀ z, ξ z ∈ alphabet)
    (S : Finset Lattice) (hS : GeneratingSet ξ S)
    (m : ℕ) (C : AntipodalEdgeCycle S m) (i : ℤ)
    (hxper : xper ∈ OrbitClosure ξ)
    (hperiod : ∃ a : ℤ, a ≠ 0 ∧ HasPeriod xper (a • C.direction i))
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G)
    (hcarrier : P.carrier = closedRealHull (normalisedUnion W G))
    (hweak : WeaklyEnveloped S P) (harc : RegionCompleteArc C i G.J P)
    (hanchor : det (C.direction i) P.firstAnchor = -1)
    (L : NormalisedWindowLimit W G)
    (hall : ∀ r : ℕ, AgreesOn L.field
      (translate ((G.phase : ℤ) • C.direction i) xper) (P.enlargement r))
    (n' : ℕ) (E : ℕ → Finset Lattice) (j₀ : ℕ)
    (hliteral : ∀ j, (E j : Set Lattice) = backwardSaturationCandidate
      (W.normalised (G.subsequence (L.index j))) (C.direction (G.J + 1))
      (P.enlargement n'))
    (hgeometry : ∀ j ≥ j₀, EnvelopedWindow S (E j) ∧
      W.normalised (G.subsequence (L.index j)) ⊂ E j ∧
      (E j : Set Lattice) ⊆ halfStrip
        (W.normalisedBase (G.subsequence (L.index j))) (C.direction i)) :
    ∃ k : ℕ, j₀ ≤ k ∧ ∀ j ≥ k,
      HasFiniteSweep S ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
        (E k : Set Lattice)) (E j) := by
  obtain ⟨k, hk, hfit⟩ := source_candidate_terminal_placements_confined ξ xper
    alphabet halphabet S hS m C i hxper hperiod W G P hP hcarrier hweak harc
    hanchor L hall n' E j₀ hliteral hgeometry
  refine ⟨k, hk, ?_⟩
  intro j hj
  exact paidTerminalSweep C hS.2.1 G.J _ (hfit j hj)


end
end ConvexNivat.Colle
