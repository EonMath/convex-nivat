import ConvexNivat.ReductionAlgebra
import ConvexNivat.Biperiodicity
import ConvexNivat.AppendixD

namespace ConvexNivat
open scoped BigOperators
open Filter

/-- 8.14: a fixed component plus safe tails leave exactly two components in
the limit; the actual low convex complexity condition is retained. -/
theorem proposition8_14 (p : ℕ) (hp : p.Prime) (θ : Configuration (ZMod p))
    (D : FirstHalfPlaneData p θ) (O : Finset (Fin D.length))
    (K : TailInventory D O) (hlow : LowConvexComplexity θ)
    (b c : Fin D.length) (hbc : b ≠ c) (d : Lattice)
    (hscale : ∃ z : Lattice, d = (K.scale : ℤ) • z)
    (hfixes : det (D.direction c) d = 0)
    (hbnegative : det (D.direction b) d < 0)
    (hsafe : ∀ j, j ≠ b → j ≠ c → SafeDirection D O d j)
    (limit : Configuration (ZMod p))
    (hlimit : SubsequentialTranslateLimit (D.field b) d limit) :
    DoublyPeriodic limit := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨s, hs⟩ := hscale
  have repr (i : Fin D.length) (z : Lattice) :
      z = det z (D.transverse i) • D.direction i + det (D.direction i) z • D.transverse i := by
    have he : det (D.direction i) (D.transverse i) • z =
        det z (D.transverse i) • D.direction i + det (D.direction i) z • D.transverse i := by
      ext <;> simp [det] <;> ring
    simpa [D.basis i] using he
  have hscalep (i : Fin D.length) : HasPeriod (D.field i) ((K.scale : ℤ) • D.direction i) := by
    obtain ⟨q, hq⟩ := K.divisible i
    rw [hq, Nat.cast_mul, mul_smul]
    simpa only [smul_smul, mul_comm] using
      hasPeriod_zsmul _ _ (D.has_period i) (q : ℤ)
  have hfixed : HasPeriod (D.field c) d := by
    have hsfix : det (D.direction c) s = 0 := by
      have hh : det (D.direction c) d = (K.scale : ℤ) * det (D.direction c) s := by
        rw [hs]; simp [det]; ring
      rw [hh] at hfixes
      exact (mul_eq_zero.mp hfixes).resolve_left (by exact_mod_cast Nat.ne_of_gt K.positive_scale)
    have hsrepr := repr c s
    rw [hsfix, zero_smul, add_zero] at hsrepr
    rw [hs, hsrepr, smul_smul]
    simpa only [smul_smul, mul_comm] using
      hasPeriod_zsmul _ _ (hscalep c) (det s (D.transverse c))
  let J := (Finset.univ : Finset (Fin D.length)).erase b |>.erase c
  have hJ (j : Fin D.length) : j ∈ J ↔ j ≠ b ∧ j ≠ c := by
    simp [J, and_comm]
  let T (j : Fin D.length) : Configuration (ZMod p) :=
    if h : j ∈ J then
      if hpos : 0 < det (D.direction j) d then K.upperTail j
      else K.lowerTail j ((hsafe j ((hJ j).mp h).1 ((hJ j).mp h).2).resolve_left hpos).1
    else 0
  have hpT (j : Fin D.length) : ∀ z, HasPeriod (T j) ((K.scale : ℤ) • z) := by
    intro z
    dsimp [T]
    split_ifs with hj hpos
    · exact K.upper_periods j z
    · exact K.lower_periods j _ z
    · intro x; rfl
  have htlimit (j : Fin D.length) (hj : j ∈ J) :
      PointwiseLimit (fun n : ℕ => translate ((n : ℤ) • d) (D.field j)) (T j) := by
    have hpTd : HasPeriod (T j) d := by rw [hs]; exact hpT j s
    have hdet (z : Lattice) (n : ℕ) : det (D.direction j) (z + (n : ℤ) • d) =
        det (D.direction j) z + (n : ℤ) * det (D.direction j) d := by
      simp [det]; ring
    intro z
    by_cases hpos : 0 < det (D.direction j) d
    · refine ⟨(max 0 (D.threshold j - det (D.direction j) z)).toNat, ?_⟩
      intro n hn
      have hnz : max 0 (D.threshold j - det (D.direction j) z) ≤ (n : ℤ) := by
        have hn' : ((max 0 (D.threshold j - det (D.direction j) z)).toNat : ℤ) ≤ n := by exact_mod_cast hn
        rwa [Int.toNat_of_nonneg (le_max_left _ _)] at hn'
      have hin : z + (n : ℤ) • d ∈ upperHalf (D.direction j) (D.threshold j) := by
        change D.threshold j ≤ _
        rw [hdet]
        have hnnonneg : 0 ≤ (n : ℤ) := by omega
        nlinarith [le_max_right (0 : ℤ) (D.threshold j - det (D.direction j) z)]
      have hag := K.upper_agreement j _ hin
      have heq : T j = K.upperTail j := by simp [T, hj, hpos]
      rw [← heq] at hag
      exact hag.trans (hasPeriod_zsmul _ d hpTd n z)
    · have hsafej := (hsafe j ((hJ j).mp hj).1 ((hJ j).mp hj).2).resolve_left hpos
      refine ⟨(max 0 (det (D.direction j) z - K.lowerThreshold j hsafej.1)).toNat, ?_⟩
      intro n hn
      have hnz : max 0 (det (D.direction j) z - K.lowerThreshold j hsafej.1) ≤ (n : ℤ) := by
        have hn' : ((max 0 (det (D.direction j) z - K.lowerThreshold j hsafej.1)).toNat : ℤ) ≤ n := by exact_mod_cast hn
        rwa [Int.toNat_of_nonneg (le_max_left _ _)] at hn'
      have hin : z + (n : ℤ) • d ∈ lowerHalf (D.direction j) (K.lowerThreshold j hsafej.1) := by
        change _ ≤ K.lowerThreshold j hsafej.1
        rw [hdet]
        have hnnonneg : 0 ≤ (n : ℤ) := by omega
        nlinarith [le_max_right (0 : ℤ) (det (D.direction j) z - K.lowerThreshold j hsafej.1)]
      have hag := K.lower_agreement j hsafej.1 _ hin
      have heq : T j = K.lowerTail j hsafej.1 := by simp [T, hj, hpos]
      rw [← heq] at hag
      exact hag.trans (hasPeriod_zsmul _ d hpTd n z)
  let B : Configuration (ZMod p) := fun z => ∑ j ∈ J, T j z
  have hpB (z : Lattice) : HasPeriod B ((K.scale : ℤ) • z) := by
    intro x
    apply Finset.sum_congr rfl
    intro j hj
    exact hpT j z x
  have hBdouble : DoublyPeriodic B :=
    (doublyPeriodic_iff_grid B).mpr ⟨K.scale, K.positive_scale, hpB⟩
  let F : Configuration (ZMod p) := fun z => D.field c z + B z
  let Ξ : Configuration (ZMod p) := fun z => F z + limit z
  have hFlim : SubsequentialTranslateLimit θ d Ξ := by
    obtain ⟨n, hn, hlim⟩ := hlimit
    refine ⟨n, hn, fun z => ?_⟩
    have hsums : ∃ N : ℕ, ∀ k ≥ N, ∀ j ∈ J,
        translate ((n k : ℤ) • d) (D.field j) z = T j z := by
      have hall : ∀ j ∈ J, ∃ N, ∀ k ≥ N,
          translate ((n k : ℤ) • d) (D.field j) z = T j z := by
        intro j hj
        obtain ⟨N, hN⟩ := htlimit j hj z
        exact ⟨N, fun k hk => hN _ (le_trans hk (hn.id_le k))⟩
      exact eventually_atTop.mp (J.eventually_all.mpr fun j hj => eventually_atTop.mpr (hall j hj))
    obtain ⟨N, hN⟩ := hsums
    obtain ⟨M, hM⟩ := hlim z
    refine ⟨max N M, fun k hk => ?_⟩
    have hfields : ∑ j ∈ J, D.field j (z + (n k : ℤ) • d) = B z := by
      apply Finset.sum_congr rfl
      exact fun j hj => hN k (le_trans (le_max_left _ _) hk) j hj
    have hsum := D.sum_eq (z + (n k : ℤ) • d)
    have hsplit : (∑ j : Fin D.length, D.field j (z + (n k : ℤ) • d)) =
        D.field b (z + (n k : ℤ) • d) + D.field c (z + (n k : ℤ) • d) +
          ∑ j ∈ J, D.field j (z + (n k : ℤ) • d) := by
      have h₁ := Finset.sum_erase_add (Finset.univ : Finset (Fin D.length))
        (fun j => D.field j (z + (n k : ℤ) • d)) (Finset.mem_univ b)
      have h₂ := Finset.sum_erase_add ((Finset.univ : Finset (Fin D.length)).erase b)
        (fun j => D.field j (z + (n k : ℤ) • d)) (by simp [hbc.symm] : c ∈ Finset.univ.erase b)
      rw [← h₁, ← h₂]
      dsimp [J]
      abel
    change θ (z + (n k : ℤ) • d) = _
    rw [hsum, hsplit, hfields, hasPeriod_zsmul _ _ hfixed (n k) z]
    have hblim := hM k (le_trans (le_max_right _ _) hk)
    change D.field b (z + (n k : ℤ) • d) = limit z at hblim
    rw [hblim]
    dsimp [Ξ, F]
    abel
  have hΞorbit : Ξ ∈ OrbitClosure θ := by
    obtain ⟨n, hn, hlim⟩ := hFlim
    intro S
    have hall : ∀ z ∈ S, ∃ N, ∀ k ≥ N, translate ((n k : ℤ) • d) θ z = Ξ z :=
      fun z _ => hlim z
    obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, ∀ z ∈ S, translate ((n k : ℤ) • d) θ z = Ξ z := by
      exact eventually_atTop.mp (S.eventually_all.mpr fun z hz => eventually_atTop.mpr (hall z hz))
    exact ⟨(n N : ℤ) • d, fun z hz => by simpa [translate, add_comm] using (hN N le_rfl z hz).symm⟩
  let h₁ := (K.scale : ℤ) • D.direction c
  let h₂ := (D.multiplier b : ℤ) • D.direction b
  have hpF : HasPeriod F h₁ := hasPeriod_add_fields _ _ _ (hscalep c) (hpB _)
  have hpL : HasPeriod limit h₂ := by
    obtain ⟨n, hn, hlim⟩ := hlimit
    intro z
    obtain ⟨N, hN⟩ := hlim z
    obtain ⟨M, hM⟩ := hlim (z + h₂)
    have he := (hasPeriod_translate_iff (D.field b) ((n (max N M) : ℤ) • d) h₂).mpr (D.has_period b) z
    exact (hM _ (le_max_right _ _)).symm.trans (he.trans (hN _ (le_max_left _ _)))
  have hind : Nonparallel h₁ h₂ := by
    have hh : det h₁ h₂ = (K.scale : ℤ) * (D.multiplier b : ℤ) * det (D.direction c) (D.direction b) := by
      simp [h₁, h₂, det]; ring
    rw [Nonparallel, hh]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast Nat.ne_of_gt K.positive_scale)
      (by exact_mod_cast Nat.ne_of_gt (D.positive_multiplier b))) (D.distinct_directions hbc.symm)
  have h₁ne := nonparallel_ne_zero_left _ _ hind
  have h₂ne := nonparallel_ne_zero_right _ _ hind
  obtain ⟨S, hS, hconvex, hlowS⟩ := hlow
  have hΞlow : complexity Ξ S ≤ S.card :=
    le_trans (orbitClosure_complexity_le θ Ξ hΞorbit S) hlowS
  have hperiodic : Periodic Ξ := by
    exact theoremD_1 p hp F limit h₁ h₂ h₁ne h₂ne hpF hpL hind
      S hS hconvex hΞlow
  obtain ⟨q, hq, hpΞ⟩ := hperiodic
  have hpar : det h₁ q = 0 := by
    by_contra hnonpar
    let g : Configuration (ZMod p) := fun z => F (z + q) - F z
    have hgeq : g = fun z => -(limit (z + q) - limit z) := by
      funext z
      have hh := hpΞ z
      change F (z + q) + limit (z + q) = F z + limit z at hh
      dsimp [g]
      linear_combination hh
    have hpgh₁ : HasPeriod g h₁ :=
      hasPeriod_sub_fields _ _ _ ((hasPeriod_translate_iff F q h₁).mpr hpF) hpF
    have hpgh₂ : HasPeriod g h₂ := by
      rw [hgeq]
      intro z
      have hh := (hasPeriod_translate_iff limit q h₂).mpr hpL z
      simp only [translate] at hh
      dsimp
      rw [hh, hpL z]
    have hFdouble := lemma8_13 p hp F h₁ q h₁ne hpF hnonpar
      ⟨h₁, h₂, hind, hpgh₁, hpgh₂⟩
    have hcdouble := doublyPeriodic_sub_fields F B hFdouble hBdouble
    have heq : F - B = D.field c := by funext z; simp [F]
    rw [heq] at hcdouble
    exact D.not_double c hcdouble
  have hcq : det (D.direction c) q = 0 := by
    have hh : det h₁ q = (K.scale : ℤ) * det (D.direction c) q := by
      simp [h₁, det]; ring
    rw [hh] at hpar
    exact (mul_eq_zero.mp hpar).resolve_left (by exact_mod_cast Nat.ne_of_gt K.positive_scale)
  have hqrepr := repr c q
  rw [hcq, zero_smul, add_zero] at hqrepr
  have hpFq : HasPeriod F ((K.scale : ℤ) • q) := by
    rw [hqrepr, smul_smul]
    simpa only [h₁, smul_smul, mul_comm] using hasPeriod_zsmul _ _ hpF (det q (D.transverse c))
  have hpLq : HasPeriod limit ((K.scale : ℤ) • q) := by
    intro z
    have hh := hasPeriod_zsmul _ q hpΞ (K.scale : ℤ) z
    change F (z + (K.scale : ℤ) • q) + limit (z + (K.scale : ℤ) • q) = F z + limit z at hh
    rw [hpFq z] at hh
    exact add_left_cancel hh
  refine ⟨h₂, (K.scale : ℤ) • q, ?_, hpL, hpLq⟩
  have hqcoef : det q (D.transverse c) ≠ 0 := by
    intro hz; rw [hz, zero_smul] at hqrepr; exact hq hqrepr
  have hh' : det h₂ ((K.scale : ℤ) • q) =
      -(K.scale : ℤ) * det q (D.transverse c) * (D.multiplier b : ℤ) *
        det (D.direction c) (D.direction b) := by
    conv_lhs => rw [hqrepr]
    simp [h₂, det]
    ring
  change det h₂ ((K.scale : ℤ) • q) ≠ 0
  rw [hh']
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt K.positive_scale))
    hqcoef) (by exact_mod_cast Nat.ne_of_gt (D.positive_multiplier b))) (D.distinct_directions hbc.symm)

end ConvexNivat
