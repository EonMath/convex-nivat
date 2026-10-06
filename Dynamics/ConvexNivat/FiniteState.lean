import ConvexNivat.ReductionDefinitions
import ConvexNivat.CorePeriods
import ConvexNivat.CoreLattice

namespace ConvexNivat
open scoped BigOperators

private theorem finite_trajectory {S : Type*} [Finite S] (x : ℕ → S)
    (hf : ∀ a b, x a = x b → x (a + 1) = x (b + 1))
    (hb : ∀ a b, x (a + 1) = x (b + 1) → x a = x b) :
    ∃ q : ℕ, 0 < q ∧ ∀ n, x (n + q) = x n := by
  classical
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite x
  have rewind : ∀ a d, x (a + d) = x a → x d = x 0 := by
    intro a
    induction a with
    | zero => intro d h; simpa using h
    | succ a ih =>
      intro d h
      apply ih d
      apply hb (a + d) a
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have finish : ∀ q, 0 < q → x q = x 0 →
      ∃ q : ℕ, 0 < q ∧ ∀ n, x (n + q) = x n := by
    intro q hq hx
    refine ⟨q, hq, ?_⟩
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf _ _ ih
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · apply finish (b - a) (by omega)
    apply rewind a
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hlt)] using heq.symm
  · apply finish (a - b) (by omega)
    apply rewind b
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hlt)] using heq

private theorem fs_row_add (B : LatticeBasis) (z w : Lattice) :
    B.row (z + w) = B.row z + B.row w := by
  simp only [LatticeBasis.row, det, Prod.fst_add, Prod.snd_add]
  ring

private theorem fs_row_smul (B : LatticeBasis) (n : ℤ) (z : Lattice) :
    B.row (n • z) = n * B.row z := by
  simp only [LatticeBasis.row, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private theorem fs_row_first (B : LatticeBasis) : B.row B.first = 0 := by
  simp only [LatticeBasis.row, det]
  ring

private theorem fs_row_second (B : LatticeBasis) : B.row B.second = 1 := by
  rcases B.unimodular with h | h <;> simp [LatticeBasis.row, h]

private theorem fs_row_sum {ι : Type*} (B : LatticeBasis) (C : Finset ι)
    (H : ι → Lattice) : B.row (∑ j ∈ C, H j) = ∑ j ∈ C, B.row (H j) := by
  classical
  induction C using Finset.induction_on with
  | empty => simp [LatticeBasis.row, det]
  | @insert a C ha ih => simp [Finset.sum_insert ha, fs_row_add, ih]

private theorem fs_coordinates (B : LatticeBasis) (z : Lattice) :
    ∃ s : ℤ, z = s • B.first + B.row z • B.second := by
  refine ⟨det B.first B.second * det z B.second, ?_⟩
  have hd : det B.first B.second * det B.first B.second = 1 := by
    rcases B.unimodular with h | h <;> simp [h]
  have hx : (det B.first B.second * det B.first B.second) • z =
      (det B.first B.second * det z B.second) • B.first +
      B.row z • B.second := by
    ext <;> simp [LatticeBasis.row, det] <;> ring
  simpa [hd] using hx

private theorem fs_extremes {ι : Type*} [Fintype ι] (β : ι → ℤ)
    (hβ : ∀ j, β j ≠ 0) :
    let Cminus := Finset.univ.filter (fun j => β j < 0)
    let Cplus := Finset.univ.filter (fun j => 0 < β j)
    let lo := ∑ j, min (β j) 0
    let hi := ∑ j, max (β j) 0
    (∑ j ∈ Cminus, β j) = lo ∧ (∑ j ∈ Cplus, β j) = hi ∧
    ∀ C : Finset ι,
      lo ≤ ∑ j ∈ C, β j ∧ (∑ j ∈ C, β j) ≤ hi ∧
      ((∑ j ∈ C, β j) = lo → C = Cminus) ∧
      ((∑ j ∈ C, β j) = hi → C = Cplus) := by
  classical
  dsimp
  have filterlo : (∑ j ∈ Finset.univ.filter (fun j => β j < 0), β j) =
      ∑ j, min (β j) 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with h <;> omega
  have filterhi : (∑ j ∈ Finset.univ.filter (fun j => 0 < β j), β j) =
      ∑ j, max (β j) 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with h <;> omega
  refine ⟨filterlo, filterhi, ?_⟩
  intro C
  have hsum : (∑ j ∈ C, β j) = ∑ j, if j ∈ C then β j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have low : ∀ j ∈ (Finset.univ : Finset ι),
      min (β j) 0 ≤ if j ∈ C then β j else 0 := by
    intro j hj
    split_ifs <;> omega
  have high : ∀ j ∈ (Finset.univ : Finset ι),
      (if j ∈ C then β j else 0) ≤ max (β j) 0 := by
    intro j hj
    split_ifs <;> omega
  rw [hsum]
  refine ⟨Finset.sum_le_sum low, Finset.sum_le_sum high, ?_, ?_⟩
  · intro h
    have he := (Finset.sum_eq_sum_iff_of_le low).mp h.symm
    ext j
    have hj := he j (Finset.mem_univ j)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hn := hβ j
    by_cases hm : j ∈ C <;> simp [hm] at hj ⊢ <;> omega
  · intro h
    have he := (Finset.sum_eq_sum_iff_of_le high).mp h
    ext j
    have hj := he j (Finset.mem_univ j)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hn := hβ j
    by_cases hm : j ∈ C <;> simp [hm] at hj ⊢ <;> omega

private theorem fs_row_sub (B : LatticeBasis) (z w : Lattice) :
    B.row (z - w) = B.row z - B.row w := by
  simp only [LatticeBasis.row, det, Prod.fst_sub, Prod.snd_sub]
  ring

private theorem fs_width_pos {r : ℕ} (hr : 0 < r) (β : Fin r → ℤ)
    (hβ : ∀ j, β j ≠ 0) :
    (∑ j, min (β j) 0) < ∑ j, max (β j) 0 := by
  apply Finset.sum_lt_sum
  · intro j hj
    omega
  · refine ⟨⟨0, hr⟩, Finset.mem_univ _, ?_⟩
    have h := hβ ⟨0, hr⟩
    omega

private theorem fs_difference_compare {ι A : Type*} [DecidableEq ι] [Ring A]
    (H : ι → Lattice) (I C₀ : Finset ι) (hC₀ : C₀ ⊆ I)
    (G : Configuration A) (z d : Lattice)
    (hz : mixedDifference H I G z = 0)
    (hzd : mixedDifference H I G (z + d) = 0)
    (heq : ∀ C ∈ I.powerset, C ≠ C₀ →
      G (z + ∑ j ∈ C, H j + d) = G (z + ∑ j ∈ C, H j)) :
    G (z + ∑ j ∈ C₀, H j + d) = G (z + ∑ j ∈ C₀, H j) := by
  classical
  have hmem : C₀ ∈ I.powerset := Finset.mem_powerset.mpr hC₀
  have hother :
      (∑ C ∈ I.powerset.erase C₀, (-1 : A) ^ (I.card - C.card) *
        G (z + d + ∑ j ∈ C, H j)) =
      ∑ C ∈ I.powerset.erase C₀, (-1 : A) ^ (I.card - C.card) *
        G (z + ∑ j ∈ C, H j) := by
    apply Finset.sum_congr rfl
    intro C hC
    rw [add_right_comm z d, heq C (Finset.mem_erase.mp hC).2
      (Finset.mem_erase.mp hC).1]
  unfold mixedDifference at hz hzd
  rw [← Finset.add_sum_erase _ _ hmem] at hz hzd
  rw [hother, add_right_comm z d] at hzd
  apply (isUnit_neg_one.pow (I.card - C₀.card)).mul_left_cancel
  exact add_right_cancel (hzd.trans hz.symm)

private theorem fs_top_compare {r A : Type*} [Fintype r] [DecidableEq r] [Ring A]
    (B : LatticeBasis) (H : r → Lattice) (hH : ∀ j, B.row (H j) ≠ 0)
    (G : Configuration A) (t₁ t₂ : ℤ)
    (hv₁ : ∀ z, B.row z = t₁ → mixedDifference H Finset.univ G z = 0)
    (hv₂ : ∀ z, B.row z = t₂ → mixedDifference H Finset.univ G z = 0)
    (heq : ∀ z, t₁ + (∑ j, min (B.row (H j)) 0) ≤ B.row z →
      B.row z < t₁ + (∑ j, max (B.row (H j)) 0) →
      G (z + (t₂ - t₁) • B.second) = G z) :
    ∀ z, B.row z = t₁ + (∑ j, max (B.row (H j)) 0) →
      G (z + (t₂ - t₁) • B.second) = G z := by
  classical
  let C₀ := Finset.univ.filter (fun j => 0 < B.row (H j))
  let a := ∑ j ∈ C₀, H j
  obtain ⟨hmin, hmax, hbounds⟩ := fs_extremes (fun j => B.row (H j)) hH
  have ha : B.row a = ∑ j, max (B.row (H j)) 0 := by
    rw [fs_row_sum]
    exact hmax
  intro z hz
  let w := z - a
  have hw : B.row w = t₁ := by
    dsimp [w]
    rw [fs_row_sub, hz, ha]
    omega
  have hw₂ : B.row (w + (t₂ - t₁) • B.second) = t₂ := by
    rw [fs_row_add, hw, fs_row_smul, fs_row_second]
    ring
  have hc := fs_difference_compare H Finset.univ C₀ (Finset.subset_univ _)
    G w ((t₂ - t₁) • B.second) (hv₁ w hw)
    (hv₂ _ hw₂) (by
      intro C hC hne
      have hb := hbounds C
      have hlt : (∑ j ∈ C, B.row (H j)) < ∑ j, max (B.row (H j)) 0 := by
        apply lt_of_le_of_ne hb.2.1
        intro he
        exact hne (hb.2.2.2 he)
      apply heq
      · rw [fs_row_add, hw, fs_row_sum]
        omega
      · rw [fs_row_add, hw, fs_row_sum]
        omega)
  simpa only [w, a, sub_add_cancel] using hc

private theorem fs_bottom_compare {r A : Type*} [Fintype r] [DecidableEq r] [Ring A]
    (B : LatticeBasis) (H : r → Lattice) (hH : ∀ j, B.row (H j) ≠ 0)
    (G : Configuration A) (t₁ t₂ : ℤ)
    (hv₁ : ∀ z, B.row z = t₁ → mixedDifference H Finset.univ G z = 0)
    (hv₂ : ∀ z, B.row z = t₂ → mixedDifference H Finset.univ G z = 0)
    (heq : ∀ z, t₁ + (∑ j, min (B.row (H j)) 0) < B.row z →
      B.row z ≤ t₁ + (∑ j, max (B.row (H j)) 0) →
      G (z + (t₂ - t₁) • B.second) = G z) :
    ∀ z, B.row z = t₁ + (∑ j, min (B.row (H j)) 0) →
      G (z + (t₂ - t₁) • B.second) = G z := by
  classical
  let C₀ := Finset.univ.filter (fun j => B.row (H j) < 0)
  let a := ∑ j ∈ C₀, H j
  obtain ⟨hmin, hmax, hbounds⟩ := fs_extremes (fun j => B.row (H j)) hH
  have ha : B.row a = ∑ j, min (B.row (H j)) 0 := by
    rw [fs_row_sum]
    exact hmin
  intro z hz
  let w := z - a
  have hw : B.row w = t₁ := by
    dsimp [w]
    rw [fs_row_sub, hz, ha]
    omega
  have hw₂ : B.row (w + (t₂ - t₁) • B.second) = t₂ := by
    rw [fs_row_add, hw, fs_row_smul, fs_row_second]
    ring
  have hc := fs_difference_compare H Finset.univ C₀ (Finset.subset_univ _)
    G w ((t₂ - t₁) • B.second) (hv₁ w hw)
    (hv₂ _ hw₂) (by
      intro C hC hne
      have hb := hbounds C
      have hlt : (∑ j, min (B.row (H j)) 0) < ∑ j ∈ C, B.row (H j) := by
        apply lt_of_le_of_ne hb.1
        intro he
        exact hne (hb.2.2.1 he.symm)
      apply heq
      · rw [fs_row_add, hw, fs_row_sum]
        omega
      · rw [fs_row_add, hw, fs_row_sum]
        omega)
  simpa only [w, a, sub_add_cancel] using hc

private def fs_state {A : Type*} (G : Configuration A) (B : LatticeBasis)
    (k L : ℕ) (lo t : ℤ) : Fin L → Fin k → A :=
  fun i j => G ((j : ℤ) • B.first + (t + lo + (i : ℤ)) • B.second)

private theorem fs_horizontal_reduce {A : Type*} (G : Configuration A)
    (B : LatticeBasis) (k : ℕ) (hp : HasPeriod G ((k : ℤ) • B.first)) (s t : ℤ) :
    G (s • B.first + t • B.second) =
      G ((s % (k : ℤ)) • B.first + t • B.second) := by
  have he := hasPeriod_zsmul G ((k : ℤ) • B.first) hp (s / (k : ℤ))
  have hs := Int.emod_add_mul_ediv s (k : ℤ)
  have hz : (s % (k : ℤ)) • B.first + t • B.second +
      (s / (k : ℤ)) • ((k : ℤ) • B.first) = s • B.first + t • B.second := by
    rw [smul_smul, mul_comm (s / (k : ℤ))]
    calc
      _ = (s % (k : ℤ) + (k : ℤ) * (s / (k : ℤ))) • B.first +
          t • B.second := by rw [add_smul]; abel
      _ = _ := by rw [hs]
  simpa only [hz] using he ((s % (k : ℤ)) • B.first + t • B.second)

private theorem fs_state_eq_iff {A : Type*} (G : Configuration A) (B : LatticeBasis)
    (k : ℕ) (hk : 0 < k) (hp : HasPeriod G ((k : ℤ) • B.first))
    (L : ℕ) (lo t₁ t₂ : ℤ) :
    fs_state G B k L lo t₁ = fs_state G B k L lo t₂ ↔
    ∀ z, t₁ + lo ≤ B.row z → B.row z < t₁ + lo + (L : ℤ) →
      G (z + (t₂ - t₁) • B.second) = G z := by
  constructor
  · intro heq z hz₁ hz₂
    obtain ⟨s, hs⟩ := fs_coordinates B z
    have hkn : (0 : ℤ) < k := by exact_mod_cast hk
    have hmod₁ := Int.emod_nonneg s (ne_of_gt hkn)
    have hmod₂ := Int.emod_lt_of_pos s hkn
    let i : Fin L := ⟨(B.row z - (t₁ + lo)).toNat, by omega⟩
    let j : Fin k := ⟨(s % (k : ℤ)).toNat, by omega⟩
    have hi : (i : ℤ) = B.row z - (t₁ + lo) := by
      exact Int.toNat_of_nonneg (by omega)
    have hj : (j : ℤ) = s % (k : ℤ) := by
      exact Int.toNat_of_nonneg hmod₁
    have hvalues := congrFun (congrFun heq i) j
    dsimp [fs_state] at hvalues
    rw [hi, hj] at hvalues
    have ht₁ : t₁ + lo + (B.row z - (t₁ + lo)) = B.row z := by ring
    have ht₂ : t₂ + lo + (B.row z - (t₁ + lo)) = B.row z + (t₂ - t₁) := by ring
    rw [ht₁, ht₂] at hvalues
    calc
      G (z + (t₂ - t₁) • B.second) =
          G (s • B.first + (B.row z + (t₂ - t₁)) • B.second) := by
        conv_lhs => rw [hs]
        rw [add_smul]; congr 1; abel
      _ = G ((s % (k : ℤ)) • B.first +
          (B.row z + (t₂ - t₁)) • B.second) := fs_horizontal_reduce G B k hp _ _
      _ = G ((s % (k : ℤ)) • B.first + B.row z • B.second) := hvalues.symm
      _ = G (s • B.first + B.row z • B.second) :=
        (fs_horizontal_reduce G B k hp _ _).symm
      _ = G z := by rw [← hs]
  · intro heq
    funext i j
    let z := (j : ℤ) • B.first + (t₁ + lo + (i : ℤ)) • B.second
    have hz : B.row z = t₁ + lo + (i : ℤ) := by
      dsimp [z]
      rw [fs_row_add, fs_row_smul, fs_row_smul, fs_row_first, fs_row_second]
      ring
    have hi₁ : (0 : ℤ) ≤ i := by exact_mod_cast (Nat.zero_le i.val)
    have hi₂ : (i : ℤ) < L := by exact_mod_cast i.isLt
    have he := heq z (by omega) (by omega)
    have hshift : z + (t₂ - t₁) • B.second =
        (j : ℤ) • B.first + (t₂ + lo + (i : ℤ)) • B.second := by
      dsimp [z]
      rw [add_assoc, ← add_smul]
      congr 2
      ring
    dsimp [fs_state]
    exact (hshift ▸ he).symm

private theorem fs_state_transition {r A : Type*} [Fintype r] [DecidableEq r]
    [Ring A] (G : Configuration A) (B : LatticeBasis) (k : ℕ) (hk : 0 < k)
    (hp : HasPeriod G ((k : ℤ) • B.first)) (H : r → Lattice)
    (hH : ∀ j, B.row (H j) ≠ 0) (L : ℕ)
    (hL : (L : ℤ) = (∑ j, max (B.row (H j)) 0) - ∑ j, min (B.row (H j)) 0)
    (t₁ t₂ : ℤ)
    (hv₁ : ∀ z, B.row z = t₁ → mixedDifference H Finset.univ G z = 0)
    (hv₂ : ∀ z, B.row z = t₂ → mixedDifference H Finset.univ G z = 0) :
    let lo := ∑ j, min (B.row (H j)) 0
    (fs_state G B k L lo t₁ = fs_state G B k L lo t₂ →
      fs_state G B k L lo (t₁ + 1) = fs_state G B k L lo (t₂ + 1)) ∧
    (fs_state G B k L lo (t₁ + 1) = fs_state G B k L lo (t₂ + 1) →
      fs_state G B k L lo t₁ = fs_state G B k L lo t₂) := by
  dsimp
  constructor
  · intro hs
    have he := (fs_state_eq_iff G B k hk hp L _ t₁ t₂).mp hs
    have ht := fs_top_compare B H hH G t₁ t₂ hv₁ hv₂ (by
      intro z hz₁ hz₂
      apply he z hz₁
      omega)
    apply (fs_state_eq_iff G B k hk hp L _ (t₁ + 1) (t₂ + 1)).mpr
    intro z hz₁ hz₂
    have hd : t₂ + 1 - (t₁ + 1) = t₂ - t₁ := by ring
    rw [hd]
    by_cases hz : B.row z < t₁ + ∑ j, max (B.row (H j)) 0
    · apply he z <;> omega
    · apply ht z
      omega
  · intro hs
    have he := (fs_state_eq_iff G B k hk hp L _ (t₁ + 1) (t₂ + 1)).mp hs
    have hd : t₂ + 1 - (t₁ + 1) = t₂ - t₁ := by ring
    have hb := fs_bottom_compare B H hH G t₁ t₂ hv₁ hv₂ (by
      intro z hz₁ hz₂
      rw [← hd]
      apply he z <;> omega)
    apply (fs_state_eq_iff G B k hk hp L _ t₁ t₂).mpr
    intro z hz₁ hz₂
    by_cases hz : t₁ + (∑ j, min (B.row (H j)) 0) < B.row z
    · rw [← hd]
      apply he z <;> omega
    · apply hb z
      omega

private theorem fs_half_state {A : Type*} [Ring A] [Finite A]
    (G : Configuration A) (B : LatticeBasis) (k : ℕ) (hk : 0 < k)
    (hp : HasPeriod G ((k : ℤ) • B.first)) (r : ℕ) (hr : 0 < r)
    (H : Fin r → Lattice) (hH : ∀ j, B.row (H j) ≠ 0) (c : ℤ)
    (hv : ∀ z, c ≤ B.row z → mixedDifference H Finset.univ G z = 0) :
    let lo := ∑ j, min (B.row (H j)) 0
    let L := ((∑ j, max (B.row (H j)) 0) - lo).toNat
    ∃ q : ℕ, 0 < q ∧ ∀ n : ℕ,
      fs_state G B k L lo (c + (n : ℤ) + (q : ℤ)) =
        fs_state G B k L lo (c + (n : ℤ)) := by
  let lo := ∑ j, min (B.row (H j)) 0
  let hi := ∑ j, max (B.row (H j)) 0
  let L := (hi - lo).toNat
  have hwidth : lo < hi := fs_width_pos hr _ hH
  have hL : (L : ℤ) = hi - lo := Int.toNat_of_nonneg (by omega)
  let x : ℕ → Fin L → Fin k → A := fun n => fs_state G B k L lo (c + (n : ℤ))
  have htrans := fun a b : ℕ => fs_state_transition G B k hk hp H hH L hL
    (c + (a : ℤ)) (c + (b : ℤ))
    (fun z hz => hv z (by omega)) (fun z hz => hv z (by omega))
  obtain ⟨q, hq, heq⟩ := finite_trajectory x
    (by
      intro a b h
      have he := (htrans a b).1 h
      simpa only [x, Nat.cast_add, Nat.cast_one, add_assoc] using he)
    (by
      intro a b h
      apply (htrans a b).2
      simpa only [x, Nat.cast_add, Nat.cast_one, add_assoc] using h)
  refine ⟨q, hq, ?_⟩
  intro n
  simpa only [x, Nat.cast_add, add_assoc] using heq n

private theorem fs_half_period {A : Type*} [Ring A] [Finite A]
    (G : Configuration A) (B : LatticeBasis) (k : ℕ) (hk : 0 < k)
    (hp : HasPeriod G ((k : ℤ) • B.first)) (r : ℕ) (hr : 0 < r)
    (H : Fin r → Lattice) (hH : ∀ j, B.row (H j) ≠ 0) (c : ℤ)
    (hv : ∀ z, c ≤ B.row z → mixedDifference H Finset.univ G z = 0) :
    ∃ q : ℕ, 0 < q ∧ ∀ z, c + (∑ j, min (B.row (H j)) 0) ≤ B.row z →
      G (z + (q : ℤ) • B.second) = G z := by
  let lo := ∑ j, min (B.row (H j)) 0
  let hi := ∑ j, max (B.row (H j)) 0
  let L := (hi - lo).toNat
  have hwidth : lo < hi := fs_width_pos hr _ hH
  have hL : (L : ℤ) = hi - lo := Int.toNat_of_nonneg (by omega)
  obtain ⟨q, hq, hs⟩ := fs_half_state G B k hk hp r hr H hH c hv
  refine ⟨q, hq, ?_⟩
  intro z hz
  let n := (B.row z - (c + lo)).toNat
  have hn : (n : ℤ) = B.row z - (c + lo) := Int.toNat_of_nonneg (by omega)
  have he := (fs_state_eq_iff G B k hk hp L lo
    (c + (n : ℤ)) (c + (n : ℤ) + (q : ℤ))).mp (hs n).symm
  have hd : c + (n : ℤ) + (q : ℤ) - (c + (n : ℤ)) = q := by ring
  rw [hd] at he
  apply he z <;> omega

private theorem fs_nonparallel (B : LatticeBasis) (k q : ℕ)
    (hk : 0 < k) (hq : 0 < q) :
    Nonparallel ((k : ℤ) • B.first) ((q : ℤ) • B.second) := by
  have hk₀ : (k : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hq₀ : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hdet : det B.first B.second ≠ 0 := by
    rcases B.unimodular with h | h <;> omega
  have he : det ((k : ℤ) • B.first) ((q : ℤ) • B.second) =
      (k : ℤ) * (q : ℤ) * det B.first B.second := by
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  change det ((k : ℤ) • B.first) ((q : ℤ) • B.second) ≠ 0
  rw [he]
  exact mul_ne_zero (mul_ne_zero hk₀ hq₀) hdet

/-- 8.8: lower-row shift β₋ is the sum of every negative transverse exponent. -/
theorem lemma8_8 (p : ℕ) (hp : p.Prime) (G : Configuration (ZMod p))
    (B : LatticeBasis) (hprimitive : Primitive B.first)
    (k : ℕ) (hk : 0 < k) (hperiod : HasPeriod G ((k : ℤ) • B.first))
    (r : ℕ) (hr : 0 < r) (H : Fin r → Lattice)
    (htransverse : ∀ j, B.row (H j) ≠ 0) (c : ℤ)
    (hvanishes : ∀ z, c ≤ B.row z → mixedDifference H Finset.univ G z = 0) :
    let βminus := ∑ j : Fin r, min (B.row (H j)) 0
    ∃ q : ℕ, 0 < q ∧
      (∀ z, c + βminus ≤ B.row z → G (z + (q : ℤ) • B.second) = G z) ∧
      FullPeriods G {z | c + βminus ≤ B.row z}
        ((k : ℤ) • B.first) ((q : ℤ) • B.second) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  dsimp
  obtain ⟨q, hq, heq⟩ := fs_half_period G B k hk hperiod r hr H htransverse c hvanishes
  refine ⟨q, hq, heq, ?_⟩
  refine ⟨?_, fs_nonparallel B k q hk hq, ?_, ?_, ?_, heq⟩
  · refine ⟨(c + (∑ j, min (B.row (H j)) 0)) • B.second, ?_⟩
    simp only [Set.mem_ofPred_eq, fs_row_smul, fs_row_second, mul_one, le_refl]
  · intro z hz
    simpa only [Set.mem_ofPred_eq, fs_row_add, fs_row_smul, fs_row_first,
      mul_zero, add_zero] using hz
  · intro z hz
    change c + (∑ j, min (B.row (H j)) 0) ≤ B.row (z + (q : ℤ) • B.second)
    rw [fs_row_add, fs_row_smul, fs_row_second, mul_one]
    have hq₀ : (0 : ℤ) < q := by exact_mod_cast hq
    exact le_trans hz (by omega)
  · intro z hz
    exact hperiod z

theorem lemma8_8_global (p : ℕ) (hp : p.Prime) (G : Configuration (ZMod p))
    (B : LatticeBasis) (hprimitive : Primitive B.first)
    (k : ℕ) (hk : 0 < k) (hperiod : HasPeriod G ((k : ℤ) • B.first))
    (r : ℕ) (hr : 0 < r) (H : Fin r → Lattice)
    (htransverse : ∀ j, B.row (H j) ≠ 0)
    (hvanishes : ∀ z, mixedDifference H Finset.univ G z = 0) :
    DoublyPeriodic G := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let lo := ∑ j, min (B.row (H j)) 0
  obtain ⟨q, hq, hupper⟩ := fs_half_period G B k hk hperiod r hr H htransverse 0
    (fun z hz => hvanishes z)
  have hdown : ∀ n : ℕ, ∀ z, lo - (n : ℤ) ≤ B.row z →
      G (z + (q : ℤ) • B.second) = G z := by
    intro n
    induction n with
    | zero =>
      intro z hz
      apply hupper z
      simpa only [Nat.cast_zero, sub_zero, zero_add] using hz
    | succ n ih =>
      intro z hz
      by_cases hprev : lo - (n : ℤ) ≤ B.row z
      · exact ih z hprev
      · let t := lo - ((n + 1 : ℕ) : ℤ) - lo
        have he := fs_bottom_compare B H htransverse G t (t + (q : ℤ))
          (fun w hw => hvanishes w) (fun w hw => hvanishes w)
          (by
            intro w hw₁ hw₂
            have hw : lo - (n : ℤ) ≤ B.row w := by
              dsimp [t, lo] at hw₁ ⊢
              omega
            have hd : t + (q : ℤ) - t = q := by ring
            rw [hd]
            exact ih w hw) z (by
            dsimp [t, lo]
            push_cast at hz ⊢
            omega)
        have hd : t + (q : ℤ) - t = q := by ring
        simpa only [hd] using he
  refine ⟨(k : ℤ) • B.first, (q : ℤ) • B.second,
    fs_nonparallel B k q hk hq, hperiod, ?_⟩
  intro z
  apply hdown (lo - B.row z).toNat z
  omega

end ConvexNivat
