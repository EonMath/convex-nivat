import ConvexNivat.Colle.GP.ProductHull
import ConvexNivat.Colle.Shared.RowCoordinates
import ConvexNivat.Colle.Shared.CycleAlignment
import ConvexNivat.Colle.GeneratingOrder

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

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
  have hz : det u 0=det u v := by simp [det] at hdet ⊢; exact hdet.symm
  obtain ⟨k,hk⟩ := (primitive_row_coordinates u hu).2.1 0 v |>.mp hz
  simp only [zero_add] at hk
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


private theorem cycle_row_length {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S) (j : ℤ)
    (n : ℤ) (hn : 0 ≤ n)
    (he : C.vertex (j + 1) - C.vertex j = n • C.direction j) :
    ((supportRow S (C.direction j)).card : ℤ) = n + 1 := by
  classical
  have hev : C.vertex (j + 1) = C.vertex j + n • C.direction j := by
    exact sub_eq_iff_eq_add.mp he |>.trans (add_comm _ _)
  let f : ℤ → Lattice := fun k => C.vertex j + k • C.direction j
  have hinj : Function.Injective f := by
    intro a b hab
    have hs : (a - b) • C.direction j = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr (add_left_cancel hab)
    have hv := primitive_ne_zero _ (C.primitive j)
    by_cases h₁ : (C.direction j).1 = 0
    · have h₂ : (C.direction j).2 ≠ 0 := fun hh => hv (Prod.ext h₁ hh)
      have hs₂ : (a - b) * (C.direction j).2 = 0 := congrArg Prod.snd hs
      exact sub_eq_zero.mp ((mul_eq_zero.mp hs₂).resolve_right h₂)
    · have hs₁ : (a - b) * (C.direction j).1 = 0 := congrArg Prod.fst hs
      exact sub_eq_zero.mp ((mul_eq_zero.mp hs₁).resolve_right h₁)
  have hset : supportRow S (C.direction j) = (Finset.Icc 0 n).image f := by
    ext z
    rw [C.support_segment j, hev]
    have hseg := (primitive_row_coordinates (C.direction j) (C.primitive j)).2.2
      (C.vertex j) 0 n hn z
    simp only [zero_smul, add_zero] at hseg
    constructor
    · rintro ⟨hz, hzs⟩
      obtain ⟨k, hk0, hkn, rfl⟩ := hseg.mp hzs
      exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk0, hkn⟩, rfl⟩
    · intro hz
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
      have hs : embed (f k) ∈ segment ℝ (embed (C.vertex j))
          (embed (C.vertex j + n • C.direction j)) :=
        hseg.mpr ⟨k, (Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2, rfl⟩
      refine ⟨(hS _).mp ?_, hs⟩
      apply (convex_convexHull ℝ _).segment_subset ?_ ?_ hs
      · exact (hS _).mpr (Finset.mem_filter.mp (C.initial_mem j)).1
      · rw [← hev]
        exact (hS _).mpr (Finset.mem_filter.mp (C.terminal_mem j)).1
  rw [hset, Finset.card_image_of_injective _ hinj, Int.card_Icc]
  omega

private theorem aligned_length_dominates {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S)
    (P : AlignedBoundary C B) (j : ℤ) (n : ℤ) (hn : 1 ≤ n)
    (he : C.vertex (j + 1) - C.vertex j = n • C.direction j) :
    n ≤ (P.length j : ℤ) := by
  have hr := cycle_row_length C hS j n (by omega) he
  have hl := P.source_length_le j
  omega

private theorem path_le_of_steps (f : ℤ → ℤ) (a : ℤ) (n : ℕ)
    (hstep : ∀ k < n, f (a + k) ≤ f (a + k + 1)) : f a ≤ f (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfirst := ih (fun k hk => hstep k (by omega))
    have hlast := hstep n (Nat.lt_succ_self n)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hfirst.trans hlast

private theorem periodic_support_of_edges {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m)
    (horder : ∀ i j : ℤ, i < j → j < i + m →
      0 < det (C.direction i) (C.direction j))
    (Q : ℤ → Lattice) (a : ℤ → ℤ)
    (hperiod : ∀ i, Q (i + 2 * (m : ℤ)) = Q i)
    (ha : ∀ j, 0 ≤ a j)
    (hedge : ∀ j, Q (j + 1) - Q j = a j • C.direction j) :
    ∀ i j, 0 ≤ det (C.direction j) (Q i - Q j) := by
  have hm := C.at_least_two
  have hdelta (j t : ℤ) :
      det (C.direction j) (Q (t + 1)) - det (C.direction j) (Q t) =
        a t * det (C.direction j) (C.direction t) := by
    have he := congrArg (det (C.direction j)) (hedge t)
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at he ⊢
    nlinarith [he]
  have hforward (j : ℤ) (n : ℕ) (hn : n ≤ m) :
      det (C.direction j) (Q j) ≤ det (C.direction j) (Q (j + n)) := by
    apply path_le_of_steps (fun t => det (C.direction j) (Q t)) j n
    intro k hk
    have hd : 0 ≤ det (C.direction j) (C.direction (j + k)) := by
      by_cases hk0 : k = 0
      · simp [hk0, det, mul_comm]
      · exact (horder j (j + k) (by omega) (by omega)).le
    have he := hdelta j (j + k)
    nlinarith [mul_nonneg (ha (j + k)) hd]
  have hbackward (j : ℤ) (n : ℕ) (hn : m ≤ n) (hn2 : n ≤ 2 * m) :
      det (C.direction j) (Q (j + 2 * m)) ≤ det (C.direction j) (Q (j + n)) := by
    have hp := path_le_of_steps (fun t => -det (C.direction j) (Q t))
      (j + n) (2 * m - n) (by
        intro k hk
        have hd : det (C.direction j) (C.direction (j + n + k)) ≤ 0 := by
          by_cases heq : n + k = m
          · have he : j + (n : ℤ) + k = j + m := by omega
            rw [he, C.antipodal]
            simp [det, mul_comm]
          · have he := horder (j + m) (j + n + k) (by omega) (by omega)
            rw [C.antipodal] at he
            have hneg : det (-C.direction j) (C.direction (j + n + k)) =
                -det (C.direction j) (C.direction (j + n + k)) := by simp [det]; ring
            rw [hneg] at he
            omega
        have he := hdelta j (j + n + k)
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (ha (j + n + k)) hd])
    have he : j + (n : ℤ) + (2 * m - n : ℕ) = j + 2 * m := by omega
    rw [he] at hp
    omega
  intro i j
  let p : ℤ := 2 * (m : ℤ)
  have hp : 0 < p := by dsimp [p]; omega
  let n : ℕ := ((i - j) % p).toNat
  have hn : (n : ℤ) = (i - j) % p := Int.toNat_of_nonneg (Int.emod_nonneg _ hp.ne')
  have hnlt : n < 2 * m := by have ht := Int.emod_lt_of_pos (i - j) hp; omega
  have heQ : Q (j + n) = Q i := by
    have hper : Function.Periodic Q p := hperiod
    have he := hper.sub_int_mul_eq (x := i) ((i - j) / p)
    have hemod := Int.emod_add_ediv_mul (i - j) p
    have hx : j + (n : ℤ) = i - ((i - j) / p) * p := by omega
    rw [hx]
    simpa only [Int.cast_id] using he
  have hh : det (C.direction j) (Q j) ≤ det (C.direction j) (Q (j + n)) := by
    by_cases hnle : n ≤ m
    · exact hforward j n hnle
    · have hb := hbackward j n (by omega) (by omega)
      rwa [hperiod] at hb
  rw [heQ] at hh
  have he : det (C.direction j) (Q i - Q j) =
      det (C.direction j) (Q i) - det (C.direction j) (Q j) := by simp [det]; ring
  rw [he]
  omega

private theorem aligned_translated_containment {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S) (hB : LatticeConvex B)
    (P : AlignedBoundary C B)
    (horder : ∀ i j : ℤ, i < j → j < i + m →
      0 < det (C.direction i) (C.direction j)) (i : ℤ) :
    (windowTranslate S (P.vertex i - C.vertex i) : Set Lattice) ⊆ B := by
  classical
  let l : ℤ → ℤ := fun j => (C.edge_length j).choose
  have hl (j : ℤ) : 1 ≤ l j ∧
      C.vertex (j + 1) - C.vertex j = l j • C.direction j :=
    (C.edge_length j).choose_spec
  let Q : ℤ → Lattice := fun j => P.vertex j - C.vertex j
  let a : ℤ → ℤ := fun j => (P.length j : ℤ) - l j
  have ha : ∀ j, 0 ≤ a j := by
    intro j
    exact sub_nonneg.mpr (aligned_length_dominates C hS P j (l j) (hl j).1 (hl j).2)
  have hperiod : ∀ j, Q (j + 2 * (m : ℤ)) = Q j := by
    intro j
    simp only [Q, P.vertex_periodic, C.vertex_periodic]
  have hedge : ∀ j, Q (j + 1) - Q j = a j • C.direction j := by
    intro j
    calc
      Q (j + 1) - Q j = (P.vertex (j + 1) - P.vertex j) -
          (C.vertex (j + 1) - C.vertex j) := by dsimp [Q]; abel
      _ = (P.length j : ℤ) • C.direction j - l j • C.direction j := by
        rw [P.edge_eq, (hl j).2]
      _ = a j • C.direction j := (sub_smul _ _ _).symm
  have hQ := periodic_support_of_edges C horder Q a hperiod ha hedge
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  apply (hB _).mp
  rw [P.hull_eq]
  intro j
  have hrow := (Finset.mem_filter.mp (C.initial_mem j)).2 x hx
  have hsource : 0 ≤ det (C.direction j) (x - C.vertex j) := by
    simp only [normal_height] at hrow
    have hh : det (C.direction j) (C.vertex j) ≤ det (C.direction j) x := by
      exact_mod_cast hrow
    dsimp [det] at hh ⊢
    nlinarith
  have hres := hQ i j
  have hsum : 0 ≤ det (C.direction j)
      (x + (P.vertex i - C.vertex i) - P.vertex j) := by
    have he : det (C.direction j) (x + (P.vertex i - C.vertex i) - P.vertex j) =
        det (C.direction j) (x - C.vertex j) + det (C.direction j) (Q i - Q j) := by
      dsimp [Q, det]
      ring
    rw [he]
    exact add_nonneg hsource hres
  have he : realDet (embed (C.direction j))
      (embed (x + (P.vertex i - C.vertex i)) - embed (P.vertex j)) =
      (det (C.direction j) (x + (P.vertex i - C.vertex i) - P.vertex j) : ℝ) := by
    simp [realDet, embed, det]
  rw [he]
  exact_mod_cast hsum

private theorem aligned_translated_containment_unconditional
    {S B : Finset Lattice} {m : ℕ} (C : AntipodalEdgeCycle S m)
    (hS : LatticeConvex S) (hB : LatticeConvex B) (P : AlignedBoundary C B) (i : ℤ) :
    (windowTranslate S (P.vertex i - C.vertex i) : Set Lattice) ⊆ B := by
  exact aligned_translated_containment C hS hB P (cycle_half_order C) i


private theorem tangent_unique {m : ℕ} (h : Fin m → Lattice)
    (hpair : Pairwise (fun i j => Nonparallel (h i) (h j)))
    (v : Lattice) (hv : v ≠ 0) {i j : Fin m}
    (hi : det v (h i) = 0) (hj : det v (h j) = 0) : i = j := by
  by_contra hij
  apply hpair hij
  by_cases hv₁ : v.1 = 0
  · have hv₂ : v.2 ≠ 0 := fun hz => hv (Prod.ext hv₁ hz)
    have he : det (h i) (h j) * v.2 = (h j).2 * det (h i) v - (h i).2 * det (h j) v := by
      dsimp [det]
      ring
    have hi' : det (h i) v = 0 := by dsimp [det] at hi ⊢; nlinarith
    have hj' : det (h j) v = 0 := by dsimp [det] at hj ⊢; nlinarith
    rw [hi', hj'] at he
    exact (mul_eq_zero.mp (by simpa using he)).resolve_right hv₂
  · have he : det (h i) (h j) * v.1 = (h j).1 * det (h i) v - (h i).1 * det (h j) v := by
      dsimp [det]
      ring
    have hi' : det (h i) v = 0 := by dsimp [det] at hi ⊢; nlinarith
    have hj' : det (h j) v = 0 := by dsimp [det] at hj ⊢; nlinarith
    rw [hi', hj'] at he
    exact (mul_eq_zero.mp (by simpa using he)).resolve_right hv₁

private theorem deleted_polynomial_nonzero (m : ℕ) (h : Fin m → Lattice)
    (hne : ∀ j, h j ≠ 0) (k : Fin m) : differenceWithout m h k ≠ 0 := by
  classical
  have hf (j : Fin m) :
      (AddMonoidAlgebra.single (h j) (1 : ℤ) - AddMonoidAlgebra.single 0 1) ≠ 0 := by
    intro he
    have he' := congrArg (fun p : AddMonoidAlgebra ℤ Lattice => p.coeff (h j))
      (sub_eq_zero.mp he)
    simpa [hne j] using he'
  have hp := Finset.prod_ne_zero_iff.mpr (fun j (_ : j ∈ Finset.univ.erase k) => hf j)
  intro hz
  exact hp (congrArg AddMonoidAlgebra.ofCoeff hz)

private theorem segment_sum_support_singleton (G H : Finset Lattice)
    (hconvex : LatticeConvex G) (hHull : windowHull G = realSegmentSum H)
    (v : Lattice) (htrans : ∀ u ∈ H, det v u ≠ 0) :
    (supportRow G v).card = 1 := by
  classical
  let b : Lattice → ℝ := fun u => if 0 < det v u then 1 else 0
  let q : Lattice := ∑ u ∈ H, if 0 < det v u then -u else 0
  have hb (u : Lattice) : 0 ≤ b u ∧ b u ≤ 1 := by
    dsimp [b]
    split_ifs <;> norm_num
  have hembed : embed q = ∑ u ∈ H, b u • embed (-u) := by
    ext <;> simp [q, b, embed, Prod.fst_sum, Prod.snd_sum]
    all_goals
      apply Finset.sum_congr rfl
      intro u hu
      split_ifs <;> simp
  have hq : q ∈ G := by
    apply (hconvex q).mp
    rw [hHull]
    exact ⟨b, fun u _ => hb u, hembed⟩
  have hdot (t : ℝ) (u : Lattice) :
      realDot (t • embed (-u)) (normal v) = -t * (det v u : ℝ) := by
    simp only [realDot, embed, normal, det, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_neg, Prod.snd_neg, Int.cast_neg, Int.cast_sub, Int.cast_mul,
      smul_eq_mul]
    ring
  have hsumdot (a : Lattice → ℝ) :
      realDot (∑ u ∈ H, a u • embed (-u)) (normal v) =
        ∑ u ∈ H, -(a u) * (det v u : ℝ) := by
    have hs : realDot (∑ u ∈ H, a u • embed (-u)) (normal v) =
        ∑ u ∈ H, realDot (a u • embed (-u)) (normal v) := by
      simp [realDot, Prod.fst_sum, Prod.snd_sum, Finset.sum_mul, Finset.sum_add_distrib]
    simpa only [hdot] using hs
  have hterm (a : Lattice → ℝ) (ha : ∀ u ∈ H, 0 ≤ a u ∧ a u ≤ 1)
      (u : Lattice) (hu : u ∈ H) :
      -(b u) * (det v u : ℝ) ≤ -(a u) * (det v u : ℝ) := by
    obtain ⟨ha0, ha1⟩ := ha u hu
    by_cases hd : 0 < det v u
    · have hd' : (0 : ℝ) < (det v u : ℝ) := by exact_mod_cast hd
      simp only [b, if_pos hd]
      nlinarith
    · have hd' : (det v u : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hd)
      simp only [b, if_neg hd]
      nlinarith
  have hmin (z : Lattice) (hz : z ∈ G) :
      realDot (embed q) (normal v) ≤ realDot (embed z) (normal v) := by
    have hh := (hconvex z).mpr hz
    rw [hHull] at hh
    obtain ⟨a, ha, he⟩ := hh
    rw [hembed, he, hsumdot, hsumdot]
    exact Finset.sum_le_sum (hterm a ha)
  have hqrow : q ∈ supportRow G v := by
    exact Finset.mem_filter.mpr ⟨hq, hmin⟩
  apply Finset.card_eq_one.mpr
  refine ⟨q, Finset.eq_singleton_iff_unique_mem.mpr ⟨hqrow, ?_⟩⟩
  intro z hz
  have hzG := (Finset.mem_filter.mp hz).1
  have hh := (hconvex z).mpr hzG
  rw [hHull] at hh
  obtain ⟨a, ha, he⟩ := hh
  have heq : (∑ u ∈ H, -(b u) * (det v u : ℝ)) =
      ∑ u ∈ H, -(a u) * (det v u : ℝ) := by
    have hzmin := (Finset.mem_filter.mp hz).2 q hq
    have hqmin := hmin z hzG
    have hdotEq := le_antisymm hqmin hzmin
    rw [hembed, he, hsumdot, hsumdot] at hdotEq
    exact hdotEq
  have hsame := (Finset.sum_eq_sum_iff_of_le (hterm a ha)).mp heq
  have hab : ∀ u ∈ H, a u = b u := by
    intro u hu
    have hd : (det v u : ℝ) ≠ 0 := by exact_mod_cast htrans u hu
    have hs := mul_right_cancel₀ hd (hsame u hu)
    exact neg_injective hs.symm
  have he' : embed z = embed q := by
    rw [he, hembed]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hab u hu]
  apply Prod.ext
  · exact Int.cast_injective (congrArg Prod.fst he')
  · exact Int.cast_injective (congrArg Prod.snd he')

private theorem segment_sum_injective_image {ι : Type*} (I : Finset ι)
    (h : ι → Lattice) (hinj : Function.Injective h) :
    realSegmentSum (I.image h) = {x | ∃ a : ι → ℝ,
      (∀ i ∈ I, 0 ≤ a i ∧ a i ≤ 1) ∧ x = ∑ i ∈ I, a i • embed (-h i)} := by
  classical
  ext x
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨fun i => a (h i), fun i hi => ha (h i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩), ?_⟩
    rw [Finset.sum_image hinj.injOn] at he
    exact he
  · rintro ⟨a, ha, he⟩
    let b := Function.extend h a (fun _ => 0)
    have hb (i : ι) : b (h i) = a i := hinj.extend_apply a (fun _ => 0) i
    refine ⟨b, ?_, ?_⟩
    · rintro _ hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      rw [hb]
      exact ha i hi
    · rw [Finset.sum_image hinj.injOn]
      simpa only [hb] using he

private theorem erased_family_reindex (m : ℕ) (h : Fin m → Lattice)
    (hne : ∀ i, h i ≠ 0) (hinj : Function.Injective h) (k : Fin m) :
    ∃ n : ℕ, ∃ g : Fin n → Lattice,
      (∀ i, g i ≠ 0) ∧ Function.Injective g ∧
      differenceWithout m h k = differenceFactors n g ∧
      realSegmentSum ((Finset.univ.erase k).image h) =
        {x | ∃ a : Fin n → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧
          x = ∑ i, a i • embed (-g i)} := by
  classical
  let I := Finset.univ.erase k
  let e : Fin I.card ≃ I := I.equivFin.symm
  let g : Fin I.card → Lattice := fun i => h (e i).val
  have hg : Function.Injective g := by
    intro i j he
    apply e.injective
    apply Subtype.ext
    exact hinj he
  refine ⟨I.card, g, fun i => hne (e i).val, hg, ?_, ?_⟩
  · unfold differenceWithout differenceFactors
    congr 1
    change (∏ j ∈ I, (AddMonoidAlgebra.single (h j) (1 : ℤ) -
      AddMonoidAlgebra.single 0 1)) = _
    rw [Finset.prod_subtype I (fun _ => Iff.rfl)]
    exact (Equiv.prod_comp e
      (fun j : I => AddMonoidAlgebra.single (h j.val) (1 : ℤ) -
        AddMonoidAlgebra.single 0 1)).symm
  · have himage : I.image h = Finset.univ.image g := by
      ext u
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨e.symm ⟨j, hj⟩, by simp [g]⟩
      · rintro ⟨j, rfl⟩
        exact ⟨(e j).val, (e j).property, rfl⟩
    change realSegmentSum (I.image h) = _
    rw [himage, segment_sum_injective_image Finset.univ g hg]
    simp

private theorem deleted_faces_from_hull (m : ℕ) (h : Fin m → Lattice)
    (hne : ∀ j, h j ≠ 0)
    (hpair : Pairwise (fun i j => Nonparallel (h i) (h j)))
    (k : Fin m) (v : Lattice) (hv : v ≠ 0) (ht : det v (h k) = 0)
    (hHull : windowHull (supportWindow (differenceWithout m h k)) =
      realSegmentSum ((Finset.univ.erase k).image h)) :
    v ∉ edgeDirections (supportWindow (differenceWithout m h k)) ∧
      -v ∉ edgeDirections (supportWindow (differenceWithout m h k)) ∧
      (supportRow (supportWindow (differenceWithout m h k)) v).card = 1 ∧
      (supportRow (supportWindow (differenceWithout m h k)) (-v)).card = 1 := by
  classical
  have hconvex : LatticeConvex (supportWindow (differenceWithout m h k)) :=
    (colle_2_7 (fun _ => 0) (differenceWithout m h k)
      (deleted_polynomial_nonzero m h hne k) (by intro z; simp [laurentAction])).2.1
  have htrans : ∀ u ∈ (Finset.univ.erase k).image h, det v u ≠ 0 := by
    intro u hu hzero
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.mem_erase.mp hj).1 (tangent_unique h hpair v hv hzero ht)
  have htransneg : ∀ u ∈ (Finset.univ.erase k).image h, det (-v) u ≠ 0 := by
    intro u hu hz
    apply htrans u hu
    dsimp [det] at hz ⊢
    nlinarith
  have hpos := segment_sum_support_singleton _ _ hconvex hHull v htrans
  have hneg := segment_sum_support_singleton _ _ hconvex hHull (-v) htransneg
  refine ⟨?_, ?_, hpos, hneg⟩
  · intro he
    have hc := he.2.2
    omega
  · intro he
    have hc := he.2.2
    omega

private theorem deleted_cycle_direction_mem {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) : C.direction i ∈ edgeDirections S := by
  have hp : 0 < 2 * (m : ℤ) := by have hm := C.at_least_two; omega
  let r : Fin (2 * m) := ⟨(i % (2 * (m : ℤ))).toNat, by
    have hn := Int.emod_nonneg i (ne_of_gt hp)
    have hl := Int.emod_lt_of_pos i hp
    omega⟩
  apply (C.covers _).mpr
  refine ⟨r, ?_⟩
  have hr : (r.val : ℤ) = i % (2 * (m : ℤ)) := by
    dsimp [r]
    exact Int.toNat_of_nonneg (Int.emod_nonneg i (ne_of_gt hp))
  rw [hr]
  have he := Function.Periodic.sub_int_mul_eq (x := i) C.direction_periodic
    (i / (2 * (m : ℤ)))
  have hrep := (Int.ediv_emod_unique (a := i) hp).mp ⟨rfl, rfl⟩
  have hemod : i % (2 * (m : ℤ)) = i - (i / (2 * (m : ℤ))) * (2 * (m : ℤ)) := by
    nlinarith [hrep.1]
  simpa only [Int.cast_id, hemod] using he

private theorem erased_segment_sum_subset (m : ℕ) (h : Fin m → Lattice)
    (hinj : Function.Injective h) (k : Fin m) :
    realSegmentSum ((Finset.univ.erase k).image h) ⊆
      {x | ∃ a : Fin m → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧
        x = ∑ i, a i • embed (-h i)} := by
  classical
  rw [segment_sum_injective_image _ h hinj]
  rintro x ⟨a, ha, hx⟩
  let b : Fin m → ℝ := fun j => if j = k then 0 else a j
  refine ⟨b, ?_, ?_⟩
  · intro j
    by_cases hj : j = k
    · simp [b, hj]
    · simpa [b, hj] using ha j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  · rw [hx, ← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    simp only [b, ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

private theorem deleted_window_subset_full (m : ℕ) (h : Fin m → Lattice)
    (hinj : Function.Injective h) (k : Fin m)
    (hdel : windowHull (supportWindow (differenceWithout m h k)) =
      realSegmentSum ((Finset.univ.erase k).image h))
    (hfull : windowHull (supportWindow (differenceFactors m h)) =
      {x | ∃ a : Fin m → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧
        x = ∑ i, a i • embed (-h i)})
    (hconvex : LatticeConvex (supportWindow (differenceFactors m h))) :
    supportWindow (differenceWithout m h k) ⊆ supportWindow (differenceFactors m h) := by
  intro z hz
  apply (hconvex z).mp
  rw [hfull]
  apply erased_segment_sum_subset m h hinj k
  rw [← hdel]
  exact subset_convexHull ℝ _ (Set.mem_image_of_mem embed hz)



theorem component_direction_and_deleted_polygon (ξ : Configuration ℤ)
    (alphabet : Finset ℤ) (halphabet : ∀ z, ξ z ∈ alphabet) (hξ : ¬ Periodic ξ)
    (m : ℕ) (D : PeriodicDecomposition ℤ ξ m) (hminimal : MinimalPeriodicOrder ℤ ξ m)
    (C : AntipodalEdgeCycle (supportWindow (differenceFactors m D.period)) m) (i : ℤ) :
    ∃! k : Fin m, det (C.direction i) (D.period k) = 0 ∧
      differenceWithout m D.period k ≠ 0 ∧
      windowHull (supportWindow (differenceWithout m D.period k)) =
        realSegmentSum ((Finset.univ.erase k).image D.period) ∧
      C.direction i ∉ edgeDirections (supportWindow (differenceWithout m D.period k)) ∧
      -C.direction i ∉ edgeDirections (supportWindow (differenceWithout m D.period k)) ∧
      (supportRow (supportWindow (differenceWithout m D.period k)) (C.direction i)).card = 1 ∧
      (supportRow (supportWindow (differenceWithout m D.period k)) (-C.direction i)).card = 1 ∧
      (∀ B : Finset Lattice,
        EnvelopedWindow (supportWindow (differenceFactors m D.period)) B →
          ∃ u : Lattice, (windowTranslate (supportWindow (differenceWithout m D.period k)) u :
            Set Lattice) ⊆ halfStrip B (C.direction i) ∪ halfStrip B (-C.direction i))  := by
  classical
  have hpair := minimal_decomposition_pairwise ξ m D hminimal
  have hne : ∀ j, D.period j ≠ 0 := D.period_nonzero
  have hinj : Function.Injective D.period := by
    intro j l he
    by_contra hjl
    apply hpair hjl
    rw [he]
    simp [det, mul_comm]
  have hfull := (reflected_difference_product_actual_zonotope m D.period hne).2
  have hfull0 := (reflected_difference_product_actual_zonotope m D.period hne).1
  have hconvex : LatticeConvex (supportWindow (differenceFactors m D.period)) :=
    (colle_2_7 (fun _ => 0) _ hfull0 (by intro z; simp [laurentAction])).2.1
  have hex : ∃ k : Fin m, det (C.direction i) (D.period k) = 0 := by
    by_contra hnot
    push_neg at hnot
    have htrans : ∀ u ∈ Finset.univ.image D.period, det (C.direction i) u ≠ 0 := by
      intro u hu
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
      exact hnot j
    have hh : windowHull (supportWindow (differenceFactors m D.period)) =
        realSegmentSum (Finset.univ.image D.period) := by
      rw [segment_sum_injective_image _ D.period hinj, hfull]
      simp [reflectedFactorHull]
    have hsingle := segment_sum_support_singleton _ _ hconvex hh (C.direction i) htrans
    have hedge := (deleted_cycle_direction_mem C i).2.2
    omega
  obtain ⟨k, hk⟩ := hex
  have hdel0 := deleted_polynomial_nonzero m D.period hne k
  have hdel : windowHull (supportWindow (differenceWithout m D.period k)) =
      realSegmentSum ((Finset.univ.erase k).image D.period) := by
    obtain ⟨n, g, hg, hgi, hp, hseg⟩ := erased_family_reindex m D.period hne hinj k
    rw [hp, (reflected_difference_product_actual_zonotope n g hg).2, hseg]
    rfl
  have hfaces := deleted_faces_from_hull m D.period hne hpair k (C.direction i)
    (primitive_ne_zero _ (C.primitive i)) hk hdel
  refine ⟨k, ⟨hk, hdel0, hdel, hfaces.1, hfaces.2.1, hfaces.2.2.1,
    hfaces.2.2.2, ?_⟩, ?_⟩
  · intro B hB
    obtain ⟨P⟩ := (enveloped_boundary_aligned_cycle C hB).1
    have hcontain := aligned_translated_containment_unconditional C hconvex hB.2.1 P i
    have hsub := deleted_window_subset_full m D.period hinj k hdel hfull hconvex
    refine ⟨P.vertex i - C.vertex i, ?_⟩
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    apply Set.mem_union_left
    refine ⟨q + (P.vertex i - C.vertex i), ?_, 0, by simp⟩
    apply hcontain
    exact Finset.mem_image.mpr ⟨q, hsub hq, rfl⟩
  · intro l hl
    exact tangent_unique D.period hpair (C.direction i)
      (primitive_ne_zero _ (C.primitive i)) hl.1 hk

end
end ConvexNivat.Colle
