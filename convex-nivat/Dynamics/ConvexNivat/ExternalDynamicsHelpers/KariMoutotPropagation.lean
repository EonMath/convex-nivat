import ConvexNivat.ExternalDynamicsHelpers.KariMoutotCore

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

private theorem dot_add (a b u : Lattice) : latticeDot (a + b) u = latticeDot a u + latticeDot b u := by
  simp [latticeDot]; ring
private theorem dot_sub (a b u : Lattice) : latticeDot (a - b) u = latticeDot a u - latticeDot b u := by
  simp [latticeDot]; ring
private theorem dot_smul (k : ℤ) (a u : Lattice) : latticeDot (k • a) u = k * latticeDot a u := by
  simp [latticeDot]; ring
private theorem dot_neg_right (a u : Lattice) : latticeDot a (-u) = -latticeDot a u := by
  simp [latticeDot]; ring
private theorem dot_self_pos (u : Lattice) (hu : u ≠ 0) : 0 < latticeDot u u := by
  have hn : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra h; push_neg at h; exact hu (Prod.ext h.1 h.2)
  unfold latticeDot
  rcases hn with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg u.2]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg u.1]

private theorem limit_on_finset (xs : ℕ → Configuration ℤ) (x : Configuration ℤ)
    (h : PointwiseLimit xs x) (B : Finset Lattice) :
    ∃ N, ∀ j ≥ N, ∀ z ∈ B, xs j z = x z := by
  classical
  induction B using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a B ha ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := h a
    refine ⟨max N M, fun j hj z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hM j (le_trans (le_max_right _ _) hj)
    · exact hN j (le_trans (le_max_left _ _) hj) z hz

private theorem limit_subseq (xs : ℕ → Configuration ℤ) (x : Configuration ℤ)
    (h : PointwiseLimit xs x) (s : ℕ → ℕ) (hs : StrictMono s) :
    PointwiseLimit (fun j => xs (s j)) x := by
  intro z
  obtain ⟨N, hN⟩ := h z
  exact ⟨N, fun j hj => hN (s j) (hj.trans (hs.id_le j))⟩

private theorem limit_unique (xs : ℕ → Configuration ℤ) (x y : Configuration ℤ)
    (hx : PointwiseLimit xs x) (hy : PointwiseLimit xs y) : x = y := by
  funext z
  obtain ⟨N, hN⟩ := hx z
  obtain ⟨M, hM⟩ := hy z
  exact (hN (max N M) (le_max_left _ _)).symm.trans (hM _ (le_max_right _ _))

theorem discrete_box_period_saturation (u v : Lattice) (hu : u ≠ 0)
    (hv : v ≠ 0) (hperp : latticeDot u v = 0) (k : ℕ)
    (hk : |latticeDot (quarterTurn u) v| < (k : ℤ)) :
    {z : Lattice | ∃ b ∈ discreteBox u k, ∃ j : ℤ, z = b + j • v} =
      {z | -(k : ℤ) < latticeDot z u ∧ latticeDot z u < 0} := by
  have hcomm : latticeDot v u = 0 := by simpa [latticeDot, mul_comm] using hperp
  have hd : latticeDot v (quarterTurn u) ≠ 0 := by
    intro h
    have hp := dot_self_pos u hu
    have h1 : v.1 * latticeDot u u = 0 := by
      dsimp [latticeDot, quarterTurn] at *
      linear_combination u.1 * hcomm + u.2 * h
    have h2 : v.2 * latticeDot u u = 0 := by
      dsimp [latticeDot, quarterTurn] at *
      linear_combination u.2 * hcomm - u.1 * h
    exact hv (Prod.ext ((mul_eq_zero.mp h1).resolve_right (ne_of_gt hp))
      ((mul_eq_zero.mp h2).resolve_right (ne_of_gt hp)))
  have hk' : |latticeDot v (quarterTurn u)| < (k : ℤ) := by
    simpa [latticeDot, mul_comm] using hk
  have hkpos : 0 < (k : ℤ) := lt_of_le_of_lt (abs_nonneg _) hk'
  ext z
  constructor
  · rintro ⟨b, hb, j, rfl⟩
    change -(k : ℤ) < latticeDot (b + j • v) u ∧ latticeDot (b + j • v) u < 0
    rw [dot_add, dot_smul, hcomm, mul_zero, add_zero]
    exact ⟨hb.1, hb.2.1⟩
  · intro hz
    let q := latticeDot z (quarterTurn u) / latticeDot v (quarterTurn u)
    refine ⟨z - q • v, ?_, q, by abel⟩
    have hdot : latticeDot (z - q • v) u = latticeDot z u := by
      rw [dot_sub, dot_smul, hcomm, mul_zero, sub_zero]
    have hqt : latticeDot (z - q • v) (quarterTurn u) =
        latticeDot z (quarterTurn u) % latticeDot v (quarterTurn u) := by
      rw [dot_sub, dot_smul]
      dsimp [q]
      have := Int.emod_add_ediv_mul (latticeDot z (quarterTurn u)) (latticeDot v (quarterTurn u))
      omega
    change -(k : ℤ) < _ ∧ _ < 0 ∧ -(k : ℤ) < _ ∧ _ < (k : ℤ)
    rw [hdot, hqt]
    exact ⟨hz.1, hz.2, by have := Int.emod_nonneg (latticeDot z (quarterTurn u)) hd; omega,
      (Int.emod_lt_abs _ hd).trans hk'⟩

theorem finite_box_codes_forward_half (ξ x y : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) (hy : y ∈ OrbitClosure ξ)
    (u : Lattice) (hu : u ≠ 0) (k : ℕ) (B : Finset Lattice)
    (hB : (B : Set Lattice) = discreteBox u k) (hcode : PatternDetermines ξ B 0)
    (hstripe : AgreesOn x y {z | -(k : ℤ) < latticeDot z u ∧ latticeDot z u < 0}) :
    AgreesOn x y (strictHalf (-u)) := by
  have hall : ∀ d : ℕ, ∀ z : Lattice, latticeDot z u = d → x z = y z := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro z hz
      have he := hcode x hx y hy z
      simp only [zero_add] at he
      apply he
      intro b hb
      have hb' : b ∈ discreteBox u k := by rw [← hB]; exact hb
      have hd : latticeDot (b + z) u = latticeDot b u + d := by rw [dot_add, hz]
      by_cases hn : latticeDot (b + z) u < 0
      · exact hstripe _ ⟨by have := hb'.1; omega, hn⟩
      · have hp : 0 ≤ latticeDot (b + z) u := by omega
        exact ih (latticeDot (b + z) u).toNat (by
          have := hb'.2.1
          omega) (b + z) (Int.toNat_of_nonneg hp).symm
  intro z hz
  have hp : 0 < latticeDot z u := by
    change latticeDot z (-u) < 0 at hz
    rw [dot_neg_right] at hz
    omega
  exact hall (latticeDot z u).toNat z (Int.toNat_of_nonneg hp.le).symm

theorem kariMoutot_lemma9 (ξ x y : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) (hy : y ∈ OrbitClosure ξ)
    (u v : Lattice) (hu : u ≠ 0) (hv : v ≠ 0) (hperp : latticeDot u v = 0)
    (k : ℕ) (hk : |latticeDot (quarterTurn u) v| < (k : ℤ))
    (B : Finset Lattice) (hB : (B : Set Lattice) = discreteBox u k)
    (hcode : PatternDetermines ξ B 0)
    (himage : periodDifference x v = periodDifference y v)
    (hagree : AgreesOn x y (B : Set Lattice)) :
    AgreesOn x y (strictHalf (-u)) := by
  apply finite_box_codes_forward_half ξ x y hx hy u hu k B hB hcode
  have hp := (equal_factor_images_iff_periodic_difference x y v).mp himage
  intro z hz
  have hsat := discrete_box_period_saturation u v hu hv hperp k hk
  have hz' : z ∈ {z : Lattice | ∃ b ∈ discreteBox u k, ∃ j : ℤ, z = b + j • v} := by
    rw [hsat]; exact hz
  obtain ⟨b, hb, j, rfl⟩ := hz'
  have hbj := hasPeriod_zsmul (fun z => x z - y z) v hp j b
  have he := hagree b (by rw [hB]; exact hb)
  dsimp at hbj
  omega

theorem kariMoutot_corollary10 (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (u v : Lattice) (hu : u ≠ 0) (hv : v ≠ 0) (hperp : latticeDot u v = 0)
    (k : ℕ) (hk : |latticeDot (quarterTurn u) v| < (k : ℤ))
    (B : Finset Lattice) (hB : (B : Set Lattice) = discreteBox u k)
    (hcode : PatternDetermines ξ B 0)
    (n : ℕ) (c : Fin n → Configuration ℤ)
    (hc : ∀ i, c i ∈ OrbitClosure ξ) (hinj : Function.Injective c)
    (himage : ∀ i j, periodDifference (c i) v = periodDifference (c j) v) :
    n ≤ A.card ^ B.card := by
  classical
  obtain ⟨t, ht⟩ := finite_tuple_distinguished_on_half n c hinj u hu
  let f : Fin n → (B → A) := fun i z =>
    ⟨c i (z.val - t), orbitClosure_alphabet ξ (c i) A hA (hc i) _⟩
  have hfinj : Function.Injective f := by
    intro i j he
    by_contra hij
    obtain ⟨z, hz, hne⟩ := ht i j hij
    have him : periodDifference (translate (-t) (c i)) v =
        periodDifference (translate (-t) (c j)) v := by
      funext a
      have h := congrFun (himage i j) (a - t)
      simpa [periodDifference, translate, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    have hag : AgreesOn (translate (-t) (c i)) (translate (-t) (c j)) (B : Set Lattice) := by
      intro a ha
      exact congrArg Subtype.val (congrFun he ⟨a, ha⟩)
    have hforward := kariMoutot_lemma9 ξ _ _
      (orbitClosure_translate_member ξ _ (hc i) (-t))
      (orbitClosure_translate_member ξ _ (hc j) (-t))
      u v hu hv hperp k hk B hB hcode him hag
    have heq := hforward (z + t) hz
    exact hne (by simpa [translate] using heq)
  have hcard := Fintype.card_le_of_injective f hfinj
  simpa using hcard

theorem factor_fibre_finite_bound (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (u v : Lattice) (hu : u ≠ 0) (hv : v ≠ 0) (hperp : latticeDot u v = 0)
    (k : ℕ) (hk : |latticeDot (quarterTurn u) v| < (k : ℤ))
    (B : Finset Lattice) (hB : (B : Set Lattice) = discreteBox u k)
    (hcode : PatternDetermines ξ B 0) (b : Configuration ℤ) :
    (factorFibre ξ v b).Finite ∧ (factorFibre ξ v b).ncard ≤ A.card ^ B.card := by
  classical
  let F := factorFibre ξ v b
  have bound : ∀ n : ℕ, ∀ f : Fin n → F, Function.Injective f → n ≤ A.card ^ B.card := by
    intro n f hf
    exact kariMoutot_corollary10 ξ A hA u v hu hv hperp k hk B hB hcode n
      (fun i => (f i).val) (fun i => (f i).property.1)
      (fun i j h => hf (Subtype.ext h))
      (fun i j => (f i).property.2.trans (f j).property.2.symm)
  have hfinite : F.Finite := by
    by_contra h
    letI : Infinite F := Set.infinite_coe_iff.mpr h
    let e : ℕ ↪ F := Infinite.natEmbedding F
    have he := bound (A.card ^ B.card + 1) (fun i => e i.val)
      (fun i j h => Fin.ext (e.injective h))
    omega
  refine ⟨hfinite, ?_⟩
  letI := hfinite.fintype
  have h := bound (Fintype.card F) (Fintype.equivFin F).symm
    (Fintype.equivFin F).symm.injective
  simpa only [Set.fintypeCard_eq_ncard] using h

theorem maximal_factor_fibre_tuple (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (u v : Lattice) (hu : u ≠ 0) (hv : v ≠ 0) (hperp : latticeDot u v = 0)
    (k : ℕ) (hk : |latticeDot (quarterTurn u) v| < (k : ℤ))
    (B : Finset Lattice) (hB : (B : Set Lattice) = discreteBox u k)
    (hcode : PatternDetermines ξ B 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : Fin n → Configuration ℤ,
      (∀ i, c i ∈ OrbitClosure ξ) ∧ Function.Injective c ∧
      (∀ i j, periodDifference (c i) v = periodDifference (c j) v) ∧
      ∀ b : Configuration ℤ, (factorFibre ξ v b).ncard ≤ n := by
  classical
  let f := fun b => (factorFibre ξ v b).ncard
  have hb : ∀ b, (factorFibre ξ v b).Finite ∧ f b ≤ A.card ^ B.card :=
    factor_fibre_finite_bound ξ A hA u v hu hv hperp k hk B hB hcode
  have hbounded : BddAbove (Set.range f) := ⟨A.card ^ B.card, by rintro _ ⟨b, rfl⟩; exact (hb b).2⟩
  obtain ⟨b, hmax⟩ := Nat.sSup_mem (Set.range_nonempty f) hbounded
  let F := factorFibre ξ v b
  letI := (hb b).1.fintype
  have hmax' : ∀ a, f a ≤ f b := by
    intro a
    rw [hmax]
    exact le_csSup hbounded ⟨a, rfl⟩
  have hn : 0 < Fintype.card F := by
    have hself : ξ ∈ factorFibre ξ v (periodDifference ξ v) :=
      ⟨orbitClosure_contains_self ξ, rfl⟩
    have hp := Set.ncard_pos ((hb _).1) |>.mpr ⟨ξ, hself⟩
    have hh := hmax' (periodDifference ξ v)
    rw [Set.fintypeCard_eq_ncard]
    change 0 < f b
    exact hp.trans_le hh
  refine ⟨Fintype.card F, hn, fun i => ((Fintype.equivFin F).symm i).val, ?_, ?_, ?_, ?_⟩
  · intro i; exact ((Fintype.equivFin F).symm i).property.1
  · intro i j h
    exact (Fintype.equivFin F).symm.injective (Subtype.ext h)
  · intro i j
    exact ((Fintype.equivFin F).symm i).property.2.trans
      ((Fintype.equivFin F).symm j).property.2.symm
  · intro a
    simpa only [Set.fintypeCard_eq_ncard] using hmax' a

theorem strict_determinism_finite_box (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (u : Lattice) (hu : u ≠ 0)
    (hdet : StrictDeterministic ξ u) (lower : ℕ) :
    ∃ k : ℕ, lower < k ∧ ∃ B : Finset Lattice,
      (B : Set Lattice) = discreteBox u k ∧ PatternDetermines ξ B 0 := by
  classical
  let B : ℕ → Finset Lattice := fun k => (discreteBox_finite u hu k).toFinset
  have hB : ∀ k, (B k : Set Lattice) = discreteBox u k := fun k => Set.Finite.coe_toFinset _
  by_contra hn
  have hbad : ∀ j : ℕ, ∃ x y : Configuration ℤ,
      x ∈ OrbitClosure ξ ∧ y ∈ OrbitClosure ξ ∧
      AgreesOn x y (discreteBox u (j + lower + 1)) ∧ x 0 ≠ y 0 := by
    intro j
    have hnc : ¬ PatternDetermines ξ (B (j + lower + 1)) 0 := by
      intro h
      exact hn ⟨j + lower + 1, by omega, B _, hB _, h⟩
    unfold PatternDetermines at hnc
    push Not at hnc
    obtain ⟨x, hx, y, hy, t, hag, hne⟩ := hnc
    refine ⟨translate t x, translate t y,
      orbitClosure_translate_member ξ x hx t, orbitClosure_translate_member ξ y hy t, ?_, ?_⟩
    · intro z hz
      exact hag z (by rw [← hB] at hz; exact hz)
    · simpa [translate] using hne
  choose x y hx hy hag hne using hbad
  let xs : ℕ → Fin 2 → Configuration ℤ := fun j i => if i = 0 then x j else y j
  obtain ⟨s, hs, d, hd, hlim⟩ := finite_tuple_joint_subsequence ξ A hA 2 xs (by
    intro j i; dsimp [xs]; split <;> simp_all)
  have hlim0 : PointwiseLimit (fun j => x (s j)) (d 0) := by simpa [xs] using hlim 0
  have hlim1 : PointwiseLimit (fun j => y (s j)) (d 1) := by simpa [xs] using hlim 1
  have hdeq : d 0 = d 1 := hdet (d 0) (hd 0) (d 1) (hd 1) (by
    intro z hz
    have hzneg : latticeDot z u < 0 := by
      change realDot (embed z) (embed u) < 0 at hz
      rw [← latticeDot_cast] at hz
      exact_mod_cast hz
    obtain ⟨N, hN⟩ := hlim0 z
    obtain ⟨M, hM⟩ := hlim1 z
    let q := N + M + (latticeDot z u).natAbs + (latticeDot z (quarterTurn u)).natAbs + 1
    have hslarge := hs.id_le q
    have hmem : z ∈ discreteBox u (s q + lower + 1) := by
      have h1 := le_abs_self (latticeDot z u)
      have h2 := neg_le_abs (latticeDot z u)
      have h3 := le_abs_self (latticeDot z (quarterTurn u))
      have h4 := neg_le_abs (latticeDot z (quarterTurn u))
      rw [← Int.natCast_natAbs] at h1 h2 h3 h4
      change -(↑(s q + lower + 1) : ℤ) < _ ∧ _ < 0 ∧ -(↑(s q + lower + 1) : ℤ) < _ ∧ _ < _
      dsimp [q] at *
      omega
    exact (hN q (by dsimp [q]; omega)).symm.trans
      ((hag (s q) z hmem).trans (hM q (by dsimp [q]; omega))))
  obtain ⟨N, hN⟩ := hlim0 0
  obtain ⟨M, hM⟩ := hlim1 0
  exact hne (s (max N M)) ((hN _ (le_max_left _ _)).trans
    ((congrFun hdeq 0).trans (hM _ (le_max_right _ _)).symm))

theorem kariMoutot_lemma11 (ξ : Configuration ℤ)
    (u v : Lattice) (hu : u ≠ 0) (hv : v ≠ 0) (hperp : latticeDot u v = 0)
    (k : ℕ) (hk : |latticeDot (quarterTurn u) v| < (k : ℤ))
    (B : Finset Lattice) (hB : (B : Set Lattice) = discreteBox u k)
    (hcode : PatternDetermines ξ B 0) (n : ℕ) (c d : Fin n → Configuration ℤ)
    (hc : ∀ i, c i ∈ OrbitClosure ξ) (hinj : Function.Injective c)
    (himage : ∀ i j, periodDifference (c i) v = periodDifference (c j) v)
    (s : ℕ → ℕ) (hs : StrictMono s)
    (hlim : ∀ i, PointwiseLimit (fun j => translate (-((s j : ℤ) • u)) (c i)) (d i)) :
    (∀ i j, periodDifference (d i) v = periodDifference (d j) v) ∧
    ∀ i j, i ≠ j → ∀ t : Lattice,
      ∃ z ∈ translatedWindow B t, d i z ≠ d j z := by
  have htranslation (t : Lattice) (i j : Fin n) :
      periodDifference (translate t (c i)) v = periodDifference (translate t (c j)) v := by
    funext z
    have h := congrFun (himage i j) (z + t)
    simpa [periodDifference, translate, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  refine ⟨equal_factor_images_joint_limit n _ d v hlim (fun q i j => htranslation _ i j), ?_⟩
  intro i j hij t
  classical
  by_contra hn
  push Not at hn
  obtain ⟨z, hz⟩ := Function.ne_iff.mp (fun h => hij (hinj h))
  let W := B.image (fun b => b - t)
  obtain ⟨N, hN⟩ := limit_on_finset _ _ (hlim i) W
  obtain ⟨M, hM⟩ := limit_on_finset _ _ (hlim j) W
  let q := N + M + (latticeDot (z + t) u).natAbs + 1
  let a : Lattice := -((s q : ℤ) • u) - t
  have hag : AgreesOn (translate a (c i)) (translate a (c j)) (B : Set Lattice) := by
    intro b hb
    have hw : b - t ∈ W := Finset.mem_image.mpr ⟨b, hb, rfl⟩
    have ht : b - t ∈ translatedWindow B t := by simpa [translatedWindow] using hb
    have h1 := hN q (by dsimp [q]; omega) _ hw
    have h2 := hM q (by dsimp [q]; omega) _ hw
    have he := h1.trans ((hn (b - t) ht).trans h2.symm)
    simpa [translate, a, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using he
  have hf := kariMoutot_lemma9 ξ _ _
    (orbitClosure_translate_member ξ _ (hc i) a)
    (orbitClosure_translate_member ξ _ (hc j) a)
    u v hu hv hperp k hk B hB hcode (htranslation a i j) hag
  have hpos : z - a ∈ strictHalf (-u) := by
    have hp := dot_self_pos u hu
    have hslarge := hs.id_le q
    have hneg := neg_le_abs (latticeDot (z + t) u)
    rw [← Int.natCast_natAbs] at hneg
    change latticeDot (z - a) (-u) < 0
    rw [dot_neg_right]
    have he : latticeDot (z - a) u = latticeDot (z + t) u + (s q : ℤ) * latticeDot u u := by
      rw [show z - a = z + t + (s q : ℤ) • u by dsimp [a]; abel, dot_add, dot_smul]
    rw [he]
    have hslarge' : (q : ℤ) ≤ s q := by exact_mod_cast hslarge
    have hq : (latticeDot (z + t) u).natAbs < q := by dsimp [q]; omega
    have hq' : ((latticeDot (z + t) u).natAbs : ℤ) < q := by exact_mod_cast hq
    have hsnonneg : 0 ≤ (s q : ℤ) := Int.natCast_nonneg _
    nlinarith
  exact hz (by simpa [translate] using hf (z - a) hpos)

end
end ConvexNivat.ExternalDynamicsHelpers
