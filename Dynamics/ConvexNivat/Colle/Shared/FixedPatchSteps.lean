import ConvexNivat.Colle.Shared.SequenceDefinitions
import ConvexNivat.Colle.Shared.RowCoordinates

namespace ConvexNivat.Colle
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


private theorem periodic_mod {α : Type*} (f : ℤ → α) (n : ℕ)
    (hn : 0 < n) (hf : ∀ j, f (j+(n : ℤ))=f j) (j : ℤ) : f (j % n)=f j := by
  have hp : Function.Periodic f (n : ℤ) := hf
  have h := hp.int_mul (j/(n : ℤ)) (j % (n : ℤ))
  simpa only [Int.cast_id,Int.emod_add_ediv_mul] using h.symm



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



private theorem fp_second_support {v w : Lattice} (P : Region v w)
    {z : Lattice} (hz : z ∈ P.lattice) : det w P.secondAnchor ≤ det w z := by
  have h := P.second_support (embed z) hz
  have he : realDet (embed w) (embed z - embed P.secondAnchor) =
      (det w z - det w P.secondAnchor : ℤ) := by simp [realDet, embed, det]; ring
  change 0 ≤ realDet (embed w) (embed z - embed P.secondAnchor) at h
  rw [he] at h
  have hh : (0 : ℤ) ≤ det w z - det w P.secondAnchor := by exact_mod_cast h
  omega

private theorem fp_enlargement_height {v w : Lattice} (P : Region v w)
    (n : ℕ) {z : Lattice} (hz : z ∈ P.enlargement n) :
    det w P.secondAnchor - (n : ℤ) ≤ det w z := by
  obtain ⟨g, hg, t, hzt, hzP | hzrows⟩ := hz
  · have hh := fp_second_support P hzP
    omega
  · exact hzrows.1

private theorem fp_lattice_subset_enlargement {v w : Lattice}
    (P : Region v w) (n : ℕ) : P.lattice ⊆ P.enlargement n := by
  intro z hz
  exact ⟨z, hz, 0, by simp, Or.inl hz⟩

private theorem fp_enlargement_mono {v w : Lattice} (P : Region v w) :
    Monotone P.enlargement := by
  intro n k hnk z hz
  obtain ⟨g, hg, t, he, hp | hh⟩ := hz
  · exact ⟨g, hg, t, he, Or.inl hp⟩
  · exact ⟨g, hg, t, he, Or.inr ⟨by omega, hh.2⟩⟩

private theorem fp_candidate_finite {v w : Lattice} (P : Region v w)
    (A : Finset Lattice) (d : Lattice) (hd : 0 < det w d) (n : ℕ) :
    (backwardSaturationCandidate A d (P.enlargement n)).Finite := by
  classical
  let F : Finset Lattice := A.biUnion fun g =>
    (Finset.range ((det w g - (det w P.secondAnchor - (n : ℤ))).toNat + 1)).image
      (fun t : ℕ => g - (t : ℤ) • d)
  apply F.finite_toSet.subset
  intro z hz
  obtain ⟨⟨g, hg, t, he⟩, hzP⟩ := hz
  have hzheight := fp_enlargement_height P n hzP
  have hdet : det w z = det w g - (t : ℤ) * det w d := by
    rw [he]
    simp [det]
    ring
  have ht0 : (0 : ℤ) ≤ t := by omega
  have ht1 : (t : ℤ) ≤ det w g - (det w P.secondAnchor - (n : ℤ)) := by
    nlinarith
  have ht : t < (det w g - (det w P.secondAnchor - (n : ℤ))).toNat + 1 := by omega
  apply Finset.mem_biUnion.mpr
  refine ⟨g, hg, Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, ?_⟩⟩
  simpa [sub_eq_add_neg] using he.symm

private theorem fp_candidate_mono {A B : Finset Lattice} {d : Lattice}
    {U V : Set Lattice} (hAB : A ⊆ B) (hUV : U ⊆ V) :
    backwardSaturationCandidate A d U ⊆ backwardSaturationCandidate B d V := by
  rintro z ⟨⟨g, hg, t, he⟩, hz⟩
  exact ⟨⟨g, hAB hg, t, he⟩, hUV hz⟩

private theorem fp_candidate_contains {A : Finset Lattice} {d : Lattice}
    {U : Set Lattice} (hAU : (A : Set Lattice) ⊆ U) :
    (A : Set Lattice) ⊆ backwardSaturationCandidate A d U := by
  intro z hz
  exact ⟨⟨z, hz, 0, by simp⟩, hAU hz⟩

private theorem fp_normalised_mono {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    {W : AlternatingWindows ξ xper C i} (G : GrowingSubsequence W) :
    Monotone (fun j => W.normalised (G.subsequence j)) := by
  exact monotone_nat_of_le_succ G.nested

private theorem fp_all_literal_candidates {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G) (n : ℕ) :
    ∃ E : ℕ → Finset Lattice,
      (∀ j, (E j : Set Lattice) = backwardSaturationCandidate
        (W.normalised (G.subsequence j)) (C.direction (G.J + 1)) (P.enlargement n)) ∧
      Monotone E ∧ ∀ j, W.normalised (G.subsequence j) ⊆ E j := by
  classical
  have hf (j : ℕ) := fp_candidate_finite P (W.normalised (G.subsequence j))
    (C.direction (G.J + 1)) (cycle_turn_positive C G.J) n
  let E (j : ℕ) := (hf j).toFinset
  have he (j : ℕ) : (E j : Set Lattice) = backwardSaturationCandidate
      (W.normalised (G.subsequence j)) (C.direction (G.J + 1)) (P.enlargement n) := by
    exact Set.Finite.coe_toFinset (hf j)
  refine ⟨E, he, ?_, ?_⟩
  · intro a b hab z hz
    have h := fp_candidate_mono (d := C.direction (G.J + 1)) (fp_normalised_mono G hab) (Set.Subset.refl (P.enlargement n))
    have hza : z ∈ (E a : Set Lattice) := hz
    rw [he a] at hza
    have hzb := h hza
    rw [← he b] at hzb
    exact hzb
  · intro j z hz
    have hzP : z ∈ P.lattice := by
      rw [hP]
      exact Set.mem_iUnion.mpr ⟨j, hz⟩
    have hzU := fp_lattice_subset_enlargement P n hzP
    have hez : z ∈ backwardSaturationCandidate
        (W.normalised (G.subsequence j)) (C.direction (G.J + 1)) (P.enlargement n) :=
      ⟨⟨z, hz, 0, by simp⟩, hzU⟩
    rw [← he j] at hez
    exact hez

private theorem fp_predecessor_turn {v w : Lattice} (P : Region v w) :
    0 < det P.predecessor w := by
  unfold Region.predecessor
  split_ifs with h
  · exact P.second_turn ⟨P.boundedCount - 1, Nat.sub_lt h Nat.zero_lt_one⟩ (by simp; omega)
  · exact P.turn_positive

private theorem fp_second_ray_mem {v w : Lattice} (P : Region v w)
    (t : ℤ) (ht : 0 ≤ t) : P.secondAnchor + t • w ∈ P.lattice := by
  apply P.closed.frontier_subset
  rw [P.boundary_eq]
  apply Or.inl
  apply Or.inr
  refine ⟨(t : ℝ), by exact_mod_cast ht, ?_⟩
  simp [Region.secondAnchor, embed]

private theorem fp_exterior_seed {v w : Lattice} (P : Region v w)
    (d : Lattice) (hd : 0 < det w d) :
    ∃ width : ℕ, ∃ g z : Lattice, g ∈ P.lattice ∧
      z ∉ P.lattice ∧ z ∈ P.enlargement width ∧
      ∃ t : ℕ, z = g + (t : ℤ) • (-d) := by
  let a : ℤ := det w d
  let b : ℤ := det P.predecessor w
  let c : ℤ := det P.predecessor d
  let offset : ℤ := max 0 (-c)
  have ha : 0 < a := hd
  have hb : 0 < b := fp_predecessor_turn P
  have hoff : 0 ≤ offset := le_max_left _ _
  have hc : 0 ≤ offset + c := by dsimp [offset]; omega
  let base : Lattice := P.secondAnchor + offset • w
  let g : Lattice := P.secondAnchor + (offset + c) • w
  let z : Lattice := base + a • P.predecessor
  have hbase : base ∈ P.lattice := fp_second_ray_mem P offset hoff
  have hg : g ∈ P.lattice := fp_second_ray_mem P (offset + c) hc
  have hdet : det w z = det w P.secondAnchor - a * b := by
    dsimp [z, base, a, b]
    simp [det]
    ring
  have hout : z ∉ P.lattice := by
    intro hz
    have hh := fp_second_support P hz
    nlinarith [mul_pos ha hb]
  have hwidth : ((a * b).toNat : ℤ) = a * b := Int.toNat_of_nonneg (mul_pos ha hb).le
  refine ⟨(a * b).toNat, g, z, hg, hout, ?_, b.toNat, ?_⟩
  · refine ⟨base, hbase, a.toNat, ?_, Or.inr ?_⟩
    · dsimp [z]
      rw [Int.toNat_of_nonneg ha.le]
    · rw [hdet, hwidth]
      constructor <;> nlinarith [mul_pos ha hb]
  · rw [Int.toNat_of_nonneg hb.le]
    dsimp [z, base, g, a, b, c]
    apply Prod.ext <;> simp [det] <;> ring

private theorem fp_eventual_strict_candidates {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G) (n : ℕ) :
    ∃ n' : ℕ, n ≤ n' ∧ ∃ E : ℕ → Finset Lattice, ∃ j₀ : ℕ,
      (∀ j, (E j : Set Lattice) = backwardSaturationCandidate
        (W.normalised (G.subsequence j)) (C.direction (G.J + 1)) (P.enlargement n')) ∧
      Monotone E ∧ ∀ j ≥ j₀, W.normalised (G.subsequence j) ⊂ E j := by
  obtain ⟨width, g, z, hg, hz, hzwidth, t, hzt⟩ :=
    fp_exterior_seed P (C.direction (G.J + 1)) (cycle_turn_positive C G.J)
  have hgUnion : g ∈ normalisedUnion W G := hP ▸ hg
  obtain ⟨j₀, hgj₀⟩ := Set.mem_iUnion.mp hgUnion
  let n' := max n width
  obtain ⟨E, hE, hmonoE, hAE⟩ := fp_all_literal_candidates W G P hP n'
  refine ⟨n', le_max_left _ _, E, j₀, hE, hmonoE, ?_⟩
  intro j hj
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hAE j, ?_⟩
  intro hEq
  have hgj := fp_normalised_mono G hj hgj₀
  have hzE : z ∈ (E j : Set Lattice) := by
    rw [hE j]
    exact ⟨⟨g, hgj, t, hzt⟩, fp_enlargement_mono P (le_max_right n width) hzwidth⟩
  have hzA : z ∈ W.normalised (G.subsequence j) := by rw [hEq]; exact hzE
  apply hz
  rw [hP]
  exact Set.mem_iUnion.mpr ⟨j, hzA⟩

private theorem fp_finite_patch_capture {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (F : Finset Lattice) (hF : (F : Set Lattice) ⊆ normalisedUnion W G) :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, F ⊆ W.normalised (G.subsequence j) := by
  classical
  have hc : ∀ z ∈ F, ∃ j, z ∈ W.normalised (G.subsequence j) := by
    intro z hz
    exact Set.mem_iUnion.mp (hF hz)
  choose index hindex using hc
  let j₀ : ℕ := F.sup fun z => if hz : z ∈ F then index z hz else 0
  refine ⟨j₀, ?_⟩
  intro j hj z hz
  have hi : index z hz ≤ j₀ := by
    have h := Finset.le_sup (f := fun z => if hz : z ∈ F then index z hz else 0) hz
    simpa only [dif_pos hz] using h
  exact fp_normalised_mono G (hi.trans hj) (hindex z hz)

private theorem fp_sweep_domain_mono {U V : Set Lattice} (hUV : U ⊆ V)
    (steps : List (Lattice × Lattice)) : sweepDomain U steps ⊆ sweepDomain V steps := by
  induction steps generalizing U V with
  | nil => exact hUV
  | cons step steps ih =>
    apply ih
    exact Set.union_subset_union hUV (Set.Subset.refl _)

private theorem fp_valid_sweep_mono {S : Finset Lattice} {U V : Set Lattice}
    {steps : List (Lattice × Lattice)} (hUV : U ⊆ V)
    (hs : ValidGeneratingSweep S U steps) : ValidGeneratingSweep S V steps := by
  induction hs generalizing V with
  | nil => exact ValidGeneratingSweep.nil V
  | cons U u z steps hz he hs ih =>
    exact ValidGeneratingSweep.cons V u z steps hz (fun q hq => hUV (he q hq))
      (ih (Set.union_subset_union hUV (Set.Subset.refl _)))

private theorem fp_finite_sweep_mono {S F : Finset Lattice} {U V : Set Lattice}
    (hUV : U ⊆ V) (hs : HasFiniteSweep S U F) : HasFiniteSweep S V F := by
  obtain ⟨steps, hv, hF⟩ := hs
  exact ⟨steps, fp_valid_sweep_mono hUV hv, hF.trans (fp_sweep_domain_mono hUV steps)⟩

private theorem fp_fixed_seed_threshold {S : Finset Lattice} {A E : ℕ → Finset Lattice}
    (hE : Monotone E) {j₀ j₁ : ℕ} (hj : j₀ ≤ j₁)
    (hsweep : ∀ j ≥ j₀, HasFiniteSweep S ((A j : Set Lattice) ∪ (E j₀ : Set Lattice)) (E j)) :
    ∀ j ≥ j₁, HasFiniteSweep S ((A j : Set Lattice) ∪ (E j₁ : Set Lattice)) (E j) := by
  intro j hj1
  apply fp_finite_sweep_mono _ (hsweep j (hj.trans hj1))
  exact Set.union_subset_union (Set.Subset.refl _) (fun z hz => hE hj hz)

end
end ConvexNivat.Colle
