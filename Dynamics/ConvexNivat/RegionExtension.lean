import ConvexNivat.ReductionRegions

namespace ConvexNivat
open scoped BigOperators

theorem lemma8_2_extensionAlong {A : Type*} (G : Configuration A)
    (R : Set Lattice) (h k : Lattice) (hfull : FullPeriods G R h k)
    (hentry : ∀ z, ∃ n : ℕ, z + (n : ℤ) • (h + k) ∈ R) :
    AgreesOn (extensionAlong G R (h + k) hentry) G R ∧
    HasPeriod (extensionAlong G R (h + k) hentry) h ∧
    HasPeriod (extensionAlong G R (h + k) hentry) k ∧
    (∀ a b : ℤ, HasPeriod (extensionAlong G R (h + k) hentry) (a • h + b • k)) ∧
    DoublyPeriodic (extensionAlong G R (h + k) hentry) ∧
    ∀ z n, z + (n : ℤ) • (h + k) ∈ R →
      extensionAlong G R (h + k) hentry z = G (z + (n : ℤ) • (h + k)) := by
  have hf : ForwardInvariant R (h + k) := by
    intro z hz
    simpa only [add_assoc] using hfull.2.2.2.1 (z + h) (hfull.2.2.1 z hz)
  have hp : ∀ z ∈ R, G (z + (h + k)) = G z := by
    intro z hz
    rw [← add_assoc, hfull.2.2.2.2.2 _ (hfull.2.2.1 z hz), hfull.2.2.2.2.1 _ hz]
  have iterate : ∀ (z : Lattice), z ∈ R → ∀ n : ℕ,
      z + (n : ℤ) • (h + k) ∈ R ∧ G (z + (n : ℤ) • (h + k)) = G z := by
    intro z hz n
    induction n with
    | zero => simpa using And.intro hz (Eq.refl (G z))
    | succ n ih =>
      have heq : z + ((n + 1 : ℕ) : ℤ) • (h + k) =
          (z + (n : ℤ) • (h + k)) + (h + k) := by
        simp [add_smul, add_assoc, add_comm, add_left_comm]
      rw [heq]
      exact ⟨hf _ ih.1, (hp _ ih.1).trans ih.2⟩
  have compare : ∀ z (m n : ℤ), z + m • (h + k) ∈ R →
      z + n • (h + k) ∈ R → G (z + m • (h + k)) = G (z + n • (h + k)) := by
    intro z m n hm hn
    have forward : ∀ a b : ℤ, a ≤ b → z + a • (h + k) ∈ R →
        G (z + b • (h + k)) = G (z + a • (h + k)) := by
      intro a b hab ha
      have hcast : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
      have heq : (z + a • (h + k)) + ((b - a).toNat : ℤ) • (h + k) =
          z + b • (h + k) := by
        rw [hcast, add_assoc, ← add_smul]
        simp
      simpa only [heq] using (iterate _ ha (b - a).toNat).2
    rcases le_total m n with hmn | hnm
    · exact (forward m n hmn hm).symm
    · exact forward n m hnm hn
  have consistent : ∀ z (n : ℤ), z + n • (h + k) ∈ R →
      extensionAlong G R (h + k) hentry z = G (z + n • (h + k)) := by
    intro z n hn
    exact compare z _ n (Classical.choose_spec (hentry z)) hn
  have hh : HasPeriod (extensionAlong G R (h + k) hentry) h := by
    intro z
    obtain ⟨n, hn⟩ := hentry z
    have hnh : z + h + (n : ℤ) • (h + k) ∈ R := by
      simpa only [add_right_comm] using hfull.2.2.1 _ hn
    rw [consistent (z + h) n hnh, consistent z n hn]
    simpa only [add_right_comm] using hfull.2.2.2.2.1 _ hn
  have hk : HasPeriod (extensionAlong G R (h + k) hentry) k := by
    intro z
    obtain ⟨n, hn⟩ := hentry z
    have hnk : z + k + (n : ℤ) • (h + k) ∈ R := by
      simpa only [add_right_comm] using hfull.2.2.2.1 _ hn
    rw [consistent (z + k) n hnk, consistent z n hn]
    simpa only [add_right_comm] using hfull.2.2.2.2.2 _ hn
  refine ⟨?_, hh, hk, ?_, ⟨h, k, hfull.2.1, hh, hk⟩, consistent⟩
  · intro z hz
    simpa using consistent z 0 (by simpa using hz)
  · intro a b
    exact hasPeriod_add _ _ _ (hasPeriod_zsmul _ _ hh a) (hasPeriod_zsmul _ _ hk b)

theorem lemma8_2_halfPlane_normal {A : Type*} (G : Configuration A)
    (H : HalfPlane) (h k : Lattice) (hfull : FullPeriods G H.carrier h k) :
    0 < realDot (embed (h + k)) H.normal := by
  have dot_add : ∀ x y : Lattice,
      realDot (embed (x + y)) H.normal =
        realDot (embed x) H.normal + realDot (embed y) H.normal := by
    intro x y
    simp [realDot, embed]
    ring
  have dot_mul : ∀ (x : Lattice) (n : ℤ),
      realDot (embed (n • x)) H.normal = (n : ℝ) * realDot (embed x) H.normal := by
    intro x n
    simp [realDot, embed]
    ring
  have nonneg : ∀ d : Lattice, ForwardInvariant H.carrier d →
      0 ≤ realDot (embed d) H.normal := by
    intro d hd
    by_contra hneg
    have hdneg : realDot (embed d) H.normal < 0 := lt_of_not_ge hneg
    obtain ⟨z, hz⟩ := hfull.1
    have iter : ∀ n : ℕ, z + (n : ℤ) • d ∈ H.carrier := by
      intro n
      induction n with
      | zero => simpa using hz
      | succ n ih =>
        simpa [add_smul, add_assoc] using hd _ ih
    obtain ⟨n, hn⟩ := exists_nat_gt
      ((realDot (embed z) H.normal - H.threshold) / (-realDot (embed d) H.normal))
    have hmul := (div_lt_iff₀ (neg_pos.mpr hdneg)).mp hn
    have hout : realDot (embed z) H.normal + (n : ℝ) * realDot (embed d) H.normal <
        H.threshold := by nlinarith
    have hin := iter n
    unfold HalfPlane.carrier at hin
    simp only [Set.mem_ofPred_eq, dot_add, dot_mul, Int.cast_natCast] at hin
    cases hs : H.strict <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hin <;> linarith
  have hh := nonneg h hfull.2.2.1
  have hk := nonneg k hfull.2.2.2.1
  rw [dot_add]
  by_contra hle
  have hhz : realDot (embed h) H.normal = 0 := by linarith
  have hkz : realDot (embed k) H.normal = 0 := by linarith
  have hd : (h.1 : ℝ) * k.2 - (h.2 : ℝ) * k.1 ≠ 0 := by
    exact_mod_cast hfull.2.1
  have hz1 : H.normal.1 = 0 := by
    apply (mul_eq_zero.mp (show ((h.1 : ℝ) * k.2 - (h.2 : ℝ) * k.1) * H.normal.1 = 0 by
      calc
        _ = (k.2 : ℝ) * realDot (embed h) H.normal -
            (h.2 : ℝ) * realDot (embed k) H.normal := by dsimp [realDot, embed]; ring
        _ = 0 := by rw [hhz, hkz]; ring)).resolve_left hd
  have hz2 : H.normal.2 = 0 := by
    apply (mul_eq_zero.mp (show ((h.1 : ℝ) * k.2 - (h.2 : ℝ) * k.1) * H.normal.2 = 0 by
      calc
        _ = (h.1 : ℝ) * realDot (embed k) H.normal -
            (k.1 : ℝ) * realDot (embed h) H.normal := by dsimp [realDot, embed]; ring
        _ = 0 := by rw [hhz, hkz]; ring)).resolve_left hd
  exact H.normal_ne_zero (Prod.ext hz1 hz2)

theorem lemma8_2_region_cone {A : Type*} (G : Configuration A)
    (R : Set Lattice) (hR : LatticeConvexRegion R) (h k : Lattice)
    (hfull : FullPeriods G R h k) :
    FullDimensional (regionCone R) ∧ embed (h + k) ∈ interior (regionCone R) := by
  have hc : Convex ℝ (closedRealHull R) := (convex_convexHull ℝ (embed '' R)).closure
  have ray : ∀ (d : RealPlane), d ∈ regionCone R → ∀ t : ℝ,
      0 ≤ t → t • d ∈ regionCone R := by
    intro d hd t ht x hx
    have iter : ∀ n : ℕ, x + (n : ℝ) • d ∈ closedRealHull R := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih =>
        simpa [Nat.cast_add, add_smul, add_assoc] using hd _ ih
    obtain ⟨N, hN⟩ := exists_nat_gt t
    have hNp : (0 : ℝ) < N := lt_of_le_of_lt ht hN
    have hseg := hc.add_smul_mem hx (iter N)
      (show t / (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
        ⟨div_nonneg ht hNp.le, (div_le_one hNp).mpr hN.le⟩)
    simpa only [smul_smul, div_mul_cancel₀ _ hNp.ne'] using hseg
  have hh := latticeRegion_forward_period_in_cone R hR h hfull.2.2.1
  have hk := latticeRegion_forward_period_in_cone R hR k hfull.2.2.2.1
  have span : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a • embed h + b • embed k ∈ regionCone R := by
    intro a b ha hb x hx
    exact (show x + (a • embed h + b • embed k) ∈ closedRealHull R by
      rw [← add_assoc]
      exact ray _ hk b hb _ (ray _ hh a ha _ hx))
  let D : ℝ := (h.1 : ℝ) * k.2 - (h.2 : ℝ) * k.1
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast hfull.2.1
  let a : RealPlane → ℝ := fun x => (x.1 * k.2 - x.2 * k.1) / D
  let b : RealPlane → ℝ := fun x => ((h.1 : ℝ) * x.2 - (h.2 : ℝ) * x.1) / D
  have decomp : ∀ x : RealPlane, x = a x • embed h + b x • embed k := by
    intro x
    ext <;> dsimp [a, b, embed] <;> field_simp <;> dsimp [D] <;> ring
  let U : Set RealPlane := {x | 0 < a x ∧ 0 < b x}
  have hopen : IsOpen U := by
    exact (isOpen_lt continuous_const (by fun_prop : Continuous a)).inter
      (isOpen_lt continuous_const (by fun_prop : Continuous b))
  have hin : embed (h + k) ∈ U := by
    have ha : a (embed (h + k)) = 1 := by
      dsimp [a, embed]
      simp only [Int.cast_add]
      apply (div_eq_one_iff_eq hD).mpr
      dsimp [D]
      ring
    have hb : b (embed (h + k)) = 1 := by
      dsimp [b, embed]
      simp only [Int.cast_add]
      apply (div_eq_one_iff_eq hD).mpr
      dsimp [D]
      ring
    exact ⟨by rw [ha]; norm_num, by rw [hb]; norm_num⟩
  have hsub : U ⊆ regionCone R := by
    intro x hx
    rw [decomp x]
    exact span _ _ hx.1.le hx.2.le
  have hmem : embed (h + k) ∈ interior (regionCone R) := interior_maximal hsub hopen hin
  exact ⟨⟨embed (h + k), hmem⟩, hmem⟩

/-- 8.2: eventual entry, with precisely the two forward periods specified. -/
theorem lemma8_2_eventual_entry {A : Type*} (G : Configuration A)
    (R : Set Lattice) (hR : LatticeConvexRegion R ∨ ∃ H : HalfPlane, R = H.carrier)
    (h k : Lattice) (hfull : FullPeriods G R h k) :
    ∀ z, ∃ N : ℕ, ∀ n ≥ N, z + (n : ℤ) • (h + k) ∈ R := by
  rcases hR with hR | ⟨H, rfl⟩
  · have hc : Convex ℝ (closedRealHull R) := (convex_convexHull ℝ (embed '' R)).closure
    have ray : ∀ (d : RealPlane), d ∈ regionCone R → ∀ t : ℝ,
        0 ≤ t → t • d ∈ regionCone R := by
      intro d hd t ht x hx
      have iter : ∀ n : ℕ, x + (n : ℝ) • d ∈ closedRealHull R := by
        intro n
        induction n with
        | zero => simpa using hx
        | succ n ih =>
          simpa [Nat.cast_add, add_smul, add_assoc] using hd _ ih
      obtain ⟨N, hN⟩ := exists_nat_gt t
      have hNp : (0 : ℝ) < N := lt_of_le_of_lt ht hN
      have hseg := hc.add_smul_mem hx (iter N)
        (show t / (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
          ⟨div_nonneg ht hNp.le, (div_le_one hNp).mpr hN.le⟩)
      simpa only [smul_smul, div_mul_cancel₀ _ hNp.ne'] using hseg
    have hh := latticeRegion_forward_period_in_cone R hR h hfull.2.2.1
    have hk := latticeRegion_forward_period_in_cone R hR k hfull.2.2.2.1
    obtain ⟨r, hr⟩ := hfull.1
    have hrC : embed r ∈ closedRealHull R := by
      rw [latticeRegion_closedHull R hR] at hr
      exact hr
    let D : ℝ := (h.1 : ℝ) * k.2 - (h.2 : ℝ) * k.1
    have hD : D ≠ 0 := by
      dsimp [D]
      exact_mod_cast hfull.2.1
    intro z
    let x := embed z - embed r
    let a : ℝ := (x.1 * k.2 - x.2 * k.1) / D
    let b : ℝ := ((h.1 : ℝ) * x.2 - (h.2 : ℝ) * x.1) / D
    have hdecomp : x = a • embed h + b • embed k := by
      ext <;> dsimp [a, b, embed] <;> field_simp <;> dsimp [D] <;> ring
    obtain ⟨N, hN⟩ := exists_nat_gt (max (-a) (-b))
    refine ⟨N, ?_⟩
    intro n hn
    have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have ha : 0 ≤ (n : ℝ) + a := by have := le_max_left (-a) (-b); linarith
    have hb : 0 ≤ (n : ℝ) + b := by have := le_max_right (-a) (-b); linarith
    have hmem := ray _ hk ((n : ℝ) + b) hb _ (ray _ hh ((n : ℝ) + a) ha _ hrC)
    have heq : embed (z + (n : ℤ) • (h + k)) =
        (embed r + ((n : ℝ) + a) • embed h) + ((n : ℝ) + b) • embed k := by
      have hz : embed z = embed r + x := by dsimp [x]; abel
      have he : embed (z + (n : ℤ) • (h + k)) =
          embed z + (n : ℝ) • (embed h + embed k) := by
        ext <;> simp [embed] <;> ring
      rw [he, hz, hdecomp]
      module
    rw [latticeRegion_closedHull R hR]
    change embed (z + (n : ℤ) • (h + k)) ∈ closedRealHull R
    rwa [heq]
  · intro z
    exact halfPlane_eventually_enters H (h + k) z (lemma8_2_halfPlane_normal G H h k hfull)

end ConvexNivat
