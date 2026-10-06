import ConvexNivat.FiniteState
import ConvexNivat.RegionExtension

namespace ConvexNivat
open scoped BigOperators

private theorem fh_md_insert {ι A : Type*} [DecidableEq ι] [Ring A]
    (H : ι → Lattice) (I : Finset ι) (j : ι) (hj : j ∉ I)
    (f : Configuration A) (z : Lattice) :
    mixedDifference H (insert j I) f z =
      mixedDifference H I f (z + H j) - mixedDifference H I f z := by
  unfold mixedDifference
  rw [Finset.sum_powerset_insert hj, sub_eq_add_neg, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro C hC
    have hjC : j ∉ C := fun h => hj (Finset.mem_powerset.mp hC h)
    rw [Finset.card_insert_of_notMem hj, Finset.card_insert_of_notMem hjC,
      Nat.add_sub_add_right, Finset.sum_insert hjC]
    congr 2
    abel

  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro C hC
    have hc := Finset.card_le_card (Finset.mem_powerset.mp hC)
    rw [Finset.card_insert_of_notMem hj]
    have he : I.card + 1 - C.card = (I.card - C.card) + 1 := by omega
    rw [he, pow_succ]
    simp

private theorem fh_md_period {ι A : Type*} [DecidableEq ι] [Ring A]
    (H : ι → Lattice) (I : Finset ι) (f : Configuration A) (v : Lattice)
    (hf : HasPeriod f v) : HasPeriod (mixedDifference H I f) v := by
  intro z
  unfold mixedDifference
  apply Finset.sum_congr rfl
  intro C hC
  congr 1
  simpa only [add_assoc, add_left_comm, add_comm] using hf (z + ∑ j ∈ C, H j)

private theorem fh_md_kills_period {ι A : Type*} [DecidableEq ι] [Ring A]
    (H : ι → Lattice) (I : Finset ι) (j : ι) (hj : j ∈ I)
    (f : Configuration A) (hf : HasPeriod f (H j)) (z : Lattice) :
    mixedDifference H I f z = 0 := by
  rw [← Finset.insert_erase hj, fh_md_insert H _ _ (Finset.notMem_erase _ _)]
  exact sub_eq_zero.mpr (fh_md_period H _ f _ hf z)

private theorem fh_md_sum {ι κ A : Type*} [DecidableEq ι] [Ring A]
    (H : ι → Lattice) (I : Finset ι) (J : Finset κ)
    (f : κ → Configuration A) (z : Lattice) :
    mixedDifference H I (fun w => ∑ j ∈ J, f j w) z =
      ∑ j ∈ J, mixedDifference H I (f j) z := by
  unfold mixedDifference
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private theorem fh_md_congr {ι A : Type*} [DecidableEq ι] [Ring A]
    (H : ι → Lattice) (I : Finset ι) (f g : Configuration A) (z : Lattice)
    (hfg : ∀ C ∈ I.powerset, f (z + ∑ j ∈ C, H j) = g (z + ∑ j ∈ C, H j)) :
    mixedDifference H I f z = mixedDifference H I g z := by
  exact Finset.sum_congr rfl (fun C hC => congrArg _ (hfg C hC))

private theorem fh_md_isolation {m : ℕ} {A : Type*} [Ring A]
    (component : Fin m → Configuration A) (H : Fin m → Lattice)
    (hperiod : ∀ j, HasPeriod (component j) (H j)) (i : Fin m) (z : Lattice) :
    mixedDifference H (Finset.univ.erase i) (fun w => ∑ j, component j w) z =
      mixedDifference H (Finset.univ.erase i) (component i) z := by
  rw [fh_md_sum]
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact fh_md_kills_period H _ j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
      _ (hperiod j) z
  · simp

private theorem fh_md_regional_zero {m : ℕ} {A : Type*} [Ring A]
    (component : Fin m → Configuration A) (H : Fin m → Lattice)
    (hperiod : ∀ j, HasPeriod (component j) (H j)) (i : Fin m)
    (hne : (Finset.univ.erase i).Nonempty)
    (F : Configuration A) (hF : ∀ j, HasPeriod F (H j))
    (R : Set Lattice) (hagree : AgreesOn (fun w => ∑ j, component j w) F R)
    (z : Lattice)
    (hz : ∀ C ∈ (Finset.univ.erase i).powerset, z + ∑ j ∈ C, H j ∈ R) :
    mixedDifference H (Finset.univ.erase i) (component i) z = 0 := by
  rw [← fh_md_isolation component H hperiod i z]
  rw [fh_md_congr H _ _ F z (fun C hC => hagree _ (hz C hC))]
  obtain ⟨j, hj⟩ := hne
  exact fh_md_kills_period H _ j hj F (hF j) z

private theorem fh_md_succ_isolation {n : ℕ} {A : Type*} [Ring A]
    (component : Fin (n + 1) → Configuration A) (i : Fin (n + 1))
    (H : Fin n → Lattice)
    (hperiod : ∀ j, HasPeriod (component (i.succAbove j)) (H j)) (z : Lattice) :
    mixedDifference H Finset.univ (fun w => ∑ j, component j w) z =
      mixedDifference H Finset.univ (component i) z := by
  rw [fh_md_sum]
  apply Finset.sum_eq_single i
  · intro j hj hji
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hji
    exact fh_md_kills_period H _ j (Finset.mem_univ _) _ (hperiod j) z
  · simp

private theorem fh_regional_isolation {n : ℕ} {A : Type*} [Ring A]
    (hn : 0 < n) (component : Fin (n + 1) → Configuration A)
    (i : Fin (n + 1)) (H : Fin n → Lattice)
    (hperiod : ∀ j, HasPeriod (component (i.succAbove j)) (H j))
    (F : Configuration A) (hF : ∀ j, HasPeriod F (H j))
    (R : Set Lattice) (hagree : AgreesOn (fun w => ∑ j, component j w) F R)
    (z : Lattice)
    (hz : ∀ C : Finset (Fin n), z + ∑ j ∈ C, H j ∈ R) :
    mixedDifference H Finset.univ (component i) z = 0 := by
  rw [← fh_md_succ_isolation component i H hperiod z]
  rw [fh_md_congr H _ _ F z (fun C _ => hagree _ (hz C))]
  exact fh_md_kills_period H _ ⟨0, hn⟩ (Finset.mem_univ _) F (hF _) z

private theorem fh_saturated_isolation {n : ℕ} {A : Type*} [Ring A]
    (hn : 0 < n) (component : Fin (n + 1) → Configuration A)
    (i : Fin (n + 1)) (H : Fin n → Lattice)
    (hperiod : ∀ j, HasPeriod (component (i.succAbove j)) (H j))
    (F : Configuration A) (hF : ∀ j, HasPeriod F (H j))
    (R : Set Lattice) (hagree : AgreesOn (fun w => ∑ j, component j w) F R)
    (h : Lattice) (hh : HasPeriod (component i) h) (z : Lattice)
    (hz : ∃ q : ℤ, ∀ C : Finset (Fin n), z + q • h + ∑ j ∈ C, H j ∈ R) :
    mixedDifference H Finset.univ (component i) z = 0 := by
  obtain ⟨q, hq⟩ := hz
  rw [← hasPeriod_zsmul _ h (fh_md_period H Finset.univ (component i) h hh) q z]
  exact fh_regional_isolation hn component i H hperiod F hF R hagree _ hq

private theorem fh_component_from_saturation
    (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 0 < n)
    (component : Fin (n + 1) → Configuration (ZMod p))
    (v : Fin (n + 1) → Lattice) (hv : ∀ i, Primitive (v i))
    (k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (hperiod : ∀ i, HasPeriod (component i) ((k i : ℤ) • v i))
    (hpairwise : Pairwise (fun i j => Nonparallel (v i) (v j)))
    (R : Set Lattice) (F : Configuration (ZMod p)) (hF : DoublyPeriodic F)
    (hagree : AgreesOn (fun w => ∑ j, component j w) F R)
    (i : Fin (n + 1))
    (hsat : ∀ E : Finset Lattice,
      (((∃ x, x ∈ realLine (v i) ∧ x ∈ interior (regionCone R)) ∧
        ∀ z : Lattice, ∃ q : ℤ, ∀ e ∈ E,
          z + q • ((k i : ℤ) • v i) + e ∈ R) ∨
       (Disjoint (realLine (v i)) (interior (regionCone R)) ∧
        ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
          regionCone R ⊆ {w | 0 ≤ (σ : ℝ) * realDet (embed (v i)) w} ∧
          ∃ c : ℤ, ∀ z : Lattice, c ≤ σ * det (v i) z →
            ∃ q : ℤ, ∀ e ∈ E, z + q • ((k i : ℤ) • v i) + e ∈ R))) :
    ((∃ x, x ∈ realLine (v i) ∧ x ∈ interior (regionCone R)) ∧
      DoublyPeriodic (component i)) ∨
    (Disjoint (realLine (v i)) (interior (regionCone R)) ∧
      ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∃ t : ℤ,
        regionCone R ⊆ {w | 0 ≤ (σ : ℝ) * realDet (embed (v i)) w} ∧
        FullyPeriodicOn (component i) (signedUpperHalf σ (v i) t)) := by
  classical
  obtain ⟨N, hN, hNF⟩ := (doublyPeriodic_iff_grid F).mp hF
  let H : Fin n → Lattice := fun j =>
    (N : ℤ) • ((k (i.succAbove j) : ℤ) • v (i.succAbove j))
  have hHP : ∀ j, HasPeriod (component (i.succAbove j)) (H j) :=
    fun j => hasPeriod_zsmul _ _ (hperiod _) N
  have hHF : ∀ j, HasPeriod F (H j) := fun j => hNF _
  have htrans : ∀ j, det (v i) (H j) ≠ 0 := by
    intro j
    have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    have hk0 : (k (i.succAbove j) : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hk _)
    have hdet : det (v i) (H j) =
        (N : ℤ) * (k (i.succAbove j) : ℤ) * det (v i) (v (i.succAbove j)) := by
      simp [H, det, smul_eq_mul]
      ring
    rw [hdet]
    exact mul_ne_zero (mul_ne_zero hN0 hk0) (hpairwise (Fin.succAbove_ne _ _).symm)
  let E : Finset Lattice := Finset.univ.powerset.image (fun C : Finset (Fin n) => ∑ j ∈ C, H j)
  have hmem : ∀ C : Finset (Fin n), (∑ j ∈ C, H j) ∈ E := by
    intro C
    exact Finset.mem_image.mpr ⟨C, Finset.mem_powerset.mpr (Finset.subset_univ C), rfl⟩
  have annihilate : ∀ z, (∃ q : ℤ, ∀ e ∈ E,
      z + q • ((k i : ℤ) • v i) + e ∈ R) →
      mixedDifference H Finset.univ (component i) z = 0 := by
    intro z hz
    obtain ⟨q, hq⟩ := hz
    exact fh_saturated_isolation hn component i H hHP F hHF R hagree _ (hperiod i) z
      ⟨q, fun C => hq _ (hmem C)⟩
  obtain ⟨u, hu⟩ := primitive_height_surjective (v i) (hv i) 1
  change det (v i) u = 1 at hu
  rcases hsat E with ⟨hline, hglobal⟩ | ⟨hline, σ, hσ, hcone, c, hhalf⟩
  · left
    refine ⟨hline, ?_⟩
    let B : LatticeBasis := ⟨v i, u, Or.inl hu⟩
    exact lemma8_8_global p hp (component i) B (hv i) (k i) (hk i) (hperiod i)
      n hn H (by intro j; simpa [LatticeBasis.row, B, hu] using htrans j)
      (fun z => annihilate z (hglobal z))
  · right
    have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hbasis : det (v i) (σ • u) = σ := by
      calc
        _ = σ * det (v i) u := by simp [det, smul_eq_mul]; ring
        _ = σ := by rw [hu, mul_one]
    let B : LatticeBasis := ⟨v i, σ • u, by rw [hbasis]; exact hσ⟩
    have hrow : ∀ z, B.row z = σ * det (v i) z := by
      intro z
      simp only [LatticeBasis.row, B, hbasis]
    obtain ⟨q, hq, heq, hfull⟩ := lemma8_8 p hp (component i) B (hv i) (k i) (hk i)
      (hperiod i) n hn H (by intro j; rw [hrow]; exact mul_ne_zero hσne (htrans j)) c
      (by intro z hz; apply annihilate z; apply hhalf z; rwa [hrow] at hz)
    refine ⟨hline, σ, hσ, c + ∑ j, min (B.row (H j)) 0, hcone, ?_⟩
    refine ⟨(k i : ℤ) • v i, (q : ℤ) • (σ • u), ?_⟩
    simpa only [signedUpperHalf, hrow, B] using hfull

private theorem fh_cone_add (R : Set Lattice) {u v : RealPlane}
    (hu : u ∈ regionCone R) (hv : v ∈ regionCone R) : u + v ∈ regionCone R := by
  intro x hx
  simpa only [add_assoc] using hv (x + u) (hu x hx)

private theorem fh_cone_smul (R : Set Lattice) {v : RealPlane}
    (hv : v ∈ regionCone R) {t : ℝ} (ht : 0 ≤ t) : t • v ∈ regionCone R := by
  have hconv : Convex ℝ (closedRealHull R) := (convex_convexHull ℝ (embed '' R)).closure
  intro x hx
  have hn : ∀ n : ℕ, x + (n : ℝ) • v ∈ closedRealHull R := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, zero_smul, add_zero] using hx
    | succ n ih => simpa [add_smul, add_assoc] using hv _ ih
  obtain ⟨n, hnt⟩ := exists_nat_gt t
  have hnp : (0 : ℝ) < n := lt_of_le_of_lt ht hnt
  have hseg := hconv.add_smul_mem hx (hn n)
    (show t / (n : ℝ) ∈ Set.Icc 0 1 from
      ⟨div_nonneg ht hnp.le, (div_le_one hnp).mpr hnt.le⟩)
  simpa only [smul_smul, div_mul_cancel₀ _ hnp.ne'] using hseg

private theorem fh_cone_convex (R : Set Lattice) : Convex ℝ (regionCone R) := by
  intro x hx y hy a b ha hb hab
  exact fh_cone_add R (fh_cone_smul R hx ha) (fh_cone_smul R hy hb)

private theorem fh_realDet_zero_line (v : Lattice) (hv : v ≠ 0) (x : RealPlane)
    (hdet : realDet (embed v) x = 0) : x ∈ realLine v := by
  by_cases hfirst : v.1 = 0
  · have hsecond : v.2 ≠ 0 := by
      intro h
      exact hv (Prod.ext hfirst h)
    have hsecondR : (v.2 : ℝ) ≠ 0 := by exact_mod_cast hsecond
    refine ⟨x.2 / v.2, ?_⟩
    ext
    · have hx : x.1 = 0 := by
        have hm : (v.2 : ℝ) * x.1 = 0 := by simpa [realDet, embed, hfirst] using hdet
        exact (mul_eq_zero.mp hm).resolve_left hsecondR
      simp [embed, hfirst, hx]
    · simp [embed, smul_eq_mul, hsecondR]
  · have hfirstR : (v.1 : ℝ) ≠ 0 := by exact_mod_cast hfirst
    refine ⟨x.1 / v.1, ?_⟩
    ext
    · simp [embed, smul_eq_mul, hfirstR]
    · dsimp [embed, smul_eq_mul]
      dsimp [realDet, embed] at hdet
      field_simp
      nlinarith

private theorem fh_cone_side (R : Set Lattice) (g : RealPlane)
    (hg : g ∈ interior (regionCone R)) (v : Lattice) (hv : v ≠ 0)
    (havoid : Disjoint (realLine v) (interior (regionCone R))) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      0 < (σ : ℝ) * realDet (embed v) g ∧
      regionCone R ⊆ {w | 0 ≤ (σ : ℝ) * realDet (embed v) w} := by
  have hgn : realDet (embed v) g ≠ 0 := by
    intro heq
    exact Set.disjoint_left.mp havoid (fh_realDet_zero_line v hv g heq) hg
  have same_side : ∀ w ∈ regionCone R,
      0 ≤ realDet (embed v) g * realDet (embed v) w := by
    intro w hw
    by_contra hneg
    have hneg' := lt_of_not_ge hneg
    let a : ℝ := realDet (embed v) g
    let b : ℝ := realDet (embed v) w
    have hab : a * b < 0 := hneg'
    have haneq : a ≠ 0 := hgn
    have hbneq : b ≠ 0 := by intro hz; simp [hz] at hab
    have hsub : b - a ≠ 0 := by intro hz; have : b = a := sub_eq_zero.mp hz; rw [this] at hab; nlinarith [sq_nonneg a]
    have hratio : 0 < b / (b - a) := by
      rcases lt_or_gt_of_ne haneq with ha | ha
      · have hb : 0 < b := by nlinarith
        exact div_pos hb (by linarith)
      · have hb : b < 0 := by nlinarith
        exact div_pos_of_neg_of_neg hb (by linarith)
    have hother : 0 ≤ -a / (b - a) := by
      rcases lt_or_gt_of_ne haneq with ha | ha
      · have hb : 0 < b := by nlinarith
        exact (div_pos (by linarith) (by linarith)).le
      · have hb : b < 0 := by nlinarith
        exact (div_pos_of_neg_of_neg (by linarith) (by linarith)).le
    have hsum : b / (b - a) + -a / (b - a) = 1 := by field_simp; ring
    have hin := (fh_cone_convex R).combo_interior_self_mem_interior hg hw hratio hother hsum
    have hlin : (b / (b - a)) • g + (-a / (b - a)) • w ∈ realLine v := by
      apply fh_realDet_zero_line v hv
      have hcalc : realDet (embed v) ((b / (b - a)) • g + (-a / (b - a)) • w) =
          (b * a - a * b) / (b - a) := by
        dsimp [realDet, embed, a, b]
        ring
      rw [hcalc, mul_comm b a, sub_self, zero_div]
    exact Set.disjoint_left.mp havoid hlin hin
  rcases lt_or_gt_of_ne hgn with hgneg | hgpos
  · refine ⟨-1, Or.inr rfl, by simp; exact hgneg, ?_⟩
    intro w hw
    have h := same_side w hw
    change 0 ≤ ((-1 : ℤ) : ℝ) * realDet (embed v) w
    norm_num
    nlinarith
  · refine ⟨1, Or.inl rfl, by simpa using hgpos, ?_⟩
    intro w hw
    have h := same_side w hw
    change 0 ≤ ((1 : ℤ) : ℝ) * realDet (embed v) w
    norm_num
    nlinarith

private theorem fh_cone_half_saturation (R : Set Lattice)
    (g : RealPlane) (hg : g ∈ interior (regionCone R))
    (v : Lattice) (k : ℕ) (hk : 0 < k) (σ : ℤ)
    (hpos : 0 < (σ : ℝ) * realDet (embed v) g) :
    ∃ c : ℤ, ∀ z : Lattice, c ≤ σ * det v z →
      ∃ q : ℤ, embed (z + q • ((k : ℤ) • v)) ∈ regionCone R := by
  let d := embed v
  let δ := realDet d g
  let a : ℝ := (σ : ℝ) * δ
  have ha : 0 < a := hpos
  have hδ : δ ≠ 0 := by intro h; simp [a, h] at ha
  have hσ : (σ : ℝ) ≠ 0 := by intro h; simp [a, h] at ha
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hcont : Continuous (fun t : ℝ => g + t • d) := by fun_prop
  have hpre : (fun t : ℝ => g + t • d) ⁻¹' regionCone R ∈ nhds (0 : ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa only [zero_smul, add_zero] using mem_interior_iff_mem_nhds.mp hg
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨⌈a * ((k : ℝ) / ε)⌉, ?_⟩
  intro z hz
  let w := embed z
  let α : ℝ := realDet d w / δ
  let β : ℝ := realDet w g / δ
  have hα : α = ((σ : ℝ) * realDet d w) / a := by
    dsimp [α, a]
    field_simp
  have hcast : realDet d w = (det v z : ℝ) := by simp [d, w, realDet, det, embed]
  have hrow : (⌈a * ((k : ℝ) / ε)⌉ : ℝ) ≤ (σ : ℝ) * realDet d w := by
    rw [hcast]
    exact_mod_cast hz
  have hαlower : (k : ℝ) / ε ≤ α := by
    rw [hα]
    apply (le_div_iff₀ ha).mpr
    have hh := (Int.le_ceil (a * ((k : ℝ) / ε))).trans hrow
    nlinarith
  have hαpos : 0 < α := lt_of_lt_of_le (div_pos hkp hε) hαlower
  have hdecomp : w = α • g + β • d := by
    ext <;> dsimp [α, β] <;> field_simp <;> dsimp [δ, realDet] <;> ring
  let q : ℤ := -⌊β / (k : ℝ)⌋
  let r : ℝ := β + (q : ℝ) * k
  have hr0 : 0 ≤ r := by
    have hh := (le_div_iff₀ hkp).mp (Int.floor_le (β / (k : ℝ)))
    dsimp [r, q]
    rw [Int.cast_neg]
    nlinarith
  have hrk : r < k := by
    have hh := (div_lt_iff₀ hkp).mp (Int.lt_floor_add_one (β / (k : ℝ)))
    dsimp [r, q]
    rw [Int.cast_neg]
    nlinarith
  have ht0 : 0 ≤ r / α := div_nonneg hr0 hαpos.le
  have htε : r / α < ε := by
    apply (div_lt_iff₀ hαpos).mpr
    have hh := (div_le_iff₀ hε).mp hαlower
    nlinarith
  have hnear : g + (r / α) • d ∈ regionCone R := by
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0] using htε
  refine ⟨q, ?_⟩
  have hembed : embed (z + q • ((k : ℤ) • v)) = w + ((q : ℝ) * k) • d := by
    ext <;> simp [w, d, embed, smul_eq_mul] <;> ring
  rw [hembed, hdecomp]
  have hrew : α • g + β • d + ((q : ℝ) * k) • d = α • (g + (r / α) • d) := by
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hαpos.ne']
    dsimp [r]
    rw [add_smul, add_assoc]
  rw [hrew]
  exact fh_cone_smul R hnear hαpos.le

private theorem fh_cone_interior_absorb (R : Set Lattice) (g : RealPlane)
    (hg : g ∈ interior (regionCone R)) (w : RealPlane) :
    ∃ T : ℝ, 0 < T ∧ ∀ t ≥ T, w + t • g ∈ regionCone R := by
  have hcont : Continuous (fun t : ℝ => g + t • w) := by fun_prop
  have hpre : (fun t : ℝ => g + t • w) ⁻¹' regionCone R ∈ nhds (0 : ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa only [zero_smul, add_zero] using mem_interior_iff_mem_nhds.mp hg
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have he : 0 < ε / 2 := by positivity
  have hpoint : g + (ε / 2) • w ∈ regionCone R := by
    apply hball
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos he]
    linarith
  have hbase : w + (ε / 2)⁻¹ • g ∈ regionCone R := by
    have h := fh_cone_smul R hpoint (inv_nonneg.mpr he.le)
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ he.ne', one_smul, add_comm] using h
  refine ⟨(ε / 2)⁻¹, inv_pos.mpr he, ?_⟩
  intro t ht
  have h := fh_cone_add R hbase (fh_cone_smul R (interior_subset hg) (sub_nonneg.mpr ht))
  convert h using 1
  rw [add_assoc, ← add_smul]
  congr 1
  ring

private theorem fh_cone_line_saturation (R : Set Lattice) (v : Lattice)
    (k : ℕ) (hk : 0 < k)
    (hline : ∃ x, x ∈ realLine v ∧ x ∈ interior (regionCone R)) :
    ∀ z : Lattice, ∃ q : ℤ, embed (z + q • ((k : ℤ) • v)) ∈ regionCone R := by
  obtain ⟨x, ⟨t, rfl⟩, hx⟩ := hline
  intro z
  obtain ⟨T, hT, hbound⟩ := fh_cone_interior_absorb R (t • embed v) hx (embed z)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases ht0 : t = 0
  · refine ⟨0, ?_⟩
    simpa [ht0] using hbound T le_rfl
  have embed_shift : ∀ q : ℤ,
      embed (z + q • ((k : ℤ) • v)) = embed z + (((q : ℝ) * k) / t) • (t • embed v) := by
    intro q
    simp only [smul_smul, div_mul_cancel₀ _ ht0]
    ext <;> simp [embed, smul_eq_mul] <;> ring
  rcases lt_or_gt_of_ne ht0 with ht | ht
  · refine ⟨⌊T * t / (k : ℝ)⌋, ?_⟩
    rw [embed_shift]
    apply hbound
    apply (le_div_iff_of_neg ht).mpr
    have h := (le_div_iff₀ hkR).mp (Int.floor_le (T * t / (k : ℝ)))
    linarith
  · refine ⟨⌈T * t / (k : ℝ)⌉, ?_⟩
    rw [embed_shift]
    apply hbound
    apply (le_div_iff₀ ht).mpr
    have h := (div_le_iff₀ hkR).mp (Int.le_ceil (T * t / (k : ℝ)))
    linarith

private theorem fh_region_period_saturation
    (R : Set Lattice) (hR : LatticeConvexRegion R) (hne : R.Nonempty)
    (a b : Lattice) (hab : Nonparallel a b)
    (ha : ForwardInvariant R a) (hb : ForwardInvariant R b)
    (v : Lattice) (hv : Primitive v) (k : ℕ) (hk : 0 < k)
    (E : Finset Lattice) :
    (((∃ x, x ∈ realLine v ∧ x ∈ interior (regionCone R)) ∧
       ∀ z : Lattice, ∃ q : ℤ,
         ∀ e ∈ E, z + q • ((k : ℤ) • v) + e ∈ R) ∨
     (Disjoint (realLine v) (interior (regionCone R)) ∧
       ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
         regionCone R ⊆ {w | 0 ≤ (σ : ℝ) * realDet (embed v) w} ∧
         ∃ c : ℤ, ∀ z : Lattice, c ≤ σ * det v z →
           ∃ q : ℤ, ∀ e ∈ E, z + q • ((k : ℤ) • v) + e ∈ R)) := by
  classical
  let f : Configuration Unit := fun _ => ()
  have hfull : FullPeriods f R a b := ⟨hne, hab, ha, hb, fun _ _ => rfl, fun _ _ => rfl⟩
  have hg := (lemma8_2_region_cone f R hR a b hfull).2
  have hentry := lemma8_2_eventual_entry f R (Or.inl hR) a b hfull
  choose N hN using hentry
  let y : Lattice := ((E.sup N : ℕ) : ℤ) • (a + b)
  have hy : ∀ e ∈ E, y + e ∈ R := by
    intro e he
    simpa only [y, add_comm] using hN e (E.sup N) (Finset.le_sup he)
  have htranslate : ∀ w : Lattice, embed w ∈ regionCone R →
      ∀ e ∈ E, y + w + e ∈ R := by
    intro w hw e he
    have hey : embed (y + e) ∈ closedRealHull R := by
      have h := hy e he
      rw [latticeRegion_closedHull R hR] at h
      exact h
    have h := hw _ hey
    rw [latticeRegion_closedHull R hR]
    change embed (y + w + e) ∈ closedRealHull R
    convert h using 1 <;> ext <;> simp [embed] <;> ring
  by_cases hline : ∃ x, x ∈ realLine v ∧ x ∈ interior (regionCone R)
  · refine Or.inl ⟨hline, ?_⟩
    intro z
    obtain ⟨q, hq⟩ := fh_cone_line_saturation R v k hk hline (z - y)
    refine ⟨q, ?_⟩
    intro e he
    have h := htranslate _ hq e he
    convert h using 1 <;> abel
  · have hdisj : Disjoint (realLine v) (interior (regionCone R)) := by
      apply Set.disjoint_left.mpr
      intro x hxl hxi
      exact hline ⟨x, hxl, hxi⟩
    obtain ⟨σ, hσ, hpos, hside⟩ := fh_cone_side R (embed (a + b)) hg v (primitive_ne_zero v hv) hdisj
    obtain ⟨c, hc⟩ := fh_cone_half_saturation R (embed (a + b)) hg v k hk σ hpos
    refine Or.inr ⟨hdisj, σ, hσ, hside, c + σ * det v y, ?_⟩
    intro z hz
    have hrow : c ≤ σ * det v (z - y) := by
      have heq : det v (z - y) = det v z - det v y := by simp [det]; ring
      rw [heq]
      nlinarith
    obtain ⟨q, hq⟩ := hc (z - y) hrow
    refine ⟨q, ?_⟩
    intro e he
    have h := htranslate _ hq e he
    convert h using 1 <;> abel

private theorem fh_cone_closed (R : Set Lattice) : IsClosed (regionCone R) := by
  have heq : regionCone R = ⋂ x ∈ closedRealHull R,
      (fun y : RealPlane => x + y) ⁻¹' closedRealHull R := by
    ext y
    simp only [regionCone, recessionCone, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [heq]
  exact isClosed_biInter fun x _ => isClosed_closure.preimage (by fun_prop)

private theorem fh_sector_from_coordinates (R : Set Lattice)
    (p q : RealPlane →ₗ[ℝ] ℝ) (r s : RealPlane)
    (hpr : p r = 1) (hps : p s = 0) (hqr : q r = 0) (hqs : q s = 1)
    (hcoords : ∀ x, x = (p x) • r + (q x) • s)
    (hp : ∀ x ∈ regionCone R, 0 ≤ p x) (hq : ∀ x ∈ regionCone R, 0 ≤ q x)
    (a b : RealPlane) (ha : a ∈ regionCone R) (hb : b ∈ regionCone R)
    (hab : realDet a b ≠ 0) : ClosedSector (regionCone R) := by
  let P : ℝ → RealPlane := fun t => (1 - t) • r + t • s
  let S : Set ℝ := P ⁻¹' regionCone R
  have hpP : ∀ t, p (P t) = 1 - t := by intro t; simp [P, hpr, hps]
  have hqP : ∀ t, q (P t) = t := by intro t; simp [P, hqr, hqs]
  have hclosed : IsClosed S := (fh_cone_closed R).preimage (by fun_prop)
  have hsub : S ⊆ Set.Icc 0 1 := by
    intro t ht
    have ht' : P t ∈ regionCone R := ht
    have h1 := hp _ ht'
    have h2 := hq _ ht'
    rw [hpP] at h1
    rw [hqP] at h2
    exact ⟨h2, by linarith⟩
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed hsub
  have normalize : ∀ x ∈ regionCone R, x ≠ 0 →
      ∃ l : ℝ, 0 < l ∧ ∃ t ∈ S, x = l • P t := by
    intro x hx hx0
    let l := p x + q x
    have hxp := hp x hx
    have hxq := hq x hx
    have hl : 0 < l := by
      by_contra hn
      have hzero : p x = 0 ∧ q x = 0 := by dsimp [l] at hn; constructor <;> linarith
      apply hx0
      simpa only [hzero.1, hzero.2, zero_smul, add_zero] using hcoords x
    have heq : x = l • P (q x / l) := by
      dsimp only [P]
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hl.ne']
      have hlp : l * (1 - q x / l) = p x := by
        rw [mul_sub, mul_one, mul_div_cancel₀ _ hl.ne']
        dsimp [l]
        ring
      rw [hlp]
      exact hcoords x
    refine ⟨l, hl, q x / l, ?_, heq⟩
    change P (q x / l) ∈ regionCone R
    have hh := fh_cone_smul R hx (inv_nonneg.mpr hl.le)
    rwa [heq, smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at hh
  have ha0 : a ≠ 0 := by intro h; apply hab; simp [h, realDet]
  obtain ⟨la, hla, ta, hta, heqa⟩ := normalize a ha ha0
  have hne : S.Nonempty := ⟨ta, hta⟩
  obtain ⟨lo, hlo⟩ := hcompact.exists_isLeast hne
  obtain ⟨hi, hhi⟩ := hcompact.exists_isGreatest hne
  have hlhi : lo ≤ hi := hlo.2 hhi.1
  have hspan : regionCone R = {x | ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      x = α • P lo + β • P hi} := by
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hx0 : x = 0
      · exact ⟨0, 0, le_rfl, le_rfl, by simp [hx0]⟩
      obtain ⟨l, hl, t, ht, heq⟩ := normalize x hx hx0
      have hlt : lo ≤ t := hlo.2 ht
      have hth : t ≤ hi := hhi.2 ht
      by_cases hsame : lo = hi
      · have htlo : t = lo := by rw [← hsame] at hth; exact le_antisymm hth hlt
        exact ⟨l, 0, hl.le, le_rfl, by simpa only [htlo, zero_smul, add_zero] using heq⟩
      have hdiff : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne hlhi hsame)
      let u := (hi - t) / (hi - lo)
      let v := (t - lo) / (hi - lo)
      have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hth) hdiff.le
      have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hlt) hdiff.le
      have htcombo : P t = u • P lo + v • P hi := by
        ext <;> dsimp [P, u, v] <;> field_simp <;> ring
      refine ⟨l * u, l * v, mul_nonneg hl.le hu, mul_nonneg hl.le hv, ?_⟩
      rw [heq, htcombo, smul_add, smul_smul, smul_smul]
    · rintro x ⟨α, β, hα, hβ, rfl⟩
      exact fh_cone_add R (fh_cone_smul R hlo.1 hα) (fh_cone_smul R hhi.1 hβ)
  refine ⟨P lo, P hi, ?_, hspan⟩
  intro hdet
  have harep := ha
  have hbrep := hb
  rw [hspan] at harep hbrep
  obtain ⟨α, β, hα, hβ, rfl⟩ := harep
  obtain ⟨γ, δ, hγ, hδ, rfl⟩ := hbrep
  apply hab
  have heq : realDet (α • P lo + β • P hi) (γ • P lo + δ • P hi) =
      (α * δ - β * γ) * realDet (P lo) (P hi) := by
    simp [realDet]
    ring
  rw [heq, hdet, mul_zero]

private theorem fh_cone_sector_of_two (R : Set Lattice)
    (g : RealPlane) (hg : g ∈ interior (regionCone R))
    (v w : Lattice) (hvw : Nonparallel v w)
    (havoidv : Disjoint (realLine v) (interior (regionCone R)))
    (havoidw : Disjoint (realLine w) (interior (regionCone R)))
    (a b : Lattice) (ha : embed a ∈ regionCone R) (hb : embed b ∈ regionCone R)
    (hab : Nonparallel a b) : ClosedSector (regionCone R) := by
  obtain ⟨σ, hσ, hposσ, hsideσ⟩ := fh_cone_side R g hg v (nonparallel_ne_zero_left v w hvw) havoidv
  obtain ⟨τ, hτ, hposτ, hsideτ⟩ := fh_cone_side R g hg w (nonparallel_ne_zero_right v w hvw) havoidw
  let p : RealPlane →ₗ[ℝ] ℝ :=
    { toFun := fun x => (σ : ℝ) * realDet (embed v) x
      map_add' := by intro x y; simp [realDet]; ring
      map_smul' := by intro t x; simp [realDet]; ring }
  let q : RealPlane →ₗ[ℝ] ℝ :=
    { toFun := fun x => (τ : ℝ) * realDet (embed w) x
      map_add' := by intro x y; simp [realDet]; ring
      map_smul' := by intro t x; simp [realDet]; ring }
  have hs0 : (σ : ℝ) ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have ht0 : (τ : ℝ) ≠ 0 := by rcases hτ with rfl | rfl <;> norm_num
  let D : ℝ := realDet (embed v) (embed w)
  have hD : D ≠ 0 := by dsimp [D, realDet, embed]; exact_mod_cast hvw
  let r : RealPlane := ((σ : ℝ) * D)⁻¹ • embed w
  let s : RealPlane := (-((τ : ℝ) * D))⁻¹ • embed v
  have hpr : p r = 1 := by
    change (σ : ℝ) * realDet (embed v) (((σ : ℝ) * D)⁻¹ • embed w) = 1
    have hlin : realDet (embed v) (((σ : ℝ) * D)⁻¹ • embed w) = ((σ : ℝ) * D)⁻¹ * D := by
      dsimp [realDet, D]; ring
    rw [hlin]
    field_simp
  have hps : p s = 0 := by
    change (σ : ℝ) * realDet (embed v) ((-((τ : ℝ) * D))⁻¹ • embed v) = 0
    dsimp [realDet]
    ring
  have hqr : q r = 0 := by
    change (τ : ℝ) * realDet (embed w) (((σ : ℝ) * D)⁻¹ • embed w) = 0
    dsimp [realDet]
    ring
  have hqs : q s = 1 := by
    change (τ : ℝ) * realDet (embed w) ((-((τ : ℝ) * D))⁻¹ • embed v) = 1
    have hlin : realDet (embed w) ((-((τ : ℝ) * D))⁻¹ • embed v) =
        (-((τ : ℝ) * D))⁻¹ * -D := by dsimp [realDet, D]; ring
    rw [hlin]
    field_simp
  have hcoords : ∀ x, x = p x • r + q x • s := by
    intro x
    ext <;> dsimp [p, q, r, s] <;> field_simp <;> dsimp [D, realDet] <;> ring
  have habR : realDet (embed a) (embed b) ≠ 0 := by dsimp [realDet, embed]; exact_mod_cast hab
  exact fh_sector_from_coordinates R p q r s hpr hps hqr hqs hcoords
    hsideσ hsideτ (embed a) (embed b) ha hb habR

theorem proposition8_9 (p : ℕ) (hp : p.Prime) (m : ℕ) (hm : 2 ≤ m)
    (component : Fin m → Configuration (ZMod p))
    (v : Fin m → Lattice) (hv : ∀ i, Primitive (v i))
    (k : Fin m → ℕ) (hk : ∀ i, 0 < k i)
    (hperiod : ∀ i, HasPeriod (component i) ((k i : ℤ) • v i))
    (hpairwise : Pairwise (fun i j => Nonparallel (v i) (v j)))
    (R : Set Lattice) (hR : LatticeConvexRegion R) (a b : Lattice)
    (hfull : FullPeriods (fun z => ∑ i, component i z) R a b) :
    embed a ∈ regionCone R ∧ embed b ∈ regionCone R ∧ FullDimensional (regionCone R) ∧
    (∀ i,
      ((∃ x, x ∈ realLine (v i) ∧ x ∈ interior (regionCone R)) ∧
        DoublyPeriodic (component i)) ∨
      (Disjoint (realLine (v i)) (interior (regionCone R)) ∧
        ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∃ t : ℤ,
          regionCone R ⊆ {w | 0 ≤ (σ : ℝ) * realDet (embed (v i)) w} ∧
          FullyPeriodicOn (component i) (signedUpperHalf σ (v i) t))) ∧
    (¬ Periodic (fun z => ∑ i, component i z) →
      (∀ i, ¬ DoublyPeriodic (component i)) →
        ClosedSector (regionCone R) ∧
          ∀ i, embed (v i) ∉ interior (regionCone R) ∧
            embed (-v i) ∉ interior (regionCone R)) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hn : 0 < n := by omega
  have ha := latticeRegion_forward_period_in_cone R hR a hfull.2.2.1
  have hb := latticeRegion_forward_period_in_cone R hR b hfull.2.2.2.1
  have hcone := lemma8_2_region_cone (fun z => ∑ i, component i z) R hR a b hfull
  have hentry : ∀ z, ∃ t : ℕ, z + (t : ℤ) • (a + b) ∈ R := by
    intro z
    obtain ⟨t, ht⟩ := lemma8_2_eventual_entry (fun z => ∑ i, component i z) R (Or.inl hR) a b hfull z
    exact ⟨t, ht t le_rfl⟩
  let F := extensionAlong (fun z => ∑ i, component i z) R (a + b) hentry
  have hex := lemma8_2_extensionAlong (fun z => ∑ i, component i z) R a b hfull hentry
  have hF : DoublyPeriodic F := hex.2.2.2.2.1
  have hagree : AgreesOn (fun z => ∑ i, component i z) F R := fun z hz => (hex.1 z hz).symm
  have hclass : ∀ i,
      ((∃ x, x ∈ realLine (v i) ∧ x ∈ interior (regionCone R)) ∧
        DoublyPeriodic (component i)) ∨
      (Disjoint (realLine (v i)) (interior (regionCone R)) ∧
        ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∃ t : ℤ,
          regionCone R ⊆ {w | 0 ≤ (σ : ℝ) * realDet (embed (v i)) w} ∧
          FullyPeriodicOn (component i) (signedUpperHalf σ (v i) t)) := by
    intro i
    exact fh_component_from_saturation p hp n hn component v hv k hk hperiod hpairwise R F hF hagree i
      (fun E => fh_region_period_saturation R hR hfull.1 a b hfull.2.1 hfull.2.2.1 hfull.2.2.2.1
        (v i) (hv i) (k i) (hk i) E)
  refine ⟨ha, hb, hcone.1, hclass, ?_⟩
  intro haper hnodouble
  have havoid : ∀ i, Disjoint (realLine (v i)) (interior (regionCone R)) := by
    intro i
    rcases hclass i with hc | hc
    · exact False.elim (hnodouble i hc.2)
    · exact hc.1
  have h01 : (⟨0, by omega⟩ : Fin (n + 1)) ≠ ⟨1, by omega⟩ := by
    intro heq
    have hval := congrArg Fin.val heq
    simp at hval
  refine ⟨fh_cone_sector_of_two R (embed (a + b)) hcone.2
    (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) (hpairwise h01)
    (havoid _) (havoid _) a b ha hb hfull.2.1, ?_⟩
  intro i
  constructor
  · intro hmem
    exact Set.disjoint_left.mp (havoid i) ⟨1, by simp⟩ hmem
  · intro hmem
    apply Set.disjoint_left.mp (havoid i) _ hmem
    refine ⟨-1, ?_⟩
    ext <;> simp [embed]

end ConvexNivat
