import ConvexNivat.ReductionDefinitions
import ConvexNivat.CorePeriods
import ConvexNivat.CoreLattice

namespace ConvexNivat
open Filter Topology

/-- 8.16 step 1, separated so its finite-limit argument is an actual obligation. -/
theorem lemma8_16_finite_limits (p : ℕ) (hp : p.Prime)
    (G : Configuration (ZMod p)) (v u : Lattice)
    (hv : Primitive v) (hbasis : det v u = 1) (k : ℕ) (hk : 0 < k)
    (hperiod : HasPeriod G ((k : ℤ) • v)) (d : Lattice) (hnegative : det v d < 0)
    (hlimits : ∀ y, SubsequentialTranslateLimit G d y → DoublyPeriodic y) :
    (translateLimitSet G d).Finite := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : TopologicalSpace (ZMod p) := ⊥
  have hlim (f : ℕ → Configuration (ZMod p)) (y : Configuration (ZMod p)) :
      PointwiseLimit f y ↔ Tendsto f atTop (𝓝 y) := by
    simp only [PointwiseLimit, tendsto_pi_nhds, nhds_discrete, tendsto_pure,
      eventually_atTop]
  have hcluster (y : Configuration (ZMod p)) :
      y ∈ translateLimitSet G d ↔
        MapClusterPt y atTop (fun n : ℕ => translate ((n : ℤ) • d) G) := by
    constructor
    · rintro ⟨n, hn, hy⟩
      exact ((hlim _ _).mp hy).mapClusterPt.of_comp hn.tendsto_atTop
    · intro hy
      obtain ⟨n, hn, ht⟩ := hy.tendsto_subseq
      exact ⟨n, hn, (hlim _ _).mpr ht⟩
  have hclosed : IsClosed (translateLimitSet G d) := by
    have heq : translateLimitSet G d =
        {y | MapClusterPt y atTop (fun n : ℕ => translate ((n : ℤ) • d) G)} := by
      ext y
      exact hcluster y
    rw [heq]
    exact isClosed_setOfPred_clusterPt
  have hcompact : IsCompact (translateLimitSet G d) := hclosed.isCompact
  have hkv (y : Configuration (ZMod p)) (hy : y ∈ translateLimitSet G d) :
      HasPeriod y ((k : ℤ) • v) := by
    obtain ⟨n, hn, hy⟩ := hy
    intro z
    obtain ⟨N₁, hN₁⟩ := hy z
    obtain ⟨N₂, hN₂⟩ := hy (z + (k : ℤ) • v)
    have hp' := (hasPeriod_translate_iff G ((n (max N₁ N₂) : ℤ) • d)
      ((k : ℤ) • v)).mpr hperiod z
    exact (hN₂ (max N₁ N₂) (le_max_right _ _)).symm.trans
      (hp'.trans (hN₁ (max N₁ N₂) (le_max_left _ _)))
  have hshift (y : Configuration (ZMod p)) (hy : y ∈ translateLimitSet G d)
      (a : ℤ) : translate (a • d) y ∈ translateLimitSet G d := by
    obtain ⟨n, hn, hy⟩ := hy
    have hnonneg (j : ℕ) : 0 ≤ (n (j + a.natAbs) : ℤ) + a := by
      have hnj : (a.natAbs : ℤ) ≤ n (j + a.natAbs) := by
        exact_mod_cast (le_trans (Nat.le_add_left _ _) (hn.id_le (j + a.natAbs)))
      have habs := Int.natCast_natAbs a
      have habsa := neg_abs_le a
      omega
    let m : ℕ → ℕ := fun j => ((n (j + a.natAbs) : ℤ) + a).toNat
    have hmcast (j : ℕ) : (m j : ℤ) = (n (j + a.natAbs) : ℤ) + a :=
      Int.toNat_of_nonneg (hnonneg j)
    refine ⟨m, ?_, ?_⟩
    · intro i j hij
      have hlt := hn (Nat.add_lt_add_right hij a.natAbs)
      have hi := hmcast i
      have hj := hmcast j
      omega
    · intro z
      obtain ⟨N, hN⟩ := hy (z + a • d)
      refine ⟨N, fun j hj => ?_⟩
      have heq := hN (j + a.natAbs) (by omega)
      simpa only [translate, hmcast, add_smul, add_assoc, add_comm, add_left_comm]
        using heq
  have hrepr (z : Lattice) : z = det z u • v + det v z • u := by
    have heq : (det v u) • z = det z u • v + det v z • u := by
      ext <;> simp [det] <;> ring
    simpa [hbasis] using heq
  have hcover (e : Lattice) (he : 0 < det v e) :
      ∃ F : Finset Lattice, ∀ z : Lattice,
        ∃ r ∈ F, ∃ a b : ℤ, z = r + a • ((k : ℤ) • v) + b • e := by
    let D := det v e
    let F := ((Finset.Ico (0 : ℤ) k).product (Finset.Ico (0 : ℤ) D)).image
      (fun st => st.1 • v + st.2 • u)
    refine ⟨F, fun z => ?_⟩
    let b := det v z / D
    let w := z - b • e
    let s := det w u
    have hkz : 0 < (k : ℤ) := by exact_mod_cast hk
    have hw : det v w = det v z % D := by
      change height v (z + -(b • e)) = _
      rw [height_add]
      have hneg : -(b • e) = (-b) • e := by simp
      rw [hneg, height_zsmul]
      change det v z + -b * D = _
      have hdiv := Int.ediv_mul_add_emod (det v z) D
      dsimp [b]
      linear_combination -hdiv
    refine ⟨(s % k) • v + (det v z % D) • u, ?_, s / k, b, ?_⟩
    · change _ ∈ ((Finset.Ico (0 : ℤ) k).product (Finset.Ico (0 : ℤ) D)).image _
      apply Finset.mem_image.mpr
      refine ⟨(s % k, det v z % D), ?_, rfl⟩
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (ne_of_gt hkz), Int.emod_lt_of_pos _ hkz⟩,
        Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (ne_of_gt he), Int.emod_lt_of_pos _ he⟩⟩
    · have hwrepr := hrepr w
      rw [hw] at hwrepr
      change w = s • v + (det v z % D) • u at hwrepr
      have hs : s % (k : ℤ) + s / (k : ℤ) * (k : ℤ) = s :=
        Int.emod_add_ediv_mul s k
      calc
        z = w + b • e := by dsimp [w]; abel
        _ = (s • v + (det v z % D) • u) + b • e := by rw [hwrepr]
        _ = ((s % k + s / k * (k : ℤ)) • v + (det v z % D) • u) + b • e := by
          rw [hs]
        _ = ((s % k) • v + (det v z % D) • u) +
            (s / k) • ((k : ℤ) • v) + b • e := by
          rw [smul_smul, add_smul]
          abel
  have hmove (f : Configuration (ZMod p)) (e : Lattice) (R : ℤ)
      (hf : HasPeriod f (R • e)) (z : Lattice) (a b t : ℤ)
      (hab : a = b + t * R) : f (z + a • e) = f (z + b • e) := by
    rw [hab, add_smul, mul_smul, ← add_assoc]
    exact hasPeriod_zsmul f (R • e) hf t (z + b • e)
  have hisolate (θ : Configuration (ZMod p)) (hθ : θ ∈ translateLimitSet G d) :
      ∃ S : Finset Lattice, ∀ x ∈ translateLimitSet G d,
        (∀ z ∈ S, x z = θ z) → x = θ := by
    obtain ⟨q, hq, hqθ⟩ := doublyPeriodic_multiple_period θ (hlimits θ hθ) d
    let e := (-q) • d
    have heθ : HasPeriod θ e := by
      simpa [e] using hasPeriod_neg θ (q • d) hqθ
    have hepos : 0 < det v e := by
      change 0 < height v ((-q) • d)
      rw [height_zsmul]
      change 0 < -q * det v d
      exact mul_pos_of_neg_of_neg (by omega) hnegative
    obtain ⟨F, hF⟩ := hcover e hepos
    have hvalues (f : Configuration (ZMod p)) (hf : HasPeriod f ((k : ℤ) • v))
        (z : Lattice) : ∃ r ∈ F, ∃ b : ℤ,
          f z = f (r + b • e) ∧ θ z = θ r := by
      obtain ⟨r, hr, a, b, hz⟩ := hF z
      refine ⟨r, hr, b, ?_, ?_⟩
      · rw [hz, add_right_comm]
        exact hasPeriod_zsmul f ((k : ℤ) • v) hf a (r + b • e)
      · rw [hz, add_right_comm]
        exact (hasPeriod_zsmul θ ((k : ℤ) • v) (hkv θ hθ) a (r + b • e)).trans
          (hasPeriod_zsmul θ e heθ b r)
    have hdetermine (f : Configuration (ZMod p)) (hf : f ∈ translateLimitSet G d)
        (hag : ∀ r ∈ F, ∀ m : ℕ, 0 < m → f (r - (m : ℤ) • e) = θ r) : f = θ := by
      obtain ⟨R, hR, hRf⟩ := doublyPeriodic_multiple_period f (hlimits f hf) e
      funext z
      obtain ⟨r, hr, b, hfr, hθr⟩ := hvalues f (hkv f hf) z
      let m : ℕ := (R - b % R).toNat
      have hmod := Int.emod_lt_of_pos b (show 0 < R by omega)
      have hmcast : (m : ℤ) = R - b % R := Int.toNat_of_nonneg (by omega)
      have hmpos : 0 < m := by omega
      have hb : b = -(m : ℤ) + (b / R + 1) * R := by
        rw [hmcast]
        linear_combination -(Int.ediv_mul_add_emod b R)
      have hm := hmove f e R hRf r b (-(m : ℤ)) (b / R + 1) hb
      rw [hfr, hθr, hm]
      simpa only [neg_smul, ← sub_eq_add_neg] using hag r hr m hmpos
    by_contra hiso
    push Not at hiso
    let S (n : ℕ) : Finset Lattice := F.biUnion fun z =>
      (Finset.range (n + 1)).image fun j : ℕ => z + (j : ℤ) • e
    choose x hx hag hne using (fun n : ℕ => hiso (S n))
    have hbad (n : ℕ) : ∃ m : ℕ, ∃ r ∈ F,
        x n (r + (m : ℤ) • e) ≠ θ r := by
      by_contra hb
      push Not at hb
      apply hne n
      obtain ⟨R, hR, hRx⟩ := doublyPeriodic_multiple_period (x n) (hlimits _ (hx n)) e
      funext z
      obtain ⟨r, hr, b, hxr, hθr⟩ := hvalues (x n) (hkv _ (hx n)) z
      have hmod : 0 ≤ b % R := Int.emod_nonneg _ (by omega)
      have hmcast : ((b % R).toNat : ℤ) = b % R := Int.toNat_of_nonneg hmod
      have hmb := hmove (x n) e R hRx r b (b % R) (b / R)
        (Int.emod_add_ediv_mul b R).symm
      rw [hxr, hθr, hmb, ← hmcast]
      exact hb (b % R).toNat r hr
    let a (n : ℕ) : ℕ := Nat.find (hbad n)
    have ha_bad (n : ℕ) : ∃ r ∈ F, x n (r + (a n : ℤ) • e) ≠ θ r :=
      Nat.find_spec (hbad n)
    have ha_good (n j : ℕ) (hj : j < a n) (r : Lattice) (hr : r ∈ F) :
        x n (r + (j : ℤ) • e) = θ r := by
      by_contra hne'
      exact Nat.find_min (hbad n) hj ⟨r, hr, hne'⟩
    have ha_large (n : ℕ) : n < a n := by
      by_contra hna
      obtain ⟨r, hr, hbad'⟩ := ha_bad n
      apply hbad'
      have hmem : r + (a n : ℤ) • e ∈ S n := by
        apply Finset.mem_biUnion.mpr
        refine ⟨r, hr, Finset.mem_image.mpr ⟨a n, ?_, rfl⟩⟩
        exact Finset.mem_range.mpr (by omega)
      exact (hag n _ hmem).trans (hasPeriod_zsmul θ e heθ (a n) r)
    let x' (n : ℕ) := translate ((a n : ℤ) • e) (x n)
    have hx' (n : ℕ) : x' n ∈ translateLimitSet G d := by
      simpa only [x', e, smul_smul] using hshift (x n) (hx n) ((a n : ℤ) * -q)
    obtain ⟨y, hy, t, ht, hty⟩ := hcompact.isSeqCompact hx'
    have hty' := (hlim _ _).mpr hty
    have hyeq : y = θ := by
      apply hdetermine y hy
      intro r hr m hm
      obtain ⟨N, hN⟩ := hty' (r - (m : ℤ) • e)
      let j := max N m
      have hmle : m ≤ a (t j) := by
        exact le_trans (le_trans (le_max_right N m) (ht.id_le j))
          (Nat.le_of_lt (ha_large (t j)))
      have hgood := ha_good (t j) (a (t j) - m) (by omega) r hr
      have hcast : ((a (t j) - m : ℕ) : ℤ) = (a (t j) : ℤ) - m :=
        Nat.cast_sub hmle
      have hlattice : r - (m : ℤ) • e + (a (t j) : ℤ) • e =
          r + ((a (t j) - m : ℕ) : ℤ) • e := by
        rw [hcast, sub_smul]
        abel
      have hh := hN j (le_max_left _ _)
      change x (t j) (r - (m : ℤ) • e + (a (t j) : ℤ) • e) = _ at hh
      rw [hlattice] at hh
      exact hh.symm.trans hgood
    have hevent : ∀ᶠ j in atTop, ∀ r ∈ F, x' (t j) r = θ r := by
      apply F.eventually_all.mpr
      intro r hr
      obtain ⟨N, hN⟩ := hty' r
      exact eventually_atTop.mpr ⟨N, fun j hj => (hN j hj).trans (congrFun hyeq r)⟩
    obtain ⟨j, hj⟩ := hevent.exists
    obtain ⟨r, hr, hbad'⟩ := ha_bad (t j)
    exact hbad' (hj r hr)
  apply hcompact.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro θ hθ
  obtain ⟨S, hS⟩ := hisolate θ hθ
  refine ⟨{x | ∀ z ∈ S, x z = θ z}, ?_, ?_⟩
  · change IsOpen ((S : Set Lattice).pi (fun z => {θ z}))
    exact isOpen_set_pi S.finite_toSet (fun _ _ => isOpen_discrete _)
  · ext x
    constructor
    · rintro ⟨hxS, hx⟩
      exact Set.mem_singleton_iff.mpr (hS x hx hxS)
    · rintro rfl
      exact ⟨fun _ _ => rfl, hθ⟩

/-- 8.16, including the quantification over every actual subsequential limit. -/
theorem lemma8_16 (p : ℕ) (hp : p.Prime) (G : Configuration (ZMod p))
    (v u : Lattice) (hv : Primitive v) (hbasis : det v u = 1)
    (k : ℕ) (hk : 0 < k) (hperiod : HasPeriod G ((k : ℤ) • v))
    (d : Lattice) (hnegative : det v d < 0)
    (hlimits : ∀ y, SubsequentialTranslateLimit G d y → DoublyPeriodic y) :
    ∃ β : ℤ, ∃ θstar : Configuration (ZMod p),
      DoublyPeriodic θstar ∧ AgreesOn G θstar (lowerHalf v β) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : TopologicalSpace (ZMod p) := ⊥
  have hlim (f : ℕ → Configuration (ZMod p)) (y : Configuration (ZMod p)) :
      PointwiseLimit f y ↔ Tendsto f atTop (𝓝 y) := by
    simp only [PointwiseLimit, tendsto_pi_nhds, nhds_discrete, tendsto_pure,
      eventually_atTop]
  have hfinite := lemma8_16_finite_limits p hp G v u hv hbasis k hk hperiod d hnegative hlimits
  have hkv (y : Configuration (ZMod p)) (hy : y ∈ translateLimitSet G d) :
      HasPeriod y ((k : ℤ) • v) := by
    obtain ⟨n, hn, hy⟩ := hy
    intro z
    obtain ⟨N₁, hN₁⟩ := hy z
    obtain ⟨N₂, hN₂⟩ := hy (z + (k : ℤ) • v)
    have hp' := (hasPeriod_translate_iff G ((n (max N₁ N₂) : ℤ) • d)
      ((k : ℤ) • v)).mpr hperiod z
    exact (hN₂ (max N₁ N₂) (le_max_right _ _)).symm.trans
      (hp'.trans (hN₁ (max N₁ N₂) (le_max_left _ _)))
  have hshift (y : Configuration (ZMod p)) (hy : y ∈ translateLimitSet G d)
      (a : ℤ) : translate (a • d) y ∈ translateLimitSet G d := by
    obtain ⟨n, hn, hy⟩ := hy
    have hnonneg (j : ℕ) : 0 ≤ (n (j + a.natAbs) : ℤ) + a := by
      have hnj : (a.natAbs : ℤ) ≤ n (j + a.natAbs) := by
        exact_mod_cast (le_trans (Nat.le_add_left _ _) (hn.id_le (j + a.natAbs)))
      have habs := Int.natCast_natAbs a
      have habsa := neg_abs_le a
      omega
    let m : ℕ → ℕ := fun j => ((n (j + a.natAbs) : ℤ) + a).toNat
    have hmcast (j : ℕ) : (m j : ℤ) = (n (j + a.natAbs) : ℤ) + a :=
      Int.toNat_of_nonneg (hnonneg j)
    refine ⟨m, ?_, ?_⟩
    · intro i j hij
      have hlt := hn (Nat.add_lt_add_right hij a.natAbs)
      have hi := hmcast i
      have hj := hmcast j
      omega
    · intro z
      obtain ⟨N, hN⟩ := hy (z + a • d)
      refine ⟨N, fun j hj => ?_⟩
      have heq := hN (j + a.natAbs) (by omega)
      simpa only [translate, hmcast, add_smul, add_assoc, add_comm, add_left_comm]
        using heq
  have hrepr (z : Lattice) : z = det z u • v + det v z • u := by
    have heq : (det v u) • z = det z u • v + det v z • u := by
      ext <;> simp [det] <;> ring
    simpa [hbasis] using heq
  have hcover (e : Lattice) (he : 0 < det v e) :
      ∃ F : Finset Lattice, ∀ z : Lattice,
        ∃ r ∈ F, ∃ a b : ℤ, z = r + a • ((k : ℤ) • v) + b • e := by
    let D := det v e
    let F := ((Finset.Ico (0 : ℤ) k).product (Finset.Ico (0 : ℤ) D)).image
      (fun st => st.1 • v + st.2 • u)
    refine ⟨F, fun z => ?_⟩
    let b := det v z / D
    let w := z - b • e
    let s := det w u
    have hkz : 0 < (k : ℤ) := by exact_mod_cast hk
    have hw : det v w = det v z % D := by
      change height v (z + -(b • e)) = _
      rw [height_add]
      have hneg : -(b • e) = (-b) • e := by simp
      rw [hneg, height_zsmul]
      change det v z + -b * D = _
      have hdiv := Int.ediv_mul_add_emod (det v z) D
      dsimp [b]
      linear_combination -hdiv
    refine ⟨(s % k) • v + (det v z % D) • u, ?_, s / k, b, ?_⟩
    · change _ ∈ ((Finset.Ico (0 : ℤ) k).product (Finset.Ico (0 : ℤ) D)).image _
      apply Finset.mem_image.mpr
      refine ⟨(s % k, det v z % D), ?_, rfl⟩
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (ne_of_gt hkz), Int.emod_lt_of_pos _ hkz⟩,
        Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (ne_of_gt he), Int.emod_lt_of_pos _ he⟩⟩
    · have hwrepr := hrepr w
      rw [hw] at hwrepr
      change w = s • v + (det v z % D) • u at hwrepr
      have hs : s % (k : ℤ) + s / (k : ℤ) * (k : ℤ) = s :=
        Int.emod_add_ediv_mul s k
      calc
        z = w + b • e := by dsimp [w]; abel
        _ = (s • v + (det v z % D) • u) + b • e := by rw [hwrepr]
        _ = ((s % k + s / k * (k : ℤ)) • v + (det v z % D) • u) + b • e := by
          rw [hs]
        _ = ((s % k) • v + (det v z % D) • u) +
            (s / k) • ((k : ℤ) • v) + b • e := by
          rw [smul_smul, add_smul]
          abel
  have hevent (S : Finset Lattice) : ∀ᶠ n : ℕ in atTop,
      ∃ y ∈ translateLimitSet G d, ∀ z ∈ S, translate ((n : ℤ) • d) G z = y z := by
    by_contra he
    obtain ⟨t, ht, hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp he)
    obtain ⟨y, r, hr, hry⟩ := SeqCompactSpace.tendsto_subseq
      (fun j : ℕ => translate ((t j : ℤ) • d) G)
    have hy : y ∈ translateLimitSet G d := ⟨t ∘ r, ht.comp hr, (hlim _ _).mpr hry⟩
    have hpoint := (hlim _ _).mpr hry
    have ha : ∀ᶠ j in atTop, ∀ z ∈ S, translate ((t (r j) : ℤ) • d) G z = y z := by
      apply S.eventually_all.mpr
      intro z hz
      exact eventually_atTop.mpr (hpoint z)
    obtain ⟨j, hj⟩ := ha.exists
    exact hbad (r j) ⟨y, hy, hj⟩
  haveI : Fintype (translateLimitSet G d) := hfinite.fintype
  have hsep : ∀ x y : translateLimitSet G d, ∃ z : Lattice,
      x ≠ y → x.val z ≠ y.val z := by
    intro x y
    by_cases h : x = y
    · exact ⟨0, fun hh => (hh h).elim⟩
    · have hne : x.val ≠ y.val := fun heq => h (Subtype.ext heq)
      have hex : ∃ z, x.val z ≠ y.val z := by
        by_contra hn
        push Not at hn
        exact hne (funext hn)
      obtain ⟨z, hz⟩ := hex
      exact ⟨z, fun _ => hz⟩
  choose sep hsep using hsep
  let S₀ : Finset Lattice := Finset.univ.image
    (fun xy : (translateLimitSet G d) × (translateLimitSet G d) => sep xy.1 xy.2)
  have hdist (x y : Configuration (ZMod p))
      (hx : x ∈ translateLimitSet G d) (hy : y ∈ translateLimitSet G d)
      (ha : ∀ z ∈ S₀, x z = y z) : x = y := by
    by_contra hne
    have hxy : (⟨x, hx⟩ : translateLimitSet G d) ≠ ⟨y, hy⟩ := by
      intro heq
      exact hne (congrArg Subtype.val heq)
    apply hsep ⟨x, hx⟩ ⟨y, hy⟩ hxy
    apply ha
    exact Finset.mem_image.mpr ⟨(⟨x, hx⟩, ⟨y, hy⟩), Finset.mem_univ _, rfl⟩
  have hepos : 0 < det v (-d) := by
    have hh := height_zsmul v d (-1)
    simp only [neg_smul, one_smul, neg_mul, one_mul] at hh
    change det v (-d) = -det v d at hh
    rw [hh]
    omega
  obtain ⟨F, hF⟩ := hcover (-d) hepos
  let S := (S₀ ∪ S₀.image (fun z => z + d)) ∪ F
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hevent S)
  have hex (n : ℕ) : ∃ y ∈ translateLimitSet G d,
      ∀ z ∈ S, translate (((N + n : ℕ) : ℤ) • d) G z = y z :=
    hN (N + n) (Nat.le_add_right _ _)
  choose y hy hag using hex
  have hstep (n : ℕ) : y (n + 1) = translate d (y n) := by
    apply hdist _ _ (hy (n + 1))
      (by simpa using hshift (y n) (hy n) 1)
    intro z hz
    have hzS : z ∈ S := Finset.mem_union_left _ (Finset.mem_union_left _ hz)
    have hzdS : z + d ∈ S := Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
    have h1 := hag (n + 1) z hzS
    have h2 := hag n (z + d) hzdS
    change _ = y n (z + d)
    rw [← h1, ← h2]
    simp only [translate, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    congr 1
    abel
  have htrack (n : ℕ) : y n = translate ((n : ℤ) • d) (y 0) := by
    induction n with
    | zero =>
      funext z
      change y 0 z = y 0 (z + (0 : ℤ) • d)
      rw [zero_smul, add_zero]
    | succ n ih =>
      rw [hstep, ih]
      funext z
      simp only [translate, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      congr 1
      abel
  have hFn : F.Nonempty := by
    obtain ⟨r, hr, a, b, hz⟩ := hF 0
    exact ⟨r, hr⟩
  let B := F.inf' hFn (det v)
  let θstar := translate (-(N : ℤ) • d) (y 0)
  have hθstar : DoublyPeriodic θstar :=
    (doublyPeriodic_translate_iff (y 0) (-(N : ℤ) • d)).mpr (hlimits _ (hy 0))
  refine ⟨B + (N : ℤ) * det v d, θstar, hθstar, ?_⟩
  intro w hw
  change det v w ≤ B + (N : ℤ) * det v d at hw
  obtain ⟨r, hr, a, b, hwrepr⟩ := hF w
  have hB : B ≤ det v r := Finset.inf'_le _ hr
  have hwdet : det v w = det v r + (-b) * det v d := by
    rw [hwrepr]
    change height v (r + a • ((k : ℤ) • v) + b • (-d)) = _
    rw [height_add, height_add, height_zsmul, height_zsmul, height_self]
    have hneg : -d = (-1 : ℤ) • d := by simp
    rw [hneg, height_zsmul, height_zsmul]
    change det v r + a * ((k : ℤ) * 0) + b * ((-1) * det v d) = _
    ring
  have hnN : (N : ℤ) ≤ -b := by nlinarith
  let n : ℕ := (-b).toNat
  have hncast : (n : ℤ) = -b := Int.toNat_of_nonneg (by omega)
  have hnN' : N ≤ n := by omega
  let m := n - N
  have hNm : N + m = n := by dsimp [m]; omega
  have hnm : (n : ℤ) - N = (m : ℤ) := (Nat.cast_sub hnN').symm
  have hwrepr' : w = r + a • ((k : ℤ) • v) + (n : ℤ) • d := by
    rw [hwrepr, hncast, smul_neg, neg_smul]
  have hG : G w = y m r := by
    calc
      G w = G (r + (n : ℤ) • d) := by
        rw [hwrepr', add_right_comm]
        exact hasPeriod_zsmul G ((k : ℤ) • v) hperiod a (r + (n : ℤ) • d)
      _ = y m r := by
        have hh := hag m r (Finset.mem_union_right _ hr)
        simpa only [hNm, translate] using hh
  have htailkv : HasPeriod θstar ((k : ℤ) • v) :=
    (hasPeriod_translate_iff (y 0) (-(N : ℤ) • d) ((k : ℤ) • v)).mpr (hkv _ (hy 0))
  calc
    G w = y m r := hG
    _ = y 0 (r + (m : ℤ) • d) := by rw [htrack]; rfl
    _ = θstar (r + (n : ℤ) • d) := by
      change y 0 (r + (m : ℤ) • d) = y 0 (r + (n : ℤ) • d + -(N : ℤ) • d)
      rw [add_assoc, ← add_smul]
      have hsum : (n : ℤ) + -(N : ℤ) = (m : ℤ) := by omega
      rw [hsum]
    _ = θstar w := by
      rw [hwrepr', add_right_comm]
      exact (hasPeriod_zsmul θstar ((k : ℤ) • v) htailkv a (r + (n : ℤ) • d)).symm

end ConvexNivat
