import ConvexNivat.Colle.Definitions
import ConvexNivat.CorePeriods

namespace ConvexNivat.Colle
open Filter Topology

/-- The reviewed finite-window definition equals the actual discrete product
topology orbit closure used by all cited sources. -/
theorem orbitClosure_eq_topological_closure {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (ξ : Configuration A) :
    OrbitClosure ξ = closure (Set.range (fun u : Lattice => translate u ξ)) := by
  classical
  ext x
  constructor
  · intro hx
    apply mem_closure_iff_nhds.mpr
    intro U hU
    rw [nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨S, V, hV, hVU⟩ := hU
    obtain ⟨u, hu⟩ := hx S
    refine ⟨translate u ξ, hVU ?_, ⟨u, rfl⟩⟩
    intro z hz
    change ξ (z + u) ∈ V z
    rw [add_comm, ← hu z hz]
    exact mem_of_mem_nhds (hV z)
  · intro hx S
    let U : Set (Configuration A) := (S : Set Lattice).pi (fun z => {x z})
    have hU : U ∈ 𝓝 x := set_pi_mem_nhds S.finite_toSet (fun z _ =>
      (isOpen_discrete _).mem_nhds (Set.mem_singleton _))
    obtain ⟨y, hy, u, rfl⟩ := mem_closure_iff_nhds.mp hx U hU
    refine ⟨u, fun z hz => ?_⟩
    exact (Set.mem_singleton_iff.mp (hy z hz)).symm.trans
      (by simp [translate, add_comm])

theorem orbitClosure_contains_self {A : Type*} (ξ : Configuration A) :
    ξ ∈ OrbitClosure ξ := by
  intro S
  exact ⟨0, fun z _ => by simp⟩

theorem orbitClosure_translate_member {A : Type*} (ξ x : Configuration A)
    (hx : x ∈ OrbitClosure ξ) (u : Lattice) :
    translate u x ∈ OrbitClosure ξ := by
  intro S
  obtain ⟨v, hv⟩ := hx (S.image (fun z => z + u))
  refine ⟨v + u, fun z hz => ?_⟩
  have he := hv (z + u) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  simpa [translate, add_assoc, add_comm, add_left_comm] using he

theorem orbitClosure_translate_eq {A : Type*} (ξ : Configuration A) (u : Lattice) :
    OrbitClosure (translate u ξ) = OrbitClosure ξ := by
  ext x
  constructor
  · intro hx S
    obtain ⟨v, hv⟩ := hx S
    refine ⟨v + u, fun z hz => ?_⟩
    simpa [translate, add_assoc, add_comm, add_left_comm] using hv z hz
  · intro hx S
    obtain ⟨v, hv⟩ := hx S
    refine ⟨v - u, fun z hz => ?_⟩
    change x z = ξ ((v - u + z) + u)
    have he : (v - u + z) + u = v + z := by abel
    rw [he]
    exact hv z hz

theorem orbitClosure_transitive {A : Type*} (ξ x : Configuration A)
    (hx : x ∈ OrbitClosure ξ) : OrbitClosure x ⊆ OrbitClosure ξ := by
  intro y hy S
  obtain ⟨u, hu⟩ := hy S
  obtain ⟨v, hv⟩ := hx (S.image (fun z => u + z))
  refine ⟨v + u, fun z hz => ?_⟩
  rw [hu z hz, add_assoc]
  exact hv _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

theorem orbitClosure_alphabet (ξ x : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hx : x ∈ OrbitClosure ξ) : ∀ z, x z ∈ A := by
  intro z
  obtain ⟨u, hu⟩ := hx {z}
  rw [hu z (by simp)]
  exact hA _

/-- Compactness in the product topology of ℤ^ℤ² comes from the actual finite
alphabet restriction at every coordinate, not compactness of the integer alphabet. -/
theorem orbitClosure_isCompact (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) : IsCompact (OrbitClosure ξ) := by
  have hcomp : IsCompact {x : Configuration ℤ | ∀ z, x z ∈ A} := by
    exact isCompact_pi_infinite (fun _ : Lattice => A.finite_toSet.isCompact)
  apply hcomp.of_isClosed_subset
  · rw [orbitClosure_eq_topological_closure]
    exact isClosed_closure
  · intro x hx z
    exact orbitClosure_alphabet ξ x A hA hx z

theorem orbitClosure_pointwise_subsequence (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (xs : ℕ → Configuration ℤ)
    (hxs : ∀ i, xs i ∈ OrbitClosure ξ) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ x ∈ OrbitClosure ξ,
      PointwiseLimit (fun j => xs (s j)) x := by
  obtain ⟨x, hx, s, hs, hlim⟩ :=
    (orbitClosure_isCompact ξ A hA).tendsto_subseq hxs
  refine ⟨s, hs, x, hx, ?_⟩
  simpa only [PointwiseLimit, tendsto_pi_nhds, nhds_discrete, Filter.tendsto_pure,
    Filter.eventually_atTop, Function.comp_apply] using hlim

theorem orbitClosure_period_inheritance {A : Type*} (ξ x : Configuration A)
    (hx : x ∈ OrbitClosure ξ) (h : Lattice) (hperiod : HasPeriod ξ h) :
    HasPeriod x h := by
  intro z
  obtain ⟨u, hu⟩ := hx {z, z + h}
  rw [hu (z + h) (by simp), hu z (by simp)]
  simpa [add_assoc] using hperiod (u + z)

theorem orbitClosure_annihilator_inheritance (ξ x : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) (φ : IntegerLaurent) (hφ : Annihilates φ ξ) :
    Annihilates φ x := by
  intro z
  obtain ⟨u, hu⟩ := hx (φ.support.image (fun q => z - q))
  change φ.sum (fun q c => c * x (z - q)) = 0
  calc
    _ = φ.sum (fun q c => c * ξ ((u + z) - q)) := by
      apply Finsupp.sum_congr
      intro q hq
      rw [hu _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩), add_sub_assoc]
    _ = 0 := hφ (u + z)

theorem orbitClosure_nontrivial_annihilator (ξ x : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) (hann : HasNontrivialIntegerAnnihilator ξ) :
    HasNontrivialIntegerAnnihilator x := by
  obtain ⟨φ, hφ, hannφ⟩ := hann
  refine ⟨φ, hφ, fun z => ?_⟩
  obtain ⟨u, hu⟩ := hx (φ.support.image (fun q => z + q))
  change φ.sum (fun q c => c * x (z + q)) = 0
  calc
    _ = φ.sum (fun q c => c * ξ ((u + z) + q)) := by
      apply Finsupp.sum_congr
      intro q hq
      rw [hu _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩), add_assoc]
    _ = 0 := hannφ (u + z)

theorem orbitClosure_complexity_le (ξ x : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (S : Finset Lattice) : complexity x S ≤ complexity ξ S := by
  classical
  let encode : Pattern {a : ℤ // a ∈ A} S → Pattern ℤ S := fun p z => (p z).val
  have hfinite : (patternSet ξ S).Finite := by
    apply (Set.finite_range encode).subset
    rintro p ⟨u, rfl⟩
    exact ⟨fun z => ⟨ξ (u + z.val), hA _⟩, rfl⟩
  apply Set.ncard_le_ncard _ hfinite
  rintro p ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := hx (S.image (fun z => u + z))
  refine ⟨v + u, ?_⟩
  funext z
  change ξ ((v + u) + z.val) = x (u + z.val)
  rw [add_assoc]
  exact (hv _ (Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩)).symm

theorem finite_orbitClosure_iff_doublyPeriodic (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) :
    (OrbitClosure ξ).Finite ↔ DoublyPeriodic ξ := by
  classical
  constructor
  · intro hfin
    let := hfin.to_subtype
    have haxis (e : Lattice) : ∃ m : ℤ, m ≠ 0 ∧ HasPeriod ξ (m • e) := by
      let f : ℤ → OrbitClosure ξ := fun i =>
        ⟨translate (i • e) ξ,
          orbitClosure_translate_member ξ ξ (orbitClosure_contains_self ξ) _⟩
      obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
      have heq' : translate (i • e) ξ = translate (j • e) ξ := congrArg Subtype.val heq
      refine ⟨i - j, sub_ne_zero.mpr hij, fun z => ?_⟩
      have hz := congrFun heq' (z - j • e)
      have hleft : z - j • e + i • e = z + (i - j) • e := by
        rw [sub_smul]
        abel
      simpa only [translate, hleft, sub_add_cancel] using hz
    obtain ⟨m, hm, hmx⟩ := haxis (1, 0)
    obtain ⟨k, hk, hky⟩ := haxis (0, 1)
    refine ⟨m • (1, 0), k • (0, 1), ?_, hmx, hky⟩
    simpa [Nonparallel, det, smul_eq_mul] using mul_ne_zero hm hk
  · intro hdouble
    obtain ⟨N, hN, hgrid⟩ := (doublyPeriodic_iff_grid ξ).mp hdouble
    let F : Finset Lattice := (Finset.Ico (0 : ℤ) N).product (Finset.Ico (0 : ℤ) N)
    let f : OrbitClosure ξ → Pattern {a : ℤ // a ∈ A} F :=
      fun x z => ⟨x.val z.val, orbitClosure_alphabet ξ x.val A hA x.property z.val⟩
    have hf : Function.Injective f := by
      intro x y heq
      apply Subtype.ext
      funext z
      let w : Lattice := (z.1 % N, z.2 % N)
      have hNz : 0 < (N : ℤ) := by exact_mod_cast hN
      have hw : w ∈ F := Finset.mem_product.mpr
        ⟨Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (ne_of_gt hNz), Int.emod_lt_of_pos _ hNz⟩,
         Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (ne_of_gt hNz), Int.emod_lt_of_pos _ hNz⟩⟩
      have hz : w + (N : ℤ) • (z.1 / N, z.2 / N) = z := by
        apply Prod.ext
        · change z.1 % (N : ℤ) + (N : ℤ) * (z.1 / (N : ℤ)) = z.1
          simpa [mul_comm] using Int.emod_add_ediv_mul z.1 N
        · change z.2 % (N : ℤ) + (N : ℤ) * (z.2 / (N : ℤ)) = z.2
          simpa [mul_comm] using Int.emod_add_ediv_mul z.2 N
      have hpx := orbitClosure_period_inheritance ξ x.val x.property _
        (hgrid (z.1 / N, z.2 / N)) w
      have hpy := orbitClosure_period_inheritance ξ y.val y.property _
        (hgrid (z.1 / N, z.2 / N)) w
      rw [hz] at hpx hpy
      exact hpx.trans ((congrArg Subtype.val (congrFun heq ⟨w, hw⟩)).trans hpy.symm)
    let := Finite.of_injective f hf
    exact Set.toFinite _

/-- Inheritance uses actual witness fields and transitivity of orbit closure. -/
theorem oneSidedNonexpansive_inheritance (ξ x : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) (n : RealPlane) (hn : OneSidedNonexpansive x n) :
    OneSidedNonexpansive ξ n := by
  obtain ⟨hn0, y, hy, z, hz, hyz, hag⟩ := hn
  exact ⟨hn0, y, orbitClosure_transitive ξ x hx hy,
    z, orbitClosure_transitive ξ x hx hz, hyz, hag⟩

theorem nonexpansiveLine_inheritance (ξ x : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) (n : RealPlane) (hn : NonexpansiveLine x n) :
    NonexpansiveLine ξ n := by
  refine ⟨hn.1, fun width hw => ?_⟩
  obtain ⟨y, hy, z, hz, hyz, hag⟩ := hn.2 width hw
  exact ⟨y, orbitClosure_transitive ξ x hx hy,
    z, orbitClosure_transitive ξ x hx hz, hyz, hag⟩

theorem oneSidedNonexpansive_implies_band (ξ : Configuration ℤ) (n : RealPlane)
    (hn : OneSidedNonexpansive ξ n) : NonexpansiveLine ξ n := by
  obtain ⟨hn0, x, hx, y, hy, hne, hag⟩ := hn
  refine ⟨hn0, fun width hw => ?_⟩
  have hcoord : n.1 ≠ 0 ∨ n.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hn0 (Prod.ext hc.1 hc.2)
  have hlarge (a : ℝ) (ha : a ≠ 0) : ∃ k : ℤ, width ≤ (k : ℝ) * a := by
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · obtain ⟨k, hk⟩ := exists_int_lt (width / a)
      exact ⟨k, ((lt_div_iff_of_neg hneg).mp hk).le⟩
    · obtain ⟨k, hk⟩ := exists_int_gt (width / a)
      exact ⟨k, ((div_lt_iff₀ hpos).mp hk).le⟩
  have hu : ∃ u : Lattice, width ≤ realDot (embed u) n := by
    rcases hcoord with h1 | h2
    · obtain ⟨k, hk⟩ := hlarge n.1 h1
      exact ⟨(k, 0), by simpa [embed, realDot] using hk⟩
    · obtain ⟨k, hk⟩ := hlarge n.2 h2
      exact ⟨(0, k), by simpa [embed, realDot] using hk⟩
  obtain ⟨u, hu⟩ := hu
  refine ⟨translate u x, orbitClosure_translate_member ξ x hx u,
    translate u y, orbitClosure_translate_member ξ y hy u, ?_, ?_⟩
  · intro heq
    apply hne
    funext z
    have he := congrFun heq (z - u)
    simpa [translate] using he
  · intro z hz
    change |realDot (embed z) n| ≤ width at hz
    apply hag
    change 0 ≤ realDot (embed (z + u)) n
    have he : realDot (embed (z + u)) n = realDot (embed z) n + realDot (embed u) n := by
      simp [embed, realDot, Int.cast_add]; ring
    rw [he]
    have hz' := (abs_le.mp hz).1
    linarith

theorem oneSidedNonexpansive_positive_scale (ξ : Configuration ℤ) (n : RealPlane)
    (t : ℝ) (ht : 0 < t) :
    OneSidedNonexpansive ξ (t • n) ↔ OneSidedNonexpansive ξ n := by
  have hhalf : {z : Lattice | 0 ≤ realDot (embed z) (t • n)} =
      {z : Lattice | 0 ≤ realDot (embed z) n} := by
    ext z
    change (0 ≤ realDot (embed z) (t • n)) ↔ (0 ≤ realDot (embed z) n)
    have he : realDot (embed z) (t • n) = t * realDot (embed z) n := by
      simp [realDot, smul_eq_mul]; ring
    rw [he]
    exact mul_nonneg_iff_of_pos_left ht
  have hzero : t • n ≠ 0 ↔ n ≠ 0 := by
    rw [smul_ne_zero_iff]
    simp [ne_of_gt ht]
  simp only [OneSidedNonexpansive, hhalf, hzero]

theorem oneSidedNonexpansive_period_tangent (ξ : Configuration ℤ) (n : RealPlane)
    (hn : OneSidedNonexpansive ξ n) (h : Lattice) (hperiod : HasPeriod ξ h) :
    realDot (embed h) n = 0 := by
  obtain ⟨hn0, x, hx, y, hy, hne, hag⟩ := hn
  by_contra ha
  apply hne
  funext z
  have hpX : Function.Periodic x h := orbitClosure_period_inheritance ξ x hx h hperiod
  have hpY : Function.Periodic y h := orbitClosure_period_inheritance ξ y hy h hperiod
  have hshift : ∃ k : ℤ, 0 ≤ realDot (embed (z + k • h)) n := by
    let a := realDot (embed h) n
    let b := realDot (embed z) n
    have hd (k : ℤ) : realDot (embed (z + k • h)) n = b + (k : ℝ) * a := by
      simp [a, b, embed, realDot, Int.cast_add, Int.cast_mul]; ring
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · obtain ⟨k, hk⟩ := exists_int_lt (-b / a)
      refine ⟨k, ?_⟩
      rw [hd]
      have hm := (lt_div_iff_of_neg hneg).mp hk
      linarith
    · obtain ⟨k, hk⟩ := exists_int_gt (-b / a)
      refine ⟨k, ?_⟩
      rw [hd]
      have hm := (div_lt_iff₀ hpos).mp hk
      linarith
  obtain ⟨k, hk⟩ := hshift
  exact (hpX.zsmul k z).symm.trans ((hag _ hk).trans (hpY.zsmul k z))

theorem nonexpansiveLine_period_tangent (ξ : Configuration ℤ) (n : RealPlane)
    (hn : NonexpansiveLine ξ n) (h : Lattice) (hperiod : HasPeriod ξ h) :
    realDot (embed h) n = 0 := by
  by_contra ha
  let a := realDot (embed h) n
  obtain ⟨x, hx, y, hy, hne, hag⟩ := hn.2 |a| (abs_pos.mpr ha)
  apply hne
  funext z
  have hpX : Function.Periodic x h := orbitClosure_period_inheritance ξ x hx h hperiod
  have hpY : Function.Periodic y h := orbitClosure_period_inheritance ξ y hy h hperiod
  let b := realDot (embed z) n
  let k : ℤ := -Int.floor (b / a)
  have hd : realDot (embed (z + k • h)) n = (b / a - Int.floor (b / a)) * a := by
    have ha' : a ≠ 0 := ha
    calc
      _ = b + (k : ℝ) * a := by
        simp [a, b, embed, realDot, Int.cast_add, Int.cast_mul]
        ring
      _ = b - (Int.floor (b / a) : ℝ) * a := by simp [k]; ring
      _ = _ := by rw [sub_mul, div_mul_cancel₀ b ha']
  have hbnd : |realDot (embed (z + k • h)) n| ≤ |a| := by
    rw [hd, abs_mul]
    have hf : |b / a - (Int.floor (b / a) : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
      linarith [Int.lt_floor_add_one (b / a)]
    simpa using mul_le_mul_of_nonneg_right hf (abs_nonneg a)
  exact (hpX.zsmul k z).symm.trans ((hag _ hbnd).trans (hpY.zsmul k z))

theorem two_nonexpansive_lines_nonperiodic (ξ : Configuration ℤ) (n n' : RealPlane)
    (hn : NonexpansiveLine ξ n) (hn' : NonexpansiveLine ξ n')
    (hindependent : realDet n n' ≠ 0) : ¬ Periodic ξ := by
  rintro ⟨h, hh, hp⟩
  have ha := nonexpansiveLine_period_tangent ξ n hn h hp
  have hb := nonexpansiveLine_period_tangent ξ n' hn' h hp
  have hd := hindependent
  unfold realDot embed at ha hb
  unfold realDet at hd
  have hz1 : (h.1 : ℝ) * (n.1 * n'.2 - n.2 * n'.1) = 0 := by
    linear_combination n'.2 * ha - n.2 * hb
  have hz2 : (h.2 : ℝ) * (n.1 * n'.2 - n.2 * n'.1) = 0 := by
    linear_combination n.1 * hb - n'.1 * ha
  have h1 : h.1 = 0 := by exact_mod_cast (mul_eq_zero.mp hz1).resolve_right hd
  have h2 : h.2 = 0 := by exact_mod_cast (mul_eq_zero.mp hz2).resolve_right hd
  apply hh
  exact Prod.ext h1 h2

/-- The source's closure can always supply an accumulation point along a
nonzero ray, with actual finite-window convergence and strict subsequence. -/
theorem ray_translate_accumulation (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (v : Lattice) :
    ∃ x ∈ OrbitClosure ξ, SubsequentialTranslateLimit ξ v x := by
  obtain ⟨s, hs, x, hx, hlim⟩ := orbitClosure_pointwise_subsequence ξ A hA
    (fun j => translate ((j : ℤ) • v) ξ)
    (fun j => orbitClosure_translate_member ξ ξ (orbitClosure_contains_self ξ) _)
  exact ⟨x, hx, s, hs, hlim⟩

end ConvexNivat.Colle
