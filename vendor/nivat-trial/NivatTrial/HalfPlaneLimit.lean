import NivatTrial.PeriodicSubshift
import NivatTrial.Periodicity
import NivatTrial.Divisibility
import Mathlib.Dynamics.OmegaLimit

/-! The propagation argument of Lemma 8.16. A finite fundamental domain
turns fields with one fixed period into one-dimensional block sequences. -/

namespace NivatTrial.HalfPlaneLimit

open Set Filter Topology Function
open NivatTrial.Geometry NivatTrial.Periodicity
open scoped Classical

abbrev G := ℤ × ℤ

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]

def translationFlow (d : G) : Flow ℤ (G → A) where
  toFun n y := Dynamics.shift (n • d) y
  cont' := continuous_prod_of_discrete_left.mpr
    (fun n => Dynamics.continuous_shift (n • d))
  map_add' m n y := by rw [add_smul, Dynamics.shift_add]
  map_zero' y := by simp

def limitSet (x : G → A) (d : G) : Set (G → A) :=
  omegaLimit (atTop : Filter ℤ) (translationFlow d) {x}

theorem map_natCast_atTop : Filter.map (fun n : ℕ => (n : ℤ)) atTop = atTop := by
  rw [← Nat.comap_cast_atTop (R := ℤ)]
  apply map_comap_of_mem
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
  exact ⟨n.toNat, Int.toNat_of_nonneg hn⟩

theorem mem_limitSet_iff (x y : G → A) (d : G) : y ∈ limitSet x d ↔
    MapClusterPt y atTop (fun n : ℕ => Dynamics.shift (n • d) x) := by
  rw [limitSet, mem_omegaLimit_singleton_iff_mapClusterPt]
  change ClusterPt y (Filter.map (fun n : ℤ => Dynamics.shift (n • d) x) atTop) ↔
    ClusterPt y (Filter.map (fun n : ℕ => Dynamics.shift (n • d) x) atTop)
  rw [← map_natCast_atTop, Filter.map_map]
  rfl

theorem isClosed_limitSet (x : G → A) (d : G) : IsClosed (limitSet x d) :=
  isClosed_omegaLimit _ _ _

theorem shift_limitSet (x : G → A) (d : G) (n : ℤ) :
    Dynamics.shift (n • d) '' limitSet x d = limitSet x d := by
  have hi := Flow.isInvariant_omegaLimit atTop (translationFlow d) {x}
    (fun n => by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop (b - n)] with m hm
      omega)
  exact ((Flow.isInvariant_iff_image_eq (translationFlow d) (limitSet x d)).mp hi) n

theorem limitSet_subset_orbitClosure (x : G → A) (d : G) :
    limitSet x d ⊆ Dynamics.orbitClosure x := by
  apply (omegaLimit_subset_closure_image2 atTop (translationFlow d) {x} univ_mem).trans
  apply closure_mono
  rintro y ⟨n, _, z, hz, rfl⟩
  have hz' : z = x := Set.mem_singleton_iff.mp hz
  rw [hz']
  exact Dynamics.shift_mem_orbit x (n • d)

def blockSequence (D : Set G) (d : G) (y : G → A) : ℤ → D → A :=
  fun n r => y ((r : G) + n • d)

theorem continuous_blockSequence (D : Set G) (d : G) :
    Continuous (blockSequence D d : (G → A) → ℤ → D → A) := by
  apply continuous_pi
  intro n
  apply continuous_pi
  intro r
  exact continuous_apply _

theorem blockSequence_shift (D : Set G) (d : G) (y : G → A) (n : ℤ) :
    blockSequence D d (Dynamics.shift (n • d) y) =
      PeriodicSubshift.shift n (blockSequence D d y) := by
  funext i r
  simp only [blockSequence, Dynamics.shift, PeriodicSubshift.shift, add_smul]
  congr 1
  abel

theorem blockSequence_injective (h d : G) (hdet : det h d ≠ 0)
    {x y : G → A} (hx : IsPeriod x h) (hy : IsPeriod y h)
    (heq : blockSequence (Divisibility.fundamentalDomain h d) d x =
      blockSequence (Divisibility.fundamentalDomain h d) d y) : x = y := by
  funext z
  obtain ⟨r, m, n, hr⟩ := Divisibility.fundamentalDomain_representatives h d hdet z
  have hblock := congrFun (congrFun heq n) r
  rw [hr]
  calc
    x ((r : G) + m • h + n • d) = x ((r : G) + n • d) := by
      simpa only [add_assoc, add_comm, add_left_comm] using hx.zsmul m ((r : G) + n • d)
    _ = y ((r : G) + n • d) := hblock
    _ = y ((r : G) + m • h + n • d) := by
      symm
      simpa only [add_assoc, add_comm, add_left_comm] using hy.zsmul m ((r : G) + n • d)

theorem blockSequence_periodic (D : Set G) (d : G) {y : G → A}
    (hy : IsDoublyPeriodic y) : PeriodicSubshift.PeriodicPoint (blockSequence D d y) := by
  obtain ⟨q, hq, hhor, hver⟩ := rectangular_periods_of_doublyPeriodic hy
  have hp := period_in_scaled_direction y q d hhor hver
  refine ⟨q, hq, ?_⟩
  intro n
  funext r
  simpa only [blockSequence, add_smul, natCast_zsmul, add_assoc] using hp ((r : G) + n • d)

theorem finite_compact_periodic_fields (Ω : Set (G → A)) (hcompact : IsCompact Ω)
    (h d : G) (hdet : det h d ≠ 0)
    (hshift : ∀ n : ℤ, Dynamics.shift (n • d) '' Ω = Ω)
    (hfixed : ∀ y ∈ Ω, IsPeriod y h) (hdoubly : ∀ y ∈ Ω, IsDoublyPeriodic y) :
    Ω.Finite := by
  let D := Divisibility.fundamentalDomain h d
  let := (Divisibility.fundamentalDomain_finite h d hdet).fintype
  let E : (G → A) → ℤ → D → A := blockSequence D d
  have hc : IsCompact (E '' Ω) := hcompact.image (continuous_blockSequence D d)
  have hs (n : ℤ) : PeriodicSubshift.shift n '' (E '' Ω) = E '' Ω := by
    rw [Set.image_image]
    change (PeriodicSubshift.shift n ∘ E) '' Ω = E '' Ω
    have heq : PeriodicSubshift.shift n ∘ E = E ∘ Dynamics.shift (n • d) := by
      funext y
      exact (blockSequence_shift D d y n).symm
    rw [heq]
    calc
      (E ∘ Dynamics.shift (n • d)) '' Ω = E '' (Dynamics.shift (n • d) '' Ω) :=
        (Set.image_image E (Dynamics.shift (n • d)) Ω).symm
      _ = E '' Ω := by rw [hshift n]
  have hp : ∀ b ∈ E '' Ω, PeriodicSubshift.PeriodicPoint b := by
    rintro b ⟨y, hy, rfl⟩
    exact blockSequence_periodic D d (hdoubly y hy)
  have hf := PeriodicSubshift.finite_of_compact_periodic (E '' Ω) hc hs hp
  apply hf.of_finite_image
  intro x hx y hy heq
  exact blockSequence_injective h d hdet (hfixed x hx) (hfixed y hy) heq

section FiniteAlphabet

variable [Finite A]

theorem finite_limitSet (x : G → A) (h d : G) (hdet : det h d ≠ 0)
    (hx : IsPeriod x h)
    (hall : ∀ y, MapClusterPt y atTop (fun n : ℕ => Dynamics.shift (n • d) x) →
      IsDoublyPeriodic y) : (limitSet x d).Finite := by
  apply finite_compact_periodic_fields (limitSet x d) (isClosed_limitSet x d).isCompact
    h d hdet (shift_limitSet x d)
  · intro y hy
    exact hx.orbitClosure (limitSet_subset_orbitClosure x d hy)
  · intro y hy
    exact hall y ((mem_limitSet_iff x y d).mp hy)

theorem eventually_block_match (x : G → A) (d : G) (D : Set G) (hfinite : D.Finite)
    (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ y ∈ limitSet x d,
      ∀ i : ℤ, -(q : ℤ) ≤ i → i ≤ q →
        blockSequence D d (Dynamics.shift (n • d) x) i = blockSequence D d y i := by
  let := hfinite.fintype
  let U : Set (G → A) := ⋃ y ∈ limitSet x d,
    (blockSequence D d) ⁻¹' PeriodicSubshift.intervalCylinder (blockSequence D d y) q
  have hopen : IsOpen U := by
    apply isOpen_iUnion
    intro y
    apply isOpen_iUnion
    intro hy
    exact (PeriodicSubshift.isOpen_intervalCylinder _ _).preimage
      (continuous_blockSequence D d)
  have hsub : limitSet x d ⊆ U := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, fun _ _ _ => rfl⟩⟩
  have hev := eventually_mapsTo_of_isOpen_of_omegaLimit_subset
    (atTop : Filter ℤ) (translationFlow d) {x} hopen hsub
  have he : ∀ᶠ n : ℤ in atTop, Dynamics.shift (n • d) x ∈ U :=
    hev.mono (fun n hn => hn (Set.mem_singleton x))
  filter_upwards [he.natCast_atTop] with n hn
  rcases Set.mem_iUnion.mp hn with ⟨y, hn⟩
  rcases Set.mem_iUnion.mp hn with ⟨hy, hn⟩
  exact ⟨y, hy, hn⟩

/-- After a fixed number of translations, the entire positive block tail is
exactly the positive tail of a single limit configuration. -/
theorem block_tail_agreement (x : G → A) (h d : G) (hdet : det h d ≠ 0)
    (hx : IsPeriod x h)
    (hall : ∀ y, MapClusterPt y atTop (fun n : ℕ => Dynamics.shift (n • d) x) →
      IsDoublyPeriodic y) :
    ∃ N : ℕ, ∃ y ∈ limitSet x d,
      ∀ n : ℤ, (N : ℤ) ≤ n → ∀ r : Divisibility.fundamentalDomain h d,
        x ((r : G) + n • d) = y ((r : G) + (n - N) • d) := by
  let Ω := limitSet x d
  let D := Divisibility.fundamentalDomain h d
  let E : (G → A) → ℤ → D → A := blockSequence D d
  have hfinite : Ω.Finite := finite_limitSet x h d hdet hx hall
  let := hfinite.fintype
  have hdp : ∀ y : Ω, IsDoublyPeriodic (y : G → A) :=
    fun y => hall y ((mem_limitSet_iff x y d).mp y.property)
  obtain ⟨q, hq, hrect⟩ := common_rectangular_periods (fun y : Ω => (y : G → A)) hdp
  have hqd (y : G → A) (hy : y ∈ Ω) : IsPeriod y (q • d) :=
    period_in_scaled_direction y q d (hrect ⟨y, hy⟩).1 (hrect ⟨y, hy⟩).2
  have hqp (y : G → A) (hy : y ∈ Ω) : Function.Periodic (E y) (q : ℤ) := by
    intro n
    funext r
    simpa only [E, blockSequence, add_smul, natCast_zsmul, add_assoc] using
      hqd y hy ((r : G) + n • d)
  have hfixed (y : G → A) (hy : y ∈ Ω) : IsPeriod y h :=
    hx.orbitClosure (limitSet_subset_orbitClosure x d hy)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_block_match x d D (Divisibility.fundamentalDomain_finite h d hdet) q)
  have hex (m : ℕ) : ∃ y ∈ Ω, ∀ i : ℤ, -(q : ℤ) ≤ i → i ≤ q →
      E (Dynamics.shift ((N + m) • d) x) i = E y i := hN (N + m) (by omega)
  choose Y hY hagree using hex
  have hstep (m : ℕ) : Y (m + 1) = Dynamics.shift d (Y m) := by
    apply blockSequence_injective h d hdet (hfixed _ (hY (m + 1)))
      ((hfixed _ (hY m)).shift d)
    apply PeriodicSubshift.periodic_determined _ _ q hq (hqp _ (hY (m + 1)))
    · intro i
      funext r
      simpa only [blockSequence, add_smul, natCast_zsmul, add_assoc] using
        (hqd (Y m) (hY m)).shift d ((r : G) + i • d)
    · intro i hi0 hiq
      funext r
      have ha := congrFun (hagree (m + 1) i (by omega) (by omega)) r
      have hb := congrFun (hagree m (i + 1) (by omega) (by omega)) r
      calc
        E (Y (m + 1)) i r = E (Dynamics.shift ((N + (m + 1)) • d) x) i r := ha.symm
        _ = E (Dynamics.shift ((N + m) • d) x) (i + 1) r := by
          simp only [E, blockSequence, Dynamics.shift, Nat.cast_add, Nat.cast_one,
            natCast_zsmul, add_smul, one_smul]
          congr 1
          abel
        _ = E (Y m) (i + 1) r := hb
        _ = E (Dynamics.shift d (Y m)) i r := by
          simp only [E, blockSequence, Dynamics.shift, add_smul, one_smul]
          congr 1
          abel
  have hiterate (m : ℕ) : Y m = Dynamics.shift (m • d) (Y 0) := by
    induction m with
    | zero => simp
    | succ m hm =>
      rw [hstep, hm, ← Dynamics.shift_add]
      congr 1
      simp [add_smul, add_comm]
  refine ⟨N, Y 0, hY 0, ?_⟩
  intro n hn r
  let m := (n - N).toNat
  have hm : (m : ℤ) = n - N := Int.toNat_of_nonneg (by omega)
  have hnm : n = ((N + m : ℕ) : ℤ) := by omega
  have ha := congrFun (hagree m 0 (by omega) (by omega)) r
  rw [hiterate m] at ha
  change x (((N + m : ℕ) : ℤ) • d + ((r : G) + (0 : ℤ) • d)) =
    Y 0 ((m : ℤ) • d + ((r : G) + (0 : ℤ) • d)) at ha
  rw [← hnm, hm] at ha
  simpa only [zero_smul, add_zero, add_comm] using ha

/-- Propagation to an actual determinant half-plane. The proof only uses
the independence supplied by `det v d < 0`, so no primitive-basis assumption
is needed here. -/
theorem tail_agreement (x : G → A) (v d : G) (k : ℕ) (hk : 0 < k)
    (hx : IsPeriod x (k • v)) (hd : det v d < 0)
    (hall : ∀ y, MapClusterPt y atTop (fun n : ℕ => Dynamics.shift (n • d) x) →
      IsDoublyPeriodic y) :
    ∃ β : ℤ, ∃ θ : G → A, IsDoublyPeriodic θ ∧
      ∀ z : G, det v z ≤ β → x z = θ z := by
  have hdet : det (k • v) d ≠ 0 := by
    change det ((k : ℤ) • v) d ≠ 0
    rw [det_zsmul_left]
    exact mul_ne_zero (by omega) (ne_of_lt hd)
  let D := Divisibility.fundamentalDomain (k • v) d
  let := (Divisibility.fundamentalDomain_finite (k • v) d hdet).fintype
  let M : ℤ := ∑ r : D, |det v (r : G)|
  have hbound (r : D) : -M ≤ det v (r : G) := by
    have hs : |det v (r : G)| ≤ M :=
      Finset.single_le_sum (fun (s : D) _ => abs_nonneg (det v (s : G))) (Finset.mem_univ r)
    have := neg_le_abs (det v (r : G))
    omega
  obtain ⟨N, y, hy, htail⟩ := block_tail_agreement x (k • v) d hdet hx hall
  let θ := Dynamics.shift (-(N • d)) y
  have hyp : IsPeriod y (k • v) :=
    hx.orbitClosure (limitSet_subset_orbitClosure x d hy)
  have hθp : IsPeriod θ (k • v) := hyp.shift _
  refine ⟨-M + (N : ℤ) * det v d, θ,
    (hall y ((mem_limitSet_iff x y d).mp hy)).shift _, ?_⟩
  intro z hz
  obtain ⟨r, m, n, hr⟩ := Divisibility.fundamentalDomain_representatives (k • v) d hdet z
  have hheight : det v z = det v (r : G) + n * det v d := by
    rw [hr]
    simp only [det_add_right, det_zsmul_right, det_nsmul_right,
      det_self, mul_zero, add_zero]
  have hn : (N : ℤ) ≤ n := by
    have hb := hbound r
    nlinarith
  rw [hr]
  calc
    x ((r : G) + m • (k • v) + n • d) = x ((r : G) + n • d) := by
      simpa only [add_assoc, add_comm, add_left_comm] using hx.zsmul m ((r : G) + n • d)
    _ = y ((r : G) + (n - N) • d) := htail n hn r
    _ = θ ((r : G) + n • d) := by
      dsimp [θ, Dynamics.shift]
      congr 1
      change (r : G) + (n - N) • d = -((N : ℤ) • d) + ((r : G) + n • d)
      rw [sub_smul]
      abel
    _ = θ ((r : G) + m • (k • v) + n • d) := by
      symm
      simpa only [add_assoc, add_comm, add_left_comm] using
        hθp.zsmul m ((r : G) + n • d)

/-- The same statement with the paper's convergent subsequence hypothesis.
First countability identifies subsequential limits with filter cluster points. -/
theorem tail_agreement_of_subsequential_limits (x : G → A) (v d : G)
    (k : ℕ) (hk : 0 < k) (hx : IsPeriod x (k • v)) (hd : det v d < 0)
    (hall : ∀ (y : G → A) (φ : ℕ → ℕ), StrictMono φ →
      Tendsto (fun n => Dynamics.shift (φ n • d) x) atTop (𝓝 y) → IsDoublyPeriodic y) :
    ∃ β : ℤ, ∃ θ : G → A, IsDoublyPeriodic θ ∧
      ∀ z : G, det v z ≤ β → x z = θ z := by
  apply tail_agreement x v d k hk hx hd
  intro y hy
  obtain ⟨φ, hφ, hlim⟩ := hy.tendsto_subseq
  exact hall y φ hφ hlim

end FiniteAlphabet

end NivatTrial.HalfPlaneLimit
