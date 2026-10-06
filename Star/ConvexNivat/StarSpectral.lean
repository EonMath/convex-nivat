import Mathlib
import ConvexNivat.Core
import ConvexNivat.CorePeriods
import ConvexNivat.CoreLattice
import ConvexNivat.CorePatterns
import ConvexNivat.SpectralFourier
import ConvexNivat.IntegerEncoding

open scoped BigOperators

namespace ConvexNivat

noncomputable section

/-- An admissible choice of the common tangential periods of source §0.3.
Only actual period conditions are bundled; no spectral conclusions are fields. -/
structure StarCommonPeriods {p : ℕ} (star : StarData p) where
  multiplier : Fin star.m → ℕ
  positive : ∀ i, 0 < multiplier i
  component_period : ∀ i, HasPeriod (star.component i).field
    ((multiplier i : ℤ) • (star.component i).direction)
  left_period : ∀ i j, HasPeriod (star.component j).leftTail
    ((multiplier i : ℤ) • (star.component i).direction)
  right_period : ∀ i j, HasPeriod (star.component j).rightTail
    ((multiplier i : ℤ) • (star.component i).direction)

/-- The common-period construction in §0.3 is itself an explicit obligation. -/
theorem star_common_periods_exist {p : ℕ} (star : StarData p) :
    Nonempty (StarCommonPeriods star) := by
  classical
  have ht : ∀ j : Fin star.m, ∃ N : ℕ, 0 < N ∧ ∀ z : Lattice,
      HasPeriod (star.component j).leftTail ((N : ℤ) • z) ∧
      HasPeriod (star.component j).rightTail ((N : ℤ) • z) := by
    intro j
    obtain ⟨L, hL, hpL⟩ := (doublyPeriodic_iff_grid _).mp
      (star.component j).left_doubly_periodic
    obtain ⟨R, hR, hpR⟩ := (doublyPeriodic_iff_grid _).mp
      (star.component j).right_doubly_periodic
    refine ⟨L * R, Nat.mul_pos hL hR, fun z => ⟨?_, ?_⟩⟩
    · simpa only [Nat.cast_mul, smul_smul] using hpL ((R : ℤ) • z)
    · simpa only [Nat.cast_mul, mul_comm L R, smul_smul] using hpR ((L : ℤ) • z)
  choose n hn hp using ht
  let N := ∏ j, n j
  have hN : 0 < N := Finset.prod_pos (fun j _ => hn j)
  have hpN : ∀ z : Lattice, ∀ j,
      HasPeriod (star.component j).leftTail ((N : ℤ) • z) ∧
      HasPeriod (star.component j).rightTail ((N : ℤ) • z) := by
    intro z j
    have h := hp j (((∏ k ∈ Finset.univ.erase j, n k) : ℤ) • z)
    simpa only [N, ← Finset.mul_prod_erase _ n (Finset.mem_univ j),
      Nat.cast_mul, Nat.cast_prod, smul_smul] using h
  choose k hk hpk using fun i => (star.component i).tangential_period
  have hkpos : ∀ i, 0 < (k i).toNat := by intro i; have := hk i; omega
  refine ⟨{ multiplier := fun i => N * (k i).toNat
            positive := fun i => Nat.mul_pos hN (hkpos i)
            component_period := ?_
            left_period := ?_
            right_period := ?_ }⟩
  · intro i
    simpa only [Nat.cast_mul, Int.toNat_of_nonneg (by have := hk i; omega : 0 ≤ k i),
      smul_smul] using hasPeriod_zsmul _ _ (hpk i) (N : ℤ)
  · intro i j
    simpa only [Nat.cast_mul, smul_smul] using
      (hpN (((k i).toNat : ℤ) • (star.component i).direction) j).1
  · intro i j
    simpa only [Nat.cast_mul, smul_smul] using
      (hpN (((k i).toNat : ℤ) • (star.component i).direction) j).2

/-- Choose actual admissible periods, using the §0.3 existence obligation. -/
def chooseStarCommonPeriods {p : ℕ} (star : StarData p) :
    StarCommonPeriods star := Classical.choice (star_common_periods_exist star)

def StarCommonPeriods.vector {p : ℕ} {star : StarData p}
    (periods : StarCommonPeriods star) (i : Fin star.m) : Lattice :=
  (periods.multiplier i : ℤ) • (star.component i).direction

inductive RayOrientation
  | positive
  | negative
  deriving DecidableEq

def RayOrientation.sign : RayOrientation → ℤ
  | .positive => 1
  | .negative => -1

inductive TailSide
  | left
  | right
  deriving DecidableEq

def componentTail {p : ℕ} (star : StarData p) (i : Fin star.m)
    (side : TailSide) : Configuration (ZMod p) :=
  match side with
  | .left => (star.component i).leftTail
  | .right => (star.component i).rightTail

/-- Formula (2.0): the actual tail of component j selected by the ray σvᵢ. -/
def rayTail {p : ℕ} (star : StarData p) (i j : Fin star.m)
    (σ : RayOrientation) : Configuration (ZMod p) :=
  if 0 < σ.sign * det (star.component j).direction (star.component i).direction
  then (star.component j).rightTail else (star.component j).leftTail

/-- Bᵢ^σ is the sum of tails of every component other than i. -/
def rayBackground {p : ℕ} (star : StarData p) (i : Fin star.m)
    (σ : RayOrientation) : Configuration (ZMod p) :=
  fun z => ∑ j ∈ Finset.univ.erase i, rayTail star i j σ z

/-- The actual isolating configuration Ξᵢ^σ, not an abstract orbit-closure witness. -/
def isolatingConfiguration {p : ℕ} (star : StarData p) (i : Fin star.m)
    (σ : RayOrientation) : Configuration (ZMod p) :=
  (star.component i).field + rayBackground star i σ

/-- The pure left or right background Gᵢ^{σ,ε}. -/
def pureRayBackground {p : ℕ} (star : StarData p) (i : Fin star.m)
    (σ : RayOrientation) (side : TailSide) : Configuration (ZMod p) :=
  componentTail star i side + rayBackground star i σ

/-- Source colour indicators take characteristic-zero values. -/
def colorIndicator {p : ℕ} (χ : Configuration (ZMod p)) (a : ZMod p) :
    Configuration ℂ := fun z => if χ z = a then 1 else 0

/-- The exceptional colour-difference fields dᵢ,σ,ε,a. -/
def exceptionalDifference {p : ℕ} (star : StarData p) (i : Fin star.m)
    (σ : RayOrientation) (side : TailSide) (a : ZMod p) : Configuration ℂ :=
  colorIndicator (isolatingConfiguration star i σ) a -
    colorIndicator (pureRayBackground star i σ side) a

/-- Λᵢ consists exactly of roots occurring in some actual exceptional field. -/
def exceptionalSpectrum {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) : Finset ℂ :=
  @Finset.filter ℂ (fun ζ => ∃ σ side a,
      spectralOccurs (star.component i).direction (periods.multiplier i) ζ
        (exceptionalDifference star i σ side a)) (Classical.decPred _)
    (rootSpectrum (periods.multiplier i))

/-- The exceptional univariate polynomial Aᵢ of formula (2.1). -/
def exceptionalUnivariate {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) : Polynomial ℂ :=
  ∏ ζ ∈ exceptionalSpectrum star periods i, (Polynomial.X - Polynomial.C ζ)

/-- The scalar difference after an actual integer colour encoding. -/
def encodedExceptionalDifference {p : ℕ} (star : StarData p) (i : Fin star.m)
    (σ : RayOrientation) (side : TailSide) (w : ZMod p → ℤ) : Configuration ℂ :=
  fun z => (w (isolatingConfiguration star i σ z) : ℂ) -
    (w (pureRayBackground star i σ side z) : ℂ)

/-- Both parts of source Lemma 2.2's conclusion, separated from existence. -/
def SpectrumPreservingEncoding {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (w : ZMod p → ℤ) : Prop :=
  Function.Injective w ∧ ∀ i ζ, ζ ∈ exceptionalSpectrum star periods i →
    ∃ σ side, spectralOccurs (star.component i).direction (periods.multiplier i) ζ
      (encodedExceptionalDifference star i σ side w)

/-- §2.1: the source limits along either ray are eventual finite-window
stabilisation to the actual isolating configuration. -/
theorem isolating_configuration_finite_stabilisation {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation)
    (W : Finset Lattice) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z ∈ W,
      star.configuration (z + ((n : ℤ) * σ.sign) • periods.vector i) =
        isolatingConfiguration star i σ z := by
  classical
  let K : Fin star.m × Lattice → ℕ := fun q =>
    ((star.component q.1).upper - height (star.component q.1).direction q.2).natAbs +
    (height (star.component q.1).direction q.2 - (star.component q.1).lower).natAbs + 1
  refine ⟨(Finset.univ.product W).sup K, ?_⟩
  intro n hn z hz
  let q : Lattice := ((n : ℤ) * σ.sign) • periods.vector i
  have hown : (star.component i).field (z + q) = (star.component i).field z :=
    hasPeriod_zsmul _ _ (periods.component_period i) ((n : ℤ) * σ.sign) z
  have ht : ∀ j : Fin star.m, j ≠ i →
      (star.component j).field (z + q) = rayTail star i j σ z := by
    intro j hji
    have hK : K (j, z) ≤ n := (Finset.le_sup
      (s := Finset.univ.product W) (f := K)
      (Finset.mem_product.mpr ⟨Finset.mem_univ j, hz⟩)).trans hn
    have hna : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have hκ : (0 : ℤ) < periods.multiplier i := by exact_mod_cast periods.positive i
    have hheight : height (star.component j).direction (z + q) =
        height (star.component j).direction z +
          (n : ℤ) * (periods.multiplier i : ℤ) *
            (σ.sign * det (star.component j).direction (star.component i).direction) := by
      dsimp [q, StarCommonPeriods.vector]
      rw [height_add, height_zsmul, height_zsmul]
      dsimp [height]
      ring
    have hdet : σ.sign * det (star.component j).direction (star.component i).direction ≠ 0 := by
      apply mul_ne_zero
      · cases σ <;> simp [RayOrientation.sign]
      · exact star.pairwise_nonparallel j i hji
    have hupper := Int.le_natAbs (a := (star.component j).upper -
      height (star.component j).direction z)
    have hlower := Int.le_natAbs (a := height (star.component j).direction z -
      (star.component j).lower)
    have hK' : (K (j, z) : ℤ) ≤ n := by exact_mod_cast hK
    dsimp [K] at hK'
    have hupper0 := Int.natCast_nonneg
      ((star.component j).upper - height (star.component j).direction z).natAbs
    have hlower0 := Int.natCast_nonneg
      (height (star.component j).direction z - (star.component j).lower).natAbs
    unfold rayTail
    split
    · rename_i hpos
      have hslope : 1 ≤ (periods.multiplier i : ℤ) *
          (σ.sign * det (star.component j).direction (star.component i).direction) := by
        nlinarith
      have hright : (star.component j).upper < height (star.component j).direction (z + q) := by
        rw [hheight]
        have := mul_le_mul_of_nonneg_left hslope hna
        nlinarith
      rw [(star.component j).right_agreement (z + q) hright]
      exact hasPeriod_zsmul _ _ (periods.right_period i j) ((n : ℤ) * σ.sign) z
    · rename_i hneg
      have hslope : (periods.multiplier i : ℤ) *
          (σ.sign * det (star.component j).direction (star.component i).direction) ≤ -1 := by
        have : σ.sign * det (star.component j).direction (star.component i).direction < 0 := by omega
        nlinarith
      have hleft : height (star.component j).direction (z + q) < (star.component j).lower := by
        rw [hheight]
        have := mul_le_mul_of_nonneg_left hslope hna
        nlinarith
      rw [(star.component j).left_agreement (z + q) hleft]
      exact hasPeriod_zsmul _ _ (periods.left_period i j) ((n : ℤ) * σ.sign) z
  change (∑ j, (star.component j).field (z + q)) =
    (star.component i).field z + ∑ j ∈ Finset.univ.erase i, rayTail star i j σ z
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hown]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact ht j (Finset.mem_erase.mp hj).1

theorem isolating_configuration_period {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation) :
    HasPeriod (isolatingConfiguration star i σ) (periods.vector i) := by
  classical
  apply hasPeriod_add_fields
  · exact periods.component_period i
  · intro z
    apply Finset.sum_congr rfl
    intro j _
    unfold rayTail
    split
    · exact periods.right_period i j z
    · exact periods.left_period i j z

theorem pure_ray_background_common_period {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i j : Fin star.m) (σ : RayOrientation)
    (side : TailSide) :
    HasPeriod (pureRayBackground star i σ side) (periods.vector j) := by
  classical
  apply hasPeriod_add_fields
  · cases side with
    | left => exact periods.left_period j i
    | right => exact periods.right_period j i
  · intro z
    apply Finset.sum_congr rfl
    intro k _
    unfold rayTail
    split
    · exact periods.right_period j k z
    · exact periods.left_period j k z

theorem pure_ray_background_doubly_periodic {p : ℕ} (star : StarData p)
    (i : Fin star.m) (σ : RayOrientation) (side : TailSide) :
    DoublyPeriodic (pureRayBackground star i σ side) := by
  classical
  apply doublyPeriodic_add_fields
  · cases side with
    | left => exact (star.component i).left_doubly_periodic
    | right => exact (star.component i).right_doubly_periodic
  · have he : rayBackground star i σ = ∑ j ∈ Finset.univ.erase i, rayTail star i j σ := by
      ext z
      simp [rayBackground]
    rw [he]
    apply Finset.sum_induction
    · intro f g hf hg
      exact doublyPeriodic_add_fields f g hf hg
    · apply (doublyPeriodic_iff_grid _).mpr
      exact ⟨1, by omega, by intro z w; rfl⟩
    · intro j _
      unfold rayTail
      split
      · exact (star.component j).right_doubly_periodic
      · exact (star.component j).left_doubly_periodic

/-- §2.1: the actual isolated configurations lie in the original orbit closure. -/
theorem isolating_configuration_mem_orbit_closure {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation) :
    isolatingConfiguration star i σ ∈ OrbitClosure star.configuration := by
  intro W
  obtain ⟨N, hN⟩ := isolating_configuration_finite_stabilisation star periods i σ W
  exact ⟨((N : ℤ) * σ.sign) • periods.vector i,
    fun z hz => by simpa [add_comm] using (hN N le_rfl z hz).symm⟩

/-- §2.1: each actual pure ray background also lies in the original orbit closure. -/
theorem pure_ray_background_mem_orbit_closure {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation)
    (side : TailSide) :
    pureRayBackground star i σ side ∈ OrbitClosure star.configuration := by
  classical
  let G := pureRayBackground star i σ side
  obtain ⟨N, hN, hp⟩ := (doublyPeriodic_iff_grid G).mp
    (pure_ray_background_doubly_periodic star i σ side)
  obtain ⟨v, hv⟩ := primitive_height_surjective (star.component i).direction
    (star.component i).primitive 1
  let K : Lattice → ℕ := fun z =>
    ((star.component i).upper - height (star.component i).direction z).natAbs +
      (height (star.component i).direction z - (star.component i).lower).natAbs + 1
  intro W
  let n := W.sup K
  let u := match side with
    | .right => (n : ℤ) • ((N : ℤ) • v)
    | .left => -((n : ℤ) • ((N : ℤ) • v))
  have hpu : HasPeriod G u := by
    cases side with
    | right => exact hasPeriod_zsmul G _ (hp v) n
    | left => exact hasPeriod_neg G _ (hasPeriod_zsmul G _ (hp v) n)
  have hI : ∀ z ∈ W, isolatingConfiguration star i σ (z + u) = G z := by
    intro z hz
    have hK : K z ≤ n := Finset.le_sup hz
    have hK' : (K z : ℤ) ≤ n := by exact_mod_cast hK
    dsimp [K] at hK'
    have hupper := Int.le_natAbs (a := (star.component i).upper -
      height (star.component i).direction z)
    have hlower := Int.le_natAbs (a := height (star.component i).direction z -
      (star.component i).lower)
    have hu0 := Int.natCast_nonneg
      ((star.component i).upper - height (star.component i).direction z).natAbs
    have hl0 := Int.natCast_nonneg
      (height (star.component i).direction z - (star.component i).lower).natAbs
    have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
    have hn0 := Int.natCast_nonneg n
    have hnN := mul_le_mul_of_nonneg_left hN' hn0
    have hsame : isolatingConfiguration star i σ (z + u) = G (z + u) := by
      cases side with
      | right =>
          have hright : (star.component i).upper < height (star.component i).direction (z + u) := by
            simp only [u, height_add, height_zsmul, hv, mul_one]
            nlinarith
          change (star.component i).field (z + u) + rayBackground star i σ (z + u) =
            (star.component i).rightTail (z + u) + rayBackground star i σ (z + u)
          rw [(star.component i).right_agreement (z + u) hright]
      | left =>
          have hleft : height (star.component i).direction (z + u) < (star.component i).lower := by
            simp only [u, height_add]
            rw [show height (star.component i).direction
                (-((n : ℤ) • ((N : ℤ) • v))) = -(n : ℤ) * N by
              rw [← neg_smul, height_zsmul, height_zsmul, hv, mul_one]]
            nlinarith
          change (star.component i).field (z + u) + rayBackground star i σ (z + u) =
            (star.component i).leftTail (z + u) + rayBackground star i σ (z + u)
          rw [(star.component i).left_agreement (z + u) hleft]
    exact hsame.trans (hpu z)
  obtain ⟨v', hv'⟩ := isolating_configuration_mem_orbit_closure star periods i σ
    (W.image (fun z => z + u))
  refine ⟨v' + u, fun z hz => ?_⟩
  have h := hv' (z + u) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  rw [hI z hz] at h
  simpa only [add_assoc, add_comm, add_left_comm] using h

/-- Property (P1), right orientation, with the strict source half-plane. -/
theorem exceptional_difference_right_vanishes {p : ℕ} (star : StarData p)
    (i : Fin star.m) (σ : RayOrientation) (a : ZMod p) :
    ∀ z, (star.component i).upper < height (star.component i).direction z →
      exceptionalDifference star i σ .right a z = 0 := by
  intro z hz
  have h := (star.component i).right_agreement z hz
  simp [exceptionalDifference, isolatingConfiguration, pureRayBackground,
    componentTail, colorIndicator, h]

/-- Property (P1), left orientation. -/
theorem exceptional_difference_left_vanishes {p : ℕ} (star : StarData p)
    (i : Fin star.m) (σ : RayOrientation) (a : ZMod p) :
    ∀ z, height (star.component i).direction z < (star.component i).lower →
      exceptionalDifference star i σ .left a z = 0 := by
  intro z hz
  have h := (star.component i).left_agreement z hz
  simp [exceptionalDifference, isolatingConfiguration, pureRayBackground,
    componentTail, colorIndicator, h]

/-- Property (P2). -/
theorem exceptional_difference_period {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation)
    (side : TailSide) (a : ZMod p) :
    HasPeriod (exceptionalDifference star i σ side a) (periods.vector i) := by
  intro z
  have hI := isolating_configuration_period star periods i σ z
  have hG := pure_ray_background_common_period star periods i i σ side z
  simp only [exceptionalDifference, Pi.sub_apply, colorIndicator, hI, hG]

/-- Source Lemma 2.1; emptiness cannot be hidden by allowing zero degrees. -/
theorem exceptional_spectrum_nonempty {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) :
    (exceptionalSpectrum star periods i).Nonempty := by
  classical
  by_contra hn
  have hd : ∀ a : ZMod p, exceptionalDifference star i .positive .right a = 0 := by
    intro a
    have hp : ∀ ζ ∈ rootSpectrum (periods.multiplier i),
        spectralProjection (star.component i).direction (periods.multiplier i) ζ
          (exceptionalDifference star i .positive .right a) = 0 := by
      intro ζ hζ
      by_contra hocc
      exact hn ⟨ζ, Finset.mem_filter.mpr ⟨hζ, .positive, .right, a, hocc⟩⟩
    have hc := spectral_projection_complete (star.component i).direction
      (periods.multiplier i) (periods.positive i)
      (exceptionalDifference star i .positive .right a)
      (exceptional_difference_period star periods i .positive .right a)
    rw [Finset.sum_eq_zero hp] at hc
    exact hc.symm
  have hf : (star.component i).field = (star.component i).rightTail := by
    funext z
    let a := isolatingConfiguration star i .positive z
    have hz := congrFun (hd a) z
    have he : isolatingConfiguration star i .positive z =
        pureRayBackground star i .positive .right z := by
      by_contra hne
      simp [exceptionalDifference, colorIndicator, a, eq_comm, hne] at hz
    exact add_right_cancel he
  exact (star.component i).not_doubly_periodic (hf ▸ (star.component i).right_doubly_periodic)

/-- Source Lemma 2.2: injective integer encoding preserves every exceptional root. -/
theorem spectrum_preserving_integer_encoding {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) :
    ∃ w : ZMod p → ℤ, SpectrumPreservingEncoding star periods w := by
  classical
  let : NeZero p := ⟨star.prime.ne_zero⟩
  let Condition := Σ i : Fin star.m, {ζ : ℂ // ζ ∈ exceptionalSpectrum star periods i}
  have hwitness : ∀ b : Condition, ∃ σ side a z,
      spectralProjection (star.component b.1).direction (periods.multiplier b.1)
        b.2.val (exceptionalDifference star b.1 σ side a) z ≠ 0 := by
    intro b
    obtain ⟨σ, side, a, ha⟩ := (Finset.mem_filter.mp b.2.property).2
    obtain ⟨z, hz⟩ : ∃ z, spectralProjection (star.component b.1).direction
        (periods.multiplier b.1) b.2.val (exceptionalDifference star b.1 σ side a) z ≠ 0 := by
      by_contra! hn
      exact ha (funext hn)
    exact ⟨σ, side, a, z, hz⟩
  choose σ side a z hz using hwitness
  let coeff : Condition → ZMod p → ℂ := fun b c =>
    spectralProjection (star.component b.1).direction (periods.multiplier b.1)
      b.2.val (exceptionalDifference star b.1 (σ b) (side b) c) (z b)
  obtain ⟨w, hwinj, hw⟩ := finite_integer_encoding coeff (fun b => ⟨a b, hz b⟩)
  have hencode : ∀ i σ side z,
      encodedExceptionalDifference star i σ side w z =
        ∑ c : ZMod p, (w c : ℂ) * exceptionalDifference star i σ side c z := by
    intro i σ side z
    simp [encodedExceptionalDifference, exceptionalDifference, colorIndicator,
      mul_sub, Finset.sum_sub_distrib, mul_ite, eq_comm]
  refine ⟨w, hwinj, ?_⟩
  intro i ζ hζ
  let b : Condition := ⟨i, ζ, hζ⟩
  refine ⟨σ b, side b, ?_⟩
  intro hzero
  apply hw b
  have hlinear : spectralProjection (star.component i).direction (periods.multiplier i) ζ
      (encodedExceptionalDifference star i (σ b) (side b) w) (z b) =
      ∑ c : ZMod p, (w c : ℂ) * coeff b c := by
    simp only [spectralProjection, coeff]
    simp_rw [hencode, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [b]
    ring
  rw [← hlinear]
  exact congrFun hzero (z b)

end
end ConvexNivat
