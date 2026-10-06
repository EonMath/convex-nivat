import NivatTrial.PeriodicInterface
import NivatTrial.ColleGenerating
import NivatTrial.RegionGeometry

/-! Elementary periodic-interface geometry. Agreement with a doubly periodic
point on a half-plane creates two independent forward regional periods. The
interface point cannot be doubly periodic, and any of its periods must run
parallel to the interface. -/

namespace NivatTrial.ColleRegions

open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.Zonotope
open NivatTrial.Periodicity NivatTrial.PeriodicInterface
open NivatTrial.ColleGenerating NivatTrial.RegionGeometry
open scoped Classical
noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

theorem halfPlane_latticeConvexRegion (v : Plane) :
    LatticeConvexRegion (halfPlane v 0) := by
  refine ⟨{x : Plane | (0 : ℝ) ≤ linearScore v x},
    convex_halfSpace_ge (linearScore v).isLinear 0, ?_⟩
  ext z
  rfl

theorem halfPlane_nonempty (v : Plane) : (halfPlane v 0).Nonempty :=
  ⟨0, by simp [halfPlane]⟩

theorem forwardInvariant_halfPlane (v : Plane) (a : G)
    (ha : 0 ≤ score v a) : ForwardInvariant (halfPlane v 0) a := by
  intro z hz
  change (0 : ℝ) ≤ score v (z+a)
  rw [score_add]
  have hz' : (0 : ℝ) ≤ score v z := hz
  linarith

theorem periodicOn_of_halfPlane_agreement {A : Type*}
    {x y : G → A} {v : Plane} {a : G}
    (ha : 0 ≤ score v a) (hxp : IsPeriod x a)
    (hxy : AgreeOn x y (halfPlane v 0)) :
    PeriodicOn y (halfPlane v 0) a := by
  constructor
  · exact forwardInvariant_halfPlane v a ha
  · intro z hz
    calc
      y (z+a) = x (z+a) := (hxy (z+a) (forwardInvariant_halfPlane v a ha z hz)).symm
      _ = x z := hxp z
      _ = y z := hxy z hz

/-- Two doubly periodic fields cannot differ beyond a half-plane while
agreeing on it: they have a common positive transverse period. -/
theorem doublyPeriodic_eq_of_halfPlane_agreement {A : Type*}
    {x y : G → A} (hx : IsDoublyPeriodic x) (hy : IsDoublyPeriodic y)
    {v : Plane} (hv : v ≠ 0)
    (hxy : AgreeOn x y (halfPlane v 0)) : x = y := by
  obtain ⟨g,hg⟩ := exists_positive_score hv
  obtain ⟨qx,hqx,hpx⟩ := direction_period_of_finite_orbit x g
    (finite_orbit_of_doublyPeriodic x hx)
  obtain ⟨qy,hqy,hpy⟩ := direction_period_of_finite_orbit y g
    (finite_orbit_of_doublyPeriodic y hy)
  let q := qx*qy
  have hq : 0 < q := Nat.mul_pos hqx hqy
  have hxp : IsPeriod x (q • g) := by
    have heq : qy • (qx • g) = q • g := by
      rw [smul_smul]
      dsimp [q]
      rw [Nat.mul_comm qy qx]
    rw [← heq]
    exact hpx.nsmul qy
  have hyp : IsPeriod y (q • g) := by
    have heq : qx • (qy • g) = q • g := by
      rw [smul_smul]
    rw [← heq]
    exact hpy.nsmul qx
  have hscore : 0 < score v (q • g) := by
    rw [score_nsmul]
    exact mul_pos (by exact_mod_cast hq) hg
  funext z
  obtain ⟨n, hn⟩ := exists_nat_gt (-score v z / score v (q • g))
  have hz : z + n • (q • g) ∈ halfPlane v 0 := by
    change (0 : ℝ) ≤ score v (z + n • (q • g))
    rw [score_add, score_nsmul]
    have hmul := (div_lt_iff₀ hscore).mp hn
    linarith
  calc
    x z = x (z + n • (q • g)) := (hxp.nsmul n z).symm
    _ = y (z + n • (q • g)) := hxy _ hz
    _ = y z := hyp.nsmul n z

/-- A period of a proper periodic interface cannot cross its boundary. -/
theorem period_parallel_to_interface {A : Type*}
    {x y : G → A} (hx : IsDoublyPeriodic x)
    {v : Plane} (hv : v ≠ 0)
    (hxy : AgreeOn x y (halfPlane v 0)) (hne : x ≠ y)
    {u : G} (hyu : IsPeriod y u) : score v u = 0 := by
  have hpositive : ∀ a : G, IsPeriod y a → 0 < score v a → False := by
    intro a hya ha
    have hxp : IsPeriod x a := by
      have hshift : AgreeOn (shift a x) x (halfPlane v 0) := by
        intro z hz
        change x (a+z) = x z
        have hzplus : z+a ∈ halfPlane v 0 := forwardInvariant_halfPlane v a ha.le z hz
        calc
          x (a+z) = y (z+a) := by
            rw [add_comm]
            exact hxy _ hzplus
          _ = y z := hya z
          _ = x z := (hxy z hz).symm
      have heq := doublyPeriodic_eq_of_halfPlane_agreement (hx.shift a) hx hv hshift
      intro z
      simpa [shift, add_comm] using congrFun heq z
    apply hne
    funext z
    obtain ⟨n,hn⟩ := exists_nat_gt (-score v z / score v a)
    have hz : z+n•a ∈ halfPlane v 0 := by
      change (0 : ℝ) ≤ score v (z+n•a)
      rw [score_add, score_nsmul]
      have hmul := (div_lt_iff₀ ha).mp hn
      linarith
    calc
      x z = x (z+n•a) := (hxp.nsmul n z).symm
      _ = y (z+n•a) := hxy _ hz
      _ = y z := hya.nsmul n z
  by_contra hzero
  rcases lt_or_gt_of_ne hzero with hneg | hpos
  · exact hpositive (-u) hyu.neg (by rw [score_neg]; linarith)
  · exact hpositive u hyu hpos

private theorem det_neg_left (a b : G) :
    NivatTrial.Geometry.det (-a) b = -NivatTrial.Geometry.det a b := by
  simp [NivatTrial.Geometry.det]
  ring

/-- Sign two independent periods so that both point into the chosen closed
half-plane, keeping their determinant nonzero. -/
theorem inward_periods {A : Type*} {x : G → A}
    (hx : IsDoublyPeriodic x) (v : Plane) :
    ∃ a b : G, NivatTrial.Geometry.det a b ≠ 0 ∧
      0 ≤ score v a ∧ 0 ≤ score v b ∧
      IsPeriod x a ∧ IsPeriod x b := by
  obtain ⟨h,k,hdet,hh,hk⟩ := hx
  let a := if 0 ≤ score v h then h else -h
  let b := if 0 ≤ score v k then k else -k
  have ha : 0 ≤ score v a := by
    dsimp [a]
    split_ifs with hs
    · exact hs
    · rw [score_neg]
      linarith
  have hb : 0 ≤ score v b := by
    dsimp [b]
    split_ifs with hs
    · exact hs
    · rw [score_neg]
      linarith
  have hap : IsPeriod x a := by
    by_cases hs : 0 ≤ score v h
    · simpa [a,hs] using hh
    · simpa [a,hs] using hh.neg
  have hbp : IsPeriod x b := by
    by_cases hs : 0 ≤ score v k
    · simpa [b,hs] using hk
    · simpa [b,hs] using hk.neg
  have hab : NivatTrial.Geometry.det a b ≠ 0 := by
    dsimp [a,b]
    split_ifs <;> simpa only [NivatTrial.Geometry.det_neg_right, det_neg_left,
      neg_ne_zero, neg_neg] using hdet
  exact ⟨a,b,hab,ha,hb,hap,hbp⟩

/-- The compact interface yields a genuine convex regional pair of forward
periods. The interface is known to be non-doubly-periodic; excluding its
possible period *parallel* to the boundary is a later Colle step. -/
theorem exists_periodic_halfPlane_region {A : Type*} [Fintype A]
    (θ p : G → A) (hp : p ∈ languageHull θ)
    (hpDP : IsDoublyPeriodic p) (hθ : ¬IsDoublyPeriodic θ) :
    ∃ y ∈ languageHull θ, ¬IsDoublyPeriodic y ∧
      ∃ v : Plane, v ≠ 0 ∧
        ∃ R : Set G, LatticeConvexRegion R ∧ R.Nonempty ∧
          ∃ a b : G, NivatTrial.Geometry.det a b ≠ 0 ∧
            PeriodicOn y R a ∧ PeriodicOn y R b := by
  obtain ⟨v,hv,x,hxp,y,hy,hne,hagree⟩ :=
    exists_periodic_interface θ p hp hpDP hθ
  have hxDP : IsDoublyPeriodic x := by
    obtain ⟨u,hu⟩ := hxp
    rw [← hu]
    exact hpDP.shift u
  have hyNot : ¬IsDoublyPeriodic y :=
    fun hyDP => hne (doublyPeriodic_eq_of_halfPlane_agreement hxDP hyDP hv hagree)
  obtain ⟨a,b,hab,ha,hb,hap,hbp⟩ := inward_periods hxDP v
  exact ⟨y,hy,hyNot,v,hv,halfPlane v 0,
    halfPlane_latticeConvexRegion v,halfPlane_nonempty v,a,b,hab,
    periodicOn_of_halfPlane_agreement ha hap hagree,
    periodicOn_of_halfPlane_agreement hb hbp hagree⟩

end

end NivatTrial.ColleRegions
