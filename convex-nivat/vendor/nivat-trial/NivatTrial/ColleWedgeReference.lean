import NivatTrial.ColleCaseOne
import NivatTrial.ColleReferenceLimits
import NivatTrial.ColleMinimality

/-! A periodic wedge supplies an actual globally periodic reference in the
directional orbit hull. The reference agrees with the original field on
the whole wedge, not just on a fixed finite sample. -/

namespace NivatTrial.ColleWedgeReference

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.NonexpansiveExistence NivatTrial.Periodicity NivatTrial.RegionGeometry
open NivatTrial.ColleCaseOne NivatTrial.ColleOrbitCofactor
open NivatTrial.ColleBoundaryLimits NivatTrial.ExternalInputs
open NivatTrial.ColleProperReferences NivatTrial.CollePeriodDirections
open Filter
open scoped Classical
noncomputable section

theorem eventually_mem_wedge {u k : Lattice} (huk : 0 < det u k)
    (c : ℤ) (Q : ℕ) (hQ : 0 < Q) (z : Lattice) (hz : 0 ≤ det u z) :
    ∀ᶠ n : ℕ in atTop, z+n•(Q•u) ∈ wedge u k c := by
  obtain ⟨N,hN⟩ := exists_nat_gt (det k z-c)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hQ' : (0:ℤ) < Q := by exact_mod_cast hQ
  have hn' : (N:ℤ) ≤ n := by exact_mod_cast hn
  have hnn : (0:ℤ) ≤ n := by positivity
  constructor
  · simpa only [det_add_right,det_nsmul_right,det_self,mul_zero,add_zero] using hz
  · simp only [det_add_right,det_nsmul_right,det_swap k u]
    have hprod : (1:ℤ) ≤ (Q:ℤ)*det u k := by nlinarith
    nlinarith

theorem exists_periodic_reference_for_wedge {M n : ℕ}
    (x : Lattice → Fin M) (E : IntegerDecomposition (integerField x) n)
    (u k : Lattice) (huk : 0 < det u k) (c : ℤ)
    (Q : ℕ) (hQ : 0 < Q) (hper : PeriodicOn x (wedge u k c) (Q•u)) :
    ∃ p ∈ languageHull x, DirectionOrbitHull x p u ∧
      AgreeOn x p (wedge u k c) ∧ ∃ P : ℕ, 0 < P ∧ IsPeriod p (P•u) := by
  let : TopologicalSpace (Fin M) := ⊥
  have : DiscreteTopology (Fin M) := ⟨rfl⟩
  let X (t : ℕ) := shift (t•(Q•u)) x
  have hX (t : ℕ) : X t ∈ languageHull x :=
    shift_mem_languageHull (self_mem_languageHull x) _
  obtain ⟨p,hp,φ,hφ,hlim⟩ := (isCompact_languageHull x).tendsto_subseq hX
  have hcoord (z : Lattice) : ∀ᶠ t : ℕ in atTop, X (φ t) z = p z :=
    eventually_coordinate_eq hlim z
  have horbit : DirectionOrbitHull x p u := by
    intro S
    have hall : ∀ᶠ t : ℕ in atTop, ∀ z ∈ S, X (φ t) z = p z :=
      S.eventually_all.mpr (fun z _ => hcoord z)
    obtain ⟨t,ht⟩ := hall.exists
    refine ⟨((φ t)*Q : ℕ),?_⟩
    intro z hz
    simpa only [X,shift_apply,smul_smul,natCast_zsmul] using ht z hz
  have hagree : AgreeOn x p (wedge u k c) := by
    intro z hz
    obtain ⟨t,ht⟩ := (hcoord z).exists
    have he := (hper.nsmul (φ t)).2 z hz
    have hxz : X (φ t) z = x z := by
      simpa only [X,shift_apply,add_comm] using he
    exact hxz.symm.trans ht
  have hhalfper : ∀ z, (0:ℤ) ≤ det u z → p (z+Q•u) = p z := by
    intro z hz
    have hlarge : ∀ᶠ t : ℕ in atTop, z+(φ t)•(Q•u) ∈ wedge u k c :=
      hφ.tendsto_atTop.eventually (eventually_mem_wedge huk c Q hQ z hz)
    obtain ⟨t,ht,he₁,he₂⟩ := (hlarge.and ((hcoord (z+Q•u)).and (hcoord z))).exists
    rw [← he₁,← he₂]
    have he := hper.2 (z+(φ t)•(Q•u)) ht
    simpa only [X,shift_apply,add_assoc,add_comm,add_left_comm] using he
  have hu : u ≠ 0 := by intro he; simp [he,det] at huk
  obtain ⟨P,hP,hpP⟩ := global_period_of_integer_hull_halfPlane_period E hp u hu
    (Q•u) (by simp only [det_nsmul_right,det_self,mul_zero]) 0 hhalfper
  exact ⟨p,hp,horbit,hagree,P*Q,Nat.mul_pos hP hQ,by simpa only [mul_smul] using hpP⟩

theorem two_period_wedge_of_halfPlane_extension {A : Type*}
    (x p : Lattice → A) (u k : Lattice) (huk : 0 < det u k) (c : ℤ)
    (hxp : AgreeOn x p (wedge u k c))
    (hext : HasDoublyPeriodicExtension p (halfPlane (embed u) 0)) :
    ∃ a b : Lattice, det a b ≠ 0 ∧
      PeriodicOn x (wedge u k c) a ∧ PeriodicOn x (wedge u k c) b := by
  obtain ⟨q,hq,hpq⟩ := hext
  obtain ⟨P,hP,hPu⟩ := direction_period_of_finite_orbit
    q u (finite_orbit_of_doublyPeriodic q hq)
  obtain ⟨Q,hQ,hQk⟩ := direction_period_of_finite_orbit
    q k (finite_orbit_of_doublyPeriodic q hq)
  have hagree : AgreeOn x q (wedge u k c) := by
    intro z hz
    apply (hxp z hz).trans
    apply hpq z
    change (0:ℝ) ≤ score (embed u) z
    have he : (0:ℝ) ≤ (det u z:ℝ) := by exact_mod_cast hz.1
    simpa [score,embed,det] using he
  have hfirst := (wedge_forward_first huk c).nsmul P
  have hsecond := (wedge_forward_second huk c).nsmul Q
  refine ⟨P•u,Q•k,?_,⟨hfirst,?_⟩,⟨hsecond,?_⟩⟩
  · simp only [← natCast_zsmul,det_zsmul_left,det_zsmul_right]
    exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hQ)
      (mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hP) (ne_of_gt huk))
  · intro z hz
    exact (hagree _ (hfirst z hz)).trans ((hPu z).trans (hagree z hz).symm)
  · intro z hz
    exact (hagree _ (hsecond z hz)).trans ((hQk z).trans (hagree z hz).symm)

end
end NivatTrial.ColleWedgeReference
