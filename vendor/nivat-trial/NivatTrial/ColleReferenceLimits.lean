import NivatTrial.ColleBoundaryLimits
import NivatTrial.ColleProperReferences

/-! The first singly periodic boundary limit in Colle's second case.
Backward translates fill the original supporting half-plane and retain a
fixed periodic reference there, including its obstruction to a doubly
periodic extension. -/

namespace NivatTrial.ColleReferenceLimits

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Dynamics
open NivatTrial.Nonexpansive NivatTrial.NonexpansiveExistence
open NivatTrial.Periodicity NivatTrial.ExternalInputs
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleEnvelopeRays
open NivatTrial.ColleBoundaryLimits NivatTrial.ColleOrbitCofactor
open NivatTrial.ColleProperReferences
open Filter
open scoped Classical
noncomputable section

theorem exists_directional_limit_with_agreement {A : Type*} [Fintype A]
    (x p : Lattice → A) (q : Lattice) (R : Set Lattice)
    (hagree : ∀ z ∈ R, ∀ᶠ n : ℕ in atTop, x (z+n•q) = p z) :
    ∃ y : Lattice → A, DirectionOrbitHull x y q ∧ AgreeOn y p R := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have hx (n : ℕ) : shift (n•q) x ∈ languageHull x :=
    shift_mem_languageHull (self_mem_languageHull x) _
  obtain ⟨y,_,φ,hφ,hlim⟩ := (isCompact_languageHull x).tendsto_subseq hx
  refine ⟨y,?_,?_⟩
  · intro S
    have hevent : ∀ᶠ n : ℕ in atTop, ∀ z ∈ S, shift ((φ n)•q) x z = y z :=
      S.eventually_all.mpr (fun z _ => eventually_coordinate_eq hlim z)
    obtain ⟨n,hn⟩ := hevent.exists
    exact ⟨φ n,by simpa only [shift_apply,natCast_zsmul] using hn⟩
  · intro z hz
    have hp := hφ.tendsto_atTop.eventually (hagree z hz)
    obtain ⟨n,hpn,he⟩ := (hp.and (eventually_coordinate_eq hlim z)).exists
    rw [← he]
    simpa only [Function.comp_apply,shift_apply,add_comm] using hpn

theorem exists_backward_reference_limit {A : Type*} [Fintype A]
    (x p : Lattice → A) (D : Finset Lattice) (R : Set Lattice)
    (hR : IsEnvelope D R) (u k : Lattice) (huk : 0 < det u k)
    (hzero : 0 ∈ R) (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hxp : AgreeOn x p R) (hp : IsPeriod p u) :
    ∃ y : Lattice → A, DirectionOrbitHull x y (-u) ∧
      AgreeOn y p (halfPlane (embed u) 0) := by
  apply exists_directional_limit_with_agreement x p (-u) (halfPlane (embed u) 0)
  intro z hz
  have hz' : 0 ≤ det u z := by
    have hs : (0:ℝ) ≤ (det u z:ℝ) := by simpa [halfPlane,score,embed,det] using hz
    exact_mod_cast hs
  filter_upwards [eventually_mem_bottom_halfPlane D R hR u k huk hzero hback hheight z hz'] with n hn
  exact (hxp (z+n•(-u)) hn).trans (hp.neg.nsmul n z)

theorem exists_singly_periodic_reference_limit
    {M m : ℕ} (x p : Lattice → Fin M)
    (E : IntegerDecomposition (integerField x) m)
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u k : Lattice) (huk : 0 < det u k)
    (hzero : 0 ∈ R) (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hxp : AgreeOn x p R) (hp : IsPeriod p u)
    (hproper : ¬HasDoublyPeriodicExtension p (halfPlane (embed u) 0)) :
    ∃ y : Lattice → Fin M, DirectionOrbitHull x y (-u) ∧
      ¬IsDoublyPeriodic y ∧ ∃ Q : ℕ, 0 < Q ∧ IsPeriod y (Q•u) := by
  obtain ⟨y,hy,hyp⟩ := exists_backward_reference_limit x p D R hR u k huk
    hzero hback hheight hxp hp
  have hu : u ≠ 0 := by intro he; simp [he,det] at huk
  have hpy : ∀ z, (0:ℤ) ≤ det u z → y (z+u) = y z := by
    intro z hz
    have hm : z ∈ halfPlane (embed u) 0 := by
      change (0:ℝ) ≤ score (embed u) z
      have hh : (0:ℝ) ≤ (det u z:ℝ) := by exact_mod_cast hz
      simpa [score,embed,det] using hh
    have hmu : z+u ∈ halfPlane (embed u) 0 := by
      change (0:ℝ) ≤ score (embed u) (z+u)
      rw [score_add,NivatTrial.ColleHalfPlanePeriod.score_embed_self,add_zero]
      exact hm
    exact (hyp (z+u) hmu).trans ((hp z).trans (hyp z hm).symm)
  obtain ⟨Q,hQ,hper⟩ := global_period_of_integer_hull_halfPlane_period E
    (directionOrbitHull_mem_languageHull hy) u hu u (det_self u) 0 hpy
  refine ⟨y,hy,?_,Q,hQ,hper⟩
  intro hdp
  exact hproper ⟨y,hdp,fun z hz => (hyp z hz).symm⟩

end
end NivatTrial.ColleReferenceLimits
