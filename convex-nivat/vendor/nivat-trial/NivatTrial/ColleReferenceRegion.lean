import NivatTrial.ColleCaseTwoAperiodic
import NivatTrial.ColleWedgeReference

/-! A second period of the reference on a high half-plane gives two actual
periods of the original nonperiodic configuration on a smaller convex
region. The witness configuration is unchanged by this final restriction. -/

namespace NivatTrial.ColleReferenceRegion

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Dynamics
open NivatTrial.Periodicity NivatTrial.Nonexpansive NivatTrial.RegionGeometry
open NivatTrial.ColleGenerating
open NivatTrial.ColleEnvelopeGeometry
open scoped Classical
noncomputable section

def upperCut (R : Set Lattice) (u : Lattice) (b : ℤ) : Set Lattice :=
  R ∩ {z | b ≤ det u z}

theorem upperCut_latticeConvex (R : Set Lattice) (hR : LatticeConvexRegion R)
    (u : Lattice) (b : ℤ) : LatticeConvexRegion (upperCut R u b) := by
  obtain ⟨C,hC,hRC⟩ := hR
  refine ⟨C ∩ {x | (b:ℝ) ≤ linearScore (embed u) x},
    hC.inter (convex_halfSpace_ge (linearScore (embed u)).isLinear b),?_⟩
  ext z
  simp only [upperCut,hRC,Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,
    linearScore_embed_det,Int.cast_le]

theorem upperCut_forward {R : Set Lattice} {a : Lattice}
    (hR : ForwardInvariant R a) (u : Lattice) (b : ℤ) (ha : 0 ≤ det u a) :
    ForwardInvariant (upperCut R u b) a := by
  intro z hz
  refine ⟨hR z hz.1,?_⟩
  change b ≤ det u (z+a)
  rw [det_add_right]
  exact hz.2.trans (le_add_of_nonneg_right ha)

theorem two_period_region_of_reference_halfPlane_period {A : Type*}
    (x p : Lattice → A) (R : Set Lattice) (hR : LatticeConvexRegion R)
    (u k : Lattice) (huk : 0 < det u k)
    (hback : ForwardInvariant R (-u)) (hforward : ForwardInvariant R k)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hxp : AgreeOn x p R) (hp : IsPeriod p u)
    (b : ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hsecond : ∀ z, b ≤ det u z → p (z+Q•k)=p z) :
    ∃ K : Set Lattice, LatticeConvexRegion K ∧ K.Nonempty ∧
      K ⊆ R ∧ ∃ a d : Lattice, det a d ≠ 0 ∧ PeriodicOn x K a ∧ PeriodicOn x K d := by
  let K := upperCut R u b
  have hKc : LatticeConvexRegion K := upperCut_latticeConvex R hR u b
  have hKn : K.Nonempty := by
    obtain ⟨z,hz,hzb⟩ := hheight b
    exact ⟨z,hz,hzb⟩
  have hKu : ForwardInvariant K (-u) := upperCut_forward hback u b (by simp)
  have hKk : ForwardInvariant K (Q•k) := by
    apply upperCut_forward (hforward.nsmul Q) u b
    rw [det_nsmul_right]
    exact mul_nonneg (by positivity) huk.le
  refine ⟨K,hKc,hKn,Set.inter_subset_left,-u,Q•k,?_,⟨hKu,?_⟩,⟨hKk,?_⟩⟩
  · rw [det_neg_left,det_nsmul_right]
    exact neg_ne_zero.mpr (mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hQ) (ne_of_gt huk))
  · intro z hz
    exact (hxp _ (hKu z hz).1).trans ((hp.neg z).trans (hxp z hz.1).symm)
  · intro z hz
    exact (hxp _ (hKk z hz).1).trans ((hsecond z hz.2).trans (hxp z hz.1).symm)

end
end NivatTrial.ColleReferenceRegion
