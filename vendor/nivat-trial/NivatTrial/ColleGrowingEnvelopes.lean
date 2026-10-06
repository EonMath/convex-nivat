import NivatTrial.ColleBoundaryRecenter
import NivatTrial.CollePeriodicPhases
import NivatTrial.ColleEnvelopeLimits
import NivatTrial.ColleEnvelopeRecession

/-! Assemble the geometric extraction from actual growing agreement
windows. The resulting configuration belongs to the original language hull;
its region has two independent inward directions and keeps the prescribed
edge lengths. A separate boundary-defect argument is still needed to prove
that this configuration is aperiodic. -/

namespace NivatTrial.ColleGrowingEnvelopes

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.RegionGeometry NivatTrial.Nonexpansive
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeTranslation NivatTrial.ColleBoundaryRecenter
open NivatTrial.CollePeriodicPhases NivatTrial.ColleEnvelopeLimits
open NivatTrial.ColleEnvelopeRecession
open scoped Classical
noncomputable section

theorem extract_two_direction_region {A : Type*} [Fintype A]
    (θ p : Lattice → A) (D : Finset Lattice) (u k : Lattice)
    (huk : 0 < det u k) (hp : IsPeriod p u)
    (T : ℕ → Finset Lattice)
    (henv : ∀ n, IsEnvelope D (T n : Set Lattice))
    (hfaces : ∀ n, LongFaces D (T n : Set Lattice))
    (hzero : ∀ n, 0 ∈ T n) (hback : ∀ n, n•u ∈ T n)
    (hheight : ∀ n, n•k ∈ T n)
    (hhalf : ∀ n, ∀ z ∈ T n, 0 ≤ det u z)
    (x : ℕ → Lattice → A) (hx : ∀ n, x n ∈ languageHull θ)
    (hagree : ∀ n, AgreeOn (x n) p (T n : Set Lattice)) :
    ∃ y ∈ languageHull θ, ∃ q ∈ languageHull p, ∃ R : Set Lattice,
      (∃ c : Lattice, det u c = 0 ∧ q = shift c p) ∧
      IsPeriod q u ∧ AgreeOn y q R ∧ IsEnvelope D R ∧ LongFaces D R ∧
      LatticeConvexRegion R ∧ 0 ∈ R ∧ u ∉ R ∧
      (∀ z ∈ R, 0 ≤ det u z) ∧
      (∀ n : ℕ, -(n•u) ∈ R) ∧
      (∀ N : ℤ, ∃ z ∈ R, N ≤ det u z) ∧
      ∃ d ∈ D, 0 < det u d ∧ ForwardInvariant R (-u) ∧ ForwardInvariant R d := by
  have hu : u ≠ 0 := by intro he; simp [he,det] at huk
  have hconvex (n : ℕ) : NivatTrial.LatticePolygon.IsLatticeConvex (T n) :=
    NivatTrial.ColleEnvelopeGeometry.latticeConvex_finset_of_region (T n) (henv n).latticeConvex
  choose c hcT hcu hcz hcout hcback hcheight using fun n =>
    recenter_with_growing_backward_segment (T n) (hconvex n) (hzero n) u k huk n (hback n)
  obtain ⟨q,a,ha,hq,hqp,hqmem⟩ := constant_boundary_phase_subsequence p u hu hp c hcu
  let U (n : ℕ) := recenterWindow (T (a n)) (c (a n))
  have hUz (n : ℕ) : 0 ∈ U n := hcz (a n)
  have hUenv (n : ℕ) : IsEnvelope D (U n : Set Lattice) :=
    isEnvelope_recenterWindow (henv (a n)) _
  obtain ⟨b,hb,hbmono⟩ := exists_monotone_subsequence D U hUz hUenv
  let e (n : ℕ) := a (b n)
  have he : StrictMono e := ha.comp hb
  let V (n : ℕ) := U (b n)
  let X (n : ℕ) := shift (c (e n)) (x (e n))
  have hVmono : ∀ m n, m ≤ n → V m ⊆ V n := hbmono
  have hX (n : ℕ) : X n ∈ languageHull θ := shift_mem_languageHull (hx (e n)) _
  have hXagree (n : ℕ) (z : Lattice) (hz : z ∈ V n) : X n z = q z := by
    have hzT : z+c (e n) ∈ T (e n) := (mem_recenterWindow _ _ _).mp hz
    have heq := hagree (e n) (z+c (e n)) hzT
    change x (e n) (c (e n)+z) = q z
    rw [← hq (b n)]
    simpa only [shift_apply,add_comm] using heq
  obtain ⟨y,hy,hyq⟩ := limit_on_increasing_region θ q V hVmono X hX hXagree
  let R := increasingRegion V
  have hRenv : IsEnvelope D R := increasingRegion_isEnvelope D V (fun n => hUenv (b n)) hVmono
  have hRfaces : LongFaces D R := increasingRegion_longFaces D V
    (fun n => longFaces_recenterWindow (hfaces (e n)) _)
  have hRzero : 0 ∈ R := ⟨0,hUz (b 0)⟩
  have hRout : u ∉ R := by
    rintro ⟨n,hn⟩
    exact hcout (e n) hn
  have hRback (n : ℕ) : -(n•u) ∈ R := ⟨n,hcback (e n) n (he.id_le n)⟩
  have hRhalf (z : Lattice) (hz : z ∈ R) : 0 ≤ det u z := by
    obtain ⟨n,hn⟩ := hz
    have hh := hhalf (e n) (z+c (e n)) ((mem_recenterWindow _ _ _).mp hn)
    simpa only [det_add_right,hcu,add_zero] using hh
  have hRheight (N : ℤ) : ∃ z ∈ R, N ≤ det u z := by
    obtain ⟨n,hn⟩ := exists_nat_gt N
    refine ⟨(e n)•k-c (e n),⟨n,?_⟩,?_⟩
    · change (e n)•k-c (e n) ∈ recenterWindow (T (e n)) (c (e n))
      simpa only [mem_recenterWindow,sub_add_cancel] using hheight (e n)
    · rw [hcheight,det_nsmul_right]
      have hne : (n:ℤ) ≤ e n := by exact_mod_cast he.id_le n
      have hnonneg : (0:ℤ) ≤ e n := by omega
      nlinarith
  obtain ⟨d,hd,hud,hRu,hRd⟩ := exists_second_recession_direction D R hRenv u
    hRzero hRout hRback hRheight
  exact ⟨y,hy,q,hqmem,R,⟨c (a 0),hcu (a 0),(hq 0).symm⟩,
    hqp,hyq,hRenv,hRfaces,hRenv.latticeConvex,
    hRzero,hRout,hRhalf,hRback,hRheight,d,hd,hud,hRu,hRd⟩

end
end NivatTrial.ColleGrowingEnvelopes
