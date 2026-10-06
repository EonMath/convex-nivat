import NivatTrial.ColleGrowingEnvelopes
import NivatTrial.ColleMaximalSeedDefect
import NivatTrial.ColleFiniteDefectLimits
import NivatTrial.ColleMaximalTranslation
import NivatTrial.ColleMaximalAgreementLimit

/-! Colle's growing-envelope extraction with a retained genuine defect.
Maximality and the product recurrence place a disagreement in one fixed
finite early-window expansion before taking the configuration limit. -/

namespace NivatTrial.ColleDefectiveGrowingEnvelopes

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.RegionGeometry NivatTrial.Nonexpansive NivatTrial.OneSidedRecurrence
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeTranslation NivatTrial.ColleBoundaryRecenter
open NivatTrial.CollePeriodicPhases NivatTrial.ColleEnvelopeLimits
open NivatTrial.ColleEnvelopeRecession NivatTrial.ColleEnvelopeGeometry
open NivatTrial.ColleMaximalTranslation NivatTrial.ColleMaximalSeedDefect
open NivatTrial.ColleFiniteDefectLimits
open NivatTrial.ColleMaximalAgreementLimit
open scoped Classical
noncomputable section

theorem extract_region_with_actual_defect {A : Type*} [Fintype A]
    (θ p : Lattice → A) (code : A → ℤ) (hcode : Function.Injective code)
    (hs : List Lattice) (hne : ∀ d ∈ hs, d ≠ 0)
    (hind : hs.Pairwise (fun d e => det d e ≠ 0))
    (hann : iteratedIncrement hs (encode code θ) = 0)
    (D : Finset Lattice) (hdirs : ∀ d ∈ hs, d ∈ D ∧ -d ∈ D)
    (u k : Lattice) (huk : 0 < det u k) (huD : u ∈ D) (hnuD : -u ∈ D)
    (hpHull : p ∈ languageHull θ) (hp : IsPeriod p u)
    (T : ℕ → Finset Lattice) (Q : ℕ → Set Lattice)
    (henv : ∀ n, IsEnvelope D (T n : Set Lattice))
    (hfaces : ∀ n, LongFaces D (T n : Set Lattice))
    (hzero : ∀ n, 0 ∈ T n) (hback : ∀ n, n•u ∈ T n)
    (hheight : ∀ n, n•k ∈ T n)
    (hhalf : ∀ n, ∀ z ∈ T n, 0 ≤ det u z)
    (hQenv : ∀ n, IsEnvelope D (Q n))
    (hTQ : ∀ n, (T n : Set Lattice) ⊆ Q n)
    (hQforward : ∀ n, ForwardInvariant (Q n) u)
    (x : ℕ → Lattice → A) (hx : ∀ n, x n ∈ languageHull θ)
    (hagree : ∀ n, AgreeOn (x n) p (T n : Set Lattice))
    (hmax : ∀ n, ∀ R : Set Lattice, (T n : Set Lattice) ⊆ R → R ⊆ Q n →
      IsEnvelope D R → LongFaces D R → AgreeOn (x n) p R → R = (T n : Set Lattice)) :
    ∃ y ∈ languageHull θ, ∃ q ∈ languageHull p, ∃ R : Set Lattice,
      (∃ c : Lattice, det u c = 0 ∧ q = shift c p) ∧
      IsPeriod q u ∧ AgreeOn y q R ∧ IsEnvelope D R ∧ LongFaces D R ∧
      LatticeConvexRegion R ∧ 0 ∈ R ∧ u ∉ R ∧
      (∀ z ∈ R, 0 ≤ det u z) ∧ (∀ n : ℕ, -(n•u) ∈ R) ∧
      (∀ N : ℤ, ∃ z ∈ R, N ≤ det u z) ∧
      (∃ d ∈ D, 0 < det u d ∧ ForwardInvariant R (-u) ∧ ForwardInvariant R d) ∧
      (∃ z : Lattice, 0 ≤ det u z ∧ y z ≠ q z) ∧
      FiniteExtensionMaximal D y q R {z | 0 ≤ det u z} ∧
      (∀ F : Finset Lattice, (F : Set Lattice) ⊆ R →
        ∃ W : Finset Lattice, F ⊆ W ∧ (W : Set Lattice) ⊆ R ∧
          IsEnvelope D (W : Set Lattice) ∧ LongFaces D (W : Set Lattice) ∧ 0 ∈ W) := by
  have hu : u ≠ 0 := by intro he; simp [he,det] at huk
  have hconvex (n : ℕ) : NivatTrial.LatticePolygon.IsLatticeConvex (T n) :=
    latticeConvex_finset_of_region (T n) (henv n).latticeConvex
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
  let Q' (n : ℕ) := recenter (Q (e n)) (c (e n))
  have hVmono : ∀ m n, m ≤ n → V m ⊆ V n := hbmono
  have hVeq (n : ℕ) : (V n : Set Lattice) = recenter (T (e n) : Set Lattice) (c (e n)) :=
    coe_recenterWindow _ _
  have hVenv (n : ℕ) : IsEnvelope D (V n : Set Lattice) := hUenv (b n)
  have hVfaces (n : ℕ) : LongFaces D (V n : Set Lattice) :=
    longFaces_recenterWindow (hfaces (e n)) _
  have hVhalf (n : ℕ) (z : Lattice) (hz : z ∈ V n) : 0 ≤ det u z := by
    have hh := hhalf (e n) (z+c (e n)) ((mem_recenterWindow _ _ _).mp hz)
    simpa only [det_add_right,hcu,add_zero] using hh
  have hX (n : ℕ) : X n ∈ languageHull θ := shift_mem_languageHull (hx (e n)) _
  have hXagree (n : ℕ) (z : Lattice) (hz : z ∈ V n) : X n z = q z := by
    have hzT : z+c (e n) ∈ T (e n) := (mem_recenterWindow _ _ _).mp hz
    have heq := hagree (e n) (z+c (e n)) hzT
    change x (e n) (c (e n)+z) = q z
    rw [← hq (b n)]
    simpa only [shift_apply,add_comm] using heq
  have hQ' (n : ℕ) : IsEnvelope D (Q' n) := isEnvelope_recenter (hQenv (e n)) _
  have hVQ (n : ℕ) : (V n : Set Lattice) ⊆ Q' n := by
    rw [hVeq]
    exact recenter_mono (hTQ (e n)) _
  have hQ'forward (n : ℕ) : ForwardInvariant (Q' n) u :=
    recenter_forward (hQforward (e n)) _
  have hXmax (n : ℕ) : ∀ S : Set Lattice, (V n : Set Lattice) ⊆ S → S ⊆ Q' n →
      IsEnvelope D S → LongFaces D S → AgreeOn (X n) q S → S = (V n : Set Lattice) := by
    intro S hVS hSQ hSe hSf hXS
    have hpq : shift (c (e n)) p = q := hq (b n)
    have hSagree : AgreeOn (shift (c (e n)) (x (e n))) (shift (c (e n)) p) S := by
      rw [hpq]
      exact hXS
    have heq := maximal_agreement_recenter D (T (e n)) (Q (e n)) (x (e n)) p
      (c (e n)) (hmax (e n)) S (by rwa [← hVeq]) hSQ hSe hSf hSagree
    exact heq.trans (hVeq n).symm
  let W := stepWindow (V 0) u
  have hbad (n : ℕ) : ∃ z ∈ W, X n z ≠ q z :=
    maximal_window_has_fixed_seed_defect θ code hcode hs hne hind hann (X n) q
      (hX n) (languageHull_trans hpHull hqmem) D (V n) (V 0) (Q' n) u hdirs
      (hVenv n) (hVfaces n) (hVenv 0) (hVfaces 0) (hVmono 0 n (Nat.zero_le n))
      (hUz (b 0)) (hcout (e n)) hu huD hnuD (hQ' n) (hVQ n) (hQ'forward n)
      (hXagree n) (hXmax n)
  let R := increasingRegion V
  have hRenv : IsEnvelope D R := increasingRegion_isEnvelope D V hVenv hVmono
  have hRfaces : LongFaces D R := increasingRegion_longFaces D V hVfaces
  have hRzero : 0 ∈ R := ⟨0,hUz (b 0)⟩
  have hRout : u ∉ R := by rintro ⟨n,hn⟩; exact hcout (e n) hn
  have hRback (n : ℕ) : -(n•u) ∈ R := ⟨n,hcback (e n) n (he.id_le n)⟩
  have hRhalf (z : Lattice) (hz : z ∈ R) : 0 ≤ det u z := by
    obtain ⟨n,hn⟩ := hz
    exact hVhalf n z hn
  have hRheight (N : ℤ) : ∃ z ∈ R, N ≤ det u z := by
    obtain ⟨n,hn⟩ := exists_nat_gt N
    refine ⟨(e n)•k-c (e n),⟨n,?_⟩,?_⟩
    · change (e n)•k-c (e n) ∈ recenterWindow (T (e n)) (c (e n))
      simpa only [mem_recenterWindow,sub_add_cancel] using hheight (e n)
    · rw [hcheight,det_nsmul_right]
      have hne' : (n:ℤ) ≤ e n := by exact_mod_cast he.id_le n
      have hnonneg : (0:ℤ) ≤ e n := by omega
      nlinarith
  have hcover (S : Finset Lattice) (hS : (S : Set Lattice) ⊆ {z | 0 ≤ det u z}) :
      ∀ᶠ n : ℕ in Filter.atTop, (S : Set Lattice) ⊆ Q' n :=
    eventually_finite_subset_ambient D V hVmono hRenv u k huk hRzero hRback hRheight
      Q' hVQ hQ'forward S hS
  obtain ⟨y,hy,hyq,⟨zbad,hzbad,hybad⟩,hlimitmax⟩ :=
    limit_with_finite_defect_and_maximality θ q code hcode hs hne hind hann
      (languageHull_trans hpHull hqmem) D hdirs V hVmono hVenv hVfaces Q' hQ' hVQ
      {z | 0 ≤ det u z} hcover X hX hXagree hXmax W hbad
  obtain ⟨d,hd,hud,hRu,hRd⟩ := exists_second_recession_direction D R hRenv u
    hRzero hRout hRback hRheight
  have hzbadhalf : 0 ≤ det u zbad :=
    stepWindow_in_bottom_halfPlane (V 0) u (hVhalf 0) zbad hzbad
  refine ⟨y,hy,q,hqmem,R,⟨c (a 0),hcu (a 0),(hq 0).symm⟩,
    hqp,hyq,hRenv,hRfaces,hRenv.latticeConvex,hRzero,hRout,hRhalf,hRback,hRheight,
    ⟨d,hd,hud,hRu,hRd⟩,⟨zbad,hzbadhalf,hybad⟩,hlimitmax,?_⟩
  intro F hF
  obtain ⟨N,hN⟩ := finite_subset_in_increasing_region V hVmono F hF
  exact ⟨V N,hN,fun z hz => ⟨N,hz⟩,hVenv N,hVfaces N,hUz (b N)⟩

end
end NivatTrial.ColleDefectiveGrowingEnvelopes
