import NivatTrial.NonexpansiveExistence

/-! A non-doubly-periodic configuration with a doubly-periodic hull point has
an actual interface limit: a hull point agrees with a periodic orbit point on
a closed half-plane but differs elsewhere. This is a compactness precursor to
Colle's maximal regional extraction; it does not assert that the interface
point is itself aperiodic. -/

namespace NivatTrial.PeriodicInterface

open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.NonexpansiveGeometry
open NivatTrial.NonexpansiveExistence NivatTrial.Periodicity
open Set Filter Topology
open scoped Classical
noncomputable section

variable {A : Type*} [Fintype A]

theorem recentered_periodic_disagreement (θ p : Lattice → A)
    (hp : p ∈ languageHull θ) (hpDP : IsDoublyPeriodic p)
    (hθ : ¬IsDoublyPeriodic θ) (n : ℕ) :
    ∃ x ∈ languageHull θ, ∃ y ∈ languageHull θ, ∃ w : Lattice,
      x 0 ≠ y 0 ∧ w ≠ 0 ∧ (n : ℝ) < radius w ∧
      x ∈ orbit p ∧
      ∀ z, energy (w + z) < energy w → x z = y z := by
  obtain ⟨u, hu⟩ := hp (box n)
  have hy : shift u θ ∈ languageHull θ := shift_mem_languageHull (self_mem_languageHull θ) u
  have hne : p ≠ shift u θ := by
    intro heq
    apply hθ
    have hdp : IsDoublyPeriodic (shift u θ) := heq ▸ hpDP
    simpa using hdp.shift (-u)
  obtain ⟨w, hw, hmin⟩ := nearest_disagreement p (shift u θ) hne
  have hwbox : w ∉ box n := by
    intro hwb
    exact hw (by simpa [shift] using (hu w hwb).symm)
  have hw0 : w ≠ 0 := by
    intro hz
    apply hwbox
    rw [hz]
    apply mem_box_of_energy_le
    simp
  refine ⟨shift w p,shift_mem_languageHull hp w,
    shift w (shift u θ),shift_mem_languageHull hy w,w,?_,hw0,
    radius_gt_of_not_mem_box hwbox,shift_mem_orbit p w,?_⟩
  · simpa [shift] using hw
  · intro z hz
    exact hmin (w+z) hz

/-- The nearest-disagreement construction yields an open-half-plane interface
with the periodic reference still in its genuine finite orbit. -/
theorem exists_open_periodic_interface (θ p : Lattice → A)
    (hp : p ∈ languageHull θ) (hpDP : IsDoublyPeriodic p)
    (hθ : ¬IsDoublyPeriodic θ) :
    ∃ v : Plane, v ≠ 0 ∧ ∃ x ∈ orbit p, ∃ y ∈ languageHull θ,
      x 0 ≠ y 0 ∧ ∀ z, 0 < score v z → x z = y z := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  choose x hx y hy w hd hw hr hxp ha using
    (recentered_periodic_disagreement θ p hp hpDP hθ)
  let seq (n : ℕ) := ((x n,y n),normal (w n))
  have hc : IsCompact ((languageHull θ ×ˢ languageHull θ) ×ˢ
      Set.Icc ((-1:ℝ),(-1:ℝ)) (1,1)) :=
    ((isCompact_languageHull θ).prod (isCompact_languageHull θ)).prod isCompact_Icc
  have hmem (n : ℕ) : seq n ∈ ((languageHull θ ×ˢ languageHull θ) ×ˢ
      Set.Icc ((-1:ℝ),(-1:ℝ)) (1,1)) :=
    ⟨⟨hx n,hy n⟩,normal_bounds (hw n)⟩
  obtain ⟨r,hrmem,φ,hφ,hlim⟩ := hc.tendsto_subseq hmem
  have hnorm : Tendsto (fun n => normal (w (φ n))) atTop (𝓝 r.2) :=
    (continuous_snd.tendsto r).comp hlim
  have hunit : r.2.1^2 + r.2.2^2 = 1 := by
    have hclosed : IsClosed {v : Plane | v.1^2+v.2^2=(1:ℝ)} :=
      isClosed_eq (by fun_prop) continuous_const
    exact hclosed.mem_of_tendsto hnorm
      (Eventually.of_forall (fun n => normal_unit (hw (φ n))))
  have hv : r.2 ≠ 0 := by
    intro he
    rw [he] at hunit
    norm_num at hunit
  have hxlim : Tendsto (fun n => x (φ n)) atTop (𝓝 r.1.1) :=
    ((continuous_fst.comp continuous_fst).tendsto r).comp hlim
  have hylim : Tendsto (fun n => y (φ n)) atTop (𝓝 r.1.2) :=
    ((continuous_snd.comp continuous_fst).tendsto r).comp hlim
  have hxp' : r.1.1 ∈ orbit p := by
    have hclosed : IsClosed (orbit p) := (finite_orbit_of_doublyPeriodic p hpDP).isClosed
    exact hclosed.mem_of_tendsto hxlim
      (Eventually.of_forall (fun n => hxp (φ n)))
  have hbad : r.1.1 0 ≠ r.1.2 0 := by
    intro he
    obtain ⟨n,hnx,hny⟩ := ((eventually_coordinate_eq hxlim 0).and
      (eventually_coordinate_eq hylim 0)).exists
    exact hd (φ n) (hnx.trans (he.trans hny.symm))
  refine ⟨r.2,hv,r.1.1,hxp',r.1.2,hrmem.1.2,hbad,?_⟩
  intro z hz
  have hscorelim : Tendsto (fun n => score (normal (w (φ n))) z) atTop
      (𝓝 (score r.2 z)) := (continuous_score z).continuousAt.tendsto.comp hnorm
  have hscore : ∀ᶠ n in atTop, score r.2 z / 2 < score (normal (w (φ n))) z :=
    hscorelim.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨N, hN⟩ := exists_nat_gt ((energy z : ℝ) / score r.2 z)
  have hbound : ∀ᶠ n in atTop, N ≤ φ n :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
  have heq : ∀ᶠ n in atTop, x (φ n) z = y (φ n) z := by
    filter_upwards [hscore,hbound] with n hsn hbn
    apply ha (φ n) z
    apply energy_add_lt (hw (φ n))
    have hNcast : (N:ℝ) ≤ φ n := by exact_mod_cast hbn
    have hlarge : (energy z:ℝ) < radius (w (φ n)) * score r.2 z := by
      have hmul := (div_lt_iff₀ hz).mp hN
      have hrn := hr (φ n)
      nlinarith
    have hpos := radius_pos (hw (φ n))
    nlinarith
  obtain ⟨n,hnx,hny,hnxy⟩ := ((eventually_coordinate_eq hxlim z).and
    ((eventually_coordinate_eq hylim z).and heq)).exists
  exact hnx.symm.trans (hnxy.trans hny)

/-- Shift the open interface inward by a lattice vector to obtain agreement
on the *closed* half-plane used by ONED. -/
theorem exists_periodic_interface (θ p : Lattice → A)
    (hp : p ∈ languageHull θ) (hpDP : IsDoublyPeriodic p)
    (hθ : ¬IsDoublyPeriodic θ) :
    ∃ v : Plane, v ≠ 0 ∧ ∃ x ∈ orbit p, ∃ y ∈ languageHull θ,
      x ≠ y ∧ AgreeOn x y (halfPlane v 0) := by
  obtain ⟨v,hv,x,hx,y,hy,hbad,hagree⟩ :=
    exists_open_periodic_interface θ p hp hpDP hθ
  obtain ⟨g,hg⟩ := exists_positive_score hv
  have hxshift : shift g x ∈ orbit p := by
    obtain ⟨k,hk⟩ := hx
    exact ⟨g+k, by rw [← hk]; exact shift_add g k p⟩
  refine ⟨v,hv,shift g x,hxshift,shift g y,shift_mem_languageHull hy g,?_,?_⟩
  · intro he
    exact hbad (congrFun (shift_injective g he) 0)
  · intro z hz
    apply hagree (g+z)
    change 0 ≤ score v z at hz
    rw [score_add]
    linarith

end

end NivatTrial.PeriodicInterface
