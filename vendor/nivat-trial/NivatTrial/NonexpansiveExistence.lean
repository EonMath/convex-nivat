import NivatTrial.NonexpansiveGeometry
import NivatTrial.Periodicity
import Mathlib.Topology.Sequences

/-! An infinite two-dimensional finite-alphabet orbit closure has a one-sided
nonexpansive direction. We recenter the nearest disagreement, then pass to a
limit of the configurations and of the inward unit normals. -/

namespace NivatTrial.NonexpansiveExistence

open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.NonexpansiveGeometry
open Set Filter Topology
open scoped Classical
noncomputable section

variable {A : Type*}

theorem ambiguous_window [Fintype A] (θ : Lattice → A)
    (hθ : (languageHull θ).Infinite) (S : Finset Lattice) :
    ∃ x ∈ languageHull θ, ∃ y ∈ languageHull θ,
      x ≠ y ∧ ∀ z ∈ S, x z = y z := by
  let p : languageHull θ → (S → A) := fun x z => x.val z.val
  have hn : ¬Function.Injective p := by
    intro hi
    have : Finite (languageHull θ) := Finite.of_injective p hi
    exact hθ (Set.toFinite (languageHull θ))
  obtain ⟨x,y,hxy,hne⟩ := Function.not_injective_iff.mp hn
  refine ⟨x,x.property,y,y.property,fun he => hne (Subtype.ext he),?_⟩
  intro z hz
  exact congrFun hxy ⟨z,hz⟩

theorem nearest_disagreement (x y : Lattice → A) (hne : x ≠ y) :
    ∃ w : Lattice, x w ≠ y w ∧ ∀ z, energy z < energy w → x z = y z := by
  have hex : ∃ n : ℕ, ∃ w : Lattice, energy w = n ∧ x w ≠ y w := by
    obtain ⟨w,hw⟩ := Function.ne_iff.mp hne
    exact ⟨energy w,w,rfl,hw⟩
  obtain ⟨w,hw,hd⟩ := Nat.find_spec hex
  refine ⟨w,hd,?_⟩
  intro z hz
  by_contra hd'
  have he := Nat.find_min' hex ⟨z,rfl,hd'⟩
  omega

theorem recentered_ambiguity [Fintype A] (θ : Lattice → A)
    (hθ : (languageHull θ).Infinite) (n : ℕ) :
    ∃ x ∈ languageHull θ, ∃ y ∈ languageHull θ, ∃ w : Lattice,
      x 0 ≠ y 0 ∧ w ≠ 0 ∧ (n:ℝ) < radius w ∧
      ∀ z, energy (w+z) < energy w → x z = y z := by
  obtain ⟨x,hx,y,hy,hne,hagree⟩ := ambiguous_window θ hθ (box n)
  obtain ⟨w,hw,hmin⟩ := nearest_disagreement x y hne
  have hwbox : w ∉ box n := fun h => hw (hagree w h)
  have hw0 : w ≠ 0 := by
    intro hz
    apply hwbox
    rw [hz]
    apply mem_box_of_energy_le
    simp
  refine ⟨shift w x,shift_mem_languageHull hx w,
    shift w y,shift_mem_languageHull hy w,w,?_,hw0,
    radius_gt_of_not_mem_box hwbox,?_⟩
  · simpa [shift] using hw
  · intro z hz
    exact hmin (w+z) hz

section Topology

variable [TopologicalSpace A] [DiscreteTopology A]

theorem eventually_coordinate_eq {x : ℕ → Lattice → A} {y : Lattice → A}
    (h : Tendsto x atTop (𝓝 y)) (z : Lattice) :
    ∀ᶠ n in atTop, x n z = y z := by
  exact (tendsto_pi_nhds.mp h z).eventually
    ((isOpen_discrete ({y z}:Set A)).mem_nhds rfl)

theorem isCompact_languageHull [Fintype A] (θ : Lattice → A) :
    IsCompact (languageHull θ) := by
  rw [← orbitClosure_eq_languageHull]
  exact (isClosed_orbitClosure θ).isCompact

end Topology

/-- The direction and both configurations are taken along the same convergent
subsequence. Disagreement at the origin survives because the alphabet is
discrete. -/
theorem exists_open_halfPlane_ambiguity [Fintype A] (θ : Lattice → A)
    (hθ : (languageHull θ).Infinite) :
    ∃ v : Plane, v ≠ 0 ∧ ∃ x ∈ languageHull θ, ∃ y ∈ languageHull θ,
      x 0 ≠ y 0 ∧ ∀ z, 0 < score v z → x z = y z := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  choose x hx y hy w hd hw hr ha using (recentered_ambiguity θ hθ)
  let seq (n : ℕ) := ((x n,y n),normal (w n))
  have hc : IsCompact ((languageHull θ ×ˢ languageHull θ) ×ˢ
      Set.Icc ((-1:ℝ),(-1:ℝ)) (1,1)) :=
    ((isCompact_languageHull θ).prod (isCompact_languageHull θ)).prod isCompact_Icc
  have hmem (n : ℕ) : seq n ∈ ((languageHull θ ×ˢ languageHull θ) ×ˢ
      Set.Icc ((-1:ℝ),(-1:ℝ)) (1,1)) :=
    ⟨⟨hx n,hy n⟩,normal_bounds (hw n)⟩
  obtain ⟨p,hp,φ,hφ,hlim⟩ := hc.tendsto_subseq hmem
  have hnorm : Tendsto (fun n => normal (w (φ n))) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hlim
  have hunit : p.2.1^2 + p.2.2^2 = 1 := by
    have hclosed : IsClosed {v : Plane | v.1^2+v.2^2=(1:ℝ)} :=
      isClosed_eq (by fun_prop) continuous_const
    exact hclosed.mem_of_tendsto hnorm (Eventually.of_forall (fun n => normal_unit (hw (φ n))))
  have hv : p.2 ≠ 0 := by
    intro he
    rw [he] at hunit
    norm_num at hunit
  have hxlim : Tendsto (fun n => x (φ n)) atTop (𝓝 p.1.1) :=
    ((continuous_fst.comp continuous_fst).tendsto p).comp hlim
  have hylim : Tendsto (fun n => y (φ n)) atTop (𝓝 p.1.2) :=
    ((continuous_snd.comp continuous_fst).tendsto p).comp hlim
  have hbad : p.1.1 0 ≠ p.1.2 0 := by
    intro he
    obtain ⟨n,hnx,hny⟩ := ((eventually_coordinate_eq hxlim 0).and
      (eventually_coordinate_eq hylim 0)).exists
    exact hd (φ n) (hnx.trans (he.trans hny.symm))
  refine ⟨p.2,hv,p.1.1,hp.1.1,p.1.2,hp.1.2,hbad,?_⟩
  intro z hz
  have hscorelim : Tendsto (fun n => score (normal (w (φ n))) z) atTop
      (𝓝 (score p.2 z)) := (continuous_score z).continuousAt.tendsto.comp hnorm
  have hscore : ∀ᶠ n in atTop, score p.2 z / 2 < score (normal (w (φ n))) z :=
    hscorelim.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨N,hN⟩ := exists_nat_gt ((energy z:ℝ) / score p.2 z)
  have hbound : ∀ᶠ n in atTop, N ≤ φ n :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
  have heq : ∀ᶠ n in atTop, x (φ n) z = y (φ n) z := by
    filter_upwards [hscore,hbound] with n hsn hbn
    apply ha (φ n) z
    apply energy_add_lt (hw (φ n))
    have hNcast : (N:ℝ) ≤ φ n := by exact_mod_cast hbn
    have hlarge : (energy z:ℝ) < radius (w (φ n)) * score p.2 z := by
      have hmul := (div_lt_iff₀ hz).mp hN
      have hrn := hr (φ n)
      nlinarith
    have hpos := radius_pos (hw (φ n))
    nlinarith
  obtain ⟨n,hnx,hny,hnxy⟩ := ((eventually_coordinate_eq hxlim z).and
    ((eventually_coordinate_eq hylim z).and heq)).exists
  exact hnx.symm.trans (hnxy.trans hny)

theorem exists_oneSidedNonexpansive_of_infinite [Fintype A] (θ : Lattice → A)
    (hθ : (languageHull θ).Infinite) :
    ∃ v : Plane, v ≠ 0 ∧ OneSidedNonexpansive θ v := by
  obtain ⟨v,hv,x,hx,y,hy,hbad,hagree⟩ := exists_open_halfPlane_ambiguity θ hθ
  obtain ⟨g,hg⟩ := exists_positive_score hv
  refine ⟨v,hv,shift g x,shift_mem_languageHull hx g,
    shift g y,shift_mem_languageHull hy g,?_,?_⟩
  · intro he
    exact hbad (congrFun (shift_injective g he) 0)
  · intro z hz
    apply hagree (g+z)
    change 0 ≤ score v z at hz
    rw [score_add]
    linarith

/-- The finite-alphabet two-dimensional consequence of the nonexpansive
subspace theorem needed by the regional argument. -/
theorem doublyPeriodic_of_all_oneSidedExpansive [Fintype A] (θ : Lattice → A)
    (hθ : ∀ v : Plane, v ≠ 0 → OneSidedExpansive θ v) :
    NivatTrial.Periodicity.IsDoublyPeriodic θ := by
  apply NivatTrial.Periodicity.doublyPeriodic_of_finite_orbit
  have hf : (languageHull θ).Finite := by
    by_contra hi
    obtain ⟨v,hv,h⟩ := exists_oneSidedNonexpansive_of_infinite θ hi
    exact hθ v hv h
  exact hf.subset (orbit_subset_languageHull θ)

end
end NivatTrial.NonexpansiveExistence
