import NivatTrial.NonexpansiveExistence
import NivatTrial.ColleRegions

/-! The compactness step of Colle's Lemma 3.5, separated from the finite
enveloped-window construction: expanding actual hull patches with one fixed
disagreement have a genuine limit with that disagreement. -/

namespace NivatTrial.ColleRegionCompactness

open NivatTrial.Dynamics NivatTrial.NonexpansiveGeometry
open NivatTrial.NonexpansiveExistence NivatTrial.Nonexpansive
open NivatTrial.Periodicity NivatTrial.RegionGeometry
open Set Filter Topology
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

theorem box_mono {n m : ℕ} (hnm : n ≤ m) : box n ⊆ box m := by
  intro z hz
  change z ∈ Finset.Icc (-((m:ℤ),(m:ℤ))) ((m:ℤ),(m:ℤ))
  change z ∈ Finset.Icc (-((n:ℤ),(n:ℤ))) ((n:ℤ),(n:ℤ)) at hz
  rw [Finset.mem_Icc] at hz ⊢
  change (-(n:ℤ) ≤ z.1 ∧ -(n:ℤ) ≤ z.2) ∧
    (z.1 ≤ (n:ℤ) ∧ z.2 ≤ (n:ℤ)) at hz
  change (-(m:ℤ) ≤ z.1 ∧ -(m:ℤ) ≤ z.2) ∧
    (z.1 ≤ (m:ℤ) ∧ z.2 ≤ (m:ℤ))
  omega

theorem eventually_mem_box (z : G) :
    ∀ᶠ n : ℕ in atTop, z ∈ box n := by
  let N := energy z + 1
  have hN : z ∈ box N := by
    apply mem_box_of_energy_le
    dsimp [N]
    nlinarith [Nat.zero_le (energy z)]
  filter_upwards [eventually_ge_atTop N] with n hn
  exact box_mono hn hN

variable {A : Type*} [Fintype A]

/-- A fixed defect cannot disappear in an orbit-limit while agreement grows
on every finite part of a prescribed region. -/
theorem limit_of_expanding_agreement
    (θ p : G → A) (R : Set G) (w : G)
    (hpatch : ∀ n : ℕ, ∃ x ∈ languageHull θ,
      (∀ z ∈ R, z ∈ box n → x z = p z) ∧ x w ≠ p w) :
    ∃ y ∈ languageHull θ, AgreeOn y p R ∧ y w ≠ p w := by
  choose x hx hagree hbad using hpatch
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨y,hy,φ,hφ,hlim⟩ := (isCompact_languageHull θ).tendsto_subseq hx
  refine ⟨y,hy,?_,?_⟩
  · intro z hz
    have hevent : ∀ᶠ n : ℕ in atTop, z ∈ box (φ n) :=
      hφ.tendsto_atTop.eventually (eventually_mem_box z)
    obtain ⟨n,hnbox,hneq⟩ :=
      (hevent.and (eventually_coordinate_eq hlim z)).exists
    exact hneq.symm.trans (hagree (φ n) z hz hnbox)
  · intro he
    obtain ⟨n,hn⟩ := (eventually_coordinate_eq hlim w).exists
    exact hbad (φ n) (hn.trans he)

/-- The same limit keeps any finite collection of individually pinned
period defects. -/
theorem limit_of_expanding_agreement_with_defects
    (θ p : G → A) (R : Set G) (E : Finset G) (site : G → G)
    (hpatch : ∀ n : ℕ, ∃ x ∈ languageHull θ,
      (∀ z ∈ R, z ∈ box n → x z = p z) ∧
      ∀ h ∈ E, x (site h + h) ≠ x (site h)) :
    ∃ y ∈ languageHull θ, AgreeOn y p R ∧
      ∀ h ∈ E, y (site h + h) ≠ y (site h) := by
  choose x hx hlocal hbad using hpatch
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨y,hy,φ,hφ,hlim⟩ := (isCompact_languageHull θ).tendsto_subseq hx
  refine ⟨y,hy,?_,?_⟩
  · intro z hz
    have hevent : ∀ᶠ n : ℕ in atTop, z ∈ box (φ n) :=
      hφ.tendsto_atTop.eventually (eventually_mem_box z)
    obtain ⟨n,hnbox,hneq⟩ :=
      (hevent.and (eventually_coordinate_eq hlim z)).exists
    exact hneq.symm.trans (hlocal (φ n) z hz hnbox)
  · intro h hh he
    obtain ⟨n,hn1,hn2⟩ :=
      ((eventually_coordinate_eq hlim (site h+h)).and
        (eventually_coordinate_eq hlim (site h))).exists
    exact hbad (φ n) h hh (hn1.trans (he.trans hn2.symm))

end

end NivatTrial.ColleRegionCompactness
