import NivatTrial.FiniteDetermination
import NivatTrial.Divisibility
import NivatTrial.PeriodicDifference

/-! A finite coding patch on a positive half-plane propagates equality to
the opposite half-plane. Periodicity of the difference reduces the initial
infinite band to finitely many lattice representatives. -/

namespace NivatTrial.PeriodicBandCoding

open NivatTrial.Geometry NivatTrial.Nonexpansive NivatTrial.Divisibility
open NivatTrial.Periodicity NivatTrial.PeriodicDifference NivatTrial.Dynamics
open NivatTrial.AmbiguityPropagation NivatTrial.FiniteDetermination
open scoped Classical
noncomputable section

theorem finite_band_representatives (h d : Lattice) (hdet : Geometry.det h d ≠ 0)
    (v : Plane) (hh : score v h = 0) (hd : 0 < score v d) (a b : ℝ) :
    ∃ S : Finset Lattice, ∀ z, a ≤ score v z → score v z ≤ b →
      ∃ s ∈ S, ∃ m : ℤ, z = s + m • h := by
  let D := (fundamentalDomain_finite h d hdet).toFinset
  let I (r : Lattice) : Finset ℤ :=
    Finset.Icc ⌈(a-score v r)/score v d⌉ ⌊(b-score v r)/score v d⌋
  let S := D.biUnion (fun r => (I r).image (fun n => r+n•d))
  refine ⟨S,?_⟩
  intro z hza hzb
  obtain ⟨r,m,n,hz⟩ := fundamentalDomain_representatives h d hdet z
  have he : score v z = score v r + (n:ℝ)*score v d := by
    rw [hz,score_add,score_add,score_zsmul,score_zsmul,hh,mul_zero,add_zero]
  have hnlo : (a-score v r)/score v d ≤ (n:ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hnhi : (n:ℝ) ≤ (b-score v r)/score v d := by
    apply (le_div_iff₀ hd).mpr
    linarith
  have hni : n ∈ I r := by
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr hnlo,Int.le_floor.mpr hnhi⟩
  refine ⟨(r:Lattice)+n•d,?_,m,?_⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨r,?_,Finset.mem_image.mpr ⟨n,hni,rfl⟩⟩
    simp [D]
  · rw [hz]
    abel

theorem score_bounds (S : Finset Lattice) (v : Plane)
    (hS : ∀ s ∈ S, 0 < score v s) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ s ∈ S, δ ≤ score v s ∧ score v s ≤ M := by
  by_cases hne : S.Nonempty
  · obtain ⟨s,hs,hmin⟩ := Finset.exists_min_image S (score v) hne
    obtain ⟨t,ht,hmax⟩ := Finset.exists_max_image S (score v) hne
    exact ⟨score v s,hS s hs,score v t,(hS t ht).le,fun z hz => ⟨hmin z hz,hmax z hz⟩⟩
  · refine ⟨1,by norm_num,0,le_rfl,?_⟩
    intro s hs
    exact (hne ⟨s,hs⟩).elim

variable {A : Type*} [Fintype A]

omit [Fintype A] in
/-- The finite positive coding rule propagates a complete band downwards.
The height parameter is real; rationality is not required for this step. -/
theorem band_codes_lower_halfPlane {θ x y : Lattice → A}
    (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (S : Finset Lattice) (v : Plane) (δ M : ℝ) (hδ : 0 < δ)
    (hS : ∀ s ∈ S, δ ≤ score v s ∧ score v s ≤ M)
    (hdet : Determines θ S 0)
    (hband : ∀ z, 0 ≤ score v z → score v z ≤ M → x z = y z) :
    ∀ z, score v z ≤ M → x z = y z := by
  have hall (n : ℕ) : ∀ z, -(n:ℝ)*δ ≤ score v z → score v z ≤ M → x z = y z := by
    induction n with
    | zero => simpa using hband
    | succ n ih =>
      intro z hz hM
      by_cases hz0 : 0 ≤ score v z
      · exact hband z hz0 hM
      · have hpat : patternAt x S z = patternAt y S z := by
          funext s
          apply ih (z+s.val)
          · rw [score_add]
            have hs := (hS s s.property).1
            push_cast at hz
            nlinarith
          · rw [score_add]
            have hs := (hS s s.property).2
            linarith
        simpa using hdet x hx y hy z z hpat
  intro z hz
  obtain ⟨n,hn⟩ := exists_nat_gt (-score v z / δ)
  have hn' := (div_lt_iff₀ hδ).mp hn
  exact hall n z (by linarith) hz

/-- One common increment plus a finite patch determines the whole lower
half-plane, uniformly for every pair in the same language hull. -/
theorem exists_finite_fiber_coding (θ : Lattice → A) (w : A → ℤ)
    (hw : Function.Injective w) (v : Plane) (hv : v ≠ 0)
    (hexp : OneSidedExpansive θ v) (h d : Lattice)
    (hdet : Geometry.det h d ≠ 0) (hh : score v h = 0) (hd : 0 < score v d) :
    ∃ B : Finset Lattice, ∀ x ∈ languageHull θ, ∀ y ∈ languageHull θ,
      increment (encode w x) h = increment (encode w y) h →
      (∀ b ∈ B, x b = y b) → ∀ z, score v z ≤ 0 → x z = y z := by
  obtain ⟨S,hS,hcode⟩ := exists_finite_positive_coding hv hexp
  obtain ⟨δ,hδ,M,hM,hbounds⟩ := score_bounds S v hS
  obtain ⟨B,hB⟩ := finite_band_representatives h d hdet v hh hd 0 M
  refine ⟨B,?_⟩
  intro x hx y hy hinc hagree
  have hp : IsPeriod (encode w x - encode w y) h := by
    intro z
    have he := congrFun hinc z
    change w (x (z+h))-w (x z) = w (y (z+h))-w (y z) at he
    change w (x (z+h))-w (y (z+h)) = w (x z)-w (y z)
    omega
  have hband : ∀ z, 0 ≤ score v z → score v z ≤ M → x z = y z := by
    intro z hz0 hzM
    obtain ⟨b,hb,m,hz⟩ := hB z hz0 hzM
    have he := hp.zsmul m b
    rw [← hz] at he
    have he0 : (encode w x - encode w y) b = 0 := by
      change w (x b)-w (y b) = 0
      rw [hagree b hb,sub_self]
    rw [he0] at he
    exact hw (sub_eq_zero.mp he)
  intro z hz
  exact band_codes_lower_halfPlane hx hy S v δ M hδ hbounds hcode hband z (hz.trans hM)

end
end NivatTrial.PeriodicBandCoding
