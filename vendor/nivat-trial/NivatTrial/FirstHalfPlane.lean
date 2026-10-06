import NivatTrial.IncrementSupport

/-! The first periodic half-plane for every non-doubly-periodic summand.
Entry along the sum of two regional periods replaces recession-cone geometry. -/

namespace NivatTrial.FirstHalfPlane

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.RegionGeometry NivatTrial.IncrementSupport
open scoped Classical

noncomputable section

def height (v : Lattice) : Lattice →+ ℤ where
  toFun := det v
  map_zero' := det_zero_right v
  map_add' := det_add_right v

@[simp] theorem height_apply (v z : Lattice) : height v z = det v z := rfl

theorem det_neg_left (v w : Lattice) : det (-v) w = -det v w := by simp [det]; ring

variable {ι A : Type*} [Fintype ι] [Nontrivial ι] [AddCommGroup A] [Fintype A]

theorem component_tail (F : ι → Lattice → A) (h H : ι → Lattice)
    (hne : ∀ i, h i ≠ 0) (hp : ∀ i, IsPeriod (F i) (h i))
    (hHP : ∀ i, IsPeriod (F i) (H i))
    (htrans : ∀ i j, i ≠ j → det (h i) (H j) ≠ 0)
    (hndp : ∀ i, ¬IsDoublyPeriodic (F i))
    (R : Set Lattice) (g : Lattice)
    (hentry : ∀ z, ∃ N : ℕ, ∀ n ≥ N, z+n•g ∈ R)
    (B : Lattice → A) (hB : ∀ i, IsPeriod B (H i))
    (hagrees : ∀ z ∈ R, (∑ j, F j) z = B z) (i : ι) :
    ∃ v : Lattice, (v=h i ∨ v= -h i) ∧ 0 < det v g ∧ IsPeriod (F i) v ∧
      ∃ c : ℤ, ∃ η : Lattice → A, IsDoublyPeriodic η ∧
        ∀ z, c ≤ det v z → F i z=η z := by
  let hs := cofactorDirections H i
  let D := iteratedIncrement hs (F i)
  let R' := erosion R (offsets hs)
  have hDp : IsPeriod D (h i) := iteratedIncrement_period hs (hp i)
  have hDe : ∀ z, ∃ N : ℕ, ∀ n ≥ N, z+n•g ∈ R' := erosion_entry g hentry (offsets hs)
  have hDz : ∀ z ∈ R', D z=0 := by
    have hzero := zero_on_erosion hs (∑ j,F j) B R hagrees
      (cofactor_kills_background H B hB i)
    rw [cofactor_isolates F H hHP i] at hzero
    exact hzero
  have hT : ∀ d ∈ hs, height (h i) d ≠ 0 :=
    cofactor_transverse H i (height (h i)) (fun j hji => htrans i j hji.symm)
  have hgn : det (h i) g ≠ 0 := by
    intro hz
    obtain ⟨M,hM,hMg⟩ := parallel_direction_period hDp (hne i) g hz
    have hDzero := vanishing_global D R' g M hM hMg hDe hDz
    exact hndp i (doublyPeriodic_of_iteratedIncrement (height (h i)) (h i)
      (hne i) (det_self _) hs hT (F i) (hp i) hDzero)
  have step (v : Lattice) (hv : v=h i ∨ v= -h i) (hvg : 0 < det v g)
      (hvp : IsPeriod (F i) v) :
      ∃ v : Lattice, (v=h i ∨ v= -h i) ∧ 0 < det v g ∧ IsPeriod (F i) v ∧
        ∃ c : ℤ, ∃ η : Lattice → A, IsDoublyPeriodic η ∧
          ∀ z, c ≤ det v z → F i z=η z := by
    have hvn : v ≠ 0 := by intro he; simp [he, det] at hvg
    have hDv : IsPeriod D v := iteratedIncrement_period hs hvp
    obtain ⟨c,hzero⟩ := vanishing_halfplane D R' v g hDv hvg hDe hDz
    have hTv : ∀ d ∈ hs, height v d ≠ 0 := by
      intro d hd
      rcases hv with rfl | rfl
      · exact hT d hd
      · simpa only [height_apply, det_neg_left, neg_ne_zero] using hT d hd
    obtain ⟨b,q,hq,hqper⟩ := tail_period_of_iteratedIncrement (height v) v g hvn
      (det_self _) hvg hs hTv (F i) hvp c hzero
    have hqg : 0 < height v (q•g) := by
      rw [height_apply, det_nsmul_right]
      exact mul_pos (by exact_mod_cast hq) hvg
    obtain ⟨η,ha,hη⟩ := extension_of_positive_period (F i) (height v) b v (q•g)
      hvn (det_self _) hqg hvp hqper
    exact ⟨v,hv,hvg,hvp,b,η,hη,fun z hz => (ha z hz).symm⟩
  by_cases hgpos : 0 < det (h i) g
  · exact step (h i) (Or.inl rfl) hgpos (hp i)
  · apply step (-h i) (Or.inr rfl) _ (hp i).neg
    rw [det_neg_left]
    omega

/-- Proposition 8.9 in the form used by the remaining reduction: a common
strict interior direction and one actual doubly periodic tail per component. -/
theorem one_sided_tails (F : ι → Lattice → A) (h : ι → Lattice)
    (hne : ∀ i, h i ≠ 0) (hp : ∀ i, IsPeriod (F i) (h i))
    (hpair : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0)
    (hndp : ∀ i, ¬IsDoublyPeriodic (F i))
    (R : Set Lattice) (hR : LatticeConvexRegion R) (hRne : R.Nonempty)
    (a b : Lattice) (hab : det a b ≠ 0)
    (ha : PeriodicOn (∑ i,F i) R a) (hb : PeriodicOn (∑ i,F i) R b) :
    ∃ v : ι → Lattice, ∃ g : Lattice, ∃ c : ι → ℤ, ∃ η : ι → Lattice → A,
      (∀ i, v i=h i ∨ v i= -h i) ∧
      (∀ i, IsPeriod (F i) (v i)) ∧ (∀ i, 0 < det (v i) g) ∧
      (∀ i j, i ≠ j → det (v i) (v j) ≠ 0) ∧
      (∀ i, IsDoublyPeriodic (η i)) ∧ (∀ i z, c i ≤ det (v i) z → F i z=η i z) := by
  obtain ⟨B,hBR,_,_,hBdp⟩ := doublyPeriodic_extension (∑ i,F i) R hR hRne a b hab ha hb
  have hBfinite := finite_orbit_of_doublyPeriodic B hBdp
  choose M hM hMp using fun i => direction_period_of_finite_orbit B (h i) hBfinite
  let H := fun i => M i • h i
  have hHP : ∀ i, IsPeriod (F i) (H i) := fun i => (hp i).nsmul (M i)
  have htrans : ∀ i j, i ≠ j → det (h i) (H j) ≠ 0 := by
    intro i j hij
    rw [det_nsmul_right]
    exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt (hM j)) (hpair i j hij)
  have hentry := eventual_entry R hR hRne a b hab ha.1 hb.1
  have hcomp := component_tail F h H hne hp hHP htrans hndp R (a+b) hentry B hMp
    (fun z hz => (hBR z hz).symm)
  choose v hv hvg hvp c η hη hηa using hcomp
  refine ⟨v,a+b,c,η,hv,hvp,hvg,?_,hη,hηa⟩
  intro i j hij
  rcases hv i with hi | hi <;> rcases hv j with hj | hj <;>
    simpa only [hi,hj,det_neg_left,det_neg_right,neg_ne_zero] using hpair i j hij

end
end NivatTrial.FirstHalfPlane
