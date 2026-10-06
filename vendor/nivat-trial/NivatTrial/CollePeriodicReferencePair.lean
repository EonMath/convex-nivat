import NivatTrial.ColleWitnessHalfPlane
import NivatTrial.ColleBoundaryLimits
import NivatTrial.ColleGeneratingTransforms

/-! The two actual witnesses at a horizontal nonexpansive interface keep
their last disagreement while their lower-half-plane periods become global
periods through the proved integer decomposition theorem. -/

namespace NivatTrial.CollePeriodicReferencePair

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.Periodicity NivatTrial.ExternalInputs
open NivatTrial.BalancedWindows NivatTrial.ColleGenerating
open NivatTrial.ColleBalancedRows NivatTrial.ColleWitnessHalfPlane
open NivatTrial.ColleBoundaryLimits
open NivatTrial.ColleGeneratingTransforms NivatTrial.LatticeCoordinates
open scoped Classical
noncomputable section

def reflectIntegerDecomposition {M m : ℕ} {θ : Lattice → Fin M}
    (E : IntegerDecomposition (integerField θ) m) :
    IntegerDecomposition (integerField (θ ∘ reflectY)) m where
  component i := E.component i ∘ reflectY
  period i := reflectY (E.period i)
  period_ne_zero i := by
    intro he
    exact E.period_ne_zero i
      (reflectY.injective (by simpa only [map_zero] using he))
  independent i j hij := by
    have h := E.independent i j hij
    simp [Geometry.det] at h ⊢
    omega
  component_period i := by
    intro z
    change E.component i (reflectY (z + reflectY (E.period i))) =
      E.component i (reflectY z)
    simpa [map_add] using E.component_period i (reflectY z)
  sum_eq := by
    funext z
    have hz := congrFun E.sum_eq (reflectY z)
    simpa [integerField, encode, Finset.sum_apply, Function.comp_def] using hz

theorem horizontal_ONED_has_globally_periodic_interface_pair {M m : ℕ}
    (θ : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) m)
    (B : Finset Lattice) (hgen : GeneratingWindow θ B)
    (hminus : MinusBalanced θ B)
    (honed : OneSidedNonexpansive θ (1,0)) :
    ∃ x ∈ languageHull θ, ∃ y ∈ languageHull θ,
      ∃ d : ℤ, ∃ w : Lattice,
      w.2 = d ∧ x w ≠ y w ∧
      (∀ z : Lattice, 0 ≤ z.2 → x z = y z) ∧
      (∀ z : Lattice, d < z.2 → x z = y z) ∧
      HasIntegerDecomposition (integerField x) m ∧
      HasIntegerDecomposition (integerField y) m ∧
      ∃ P : ℕ, 0 < P ∧
        IsPeriod x (P • ((1,0) : Lattice)) ∧
        IsPeriod y (P • ((1,0) : Lattice)) := by
  obtain ⟨x,hx,y,hy,d,w,hw,hwne,hupper,hhighest,hQ,hxlower,hylower⟩ :=
    horizontal_ONED_has_periodic_interface_pair θ B hgen hminus honed
  let u : Lattice := (1,0)
  let Q : ℕ := Nat.factorial (2*((bottomEdge B).card-1))
  let b : ℤ := -(d+upper B-lower B)
  have hu : -u ≠ 0 := by simp [u]
  have ha : det (-u) (Q•u) = 0 := by simp [det,u]
  have hXreg : ∀ z, b ≤ det (-u) z → x (z+Q•u) = x z := by
    intro z hz
    have hr : z.2 ≤ d+upper B-lower B := by
      simp [b,det,u] at hz
      omega
    have hh := hxlower z hr
    change x (z+Q•u) = x z at hh
    exact hh
  have hYreg : ∀ z, b ≤ det (-u) z → y (z+Q•u) = y z := by
    intro z hz
    have hr : z.2 ≤ d+upper B-lower B := by
      simp [b,det,u] at hz
      omega
    have hh := hylower z hr
    change y (z+Q•u) = y z at hh
    exact hh
  obtain ⟨Kx,hKx,hXp⟩ :=
    global_period_of_integer_hull_halfPlane_period E hx (-u) hu
      (Q•u) ha b hXreg
  obtain ⟨Ky,hKy,hYp⟩ :=
    global_period_of_integer_hull_halfPlane_period E hy (-u) hu
      (Q•u) ha b hYreg
  let P : ℕ := Kx*Ky*Q
  have hP : 0 < P := mul_pos (mul_pos hKx hKy) hQ
  have hXpP : IsPeriod x (P•u) := by
    have h := hXp.nsmul Ky
    simpa [P,smul_smul,mul_comm,mul_left_comm,mul_assoc] using h
  have hYpP : IsPeriod y (P•u) := by
    have h := hYp.nsmul Kx
    simpa [P,smul_smul,mul_comm,mul_left_comm,mul_assoc] using h
  exact ⟨x,hx,y,hy,d,w,hw,hwne,hupper,hhighest,
    decomposition_in_languageHull E hx,
    decomposition_in_languageHull E hy,
    P,hP,hXpP,hYpP⟩

/-- The original convex low-complexity window chooses one balanced extreme
edge. Reflection handles the upper-edge case while returning both actual
periodic witnesses and their disagreement site to the original field. -/
theorem low_complexity_has_globally_periodic_interface_pair {M m : ℕ}
    (θ : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) m)
    (S : Finset Lattice) (hS : NivatTrial.LatticePolygon.IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card)
    (hpos : OneSidedNonexpansive θ (1,0))
    (hneg : OneSidedNonexpansive θ (-1,0)) :
    ∃ x ∈ languageHull θ, ∃ y ∈ languageHull θ,
      ∃ d : ℤ, ∃ w : Lattice,
      w.2 = d ∧ x w ≠ y w ∧
      (((∀ z : Lattice, 0 ≤ z.2 → x z = y z) ∧
        (∀ z : Lattice, d < z.2 → x z = y z)) ∨
       ((∀ z : Lattice, z.2 ≤ 0 → x z = y z) ∧
        (∀ z : Lattice, z.2 < d → x z = y z))) ∧
      ∃ P : ℕ, 0 < P ∧
        IsPeriod x (P • ((1,0) : Lattice)) ∧
        IsPeriod y (P • ((1,0) : Lattice)) := by
  obtain ⟨B,_,hgen,hlowB⟩ := exists_generating_window θ S hS hlow
  rcases generatingWindow_balanced_choice θ B hgen hlowB with hplus | hminus
  · let θ' := θ ∘ reflectY
    let B' := mapWindow reflectY B
    have hgen' : GeneratingWindow θ' B' :=
      NivatTrial.ColleGeneratingTransforms.GeneratingWindow.reflectY hgen
    have hminus' : MinusBalanced θ' B' :=
      NivatTrial.ColleGeneratingTransforms.PlusBalanced.reflectY_minus hplus
    have honed' : OneSidedNonexpansive θ' (1,0) :=
      oneSidedNonexpansive_reflectY_horizontal hneg
    obtain ⟨x',hx',y',hy',d',w',hw',hbad',hupper',hhighest',_,_,P,hP,hxP,hyP⟩ :=
      horizontal_ONED_has_globally_periodic_interface_pair θ'
        (reflectIntegerDecomposition E) B' hgen' hminus' honed'
    let x := x' ∘ reflectY
    let y := y' ∘ reflectY
    let w := reflectY w'
    have hx : x ∈ languageHull θ := by
      have hh := mem_languageHull_reflectY hx'
      simpa [x, θ', Function.comp_def] using hh
    have hy : y ∈ languageHull θ := by
      have hh := mem_languageHull_reflectY hy'
      simpa [y, θ', Function.comp_def] using hh
    have hw : w.2 = -d' := by simp [w,hw']
    have hbad : x w ≠ y w := by
      simpa [x,y,w,Function.comp_def] using hbad'
    have hbelow : ∀ z : Lattice, z.2 ≤ 0 → x z = y z := by
      intro z hz
      have hz' : 0 ≤ (reflectY z).2 := by simpa using hz
      exact hupper' (reflectY z) hz'
    have hlast : ∀ z : Lattice, z.2 < -d' → x z = y z := by
      intro z hz
      have hz' : d' < (reflectY z).2 := by simp; omega
      exact hhighest' (reflectY z) hz'
    have hxPeriod : IsPeriod x (P • ((1,0) : Lattice)) := by
      apply (isPeriod_comp_iff reflectY x' _).mpr
      simpa [map_nsmul] using hxP
    have hyPeriod : IsPeriod y (P • ((1,0) : Lattice)) := by
      apply (isPeriod_comp_iff reflectY y' _).mpr
      simpa [map_nsmul] using hyP
    exact ⟨x,hx,y,hy,-d',w,hw,hbad,Or.inr ⟨hbelow,hlast⟩,
      P,hP,hxPeriod,hyPeriod⟩
  · obtain ⟨x,hx,y,hy,d,w,hw,hbad,hupper,hhighest,_,_,P,hP,hxP,hyP⟩ :=
      horizontal_ONED_has_globally_periodic_interface_pair θ E B hgen hminus hpos
    exact ⟨x,hx,y,hy,d,w,hw,hbad,Or.inl ⟨hupper,hhighest⟩,
      P,hP,hxP,hyP⟩

end
end NivatTrial.CollePeriodicReferencePair
