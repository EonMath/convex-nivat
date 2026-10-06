import NivatTrial.ColleProperPeriodicReference
import NivatTrial.ColleRegionalBranches

/-! Normalize the actual integer decomposition and the proper periodic
reference to the same oriented direction before entering the regional
dichotomy. A global sign reversal keeps every summand and independence. -/

namespace NivatTrial.ColleRegionalEntry

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Dynamics
open NivatTrial.Nonexpansive NivatTrial.Periodicity
open NivatTrial.ExternalInputs NivatTrial.ColleDecompositionTransforms
open NivatTrial.ColleCoordinateTransport NivatTrial.ColleIntegerOpposite
open NivatTrial.ColleProperPeriodicReference NivatTrial.ColleProperReferences
open NivatTrial.ColleRationalDirections NivatTrial.ColleRegionalBranches
open NivatTrial.LatticeCoordinates
open scoped Classical

noncomputable section

/-- Reversing every factor period keeps the actual integer summands and
their pairwise independence. -/
def reversePeriods {f : Lattice → ℤ} {n : ℕ}
    (E : IntegerDecomposition f n) : IntegerDecomposition f n where
  component := E.component
  period i := -E.period i
  period_ne_zero i := by
    intro h
    exact E.period_ne_zero i (neg_eq_zero.mp h)
  independent i j hij := by
    have h : det (-E.period i) (-E.period j) = det (E.period i) (E.period j) := by
      simp [det]
    rw [h]
    exact E.independent i j hij
  component_period i := (E.component_period i).neg
  sum_eq := E.sum_eq

@[simp] theorem reversePeriods_period {f : Lattice → ℤ} {n : ℕ}
    (E : IntegerDecomposition f n) (i : Fin n) :
    (reversePeriods E).period i = -E.period i := rfl

theorem horizontal_halfPlane_of_pos (u : Lattice)
    (hzero : u.2 = 0) (hpos : 0 < u.1) :
    halfPlane (embed u) 0 = halfPlane (1,0) 0 := by
  have he : embed u = (u.1 : ℝ) • ((1,0) : ℝ × ℝ) := by
    ext <;> simp [embed,hzero]
  rw [he]
  exact halfPlane_pos_smul (u.1 : ℝ) (by exact_mod_cast hpos) (1,0)

theorem horizontal_halfPlane_of_neg (u : Lattice)
    (hzero : u.2 = 0) (hneg : u.1 < 0) :
    halfPlane (embed u) 0 = halfPlane (-1,0) 0 := by
  have he : embed u = (-(u.1 : ℝ)) • ((-1,0) : ℝ × ℝ) := by
    ext <;> simp [embed,hzero]
  rw [he]
  exact halfPlane_pos_smul (-(u.1 : ℝ))
    (by exact_mod_cast (neg_pos.mpr hneg)) (-1,0)

/-- A horizontal factor period can be reversed so that its actual
oriented half-plane is precisely whichever side has no doubly periodic
extension. -/
theorem orient_proper_horizontal_period {M n : ℕ}
    {θ p : Lattice → Fin M}
    (E : IntegerDecomposition (integerField θ) n) (i : Fin n)
    (hzero : (E.period i).2 = 0) (hp : IsPeriod p (E.period i))
    (hproper :
      ¬HasDoublyPeriodicExtension p (halfPlane (1,0) 0) ∨
      ¬HasDoublyPeriodicExtension p (halfPlane (-1,0) 0)) :
    ∃ F : IntegerDecomposition (integerField θ) n,
      F.component = E.component ∧
      IsPeriod p (F.period i) ∧
      ¬HasDoublyPeriodicExtension p (halfPlane (embed (F.period i)) 0) := by
  have hfirst : (E.period i).1 ≠ 0 := by
    intro h
    exact E.period_ne_zero i (Prod.ext h hzero)
  rcases hproper with hpplus | hpminus
  · by_cases hpos : 0 < (E.period i).1
    · refine ⟨E,rfl,hp,?_⟩
      rw [horizontal_halfPlane_of_pos _ hzero hpos]
      exact hpplus
    · have hneg : (E.period i).1 < 0 := by omega
      refine ⟨reversePeriods E,rfl,?_,?_⟩
      · exact hp.neg
      · have hz : (-(E.period i)).2 = 0 := by simp [hzero]
        have hfirst' : 0 < (-(E.period i)).1 := by simpa using (neg_pos.mpr hneg)
        rw [reversePeriods_period,horizontal_halfPlane_of_pos _ hz hfirst']
        exact hpplus
  · by_cases hneg : (E.period i).1 < 0
    · refine ⟨E,rfl,hp,?_⟩
      rw [horizontal_halfPlane_of_neg _ hzero hneg]
      exact hpminus
    · have hpos : 0 < (E.period i).1 := by omega
      refine ⟨reversePeriods E,rfl,?_,?_⟩
      · exact hp.neg
      · have hz : (-(E.period i)).2 = 0 := by simp [hzero]
        have hfirst' : (-(E.period i)).1 < 0 := by simpa using (neg_neg_of_pos hpos)
        rw [reversePeriods_period,horizontal_halfPlane_of_neg _ hz hfirst']
        exact hpminus

/-- Scale the selected factor to an actual reference period, orient it to
the proper side, and invoke the genuine regional dichotomy. -/
theorem actual_regional_dichotomy_of_proper_horizontal_reference {M n : ℕ}
    (hn : 2 ≤ n) (θ p : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) n)
    (hpHull : p ∈ languageHull θ) (hnot : ¬IsPeriodic θ)
    (i : Fin n) (hzero : (E.period i).2 = 0)
    (q : ℕ) (hq : 0 < q) (hp : IsPeriod p (q • E.period i))
    (hproper :
      ¬HasDoublyPeriodicExtension p (halfPlane (1,0) 0) ∨
      ¬HasDoublyPeriodicExtension p (halfPlane (-1,0) 0)) :
    ∃ F : IntegerDecomposition (integerField θ) n,
      F.component = E.component ∧ IsPeriod p (F.period i) ∧
      ¬HasDoublyPeriodicExtension p (halfPlane (embed (F.period i)) 0) ∧
      (HasPeriodicWedge θ F.period (F.period i) ∨
       HasDefectiveHalfStripPatches θ p F.period i) := by
  obtain ⟨E₁,hcomponent,hper,heq,_⟩ :=
    exists_reference_normalized E p i q hq hp
  have hzero₁ : (E₁.period i).2 = 0 := by
    rw [heq]
    simp [hzero]
  obtain ⟨F,hFcomponent,hFperiod,hFproper⟩ :=
    orient_proper_horizontal_period E₁ i hzero₁ hper hproper
  have hbranch := actual_regional_dichotomy hn θ p F hpHull hnot i 1
    (by omega) (by simpa using hFperiod)
  exact ⟨F,hFcomponent.trans hcomponent,hFperiod,hFproper,hbranch⟩

/-- The complete initial reduction for Colle's regional argument. Low
convex complexity, aperiodicity, and an actual integer decomposition supply
both a proper periodic reference and the corresponding genuine region
dichotomy after an integral change of coordinates. -/
theorem low_complexity_regional_dichotomy {M n : ℕ}
    (hn : 2 ≤ n) (θ : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) n)
    (S : Finset Lattice) (hS : NivatTrial.LatticePolygon.IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card)
    (hnot : ¬IsPeriodic θ) :
    ∃ e : Lattice ≃+ Lattice,
      ∃ F : IntegerDecomposition (integerField (θ ∘ e)) n,
      ∃ i : Fin n, ∃ p ∈ languageHull (θ ∘ e),
        F.component = (reparametrize E e).component ∧
        IsPeriod p (F.period i) ∧
        ¬HasDoublyPeriodicExtension p (halfPlane (embed (F.period i)) 0) ∧
        (HasPeriodicWedge (θ ∘ e) F.period (F.period i) ∨
         HasDefectiveHalfStripPatches (θ ∘ e) p F.period i) := by
  obtain ⟨j,k,c,e,hjk,hc,he,hvertical,hpos,hneg⟩ :=
    horizontal_opposite_of_low_complexity hn θ E S hlow hnot
  let θ' := θ ∘ e
  let S' := mapWindow e.symm S
  let E' : IntegerDecomposition (integerField θ') n := reparametrize E e
  have hconv' : NivatTrial.LatticePolygon.IsLatticeConvex S' :=
    isLatticeConvex_mapWindow e.symm hS
  have hlow' : patternComplexity θ' S' ≤ S'.card := by
    calc
      patternComplexity θ' S' = patternComplexity (θ' ∘ e.symm) S := by
        exact patternComplexity_mapWindow e.symm θ' S
      _ = patternComplexity θ S := by
        congr 1
        funext z
        simp [θ']
      _ ≤ S.card := hlow
      _ = S'.card := (card_mapWindow e.symm S).symm
  obtain ⟨p,hp,⟨P,hP,hpP⟩,hproper⟩ :=
    low_complexity_has_proper_horizontal_reference θ' E' S' hconv' hlow'
      hpos (by simpa using hneg)
  obtain ⟨i,hi⟩ := tangent_factor_of_nonexpansive θ' E' (1,0) hpos
  have hzero : (E'.period i).2 = 0 := by
    have hs : ((E'.period i).2 : ℝ) = 0 := by
      simpa [score] using hi
    exact_mod_cast hs
  have hPnonzero : P • ((1,0) : Lattice) ≠ 0 := by
    simp [Nat.ne_of_gt hP]
  have hparallel : det (P • ((1,0) : Lattice)) (E'.period i) = 0 := by
    simp [det,hzero]
  obtain ⟨q,hq,hpq⟩ :=
    ColleReferenceRigidity.parallel_period_of_arbitrary_alphabet
      hpP hPnonzero (E'.period i) hparallel
  have hnot' : ¬IsPeriodic θ' := by
    intro h
    exact hnot ((isPeriodic_comp_equiv_iff e θ).mp h)
  obtain ⟨F,hcomponent,hFperiod,hFproper,hbranch⟩ :=
    actual_regional_dichotomy_of_proper_horizontal_reference hn θ' p E'
      hp hnot' i hzero q hq hpq hproper
  exact ⟨e,F,i,p,hp,hcomponent,hFperiod,hFproper,hbranch⟩

end
end NivatTrial.ColleRegionalEntry
