import NivatTrial.ColleDirectionalPropagation

/-! The finite block behind Colle's equation (4.1). An exposed point on a
nonhorizontal edge is an extreme point of its horizontal row. A lower bound
on that row's cardinality places an actual run of sites inside the window,
with every positive inward shift outside the exposed edge. -/

namespace NivatTrial.ColleSlantedBlock

open NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.ColleAmbiguity NivatTrial.BalancedWindows
open NivatTrial.LatticePolygon
open NivatTrial.LatticeCoordinates NivatTrial.ColleDirectionalPropagation
open NivatTrial.ColleBalancedRows
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

theorem row_card_eq_interval_length
    {B : Finset G} (t l r : ℤ)
    (he : row B t = (Finset.Icc l r).image (fun x => (x,t))) :
    (row B t).card = (r-l+1).toNat := by
  rw [he, Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h)]
  simpa only [sub_add_eq_add_sub] using Int.card_Icc l r

theorem supportEdge_rightmost_of_positive_second
    {B : Finset G} {v : Plane} {s : G}
    (hs : s ∈ supportEdge B v) (hv : 0 < v.2)
    (t l r : ℤ) (hlr : l ≤ r) (ht : s.2 = t)
    (he : row B t = (Finset.Icc l r).image (fun x => (x,t))) :
    s.1 = r := by
  have hsB : s ∈ B := (Finset.mem_filter.mp hs).1
  have hsrow : s ∈ row B t := (mem_row B t s).mpr ⟨hsB,ht⟩
  have hsr : s.1 ≤ r := by
    rw [he] at hsrow
    obtain ⟨j,hj,hjs⟩ := Finset.mem_image.mp hsrow
    have hjs' : s = (j,t) := hjs.symm
    simpa only [hjs'] using (Finset.mem_Icc.mp hj).2
  have hrB : (r,t) ∈ B := by
    have hrrow : (r,t) ∈ row B t := by
      rw [he]
      exact Finset.mem_image.mpr ⟨r,Finset.mem_Icc.mpr
        ⟨hlr, le_refl r⟩,rfl⟩
    exact (mem_row B t (r,t)).mp hrrow |>.1
  have hmin := (Finset.mem_filter.mp hs).2 (r,t) hrB
  by_contra hne
  have hlt : s.1 < r := lt_of_le_of_ne hsr hne
  have hdiff : 0 < (r : ℝ) - (s.1 : ℝ) := by exact_mod_cast (sub_pos.mpr hlt)
  have hmul := mul_pos hv hdiff
  simp only [score, ht] at hmin
  nlinarith

theorem supportEdge_leftmost_of_negative_second
    {B : Finset G} {v : Plane} {s : G}
    (hs : s ∈ supportEdge B v) (hv : v.2 < 0)
    (t l r : ℤ) (hlr : l ≤ r) (ht : s.2 = t)
    (he : row B t = (Finset.Icc l r).image (fun x => (x,t))) :
    s.1 = l := by
  have hsB : s ∈ B := (Finset.mem_filter.mp hs).1
  have hsrow : s ∈ row B t := (mem_row B t s).mpr ⟨hsB,ht⟩
  have hsl : l ≤ s.1 := by
    rw [he] at hsrow
    obtain ⟨j,hj,hjs⟩ := Finset.mem_image.mp hsrow
    have hjs' : s = (j,t) := hjs.symm
    simpa only [hjs'] using (Finset.mem_Icc.mp hj).1
  have hlB : (l,t) ∈ B := by
    have hlrow : (l,t) ∈ row B t := by
      rw [he]
      exact Finset.mem_image.mpr ⟨l,Finset.mem_Icc.mpr
        ⟨le_refl l, hlr⟩,rfl⟩
    exact (mem_row B t (l,t)).mp hlrow |>.1
  have hmin := (Finset.mem_filter.mp hs).2 (l,t) hlB
  by_contra hne
  have hlt : l < s.1 := lt_of_le_of_ne hsl (Ne.symm hne)
  have hdiff : 0 < (s.1 : ℝ) - (l : ℝ) := by exact_mod_cast (sub_pos.mpr hlt)
  have hmul := mul_pos (neg_pos.mpr hv) hdiff
  simp only [score, ht] at hmin
  nlinarith

def inwardStep (v : Plane) : G :=
  if 0 < v.2 then (-1,0) else (1,0)

theorem inward_run_mem
    {B : Finset G} (hB : IsLatticeConvex B)
    {v : Plane} (hv : v.2 ≠ 0) {s : G}
    (hs : s ∈ supportEdge B v) (m : ℕ)
    (hcard : m ≤ (row B s.2).card)
    (j : ℕ) (hj : j < m) :
    s + (j : ℤ) • inwardStep v ∈ B := by
  have hsB : s ∈ B := (Finset.mem_filter.mp hs).1
  have hrow : (row B s.2).Nonempty :=
    ⟨s,(mem_row B s.2 s).mpr ⟨hsB,rfl⟩⟩
  obtain ⟨l,r,hlr,he⟩ := row_eq_interval hB s.2 hrow
  have hlength := row_card_eq_interval_length s.2 l r he
  have hm : (m : ℤ) ≤ r-l+1 := by omega
  by_cases hvpos : 0 < v.2
  · have hsr := supportEdge_rightmost_of_positive_second hs hvpos s.2 l r hlr rfl he
    have hbound : l ≤ s.1-(j:ℤ) ∧ s.1-(j:ℤ) ≤ r := by omega
    have hmem : (s.1-(j:ℤ),s.2) ∈ B := by
      have hl : (l,s.2) ∈ B := by
        have hh : (l,s.2) ∈ row B s.2 := by
          rw [he]
          exact Finset.mem_image.mpr ⟨l,Finset.mem_Icc.mpr
            ⟨le_refl l,hlr⟩,rfl⟩
        exact (mem_row B s.2 (l,s.2)).mp hh |>.1
      exact row_interval hB hl hsB hbound.1 (by omega)
    have heq : s + (j : ℤ) • inwardStep v = (s.1-(j:ℤ),s.2) := by
      ext <;> simp [inwardStep, hvpos, sub_eq_add_neg]
    rw [heq]
    exact hmem
  · have hvneg : v.2 < 0 := lt_of_le_of_ne (le_of_not_gt hvpos) hv
    have hsl := supportEdge_leftmost_of_negative_second hs hvneg s.2 l r hlr rfl he
    have hbound : l ≤ s.1+(j:ℤ) ∧ s.1+(j:ℤ) ≤ r := by omega
    have hmem : (s.1+(j:ℤ),s.2) ∈ B := by
      have hr : (r,s.2) ∈ B := by
        have hh : (r,s.2) ∈ row B s.2 := by
          rw [he]
          exact Finset.mem_image.mpr ⟨r,Finset.mem_Icc.mpr
            ⟨hlr,le_refl r⟩,rfl⟩
        exact (mem_row B s.2 (r,s.2)).mp hh |>.1
      exact row_interval hB hsB hr (by omega) hbound.2
    have heq : s + (j : ℤ) • inwardStep v = (s.1+(j:ℤ),s.2) := by
      ext <;> simp [inwardStep, hvpos]
    rw [heq]
    exact hmem

theorem inward_run_mem_base
    {B : Finset G} (hB : IsLatticeConvex B)
    {v : Plane} (hv : v.2 ≠ 0) {s : G}
    (hs : s ∈ supportEdge B v) (m : ℕ)
    (hcard : m ≤ (row B s.2).card)
    (j : ℕ) (hj0 : 0 < j) (hj : j < m) :
    s + (j : ℤ) • inwardStep v ∈ supportBase B v := by
  have hmem := inward_run_mem hB hv hs m hcard j hj
  apply Finset.mem_sdiff.mpr
  refine ⟨hmem,?_⟩
  intro hedge
  have hsB : s ∈ B := (Finset.mem_filter.mp hs).1
  have hmin := (Finset.mem_filter.mp hedge).2 s hsB
  have hjreal : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj0
  by_cases hvpos : 0 < v.2
  · have hmul := mul_pos hvpos hjreal
    simp [score, inwardStep, hvpos] at hmin
    nlinarith
  · have hvneg : v.2 < 0 := lt_of_le_of_ne (le_of_not_gt hvpos) hv
    have hmul := mul_pos (neg_pos.mpr hvneg) hjreal
    simp [score, inwardStep, hvpos] at hmin
    nlinarith

/-- An actual support edge parallel to an integer basis vector is a
consecutive run in that basis. This provides the full transverse block
required by the semi-ambiguity word count. -/
theorem supportEdge_run_in_basis
    (e : G ≃+ G) (B : Finset G) (v : Plane)
    (hB : IsLatticeConvex B) (hne : B.Nonempty)
    (hdual : dualNormal e v = (1,0)) :
    ∃ s₀ : G,
      supportEdge B v =
        (Finset.range (supportEdge B v).card).image
          (fun j : ℕ => s₀ + (j : ℤ) • e (1,0)) := by
  let B' := mapWindow e.symm B
  have hB' : IsLatticeConvex B' := isLatticeConvex_mapWindow e.symm hB
  have hne' : B'.Nonempty := mapWindow_nonempty e.symm hne
  have hbedge : bottomEdge B' = supportEdge B' (1,0) :=
    (horizontal_supportEdge_eq_bottomEdge B' hne').symm
  have hEdge : supportEdge B v = mapWindow e (bottomEdge B') := by
    have hBack : mapWindow e B' = B := by
      simpa [B'] using mapWindow_symm_mapWindow e.symm B
    conv_lhs => rw [← hBack]
    rw [supportEdge_mapWindow, hdual, ← hbedge]
  obtain ⟨x,hrow⟩ := row_run hB' (lower B') (bottomEdge_nonempty hne')
  let s₀ : G := e (x,lower B')
  refine ⟨s₀,?_⟩
  rw [hEdge]
  simp only [card_mapWindow]
  change mapWindow e (row B' (lower B')) =
    (Finset.range (row B' (lower B')).card).image
      (fun j : ℕ => s₀ + (j : ℤ) • e (1,0))
  conv_lhs => rw [hrow]
  ext z
  simp only [mem_mapWindow, Finset.mem_image]
  constructor
  · rintro ⟨j,hj,he⟩
    refine ⟨j,hj,?_⟩
    have hh : (x+(j:ℤ),lower B') =
        (x,lower B')+(j:ℤ) • ((1,0):G) := by ext <;> simp
    have hze : z = e (x+(j:ℤ),lower B') := by
      simpa using congrArg e he.symm
    rw [hze,hh,map_add,map_zsmul]
  · rintro ⟨j,hj,he⟩
    refine ⟨j,hj,?_⟩
    have hh : (x+(j:ℤ),lower B') =
        (x,lower B')+(j:ℤ) • ((1,0):G) := by ext <;> simp
    rw [← he,hh,map_add,map_zsmul]
    simp [s₀]

end

end NivatTrial.ColleSlantedBlock
