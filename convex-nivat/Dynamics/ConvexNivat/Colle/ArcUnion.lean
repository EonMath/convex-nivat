import ConvexNivat.Colle.Shared.AlternatingAssembly
import ConvexNivat.Colle.Shared.SequenceGrowthSteps
import ConvexNivat.Colle.Shared.HullBoundary
import ConvexNivat.Colle.RegionArcCompatibility

namespace ConvexNivat.Colle
noncomputable section

local macro "paidPositioned" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.AlternatingAssembly).num 0 ++ `ConvexNivat.Colle.maximal_window_positioned))


local macro "paidHalfOrder" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.cycle_half_order))


local macro "paidRowMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.AlternatingAssembly).num 0 ++ `ConvexNivat.Colle.row_membership))


private theorem arc_row_mem (B : Finset Lattice) (v z : Lattice) :
    z ∈ supportRow B v ↔ z ∈ B ∧ ∀ q ∈ B, det v z ≤ det v q :=
  paidRowMem B v z

private theorem arc_det_embed_sub (d z q : Lattice) :
    realDet (embed d) (embed z - embed q) = (det d (z - q) : ℝ) := by
  simp [realDet, embed, det]

private theorem arc_half_order {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i j : ℤ) (hij : i < j) (hji : j < i+m) :
    0 < det (C.direction i) (C.direction j) :=
  paidHalfOrder C i j hij hji

private theorem arc_normalised_mem_iff {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) (z : Lattice) :
    z ∈ W.normalised j ↔ z + (W.normalise j : ℤ) • C.direction i ∈ W.A j := by
  constructor
  · intro hz
    obtain ⟨q, hq, hqz⟩ := Finset.mem_image.mp hz
    simpa [← hqz] using hq
  · intro hz
    exact Finset.mem_image.mpr ⟨z + (W.normalise j : ℤ) • C.direction i, hz, by simp⟩

private theorem arc_normalised_vertex_mem {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) (d : ℤ) :
    (W.boundary j).vertex d - (W.normalise j : ℤ) • C.direction i ∈ W.normalised j := by
  rw [arc_normalised_mem_iff]
  simpa using (Finset.mem_filter.mp ((W.boundary j).initial d)).1

private theorem arc_fixed_vertex {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (d : ℤ) (hlo : i + 1 ≤ d) (hhi : d ≤ G.J) (j : ℕ) :
    (W.boundary (G.subsequence j)).vertex d -
      (W.normalise (G.subsequence j) : ℤ) • C.direction i =
    (W.boundary (G.subsequence 0)).vertex d -
      (W.normalise (G.subsequence 0) : ℤ) • C.direction i := by
  let k := (d - (i + 1)).toNat
  have hk : i + 1 + (k : ℤ) = d := by dsimp [k]; omega
  suffices H : ∀ k : ℕ, i + 1 + (k : ℤ) ≤ G.J →
      (W.boundary (G.subsequence j)).vertex (i + 1 + (k : ℤ)) -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i =
      (W.boundary (G.subsequence 0)).vertex (i + 1 + (k : ℤ)) -
        (W.normalise (G.subsequence 0) : ℤ) • C.direction i by
    simpa only [hk] using H k (by omega)
  intro k
  induction k with
  | zero => intro _; simpa using (W.terminal (G.subsequence j)).trans (W.terminal (G.subsequence 0)).symm
  | succ k ih =>
    intro hb
    have hkJ : i + 1 + (k : ℤ) < G.J := by omega
    have ih := ih (by omega)
    obtain ⟨L,hL⟩ := G.earlier_fixed (i + 1 + (k : ℤ)) (by omega) hkJ
    have e₁ := (W.boundary (G.subsequence j)).edge_eq (i + 1 + (k : ℤ))
    have e₀ := (W.boundary (G.subsequence 0)).edge_eq (i + 1 + (k : ℤ))
    rw [hL j] at e₁
    rw [hL 0] at e₀
    simp only [Nat.cast_succ, ← add_assoc]
    linear_combination (norm := module) ih + e₁ - e₀

private theorem arc_anchor_height {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) : det (C.direction i) W.anchor = -1 := by
  have hp := (paidPositioned
    S (W.B 0) (W.A 0) (C.direction i) _ _ (W.B_enveloped 0).1 (W.positioned 0) (W.maximal 0)).1
    _ ((W.boundary 0).terminal i)
  have he := W.terminal 0
  rw [W.first_normalise] at he
  simp only [Nat.cast_zero, zero_smul, sub_zero] at he
  rw [← he]
  exact hp

private theorem arc_normalised_monotone {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    Monotone (fun j => W.normalised (G.subsequence j)) := by
  exact monotone_nat_of_le_succ G.nested

private theorem arc_base_exhaustion {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (z : Lattice) (hz : -1 ≤ det (C.direction i) z) :
    ∃ j, z ∈ W.A (G.subsequence j) := by
  let R := max z.1.natAbs z.2.natAbs
  refine ⟨R,W.base_in_maximal _ (W.exhaustion _ z ?_ hz)⟩
  have hR := G.strict.id_le R
  have h₁ : |z.1| ≤ (G.subsequence R : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast (le_max_left z.1.natAbs z.2.natAbs).trans hR
  have h₂ : |z.2| ≤ (G.subsequence R : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast (le_max_right z.1.natAbs z.2.natAbs).trans hR
  simpa only [integerSquare,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc] using
    And.intro (abs_le.mp h₁) (abs_le.mp h₂)

local macro "paidHullImage" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.PositionedWindows).num 0 ++ `ConvexNivat.Colle.sg_hull_image))

private theorem arc_normalised_hull {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) (x : RealPlane) :
    x ∈ windowHull (W.normalised j) ↔
      x + embed ((W.normalise j : ℤ) • C.direction i) ∈ windowHull (W.A j) := by
  have h := paidHullImage (W.A j) (-((W.normalise j : ℤ) • C.direction i)) 1
  have he : W.normalised j = (W.A j).image
      (fun z => -((W.normalise j : ℤ) • C.direction i) + (1 : ℤ) • z) := by
    simp only [AlternatingWindows.normalised,windowTranslate,one_smul,add_comm]
  rw [he,h]
  have hneg : ∀ z : Lattice, embed (-z) = -embed z := by intro z; ext <;> simp [embed]
  simp only [Int.cast_one,one_smul,Set.mem_image,hneg]
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x + embed ((W.normalise j : ℤ) • C.direction i),hx,by abel⟩

private theorem arc_normalised_hull_support {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) (x : RealPlane) :
    x ∈ windowHull (W.normalised j) ↔ ∀ d : ℤ,
      0 ≤ realDet (embed (C.direction d))
        (x - embed ((W.boundary j).vertex d - (W.normalise j : ℤ) • C.direction i)) := by
  rw [arc_normalised_hull,(W.boundary j).hull_eq]
  simp only [Set.mem_ofPred_eq,embed_sub]
  have he : ∀ d : ℤ, x + embed ((W.normalise j : ℤ) • C.direction i) -
      embed ((W.boundary j).vertex d) = x - (embed ((W.boundary j).vertex d) -
      embed ((W.normalise j : ℤ) • C.direction i)) := by intro d; abel
  simp only [he]

private theorem arc_normalised_lattice_convex {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) : LatticeConvex (W.normalised j) := by
  intro z
  rw [arc_normalised_hull,← embed_add,(W.A_enveloped j).2.1,arc_normalised_mem_iff]

private theorem arc_first_ray_points {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) (N : ℕ) :
    ∃ j, W.anchor - (N : ℤ) • C.direction i ∈ W.normalised (G.subsequence j) := by
  let v := C.direction i
  let q := W.anchor - (N : ℤ) • v
  have hqheight : det v q = -1 := by
    dsimp [q]
    have he : det v (W.anchor - (N : ℤ) • v) = det v W.anchor := by simp [det];ring
    rw [he]
    exact arc_anchor_height W
  obtain ⟨j,hq⟩ := arc_base_exhaustion W G q (by change -1 ≤ det v q;omega)
  let D := W.boundary (G.subsequence j)
  have hpos := paidPositioned S (W.B (G.subsequence j)) (W.A (G.subsequence j)) v
    _ _ (W.B_enveloped _).1 (W.positioned _) (W.maximal _)
  have hrow : q ∈ supportRow (W.A (G.subsequence j)) v :=
    (arc_row_mem _ v q).mpr ⟨hq,fun z hz => by rw [hqheight];exact hpos.2 z hz⟩
  have hseg := (D.segment_eq i q).mp hrow
  have hterminal : D.vertex i + (D.length i : ℤ) • v = D.vertex (i+1) := by
    dsimp [v,D]
    linear_combination (norm := module) -(W.boundary (G.subsequence j)).edge_eq i
  have hc := (primitive_row_coordinates v (C.primitive i)).2.2
    (D.vertex i) 0 (D.length i : ℤ) (by positivity) q
  simp only [zero_smul,add_zero,hterminal] at hc
  obtain ⟨k,hk0,hklen,hkeq⟩ := hc.mp hseg
  have ha := W.terminal (G.subsequence j)
  have hsmul : ((D.length i : ℤ)-k) • v =
      ((N : ℤ)+(W.normalise (G.subsequence j) : ℤ)) • v := by
    dsimp [q] at hkeq
    change D.vertex (i+1) - (W.normalise (G.subsequence j) : ℤ) • v = W.anchor at ha
    rw [sub_smul,add_smul]
    linear_combination (norm := module) hterminal + hkeq + ha
  have hscalar := smul_left_injective ℤ (primitive_ne_zero v (C.primitive i)) hsmul
  have hN : (N : ℤ) ≤ D.length i := by omega
  refine ⟨j,?_⟩
  rw [arc_normalised_mem_iff]
  have hseg' := ((primitive_row_coordinates v (C.primitive i)).2.2
    (D.vertex i) 0 (D.length i : ℤ) (by positivity) _).mpr
      ⟨(D.length i : ℤ)-(N : ℤ),by omega,by omega,rfl⟩
  simp only [zero_smul,add_zero,hterminal] at hseg'
  have hmem := (D.segment_eq i _).mpr hseg' 
  have hm := (Finset.mem_filter.mp hmem).1
  convert hm using 1
  rw [sub_smul]
  change W.anchor - (N : ℤ) • v + (W.normalise (G.subsequence j) : ℤ) • v = _
  linear_combination (norm := module) -hterminal - ha

private theorem arc_second_ray_points {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) (N : ℕ) :
    ∃ j, (W.boundary (G.subsequence 0)).vertex G.J -
      (W.normalise (G.subsequence 0) : ℤ) • C.direction i +
      (N : ℤ) • C.direction G.J ∈ W.normalised (G.subsequence j) := by
  have hN : N ≤ (W.boundary (G.subsequence N)).length G.J := G.growing.id_le N
  let D := W.boundary (G.subsequence N)
  have hterminal : D.vertex G.J + (D.length G.J : ℤ) • C.direction G.J = D.vertex (G.J+1) := by
    linear_combination (norm := module) -D.edge_eq G.J
  have hc := (primitive_row_coordinates (C.direction G.J) (C.primitive G.J)).2.2
    (D.vertex G.J) 0 (D.length G.J : ℤ) (by positivity)
    (D.vertex G.J + (N : ℤ) • C.direction G.J)
  simp only [zero_smul,add_zero,hterminal] at hc
  have hm := (Finset.mem_filter.mp ((D.segment_eq G.J _).mpr
    (hc.mpr ⟨N,by positivity,by exact_mod_cast hN,rfl⟩))).1
  refine ⟨N,?_⟩
  rw [← arc_fixed_vertex W G G.J G.lower le_rfl N,arc_normalised_mem_iff]
  convert hm using 1
  dsimp [D]
  abel

private def arcPoint {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) (d : ℤ) : Lattice :=
  (W.boundary (G.subsequence 0)).vertex d -
    (W.normalise (G.subsequence 0) : ℤ) • C.direction i

private theorem arc_initial_vertex {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) :
    (W.boundary j).vertex i - (W.normalise j : ℤ) • C.direction i =
      W.anchor - ((W.boundary j).length i : ℤ) • C.direction i := by
  linear_combination (norm := module) -(W.boundary j).edge_eq i + W.terminal j

private theorem arc_first_support_value {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) (x : RealPlane) :
    realDet (embed (C.direction i))
      (x - embed ((W.boundary j).vertex i - (W.normalise j : ℤ) • C.direction i)) =
    realDet (embed (C.direction i)) (x - embed W.anchor) := by
  rw [arc_initial_vertex]
  simp [realDet,embed]
  ring

private theorem arc_support_fixed {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (d : ℤ) (hlo : i ≤ d) (hhi : d ≤ G.J) (j : ℕ) (x : RealPlane) :
    realDet (embed (C.direction d))
      (x - embed ((W.boundary (G.subsequence j)).vertex d -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i)) =
    realDet (embed (C.direction d)) (x - embed (arcPoint W G d)) := by
  by_cases he : d=i
  · subst d
    exact (arc_first_support_value W _ x).trans (arc_first_support_value W _ x).symm
  · rw [arc_fixed_vertex W G d (by omega) hhi j]
    rfl

private def arcCarrier {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) : Set RealPlane :=
  {x | ∀ d : ℤ, i ≤ d → d ≤ G.J →
    0 ≤ realDet (embed (C.direction d)) (x - embed (arcPoint W G d))}

private theorem arc_hull_subset {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) (j : ℕ) :
    windowHull (W.normalised (G.subsequence j)) ⊆ arcCarrier W G := by
  intro x hx d hlo hhi
  have h := (arc_normalised_hull_support W _ x).mp hx d
  rwa [arc_support_fixed W G d hlo hhi j x] at h

private theorem arc_support_after_ray {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (p u : Lattice) (hray : ∀ N : ℕ, ∃ j, p + (N : ℤ) • u ∈ W.normalised (G.subsequence j))
    (d : ℤ) (hd : det (C.direction d) u < 0) (x : RealPlane) :
    ∃ j, 0 ≤ realDet (embed (C.direction d))
      (x - embed ((W.boundary (G.subsequence j)).vertex d -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i)) := by
  let D : ℝ := -(det (C.direction d) u : ℝ)
  have hD : 0 < D := by dsimp [D];exact neg_pos.mpr (by exact_mod_cast hd)
  obtain ⟨N,hN⟩ := exists_nat_ge (-realDet (embed (C.direction d)) (x-embed p)/D)
  have hN' := (div_le_iff₀ hD).mp hN
  obtain ⟨j,hj⟩ := hray N
  have hs := (arc_normalised_hull_support W _ _).mp (window_mem_hull _ hj) d
  have he : realDet (embed (C.direction d))
      (x - embed ((W.boundary (G.subsequence j)).vertex d -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i)) =
      realDet (embed (C.direction d)) (x-embed p) + (N:ℝ)*D +
      realDet (embed (C.direction d))
      (embed (p+(N:ℤ)•u) - embed ((W.boundary (G.subsequence j)).vertex d -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i)) := by
    simp [D,realDet,det,embed]
    ring
  exact ⟨j,by rw [he];linarith⟩

private theorem arc_support_monotone {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (j k : ℕ) (hjk : j ≤ k) (d : ℤ) (x : RealPlane)
    (hx : 0 ≤ realDet (embed (C.direction d))
      (x - embed ((W.boundary (G.subsequence j)).vertex d -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i))) :
    0 ≤ realDet (embed (C.direction d))
      (x - embed ((W.boundary (G.subsequence k)).vertex d -
        (W.normalise (G.subsequence k) : ℤ) • C.direction i)) := by
  have hv := arc_normalised_vertex_mem W (G.subsequence j) d
  have hm := arc_normalised_monotone W G hjk hv
  have hs := (arc_normalised_hull_support W _ _).mp (window_mem_hull _ hm) d
  have he : realDet (embed (C.direction d))
      (x - embed ((W.boundary (G.subsequence k)).vertex d -
        (W.normalise (G.subsequence k) : ℤ) • C.direction i)) =
      realDet (embed (C.direction d))
      (x - embed ((W.boundary (G.subsequence j)).vertex d -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i)) +
      realDet (embed (C.direction d))
      (embed ((W.boundary (G.subsequence j)).vertex d -
        (W.normalise (G.subsequence j) : ℤ) • C.direction i) -
       embed ((W.boundary (G.subsequence k)).vertex d -
        (W.normalise (G.subsequence k) : ℤ) • C.direction i)) := by dsimp [realDet];ring
  rw [he]
  exact add_nonneg hx hs

private theorem arc_periodic_representative {α : Type*} (f : ℤ → α) (p : ℤ)
    (hf : Function.Periodic f p) (i d : ℤ) :
    f d = f (i + (d-i)%p) := by
  have h := hf.int_mul ((d-i)/p) (i+(d-i)%p)
  have he : i+(d-i)%p + (d-i)/p*p = d := by
    have he := Int.emod_add_ediv_mul (d-i) p
    omega
  simpa [he] using h

private theorem arc_carrier_union {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    arcCarrier W G = ⋃ j, windowHull (W.normalised (G.subsequence j)) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hm := C.at_least_two
    have hone : ∀ r : Fin (2*m), ∃ j, 0 ≤ realDet (embed (C.direction (i+(r.val:ℤ))))
        (x - embed ((W.boundary (G.subsequence j)).vertex (i+(r.val:ℤ)) -
          (W.normalise (G.subsequence j):ℤ) • C.direction i)) := by
      intro r
      let d : ℤ := i+(r.val:ℤ)
      have hdlo : i ≤ d := by dsimp [d];omega
      have hdhi : d < i+2*(m:ℤ) := by dsimp [d];have := r.isLt;omega
      by_cases hd : d ≤ G.J
      · refine ⟨0,?_⟩
        exact hx d hdlo hd
      · have hJd : G.J < d := by omega
        by_cases hhalf : d ≤ i+(m:ℤ)
        · have hpos := arc_half_order C G.J d hJd (by have := G.lower;omega)
          have hneg : det (C.direction d) (C.direction G.J) < 0 := by
            have he : det (C.direction d) (C.direction G.J) =
                -det (C.direction G.J) (C.direction d) := by dsimp [det];ring
            rw [he];omega
          exact arc_support_after_ray W G (arcPoint W G G.J) (C.direction G.J)
            (arc_second_ray_points W G) d hneg x
        · have hpos := arc_half_order C d (i+2*(m:ℤ)) hdhi (by omega)
          rw [C.direction_periodic] at hpos
          have hneg : det (C.direction d) (-C.direction i) < 0 := by
            have he : det (C.direction d) (-C.direction i) =
                -det (C.direction d) (C.direction i) := by dsimp [det];simp;ring
            rw [he];omega
          apply arc_support_after_ray W G W.anchor (-C.direction i) ?_ d hneg x
          intro N
          simpa only [smul_neg,sub_eq_add_neg] using arc_first_ray_points W G N
    choose index hindex using hone
    let j := Finset.univ.sup index
    apply Set.mem_iUnion.mpr
    refine ⟨j,(arc_normalised_hull_support W _ x).mpr ?_⟩
    intro d
    let r : ℤ := (d-i)%(2*(m:ℤ))
    have hp : 0 < 2*(m:ℤ) := by omega
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hp.ne'
    have hrp : r < 2*(m:ℤ) := Int.emod_lt_of_pos _ hp
    let R : Fin (2*m) := ⟨r.toNat,by omega⟩
    have hR : (R.val:ℤ)=r := Int.toNat_of_nonneg hr0
    have hdir := arc_periodic_representative C.direction _ C.direction_periodic i d
    have hver := arc_periodic_representative (W.boundary (G.subsequence j)).vertex _
      (W.boundary (G.subsequence j)).vertex_periodic i d
    rw [hdir,hver]
    have hs := arc_support_monotone W G (index R) j
      (Finset.le_sup (f:=index) (Finset.mem_univ R)) (i+(R.val:ℤ)) x (hindex R)
    simpa only [hR] using hs
  · intro x hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
    exact arc_hull_subset W G j hj

private theorem arc_carrier_closed {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    IsClosed (arcCarrier W G) := by
  have he : arcCarrier W G = ⋂ (d : ℤ) (_ : i ≤ d) (_ : d ≤ G.J),
      {x | 0 ≤ realDet (embed (C.direction d)) (x - embed (arcPoint W G d))} := by
    ext x;simp only [arcCarrier,Set.mem_iInter,Set.mem_ofPred_eq]
  rw [he]
  apply isClosed_iInter
  intro d
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  apply isClosed_le continuous_const
  dsimp [realDet];fun_prop

private theorem arc_carrier_convex {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    Convex ℝ (arcCarrier W G) := by
  intro x hx y hy a b ha hb hab d hlo hhi
  have he : realDet (embed (C.direction d))
      (a • x+b • y-embed (arcPoint W G d)) =
      a*realDet (embed (C.direction d)) (x-embed (arcPoint W G d)) +
      b*realDet (embed (C.direction d)) (y-embed (arcPoint W G d)) := by
    dsimp [realDet]
    linear_combination ((embed (C.direction d)).1*(embed (arcPoint W G d)).2 -
      (embed (C.direction d)).2*(embed (arcPoint W G d)).1)*hab
  rw [he]
  exact add_nonneg (mul_nonneg ha (hx d hlo hhi)) (mul_nonneg hb (hy d hlo hhi))

private theorem arc_carrier_lattice {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    embed ⁻¹' arcCarrier W G = normalisedUnion W G := by
  rw [arc_carrier_union]
  ext z
  simp only [Set.mem_preimage,Set.mem_iUnion,normalisedUnion,Finset.mem_coe]
  exact exists_congr (fun j => arc_normalised_lattice_convex W _ z)

private theorem arc_carrier_closed_hull {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    arcCarrier W G = closedRealHull (normalisedUnion W G) := by
  apply Set.Subset.antisymm
  · rw [arc_carrier_union]
    apply Set.iUnion_subset
    intro j
    apply Set.Subset.trans ?_ subset_closure
    apply convexHull_mono
    apply Set.image_mono
    exact Set.subset_iUnion (fun k => (W.normalised (G.subsequence k) : Set Lattice)) j
  · apply closure_minimal ?_ (arc_carrier_closed W G)
    apply convexHull_min ?_ (arc_carrier_convex W G)
    rintro _ ⟨z,hz,rfl⟩
    exact (Set.ext_iff.mp (arc_carrier_lattice W G) z).mpr hz

private theorem arc_carrier_area {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    (interior (arcCarrier W G)).Nonempty := by
  obtain ⟨x,hx⟩ := (W.A_enveloped (G.subsequence 0)).2.2.1
  let s := embed ((W.normalise (G.subsequence 0):ℤ) • C.direction i)
  have hhull : windowHull (W.normalised (G.subsequence 0)) =
      (Homeomorph.addRight s) ⁻¹' windowHull (W.A (G.subsequence 0)) := by
    ext y
    exact arc_normalised_hull W _ y
  have hi : x-s ∈ interior (windowHull (W.normalised (G.subsequence 0))) := by
    rw [hhull,← (Homeomorph.addRight s).preimage_interior]
    change x-s+s ∈ interior (windowHull (W.A (G.subsequence 0)))
    simpa using hx
  exact ⟨x-s,interior_mono (arc_hull_subset W G 0) hi⟩

private theorem arc_carrier_cone {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (x : RealPlane) (hx : x ∈ arcCarrier W G)
    (u : RealPlane) (hu : u ∈ twoRayCone (-C.direction i) (C.direction G.J)) :
    x+u ∈ arcCarrier W G := by
  obtain ⟨a,b,ha,hb,rfl⟩ := hu
  intro d hlo hhi
  have hleft : 0 ≤ det (C.direction d) (-C.direction i) := by
    have he : det (C.direction d) (-C.direction i) = det (C.direction i) (C.direction d) := by simp [det];ring
    rw [he]
    by_cases hd : d=i
    · subst d;simp [det,mul_comm]
    · exact (arc_half_order C i d (by omega) (by have := G.upper;omega)).le
  have hright : 0 ≤ det (C.direction d) (C.direction G.J) := by
    by_cases hd : d=G.J
    · subst d;simp [det,mul_comm]
    · exact (arc_half_order C d G.J (by omega) (by have := G.upper;omega)).le
  have hleftR : 0 ≤ (det (C.direction d) (-C.direction i):ℝ) := by exact_mod_cast hleft
  have hrightR : 0 ≤ (det (C.direction d) (C.direction G.J):ℝ) := by exact_mod_cast hright
  have he : realDet (embed (C.direction d))
      (x+(a • embed (-C.direction i)+b • embed (C.direction G.J))-embed (arcPoint W G d)) =
      realDet (embed (C.direction d)) (x-embed (arcPoint W G d)) +
      a*(det (C.direction d) (-C.direction i):ℝ) +
      b*(det (C.direction d) (C.direction G.J):ℝ) := by simp [realDet,det,embed];ring
  rw [he]
  exact add_nonneg (add_nonneg (hx d hlo hhi) (mul_nonneg ha hleftR)) (mul_nonneg hb hrightR)

local macro "paid_hb_active_chain_face" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.HullBoundary).num 0 ++ `ConvexNivat.Colle.hb_active_chain_face))

local macro "paid_hb_support_zero_not_interior" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.HullBoundary).num 0 ++ `ConvexNivat.Colle.hb_support_zero_not_interior))

local macro "paid_rj_real_det_smul" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.HullBoundary).num 0 ++ `ConvexNivat.Colle.rj_real_det_smul))

private def arc_region_from_chain (v w : Lattice) (hv : Primitive v) (hw : Primitive w)
    (hvw : 0<det v w) (C : Set RealPlane) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (harea : (interior C).Nonempty) (n : ℕ) (a : Fin (n+1) → Lattice) (d : Fin n → Lattice)
    (hprimitive : ∀ j, Primitive (d j))
    (hlen : ∀ j : Fin n, ∃ k : ℤ, 1≤k ∧ a j.succ-a j.castSucc=k•d j)
    (hfirst : ∀ j : Fin n, j.val=0 → 0<det v (d j))
    (hturn : ∀ j k : Fin n, k.val=j.val+1 → 0<det (d j) (d k))
    (hlast : ∀ j : Fin n, j.val+1=n → 0<det (d j) w)
    (hvertices : ∀ j, embed (a j) ∈ C)
    (hcone : ∀ x ∈ C, ∀ u ∈ twoRayCone (-v) w, x+u ∈ C)
    (hC : C={x | 0≤realDet (embed v) (x-embed (a 0)) ∧
      0≤realDet (embed w) (x-embed (a (Fin.last n))) ∧
      ∀ j, 0≤realDet (embed (d j)) (x-embed (a j.castSucc))}) :
    Region v w := by
  have hs : ∀ x ∈ C, 0≤realDet (embed v) (x-embed (a 0)) ∧
      0≤realDet (embed w) (x-embed (a (Fin.last n))) ∧
      ∀ j, 0≤realDet (embed (d j)) (x-embed (a j.castSucc)) := by rw [hC];exact fun _ h => h
  have hne : ∀ u : Lattice, Primitive u → embed u≠0 := by
    intro u hu he
    apply primitive_ne_zero u hu
    have he1 : (u.1:ℝ)=0 := congrArg Prod.fst he
    have he2 : (u.2:ℝ)=0 := congrArg Prod.snd he
    apply Prod.ext <;> change _=0
    · exact_mod_cast he1
    · exact_mod_cast he2
  have hfront : frontier C=
      {x | ∃t : ℝ, 0≤t ∧ x=embed (a 0)-t•embed v} ∪
      {x | ∃t : ℝ, 0≤t ∧ x=embed (a (Fin.last n))+t•embed w} ∪
      {x | ∃j : Fin n, x ∈ segment ℝ (embed (a j.castSucc)) (embed (a j.succ))} := by
    rw [hclosed.frontier_eq]
    ext x
    constructor
    · rintro ⟨hx,hni⟩
      have hsx := hs x hx
      have ha : realDet (embed v) (x-embed (a 0))=0 ∨
          realDet (embed w) (x-embed (a (Fin.last n)))=0 ∨
          ∃ j, realDet (embed (d j)) (x-embed (a j.castSucc))=0 := by
        by_contra! hno
        let U : Set RealPlane := {y | 0<realDet (embed v) (y-embed (a 0))} ∩
          {y | 0<realDet (embed w) (y-embed (a (Fin.last n)))} ∩
          ⋂ j : Fin n, {y | 0<realDet (embed (d j)) (y-embed (a j.castSucc))}
        have hopen (u z : RealPlane) : IsOpen {y | 0<realDet u (y-z)} := by
          apply isOpen_lt continuous_const
          dsimp [realDet];fun_prop
        have hUopen : IsOpen U := ((hopen _ _).inter (hopen _ _)).inter
          (isOpen_iInter_of_finite (fun j => hopen _ _))
        have hxU : x ∈ U := ⟨⟨lt_of_le_of_ne hsx.1 (Ne.symm hno.1),
          lt_of_le_of_ne hsx.2.1 (Ne.symm hno.2.1)⟩,
          Set.mem_iInter.mpr (fun j => lt_of_le_of_ne (hsx.2.2 j) (Ne.symm (hno.2.2 j)))⟩
        have hUC : U ⊆ C := by
          intro y hy
          rw [hC]
          exact ⟨hy.1.1.le,hy.1.2.le,fun j => (Set.mem_iInter.mp hy.2 j).le⟩
        exact hni (interior_mono hUC (by rwa [hUopen.interior_eq]))
      have hh := paid_hb_active_chain_face v w hvw n a d hlen hfirst hturn hlast x hsx.1 hsx.2.1 hsx.2.2 ha
      rcases hh with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((hx | hx) | hx)
      · obtain ⟨t,ht,rfl⟩ := hx
        have hc : -t•embed v ∈ twoRayCone (-v) w :=
          ⟨t,0,ht,le_rfl,by simp [embed]⟩
        have hm : embed (a 0)-t•embed v ∈ C := by
          simpa [sub_eq_add_neg,neg_smul] using hcone _ (hvertices 0) _ hc
        refine ⟨hm,paid_hb_support_zero_not_interior C (embed v) (embed (a 0)) _
          (hne v hv) (fun y hy => (hs y hy).1) ?_⟩
        dsimp [realDet];ring
      · obtain ⟨t,ht,rfl⟩ := hx
        have hc : t•embed w ∈ twoRayCone (-v) w := ⟨0,t,le_rfl,ht,by simp⟩
        have hm := hcone _ (hvertices (Fin.last n)) _ hc
        refine ⟨hm,paid_hb_support_zero_not_interior C (embed w) (embed (a (Fin.last n))) _
          (hne w hw) (fun y hy => (hs y hy).2.1) ?_⟩
        dsimp [realDet];ring
      · obtain ⟨j,hj⟩ := hx
        have hm := hconvex.segment_subset (hvertices j.castSucc) (hvertices j.succ) hj
        refine ⟨hm,paid_hb_support_zero_not_interior C (embed (d j)) (embed (a j.castSucc)) _
          (hne (d j) (hprimitive j)) (fun y hy => (hs y hy).2.2 j) ?_⟩
        obtain ⟨r,t,hr,ht,hrt,rfl⟩ := hj
        obtain ⟨k,hk,hedge⟩ := hlen j
        have heR : embed (a j.succ)-embed (a j.castSucc)=(k:ℝ)•embed (d j) := by
          rw [← embed_sub,hedge];ext <;> simp [embed]
        have heq : r•embed (a j.castSucc)+t•embed (a j.succ)-embed (a j.castSucc)=
            t•(embed (a j.succ)-embed (a j.castSucc)) := by
          have h := congrArg (fun z : ℝ => z•embed (a j.castSucc)) hrt
          linear_combination (norm := module) h
        rw [heq,heR,paid_rj_real_det_smul,paid_rj_real_det_smul]
        dsimp [realDet];ring
  let P : Region v w := {
    carrier := C
    closed := hclosed
    convex := hconvex
    interior_nonempty := harea
    first_primitive := hv
    second_primitive := hw
    turn_positive := hvw
    boundedCount := n
    vertex := a
    boundedDirection := d
    bounded_primitive := hprimitive
    bounded_length := hlen
    first_turn := hfirst
    bounded_turn := hturn
    second_turn := hlast
    first_support := fun x hx => (hs x hx).1
    second_support := fun x hx => (hs x hx).2.1
    bounded_support := fun j x hx => (hs x hx).2.2 j
    boundary_eq := hfront }
  exact P


private theorem arc_carrier_chain_eq {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    arcCarrier W G = {x |
      0 ≤ realDet (embed (C.direction i)) (x-embed (arcPoint W G (i+1))) ∧
      0 ≤ realDet (embed (C.direction G.J))
        (x-embed (arcPoint W G (i+1+(((G.J-i-1).toNat:ℕ):ℤ)))) ∧
      ∀ j : Fin (G.J-i-1).toNat,
        0 ≤ realDet (embed (C.direction (i+1+(j.val:ℤ))))
          (x-embed (arcPoint W G (i+1+(j.val:ℤ))))} := by
  have hlast : i+1+(((G.J-i-1).toNat:ℕ):ℤ)=G.J := by have := G.lower;omega
  have hanchor : arcPoint W G (i+1)=W.anchor := W.terminal _
  ext x
  change (∀ d : ℤ, i ≤ d → d ≤ G.J → _ ) ↔ _
  have hfirst : realDet (embed (C.direction i)) (x-embed (arcPoint W G i)) =
      realDet (embed (C.direction i)) (x-embed (arcPoint W G (i+1))) := by
    rw [hanchor]
    exact arc_first_support_value W _ x
  constructor
  · intro hx
    refine ⟨?_,?_,?_⟩
    · rw [← hfirst]
      exact hx i le_rfl (by have := G.lower;omega)
    · rw [hlast]
      exact hx G.J (by have := G.lower;omega) le_rfl
    · intro j
      exact hx _ (by omega) (by have := j.isLt;omega)
  · rintro ⟨hf,hl,hb⟩ d hdlo hdhi
    by_cases hd : d=i
    · subst d; rwa [hfirst]
    by_cases hdJ : d=G.J
    · subst d;simpa only [hlast] using hl
    let j : Fin (G.J-i-1).toNat := ⟨(d-i-1).toNat,by omega⟩
    have hj : i+1+(j.val:ℤ)=d := by dsimp [j];omega
    simpa only [hj] using hb j

private def arcRegion {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    Region (C.direction i) (C.direction G.J) := by
  let n := (G.J-i-1).toNat
  let a : Fin (n+1) → Lattice := fun j => arcPoint W G (i+1+(j.val:ℤ))
  let d : Fin n → Lattice := fun j => C.direction (i+1+(j.val:ℤ))
  apply arc_region_from_chain (C.direction i) (C.direction G.J)
    (C.primitive i) (C.primitive G.J)
    (arc_half_order C i G.J (by have := G.lower;omega) (by have := G.upper;omega))
    (arcCarrier W G) (arc_carrier_closed W G) (arc_carrier_convex W G)
    (arc_carrier_area W G) n a d
  · intro j;exact C.primitive _
  · intro j
    refine ⟨(W.boundary (G.subsequence 0)).length (i+1+(j.val:ℤ)),?_,?_⟩
    · exact_mod_cast (W.boundary (G.subsequence 0)).length_positive _
    · dsimp [a,d,arcPoint]
      have he := (W.boundary (G.subsequence 0)).edge_eq (i+1+(j.val:ℤ))
      simp only [Nat.cast_add,Nat.cast_one,← add_assoc]
      linear_combination (norm := module) he
  · intro j hj
    dsimp [d]
    apply arc_half_order C i _
    · omega
    · have := G.upper
      have := j.isLt
      dsimp [n] at *
      omega
  · intro j k hjk
    dsimp [d]
    apply arc_half_order C _ _
    · omega
    · have := C.at_least_two;omega
  · intro j hj
    dsimp [d]
    apply arc_half_order C _ G.J
    · have := j.isLt
      dsimp [n] at *
      omega
    · have := G.upper;omega
  · intro j
    exact arc_hull_subset W G 0 (window_mem_hull _ (arc_normalised_vertex_mem W _ _))
  · exact arc_carrier_cone W G
  · simpa [a,d,n] using arc_carrier_chain_eq W G

private theorem arc_region_arc {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    RegionCompleteArc C i G.J (arcRegion W G) := by
  refine ⟨rfl,rfl,G.lower,G.upper,rfl,?_,?_⟩
  · intro d; rfl
  · intro j hlo hhi
    let d : Fin (arcRegion W G).boundedCount := ⟨(j-i-1).toNat,by
      change (j-i-1).toNat < (G.J-i-1).toNat
      omega⟩
    have hd : i+1+(d.val:ℤ)=j := by dsimp [d];omega
    exact ⟨d,hd,by change C.direction (i+1+(d.val:ℤ))=C.direction j;rw [hd]⟩

private theorem arc_region_first_anchor {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    (arcRegion W G).firstAnchor = W.anchor := by
  change arcPoint W G (i+1+(0:ℕ))=W.anchor
  simp only [Nat.cast_zero,add_zero]
  exact W.terminal _

private theorem arc_ray_encard (p u : Lattice) (hu : u ≠ 0) :
    {z : Lattice | ∃ t : ℝ, 0 ≤ t ∧ embed z = embed p + t • embed u}.encard = ⊤ := by
  let f : ℕ → Lattice := fun n => p+(n:ℤ)•u
  have hf : Function.Injective f := by
    intro n k h
    have he := smul_left_injective ℤ hu (add_left_cancel h)
    exact_mod_cast he
  apply Set.Infinite.encard_eq
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨n,rfl⟩
  refine ⟨n,by positivity,?_⟩
  dsimp [f]
  ext <;> simp [embed]

private theorem arc_segment_encard (p d : Lattice) (hd : Primitive d) (L : ℕ) :
    ((L+1:ℕ):ℕ∞) ≤
      {z : Lattice | embed z ∈ segment ℝ (embed p) (embed (p+(L:ℤ)•d))}.encard := by
  let f : Fin (L+1) → Lattice := fun n => p+(n.val:ℤ)•d
  have hf : Function.Injective f := by
    intro n k h
    have he := smul_left_injective ℤ (primitive_ne_zero d hd) (add_left_cancel h)
    apply Fin.ext
    exact_mod_cast he
  have hcard : (Set.range f).encard = ((L+1:ℕ):ℕ∞) := by
    simpa [ENat.card_eq_coe_fintype_card] using hf.encard_range
  rw [← hcard]
  apply Set.encard_le_encard
  rintro _ ⟨n,rfl⟩
  have hc := (primitive_row_coordinates d hd).2.2 p 0 L (by positivity) (f n)
  simp only [zero_smul,add_zero] at hc
  exact hc.mpr ⟨n.val,by positivity,by have := n.isLt;omega,rfl⟩

local macro "paidDirectionMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.cycle_direction_mem))

private theorem arc_region_weak {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    WeaklyEnveloped S (arcRegion W G) := by
  intro d E hE
  rcases hE with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨j,rfl,rfl⟩
  · refine ⟨paidDirectionMem C i,?_⟩
    have hneg : embed (-C.direction i) = -embed (C.direction i) := by ext <;> simp [embed]
    have hr := arc_ray_encard (arcRegion W G).firstAnchor (-C.direction i)
      (neg_ne_zero.mpr (primitive_ne_zero _ (C.primitive i)))
    simp only [hneg,smul_neg,← sub_eq_add_neg] at hr
    rw [hr]
    exact le_top
  · refine ⟨paidDirectionMem C G.J,?_⟩
    rw [arc_ray_encard _ _ (primitive_ne_zero _ (C.primitive G.J))]
    exact le_top
  · let d := i+1+(j.val:ℤ)
    let L := (W.boundary (G.subsequence 0)).length d
    change C.direction d ∈ edgeDirections S ∧ _
    refine ⟨paidDirectionMem C d,?_⟩
    have he : (arcRegion W G).vertex j.succ =
        (arcRegion W G).vertex j.castSucc + (L:ℤ)•C.direction d := by
      change arcPoint W G (i+1+((j.val+1:ℕ):ℤ)) = arcPoint W G d+(L:ℤ)•C.direction d
      have h := (W.boundary (G.subsequence 0)).edge_eq d
      dsimp [arcPoint,d,L] at *
      simp only [Nat.cast_add,Nat.cast_one,← add_assoc]
      linear_combination (norm := module) h
    rw [he]
    have hsource := (W.boundary (G.subsequence 0)).source_length_le d
    have hsourceE : ((supportRow S (C.direction d)).card:ℕ∞) ≤ ((L+1:ℕ):ℕ∞) := by
      exact_mod_cast hsource
    exact hsourceE.trans (arc_segment_encard _ (C.direction d) (C.primitive d) L)

theorem normalised_union_actual_region_with_arc {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    ∃ P : Region (C.direction i) (C.direction G.J), P.lattice = normalisedUnion W G ∧
      P.carrier = closedRealHull (normalisedUnion W G) ∧ WeaklyEnveloped S P ∧
      RegionCompleteArc C i G.J P ∧
      det (C.direction i) P.firstAnchor = -1 ∧
      ∀ d : Fin P.boundedCount, ∃ j : ℤ, i + 1 ≤ j ∧ j < G.J ∧
        P.boundedDirection d = C.direction j := by
  refine ⟨arcRegion W G,arc_carrier_lattice W G,arc_carrier_closed_hull W G,
    arc_region_weak W G,arc_region_arc W G,?_,?_⟩
  · rw [arc_region_first_anchor]
    exact arc_anchor_height W
  · intro d
    refine ⟨i+1+(d.val:ℤ),by omega,?_,rfl⟩
    have hd := d.isLt
    change d.val < (G.J-i-1).toNat at hd
    omega

end
end ConvexNivat.Colle
