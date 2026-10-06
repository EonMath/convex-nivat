import ConvexNivat.Colle.Shared.HomothetyDefinitions
import ConvexNivat.Geometry.Basic
import ConvexNivat.CoreLattice

namespace ConvexNivat.Colle
noncomputable section

private theorem sg_window_mem (T : Finset Lattice) (z : Lattice) :
    z ∈ convexLatticeWindow T ↔ embed z ∈ windowHull T :=
  (lattice_windowHull_finite T).mem_toFinset

private theorem sg_window_hull (T : Finset Lattice) :
    windowHull (convexLatticeWindow T) = windowHull T := by
  apply le_antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨z, hz, rfl⟩
    exact (sg_window_mem T z).mp hz
  · apply convexHull_mono
    apply Set.image_mono
    intro z hz
    exact (sg_window_mem T z).mpr (window_mem_hull T hz)

private theorem sg_window_convex (T : Finset Lattice) :
    LatticeConvex (convexLatticeWindow T) := by
  intro z
  rw [sg_window_hull]
  exact (sg_window_mem T z).symm

private theorem sg_hull_image (S : Finset Lattice) (a : Lattice) (k : ℤ) :
    windowHull (S.image (fun z => a + k • z)) =
      (fun x : RealPlane => embed a + (k : ℝ) • x) '' windowHull S := by
  let f : RealPlane →ᵃ[ℝ] RealPlane :=
    AffineMap.const ℝ RealPlane (embed a) + (k : ℝ) • AffineMap.id ℝ RealPlane
  have himg : embed '' ((S.image (fun z => a + k • z) : Finset Lattice) : Set Lattice) =
      f '' (embed '' (S : Set Lattice)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨embed q, ⟨q, hq, rfl⟩, by ext <;> simp [f, embed]⟩
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨a + k • q, Finset.mem_image.mpr ⟨q, hq, rfl⟩,
        by ext <;> simp [f, embed]⟩
  unfold windowHull
  rw [himg, ← f.image_convexHull]
  rfl

private theorem sg_positioned_hull {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice) (N : ℕ) :
    windowHull (positionedHomothetyWindow C i e N) =
      (fun x : RealPlane => embed e + (2 * ((N : ℝ) + 1)) • x -
        ((N : ℝ) + 1) • (embed (C.vertex i) + embed (C.vertex (i+1)))) '' windowHull S := by
  rw [positionedHomothetyWindow, sg_window_hull]
  have heq : positionedHomothetyVertices C i e N =
      S.image (fun z => (e - (N + 1 : ℕ) • (C.vertex i + C.vertex (i+1))) +
        (2 * (N + 1 : ℕ) : ℤ) • z) := by
    apply Finset.image_congr
    intro z hz
    abel
  rw [heq, sg_hull_image]
  congr 1
  funext x
  ext <;> simp [embed] <;> ring

private theorem sg_positioned_vertex {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice) (N : ℕ)
    (z : Lattice) (hz : z ∈ S) :
    e + (2 * (N + 1 : ℕ) : ℤ) • z -
      (N + 1 : ℕ) • (C.vertex i + C.vertex (i+1)) ∈
      positionedHomothetyWindow C i e N := by
  apply (sg_window_mem _ _).mpr
  exact window_mem_hull _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

private theorem sg_positioned_endpoints {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice) (N : ℕ) :
    e + (N+1 : ℕ) • (C.vertex i - C.vertex (i+1)) ∈ positionedHomothetyWindow C i e N ∧
    e + (N+1 : ℕ) • (C.vertex (i+1) - C.vertex i) ∈ positionedHomothetyWindow C i e N := by
  have h0 := (Finset.mem_filter.mp (C.initial_mem i)).1
  have h1 := (Finset.mem_filter.mp (C.terminal_mem i)).1
  constructor
  · convert sg_positioned_vertex C i e N _ h0 using 1
    ext <;> simp <;> ring
  · convert sg_positioned_vertex C i e N _ h1 using 1
    ext <;> simp <;> ring

private theorem sg_support_hull (S : Finset Lattice) (d a : Lattice)
    (ha : a ∈ supportRow S d) :
    ∀ x ∈ windowHull S, (det d a : ℝ) ≤ realDet (embed d) x := by
  have hs : ∀ q ∈ S, (det d a : ℝ) ≤ realDet (embed d) (embed q) := by
    intro q hq
    have h := (Finset.mem_filter.mp ha).2 q hq
    dsimp [realDot, normal, realDet, embed, det] at h ⊢
    push_cast
    nlinarith
  apply convexHull_min
  · rintro _ ⟨q, hq, rfl⟩
    exact hs q hq
  · change Convex ℝ {x : RealPlane | (det d a : ℝ) ≤ _}
    intro x hx y hy r s hr hs hrs
    dsimp [realDet] at *
    calc
      (det d a : ℝ) ≤ r * ((embed d).1 * x.2 - (embed d).2 * x.1) +
          s * ((embed d).1 * y.2 - (embed d).2 * y.1) := by
        calc
          _ = r * (det d a : ℝ) + s * (det d a : ℝ) := by rw [← add_mul, hrs, one_mul]
          _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx hr) (mul_le_mul_of_nonneg_left hy hs)
      _ = _ := by ring

private theorem sg_support_height {S : Finset Lattice} {d a b : Lattice}
    (ha : a ∈ supportRow S d) (hb : b ∈ supportRow S d) : det d a = det d b := by
  have hab := (Finset.mem_filter.mp ha).2 b (Finset.mem_filter.mp hb).1
  have hba := (Finset.mem_filter.mp hb).2 a (Finset.mem_filter.mp ha).1
  dsimp [realDot, normal, embed] at hab hba
  have h : (det d a : ℝ) = (det d b : ℝ) := by
    dsimp [det]
    push_cast
    linarith
  exact_mod_cast h

private theorem sg_positioned_lower {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice)
    (he : det (C.direction i) e = -1) (N : ℕ) :
    ∀ z ∈ positionedHomothetyWindow C i e N, -1 ≤ det (C.direction i) z := by
  intro z hz
  have hm := window_mem_hull _ hz
  rw [sg_positioned_hull] at hm
  obtain ⟨x, hx, hxeq⟩ := hm
  have hh := sg_support_hull S (C.direction i) (C.vertex i) (C.initial_mem i) x hx
  have hi := sg_support_height (C.initial_mem i) (C.terminal_mem i)
  have heR : (det (C.direction i) e : ℝ) = -1 := by exact_mod_cast he
  have hiR : (det (C.direction i) (C.vertex i) : ℝ) =
      (det (C.direction i) (C.vertex (i+1)) : ℝ) := by exact_mod_cast hi
  have hdet : (det (C.direction i) z : ℝ) =
      -1 + (2*((N:ℝ)+1)) *
        (realDet (embed (C.direction i)) x - (det (C.direction i) (C.vertex i) : ℝ)) := by
    have hx1 := congrArg Prod.fst hxeq
    have hx2 := congrArg Prod.snd hxeq
    dsimp [realDet, embed, det] at hx1 hx2 heR hiR ⊢
    push_cast at heR hiR ⊢
    rw [← hx1, ← hx2]
    nlinarith
  have hreal : (-1:ℝ) ≤ (det (C.direction i) z : ℝ) := by
    rw [hdet]
    have hp : 0 ≤ 2 * ((N:ℝ)+1) := by positivity
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hh)]
  exact_mod_cast hreal

private theorem sg_positioned_anchor {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) :
    ∃ e : Lattice, det (C.direction i) e = -1 :=
  primitive_height_surjective _ (C.primitive i) (-1)

private theorem sg_positioned_endpoint_heights {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice)
    (he : det (C.direction i) e = -1) (N : ℕ) :
    det (C.direction i) (e + (N+1 : ℕ) • (C.vertex i - C.vertex (i+1))) = -1 ∧
    det (C.direction i) (e + (N+1 : ℕ) • (C.vertex (i+1) - C.vertex i)) = -1 := by
  have hi := sg_support_height (C.initial_mem i) (C.terminal_mem i)
  dsimp [det] at *
  constructor <;> nlinarith

private theorem sg_support_of_minimum (T : Finset Lattice) (v z : Lattice)
    (hz : z ∈ T) (hmin : ∀ q ∈ T, det v z ≤ det v q) :
    z ∈ supportRow T v := by
  apply Finset.mem_filter.mpr
  refine ⟨hz, ?_⟩
  intro q hq
  have h : (det v z : ℝ) ≤ (det v q : ℝ) := by exact_mod_cast hmin q hq
  dsimp [realDot, normal, embed, det] at *
  push_cast at h
  nlinarith

private theorem sg_positioned_support {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice)
    (he : det (C.direction i) e = -1) (N : ℕ) :
    (∀ z ∈ supportRow (positionedHomothetyWindow C i e N) (C.direction i),
      det (C.direction i) z = -1) ∧
    e + (N+1 : ℕ) • (C.vertex i - C.vertex (i+1)) ∈
      supportRow (positionedHomothetyWindow C i e N) (C.direction i) ∧
    e + (N+1 : ℕ) • (C.vertex (i+1) - C.vertex i) ∈
      supportRow (positionedHomothetyWindow C i e N) (C.direction i) := by
  have h0 := (sg_positioned_endpoints C i e N).1
  have h1 := (sg_positioned_endpoints C i e N).2
  have hh0 := (sg_positioned_endpoint_heights C i e he N).1
  have hh1 := (sg_positioned_endpoint_heights C i e he N).2
  have hs0 := sg_support_of_minimum _ _ _ h0 (by
    intro q hq
    rw [hh0]
    exact sg_positioned_lower C i e he N q hq)
  have hs1 := sg_support_of_minimum _ _ _ h1 (by
    intro q hq
    rw [hh1]
    exact sg_positioned_lower C i e he N q hq)
  exact ⟨fun z hz => (sg_support_height hz hs0).trans hh0, hs0, hs1⟩

private theorem sg_positioned_mono {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice) :
    ∀ N M, N ≤ M → positionedHomothetyWindow C i e N ⊆ positionedHomothetyWindow C i e M := by
  intro N M hNM z hz
  have hm := window_mem_hull _ hz
  rw [sg_positioned_hull] at hm
  obtain ⟨x, hx, hxeq⟩ := hm
  let c : RealPlane := (1/2 : ℝ) • embed (C.vertex i) + (1/2 : ℝ) • embed (C.vertex (i+1))
  have hc : c ∈ windowHull S :=
    (windowHull_convex S) (window_mem_hull S (Finset.mem_filter.mp (C.initial_mem i)).1)
      (window_mem_hull S (Finset.mem_filter.mp (C.terminal_mem i)).1)
      (by norm_num) (by norm_num) (by norm_num)
  let r : ℝ := ((N : ℝ)+1)/((M : ℝ)+1)
  have hM : (0 : ℝ) < (M:ℝ)+1 := by positivity
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one hM).mpr
    exact_mod_cast Nat.add_le_add_right hNM 1
  have hy : r • x + (1-r) • c ∈ windowHull S :=
    (windowHull_convex S) hx hc hr0 (by linarith) (by ring)
  apply (sg_window_mem _ _).mpr
  have ht : windowHull (positionedHomothetyVertices C i e M) =
      windowHull (positionedHomothetyWindow C i e M) := (sg_window_hull _).symm
  rw [ht, sg_positioned_hull]
  refine ⟨_, hy, ?_⟩
  rw [← hxeq]
  ext <;> dsimp [r, c] <;> field_simp <;> ring

private theorem sg_finite_capture (B : ℕ → Finset Lattice) (U : Set Lattice)
    (hmono : ∀ N M, N ≤ M → B N ⊆ B M) (hcover : (⋃ N, (B N : Set Lattice)) = U) :
    ∀ F : Finset Lattice, (∀ z ∈ F, z ∈ U) → ∃ N, F ⊆ B N := by
  intro F hF
  apply Directed.exists_mem_subset_of_finset_subset_biUnion
    (f := fun n => (B n : Set Lattice))
  · intro a b
    exact ⟨max a b, hmono a _ (le_max_left _ _), hmono b _ (le_max_right _ _)⟩
  · rw [hcover]
    exact hF

private theorem sg_source_area {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) : (interior (windowHull S)).Nonempty := by
  have hm : 0 < 2*m := by have := C.at_least_two; omega
  have hd : C.direction 0 ∈ edgeDirections S :=
    (C.covers _).mpr ⟨⟨0, hm⟩, rfl⟩
  exact hd.2.1

private theorem sg_positioned_area {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice) (N : ℕ) :
    (interior (windowHull (positionedHomothetyWindow C i e N))).Nonempty := by
  rw [sg_positioned_hull]
  have hk : (2 * ((N:ℝ)+1)) ≠ 0 := by positivity
  let f : RealPlane → RealPlane := fun x => embed e + (2 * ((N : ℝ)+1)) • x -
    ((N:ℝ)+1) • (embed (C.vertex i) + embed (C.vertex (i+1)))
  have hf : IsOpenMap f := by
    convert (isOpenMap_add_right (-((N:ℝ)+1) •
      (embed (C.vertex i) + embed (C.vertex (i+1))))).comp
      ((isOpenMap_add_left (embed e)).comp (isOpenMap_smul₀ hk)) using 1
    funext x
    simp only [f, Function.comp_apply, neg_smul, sub_eq_add_neg]
  obtain ⟨x, hx⟩ := sg_source_area C
  exact ⟨f x, hf.image_interior_subset _ ⟨x, hx, rfl⟩⟩

private theorem sg_positioned_nonempty_convex {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice) (N : ℕ) :
    (positionedHomothetyWindow C i e N).Nonempty ∧
      LatticeConvex (positionedHomothetyWindow C i e N) := by
  exact ⟨⟨_, (sg_positioned_endpoints C i e N).1⟩, sg_window_convex _⟩

private theorem sg_strict_interior_support (S : Finset Lattice) (d a : Lattice)
    (hd : Primitive d) (ha : a ∈ supportRow S d) (x : RealPlane)
    (hx : x ∈ interior (windowHull S)) :
    (det d a : ℝ) < realDet (embed d) x := by
  let H : RealPlane →ₗ[ℝ] ℝ :=
    { toFun := fun z => realDet (embed d) z
      map_add' := by intro y z; dsimp [realDet]; ring
      map_smul' := by intro r z; dsimp [realDet]; ring }
  let Hc := H.toContinuousLinearMap
  have hsurj : Function.Surjective Hc := by
    obtain ⟨e, he⟩ := primitive_height_surjective d hd 1
    have heR : realDet (embed d) (embed e) = 1 := by
      change det d e = 1 at he
      dsimp [det] at he
      dsimp [realDet, embed]
      exact_mod_cast he
    intro r
    refine ⟨r • embed e, ?_⟩
    change realDet (embed d) (r • embed e) = r
    calc
      _ = r * realDet (embed d) (embed e) := by dsimp [realDet]; ring
      _ = r := by rw [heR, mul_one]
  have h := (Hc.isOpenMap hsurj).mapsTo_interior
    (show Set.MapsTo Hc (windowHull S) (Set.Ici (det d a : ℝ)) from
      sg_support_hull S d a ha) hx
  rwa [interior_Ici] at h

private theorem sg_triangle_dilations (K : Set RealPlane) (hK : Convex ℝ K)
    (c u y z : RealPlane) (hm : c-u ∈ K) (hp : c+u ∈ K) (hy : c+y ∈ K)
    (hD : 0 < realDet u y) (hz : 0 ≤ realDet u z) :
    ∃ N : ℕ, c + (1 / (2*((N:ℝ)+1))) • z ∈ K := by
  let D := realDet u y
  let a := realDet z y / D
  let b := realDet u z / D
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hb : 0 ≤ b := div_nonneg hz hD.le
  have hab : z = a • u + b • y := by
    have heq : D • z = realDet z y • u + realDet u z • y := by
      ext <;> dsimp [D, realDet] <;> ring
    have h := congrArg (fun p : RealPlane => D⁻¹ • p) heq
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ hD0, one_smul,
      ← div_eq_inv_mul, a, b] using h
  obtain ⟨N, hN⟩ := exists_nat_ge (|a| + b)
  let k : ℝ := 2*((N:ℝ)+1)
  have hk : 0 < k := by dsimp [k]; positivity
  have hk0 := ne_of_gt hk
  have hlarge : |a| + b ≤ k := by
    dsimp [k]
    have hn0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have habs : |a/k| + b/k ≤ 1 := by
    rw [abs_div, abs_of_pos hk, ← add_div]
    exact (div_le_one hk).mpr hlarge
  let weights : Fin 3 → ℝ := ![(1-b/k-a/k)/2, (1-b/k+a/k)/2, b/k]
  let pts : Fin 3 → RealPlane := ![c-u, c+u, c+y]
  have hw : ∀ j : Fin 3, 0 ≤ weights j := by
    intro j
    fin_cases j <;> dsimp [weights]
    · have := le_abs_self (a/k)
      linarith
    · have := neg_abs_le (a/k)
      linarith
    · exact div_nonneg hb hk.le
  have hsum : ∑ j : Fin 3, weights j = 1 := by
    simp [weights, Fin.sum_univ_succ]
    ring
  have hpts : ∀ j : Fin 3, pts j ∈ K := by
    intro j
    fin_cases j
    · exact hm
    · exact hp
    · exact hy
  have hmem := hK.sum_mem (t := Finset.univ) (w := weights) (z := pts)
    (fun j _ => hw j) hsum (fun j _ => hpts j)
  refine ⟨N, ?_⟩
  convert hmem using 1
  simp only [Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero, weights, pts]
  rw [hab]
  ext <;> simp [k] <;> field_simp <;> ring

private theorem sg_positioned_exhaustion {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice)
    (he : det (C.direction i) e = -1) :
    (⋃ N, (positionedHomothetyWindow C i e N : Set Lattice)) =
      {z | -1 ≤ det (C.direction i) z} := by
  ext z
  constructor
  · intro hz
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hz
    exact sg_positioned_lower C i e he N z hN
  · intro hz
    obtain ⟨x, hx⟩ := sg_source_area C
    obtain ⟨k, hk, hkvec⟩ := C.edge_length i
    let c : RealPlane := (1/2 : ℝ) •
      (embed (C.vertex i) + embed (C.vertex (i+1)))
    let u : RealPlane := (1/2 : ℝ) •
      (embed (C.vertex (i+1)) - embed (C.vertex i))
    have hm : c-u ∈ windowHull S := by
      have heq : c-u = embed (C.vertex i) := by ext <;> dsimp [c, u] <;> ring
      rw [heq]
      exact window_mem_hull S (Finset.mem_filter.mp (C.initial_mem i)).1
    have hp : c+u ∈ windowHull S := by
      have heq : c+u = embed (C.vertex (i+1)) := by ext <;> dsimp [c, u] <;> ring
      rw [heq]
      exact window_mem_hull S (Finset.mem_filter.mp (C.terminal_mem i)).1
    have hy : c + (x-c) ∈ windowHull S := by
      simpa only [add_sub_cancel] using interior_subset hx
    have hscale : u = ((k:ℝ)/2) • embed (C.direction i) := by
      have h1 := congrArg Prod.fst hkvec
      have h2 := congrArg Prod.snd hkvec
      have h1R : (C.vertex (i+1)).1 - (C.vertex i).1 = k * (C.direction i).1 := h1
      have h2R : (C.vertex (i+1)).2 - (C.vertex i).2 = k * (C.direction i).2 := h2
      have h1c : ((C.vertex (i+1)).1:ℝ) - (C.vertex i).1 = (k:ℝ) * (C.direction i).1 := by exact_mod_cast h1R
      have h2c : ((C.vertex (i+1)).2:ℝ) - (C.vertex i).2 = (k:ℝ) * (C.direction i).2 := by exact_mod_cast h2R
      ext <;> dsimp [u, embed] <;> nlinarith
    have hc : realDet (embed (C.direction i)) c =
        (det (C.direction i) (C.vertex i) : ℝ) := by
      have hi := sg_support_height (C.initial_mem i) (C.terminal_mem i)
      have hiR : (det (C.direction i) (C.vertex i) : ℝ) =
          (det (C.direction i) (C.vertex (i+1)) : ℝ) := by exact_mod_cast hi
      dsimp [c, realDet, embed, det] at *
      push_cast at *
      nlinarith
    have hstrict := sg_strict_interior_support S (C.direction i) (C.vertex i)
      (C.primitive i) (C.initial_mem i) x hx
    have hD : 0 < realDet u (x-c) := by
      rw [hscale]
      have hdet : realDet (((k:ℝ)/2) • embed (C.direction i)) (x-c) =
          ((k:ℝ)/2) * (realDet (embed (C.direction i)) x -
            realDet (embed (C.direction i)) c) := by dsimp [realDet]; ring
      rw [hdet, hc]
      have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      exact mul_pos (by positivity) (sub_pos.mpr hstrict)
    have hzD : 0 ≤ realDet u (embed z - embed e) := by
      rw [hscale]
      have hdet : realDet (((k:ℝ)/2) • embed (C.direction i)) (embed z-embed e) =
          ((k:ℝ)/2) * ((det (C.direction i) z : ℝ) - (det (C.direction i) e : ℝ)) := by
        dsimp [realDet, embed, det]
        push_cast
        ring
      rw [hdet]
      have hze : det (C.direction i) e ≤ det (C.direction i) z := by
        rw [he]
        exact hz
      have hzeR : (det (C.direction i) e : ℝ) ≤ (det (C.direction i) z : ℝ) := by
        exact_mod_cast hze
      have hkR : (0:ℝ) ≤ k := by exact_mod_cast (show 0 ≤ k by omega)
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hzeR)
    obtain ⟨N, hN⟩ := sg_triangle_dilations (windowHull S) (windowHull_convex S)
      c u (x-c) (embed z-embed e) hm hp hy hD hzD
    apply Set.mem_iUnion.mpr
    refine ⟨N, (sg_window_mem _ _).mpr ?_⟩
    rw [← sg_window_hull (positionedHomothetyVertices C i e N)]
    change embed z ∈ windowHull (positionedHomothetyWindow C i e N)
    rw [sg_positioned_hull]
    refine ⟨_, hN, ?_⟩
    have hkN : (2*((N:ℝ)+1)) ≠ 0 := by positivity
    ext <;> dsimp [c] <;> field_simp <;> ring

private theorem sg_hull_minimizers (S : Finset Lattice) (d a : Lattice)
    (ha : a ∈ supportRow S d) (x : RealPlane) (hx : x ∈ windowHull S)
    (hxeq : realDet (embed d) x = (det d a : ℝ)) :
    x ∈ windowHull (supportRow S d) := by
  let H : RealPlane →ₗ[ℝ] ℝ :=
    { toFun := fun z => realDet (embed d) z
      map_add' := by intro y z; dsimp [realDet]; ring
      map_smul' := by intro r z; dsimp [realDet]; ring }
  let t : ℝ := det d a
  let T : Set RealPlane := {y | t ≤ H y ∧ (H y = t → y ∈ windowHull (supportRow S d))}
  have hS : embed '' (S : Set Lattice) ⊆ T := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨sg_support_hull S d a ha _ (window_mem_hull S hq), ?_⟩
    intro h
    have heq : det d q = det d a := by
      change realDet (embed d) (embed q) = (det d a : ℝ) at h
      have hd : realDet (embed d) (embed q) = (det d q : ℝ) := by
        dsimp [realDet, embed, det]; push_cast; ring
      rw [hd] at h
      exact_mod_cast h
    apply window_mem_hull
    apply sg_support_of_minimum S d q hq
    intro r hr
    rw [heq]
    have hb := sg_support_hull S d a ha _ (window_mem_hull S hr)
    have hd : realDet (embed d) (embed r) = (det d r : ℝ) := by
      dsimp [realDet, embed, det]; push_cast; ring
    rw [hd] at hb
    exact_mod_cast hb
  have hT : Convex ℝ T := by
    intro y hy z hz r s hr hs hrs
    change t ≤ H (r • y + s • z) ∧ _
    simp only [map_add, map_smul, smul_eq_mul]
    have hlo : t ≤ r * H y + s * H z := by
      calc
        _ = r*t+s*t := by rw [← add_mul, hrs, one_mul]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hy.1 hr)
          (mul_le_mul_of_nonneg_left hz.1 hs)
    refine ⟨hlo, ?_⟩
    intro heq
    by_cases hr0 : r = 0
    · have hs1 : s = 1 := by linarith
      simp only [hr0, hs1, zero_smul, one_smul, zero_add]
      apply hz.2
      simpa only [hr0, hs1, zero_mul, one_mul, zero_add] using heq
    by_cases hs0 : s = 0
    · have hr1 : r = 1 := by linarith
      simp only [hs0, hr1, zero_smul, one_smul, add_zero]
      apply hy.2
      simpa only [hs0, hr1, zero_mul, one_mul, add_zero] using heq
    have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hprod : r * (H y-t) + s * (H z-t) = 0 := by
      calc
        _ = (r*H y+s*H z)-(r+s)*t := by ring
        _ = 0 := by rw [heq, hrs]; ring
    have hry : H y = t := by
      have he : r * (H y-t) = 0 := le_antisymm
        (by nlinarith [mul_nonneg hs (sub_nonneg.mpr hz.1)])
        (mul_nonneg hr (sub_nonneg.mpr hy.1))
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hr0)
    have hsz : H z = t := by
      have he : s * (H z-t) = 0 := le_antisymm
        (by nlinarith [mul_nonneg hr (sub_nonneg.mpr hy.1)])
        (mul_nonneg hs (sub_nonneg.mpr hz.1))
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hs0)
    exact (windowHull_convex _) (hy.2 hry) (hz.2 hsz) hr hs hrs
  exact ((convexHull_min hS hT) hx).2 hxeq

private theorem sg_real_det_embed (d z : Lattice) :
    realDet (embed d) (embed z) = (det d z : ℝ) := by
  dsimp [realDet, embed, det]
  push_cast
  ring

private theorem sg_hom_height (d a : Lattice) (k : ℤ) (x : RealPlane) :
    realDet (embed d) (embed a + (k:ℝ) • x) =
      (det d a : ℝ) + (k:ℝ) * realDet (embed d) x := by
  dsimp [realDet, embed, det]
  push_cast
  ring

private theorem sg_embed_hom (a : Lattice) (k : ℤ) (q : Lattice) :
    embed (a+k•q) = embed a + (k:ℝ) • embed q := by
  ext <;> simp [embed]

private theorem sg_hom_support_image (S : Finset Lattice) (d a : Lattice) (k : ℤ)
    (hk : 0 < k) (q : Lattice) (hq : q ∈ supportRow S d) :
    a+k•q ∈ supportRow (convexLatticeWindow (S.image (fun z => a+k•z))) d := by
  apply sg_support_of_minimum
  · apply (sg_window_mem _ _).mpr
    exact window_mem_hull _ (Finset.mem_image.mpr ⟨q, (Finset.mem_filter.mp hq).1, rfl⟩)
  · intro z hz
    have hzH := (sg_window_mem _ _).mp hz
    rw [sg_hull_image] at hzH
    obtain ⟨x, hx, heq⟩ := hzH
    have hlow := sg_support_hull S d q hq x hx
    have hr : realDet (embed d) (embed (a+k•q)) ≤ realDet (embed d) (embed z) := by
      rw [sg_embed_hom, ← heq, sg_hom_height, sg_hom_height, sg_real_det_embed]
      have hb := mul_le_mul_of_nonneg_left hlow (show (0:ℝ) ≤ k by exact_mod_cast hk.le)
      linarith
    rw [sg_real_det_embed, sg_real_det_embed] at hr
    exact_mod_cast hr

private theorem sg_hom_support_pullback (S : Finset Lattice) (d a : Lattice) (k : ℤ)
    (hk : 0 < k) (q : Lattice) (hq : q ∈ supportRow S d) (z : Lattice)
    (hz : z ∈ supportRow (convexLatticeWindow (S.image (fun z => a+k•z))) d) :
    embed z ∈ (fun x : RealPlane => embed a+(k:ℝ)•x) '' windowHull (supportRow S d) := by
  have hzH := (sg_window_mem _ _).mp (Finset.mem_filter.mp hz).1
  rw [sg_hull_image] at hzH
  obtain ⟨x, hx, heq⟩ := hzH
  refine ⟨x, sg_hull_minimizers S d q hq x hx ?_, heq⟩
  have ht := sg_support_height hz (sg_hom_support_image S d a k hk q hq)
  have htR : realDet (embed d) (embed z) = realDet (embed d) (embed (a+k•q)) := by
    rw [sg_real_det_embed, sg_real_det_embed, ht]
  rw [← heq, sg_embed_hom, sg_hom_height, sg_hom_height, sg_real_det_embed] at htR
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  exact (mul_left_cancel₀ hkR (add_left_cancel htR))

private theorem sg_hom_injective (a : Lattice) (k : ℤ) (hk : 0 < k) :
    Function.Injective (fun z : Lattice => a+k•z) := by
  intro z q h
  have heq : k • z = k • q := add_left_cancel h
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  apply Prod.ext
  · exact mul_left_cancel₀ (ne_of_gt hk) h1
  · exact mul_left_cancel₀ (ne_of_gt hk) h2

private theorem sg_hom_card_lower (S : Finset Lattice) (d a : Lattice) (k : ℤ)
    (hk : 0 < k) :
    (supportRow S d).card ≤
      (supportRow (convexLatticeWindow (S.image (fun z => a+k•z))) d).card := by
  classical
  have hsub : (supportRow S d).image (fun z => a+k•z) ⊆
      supportRow (convexLatticeWindow (S.image (fun z => a+k•z))) d := by
    rintro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    exact sg_hom_support_image S d a k hk q hq
  simpa only [Finset.card_image_of_injective _ (sg_hom_injective a k hk)] using Finset.card_le_card hsub

private theorem sg_embed_injective : Function.Injective embed := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext <;> dsimp [embed] at h1 h2
  · exact_mod_cast h1
  · exact_mod_cast h2

private theorem sg_hom_edge_directions (S : Finset Lattice) (hS : S.Nonempty)
    (a : Lattice) (k : ℤ) (hk : 0 < k)
    (hareaS : (interior (windowHull S)).Nonempty)
    (hareaT : (interior (windowHull (convexLatticeWindow (S.image (fun z => a+k•z))))).Nonempty) :
    edgeDirections (convexLatticeWindow (S.image (fun z => a+k•z))) = edgeDirections S := by
  classical
  ext d
  constructor
  · intro hd
    refine ⟨hd.1, hareaS, ?_⟩
    by_contra hcard
    have hsmall : (supportRow S d).card ≤ 1 := by omega
    obtain ⟨q, hqS, hqmin⟩ := S.exists_min_image (det d) hS
    have hq := sg_support_of_minimum S d q hqS hqmin
    have hsingle : supportRow S d = {q} := by
      apply Finset.Subset.antisymm
      · intro z hz
        exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hsmall) z hz q hq)
      · simpa using hq
    have hpoint : ∀ z ∈ supportRow (convexLatticeWindow (S.image (fun z => a+k•z))) d,
        z = a+k•q := by
      intro z hz
      have hp := sg_hom_support_pullback S d a k hk q hq z hz
      rw [hsingle] at hp
      have hH : windowHull ({q} : Finset Lattice) = {embed q} := by
        simp [windowHull]
      rw [hH, Set.image_singleton] at hp
      apply sg_embed_injective
      exact hp.trans (sg_embed_hom a k q).symm
    have hsmallT : (supportRow (convexLatticeWindow (S.image (fun z => a+k•z))) d).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro z hz p hp
      exact (hpoint z hz).trans (hpoint p hp).symm
    have := hd.2.2
    omega
  · intro hd
    exact ⟨hd.1, hareaT, hd.2.2.trans (sg_hom_card_lower S d a k hk)⟩

private theorem sg_positioned_as_hom {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice) (N : ℕ) :
    positionedHomothetyWindow C i e N =
      convexLatticeWindow (S.image (fun z =>
        (e - (N+1 : ℕ) • (C.vertex i + C.vertex (i+1))) + (2*(N+1 : ℕ):ℤ) • z)) := by
  unfold positionedHomothetyWindow positionedHomothetyVertices
  congr 1
  apply Finset.image_congr
  intro z hz
  abel

private theorem sg_positioned_enveloped {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (e : Lattice) (N : ℕ) :
    EnvelopedWindow S (positionedHomothetyWindow C i e N) := by
  have hne := (sg_positioned_nonempty_convex C i e N).1
  have hconv := (sg_positioned_nonempty_convex C i e N).2
  have harea := sg_positioned_area C i e N
  have hk : (0:ℤ) < (2*(N+1 : ℕ):ℤ) := by positivity
  have hS : S.Nonempty := ⟨C.vertex i, (Finset.mem_filter.mp (C.initial_mem i)).1⟩
  have heq : edgeDirections (positionedHomothetyWindow C i e N) = edgeDirections S := by
    rw [sg_positioned_as_hom]
    apply sg_hom_edge_directions S hS _ _ hk (sg_source_area C)
    rwa [← sg_positioned_as_hom]
  refine ⟨hne, hconv, harea, ?_, congrArg Set.ncard heq⟩
  intro d hd
  refine ⟨heq ▸ hd, ?_⟩
  rw [sg_positioned_as_hom]
  exact sg_hom_card_lower S d _ _ hk

private theorem sg_segment_lattice (p d : Lattice) (hd : Primitive d) (L : ℤ)
    (hL : 0 < L) (z : Lattice) :
    embed z ∈ segment ℝ (embed p) (embed (p+L•d)) ↔
      ∃ n : ℤ, 0 ≤ n ∧ n ≤ L ∧ z = p+n•d := by
  obtain ⟨e, he⟩ := primitive_height_surjective d hd 1
  change det d e = 1 at he
  constructor
  · rintro ⟨r, s, hr, hs, hrs, hseg⟩
    have hlin : embed z = embed p + (s*(L:ℝ)) • embed d := by
      rw [← hseg, sg_embed_hom]
      have hr' : r = 1-s := by linarith
      rw [hr']
      ext <;> dsimp <;> ring
    let n : ℤ := det (z-p) e
    have hn : (n:ℝ) = s*(L:ℝ) := by
      dsimp [n]
      rw [← sg_real_det_embed]
      have hsub : embed (z-p) = embed z-embed p := by ext <;> simp [embed]
      rw [hsub, hlin, add_sub_cancel_left]
      calc
        realDet ((s*(L:ℝ)) • embed d) (embed e) =
            (s*(L:ℝ))*realDet (embed d) (embed e) := by dsimp [realDet]; ring
        _ = s*(L:ℝ) := by rw [sg_real_det_embed, he]; simp
    refine ⟨n, ?_, ?_, ?_⟩
    · have hnR : (0:ℝ) ≤ n := by rw [hn]; positivity
      exact_mod_cast hnR
    · have hs1 : s ≤ 1 := by linarith
      have hnR : (n:ℝ) ≤ L := by
        rw [hn]
        exact mul_le_of_le_one_left (by exact_mod_cast hL.le) hs1
      exact_mod_cast hnR
    · apply sg_embed_injective
      rw [sg_embed_hom, hn]
      exact hlin
  · rintro ⟨n, hn0, hnL, rfl⟩
    have hLR : (0:ℝ) < L := by exact_mod_cast hL
    have hnR : (0:ℝ) ≤ n := by exact_mod_cast hn0
    have hnLR : (n:ℝ) ≤ L := by exact_mod_cast hnL
    refine ⟨1-(n:ℝ)/L, (n:ℝ)/L, ?_, by positivity, by ring, ?_⟩
    · exact sub_nonneg.mpr ((div_le_one hLR).mpr hnLR)
    · rw [sg_embed_hom, sg_embed_hom]
      ext <;> dsimp <;> field_simp <;> ring

private theorem sg_run_injective (p d : Lattice) (hd : Primitive d) :
    Function.Injective (fun n : ℤ => p+n•d) := by
  obtain ⟨e, he⟩ := primitive_height_surjective d hd 1
  change det d e = 1 at he
  intro n t h
  have hdif : n•d = t•d := add_left_cancel h
  have hc := congrArg (fun x => det x e) hdif
  have hn : det (n•d) e = n*det d e := by dsimp [det]; ring
  have ht : det (t•d) e = t*det d e := by dsimp [det]; ring
  rwa [hn, ht, he, mul_one, mul_one] at hc

private theorem sg_cycle_support_hull {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (j : ℤ) :
    windowHull (supportRow S (C.direction j)) =
      segment ℝ (embed (C.vertex j)) (embed (C.vertex (j+1))) := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨z, hz, rfl⟩
      exact ((C.support_segment j z).mp hz).2
    · exact convex_segment _ _
  · exact (windowHull_convex _).segment_subset
      (window_mem_hull _ (C.initial_mem j)) (window_mem_hull _ (C.terminal_mem j))

private theorem sg_hom_segment (a : Lattice) (k : ℤ) (p q : Lattice) :
    (fun x : RealPlane => embed a+(k:ℝ)•x) '' segment ℝ (embed p) (embed q) =
      segment ℝ (embed (a+k•p)) (embed (a+k•q)) := by
  let f : RealPlane →ᵃ[ℝ] RealPlane :=
    AffineMap.const ℝ RealPlane (embed a) + (k:ℝ) • AffineMap.id ℝ RealPlane
  rw [sg_embed_hom, sg_embed_hom]
  exact image_segment ℝ f (embed p) (embed q)

private theorem sg_run_card (p d : Lattice) (hd : Primitive d) (L : ℕ) :
    ((Finset.Icc (0:ℤ) (L:ℤ)).image (fun n => p+n•d)).card = L+1 := by
  rw [Finset.card_image_of_injective _ (sg_run_injective p d hd), Int.card_Icc]
  simp

private theorem sg_cycle_card_bound {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (j : ℤ) (L : ℕ) (hL : 0 < L)
    (hlen : C.vertex (j+1)-C.vertex j = (L:ℤ) • C.direction j) :
    (supportRow S (C.direction j)).card ≤ L+1 := by
  classical
  have hq : C.vertex (j+1) = C.vertex j+(L:ℤ) • C.direction j := by
    rw [← hlen]; abel
  have hsub : supportRow S (C.direction j) ⊆
      (Finset.Icc (0:ℤ) (L:ℤ)).image (fun n => C.vertex j+n•C.direction j) := by
    intro z hz
    have hseg := ((C.support_segment j z).mp hz).2
    rw [hq] at hseg
    obtain ⟨n, hn0, hnL, hzeq⟩ := (sg_segment_lattice _ _ (C.primitive j) _ (by exact_mod_cast hL) z).mp hseg
    exact Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨hn0, hnL⟩, hzeq.symm⟩
  have hc := Finset.card_le_card hsub
  rwa [sg_run_card _ _ (C.primitive j)] at hc

private theorem sg_hom_cycle_card {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (j : ℤ) (a : Lattice) (k L : ℕ)
    (hk : 0 < k) (hL : 0 < L)
    (hlen : C.vertex (j+1)-C.vertex j = (L:ℤ) • C.direction j) :
    (supportRow (convexLatticeWindow (S.image (fun z => a+(k:ℤ)•z))) (C.direction j)).card = k*L+1 := by
  classical
  let T := convexLatticeWindow (S.image (fun z => a+(k:ℤ)•z))
  let p := a+(k:ℤ)•C.vertex j
  let q := a+(k:ℤ)•C.vertex (j+1)
  let d := C.direction j
  have hkZ : (0:ℤ) < k := by exact_mod_cast hk
  have hkL : (0:ℤ) < (k*L:ℕ) := by exact_mod_cast Nat.mul_pos hk hL
  have hq : q = p+((k*L:ℕ):ℤ)•d := by
    dsimp [p, q, d]
    have hvertex : C.vertex (j+1) = C.vertex j+(L:ℤ) • C.direction j := by
      rw [← hlen]; abel
    rw [hvertex, smul_add, smul_smul]
    abel
  have hpT : p ∈ supportRow T d := sg_hom_support_image S d a k hkZ _ (C.initial_mem j)
  have hqT : q ∈ supportRow T d := sg_hom_support_image S d a k hkZ _ (C.terminal_mem j)
  have heq : supportRow T d =
      (Finset.Icc (0:ℤ) ((k*L:ℕ):ℤ)).image (fun n => p+n•d) := by
    ext z
    constructor
    · intro hz
      have hseg := sg_hom_support_pullback S d a k hkZ _ (C.initial_mem j) z hz
      rw [sg_cycle_support_hull C j, sg_hom_segment] at hseg
      change embed z ∈ segment ℝ (embed p) (embed q) at hseg
      rw [hq] at hseg
      obtain ⟨n, hn0, hnL, hn⟩ := (sg_segment_lattice p d (C.primitive j) _ hkL z).mp hseg
      exact Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨hn0, hnL⟩, hn.symm⟩
    · intro hz
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
      have hseg : embed (p+n•d) ∈ segment ℝ (embed p) (embed q) := by
        rw [hq]
        exact (sg_segment_lattice p d (C.primitive j) _ hkL _).mpr
          ⟨n, (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2, rfl⟩
      have hmem : p+n•d ∈ T := by
        apply (sg_window_convex _ _).mp
        exact (windowHull_convex T).segment_subset
          (window_mem_hull T (Finset.mem_filter.mp hpT).1)
          (window_mem_hull T (Finset.mem_filter.mp hqT).1) hseg
      apply sg_support_of_minimum T d _ hmem
      intro z hz
      have hbase := sg_support_hull T d p hpT _ (window_mem_hull T hz)
      rw [sg_real_det_embed] at hbase
      have hdet : det d (p+n•d) = det d p := by dsimp [det]; ring
      rw [hdet]
      exact_mod_cast hbase
  rw [heq, sg_run_card p d (C.primitive j)]

/-- Integer homotheties centred on the selected edge midpoint. -/
theorem positioned_integer_homothetic_windows {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) :
    ∃ e : Lattice, det (C.direction i) e = -1 ∧
      let B := positionedHomothetyWindow C i e
      (∀ N, EnvelopedWindow S (B N)) ∧
      (∀ N M, N ≤ M → B N ⊆ B M) ∧
      (∀ N, ∀ z ∈ supportRow (B N) (C.direction i), det (C.direction i) z = -1) ∧
      (∀ N, ∀ j : ℤ, ∃ L : ℕ, 0 < L ∧
        C.vertex (j + 1) - C.vertex j = (L : ℤ) • C.direction j ∧
        (supportRow S (C.direction j)).card ≤ L + 1 ∧
        (supportRow (B N) (C.direction j)).card = 2 * (N + 1) * L + 1) ∧
      (∀ N, e + (N + 1 : ℕ) • (C.vertex i - C.vertex (i + 1)) ∈
        supportRow (B N) (C.direction i)) ∧
      (∀ N, e + (N + 1 : ℕ) • (C.vertex (i + 1) - C.vertex i) ∈
        supportRow (B N) (C.direction i)) ∧
      (⋃ N, (B N : Set Lattice)) = {z | -1 ≤ det (C.direction i) z} ∧
      ∀ F : Finset Lattice, (∀ z ∈ F, -1 ≤ det (C.direction i) z) →
        ∃ N, F ⊆ B N := by
  obtain ⟨e, he⟩ := sg_positioned_anchor C i
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sg_positioned_enveloped C i e
  · exact sg_positioned_mono C i e
  · intro N
    exact (sg_positioned_support C i e he N).1
  · intro N j
    obtain ⟨k, hk, hlen⟩ := C.edge_length j
    have hk0 : 0 ≤ k := by omega
    have hL : 0 < k.toNat := by omega
    have hlenN : C.vertex (j+1)-C.vertex j = (k.toNat:ℤ) • C.direction j := by
      simpa only [Int.toNat_of_nonneg hk0] using hlen
    refine ⟨k.toNat, hL, hlenN, sg_cycle_card_bound C j k.toNat hL hlenN, ?_⟩
    rw [sg_positioned_as_hom]
    exact sg_hom_cycle_card C j _ (2*(N+1)) k.toNat (by positivity) hL hlenN
  · intro N
    exact (sg_positioned_support C i e he N).2.1
  · intro N
    exact (sg_positioned_support C i e he N).2.2
  · exact sg_positioned_exhaustion C i e he
  · exact sg_finite_capture _ _ (sg_positioned_mono C i e) (sg_positioned_exhaustion C i e he)

end
end ConvexNivat.Colle
