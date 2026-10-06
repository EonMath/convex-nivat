import ConvexNivat.Colle.Shared.RowCoordinates
import ConvexNivat.Colle.Shared.Sweeps

namespace ConvexNivat.Colle
noncomputable section

private theorem domain_contains (U : Set Lattice) (steps : List (Lattice × Lattice)) :
    U ⊆ sweepDomain U steps := by
  induction steps generalizing U with
  | nil => exact Set.Subset.rfl
  | cons a t ih => exact Set.Subset.trans Set.subset_union_left (ih _)

private theorem domain_mono {U V : Set Lattice} (h : U ⊆ V)
    (steps : List (Lattice × Lattice)) : sweepDomain U steps ⊆ sweepDomain V steps := by
  induction steps generalizing U V with
  | nil => exact h
  | cons a t ih => exact ih (Set.union_subset_union h Set.Subset.rfl)

private theorem domain_append (U : Set Lattice) (s t : List (Lattice × Lattice)) :
    sweepDomain U (s ++ t) = sweepDomain (sweepDomain U s) t := by
  simp [sweepDomain, List.foldl_append]

private theorem valid_mono {S : Finset Lattice} {U V : Set Lattice}
    {s : List (Lattice × Lattice)} (hs : ValidGeneratingSweep S U s) (hUV : U ⊆ V) :
    ValidGeneratingSweep S V s := by
  induction hs generalizing V with
  | nil => exact .nil _
  | cons U u z steps hv he hr ih =>
    exact .cons V u z steps hv (fun q hq => hUV (he q hq))
      (ih (Set.union_subset_union hUV Set.Subset.rfl))

private theorem valid_append {S : Finset Lattice} {U : Set Lattice}
    {s t : List (Lattice × Lattice)} (hs : ValidGeneratingSweep S U s)
    (ht : ValidGeneratingSweep S (sweepDomain U s) t) :
    ValidGeneratingSweep S U (s ++ t) := by
  induction hs with
  | nil => exact ht
  | cons U u z steps hv he hr ih => exact .cons _ _ _ _ hv he (ih ht)

private theorem sweep_union {S F K : Finset Lattice} {U : Set Lattice}
    (hF : HasFiniteSweep S U F) (hK : HasFiniteSweep S U K) :
    HasFiniteSweep S U (F ∪ K) := by
  classical
  obtain ⟨s, hs, hF⟩ := hF
  obtain ⟨t, ht, hK⟩ := hK
  refine ⟨s ++ t, valid_append hs (valid_mono ht (domain_contains U s)), ?_⟩
  rw [domain_append]
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact domain_contains _ t (hF hz)
  · exact domain_mono (domain_contains U s) t (hK hz)

private theorem sweep_of_points {S F : Finset Lattice} {U : Set Lattice}
    (h : ∀ z ∈ F, HasFiniteSweep S U {z}) : HasFiniteSweep S U F := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨[], .nil U, by simp⟩
  | @insert z F hz ih =>
    have hF := ih (fun q hq => h q (Finset.mem_insert_of_mem hq))
    simpa using sweep_union (h z (Finset.mem_insert_self _ _)) hF

private theorem sweep_one_step {S : Finset Lattice} {U : Set Lattice}
    (u p : Lattice) (hp : WindowVertex S p)
    (hq : ∀ q ∈ S.erase p, HasFiniteSweep S U {u + q}) :
    HasFiniteSweep S U {u + p} := by
  classical
  have hF : HasFiniteSweep S U ((S.erase p).image (u + ·)) := by
    apply sweep_of_points
    intro z hz
    obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hz
    exact hq q hqS
  obtain ⟨steps, hs, hF⟩ := hF
  refine ⟨steps ++ [(u, p)], valid_append hs ?_, ?_⟩
  · refine .cons _ u p [] hp (fun q hqS => hF (Finset.mem_image.mpr ⟨q, hqS, rfl⟩)) (.nil _)
  · rw [domain_append]
    intro z hz
    have : z = u + p := Finset.mem_singleton.mp hz
    simp [this, sweepDomain]

private theorem det_add_local (v a b : Lattice) : det v (a + b) = det v a + det v b := by
  dsimp [det]; ring

private theorem det_sub_local (v a b : Lattice) : det v (a - b) = det v a - det v b := by
  dsimp [det]; ring

private theorem singleton_support_vertex {S : Finset Lattice} (hc : LatticeConvex S)
    (v : Lattice) (hcard : (supportRow S v).card = 1) :
    ∃ p, WindowVertex S p ∧ ∀ q ∈ S.erase p, det v p < det v q := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  have hpface : p ∈ supportRow S v := by rw [hp]; simp
  have hpS : p ∈ S := (Finset.mem_filter.mp hpface).1
  have hmin : ∀ q ∈ S, det v p ≤ det v q := by
    intro q hq
    have h := (Finset.mem_filter.mp hpface).2 q hq
    change realDot (embed p) (normal v) ≤ realDot (embed q) (normal v) at h
    rw [normal_height, normal_height] at h
    exact_mod_cast h
  have hs : ∀ q ∈ S.erase p, det v p < det v q := by
    intro q hq
    obtain ⟨hne, hqS⟩ := Finset.mem_erase.mp hq
    apply lt_of_le_of_ne (hmin q hqS)
    intro he
    have hqface : q ∈ supportRow S v := by
      apply Finset.mem_filter.mpr
      refine ⟨hqS, ?_⟩
      intro r hr
      rw [normal_height, normal_height]
      exact_mod_cast (show det v q ≤ det v r by rw [← he]; exact hmin r hr)
    rw [hp] at hqface
    exact hne (Finset.mem_singleton.mp hqface)
  refine ⟨p, ⟨hpS, ?_⟩, hs⟩
  have hlinear : IsLinearMap ℝ (realDet (embed v)) := by
    constructor
    · intro x y; dsimp [realDet]; ring
    · intro r x; dsimp [realDet]; ring
  have hhalf : windowHull (S.erase p) ⊆ {x | (det v p : ℝ) < realDet (embed v) x} := by
    apply convexHull_min _ (convex_halfSpace_gt hlinear _)
    rintro _ ⟨q, hq, rfl⟩
    have h := hs q hq
    dsimp [realDet, embed, det] at *
    exact_mod_cast h
  have hhull : windowHull (S.erase p) ⊆ windowHull S :=
    convexHull_mono (Set.image_mono (by intro z hz; exact Finset.mem_of_mem_erase hz))
  intro z
  constructor
  · intro hz
    have hzS := (hc z).mp (hhull hz)
    refine Finset.mem_erase.mpr ⟨?_, hzS⟩
    intro he
    subst z
    have h := hhalf hz
    change (det v p : ℝ) < realDet (embed v) (embed p) at h
    have he : realDet (embed v) (embed p) = (det v p : ℝ) := by simp [realDet, embed, det]
    rw [he] at h
    exact lt_irrefl _ h
  · intro hz
    exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩

theorem no_parallel_edge_two_sided_strip_sweep (ξ : Configuration ℤ)
    (G B : Finset Lattice) (hG : GeneratingSet ξ G) (v : Lattice) (hv : Primitive v)
    (hnoparallel : v ∉ edgeDirections G ∧ -v ∉ edgeDirections G)
    (hfaces : (supportRow G v).card = 1 ∧ (supportRow G (-v)).card = 1)
    (hfilled : ∃ lo hi : ℤ, lo ≤ hi ∧
      halfStrip B v ∪ halfStrip B (-v) = latticeStrip v lo hi)
    (hwidth : ∃ u : Lattice, (windowTranslate G u : Set Lattice) ⊆
      halfStrip B v ∪ halfStrip B (-v)) :
    (∀ F : Finset Lattice, HasFiniteSweep G (halfStrip B v ∪ halfStrip B (-v)) F) ∧
    (∀ x ∈ OrbitClosure ξ, ∀ y ∈ OrbitClosure ξ,
      AgreesOn x y (halfStrip B v ∪ halfStrip B (-v)) → x = y) := by
  classical
  obtain ⟨lo, hi, hlohi, hstrip⟩ := hfilled
  obtain ⟨p, hp, hmin⟩ := singleton_support_vertex hG.2.1 v hfaces.1
  obtain ⟨q, hq, hmaxneg⟩ := singleton_support_vertex hG.2.1 (-v) hfaces.2
  have hneg : ∀ r : Lattice, det (-v) r = -det v r := by
    intro r; dsimp [det]; ring
  have hmax : ∀ r ∈ G.erase q, det v r < det v q := by
    intro r hr
    have h := hmaxneg r hr
    rw [hneg, hneg] at h
    omega
  have hmin_all : ∀ r ∈ G, det v p ≤ det v r := by
    intro r hr
    by_cases he : r = p
    · subst r; rfl
    · exact (hmin r (Finset.mem_erase.mpr ⟨he, hr⟩)).le
  have hmax_all : ∀ r ∈ G, det v r ≤ det v q := by
    intro r hr
    by_cases he : r = q
    · subst r; rfl
    · exact (hmax r (Finset.mem_erase.mpr ⟨he, hr⟩)).le
  obtain ⟨u, hu⟩ := hwidth
  have hpfit : u + p ∈ latticeStrip v lo hi := by
    rw [← hstrip]
    apply hu
    exact Finset.mem_image.mpr ⟨p, hp.1, by simp [add_comm]⟩
  have hqfit : u + q ∈ latticeStrip v lo hi := by
    rw [← hstrip]
    apply hu
    exact Finset.mem_image.mpr ⟨q, hq.1, by simp [add_comm]⟩
  have hwidth' : det v q - det v p ≤ hi - lo := by
    obtain ⟨hpl, hpu⟩ := hpfit
    obtain ⟨hql, hqu⟩ := hqfit
    rw [det_add_local] at hpl hpu hql hqu
    omega
  let U := halfStrip B v ∪ halfStrip B (-v)
  have hexpand : ∀ n : ℕ, ∀ z : Lattice,
      lo - (n : ℤ) ≤ det v z → det v z ≤ hi + (n : ℤ) → HasFiniteSweep G U {z} := by
    intro n
    induction n with
    | zero =>
      intro z hzlo hzhi
      refine ⟨[], .nil U, ?_⟩
      intro r hr
      have he : r = z := Finset.mem_singleton.mp hr
      subst r
      change z ∈ U
      dsimp [U]
      rw [hstrip]
      exact ⟨by simpa using hzlo, by simpa using hzhi⟩
    | succ n ih =>
      intro z hzlo hzhi
      by_cases hzl : lo - (n : ℤ) ≤ det v z
      · by_cases hzh : det v z ≤ hi + (n : ℤ)
        · exact ih z hzl hzh
        · have hstep := sweep_one_step (U := U) (z - q) q hq (by
            intro r hr
            apply ih
            · have hlow := hmin_all r (Finset.mem_of_mem_erase hr)
              rw [det_add_local, det_sub_local]
              omega
            · have hstrict := hmax r hr
              rw [det_add_local, det_sub_local]
              omega)
          simpa using hstep
      · have hstep := sweep_one_step (U := U) (z - p) p hp (by
          intro r hr
          apply ih
          · have hstrict := hmin r hr
            rw [det_add_local, det_sub_local]
            omega
          · have hupper := hmax_all r (Finset.mem_of_mem_erase hr)
            rw [det_add_local, det_sub_local]
            omega)
        simpa using hstep
  have hpoint : ∀ z : Lattice, HasFiniteSweep G U {z} := by
    intro z
    obtain ⟨n, hn⟩ := exists_nat_ge (max (lo - det v z) (det v z - hi))
    have h1 := le_max_left (lo - det v z) (det v z - hi)
    have h2 := le_max_right (lo - det v z) (det v z - hi)
    exact hexpand n z (by omega) (by omega)
  refine ⟨fun F => sweep_of_points (fun z _ => hpoint z), ?_⟩
  intro x hx y hy hagree
  funext z
  obtain ⟨steps, hs, hF⟩ := hpoint z
  exact generating_one_point_and_finite_sweep ξ x y G hG hx hy U steps hs hagree
    z (hF (Finset.mem_singleton_self z))


end
end ConvexNivat.Colle
