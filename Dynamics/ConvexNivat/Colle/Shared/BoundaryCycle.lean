import ConvexNivat.Colle.Shared.Definitions
import ConvexNivat.Geometry.Triangulation.HullSeed
import ConvexNivat.Geometry.Triangulation.FanOrder
import ConvexNivat.Geometry.Triangulation.FanSupport
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Between

import ConvexNivat.Colle.Shared.RowCoordinates

namespace ConvexNivat.Colle
noncomputable section
open PolygonTriangulation

/-- Every nonzero lattice displacement has a positive primitive factor. -/
private theorem displacement_primitive_factor (d : Lattice) (hd : d ≠ 0) :
    ∃ n : ℕ, ∃ v : Lattice, 0 < n ∧ Primitive v ∧ d = (n : ℤ) • v := by
  have hg : 0 < Int.gcd d.1 d.2 := by
    by_contra! h
    have he : Int.gcd d.1 d.2 = 0 := Nat.eq_zero_of_le_zero h
    have hz := Int.gcd_eq_zero_iff.mp he
    exact hd (Prod.ext hz.1 hz.2)
  obtain ⟨a,b,hcop,ha,hb⟩ := Int.exists_gcd_one hg
  refine ⟨Int.gcd d.1 d.2, (a,b), hg, hcop, ?_⟩
  apply Prod.ext <;> change _ = (Int.gcd d.1 d.2 : ℤ) * _
  · simpa [mul_comm] using ha
  · simpa [mul_comm] using hb

/-- Irredundant generators are precisely the actual real extreme points. -/
private theorem irredundant_extremePoints (Q : Finset Lattice) (hirr : Irredundant Q) :
    (windowHull Q).extremePoints ℝ = embed '' (Q : Set Lattice) := by
  classical
  apply Set.Subset.antisymm extremePoints_convexHull_subset
  rintro _ ⟨q,hq,rfl⟩
  by_contra he
  have hsub : (windowHull Q).extremePoints ℝ ⊆ embed '' (Q.erase q : Set Lattice) := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := extremePoints_convexHull_subset hx
    refine ⟨r,Finset.mem_erase.mpr ⟨?_,hr⟩,rfl⟩
    intro h
    subst r
    exact he hx
  have hclosed : IsClosed (windowHull (Q.erase q)) := (windowHull_compact _).isClosed
  have hh := closure_minimal (convexHull_mono hsub) hclosed
  rw [closure_convexHull_extremePoints (windowHull_compact Q) (windowHull_convex Q)] at hh
  exact hirr q hq (hh (window_mem_hull Q hq))


private theorem det_zero_smul (u v : RealPlane) (hu : u ≠ 0)
    (h : realDet u v = 0) : ∃ t : ℝ, v = t • u := by
  by_cases h1 : u.1 = 0
  · have h2 : u.2 ≠ 0 := by
      intro h2
      exact hu (Prod.ext h1 h2)
    refine ⟨v.2 / u.2, Prod.ext ?_ ?_⟩
    · change v.1 = v.2 / u.2 * u.1
      rw [h1, mul_zero]
      dsimp [realDet] at h
      rw [h1, zero_mul, zero_sub] at h
      exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left h2
    · exact (div_mul_cancel₀ _ h2).symm
  · refine ⟨v.1 / u.1, Prod.ext (div_mul_cancel₀ _ h1).symm ?_⟩
    change v.2 = v.1 / u.1 * u.2
    field_simp
    dsimp [realDet] at h
    nlinarith

/-- No three different irredundant planar generators lie on one line. -/
private theorem irredundant_three_det_ne_zero (Q : Finset Lattice) (hirr : Irredundant Q)
    (a b c : Lattice) (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    det (b - a) (c - a) ≠ 0 := by
  intro hz
  have hreal : realDet (embed b - embed a) (embed c - embed a) = 0 := by
    rw [← embed_sub, ← embed_sub,
      real_determinant_and_embedding_algebra.2.2.2.2.2.2.1, hz]
    simp
  have hne : embed b - embed a ≠ 0 := sub_ne_zero.mpr (fun h => hab (embed_injective h).symm)
  obtain ⟨t,ht⟩ := det_zero_smul _ _ hne hreal
  have hcol : Collinear ℝ ({embed a, embed b, embed c} : Set RealPlane) := by
    apply (collinear_iff_of_mem (Set.mem_insert _ _)).mpr
    refine ⟨embed b - embed a, ?_⟩
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨t, by change embed c = t • (embed b - embed a) + embed a; rw [← ht]; abel⟩
  have forbid : ∀ r s t : Lattice, r ∈ Q → s ∈ Q → t ∈ Q →
      r ≠ s → r ≠ t → embed r ∉ segment ℝ (embed s) (embed t) := by
    intro r s t hr hs ht hrs hrt hseg
    exact hirr r hr ((windowHull_convex (Q.erase r)).segment_subset
      (window_mem_hull _ (Finset.mem_erase.mpr ⟨hrs.symm,hs⟩))
      (window_mem_hull _ (Finset.mem_erase.mpr ⟨hrt.symm,ht⟩)) hseg)
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact forbid b a c hb ha hc hab.symm hbc h.mem_segment
  · exact forbid c b a hc hb ha hbc.symm hca h.mem_segment
  · exact forbid a c b ha hc hb hca.symm hab h.mem_segment


private def radialVertex {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (c : RadialChain Q p N) : Fin (c.length + 3) → Lattice :=
  Fin.cases p c.point

private theorem radialVertex_zero {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (c : RadialChain Q p N) : radialVertex c 0 = p := rfl

private theorem radialVertex_succ {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (c : RadialChain Q p N) (i : Fin (c.length + 2)) :
    radialVertex c i.succ = c.point i := rfl

private theorem chain_mem {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (c : RadialChain Q p N) (i : Fin (c.length + 2)) : c.point i ∈ Q.erase p := by
  have h : c.point i ∈ Set.range c.point := ⟨i,rfl⟩
  rwa [c.range_eq] at h

private theorem radialVertex_injective {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (c : RadialChain Q p N) : Function.Injective (radialVertex c) := by
  intro i j h
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j => exact False.elim ((Finset.mem_erase.mp (chain_mem c j)).1 h.symm)
  | succ i =>
    induction j using Fin.cases with
    | zero => exact False.elim ((Finset.mem_erase.mp (chain_mem c i)).1 h)
    | succ j => exact congrArg Fin.succ (c.injective h)

private theorem radialVertex_range {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (hp : p ∈ Q) (c : RadialChain Q p N) : Set.range (radialVertex c) = (Q : Set Lattice) := by
  ext q
  constructor
  · rintro ⟨i,rfl⟩
    induction i using Fin.cases with
    | zero => exact hp
    | succ i => exact (Finset.mem_erase.mp (chain_mem c i)).2
  · intro hq
    by_cases h : q = p
    · exact ⟨0,h.symm⟩
    · have hq' : q ∈ Set.range c.point := by
        rw [c.range_eq]
        exact Finset.mem_erase.mpr ⟨h,hq⟩
      obtain ⟨i,rfl⟩ := hq'
      exact ⟨i.succ,rfl⟩

private theorem det_affine_nonneg_convex (u a : RealPlane) :
    Convex ℝ {x | 0 ≤ realDet u (x-a)} := by
  intro x hx y hy s t hs ht hst
  have he : realDet u (s • x+t • y-a) =
      s * realDet u (x-a) + t * realDet u (y-a) := by
    dsimp [realDet]
    nlinarith [congrArg (fun z : ℝ => z * u.1 * a.2) hst,
      congrArg (fun z : ℝ => z * u.2 * a.1) hst]
  change 0 ≤ realDet u (s • x+t • y-a)
  rw [he]
  exact add_nonneg (mul_nonneg hs hx) (mul_nonneg ht hy)

private theorem radial_first_support {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (ha : Anchor Q p N) (c : RadialChain Q p N) (x : RealPlane)
    (hx : x ∈ windowHull Q) :
    0 ≤ realDet (embed (c.point 0)-embed p) (x-embed p) := by
  apply convexHull_min (t := {x | 0 ≤ realDet (embed (c.point 0)-embed p) (x-embed p)})
    ?_ (det_affine_nonneg_convex _ _) hx
  rintro _ ⟨q,hq,rfl⟩
  by_cases hqp : q=p
  · simp [hqp,realDet,mul_comm]
  · have hqr : q ∈ Set.range c.point := by
      rw [c.range_eq]
      exact Finset.mem_erase.mpr ⟨hqp,hq⟩
    obtain ⟨j,rfl⟩ := hqr
    by_cases hj : j=0
    · simp [hj,realDet,mul_comm]
    · have hd := c.determinants 0 j (Fin.pos_iff_ne_zero.mpr hj)
      have he : realDet (embed (c.point 0)-embed p) (embed (c.point j)-embed p) =
          (det (c.point 0-p) (c.point j-p) : ℝ) := by simp [realDet,embed,det]
      change 0 ≤ realDet (embed (c.point 0)-embed p) (embed (c.point j)-embed p)
      rw [he]
      exact_mod_cast hd.le

private theorem radial_last_support {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (ha : Anchor Q p N) (c : RadialChain Q p N) (x : RealPlane)
    (hx : x ∈ windowHull Q) :
    0 ≤ realDet (embed p-embed (c.point (Fin.last (c.length+1))))
      (x-embed (c.point (Fin.last (c.length+1)))) := by
  apply convexHull_min
    (t := {x | 0 ≤ realDet (embed p-embed (c.point (Fin.last (c.length+1))))
      (x-embed (c.point (Fin.last (c.length+1))))})
    ?_ (det_affine_nonneg_convex _ _) hx
  rintro _ ⟨q,hq,rfl⟩
  by_cases hqp : q=p
  · simp [hqp,realDet,mul_comm]
  · have hqr : q ∈ Set.range c.point := by
      rw [c.range_eq]
      exact Finset.mem_erase.mpr ⟨hqp,hq⟩
    obtain ⟨j,rfl⟩ := hqr
    by_cases hj : j=Fin.last (c.length+1)
    · simp [hj,realDet,mul_comm]
    · have hd := c.determinants j (Fin.last (c.length+1)) (lt_of_le_of_ne (Fin.le_last j) hj)
      have he : realDet (embed p-embed (c.point (Fin.last (c.length+1))))
          (embed (c.point j)-embed (c.point (Fin.last (c.length+1)))) =
          (det (c.point j-p) (c.point (Fin.last (c.length+1))-p) : ℝ) := by
        simp [realDet,embed,det]; ring
      change 0 ≤ realDet (embed p-embed (c.point (Fin.last (c.length+1))))
          (embed (c.point j)-embed (c.point (Fin.last (c.length+1))))
      rw [he]
      exact_mod_cast hd.le

private theorem radial_support {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (hirr : Irredundant Q) (ha : Anchor Q p N) (c : RadialChain Q p N)
    (i : Fin (c.length+3)) (x : RealPlane) (hx : x ∈ windowHull Q) :
    0 ≤ realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
      (x-embed (radialVertex c i)) := by
  induction i using Fin.cases with
  | zero =>
    have hidx : (0 : Fin (c.length+3))+1 = (0 : Fin (c.length+2)).succ := by ext; simp
    rw [hidx, radialVertex_succ,radialVertex_zero]
    exact radial_first_support ha c x hx
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      rw [show (Fin.last (c.length+1)).succ = Fin.last (c.length+2) from rfl,
        Fin.last_add_one,radialVertex_zero]
      change 0 ≤ realDet (embed p-embed (c.point (Fin.last (c.length+1))))
        (x-embed (c.point (Fin.last (c.length+1))))
      exact radial_last_support ha c x hx
    | cast i =>
      have hidx : i.castSucc.succ + 1 = i.succ.succ := by
        apply Fin.ext
        rw [Fin.val_add_one]
        have hne : i.castSucc.succ ≠ Fin.last (c.length+2) := by
          intro h
          have hh := congrArg Fin.val h
          simp at hh
          omega
        simp [hne]
      rw [hidx,radialVertex_succ,radialVertex_succ]
      have h := consecutive_radial_edge_supports_hull Q hirr p N ha c i x hx
      simpa [radialVertex,embed_sub,sub_sub_sub_cancel_right,sub_sub] using h


private theorem radialVertex_mem {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (ha : Anchor Q p N) (c : RadialChain Q p N) (i : Fin (c.length+3)) :
    radialVertex c i ∈ Q := by
  have h : radialVertex c i ∈ Set.range (radialVertex c) := ⟨i,rfl⟩
  rwa [radialVertex_range ha.1 c] at h

private theorem radial_next_ne {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (c : RadialChain Q p N) (i : Fin (c.length+3)) : i+1 ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  rw [Fin.val_add_one] at hv
  split_ifs at hv with h
  · subst i
    simp at hv
  · omega

private theorem radial_strict_support {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (hirr : Irredundant Q) (ha : Anchor Q p N) (c : RadialChain Q p N)
    (i : Fin (c.length+3)) (q : Lattice) (hq : q ∈ Q)
    (hqi : q ≠ radialVertex c i) (hqnext : q ≠ radialVertex c (i+1)) :
    0 < realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
      (embed q-embed (radialVertex c i)) := by
  have hn := radial_support hirr ha c i (embed q) (window_mem_hull Q hq)
  have hne := irredundant_three_det_ne_zero Q hirr
    (radialVertex c i) (radialVertex c (i+1)) q
    (radialVertex_mem ha c i) (radialVertex_mem ha c (i+1)) hq
    (fun h => radial_next_ne c i (radialVertex_injective c h.symm)) hqnext.symm hqi
  have he : realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
      (embed q-embed (radialVertex c i)) =
      (det (radialVertex c (i+1)-radialVertex c i) (q-radialVertex c i) : ℝ) := by
    simp [realDet,embed,det]
  rw [he] at hn ⊢
  exact lt_of_le_of_ne hn (Ne.symm (by exact_mod_cast hne))

private theorem det_face_convex (u a b : RealPlane) :
    Convex ℝ {x | 0 ≤ realDet u (x-a) ∧
      (realDet u (x-a)=0 → x ∈ segment ℝ a b)} := by
  apply convex_iff_forall_pos.mpr
  intro x hx y hy s t hs ht hst
  have he : realDet u (s • x+t • y-a) =
      s * realDet u (x-a) + t * realDet u (y-a) := by
    dsimp [realDet]
    nlinarith [congrArg (fun z : ℝ => z * u.1 * a.2) hst,
      congrArg (fun z : ℝ => z * u.2 * a.1) hst]
  refine ⟨?_,?_⟩
  · change 0 ≤ realDet u (s • x+t • y-a)
    rw [he]
    exact add_nonneg (mul_nonneg hs.le hx.1) (mul_nonneg ht.le hy.1)
  · intro hz
    have hz' : s * realDet u (x-a) + t * realDet u (y-a)=0 := he ▸ hz
    have hh := (add_eq_zero_iff_of_nonneg (mul_nonneg hs.le hx.1)
      (mul_nonneg ht.le hy.1)).mp hz'
    exact (convex_segment (𝕜 := ℝ) a b) (hx.2 ((mul_eq_zero.mp hh.1).resolve_left hs.ne'))
      (hy.2 ((mul_eq_zero.mp hh.2).resolve_left ht.ne')) hs.le ht.le hst

private theorem radial_exact_face {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (hirr : Irredundant Q) (ha : Anchor Q p N) (c : RadialChain Q p N)
    (i : Fin (c.length+3)) (x : RealPlane) (hx : x ∈ windowHull Q) :
    realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
      (x-embed (radialVertex c i)) = 0 ↔
    x ∈ segment ℝ (embed (radialVertex c i)) (embed (radialVertex c (i+1))) := by
  constructor
  · have hh : ∀ x ∈ windowHull Q,
        0 ≤ realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
          (x-embed (radialVertex c i)) ∧
        (realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
          (x-embed (radialVertex c i)) = 0 →
        x ∈ segment ℝ (embed (radialVertex c i)) (embed (radialVertex c (i+1)))) := by
      apply convexHull_min ?_ (det_face_convex _ _ _)
      rintro _ ⟨q,hq,rfl⟩
      refine ⟨radial_support hirr ha c i (embed q) (window_mem_hull Q hq),?_⟩
      intro he
      by_cases hqi : q=radialVertex c i
      · simpa [hqi] using left_mem_segment ℝ (embed (radialVertex c i))
          (embed (radialVertex c (i+1)))
      by_cases hqnext : q=radialVertex c (i+1)
      · simpa [hqnext] using right_mem_segment ℝ (embed (radialVertex c i))
          (embed (radialVertex c (i+1)))
      exact False.elim ((radial_strict_support hirr ha c i q hq hqi hqnext).ne' he)
    exact (hh x hx).2
  · rintro ⟨s,t,hs,ht,hst,rfl⟩
    dsimp [realDet]
    nlinarith [congrArg (fun z : ℝ => z * (embed (radialVertex c (i+1))).1 *
        (embed (radialVertex c i)).2) hst,
      congrArg (fun z : ℝ => z * (embed (radialVertex c (i+1))).2 *
        (embed (radialVertex c i)).1) hst]


private theorem det_reconstruct (u v y : RealPlane) (hd : realDet u v ≠ 0) :
    y = (realDet y v / realDet u v) • u + (realDet u y / realDet u v) • v := by
  apply Prod.ext
  all_goals dsimp [realDet] at hd ⊢
  all_goals field_simp (disch := ring_nf at hd ⊢; assumption)
  all_goals ring

private theorem closed_slope_bracket (n : ℕ) (f : Fin (n+2) → ℝ) (r : ℝ)
    (hlo : f 0 ≤ r) (hhi : r ≤ f (Fin.last (n+1))) :
    ∃ i : Fin (n+1), f i.castSucc ≤ r ∧ r ≤ f i.succ := by
  induction n with
  | zero => exact ⟨0,hlo,hhi⟩
  | succ n ih =>
    by_cases h : r ≤ f ⟨1,by omega⟩
    · exact ⟨0,hlo,h⟩
    · obtain ⟨i,hi⟩ := ih (fun j => f j.succ) (le_of_lt (lt_of_not_ge h)) hhi
      exact ⟨i.succ,hi⟩

private theorem radial_halfplanes_hull {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (hirr : Irredundant Q) (ha : Anchor Q p N) (c : RadialChain Q p N)
    (x : RealPlane)
    (hx : ∀ i : Fin (c.length+3),
      0 ≤ realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
        (x-embed (radialVertex c i))) : x ∈ windowHull Q := by
  by_cases hxp : x=embed p
  · rw [hxp]
    exact window_mem_hull Q ha.1
  let u := embed (c.point 0-p)
  let v := embed (c.point (Fin.last (c.length+1))-p)
  let y := x-embed p
  have hfirst : 0 ≤ realDet u y := by
    have h := hx 0
    have hidx : (0 : Fin (c.length+3))+1=(0 : Fin (c.length+2)).succ := by ext; simp
    rw [hidx,radialVertex_succ,radialVertex_zero] at h
    simpa [u,y,embed_sub] using h
  have hlast : 0 ≤ realDet y v := by
    have h := hx (Fin.last (c.length+2))
    rw [Fin.last_add_one,radialVertex_zero] at h
    change 0 ≤ realDet (embed p-embed (c.point (Fin.last (c.length+1))))
      (x-embed (c.point (Fin.last (c.length+1)))) at h
    have he : realDet (embed p-embed (c.point (Fin.last (c.length+1))))
        (x-embed (c.point (Fin.last (c.length+1)))) = realDet y v := by
      dsimp [realDet,y,v,embed]
      push_cast
      ring
    rwa [he] at h
  have hd : 0 < realDet u v := by
    have h := c.determinants 0 (Fin.last (c.length+1)) (by change (0 : ℕ) < c.length+1; omega)
    have he : realDet u v =
      (det (c.point 0-p) (c.point (Fin.last (c.length+1))-p) : ℝ) := by
      simp [u,v,realDet,embed,det]
    rw [he]
    exact_mod_cast h
  have hu : 0 < ell N u := ha.2 _ (chain_mem c 0)
  have hv : 0 < ell N v := ha.2 _ (chain_mem c (Fin.last (c.length+1)))
  have hy : 0 < ell N y := by
    have hrecon := det_reconstruct u v y hd.ne'
    have he : ell N y = (realDet y v / realDet u v) * ell N u +
        (realDet u y / realDet u v) * ell N v := by
      conv_lhs => rw [hrecon]
      simp [ell]
      ring
    have ha0 := div_nonneg hlast hd.le
    have hb0 := div_nonneg hfirst hd.le
    have hnon : 0 ≤ ell N y := by rw [he]; positivity
    refine lt_of_le_of_ne hnon ?_
    intro hz
    have hsum : realDet y v / realDet u v * ell N u +
        realDet u y / realDet u v * ell N v = 0 := by rw [← he,hz]
    have ha1 : realDet y v / realDet u v = 0 := by nlinarith [mul_nonneg hb0 hv.le]
    have hb1 : realDet u y / realDet u v = 0 := by nlinarith [mul_nonneg ha0 hu.le]
    rw [ha1,hb1,zero_smul,zero_smul,add_zero] at hrecon
    exact hxp (sub_eq_zero.mp hrecon)
  have detell : ∀ a b : RealPlane, realDet a b =
      ell N a * kappa b-kappa a * ell N b := by
    intro a b
    simp [realDet,ell,kappa]
    ring
  have hlo : slope N u ≤ slope N y := by
    apply (div_le_div_iff₀ hu hy).mpr
    rw [detell] at hfirst
    linarith
  have hhi : slope N y ≤ slope N v := by
    apply (div_le_div_iff₀ hy hv).mpr
    rw [detell] at hlast
    linarith
  obtain ⟨i,hi,hj⟩ := closed_slope_bracket c.length
    (fun j => slope N (embed (c.point j-p))) (slope N y) hlo hhi
  have hiell := ha.2 _ (chain_mem c i.castSucc)
  have hjell := ha.2 _ (chain_mem c i.succ)
  have hid : 0 < realDet (embed (c.point i.castSucc-p)) (embed (c.point i.succ-p)) := by
    have h := c.determinants i.castSucc i.succ Fin.castSucc_lt_succ
    have he : realDet (embed (c.point i.castSucc-p)) (embed (c.point i.succ-p)) =
        (det (c.point i.castSucc-p) (c.point i.succ-p) : ℝ) := by
      simp [realDet,embed,det]
    rw [he]
    exact_mod_cast h
  have hdiy : 0 ≤ realDet (embed (c.point i.castSucc-p)) y := by
    have h := (div_le_div_iff₀ hiell hy).mp hi
    rw [detell]
    linarith
  have hdyj : 0 ≤ realDet y (embed (c.point i.succ-p)) := by
    have h := (div_le_div_iff₀ hy hjell).mp hj
    rw [detell]
    linarith
  have hsupp := hx i.castSucc.succ
  have hidx : i.castSucc.succ + 1 = i.succ.succ := by
    apply Fin.ext
    rw [Fin.val_add_one]
    have hne : i.castSucc.succ ≠ Fin.last (c.length+2) := by
      intro h
      have hh := congrArg Fin.val h
      simp at hh
      omega
    simp [hne]
  rw [hidx,radialVertex_succ,radialVertex_succ] at hsupp
  have hsum : realDet y (embed (c.point i.succ-p)) /
        realDet (embed (c.point i.castSucc-p)) (embed (c.point i.succ-p)) +
      realDet (embed (c.point i.castSucc-p)) y /
        realDet (embed (c.point i.castSucc-p)) (embed (c.point i.succ-p)) ≤ 1 := by
    rw [← add_div,div_le_one hid]
    have he : realDet (embed (c.point i.succ)-embed (c.point i.castSucc))
        (x-embed (c.point i.castSucc)) =
      realDet (embed (c.point i.castSucc-p)) (embed (c.point i.succ-p)) -
        realDet y (embed (c.point i.succ-p)) - realDet (embed (c.point i.castSucc-p)) y := by
      simp [realDet,embed,y]
      ring
    rw [he] at hsupp
    linarith
  have hnd : delta (fanCell c i) ≠ 0 :=
    ne_of_gt (c.determinants i.castSucc i.succ Fin.castSucc_lt_succ)
  have htriangle : x ∈ (fanCell c i).carrier := by
    apply (nondegenerate_triangle_barycentric_unique (fanCell c i) hnd x).2.2.1.mpr
    intro j
    fin_cases j
    · change 0 ≤ 1-realDet y (embed (c.point i.succ-p)) /
        realDet (embed (c.point i.castSucc-p)) (embed (c.point i.succ-p)) -
        realDet (embed (c.point i.castSucc-p)) y /
        realDet (embed (c.point i.castSucc-p)) (embed (c.point i.succ-p))
      linarith
    · exact div_nonneg hdyj hid.le
    · exact div_nonneg hdiy hid.le
  apply convexHull_mono (Set.image_mono ?_) htriangle
  intro q hq
  simp only [fanCell,LatticeTriangle.vertices,Finset.mem_coe,Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact ha.1
  · exact (Finset.mem_erase.mp (chain_mem c i.castSucc)).2
  · exact (Finset.mem_erase.mp (chain_mem c i.succ)).2


private theorem supporting_zero_not_interior (S : Set RealPlane) (u a x : RealPlane)
    (hu : u ≠ 0) (hsupp : ∀ y ∈ S, 0 ≤ realDet u (y-a))
    (hx : realDet u (x-a)=0) : x ∉ interior S := by
  let f : RealPlane →L[ℝ] ℝ :=
    u.1 • ContinuousLinearMap.snd ℝ ℝ ℝ - u.2 • ContinuousLinearMap.fst ℝ ℝ ℝ
  have hf : ∀ y, f y = realDet u y := by intro y; rfl
  have hsurj : Function.Surjective f := by
    intro t
    by_cases h1 : u.1=0
    · have h2 : u.2 ≠ 0 := by
        intro h2
        exact hu (Prod.ext h1 h2)
      refine ⟨(-t/u.2,0),?_⟩
      rw [hf]
      simp [realDet,h1,h2,mul_div_cancel₀]
    · refine ⟨(0,t/u.1),?_⟩
      rw [hf]
      simp [realDet,h1,mul_div_cancel₀]
  have ho : IsOpenMap (fun y => realDet u (y-a)) := by
    exact (f.isOpenMap hsurj).comp (Homeomorph.subRight a).isOpenMap
  intro hxi
  have hhalf : S ⊆ (fun y => realDet u (y-a)) ⁻¹' Set.Ici 0 := hsupp
  have hh := ho.interior_preimage_subset_preimage_interior (interior_mono hhalf hxi)
  simpa [interior_Ici,hx] using hh

private theorem radial_frontier {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (hirr : Irredundant Q) (ha : Anchor Q p N) (c : RadialChain Q p N) :
    frontier (windowHull Q) = {x | ∃ i : Fin (c.length+3),
      x ∈ segment ℝ (embed (radialVertex c i)) (embed (radialVertex c (i+1)))} := by
  rw [(windowHull_compact Q).isClosed.frontier_eq]
  ext x
  constructor
  · rintro ⟨hx,hni⟩
    have hzero : ∃ i : Fin (c.length+3),
        realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
          (x-embed (radialVertex c i))=0 := by
      by_contra! hno
      have hpos : ∀ i : Fin (c.length+3),
          0 < realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
            (x-embed (radialVertex c i)) := fun i =>
        lt_of_le_of_ne (radial_support hirr ha c i x hx) (Ne.symm (hno i))
      let U : Set RealPlane := ⋂ i : Fin (c.length+3),
        {y | 0 < realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
          (y-embed (radialVertex c i))}
      have hU : IsOpen U := by
        apply isOpen_iInter_of_finite
        intro i
        apply isOpen_lt continuous_const
        dsimp [realDet]
        fun_prop
      have hsub : U ⊆ windowHull Q := by
        intro y hy
        apply radial_halfplanes_hull hirr ha c y
        intro i
        exact (Set.mem_iInter.mp hy i).le
      exact hni (interior_maximal hsub hU (Set.mem_iInter.mpr hpos))
    obtain ⟨i,hi⟩ := hzero
    exact ⟨i,(radial_exact_face hirr ha c i x hx).mp hi⟩
  · rintro ⟨i,hi⟩
    have hx : x ∈ windowHull Q := (windowHull_convex Q).segment_subset
      (window_mem_hull Q (radialVertex_mem ha c i))
      (window_mem_hull Q (radialVertex_mem ha c (i+1))) hi
    refine ⟨hx,?_⟩
    apply supporting_zero_not_interior (windowHull Q)
      (embed (radialVertex c (i+1))-embed (radialVertex c i)) (embed (radialVertex c i)) x
    · intro he
      exact radial_next_ne c i (radialVertex_injective c (embed_injective (sub_eq_zero.mp he)))
    · exact radial_support hirr ha c i
    · exact (radial_exact_face hirr ha c i x hx).mpr hi


private theorem scaled_edge_det (a b d : Lattice) (l : ℕ)
    (he : b-a=(l : ℤ) • d) (x : RealPlane) :
    realDet (embed b-embed a) (x-embed a) =
      (l : ℝ) * realDet (embed d) (x-embed a) := by
  rw [← embed_sub,he]
  simp [realDet,embed]
  ring

private theorem support_row_iff_zero (B : Finset Lattice) (a d : Lattice)
    (ha : a ∈ B) (hs : ∀ x ∈ windowHull B, 0 ≤ realDet (embed d) (x-embed a))
    (z : Lattice) : z ∈ supportRow B d ↔
      z ∈ B ∧ realDet (embed d) (embed z-embed a)=0 := by
  simp only [supportRow,supportFace,Finset.mem_filter,normal_height]
  constructor
  · rintro ⟨hz,hmin⟩
    refine ⟨hz,?_⟩
    have hl := hmin a ha
    have hn := hs (embed z) (window_mem_hull B hz)
    have he : realDet (embed d) (embed z-embed a) = (det d z : ℝ)-(det d a : ℝ) := by
      simp [realDet,embed,det]
      ring
    rw [he] at hn ⊢
    linarith
  · rintro ⟨hz,hz0⟩
    refine ⟨hz,?_⟩
    intro q hq
    have hn := hs (embed q) (window_mem_hull B hq)
    have he : ∀ z : Lattice, realDet (embed d) (embed z-embed a) =
        (det d z : ℝ)-(det d a : ℝ) := by
      intro z
      simp [realDet,embed,det]
      ring
    rw [he] at hn hz0
    linarith

private theorem radial_two_steps_ne {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (c : RadialChain Q p N) (i : Fin (c.length+3)) : i+1+1 ≠ i := by
  intro h
  have hh : (1 : Fin (c.length+3))+1=0 := by
    exact add_left_cancel (show i+(1+1)=i+0 by simpa [add_assoc] using h)
  have hv := congrArg Fin.val hh
  simp [Fin.val_add,Fin.val_one, Nat.mod_eq_of_lt (show 2 < c.length+3 by omega)] at hv

private theorem radial_normalized_turn {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (hirr : Irredundant Q) (ha : Anchor Q p N) (c : RadialChain Q p N)
    (l : Fin (c.length+3) → ℕ) (d : Fin (c.length+3) → Lattice)
    (hl : ∀ i, 0 < l i)
    (he : ∀ i, radialVertex c (i+1)-radialVertex c i=(l i : ℤ) • d i)
    (i : Fin (c.length+3)) : 0 < det (d i) (d (i+1)) := by
  have hh := radial_strict_support hirr ha c i (radialVertex c (i+1+1))
    (radialVertex_mem ha c (i+1+1))
    (fun h => radial_two_steps_ne c i (radialVertex_injective c h))
    (fun h => radial_next_ne c (i+1) (radialVertex_injective c h))
  have hid : realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
        (embed (radialVertex c (i+1+1))-embed (radialVertex c i)) =
      ((det (radialVertex c (i+1)-radialVertex c i)
        (radialVertex c (i+1+1)-radialVertex c (i+1)) : ℤ) : ℝ) := by
    simp [realDet,embed,det]
    ring
  rw [hid] at hh
  have hh' : 0 < det (radialVertex c (i+1)-radialVertex c i)
      (radialVertex c (i+1+1)-radialVertex c (i+1)) := by exact_mod_cast hh
  rw [he i,he (i+1)] at hh'
  have hf : det ((l i : ℤ) • d i) ((l (i+1) : ℤ) • d (i+1)) =
      (l i : ℤ) * (l (i+1) : ℤ) * det (d i) (d (i+1)) := by simp [det]; ring
  rw [hf] at hh'
  exact (mul_pos_iff.mp hh').resolve_right
    (fun h => (not_lt_of_ge (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))) h.1) |>.2


private theorem radial_normalized_injective {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (hirr : Irredundant Q) (ha : Anchor Q p N) (c : RadialChain Q p N)
    (l : Fin (c.length+3) → ℕ) (d : Fin (c.length+3) → Lattice)
    (hl : ∀ i, 0 < l i)
    (he : ∀ i, radialVertex c (i+1)-radialVertex c i=(l i : ℤ) • d i) :
    Function.Injective d := by
  intro i j hij
  have hs : ∀ i x, x ∈ windowHull Q →
      0 ≤ realDet (embed (d i)) (x-embed (radialVertex c i)) := by
    intro i x hx
    have h := radial_support hirr ha c i x hx
    rw [scaled_edge_det _ _ _ _ (he i)] at h
    exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hl i)
  have h1 := hs i (embed (radialVertex c j))
    (window_mem_hull Q (radialVertex_mem ha c j))
  have h2 := hs j (embed (radialVertex c i))
    (window_mem_hull Q (radialVertex_mem ha c i))
  rw [← hij] at h2
  have hd0 : realDet (embed (d i))
      (embed (radialVertex c j)-embed (radialVertex c i))=0 := by
    have hneg : realDet (embed (d i))
        (embed (radialVertex c i)-embed (radialVertex c j)) =
      -realDet (embed (d i)) (embed (radialVertex c j)-embed (radialVertex c i)) := by
      simp [realDet]; ring
    rw [hneg] at h2
    linarith
  by_cases hji : j=i
  · exact hji.symm
  by_cases hjnext : j=i+1
  · subst j
    have ht := radial_normalized_turn hirr ha c l d hl he i
    rw [hij] at ht
    simp [det,mul_comm] at ht
  · have ht := radial_strict_support hirr ha c i (radialVertex c j)
      (radialVertex_mem ha c j)
      (fun h => hji (radialVertex_injective c h))
      (fun h => hjnext (radialVertex_injective c h))
    rw [scaled_edge_det _ _ _ _ (he i),hd0,mul_zero] at ht
    exact False.elim (lt_irrefl _ ht)

private def cycleIndex (n : ℕ) (j : ℤ) : Fin (n+3) :=
  ⟨(j % ((n+3 : ℕ) : ℤ)).toNat,
    (Int.toNat_lt (Int.emod_nonneg _ (by omega))).mpr
      (Int.emod_lt_of_pos _ (by omega))⟩

private theorem cycleIndex_periodic (n : ℕ) (j : ℤ) :
    cycleIndex n (j+(n+3 : ℕ))=cycleIndex n j := by
  apply Fin.ext
  simp [cycleIndex,Int.add_emod_right]

private theorem cycleIndex_nat (n : ℕ) (i : Fin (n+3)) : cycleIndex n (i.val : ℤ)=i := by
  apply Fin.ext
  simp only [cycleIndex]
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)]
  simp

private theorem cycleIndex_next (n : ℕ) (j : ℤ) :
    cycleIndex n (j+1)=cycleIndex n j+1 := by
  apply Fin.ext
  change ((j+1) % ((n+3 : ℕ) : ℤ)).toNat =
    ((j % ((n+3 : ℕ) : ℤ)).toNat+1)%(n+3)
  rw [Int.add_emod]
  have h1 : (1 : ℤ) % (n+3 : ℕ)=1 := Int.emod_eq_of_lt (by omega) (by omega)
  rw [h1]
  have h0 : 0 ≤ j % ((n+3 : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
  rw [Int.toNat_emod (by omega) (by omega),Int.toNat_add h0 (by omega)]
  rw [Int.toNat_natCast]
  rfl


private theorem primitive_eq_of_positive_parallel (u v : Lattice)
    (hu : Primitive u) (hv : Primitive v) (hdet : det u v=0)
    (x : RealPlane) (hux : 0 ≤ realDet (embed u) x)
    (hvx : 0 < realDet (embed v) x) : v=u := by
  have hz : det u 0=det u v := by simp [det] at hdet ⊢; exact hdet.symm
  obtain ⟨k,hk⟩ := (primitive_row_coordinates u hu).2.1 0 v |>.mp hz
  simp only [zero_add] at hk
  have hg : k.natAbs=1 := by
    have h := hv
    rw [hk] at h
    change Int.gcd (k*u.1) (k*u.2)=1 at h
    rw [Int.gcd_mul_left,show Int.gcd u.1 u.2=1 from hu,mul_one] at h
    exact h
  have he : realDet (embed v) x=(k : ℝ)*realDet (embed u) x := by
    rw [hk]
    simp [realDet,embed]
    ring
  have hkpos : 0 < k := by
    rw [he] at hvx
    have hk' : 0 < (k : ℝ) := by nlinarith
    exact_mod_cast hk'
  have hkone : k=1 := by
    have h : (k.natAbs : ℤ)=k := by omega
    rw [hg] at h
    exact h.symm
  simpa [hkone] using hk

private theorem edge_direction_real_support (B : Finset Lattice) (u a : Lattice)
    (ha : a ∈ supportRow B u) :
    ∀ x ∈ windowHull B, 0 ≤ realDet (embed u) (x-embed a) := by
  apply convexHull_min ?_ (det_affine_nonneg_convex _ _)
  rintro _ ⟨q,hq,rfl⟩
  have h := (Finset.mem_filter.mp ha).2 q hq
  rw [normal_height,normal_height] at h
  change 0 ≤ realDet (embed u) (embed q-embed a)
  have he : realDet (embed u) (embed q-embed a) = (det u q : ℝ)-(det u a : ℝ) := by
    simp [realDet,embed,det]
    ring
  rw [he]
  linarith

private theorem radial_normalized_covers {Q B : Finset Lattice} {p : Lattice} {N : ℕ}
    (hirr : Irredundant Q) (ha : Anchor Q p N) (c : RadialChain Q p N)
    (hQB : Q ⊆ B) (hHull : windowHull Q=windowHull B)
    (harea : (interior (windowHull B)).Nonempty)
    (l : Fin (c.length+3) → ℕ) (d : Fin (c.length+3) → Lattice)
    (hl : ∀ i, 0 < l i) (hd : ∀ i, Primitive (d i))
    (he : ∀ i, radialVertex c (i+1)-radialVertex c i=(l i : ℤ) • d i) :
    edgeDirections B=Set.range d := by
  classical
  have hs : ∀ i x, x ∈ windowHull B →
      0 ≤ realDet (embed (d i)) (x-embed (radialVertex c i)) := by
    intro i x hx
    have h := radial_support hirr ha c i x (hHull.symm ▸ hx)
    rw [scaled_edge_det _ _ _ _ (he i)] at h
    exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hl i)
  have hv : ∀ i, radialVertex c i ∈ B := fun i => hQB (radialVertex_mem ha c i)
  have hend : ∀ i, radialVertex c (i+1) ∈ supportRow B (d i) := by
    intro i
    apply (support_row_iff_zero B _ _ (hv i) (hs i) _).mpr
    refine ⟨hv (i+1),?_⟩
    have h0 : realDet (embed (radialVertex c (i+1))-embed (radialVertex c i))
        (embed (radialVertex c (i+1))-embed (radialVertex c i))=0 := by simp [realDet,mul_comm]
    rw [scaled_edge_det _ _ _ _ (he i)] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast (hl i).ne')
  ext u
  constructor
  · intro hu
    obtain ⟨a,haB,b,hbB,hab⟩ := Finset.one_lt_card.mp (show 1 < (supportRow B u).card by
      exact hu.2.2)
    have ha' : a ∈ B := (Finset.mem_filter.mp haB).1
    have hb' : b ∈ B := (Finset.mem_filter.mp hbB).1
    have hsupp := edge_direction_real_support B u a haB
    have hbzero := ((support_row_iff_zero B a u ha' hsupp b).mp hbB).2
    let x := midpoint ℝ (embed a) (embed b)
    have hxhull : x ∈ windowHull B := (windowHull_convex B).segment_subset
      (window_mem_hull B ha') (window_mem_hull B hb') (midpoint_mem_segment (embed a) (embed b))
    have hxzero : realDet (embed u) (x-embed a)=0 := by
      dsimp [x]
      rw [midpoint_eq_smul_add]
      norm_num [realDet,smul_eq_mul] at hbzero ⊢
      nlinarith
    have hxfront : x ∈ frontier (windowHull Q) := by
      rw [hHull,(windowHull_compact B).isClosed.frontier_eq]
      exact ⟨hxhull,supporting_zero_not_interior _ _ _ _ (primitive_ne_zero u hu.1 |>.imp
        (fun h => embed_injective (by simpa [embed] using h))) hsupp hxzero⟩
    rw [radial_frontier hirr ha c] at hxfront
    obtain ⟨i,hi⟩ := hxfront
    have hxne : ∀ j, x ≠ embed (radialVertex c j) := by
      intro j heq
      have hqext : embed (radialVertex c j) ∈ (windowHull Q).extremePoints ℝ := by
        rw [irredundant_extremePoints Q hirr]
        exact ⟨radialVertex c j,radialVertex_mem ha c j,rfl⟩
      rw [hHull,← heq] at hqext
      have hh := (mem_extremePoints.mp hqext).2 (embed a) (window_mem_hull B ha')
        (embed b) (window_mem_hull B hb') (midpoint_mem_openSegment (embed a) (embed b))
      exact hab (embed_injective (hh.1.trans hh.2.symm))
    obtain ⟨s,t,hs0,ht0,hst,hxt⟩ := hi
    have hspos : 0 < s := by
      by_contra! hn
      have he0 : s=0 := le_antisymm hn hs0
      have ht1 : t=1 := by linarith
      rw [he0,ht1,zero_smul,one_smul,zero_add] at hxt
      exact hxne (i+1) hxt.symm
    have htpos : 0 < t := by
      by_contra! hn
      have he0 : t=0 := le_antisymm hn ht0
      have hs1 : s=1 := by linarith
      rw [he0,hs1,zero_smul,one_smul,add_zero] at hxt
      exact hxne i hxt.symm
    have hfi := hsupp _ (window_mem_hull B (hv i))
    have hfj := hsupp _ (window_mem_hull B (hv (i+1)))
    have hxlin : realDet (embed u) (x-embed a) =
        s * realDet (embed u) (embed (radialVertex c i)-embed a) +
        t * realDet (embed u) (embed (radialVertex c (i+1))-embed a) := by
      rw [← hxt]
      dsimp [realDet]
      nlinarith [congrArg (fun z : ℝ => z * (embed u).1 * (embed a).2) hst,
        congrArg (fun z : ℝ => z * (embed u).2 * (embed a).1) hst]
    have hzi : realDet (embed u) (embed (radialVertex c i)-embed a)=0 := by
      rw [hxzero] at hxlin
      nlinarith [mul_nonneg ht0 hfj]
    have hzj : realDet (embed u) (embed (radialVertex c (i+1))-embed a)=0 := by
      rw [hxzero] at hxlin
      nlinarith [mul_nonneg hs0 hfi]
    have hzedge : det u (d i)=0 := by
      have hzE : realDet (embed u)
          (embed (radialVertex c (i+1))-embed (radialVertex c i))=0 := by
        dsimp [realDet] at hzi hzj ⊢
        linarith
      rw [← embed_sub,he i] at hzE
      have hid : realDet (embed u) (embed ((l i : ℤ) • d i)) =
          (l i : ℝ)*(det u (d i) : ℝ) := by simp [realDet,embed,det]; ring
      rw [hid] at hzE
      have hd0 : (det u (d i) : ℝ)=0 :=
        (mul_eq_zero.mp hzE).resolve_left (by exact_mod_cast (hl i).ne')
      exact_mod_cast hd0
    obtain ⟨j,hji,hjnext⟩ := Fin.exists_ne_and_ne_of_two_lt i (i+1) (by omega)
    have hstrict := radial_strict_support hirr ha c i (radialVertex c j)
      (radialVertex_mem ha c j)
      (fun h => hji (radialVertex_injective c h))
      (fun h => hjnext (radialVertex_injective c h))
    rw [scaled_edge_det _ _ _ _ (he i)] at hstrict
    have hdpos : 0 < realDet (embed (d i))
        (embed (radialVertex c j)-embed (radialVertex c i)) :=
      (mul_pos_iff.mp hstrict).resolve_right (fun h =>
        (not_lt_of_ge (show (0 : ℝ) ≤ l i by positivity)) h.1) |>.2
    have hunonneg : 0 ≤ realDet (embed u)
        (embed (radialVertex c j)-embed (radialVertex c i)) := by
      have hq := hsupp _ (window_mem_hull B (hv j))
      dsimp [realDet] at hq hzi ⊢
      linarith
    exact ⟨i,primitive_eq_of_positive_parallel u (d i) hu.1 (hd i) hzedge _ hunonneg hdpos⟩
  · rintro ⟨i,rfl⟩
    refine ⟨hd i,harea,?_⟩
    have hinitial : radialVertex c i ∈ supportRow B (d i) := by
      apply (support_row_iff_zero B _ _ (hv i) (hs i) _).mpr
      exact ⟨hv i,by simp [realDet]⟩
    exact Finset.one_lt_card.mpr ⟨radialVertex c i,hinitial,radialVertex c (i+1),hend i,
      fun h => radial_next_ne c i (radialVertex_injective c h.symm)⟩


/-- RC01: existence of the true ordered boundary, with no supplied certificate. -/
theorem finite_window_support_polygon (B : Finset Lattice)
    (hB : LatticeConvex B) (harea : (interior (windowHull B)).Nonempty) :
    Nonempty (WindowBoundary B) := by
  classical
  obtain ⟨Q,hQB,hHull,hQ,hirr,hminimal⟩ := minimal_irredundant_lattice_generators B harea
  have hQarea : (interior (windowHull Q)).Nonempty := hHull.symm ▸ harea
  have hQcard := hull_of_at_most_two_has_empty_interior.2 Q hQarea
  obtain ⟨p,N,ha,hdet,hanchor⟩ := strict_integer_exposed_anchor Q hQ hirr hQarea
  obtain ⟨c⟩ := sorted_irredundant_radial_chain Q hQcard hirr p N ha
  have hfac : ∀ i : Fin (c.length+3), ∃ l : ℕ, ∃ d : Lattice,
      0 < l ∧ Primitive d ∧ radialVertex c (i+1)-radialVertex c i=(l : ℤ) • d := by
    intro i
    apply displacement_primitive_factor
    intro he
    exact radial_next_ne c i (radialVertex_injective c (sub_eq_zero.mp he))
  choose l d hl hd he using hfac
  have hv : ∀ i, radialVertex c i ∈ B := fun i => hQB (radialVertex_mem ha c i)
  have hs : ∀ i x, x ∈ windowHull B →
      0 ≤ realDet (embed (d i)) (x-embed (radialVertex c i)) := by
    intro i x hx
    have h := radial_support hirr ha c i x (hHull.symm ▸ hx)
    rw [scaled_edge_det _ _ _ _ (he i)] at h
    exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hl i)
  have hface : ∀ i z, z ∈ supportRow B (d i) ↔
      embed z ∈ segment ℝ (embed (radialVertex c i)) (embed (radialVertex c (i+1))) := by
    intro i z
    rw [support_row_iff_zero B _ _ (hv i) (hs i)]
    constructor
    · rintro ⟨hz,hz0⟩
      apply (radial_exact_face hirr ha c i _ (hHull.symm ▸ window_mem_hull B hz)).mp
      rw [scaled_edge_det _ _ _ _ (he i),hz0,mul_zero]
    · intro hz
      have hzhull := (windowHull_convex B).segment_subset
        (window_mem_hull B (hv i)) (window_mem_hull B (hv (i+1))) hz
      refine ⟨(hB z).mp hzhull,?_⟩
      have hzero := (radial_exact_face hirr ha c i _ (hHull.symm ▸ hzhull)).mpr hz
      rw [scaled_edge_det _ _ _ _ (he i)] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (by exact_mod_cast (hl i).ne')
  refine ⟨{
    count := c.length+3
    at_least_three := by omega
    vertex := fun j => radialVertex c (cycleIndex c.length j)
    direction := fun j => d (cycleIndex c.length j)
    length := fun j => l (cycleIndex c.length j)
    vertex_periodic := fun j => by rw [cycleIndex_periodic]
    direction_periodic := fun j => by rw [cycleIndex_periodic]
    length_periodic := fun j => by rw [cycleIndex_periodic]
    distinct_vertices := ?_
    distinct_directions := ?_
    extreme_points := ?_
    vertex_mem := fun j => hv (cycleIndex c.length j)
    primitive := fun j => hd (cycleIndex c.length j)
    length_positive := fun j => hl (cycleIndex c.length j)
    edge_eq := ?_
    turns := ?_
    support_segment := ?_
    supports := fun j => hs (cycleIndex c.length j)
    hull_eq := ?_
    frontier_eq := ?_
    covers := ?_
  }⟩
  · simpa only [cycleIndex_nat] using radialVertex_injective c
  · simpa only [cycleIndex_nat] using radial_normalized_injective hirr ha c l d hl he
  · rw [← hHull,irredundant_extremePoints Q hirr]
    simp only [cycleIndex_nat]
    rw [← radialVertex_range ha.1 c]
    ext x
    simp
  · intro j
    rw [cycleIndex_next]
    exact he (cycleIndex c.length j)
  · intro j
    rw [cycleIndex_next]
    exact radial_normalized_turn hirr ha c l d hl he (cycleIndex c.length j)
  · intro j z
    rw [cycleIndex_next]
    exact hface (cycleIndex c.length j) z
  · ext x
    constructor
    · intro hx j
      exact hs (cycleIndex c.length j) x hx
    · intro hx
      rw [← hHull]
      apply radial_halfplanes_hull hirr ha c x
      intro i
      have hi := hx (i.val : ℤ)
      simp only [cycleIndex_nat] at hi
      rw [scaled_edge_det _ _ _ _ (he i)]
      exact mul_nonneg (by positivity) hi
  · rw [← hHull,radial_frontier hirr ha c]
    simp only [cycleIndex_next,cycleIndex_nat]
  · rw [radial_normalized_covers hirr ha c hQB hHull harea l d hl hd he]
    simp only [cycleIndex_nat]

end
end ConvexNivat.Colle
