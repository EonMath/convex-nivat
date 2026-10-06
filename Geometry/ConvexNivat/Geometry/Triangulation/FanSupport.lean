import ConvexNivat.Geometry.Triangulation.FanGeometry
import ConvexNivat.Geometry.Triangulation.Coordinates

namespace ConvexNivat.PolygonTriangulation
open scoped BigOperators

private theorem weighted_three_mem {S : Set RealPlane} (hS : Convex ℝ S)
    {p u v : RealPlane} (hp : p ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) :
    (1-a-b) • p + a • u + b • v ∈ S := by
  have hh := hS.sum_mem (t := Finset.univ) (w := ![1-a-b,a,b]) (z := ![p,u,v])
    (by intro i hi; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_succ])
    (by intro i hi; fin_cases i
        · exact hp
        · exact hu
        · exact hv)
  simpa [Fin.sum_univ_succ, add_assoc] using hh

private theorem hull_weighted_of_relative (Q : Finset Lattice) (p q r z : Lattice)
    (hp : p ∈ Q) (hq : q ∈ Q) (hr : r ∈ Q) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (he : embed (z-p) = a • embed (q-p) + b • embed (r-p)) :
    embed z ∈ windowHull Q := by
  have hh := weighted_three_mem (windowHull_convex Q)
    (window_mem_hull Q hp) (window_mem_hull Q hq) (window_mem_hull Q hr) ha hb hab
  have he' : embed z = (1-a-b) • embed p + a • embed q + b • embed r := by
    simp only [embed_sub] at he
    calc
      embed z = embed p + (embed z - embed p) := by abel
      _ = embed p + (a • (embed q - embed p) + b • (embed r - embed p)) := by rw [he]
      _ = _ := by module
  exact he' ▸ hh

private theorem chain_mem_erase {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (c : RadialChain Q p N) (i : Fin (c.length+2)) : c.point i ∈ Q.erase p := by
  change c.point i ∈ (Q.erase p : Set Lattice)
  rw [← c.range_eq]
  exact Set.mem_range_self i

private theorem linear_det_identity (N : ℕ) (x y : RealPlane) :
    realDet x y = ell N x * kappa y - kappa x * ell N y := by
  simp only [realDet,ell,kappa]
  ring

private def ellMap (N : ℕ) : RealPlane →ₗ[ℝ] ℝ where
  toFun := ell N
  map_add' := by intros; simp [ell]; ring
  map_smul' := by intros; simp [ell]; ring

private def kappaMap : RealPlane →ₗ[ℝ] ℝ where
  toFun := kappa
  map_add' := by intros; simp [kappa]; ring
  map_smul' := by intros; simp [kappa]

private theorem det_support_convex (u v : RealPlane) :
    Convex ℝ {x | 0 ≤ realDet (v-u) (x-u)} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ realDet (v-u) (a • x+b • y-u)
  have he : realDet (v-u) (a • x+b • y-u) =
      a * realDet (v-u) (x-u) + b * realDet (v-u) (y-u) := by
    have hu : a • x+b • y-u = a • (x-u)+b • (y-u) := by
      calc
        a • x+b • y-u = a • x+b • y-(a+b) • u := by rw [hab,one_smul]
        _ = _ := by module
    rw [hu]
    simp [realDet]
    ring
  rw [he]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

/-- PT23: consecutive ordered generators are genuine supporting boundary edges. -/
theorem consecutive_radial_edge_supports_hull (Q : Finset Lattice)
    (hirr : Irredundant Q) (p : Lattice) (N : ℕ) (ha : Anchor Q p N)
    (c : RadialChain Q p N) :
    ∀ i : Fin (c.length + 1), ∀ x ∈ windowHull Q,
      0 ≤ realDet (embed (c.point i.succ - p) - embed (c.point i.castSucc - p))
        (x - embed p - embed (c.point i.castSucc - p)) := by
  classical
  intro i x hx
  let u := embed (c.point i.castSucc - p)
  let v := embed (c.point i.succ - p)
  have hi := chain_mem_erase c i.castSucc
  have hj := chain_mem_erase c i.succ
  have hd : 0 < realDet u v := by
    have hc := c.determinants i.castSucc i.succ Fin.castSucc_lt_succ
    dsimp [u,v]
    have he : realDet (embed (c.point i.castSucc-p)) (embed (c.point i.succ-p)) =
        (det (c.point i.castSucc-p) (c.point i.succ-p) : ℝ) := by simp [realDet,embed,det]
    rw [he]
    exact_mod_cast hc
  have hg : ∀ q ∈ Q, 0 ≤ realDet (v-u) (embed (q-p)-u) := by
    intro q hq
    by_cases hqp : q=p
    · subst q
      simp only [sub_self,embed_zero]
      have he : realDet (v-u) (0-u) = realDet u v := by simp [realDet]; ring
      rw [he]
      exact hd.le
    obtain ⟨j,hj'⟩ : ∃ j, c.point j=q := by
      apply c.range_eq.symm ▸ (show q ∈ (Q.erase p : Set Lattice) from Finset.mem_erase.mpr ⟨hqp,hq⟩)
    subst q
    by_cases hji : j=i.castSucc
    · subst j; simp [u,realDet]
    by_cases hjn : j=i.succ
    · subst j; change 0 ≤ realDet (v-u) (v-u); simp [realDet,mul_comm]
    by_contra! hn
    have obs := four_point_radial_obstruction (ellMap N) kappaMap
      (linear_det_identity N) u v (embed (c.point j-p))
      (ha.2 _ hi) (ha.2 _ hj) (ha.2 _ (chain_mem_erase c j))
    by_cases hjlt : j < i.castSucc
    · obtain ⟨ha',hb',hab',he,_⟩ := obs.1 ⟨c.slopes hjlt,c.slopes Fin.castSucc_lt_succ⟩ hn
      apply hirr _ (Finset.mem_of_mem_erase hi)
      exact hull_weighted_of_relative (Q.erase (c.point i.castSucc)) p (c.point j)
        (c.point i.succ) (c.point i.castSucc)
        (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1.symm,ha.1⟩)
        (Finset.mem_erase.mpr ⟨fun h => hji (c.injective h),Finset.mem_of_mem_erase (chain_mem_erase c j)⟩)
        (Finset.mem_erase.mpr ⟨fun h => (ne_of_lt Fin.castSucc_lt_succ) (c.injective h).symm,Finset.mem_of_mem_erase hj⟩)
        _ _ ha'.le hb'.le hab'.le he
    · have hgt : i.succ < j := by
        have hvj := j.isLt
        have hvi := i.isLt
        simp only [Fin.lt_def,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ] at *
        omega
      obtain ⟨ha',hb',hab',he,_⟩ := obs.2 ⟨c.slopes Fin.castSucc_lt_succ,c.slopes hgt⟩ hn
      apply hirr _ (Finset.mem_of_mem_erase hj)
      exact hull_weighted_of_relative (Q.erase (c.point i.succ)) p (c.point i.castSucc)
        (c.point j) (c.point i.succ)
        (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1.symm,ha.1⟩)
        (Finset.mem_erase.mpr ⟨fun h => (ne_of_lt Fin.castSucc_lt_succ) (c.injective h),Finset.mem_of_mem_erase hi⟩)
        (Finset.mem_erase.mpr ⟨fun h => hjn (c.injective h),Finset.mem_of_mem_erase (chain_mem_erase c j)⟩)
        _ _ ha'.le hb'.le hab'.le he
  have hconv := det_support_convex (embed (c.point i.castSucc)) (embed (c.point i.succ))
  have hinc : embed '' (Q : Set Lattice) ⊆
      {z | 0 ≤ realDet (embed (c.point i.succ)-embed (c.point i.castSucc))
        (z-embed (c.point i.castSucc))} := by
    rintro _ ⟨q,hq,rfl⟩
    have he₁ : v-u=embed (c.point i.succ)-embed (c.point i.castSucc) := by
      dsimp [u,v]; rw [embed_sub,embed_sub]; abel
    have he₂ : embed (q-p)-u=embed q-embed (c.point i.castSucc) := by
      dsimp [u]; rw [embed_sub,embed_sub]; abel
    have hh := hg q hq
    change 0 ≤ realDet (embed (c.point i.succ)-embed (c.point i.castSucc)) (embed q-embed (c.point i.castSucc))
    simpa only [he₁,he₂] using hh
  have hh := convexHull_min hinc hconv hx
  have he₁ : v-u=embed (c.point i.succ)-embed (c.point i.castSucc) := by
    dsimp [u,v]; rw [embed_sub,embed_sub]; abel
  have he₂ : x-embed p-u=x-embed (c.point i.castSucc) := by
    dsimp [u]; rw [embed_sub]; abel
  change 0 ≤ realDet (v-u) (x-embed p-u)
  rw [he₁,he₂]
  exact hh

private theorem linear_affine (f : RealPlane →ₗ[ℝ] ℝ) (p x y : RealPlane)
    (a b : ℝ) (hab : a+b=1) :
    f (a • x+b • y-p) = a*f (x-p)+b*f (y-p) := by
  simp only [map_sub,map_add,map_smul,smul_eq_mul]
  nlinarith [congrArg (fun z : ℝ => z*f p) hab]

private theorem linear_hull_nonneg (Q : Finset Lattice) (p : Lattice)
    (f : RealPlane →ₗ[ℝ] ℝ)
    (hg : ∀ q ∈ Q, 0 ≤ f (embed q-embed p)) :
    ∀ x ∈ windowHull Q, 0 ≤ f (x-embed p) := by
  apply convexHull_min
  · rintro _ ⟨q,hq,rfl⟩
    exact hg q hq
  · intro x hx y hy a b ha hb hab
    change 0 ≤ f (a • x+b • y-embed p)
    rw [linear_affine f _ _ _ _ _ hab]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

private theorem hull_anchor_positive (Q : Finset Lattice) (p : Lattice) (N : ℕ)
    (ha : Anchor Q p N) (x : RealPlane) (hx : x ∈ windowHull Q) (hxp : x ≠ embed p) :
    0 < ell N (x-embed p) := by
  have hh : ∀ z ∈ windowHull Q,
      0 ≤ ell N (z-embed p) ∧ (ell N (z-embed p)=0 → z=embed p) := by
    apply convexHull_min
    · rintro _ ⟨q,hq,rfl⟩
      by_cases hqp : q=p
      · subst q
        change 0 ≤ ell N (embed p-embed p) ∧ (ell N (embed p-embed p)=0 → embed p=embed p)
        simp [ell]
      · have hpos := ha.2 q (Finset.mem_erase.mpr ⟨hqp,hq⟩)
        rw [embed_sub] at hpos
        exact ⟨hpos.le,fun hz => False.elim ((ne_of_gt hpos) hz)⟩
    · apply convex_iff_forall_pos.mpr
      intro u hu v hv a b ha' hb' hab
      have he := linear_affine (ellMap N) (embed p) u v a b hab
      change ell N (a • u+b • v-embed p)=a*ell N (u-embed p)+b*ell N (v-embed p) at he
      refine ⟨?_,?_⟩
      · change 0 ≤ ell N (a • u+b • v-embed p)
        rw [he]
        exact add_nonneg (mul_nonneg ha'.le hu.1) (mul_nonneg hb'.le hv.1)
      · intro hz
        have hz' : a*ell N (u-embed p)+b*ell N (v-embed p)=0 := he ▸ hz
        have hu0 : ell N (u-embed p)=0 := by
          have hh := (add_eq_zero_iff_of_nonneg (mul_nonneg ha'.le hu.1) (mul_nonneg hb'.le hv.1)).1 hz'
          exact (mul_eq_zero.mp hh.1).resolve_left (ne_of_gt ha')
        have hv0 : ell N (v-embed p)=0 := by
          have hh := (add_eq_zero_iff_of_nonneg (mul_nonneg ha'.le hu.1) (mul_nonneg hb'.le hv.1)).1 hz'
          exact (mul_eq_zero.mp hh.2).resolve_left (ne_of_gt hb')
        rw [hu.2 hu0,hv.2 hv0,← add_smul,hab,one_smul]
  exact lt_of_le_of_ne (hh x hx).1 (fun hz => hxp ((hh x hx).2 hz.symm))

private theorem closed_adjacent_bracket (n : ℕ) (f : Fin (n+2) → ℝ) (r : ℝ)
    (hlo : f 0 ≤ r) (hhi : r ≤ f (Fin.last (n+1))) :
    ∃ i : Fin (n+1), f i.castSucc ≤ r ∧ r ≤ f i.succ := by
  induction n with
  | zero => exact ⟨0,hlo,hhi⟩
  | succ n ih =>
    by_cases h : r ≤ f ⟨1,by omega⟩
    · exact ⟨0,hlo,h⟩
    · obtain ⟨i,hi⟩ := ih (fun j => f j.succ) (le_of_lt (lt_of_not_ge h)) hhi
      exact ⟨i.succ,hi⟩

/-- PT25: closed adjacent slope brackets include both extreme rays. -/
theorem hull_point_slope_bracket (Q : Finset Lattice) (p : Lattice) (N : ℕ)
    (ha : Anchor Q p N) (c : RadialChain Q p N) (x : RealPlane)
    (hx : x ∈ windowHull Q) (hxp : x ≠ embed p) :
    0 < ell N (x - embed p) ∧
    ∃ i : Fin (c.length + 1),
      slope N (embed (c.point i.castSucc - p)) ≤ slope N (x - embed p) ∧
      slope N (x - embed p) ≤ slope N (embed (c.point i.succ - p)) := by
  have hpos := hull_anchor_positive Q p N ha x hx hxp
  refine ⟨hpos, closed_adjacent_bracket c.length
    (fun j => slope N (embed (c.point j-p))) (slope N (x-embed p)) ?_ ?_⟩
  · let s := slope N (embed (c.point 0-p))
    have hh := linear_hull_nonneg Q p (kappaMap-s • ellMap N) (by
      intro q hq
      by_cases hqp : q=p
      · subst q; simp
      · obtain ⟨j,rfl⟩ : ∃ j, c.point j=q := by
          apply c.range_eq.symm ▸ (show q ∈ (Q.erase p : Set Lattice) from Finset.mem_erase.mpr ⟨hqp,hq⟩)
        have hj := ha.2 _ (chain_mem_erase c j)
        have hs : s ≤ slope N (embed (c.point j-p)) := c.slopes.monotone (Fin.zero_le j)
        have hb := (le_div_iff₀ hj).1 hs
        change 0 ≤ kappa (embed (c.point j)-embed p)-s*ell N (embed (c.point j)-embed p)
        rw [← embed_sub]
        linarith) x hx
    change 0 ≤ kappa (x-embed p)-s*ell N (x-embed p) at hh
    exact (le_div_iff₀ hpos).2 (by linarith)
  · let s := slope N (embed (c.point (Fin.last (c.length+1))-p))
    have hh := linear_hull_nonneg Q p (s • ellMap N-kappaMap) (by
      intro q hq
      by_cases hqp : q=p
      · subst q; simp
      · obtain ⟨j,rfl⟩ : ∃ j, c.point j=q := by
          apply c.range_eq.symm ▸ (show q ∈ (Q.erase p : Set Lattice) from Finset.mem_erase.mpr ⟨hqp,hq⟩)
        have hj := ha.2 _ (chain_mem_erase c j)
        have hs : slope N (embed (c.point j-p)) ≤ s := c.slopes.monotone (Fin.le_last j)
        have hb := (div_le_iff₀ hj).1 hs
        change 0 ≤ s*ell N (embed (c.point j)-embed p)-kappa (embed (c.point j)-embed p)
        rw [← embed_sub]
        linarith) x hx
    change 0 ≤ s*ell N (x-embed p)-kappa (x-embed p) at hh
    exact (div_le_iff₀ hpos).2 (by linarith)

/-- PT26: the literal fan covers every real point of the closed polygon. -/
theorem fan_covers_actual_polygon (Q : Finset Lattice) (hirr : Irredundant Q)
    (p : Lattice) (N : ℕ) (ha : Anchor Q p N) (c : RadialChain Q p N) :
    ∀ x ∈ windowHull Q, ∃ i : Fin (c.length + 1), x ∈ (fanCell c i).carrier := by
  intro x hx
  by_cases hxp : x=embed p
  · subst x
    exact ⟨0,window_mem_hull _ (by simp [fanCell,LatticeTriangle.vertices])⟩
  obtain ⟨hpos,i,hlo,hhi⟩ := hull_point_slope_bracket Q p N ha c x hx hxp
  refine ⟨i,?_⟩
  have hnd : delta (fanCell c i) ≠ 0 :=
    ne_of_gt (c.determinants i.castSucc i.succ Fin.castSucc_lt_succ)
  apply (nondegenerate_triangle_barycentric_unique (fanCell c i) hnd x).2.2.1.mpr
  let u := embed (c.point i.castSucc-p)
  let v := embed (c.point i.succ-p)
  let y := x-embed p
  have hu : 0 < ell N u := ha.2 _ (chain_mem_erase c i.castSucc)
  have hv : 0 < ell N v := ha.2 _ (chain_mem_erase c i.succ)
  have hd : 0 < realDet u v := by
    have he : realDet u v = (det (c.point i.castSucc-p) (c.point i.succ-p) : ℝ) := by
      simp [u,v,realDet,embed,det]
    rw [he]
    exact_mod_cast c.determinants i.castSucc i.succ Fin.castSucc_lt_succ
  have hdyv : 0 ≤ realDet y v := by
    rw [linear_det_identity N]
    have hh := (div_le_div_iff₀ hpos hv).1 hhi
    dsimp [y,v] at *
    linarith
  have hduy : 0 ≤ realDet u y := by
    rw [linear_det_identity N]
    have hh := (div_le_div_iff₀ hu hpos).1 hlo
    dsimp [u,y] at *
    linarith
  have hsupp := consecutive_radial_edge_supports_hull Q hirr p N ha c i x hx
  have hsum : realDet y v / realDet u v + realDet u y / realDet u v ≤ 1 := by
    rw [← add_div,div_le_one hd]
    change 0 ≤ realDet (v-u) (y-u) at hsupp
    have he : realDet (v-u) (y-u)=realDet u v-realDet y v-realDet u y := by
      simp [realDet]; ring
    rw [he] at hsupp
    linarith
  intro j
  fin_cases j
  · change 0 ≤ 1-realDet y v/realDet u v-realDet u y/realDet u v
    linarith
  · change 0 ≤ realDet y v/realDet u v
    exact div_nonneg hdyv hd.le
  · change 0 ≤ realDet u y/realDet u v
    exact div_nonneg hduy hd.le

end ConvexNivat.PolygonTriangulation
