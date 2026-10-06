import ConvexNivat.Colle.Shared.RegionAnchor
import ConvexNivat.Colle.Shared.RowCoordinates
import ConvexNivat.Geometry.Basic

namespace ConvexNivat.Colle
noncomputable section

private theorem eg_real_det (u z : Lattice) :
    realDet (embed u) (embed z) = (det u z : ℝ) := by
  simp [realDet, embed, det]

private theorem eg_det_add (u z t : Lattice) : det u (z+t) = det u z+det u t := by
  dsimp [det]
  ring

private theorem eg_det_sub (u z t : Lattice) : det u (z-t) = det u z-det u t := by
  dsimp [det]
  ring

private theorem eg_det_smul (u z : Lattice) (n : ℤ) : det u (n•z) = n*det u z := by
  dsimp [det]
  ring

private theorem eg_det_self (u : Lattice) : det u u = 0 := by dsimp [det]; ring

private theorem eg_second_anchor_mem {v w : Lattice} (P : Region v w) :
    embed P.secondAnchor ∈ P.carrier := by
  apply P.closed.closure_eq ▸ (frontier_subset_closure (s := P.carrier) ?_)
  rw [P.boundary_eq]
  exact Or.inl (Or.inr ⟨0, le_rfl, by simp [Region.secondAnchor]⟩)

private theorem eg_recession_add {v w : Lattice} (P : Region v w)
    (x : RealPlane) (hx : x ∈ P.carrier) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    x - a • embed v + b • embed w ∈ P.carrier := by
  have hcone : -a • embed v+b • embed w ∈ twoRayCone (-v) w := by
    refine ⟨a,b,ha,hb,?_⟩
    simp [embed, neg_smul]
  have hrec : -a • embed v+b • embed w ∈ recessionCone P.carrier := by
    rw [(region_halfplane_representation P).2.2.1]
    exact hcone
  have h := hrec x hx
  convert h using 1
  simp only [neg_smul]
  abel

private theorem eg_vertex_mem {v w : Lattice} (P : Region v w)
    (j : Fin (P.boundedCount+1)) : embed (P.vertex j) ∈ P.carrier := by
  rw [(region_halfplane_representation P).2.1]
  refine ⟨embed (P.vertex j), subset_convexHull ℝ _ ⟨j,rfl⟩, 0, ?_, by simp⟩
  exact ⟨0,0,le_rfl,le_rfl,by simp⟩

private theorem eg_predecessor_turn {v w : Lattice} (P : Region v w) :
    0 < det P.predecessor w := by
  unfold Region.predecessor
  split_ifs with h
  · apply P.second_turn
    simp
    omega
  · exact P.turn_positive

private theorem eg_predecessor_support {v w : Lattice} (P : Region v w) :
    ∀ x ∈ P.carrier, 0 ≤ realDet (embed P.predecessor) (x-embed P.secondAnchor) := by
  intro x hx
  unfold Region.predecessor
  split_ifs with h
  · let j : Fin P.boundedCount := ⟨P.boundedCount-1, Nat.sub_lt h Nat.zero_lt_one⟩
    have hj : j.succ = (⟨P.boundedCount,Nat.lt_succ_self _⟩ : Fin (P.boundedCount+1)) := by
      apply Fin.ext
      dsimp [j]
      omega
    have hb := P.bounded_support j x hx
    obtain ⟨k,hk,hlen⟩ := P.bounded_length j
    have hdet : realDet (embed (P.boundedDirection j)) (embed P.secondAnchor-embed (P.vertex j.castSucc)) = 0 := by
      rw [← embed_sub, eg_real_det]
      have heq : P.secondAnchor = P.vertex j.succ := by rw [hj]; rfl
      rw [heq, hlen, eg_det_smul, eg_det_self, mul_zero]
      simp
    change 0 ≤ realDet (embed (P.boundedDirection j)) (x-embed P.secondAnchor)
    dsimp [realDet] at *
    nlinarith
  · have hn : P.boundedCount = 0 := by omega
    have heq : P.firstAnchor = P.secondAnchor := by
      unfold Region.firstAnchor Region.secondAnchor
      congr 1
      apply Fin.ext
      exact hn.symm
    have hh := P.first_support x hx
    change 0 ≤ realDet (embed v) (x-embed P.firstAnchor) at hh
    rwa [heq] at hh

private theorem eg_predecessor_unit_segment {v w : Lattice} (P : Region v w)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    embed P.secondAnchor - r • embed P.predecessor ∈ P.carrier := by
  unfold Region.predecessor
  split_ifs with h
  · let j : Fin P.boundedCount := ⟨P.boundedCount-1,Nat.sub_lt h Nat.zero_lt_one⟩
    obtain ⟨k,hk,hlen⟩ := P.bounded_length j
    have hj : j.succ = (⟨P.boundedCount,Nat.lt_succ_self _⟩ : Fin (P.boundedCount+1)) := by
      apply Fin.ext
      dsimp [j]
      omega
    have heq : P.vertex j.castSucc = P.secondAnchor-k•P.boundedDirection j := by
      have hlast : P.vertex j.succ = P.secondAnchor := by rw [hj]; rfl
      rw [hlast] at hlen
      rw [← hlen]
      abel
    have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0:ℝ) < k := by linarith
    have hratio : r/(k:ℝ) ≤ 1 := (div_le_one hkpos).mpr (hr1.trans hkR)
    have hm := P.convex (eg_second_anchor_mem P) (eg_vertex_mem P j.castSucc)
      (sub_nonneg.mpr hratio) (div_nonneg hr0 hkpos.le) (show (1-r/(k:ℝ))+r/k=1 by ring)
    rw [heq] at hm
    convert hm using 1
    ext <;> simp [embed] <;> field_simp <;> ring
  · simpa only [zero_smul, add_zero] using
      eg_recession_add P (embed P.secondAnchor) (eg_second_anchor_mem P) r 0 hr0 le_rfl

private theorem eg_lattice_second_support {v w : Lattice} (P : Region v w)
    (z : Lattice) (hz : z ∈ P.lattice) : det w P.secondAnchor ≤ det w z := by
  have h := P.second_support (embed z) hz
  change 0 ≤ realDet (embed w) (embed z-embed P.secondAnchor) at h
  rw [← embed_sub, eg_real_det, eg_det_sub] at h
  have hZ : (0:ℤ) ≤ det w z-det w P.secondAnchor := by exact_mod_cast h
  exact sub_nonneg.mp hZ

private theorem eg_enlargement_contains {v w : Lattice} (P : Region v w) (n : ℕ) :
    P.lattice ⊆ P.enlargement n := by
  intro z hz
  exact ⟨z,hz,0,by simp,Or.inl hz⟩

private theorem eg_enlargement_mono {v w : Lattice} (P : Region v w) :
    Monotone P.enlargement := by
  intro n m hnm z hz
  rcases hz with ⟨g,hg,t,hz,hrow⟩
  refine ⟨g,hg,t,hz,?_⟩
  rcases hrow with hrow|⟨hlo,hhi⟩
  · exact Or.inl hrow
  · right
    have hnmZ : (n:ℤ) ≤ m := by exact_mod_cast hnm
    exact ⟨by omega,hhi⟩

private theorem eg_enlargement_lower {v w : Lattice} (P : Region v w) (n : ℕ)
    (z : Lattice) (hz : z ∈ P.enlargement n) :
    det w P.secondAnchor-(n:ℤ) ≤ det w z := by
  rcases hz with ⟨g,hg,t,hz,hrow⟩
  rcases hrow with hrow|⟨hlo,hhi⟩
  · have h := eg_lattice_second_support P z hrow
    omega
  · exact hlo

private theorem eg_enlargement_predecessor_support {v w : Lattice} (P : Region v w)
    (n : ℕ) (z : Lattice) (hz : z ∈ P.enlargement n) :
    det P.predecessor P.secondAnchor ≤ det P.predecessor z := by
  obtain ⟨g,hg,t,rfl,hrow⟩ := hz
  have hs := eg_predecessor_support P (embed g) hg
  rw [← embed_sub, eg_real_det, eg_det_sub] at hs
  have hsZ : (0:ℤ) ≤ det P.predecessor g-det P.predecessor P.secondAnchor := by exact_mod_cast hs
  rw [eg_det_add, eg_det_smul, eg_det_self, mul_zero, add_zero]
  omega

private theorem eg_enlargement_forward {v w : Lattice} (P : Region v w) (n : ℕ) :
    ForwardInvariant (P.enlargement n) w := by
  intro z hz
  obtain ⟨g,hg,t,hzeq,hrow⟩ := hz
  have hinv := (region_halfplane_representation P).2.2.2.2
  refine ⟨g+w,hinv g hg,t,?_,?_⟩
  · rw [hzeq]; abel
  · rcases hrow with hrow|⟨hlo,hhi⟩
    · exact Or.inl (hinv z hrow)
    · right
      rw [eg_det_add, eg_det_self, add_zero]
      exact ⟨hlo,hhi⟩

private theorem eg_forward_nsmul (U : Set Lattice) (w : Lattice)
    (hinv : ForwardInvariant U w) (n : ℕ) : ForwardInvariant U ((n:ℤ)•w) := by
  intro z hz
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    convert hinv _ ih using 1
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

private theorem eg_det_basis_real (d w : RealPlane) (hD : realDet d w ≠ 0) (z : RealPlane) :
    z = (-realDet w z/realDet d w) • d + (realDet d z/realDet d w) • w := by
  have heq : realDet d w • z = (-realDet w z) • d + realDet d z • w := by
    ext <;> dsimp [realDet] <;> ring
  have h := congrArg (fun p : RealPlane => (realDet d w)⁻¹ • p) heq
  simpa only [smul_add, smul_smul, inv_mul_cancel₀ hD, one_smul, ← div_eq_inv_mul] using h

private theorem eg_outside_mem {v w : Lattice} (P : Region v w) (n : ℕ)
    (z : Lattice) (hlo : det w P.secondAnchor-(n:ℤ) ≤ det w z)
    (hhi : det w z ≤ det w P.secondAnchor)
    (hsupp : det P.predecessor P.secondAnchor ≤ det P.predecessor z) :
    z ∈ P.enlargement n := by
  let D : ℝ := det P.predecessor w
  let j : ℝ := (det w P.secondAnchor : ℝ)-(det w z : ℝ)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast eg_predecessor_turn P
  have hj : 0 ≤ j := by dsimp [j]; exact_mod_cast sub_nonneg.mpr hhi
  let t : ℕ := ⌈j/D⌉₊
  let r : ℝ := (t:ℝ)-j/D
  have hr0 : 0 ≤ r := by dsimp [r,t]; exact sub_nonneg.mpr (Nat.le_ceil (j/D))
  have hr1 : r ≤ 1 := by
    have ht := Nat.ceil_lt_add_one (div_nonneg hj hD.le)
    dsimp [r,t]
    linarith
  let b : ℝ := ((det P.predecessor z : ℝ)-(det P.predecessor P.secondAnchor : ℝ))/D
  have hb : 0 ≤ b := by
    apply div_nonneg _ hD.le
    exact_mod_cast sub_nonneg.mpr hsupp
  let g : Lattice := z-(t:ℤ)•P.predecessor
  have hgeq : embed g = embed P.secondAnchor-r•embed P.predecessor+b•embed w := by
    have hbase := eg_det_basis_real (embed P.predecessor) (embed w)
      (by rw [eg_real_det]; exact ne_of_gt hD) (embed z-embed P.secondAnchor)
    have hh1 : realDet (embed w) (embed z-embed P.secondAnchor) = -j := by
      rw [← embed_sub, eg_real_det, eg_det_sub]
      dsimp [j]
      push_cast
      ring
    have hh2 : realDet (embed P.predecessor) (embed z-embed P.secondAnchor) =
        (det P.predecessor z : ℝ)-(det P.predecessor P.secondAnchor : ℝ) := by
      rw [← embed_sub, eg_real_det, eg_det_sub]
      push_cast
      rfl
    rw [hh1, hh2, eg_real_det] at hbase
    have hg : embed g = embed z-(t:ℝ)•embed P.predecessor := by
      ext <;> simp [g,embed]
    rw [hg]
    change embed z-embed P.secondAnchor = _ at hbase
    have hzbase : embed z = embed P.secondAnchor+
        (j/D)•embed P.predecessor+b•embed w := by
      dsimp [b,D] at *
      simp only [neg_neg] at hbase
      linear_combination hbase
    rw [hzbase]
    dsimp [r]
    module
  have hg : g ∈ P.lattice := by
    change embed g ∈ P.carrier
    rw [hgeq]
    have hmem := eg_recession_add P
      (embed P.secondAnchor-r•embed P.predecessor)
      (eg_predecessor_unit_segment P r hr0 hr1) 0 b le_rfl hb
    simpa only [zero_smul,sub_zero] using hmem
  exact ⟨g,hg,t,by dsimp [g]; abel,Or.inr ⟨hlo,hhi⟩⟩

private theorem eg_collar_membership {v w : Lattice} (P : Region v w) (n : ℕ)
    (z : Lattice) (hz : det w z ≤ det w P.secondAnchor) :
    z ∈ P.enlargement n ↔ det w P.secondAnchor-(n:ℤ) ≤ det w z ∧
      det P.predecessor P.secondAnchor ≤ det P.predecessor z := by
  constructor
  · intro h
    exact ⟨eg_enlargement_lower P n z h,eg_enlargement_predecessor_support P n z h⟩
  · rintro ⟨hlo,hsupp⟩
    exact eg_outside_mem P n z hlo hz hsupp

private theorem eg_integer_row_ray (d w : Lattice) (hw : Primitive w)
    (hD : 0 < det d w) (height threshold : ℤ) :
    ∃ p : Lattice, det w p = height ∧ ∀ z : Lattice, det w z = height →
      (threshold ≤ det d z ↔ ∃ a : ℕ, z = p+(a:ℤ)•w) := by
  obtain ⟨q,hq⟩ := primitive_height_surjective w hw height
  change det w q = height at hq
  let r : ℝ := ((threshold:ℝ)-(det d q:ℝ))/(det d w:ℝ)
  let k : ℤ := ⌈r⌉
  let p : Lattice := q+k•w
  have hDR : (0:ℝ) < det d w := by exact_mod_cast hD
  have hbound : ∀ a : ℤ, threshold ≤ det d (q+a•w) ↔ k ≤ a := by
    intro a
    rw [eg_det_add,eg_det_smul]
    have hc : k ≤ a ↔ r ≤ (a:ℝ) := Int.ceil_le
    rw [hc]
    dsimp [r]
    rw [div_le_iff₀ hDR]
    constructor <;> intro h
    · have hR : (threshold:ℝ) ≤ (det d q:ℝ)+(a:ℝ)*(det d w:ℝ) := by exact_mod_cast h
      linarith
    · have hR : (threshold:ℝ) ≤ (det d q:ℝ)+(a:ℝ)*(det d w:ℝ) := by linarith
      exact_mod_cast hR
  refine ⟨p,?_,?_⟩
  · dsimp [p]
    rw [eg_det_add,eg_det_smul,eg_det_self,mul_zero,add_zero,hq]
  · intro z hz
    obtain ⟨a,ha⟩ := ((primitive_row_coordinates w hw).2.1 q z).mp (hq.trans hz.symm)
    constructor
    · intro hb
      have hka : k ≤ a := (hbound a).mp (ha ▸ hb)
      refine ⟨(a-k).toNat,?_⟩
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hka),ha]
      dsimp [p]
      rw [sub_smul]
      abel
    · rintro ⟨b,rfl⟩
      have hb : k ≤ k+(b:ℤ) := by omega
      have hp : p+(b:ℤ)•w = q+(k+(b:ℤ))•w := by dsimp [p];rw [add_smul];abel
      rw [hp]
      exact (hbound _).mpr hb

private theorem eg_collar_endpoint_family {v w : Lattice} (P : Region v w) (n : ℕ) :
    ∃ endpoint : ℕ → Lattice, ∀ j : ℕ, 0 < j → j ≤ n →
      det w (endpoint j) = det w P.secondAnchor-(j:ℤ) ∧
      ∀ z : Lattice, det w z = det w P.secondAnchor-(j:ℤ) →
        (z ∈ P.enlargement n ↔ ∃ a : ℕ, z = endpoint j+(a:ℤ)•w) := by
  classical
  have hex : ∀ j : ℕ, ∃ p : Lattice, det w p = det w P.secondAnchor-(j:ℤ) ∧
      ∀ z : Lattice, det w z = det w P.secondAnchor-(j:ℤ) →
        (det P.predecessor P.secondAnchor ≤ det P.predecessor z ↔
          ∃ a : ℕ, z = p+(a:ℤ)•w) := by
    intro j
    exact eg_integer_row_ray P.predecessor w P.second_primitive (eg_predecessor_turn P) _ _
  choose endpoint hheight hmembership using hex
  refine ⟨endpoint,?_⟩
  intro j hj hjn
  refine ⟨hheight j,?_⟩
  intro z hz
  rw [eg_collar_membership P n z (by rw [hz];omega)]
  have hlo : det w P.secondAnchor-(n:ℤ) ≤ det w z := by rw [hz];omega
  simp only [hlo,true_and]
  exact hmembership j z hz

private theorem eg_real_det_add (u x y : RealPlane) :
    realDet u (x+y) = realDet u x+realDet u y := by dsimp [realDet];ring

private theorem eg_real_det_sub (u x y : RealPlane) :
    realDet u (x-y) = realDet u x-realDet u y := by dsimp [realDet];ring

private theorem eg_real_det_smul (u x : RealPlane) (t : ℝ) :
    realDet u (t•x) = t*realDet u x := by dsimp [realDet];ring

private theorem eg_second_ray {v w : Lattice} (P : Region v w)
    (b : ℝ) (hb : 0 ≤ b) : embed P.secondAnchor+b•embed w ∈ P.carrier := by
  simpa using eg_recession_add P _ (eg_second_anchor_mem P) 0 b le_rfl hb

private theorem eg_shift_above_second {v w : Lattice} (P : Region v w)
    (y : RealPlane) (hy : y ∈ P.carrier) (t : ℝ) (ht : 0 ≤ t)
    (habove : (det w P.secondAnchor:ℝ) ≤ realDet (embed w) (y+t•embed P.predecessor)) :
    y+t•embed P.predecessor ∈ P.carrier := by
  let D : ℝ := det P.predecessor w
  have hD : 0 < D := by dsimp [D];exact_mod_cast eg_predecessor_turn P
  let a : ℝ := realDet (embed w) (y-embed P.secondAnchor)/D
  let b : ℝ := realDet (embed P.predecessor) (y-embed P.secondAnchor)/D
  have ha : 0 ≤ a := div_nonneg (P.second_support y hy) hD.le
  have hb : 0 ≤ b := div_nonneg (eg_predecessor_support P y hy) hD.le
  have hrepr : y = embed P.secondAnchor-a•embed P.predecessor+b•embed w := by
    have hbase := eg_det_basis_real (embed P.predecessor) (embed w)
      (by rw [eg_real_det];exact ne_of_gt hD) (y-embed P.secondAnchor)
    rw [eg_real_det] at hbase
    change y-embed P.secondAnchor = (-realDet (embed w) (y-embed P.secondAnchor)/D)•embed P.predecessor+b•embed w at hbase
    rw [neg_div, neg_smul] at hbase
    change y-embed P.secondAnchor = -(a•embed P.predecessor)+b•embed w at hbase
    linear_combination hbase
  have ht_le : t ≤ a := by
    have hwd : realDet (embed w) (embed P.predecessor) = -D := by
      rw [eg_real_det]
      dsimp [D,det]
      push_cast
      ring
    rw [eg_real_det_add,eg_real_det_smul,hwd] at habove
    have haeq : a*D = realDet (embed w) y-(det w P.secondAnchor:ℝ) := by
      dsimp [a]
      rw [eg_real_det_sub,eg_real_det,div_mul_cancel₀ _ (ne_of_gt hD)]
    nlinarith
  by_cases ha0 : a = 0
  · have ht0 : t = 0 := by linarith
    simpa only [ht0,zero_smul,add_zero] using hy
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hm := P.convex hy (eg_second_ray P b hb)
    (sub_nonneg.mpr ((div_le_one hapos).mpr ht_le)) (div_nonneg ht hapos.le)
    (show (1-t/a)+t/a=1 by ring)
  convert hm using 1
  rw [hrepr]
  ext <;> dsimp <;> field_simp <;> ring

private theorem eg_continuous_enlargement_mem {v w : Lattice} (P : Region v w) (n : ℕ)
    (z : Lattice) (y : RealPlane) (hy : y ∈ P.carrier) (t : ℝ) (ht : 0 ≤ t)
    (hz : embed z = y+t•embed P.predecessor)
    (hlo : (det w P.secondAnchor:ℝ)-(n:ℝ) ≤ realDet (embed w) (embed z)) :
    z ∈ P.enlargement n := by
  by_cases hhi : det w z ≤ det w P.secondAnchor
  · refine eg_outside_mem P n z ?_ hhi ?_
    · rw [eg_real_det] at hlo
      exact_mod_cast hlo
    · have hs := eg_predecessor_support P y hy
      have hd : realDet (embed P.predecessor) (embed z-embed P.secondAnchor) =
          realDet (embed P.predecessor) (y-embed P.secondAnchor) := by
        rw [hz]
        dsimp [realDet]
        ring
      rw [← hd,← embed_sub,eg_real_det,eg_det_sub] at hs
      have hsZ : 0 ≤ det P.predecessor z-det P.predecessor P.secondAnchor := by exact_mod_cast hs
      exact sub_nonneg.mp hsZ
  · apply eg_enlargement_contains P n
    change embed z ∈ P.carrier
    rw [hz]
    apply eg_shift_above_second P y hy t ht
    rw [← hz,eg_real_det]
    exact_mod_cast (show det w P.secondAnchor ≤ det w z by omega)

private theorem eg_enlargement_real_witness {v w : Lattice} (P : Region v w)
    (n : ℕ) (z : Lattice) (hz : z ∈ P.enlargement n) :
    (∃ y ∈ P.carrier, ∃ t : ℝ, 0 ≤ t ∧ embed z = y+t•embed P.predecessor) ∧
      (det w P.secondAnchor:ℝ)-(n:ℝ) ≤ realDet (embed w) (embed z) := by
  have hlo := eg_enlargement_lower P n z hz
  obtain ⟨g,hg,t,hz,hrow⟩ := hz
  constructor
  · exact ⟨embed g,hg,t,by positivity,by rw [hz];ext <;> simp [embed]⟩
  · rw [eg_real_det]
    exact_mod_cast hlo

private theorem eg_enlargement_above {v w : Lattice} (P : Region v w)
    (n : ℕ) (z : Lattice) (hz : z ∈ P.enlargement n)
    (hge : det w P.secondAnchor ≤ det w z) : z ∈ P.lattice := by
  obtain ⟨⟨y,hy,t,ht,hz⟩,hlo⟩ := eg_enlargement_real_witness P n z hz
  change embed z ∈ P.carrier
  rw [hz]
  apply eg_shift_above_second P y hy t ht
  rw [← hz,eg_real_det]
  exact_mod_cast hge

private theorem eg_enlargement_hull_subset {v w : Lattice} (P : Region v w)
    (n : ℕ) (G : Finset Lattice) (hG : (G:Set Lattice) ⊆ P.enlargement n) :
    embed ⁻¹' finiteRayHull G (-v) w ⊆ P.enlargement n := by
  let K : Set RealPlane := {x | (∃ y ∈ P.carrier, ∃ t : ℝ, 0 ≤ t ∧ x=y+t•embed P.predecessor) ∧
      (det w P.secondAnchor:ℝ)-(n:ℝ) ≤ realDet (embed w) x}
  have hconv : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    obtain ⟨⟨p,hp,t,ht,rfl⟩,hx⟩ := hx
    obtain ⟨⟨q,hq,s,hs,rfl⟩,hy⟩ := hy
    refine ⟨⟨a•p+b•q,P.convex hp hq ha hb hab,a*t+b*s,
      add_nonneg (mul_nonneg ha ht) (mul_nonneg hb hs),by module⟩,?_⟩
    rw [eg_real_det_add,eg_real_det_smul,eg_real_det_smul]
    calc
      _ = a*((det w P.secondAnchor:ℝ)-(n:ℝ))+b*((det w P.secondAnchor:ℝ)-(n:ℝ)) := by
        rw [← add_mul,hab,one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  have hpoints : embed '' (G:Set Lattice) ⊆ K := by
    rintro _ ⟨z,hz,rfl⟩
    exact eg_enlargement_real_witness P n z (hG hz)
  have hH : windowHull G ⊆ K := convexHull_min hpoints hconv
  intro z hz
  obtain ⟨x,hx,u,hu,hz⟩ := hz
  obtain ⟨⟨y,hy,t,ht,hx⟩,hlow⟩ := hH hx
  obtain ⟨a,b,ha,hb,hu⟩ := hu
  have huneg : u = -a•embed v+b•embed w := by
    rw [hu]
    simp [embed,neg_smul]
  have hheight : 0 ≤ realDet (embed w) u := by
    rw [hu,eg_real_det_add,eg_real_det_smul,eg_real_det_smul,eg_real_det,eg_real_det,eg_det_self]
    have hturn : (0:ℝ) ≤ det w (-v) := by
      have heq : det w (-v) = det v w := by dsimp [det];ring
      rw [heq]
      exact_mod_cast P.turn_positive.le
    simp only [Int.cast_zero,mul_zero,add_zero]
    exact mul_nonneg ha hturn
  apply eg_continuous_enlargement_mem P n z
    (y-a•embed v+b•embed w) (eg_recession_add P y hy a b ha hb) t ht
  · rw [hz,hx,huneg]
    module
  · rw [hz,eg_real_det_add]
    linarith

private theorem eg_finite_collar_hull {v w : Lattice} (P : Region v w) (n : ℕ) :
    ∃ G : Finset Lattice, (G:Set Lattice) ⊆ P.enlargement n ∧
      P.enlargement n = embed ⁻¹' finiteRayHull G (-v) w := by
  classical
  obtain ⟨G₀,hG₀,hcell,hgen⟩ := integer_recession_finite_anchor P
  obtain ⟨endpoint,he⟩ := eg_collar_endpoint_family P n
  let G : Finset Lattice := G₀ ∪ (Finset.Icc 1 n).image endpoint
  have hG : (G:Set Lattice) ⊆ P.enlargement n := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · exact eg_enlargement_contains P n (hG₀ hz)
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
      have hjn := (Finset.mem_Icc.mp hj).2
      exact ((he j hj0 hjn).2 _ (he j hj0 hjn).1).mpr ⟨0,by simp⟩
  refine ⟨G,hG,Set.Subset.antisymm ?_ (eg_enlargement_hull_subset P n G hG)⟩
  intro z hz
  by_cases hzP : z ∈ P.lattice
  · rw [hgen] at hzP
    obtain ⟨g,hg,a,b,rfl⟩ := hzP
    refine ⟨embed g,window_mem_hull G (Finset.mem_union.mpr (Or.inl hg)),
      (a:ℝ)•embed (-v)+(b:ℝ)•embed w,⟨a,b,by positivity,by positivity,rfl⟩,?_⟩
    ext <;> simp [embed] <;> ring
  · have hlt : det w z < det w P.secondAnchor := lt_of_not_ge (fun hge => hzP (eg_enlargement_above P n z hz hge))
    let j : ℕ := (det w P.secondAnchor-det w z).toNat
    have hjcast : (j:ℤ) = det w P.secondAnchor-det w z := Int.toNat_of_nonneg (by omega)
    have hj0 : 0 < j := by omega
    have hjn : j ≤ n := by have h := eg_enlargement_lower P n z hz;omega
    have hzheight : det w z = det w P.secondAnchor-(j:ℤ) := by omega
    obtain ⟨a,ha⟩ := ((he j hj0 hjn).2 z hzheight).mp hz
    refine ⟨embed (endpoint j),window_mem_hull G ?_,(a:ℝ)•embed w,?_,?_⟩
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j,Finset.mem_Icc.mpr ⟨hj0,hjn⟩,rfl⟩))
    · exact ⟨0,a,le_rfl,by positivity,by simp⟩
    · rw [ha]
      ext <;> simp [embed]

/-- RC05 exact integer collar and finite anchor hull. -/
theorem enlargement_integer_collar {v w : Lattice} (P : Region v w) (n : ℕ) :
    (∃ endpoint : ℕ → Lattice, ∀ j : ℕ, 0 < j → j ≤ n →
      det w (endpoint j) = det w P.secondAnchor - (j : ℤ) ∧
      ∀ z : Lattice, det w z = det w P.secondAnchor - (j : ℤ) →
        (z ∈ P.enlargement n ↔ ∃ a : ℕ, z = endpoint j + (a : ℤ) • w)) ∧
    (∃ G : Finset Lattice, (G : Set Lattice) ⊆ P.enlargement n ∧
      P.enlargement n = embed ⁻¹' finiteRayHull G (-v) w) := by
  obtain ⟨endpoint, hend⟩ := eg_collar_endpoint_family P n
  obtain ⟨G,hG,hEq⟩ := eg_finite_collar_hull P n
  exact ⟨⟨endpoint,hend⟩,⟨G,hG,hEq⟩⟩

end
end ConvexNivat.Colle
