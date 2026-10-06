import ConvexNivat.Colle.Shared.RegionCore
import ConvexNivat.Colle.Shared.RowCoordinates
import ConvexNivat.Geometry.Basic
import ConvexNivat.Colle.RegionArcCompatibility
import ConvexNivat.Colle.Shared.Sweeps

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

private theorem row_mem (S : Finset Lattice) (u a : Lattice) :
    a ∈ supportRow S u ↔ a ∈ S ∧ ∀ z ∈ S, det u a ≤ det u z := by
  simp only [supportRow,supportFace,Finset.mem_filter,normal_height]
  constructor
  · rintro ⟨ha,hh⟩
    refine ⟨ha,?_⟩
    intro z hz
    exact_mod_cast hh z hz
  · rintro ⟨ha,hh⟩
    refine ⟨ha,?_⟩
    intro z hz
    exact_mod_cast hh z hz

private theorem support_det_nonneg {S : Finset Lattice} {u a z : Lattice}
    (ha : a ∈ supportRow S u) (hz : z ∈ S) : 0 ≤ det u (z-a) := by
  have hh := ((row_mem S u a).mp ha).2 z hz
  have he : det u (z-a)=det u z-det u a := by simp [det]; ring
  rw [he]
  omega

private theorem support_pair_forbids_middle {S : Finset Lattice} {u v w a : Lattice}
    (hu : a ∈ supportRow S u) (hv : a ∈ supportRow S v)
    (huv : 0 < det u v) (huw : 0 < det u w) (hwv : 0 < det w v) :
    w ∉ edgeDirections S := by
  intro hw
  have hz_eq : ∀ z ∈ supportRow S w, z=a := by
    intro z hz
    have hzS := ((row_mem S w z).mp hz).1
    have hu0 := support_det_nonneg hu hzS
    have hv0 := support_det_nonneg hv hzS
    have hw0 : det w (z-a) ≤ 0 := by
      have hh := ((row_mem S w z).mp hz).2 a ((row_mem S u a).mp hu).1
      have he : det w (z-a)=det w z-det w a := by simp [det]; ring
      rw [he]
      omega
    have hid : det u v * det w (z-a) =
        det w v * det u (z-a)+det u w * det v (z-a) := by simp [det]; ring
    have huz : det u (z-a)=0 := by nlinarith [mul_nonneg huw.le hv0]
    have hvz : det v (z-a)=0 := by nlinarith [mul_nonneg hwv.le hu0]
    have hcoord1 : det u v * (z-a).1 =
        v.1 * det u (z-a)-u.1 * det v (z-a) := by simp [det]; ring
    have hcoord2 : det u v * (z-a).2 =
        v.2 * det u (z-a)-u.2 * det v (z-a) := by simp [det]; ring
    rw [huz,hvz,mul_zero,mul_zero,sub_self] at hcoord1 hcoord2
    have h1 := (mul_eq_zero.mp hcoord1).resolve_left huv.ne'
    have h2 := (mul_eq_zero.mp hcoord2).resolve_left huv.ne'
    exact sub_eq_zero.mp (Prod.ext h1 h2)
  have hcard : (supportRow S w).card ≤ 1 := Finset.card_le_one.mpr
    (fun z hz q hq => (hz_eq z hz).trans (hz_eq q hq).symm)
  have hh := hw.2.2
  omega

private theorem periodic_mod {α : Type*} (f : ℤ → α) (n : ℕ)
    (hn : 0 < n) (hf : ∀ j, f (j+(n : ℤ))=f j) (j : ℤ) : f (j % n)=f j := by
  have hp : Function.Periodic f (n : ℤ) := hf
  have h := hp.int_mul (j/(n : ℤ)) (j % (n : ℤ))
  simpa only [Int.cast_id,Int.emod_add_ediv_mul] using h.symm


private theorem cycle_direction_mem {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (j : ℤ) : C.direction j ∈ edgeDirections S := by
  have hm := C.at_least_two
  have hj0 : 0 ≤ j % (2*m : ℕ) := Int.emod_nonneg _ (by omega)
  have hjlt : j % (2*m : ℕ) < (2*m : ℕ) := Int.emod_lt_of_pos _ (by omega)
  let k : Fin (2*m) := ⟨(j % (2*m : ℕ)).toNat,(Int.toNat_lt hj0).mpr hjlt⟩
  apply (C.covers _).mpr
  refine ⟨k,?_⟩
  change C.direction ((j % (2*m : ℕ)).toNat : ℤ)=C.direction j
  rw [Int.toNat_of_nonneg hj0]
  exact periodic_mod C.direction (2*m) (by omega) (by simpa using C.direction_periodic) j

private theorem cycle_direction_inj_between {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) {i j : ℤ} (hij : i < j) (hji : j < i+2*m) :
    C.direction i ≠ C.direction j := by
  have hm := C.at_least_two
  have hmod : ∀ k : ℤ, 0 ≤ k % (2*m : ℕ) ∧ k % (2*m : ℕ) < (2*m : ℕ) := by
    intro k
    exact ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩
  let index (k : ℤ) : Fin (2*m) := ⟨(k % (2*m : ℕ)).toNat,(Int.toNat_lt (hmod k).1).mpr (hmod k).2⟩
  have he (k : ℤ) : C.direction ((index k).val : ℤ)=C.direction k := by
    change C.direction ((k % (2*m : ℕ)).toNat : ℤ)=C.direction k
    rw [Int.toNat_of_nonneg (hmod k).1]
    exact periodic_mod C.direction (2*m) (by omega) (by simpa using C.direction_periodic) k
  intro h
  have hi : index i=index j := C.distinct ((he i).trans (h.trans (he j).symm))
  have hrem : i % (2*m : ℕ)=j % (2*m : ℕ) := by
    have hv := congrArg (fun k : Fin (2*m) => (k.val : ℤ)) hi
    simpa only [index,Int.toNat_of_nonneg (hmod i).1,Int.toNat_of_nonneg (hmod j).1] using hv
  have hdvd : (2*m : ℤ) ∣ j-i := by
    apply Int.dvd_of_emod_eq_zero
    have h' := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hrem.symm
    simpa using h'
  have hpos : 0 < j-i := by omega
  have hlt : j-i < 2*m := by omega
  have hle := Int.le_of_dvd hpos hdvd
  omega


private theorem primitive_parallel_eq_or_neg (u v : Lattice)
    (hu : Primitive u) (hv : Primitive v) (hdet : det u v=0) : v=u ∨ v= -u := by
  have hz : det u 0=det u v := by simp [det] at hdet ⊢; exact hdet.symm
  obtain ⟨k,hk⟩ := (primitive_row_coordinates u hu).2.1 0 v |>.mp hz
  simp only [zero_add] at hk
  have hg : k.natAbs=1 := by
    have h := hv
    rw [hk] at h
    change Int.gcd (k*u.1) (k*u.2)=1 at h
    rw [Int.gcd_mul_left,show Int.gcd u.1 u.2=1 from hu,mul_one] at h
    exact h
  have hkpm : k=1 ∨ k= -1 := by omega
  rcases hkpm with h | h
  · left; simpa [h] using hk
  · right; simpa [h] using hk

private theorem cycle_half_det_ne_zero {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) {i j : ℤ} (hij : i < j) (hji : j < i+m) :
    det (C.direction i) (C.direction j) ≠ 0 := by
  have hm := C.at_least_two
  intro hzero
  rcases primitive_parallel_eq_or_neg _ _ (C.primitive i) (C.primitive j) hzero with he | he
  · exact cycle_direction_inj_between C hij (by omega) he.symm
  · have hianti : C.direction j=C.direction (i+m) := by rw [C.antipodal]; exact he
    exact cycle_direction_inj_between C hji (by omega) hianti

private theorem cycle_turn_positive {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) :
    0 < det (C.direction i) (C.direction (i+1)) := by
  have hm := C.at_least_two
  have hn := support_det_nonneg (C.terminal_mem i)
    (((row_mem S _ _).mp (C.terminal_mem (i+1))).1)
  obtain ⟨k,hk,hedge⟩ := C.edge_length (i+1)
  rw [hedge] at hn
  have he : det (C.direction i) (k • C.direction (i+1)) =
      k * det (C.direction i) (C.direction (i+1)) := by simp [det]; ring
  rw [he] at hn
  have hnon : 0 ≤ det (C.direction i) (C.direction (i+1)) := by nlinarith
  exact lt_of_le_of_ne hnon (Ne.symm (cycle_half_det_ne_zero C (by omega) (by omega)))

private theorem cycle_nat_half_order {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (n : ℕ) (hn : 0 < n) (hnm : n < m) :
    0 < det (C.direction i) (C.direction (i+n)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n
      simpa using cycle_turn_positive C i
    have hprev := ih (by omega) (by omega)
    have hnext := cycle_turn_positive C (i+n)
    have hne : det (C.direction i) (C.direction (i+(n+1 : ℕ))) ≠ 0 :=
      cycle_half_det_ne_zero C (by omega) (by exact_mod_cast (show (i : ℤ)+(n+1 : ℕ) < i+m by omega))
    by_contra! hnon
    have hneg : det (C.direction i) (C.direction (i+(n+1 : ℕ))) < 0 :=
      lt_of_le_of_ne hnon hne
    have h1 : 0 < det (C.direction (i+n)) (C.direction (i+m)) := by
      rw [C.antipodal]
      have he : det (C.direction (i+n)) (-C.direction i)=
          det (C.direction i) (C.direction (i+n)) := by simp [det]; ring
      rw [he]
      exact hprev
    have h2 : 0 < det (C.direction (i+m)) (C.direction (i+(n+1 : ℕ))) := by
      rw [C.antipodal]
      have he : det (-C.direction i) (C.direction (i+(n+1 : ℕ))) =
          -det (C.direction i) (C.direction (i+(n+1 : ℕ))) := by simp [det]; ring
      rw [he]
      omega
    have hforbid := support_pair_forbids_middle (C.terminal_mem (i+n))
      (C.initial_mem (i+n+1)) hnext h1
      (by simpa [Nat.cast_add,Nat.cast_one,add_assoc] using h2)
    exact hforbid (cycle_direction_mem C (i+m))

private theorem cycle_half_order {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i j : ℤ) (hij : i < j) (hji : j < i+m) :
    0 < det (C.direction i) (C.direction j) := by
  have h := cycle_nat_half_order C i (j-i).toNat (by omega) (by omega)
  have hj : i+((j-i).toNat : ℤ)=j := by omega
  rwa [hj] at h


private theorem cycle_row_length {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S) (j : ℤ)
    (n : ℤ) (hn : 0 ≤ n)
    (he : C.vertex (j + 1) - C.vertex j = n • C.direction j) :
    ((supportRow S (C.direction j)).card : ℤ) = n + 1 := by
  classical
  have hev : C.vertex (j + 1) = C.vertex j + n • C.direction j := by
    exact sub_eq_iff_eq_add.mp he |>.trans (add_comm _ _)
  let f : ℤ → Lattice := fun k => C.vertex j + k • C.direction j
  have hinj : Function.Injective f := by
    intro a b hab
    have hs : (a - b) • C.direction j = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr (add_left_cancel hab)
    have hv := primitive_ne_zero _ (C.primitive j)
    by_cases h₁ : (C.direction j).1 = 0
    · have h₂ : (C.direction j).2 ≠ 0 := fun hh => hv (Prod.ext h₁ hh)
      have hs₂ : (a - b) * (C.direction j).2 = 0 := congrArg Prod.snd hs
      exact sub_eq_zero.mp ((mul_eq_zero.mp hs₂).resolve_right h₂)
    · have hs₁ : (a - b) * (C.direction j).1 = 0 := congrArg Prod.fst hs
      exact sub_eq_zero.mp ((mul_eq_zero.mp hs₁).resolve_right h₁)
  have hset : supportRow S (C.direction j) = (Finset.Icc 0 n).image f := by
    ext z
    rw [C.support_segment j, hev]
    have hseg := (primitive_row_coordinates (C.direction j) (C.primitive j)).2.2
      (C.vertex j) 0 n hn z
    simp only [zero_smul, add_zero] at hseg
    constructor
    · rintro ⟨hz, hzs⟩
      obtain ⟨k, hk0, hkn, rfl⟩ := hseg.mp hzs
      exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk0, hkn⟩, rfl⟩
    · intro hz
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
      have hs : embed (f k) ∈ segment ℝ (embed (C.vertex j))
          (embed (C.vertex j + n • C.direction j)) :=
        hseg.mpr ⟨k, (Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2, rfl⟩
      refine ⟨(hS _).mp ?_, hs⟩
      apply (convex_convexHull ℝ _).segment_subset ?_ ?_ hs
      · exact (hS _).mpr (Finset.mem_filter.mp (C.initial_mem j)).1
      · rw [← hev]
        exact (hS _).mpr (Finset.mem_filter.mp (C.terminal_mem j)).1
  rw [hset, Finset.card_image_of_injective _ hinj, Int.card_Icc]
  omega



private theorem anchor_segment_encard (p d : Lattice) (hd : Primitive d)
    (L : ℤ) (hL : 0≤L) :
    {z : Lattice | embed z ∈ segment ℝ (embed p) (embed (p+L • d))}.encard =
      ((L+1).toNat : ℕ∞) := by
  classical
  let f : ℤ → Lattice := fun k => p+k • d
  have hinj : Function.Injective f := by
    intro a b h
    exact smul_left_injective ℤ (primitive_ne_zero d hd) (add_left_cancel h)
  have heq : {z : Lattice | embed z ∈ segment ℝ (embed p) (embed (p+L • d))} =
      ((Finset.Icc (0 : ℤ) L).image f : Set Lattice) := by
    ext z
    have h := (primitive_row_coordinates d hd).2.2 p 0 L hL z
    simpa [Finset.mem_image,Finset.mem_Icc,f,eq_comm,and_assoc] using h
  rw [heq,Set.encard_coe_eq_coe_finsetCard,Finset.card_image_of_injective _ hinj,
    Int.card_Icc]
  simp

private theorem weak_arc_edge_length_dominates
    {S : Finset Lattice} {m : ℕ} (C : AntipodalEdgeCycle S m)
    (hconvex : LatticeConvex S) {i J : ℤ} {v w : Lattice}
    (P : Region v w) (hweak : WeaklyEnveloped S P)
    (harc : RegionCompleteArc C i J P) (r : Fin P.boundedCount)
    (ls lp : ℤ) (hls : 1 ≤ ls) (hlp : 1 ≤ lp)
    (hs : C.vertex (i + 1 + (r.val : ℤ) + 1) -
      C.vertex (i + 1 + (r.val : ℤ)) =
        ls • C.direction (i + 1 + (r.val : ℤ)))
    (hp : P.vertex r.succ - P.vertex r.castSucc =
      lp • P.boundedDirection r) : ls ≤ lp := by
  have hcard := cycle_row_length C hconvex (i+1+(r.val : ℤ)) ls (by omega) hs
  have hedge : P.vertex r.succ=P.vertex r.castSucc+lp • P.boundedDirection r :=
    (sub_eq_iff_eq_add.mp hp).trans (add_comm _ _)
  have hbound := (hweak (P.boundedDirection r)
    {z | embed z ∈ segment ℝ (embed (P.vertex r.castSucc)) (embed (P.vertex r.succ))}
    (Or.inr (Or.inr ⟨r,rfl,rfl⟩))).2
  rw [hedge,anchor_segment_encard _ _ (P.bounded_primitive r) lp (by omega),
    harc.ordered_directions] at hbound
  have hh : (supportRow S (C.direction (i+1+(r.val : ℤ)))).card≤(lp+1).toNat := by
    exact_mod_cast hbound
  omega


private theorem anchor_residual_step
    {S : Finset Lattice} {m : ℕ} (C : AntipodalEdgeCycle S m)
    (hconvex : LatticeConvex S) {i J : ℤ} {v w : Lattice}
    (P : Region v w) (hweak : WeaklyEnveloped S P)
    (harc : RegionCompleteArc C i J P) (r : Fin P.boundedCount) :
    ∃ a : ℤ, 0≤a ∧
      (P.vertex r.succ-C.vertex (i+1+(r.succ.val : ℤ))) -
        (P.vertex r.castSucc-C.vertex (i+1+(r.castSucc.val : ℤ))) =
        a • C.direction (i+1+(r.val : ℤ)) := by
  obtain ⟨ls,hls,hs⟩ := C.edge_length (i+1+(r.val : ℤ))
  obtain ⟨lp,hlp,hp⟩ := P.bounded_length r
  have hle := weak_arc_edge_length_dominates C hconvex P hweak harc r ls lp hls hlp hs hp
  refine ⟨lp-ls,by omega,?_⟩
  rw [harc.ordered_directions] at hp
  have he : i+1+(r.succ.val : ℤ)=i+1+(r.val : ℤ)+1 := by simp; ring
  rw [he]
  change (P.vertex r.succ-C.vertex (i+1+(r.val : ℤ)+1)) -
    (P.vertex r.castSucc-C.vertex (i+1+(r.val : ℤ))) = _
  calc
    _ = (P.vertex r.succ-P.vertex r.castSucc) -
        (C.vertex (i+1+(r.val : ℤ)+1)-C.vertex (i+1+(r.val : ℤ))) := by abel
    _ = _ := by rw [hp,hs,sub_smul]

private theorem anchor_residual_support
    {S : Finset Lattice} {m : ℕ} (C : AntipodalEdgeCycle S m)
    (hconvex : LatticeConvex S) {i J : ℤ} {v w : Lattice}
    (P : Region v w) (hweak : WeaklyEnveloped S P)
    (harc : RegionCompleteArc C i J P)
    (j : ℤ) (hj : i ≤ j) (hjJ : j < J)
    (r : Fin (P.boundedCount+1)) (hr : j ≤ i+1+(r.val : ℤ)) :
    0≤det (C.direction j)
      ((P.secondAnchor-C.vertex J)-(P.vertex r-C.vertex (i+1+(r.val : ℤ)))) := by
  let Q : Fin (P.boundedCount + 1) → Lattice :=
    fun r => P.vertex r-C.vertex (i+1+(r.val : ℤ))
  have hcount : i+1+(P.boundedCount : ℤ)=J := by
    have h := harc.bounded_count
    have hl := harc.lower
    omega
  have hlast : Q (Fin.last P.boundedCount)=P.secondAnchor-C.vertex J := by
    dsimp [Q,Region.secondAnchor]
    rw [hcount]
    rfl
  have hstep (r : Fin P.boundedCount) (hr : j ≤ i+1+(r.val : ℤ)) :
      det (C.direction j) (Q r.castSucc)≤det (C.direction j) (Q r.succ) := by
    obtain ⟨a,ha,he⟩ := anchor_residual_step C hconvex P hweak harc r
    have hd : 0≤det (C.direction j) (C.direction (i+1+(r.val : ℤ))) := by
      by_cases heq : j=i+1+(r.val : ℤ)
      · rw [← heq]; simp [det,mul_comm]
      · apply (cycle_half_order C j (i+1+(r.val : ℤ)) (by omega) ?_).le
        have hu := harc.upper
        have hri := r.isLt
        omega
    have hh : det (C.direction j) (Q r.succ)-det (C.direction j) (Q r.castSucc) =
        a*det (C.direction j) (C.direction (i+1+(r.val : ℤ))) := by
      calc
        _ = det (C.direction j) (Q r.succ-Q r.castSucc) := by simp [det]; ring
        _ = _ := by change det _ (_-_) = _; rw [he]; simp [det]; ring
    have hnon := mul_nonneg ha hd
    omega
  have hle : ∀ r : Fin (P.boundedCount+1), j ≤ i+1+(r.val : ℤ) →
      det (C.direction j) (Q r)≤det (C.direction j) (Q (Fin.last P.boundedCount)) := by
    intro r
    induction r using Fin.reverseInduction with
    | last => intro _; exact le_rfl
    | cast r ih =>
      intro hr
      exact (hstep r hr).trans (ih (by simp only [Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one] at hr ⊢; omega))
  have hh := hle r hr
  rw [hlast] at hh
  have he : det (C.direction j)
      ((P.secondAnchor-C.vertex J)-(P.vertex r-C.vertex (i+1+(r.val : ℤ)))) =
      det (C.direction j) (P.secondAnchor-C.vertex J)-det (C.direction j) (Q r) := by
    dsimp [Q,det]; ring
  rw [he]
  omega

private theorem terminal_anchor_source_fit
    {S : Finset Lattice} {m : ℕ} (C : AntipodalEdgeCycle S m)
    (hconvex : LatticeConvex S) {i J : ℤ} {v w : Lattice}
    (P : Region v w) (hweak : WeaklyEnveloped S P)
    (harc : RegionCompleteArc C i J P) :
    (windowTranslate S (P.secondAnchor - C.vertex J) : Set Lattice) ⊆ P.lattice := by
  intro z hz
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  change embed (q+(P.secondAnchor-C.vertex J)) ∈ P.carrier
  rw [(region_halfplane_representation P).1]
  change 0≤realDet (embed v) (embed (q+(P.secondAnchor-C.vertex J))-embed P.firstAnchor) ∧
    0≤realDet (embed w) (embed (q+(P.secondAnchor-C.vertex J))-embed P.secondAnchor) ∧
    ∀ r, 0≤realDet (embed (P.boundedDirection r))
      (embed (q+(P.secondAnchor-C.vertex J))-embed (P.vertex r.castSucc))
  have hcast (d a : Lattice) (hh : 0≤det d (q+(P.secondAnchor-C.vertex J)-a)) :
      0≤realDet (embed d) (embed (q+(P.secondAnchor-C.vertex J))-embed a) := by
    have he : realDet (embed d) (embed (q+(P.secondAnchor-C.vertex J))-embed a) =
        (det d (q+(P.secondAnchor-C.vertex J)-a) : ℝ) := by simp [realDet,embed,det]
    rw [he]
    exact_mod_cast hh
  refine ⟨hcast v P.firstAnchor ?_,hcast w P.secondAnchor ?_,?_⟩
  · conv_rhs => arg 1; rw [harc.first_ray]
    have hs := support_det_nonneg (C.terminal_mem i) hq
    have hr := anchor_residual_support C hconvex P hweak harc i (le_refl i)
      (by have h := harc.lower; omega) 0 (by simp)
    have he : det (C.direction i) (q+(P.secondAnchor-C.vertex J)-P.firstAnchor) =
        det (C.direction i) (q-C.vertex (i+1))+
        det (C.direction i) ((P.secondAnchor-C.vertex J)-(P.firstAnchor-C.vertex (i+1))) := by
      simp [det]; ring
    rw [he]
    simpa [Region.firstAnchor] using add_nonneg hs hr
  · conv_rhs => arg 1; rw [harc.second_ray]
    have hs := support_det_nonneg (C.initial_mem J) hq
    simpa only [show q+(P.secondAnchor-C.vertex J)-P.secondAnchor=q-C.vertex J by abel] using hs
  · intro r
    apply hcast
    rw [harc.ordered_directions]
    let j : ℤ := i+1+(r.val : ℤ)
    have hj : i ≤ j := by dsimp [j]; omega
    have hjJ : j < J := by
      have hcount := harc.bounded_count
      have hlo := harc.lower
      have hr := r.isLt
      dsimp [j]; omega
    have hs := support_det_nonneg (C.initial_mem j) hq
    have hr := anchor_residual_support C hconvex P hweak harc j hj hjJ r.castSucc (by rfl)
    have he : det (C.direction j) (q+(P.secondAnchor-C.vertex J)-P.vertex r.castSucc) =
        det (C.direction j) (q-C.vertex j)+
        det (C.direction j) ((P.secondAnchor-C.vertex J)-(P.vertex r.castSucc-C.vertex j)) := by
      simp [det]; ring
    rw [he]
    exact add_nonneg hs hr

private theorem gp_vertex_strict_min (S : Finset Lattice) (hc : LatticeConvex S)
    (a : Lattice) (ha : a ∈ S) (f : RealPlane → ℝ) (hf : IsLinearMap ℝ f)
    (hmin : ∀ z ∈ S.erase a, f (embed a) < f (embed z)) : WindowVertex S a := by
  refine ⟨ha, fun z => ⟨?_, ?_⟩⟩
  · intro hz
    have hsub : windowHull (S.erase a) ⊆ windowHull S :=
      convexHull_mono (Set.image_mono (Finset.erase_subset a S))
    have hbound : windowHull (S.erase a) ⊆ {x | f (embed a) < f x} := by
      apply convexHull_min _ (convex_halfSpace_gt hf _)
      rintro _ ⟨q, hq, rfl⟩
      exact hmin q hq
    refine Finset.mem_erase.mpr ⟨?_, (hc z).mp (hsub hz)⟩
    intro heq
    have hlt := hbound hz
    simpa [heq] using hlt
  · intro hz
    exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩


private theorem gp_vertex_secondary (S : Finset Lattice) (hc : LatticeConvex S)
    (v u a : Lattice) (ha : a ∈ supportRow S v)
    (htie : ∀ q ∈ S.erase a, det v q = det v a → det u a < det u q) :
    WindowVertex S a := by
  classical
  let M : ℕ := 1 + ∑ q ∈ S, (det u q - det u a).natAbs
  let f : RealPlane → ℝ := fun x => (M : ℝ) * realDet (embed v) x + realDet (embed u) x
  have hf : IsLinearMap ℝ f := by
    constructor <;> intro x y <;> simp [f, realDet] <;> ring
  have heval : ∀ z, f (embed z) = (M : ℝ) * (det v z : ℝ) + (det u z : ℝ) := by
    intro z
    simp [f, realDet, embed, det]
  apply gp_vertex_strict_min S hc a (Finset.mem_filter.mp ha).1 f hf
  intro q hq
  have hqS : q ∈ S := Finset.mem_of_mem_erase hq
  have hle : det v a ≤ det v q := by
    have h := (Finset.mem_filter.mp ha).2 q hqS
    rw [normal_height, normal_height] at h
    exact_mod_cast h
  have hpos : 0 < (M : ℤ) * (det v q - det v a) + (det u q - det u a) := by
    by_cases he : det v q = det v a
    · have hh := htie q hq he
      rw [he, sub_self, mul_zero, zero_add]
      omega
    · have hgap : (1 : ℤ) ≤ det v q - det v a := by omega
      have hsum : (det u q - det u a).natAbs ≤ ∑ r ∈ S, (det u r - det u a).natAbs :=
        Finset.single_le_sum (f := fun r : Lattice => (det u r - det u a).natAbs)
          (fun _ _ => Nat.zero_le _) hqS
      have hM : (det u q - det u a).natAbs < M := by dsimp [M]; omega
      have hMc : ((det u q - det u a).natAbs : ℤ) < M := by exact_mod_cast hM
      have hneg := Int.le_natAbs (a := -(det u q - det u a))
      simp only [Int.natAbs_neg] at hneg
      have hmul := mul_le_mul_of_nonneg_left hgap (Int.natCast_nonneg M)
      nlinarith
  have hreal : 0 < (M : ℝ) * ((det v q : ℝ) - det v a) + ((det u q : ℝ) - det u a) := by
    exact_mod_cast hpos
  rw [heval, heval]
  nlinarith



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


private theorem enlargement_new_row {v w : Lattice} (P : Region v w)
    (n : ℕ) {z : Lattice} (hz : z ∈ P.enlargement (n + 1))
    (hnot : z ∉ P.enlargement n) :
    det w z = det w P.secondAnchor - ((n : ℤ) + 1) := by
  obtain ⟨g, hg, t, hzt, hbounds⟩ := hz
  rcases hbounds with hinside | ⟨hlo, hhi⟩
  · exact False.elim (hnot ⟨g, hg, t, hzt, Or.inl hinside⟩)
  · have hlow : ¬ det w P.secondAnchor - (n : ℤ) ≤ det w z := by
      intro h
      exact hnot ⟨g, hg, t, hzt, Or.inr ⟨h, hhi⟩⟩
    push_cast at hlo
    omega

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


private theorem enlargement_new_row_iff {v w : Lattice} (P : Region v w)
    (n : ℕ) (z : Lattice) :
    (z ∈ P.enlargement (n + 1) ∧ z ∉ P.enlargement n) ↔
      det w z = det w P.secondAnchor - ((n : ℤ) + 1) ∧
      det P.predecessor P.secondAnchor ≤ det P.predecessor z := by
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨enlargement_new_row P n hz hn,
      eg_enlargement_predecessor_support P (n + 1) z hz⟩
  · rintro ⟨he, hs⟩
    constructor
    · apply eg_outside_mem P (n + 1) z <;> first | exact hs | omega
    · intro hz
      have hlo := eg_enlargement_lower P n z hz
      omega

private theorem enlargement_new_row_ray {v w : Lattice} (P : Region v w)
    (n : ℕ) :
    ∃ p : Lattice,
      (∀ z : Lattice, (z ∈ P.enlargement (n + 1) ∧ z ∉ P.enlargement n) ↔
        ∃ k : ℕ, z = p + (k : ℤ) • w) ∧
      det P.predecessor P.secondAnchor ≤ det P.predecessor p := by
  obtain ⟨p, hp, hray⟩ := eg_integer_row_ray P.predecessor w P.second_primitive
    (eg_predecessor_turn P) (det w P.secondAnchor - ((n : ℤ) + 1))
    (det P.predecessor P.secondAnchor)
  have hps := (hray p hp).mpr ⟨0, by simp⟩
  refine ⟨p, ?_, hps⟩
  intro z
  rw [enlargement_new_row_iff]
  constructor
  · rintro ⟨hz, hzs⟩
    exact (hray z hz).mp hzs
  · rintro ⟨k, rfl⟩
    have hz : det w (p + (k : ℤ) • w) =
        det w P.secondAnchor - ((n : ℤ) + 1) := by
      rw [eg_det_add, eg_det_smul, eg_det_self, mul_zero, add_zero, hp]
    exact ⟨hz, (hray _ hz).mpr ⟨k, rfl⟩⟩

private theorem sweep_known_point {S : Finset Lattice} {U : Set Lattice}
    {z : Lattice} (hz : z ∈ U) : HasFiniteSweep S U {z} := by
  exact ⟨[], .nil U, by simpa only [Finset.coe_singleton, Set.singleton_subset_iff]⟩

private theorem sweep_ray_from_block (S : Finset Lattice) (U : Set Lattice)
    (x : ℕ → Lattice) (ell t : ℕ) (hell : 1 ≤ ell) (a b : Lattice)
    (ha : WindowVertex S a) (hb : WindowVertex S b)
    (hseed : ∀ j < ell, x (t + j) ∈ U)
    (hback : ∀ k : ℕ, ∀ q ∈ S.erase a,
      x k + (q - a) ∈ U ∨ ∃ r : ℕ, 0 < r ∧ r ≤ ell ∧
        x k + (q - a) = x (k + r))
    (hforward : ∀ k : ℕ, ell ≤ k → ∀ q ∈ S.erase b,
      x k + (q - b) ∈ U ∨ ∃ r : ℕ, 0 < r ∧ r ≤ ell ∧
        x k + (q - b) = x (k - r)) :
    ∀ k : ℕ, HasFiniteSweep S U {x k} := by
  have hprefix : ∀ d : ℕ, ∀ k : ℕ, t - k = d → k < t + ell →
      HasFiniteSweep S U {x k} := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro k hkd hkb
      by_cases htk : t ≤ k
      · have he : t + (k - t) = k := by omega
        exact sweep_known_point (he ▸ hseed (k - t) (by omega))
      · have hstep := sweep_one_step (S := S) (U := U) (x k - a) a ha (by
          intro q hq
          have he : x k - a + q = x k + (q - a) := by abel
          rw [he]
          rcases hback k q hq with hold | ⟨r, hr, hre, heq⟩
          · exact sweep_known_point hold
          · rw [heq]
            apply ih (t - (k + r)) (by omega) (k + r) rfl
            omega)
        simpa using hstep
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hkb : k < t + ell
    · exact hprefix (t - k) k rfl hkb
    · have hstep := sweep_one_step (S := S) (U := U) (x k - b) b hb (by
        intro q hq
        have he : x k - b + q = x k + (q - b) := by abel
        rw [he]
        rcases hforward k (by omega) q hq with hold | ⟨r, hr, hre, heq⟩
        · exact sweep_known_point hold
        · rw [heq]
          exact ih (k - r) (by omega))
      simpa using hstep

private theorem finite_row_run_square (p w : Lattice) (ell : ℕ) :
    ∃ R : ℕ, ∀ j < ell, p + (j : ℤ) • w ∈ integerSquare R := by
  classical
  let K := (Finset.range ell).image (fun j : ℕ => p + (j : ℤ) • w)
  let R := K.sup (fun z => max z.1.natAbs z.2.natAbs)
  refine ⟨R, ?_⟩
  intro j hj
  let z := p + (j : ℤ) • w
  have hz : z ∈ K := Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  have hm : max z.1.natAbs z.2.natAbs ≤ R := Finset.le_sup (f := fun z : Lattice => max z.1.natAbs z.2.natAbs) hz
  have h1 : z.1.natAbs ≤ R := (le_max_left _ _).trans hm
  have h2 : z.2.natAbs ≤ R := (le_max_right _ _).trans hm
  have ha : |z.1| ≤ (R : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h1
  have hb : |z.2| ≤ (R : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h2
  change z ∈ integerSquare R
  simpa only [integerSquare, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc] using And.intro (abs_le.mp ha) (abs_le.mp hb)

private theorem new_row_offset_old {v w : Lattice} (P : Region v w)
    (n : ℕ) (z s : Lattice)
    (hz : z ∈ P.enlargement (n + 1) ∧ z ∉ P.enlargement n)
    (hfit : P.secondAnchor + s ∈ P.lattice) (hpos : 0 < det w s) :
    z + s ∈ P.enlargement n := by
  obtain ⟨hheight, hsupp⟩ := (enlargement_new_row_iff P n z).mp hz
  let D : ℝ := det P.predecessor w
  let c : ℝ := ((n : ℝ) + 1) / D
  let b : ℝ := ((det P.predecessor z : ℝ) -
    (det P.predecessor P.secondAnchor : ℝ)) / D
  have hD : 0 < D := by dsimp [D]; exact_mod_cast eg_predecessor_turn P
  have hc : 0 ≤ c := div_nonneg (by positivity) hD.le
  have hb : 0 ≤ b := by
    apply div_nonneg _ hD.le
    exact_mod_cast sub_nonneg.mpr hsupp
  have hbase := eg_det_basis_real (embed P.predecessor) (embed w)
    (by rw [eg_real_det]; exact ne_of_gt hD) (embed z - embed P.secondAnchor)
  have hwd : realDet (embed w) (embed z - embed P.secondAnchor) = -((n : ℝ) + 1) := by
    rw [← embed_sub, eg_real_det, eg_det_sub, hheight]
    push_cast
    ring
  have hdd : realDet (embed P.predecessor) (embed z - embed P.secondAnchor) =
      (det P.predecessor z : ℝ) - (det P.predecessor P.secondAnchor : ℝ) := by
    rw [← embed_sub, eg_real_det, eg_det_sub]
    push_cast
    rfl
  rw [hwd, hdd, eg_real_det, neg_neg] at hbase
  have heq : embed z - embed P.secondAnchor = c • embed P.predecessor + b • embed w := hbase
  let y := embed (P.secondAnchor + s) + b • embed w
  have hy : y ∈ P.carrier := by
    simpa only [zero_smul, sub_zero] using
      eg_recession_add P (embed (P.secondAnchor + s)) hfit 0 b le_rfl hb
  apply eg_continuous_enlargement_mem P n (z + s) y hy c hc
  · rw [embed_add]
    dsimp [y]
    rw [embed_add]
    linear_combination heq
  · rw [eg_real_det, eg_det_add]
    have hlow : det w P.secondAnchor - (n : ℤ) ≤ det w z + det w s := by omega
    exact_mod_cast hlow

private theorem new_row_forward {v w : Lattice} (P : Region v w)
    (n : ℕ) {z : Lattice}
    (hz : z ∈ P.enlargement (n + 1) ∧ z ∉ P.enlargement n) (r : ℕ) :
    z + (r : ℤ) • w ∈ P.enlargement (n + 1) ∧
      z + (r : ℤ) • w ∉ P.enlargement n := by
  rw [enlargement_new_row_iff] at hz ⊢
  rw [eg_det_add, eg_det_smul, eg_det_self, mul_zero, add_zero,
    eg_det_add, eg_det_smul]
  exact ⟨hz.1, hz.2.trans (le_add_of_nonneg_right
    (mul_nonneg (Int.natCast_nonneg r) (eg_predecessor_turn P).le))⟩

private theorem new_row_backward {v w : Lattice} (P : Region v w)
    (n ell : ℕ) {z : Lattice}
    (hz : z ∈ P.enlargement (n + 1) ∧ z ∉ P.enlargement n)
    (hroom : det P.predecessor P.secondAnchor + (ell : ℤ) * det P.predecessor w ≤
      det P.predecessor z) (r : ℕ) (hr : r ≤ ell) :
    z - (r : ℤ) • w ∈ P.enlargement (n + 1) ∧
      z - (r : ℤ) • w ∉ P.enlargement n := by
  rw [enlargement_new_row_iff] at hz ⊢
  rw [eg_det_sub, eg_det_smul, eg_det_self, mul_zero, sub_zero,
    eg_det_sub, eg_det_smul]
  refine ⟨hz.1, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right (show (r : ℤ) ≤ ell by exact_mod_cast hr)
    (eg_predecessor_turn P).le
  omega

private theorem arc_row_mem (S : Finset Lattice) (w a : Lattice) :
    a ∈ supportRow S w ↔ a ∈ S ∧ ∀ z ∈ S, det w a ≤ det w z := by
  have hnormal (z : Lattice) : realDot (embed z) (normal w) = (det w z : ℝ) := by
    simp [realDot, normal, embed, det]
    ring
  simp only [supportRow, supportFace, Finset.mem_filter, hnormal]
  constructor
  · rintro ⟨ha, hh⟩
    exact ⟨ha, fun z hz => by exact_mod_cast hh z hz⟩
  · rintro ⟨ha, hh⟩
    exact ⟨ha, fun z hz => by exact_mod_cast hh z hz⟩

private theorem initial_placement_from_fit {v w : Lattice} (P : Region v w)
    (S : Finset Lattice) (a : Lattice) (ell n : ℕ)
    (ha : a ∈ supportRow S w)
    (hrun : ∀ q ∈ supportRow S w, ∃ r : ℕ, r ≤ ell ∧ q = a + (r : ℤ) • w)
    (hfit : (windowTranslate S (P.secondAnchor - a) : Set Lattice) ⊆ P.lattice)
    (z : Lattice) (hz : z ∈ P.enlargement (n + 1) ∧ z ∉ P.enlargement n) :
    ∀ q ∈ S.erase a,
      z + (q - a) ∈ P.enlargement n ∨
      ∃ r : ℕ, 0 < r ∧ r ≤ ell ∧ q - a = (r : ℤ) • w ∧
        z + (r : ℤ) • w ∈ P.enlargement (n + 1) ∧
        z + (r : ℤ) • w ∉ P.enlargement n := by
  intro q hq
  have hqS := Finset.mem_of_mem_erase hq
  have hlow := ((arc_row_mem S w a).mp ha).2 q hqS
  by_cases he : det w q = det w a
  · have hqrow : q ∈ supportRow S w := (arc_row_mem S w q).mpr
      ⟨hqS, fun r hr => he ▸ ((arc_row_mem S w a).mp ha).2 r hr⟩
    obtain ⟨r, hr, hqr⟩ := hrun q hqrow
    have hrpos : 0 < r := by
      by_contra hn
      have hzero : r = 0 := by omega
      exact (Finset.mem_erase.mp hq).1 (by simpa [hzero] using hqr)
    exact Or.inr ⟨r, hrpos, hr, by rw [hqr]; abel, new_row_forward P n hz r⟩
  · left
    apply new_row_offset_old P n z (q - a) hz
    · apply hfit
      apply Finset.mem_image.mpr
      exact ⟨q, hqS, by abel⟩
    · rw [eg_det_sub]
      omega

private theorem terminal_placement_from_fit {v w : Lattice} (P : Region v w)
    (S : Finset Lattice) (a b : Lattice) (ell n : ℕ)
    (ha : a ∈ supportRow S w) (hedge : b = a + (ell : ℤ) • w)
    (hrun : ∀ q ∈ supportRow S w, ∃ r : ℕ, r ≤ ell ∧ q = a + (r : ℤ) • w)
    (hfit : (windowTranslate S (P.secondAnchor - a) : Set Lattice) ⊆ P.lattice)
    (z : Lattice) (hz : z ∈ P.enlargement (n + 1) ∧ z ∉ P.enlargement n)
    (hroom : det P.predecessor P.secondAnchor + (ell : ℤ) * det P.predecessor w ≤
      det P.predecessor z) :
    ∀ q ∈ S.erase b,
      z + (q - b) ∈ P.enlargement n ∨
      ∃ r : ℕ, 0 < r ∧ r ≤ ell ∧ q - b = -((r : ℤ) • w) ∧
        z - (r : ℤ) • w ∈ P.enlargement (n + 1) ∧
        z - (r : ℤ) • w ∉ P.enlargement n := by
  intro q hq
  have hqS := Finset.mem_of_mem_erase hq
  have hlow := ((arc_row_mem S w a).mp ha).2 q hqS
  by_cases he : det w q = det w a
  · have hqrow : q ∈ supportRow S w := (arc_row_mem S w q).mpr
      ⟨hqS, fun r hr => he ▸ ((arc_row_mem S w a).mp ha).2 r hr⟩
    obtain ⟨r, hr, hqr⟩ := hrun q hqrow
    have hrlt : r < ell := by
      by_contra hn
      have heq : r = ell := by omega
      exact (Finset.mem_erase.mp hq).1 (hqr.trans (by rw [heq, hedge]))
    refine Or.inr ⟨ell - r, by omega, by omega, ?_,
      new_row_backward P n ell hz hroom (ell - r) (by omega)⟩
    rw [hedge, hqr, Nat.cast_sub hr, sub_smul]
    abel
  · left
    have hzb := new_row_backward P n ell hz hroom ell le_rfl
    have hqfit : P.secondAnchor + (q - a) ∈ P.lattice := by
      apply hfit
      exact Finset.mem_image.mpr ⟨q, hqS, by abel⟩
    have hh := new_row_offset_old P n (z - (ell : ℤ) • w) (q - a) hzb hqfit
      (by rw [eg_det_sub]; omega)
    convert hh using 1
    rw [hedge]
    abel

private theorem finite_seed_sweep_from_fit {v w : Lattice} (P : Region v w)
    (S : Finset Lattice) (a b : Lattice) (ell : ℕ) (hell : 1 ≤ ell)
    (ha : WindowVertex S a) (hb : WindowVertex S b)
    (harow : a ∈ supportRow S w) (hedge : b = a + (ell : ℤ) • w)
    (hrun : ∀ q ∈ supportRow S w, ∃ r : ℕ, r ≤ ell ∧ q = a + (r : ℤ) • w)
    (hfit : (windowTranslate S (P.secondAnchor - a) : Set Lattice) ⊆ P.lattice)
    (n : ℕ) : ∃ R : ℕ, ∀ t : ℕ, ∀ F : Finset Lattice,
      (F : Set Lattice) ⊆ P.enlargement (n + 1) →
        HasFiniteSweep S (regionalSeed P n R t) F := by
  obtain ⟨p, hray, hpsupp⟩ := enlargement_new_row_ray P n
  obtain ⟨R, hR⟩ := finite_row_run_square p w ell
  refine ⟨R, ?_⟩
  intro t F hF
  let U := regionalSeed P n R t
  let x : ℕ → Lattice := fun k => p + (k : ℤ) • w
  have hx (k : ℕ) : x k ∈ P.enlargement (n + 1) ∧ x k ∉ P.enlargement n :=
    (hray (x k)).mpr ⟨k, rfl⟩
  have hold (z : Lattice) (hz : z ∈ P.enlargement n) : z ∈ U := Or.inl hz
  have hseed : ∀ j < ell, x (t + j) ∈ U := by
    intro j hj
    apply Or.inr
    refine ⟨(hx _).1, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨p + (j : ℤ) • w, hR j hj, ?_⟩
    dsimp [x]
    simp only [Nat.cast_add, add_smul]
    abel
  have hback : ∀ k : ℕ, ∀ q ∈ S.erase a,
      x k + (q - a) ∈ U ∨ ∃ r : ℕ, 0 < r ∧ r ≤ ell ∧
        x k + (q - a) = x (k + r) := by
    intro k q hq
    rcases initial_placement_from_fit P S a ell n harow hrun hfit (x k) (hx k) q hq
      with old | ⟨r, hr, hre, heq, _⟩
    · exact Or.inl (hold _ old)
    · refine Or.inr ⟨r, hr, hre, ?_⟩
      rw [heq]
      dsimp [x]
      simp only [Nat.cast_add, add_smul]
      abel
  have hfwd : ∀ k : ℕ, ell ≤ k → ∀ q ∈ S.erase b,
      x k + (q - b) ∈ U ∨ ∃ r : ℕ, 0 < r ∧ r ≤ ell ∧
        x k + (q - b) = x (k - r) := by
    intro k hk q hq
    have hroom : det P.predecessor P.secondAnchor + (ell : ℤ) * det P.predecessor w ≤
        det P.predecessor (x k) := by
      change _ ≤ det P.predecessor (p + (k : ℤ) • w)
      rw [eg_det_add, eg_det_smul]
      have hmul := mul_le_mul_of_nonneg_right (show (ell : ℤ) ≤ k by exact_mod_cast hk)
        (eg_predecessor_turn P).le
      omega
    rcases terminal_placement_from_fit P S a b ell n harow hedge hrun hfit
      (x k) (hx k) hroom q hq with old | ⟨r, hr, hre, heq, _⟩
    · exact Or.inl (hold _ old)
    · refine Or.inr ⟨r, hr, hre, ?_⟩
      rw [heq]
      dsimp [x]
      rw [Nat.cast_sub (hre.trans hk), sub_smul]
      abel
  have hsweep := sweep_ray_from_block S U x ell t hell a b ha hb hseed hback hfwd
  apply sweep_of_points
  intro z hz
  by_cases holdz : z ∈ P.enlargement n
  · exact sweep_known_point (hold z holdz)
  · obtain ⟨k, rfl⟩ := (hray z).mp ⟨hF hz, holdz⟩
    exact hsweep k

private theorem cycle_edge_generated_run {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hconvex : LatticeConvex S) (J : ℤ) :
    ∃ ell : ℕ, 1 ≤ ell ∧
      C.vertex (J + 1) = C.vertex J + (ell : ℤ) • C.direction J ∧
      (∀ q : Lattice, q ∈ supportRow S (C.direction J) ↔
        ∃ r : ℕ, r ≤ ell ∧ q = C.vertex J + (r : ℤ) • C.direction J) ∧
      WindowVertex S (C.vertex J) ∧ WindowVertex S (C.vertex (J + 1)) := by
  obtain ⟨ls, hls, hlen⟩ := C.edge_length J
  let ell := ls.toNat
  have hcast : (ell : ℤ) = ls := Int.toNat_of_nonneg (by omega)
  have hell : 1 ≤ ell := by omega
  have hedge : C.vertex (J + 1) = C.vertex J + (ell : ℤ) • C.direction J := by
    rw [hcast]
    exact (sub_eq_iff_eq_add.mp hlen).trans (add_comm _ _)
  have hrun : ∀ q : Lattice, q ∈ supportRow S (C.direction J) ↔
      ∃ r : ℕ, r ≤ ell ∧ q = C.vertex J + (r : ℤ) • C.direction J := by
    intro q
    have hseg := (primitive_row_coordinates (C.direction J) (C.primitive J)).2.2
      (C.vertex J) 0 (ell : ℤ) (by positivity) q
    simp only [zero_smul, add_zero] at hseg
    rw [C.support_segment J, hedge]
    constructor
    · rintro ⟨hq, hqseg⟩
      obtain ⟨r, hr0, hrle, hqr⟩ := hseg.mp hqseg
      refine ⟨r.toNat, by omega, ?_⟩
      simpa only [Int.toNat_of_nonneg hr0] using hqr
    · rintro ⟨r, hrle, hqr⟩
      have hqseg := hseg.mpr ⟨r, by positivity, by exact_mod_cast hrle, hqr⟩
      refine ⟨(hconvex q).mp ?_, hqseg⟩
      apply (convex_convexHull ℝ _).segment_subset ?_ ?_ hqseg
      · exact (hconvex _).mpr (Finset.mem_filter.mp (C.initial_mem J)).1
      · rw [← hedge]
        exact (hconvex _).mpr (Finset.mem_filter.mp (C.terminal_mem J)).1
  obtain ⟨u, hu⟩ := primitive_height_surjective (C.direction J) (C.primitive J) (-1)
  change det (C.direction J) u = -1 at hu
  have huw : det u (C.direction J) = 1 := by
    have he : det u (C.direction J) = -det (C.direction J) u := by dsimp [det]; ring
    rw [he, hu]; norm_num
  have ha : WindowVertex S (C.vertex J) := by
    apply gp_vertex_secondary S hconvex (C.direction J) u (C.vertex J) (C.initial_mem J)
    intro q hq he
    have hqrow : q ∈ supportRow S (C.direction J) := (arc_row_mem _ _ _).mpr
      ⟨Finset.mem_of_mem_erase hq, fun r hr => he ▸
        ((arc_row_mem _ _ _).mp (C.initial_mem J)).2 r hr⟩
    obtain ⟨r, hr, hqr⟩ := (hrun q).mp hqrow
    have hrpos : 0 < r := by
      by_contra hn
      have hzero : r = 0 := by omega
      exact (Finset.mem_erase.mp hq).1 (by simpa [hzero] using hqr)
    rw [hqr, eg_det_add, eg_det_smul, huw, mul_one]
    omega
  have hb : WindowVertex S (C.vertex (J + 1)) := by
    apply gp_vertex_secondary S hconvex (C.direction J) (-u) (C.vertex (J + 1))
      (C.terminal_mem J)
    intro q hq he
    have hqrow : q ∈ supportRow S (C.direction J) := (arc_row_mem _ _ _).mpr
      ⟨Finset.mem_of_mem_erase hq, fun r hr => he ▸
        ((arc_row_mem _ _ _).mp (C.terminal_mem J)).2 r hr⟩
    obtain ⟨r, hr, hqr⟩ := (hrun q).mp hqrow
    have hrlt : r < ell := by
      by_contra hn
      have heq : r = ell := by omega
      exact (Finset.mem_erase.mp hq).1 (hqr.trans (by rw [heq, hedge]))
    have hneg : det (-u) (C.direction J) = -1 := by
      have hh : det (-u) (C.direction J) = -det u (C.direction J) := by dsimp [det];ring
      rw [hh, huw]
    rw [hedge, hqr, eg_det_add, eg_det_add, eg_det_smul, eg_det_smul, hneg]
    omega
  exact ⟨ell, hell, hedge, hrun, ha, hb⟩

theorem enlarged_region_finite_seed_sweep (ξ : Configuration ℤ) (S : Finset Lattice)
    (hS : GeneratingSet ξ S) {v w : Lattice} (P : Region v w)
    (hweak : WeaklyEnveloped S P) (hcompat : RegionCompatibleArc S P) (n : ℕ) :
    ∃ R T : ℕ, ∀ t ≥ T, ∀ F : Finset Lattice,
      (F : Set Lattice) ⊆ P.enlargement (n + 1) → HasFiniteSweep S (regionalSeed P n R t) F := by
  obtain ⟨m, C, i, J, harc⟩ := hcompat
  obtain ⟨ell, hell, hedge, hrun, ha, hb⟩ := cycle_edge_generated_run C hS.2.1 J
  have hfit := terminal_anchor_source_fit C hS.2.1 P hweak harc
  have harow : C.vertex J ∈ supportRow S w := by
    rw [harc.second_ray]
    exact C.initial_mem J
  have hedge' : C.vertex (J + 1) = C.vertex J + (ell : ℤ) • w := by
    rwa [harc.second_ray]
  have hrun' : ∀ q ∈ supportRow S w, ∃ r : ℕ, r ≤ ell ∧ q = C.vertex J + (r : ℤ) • w := by
    rw [harc.second_ray]
    intro q hq
    exact (hrun q).mp hq
  obtain ⟨R, hR⟩ := finite_seed_sweep_from_fit P S (C.vertex J) (C.vertex (J + 1))
    ell hell ha hb harow hedge' hrun' hfit n
  exact ⟨R, 0, fun t _ => hR t⟩

end
end ConvexNivat.Colle
