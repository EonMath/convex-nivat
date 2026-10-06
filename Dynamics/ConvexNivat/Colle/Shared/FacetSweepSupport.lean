import ConvexNivat.Colle.Shared.FacetShiftData
import ConvexNivat.Colle.Shared.FiniteSweepLocalisation

namespace ConvexNivat.Colle
noncomputable section

local macro "paidSourceRowLength" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.cycle_row_length))
local macro "paidHalfOrder" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.cycle_half_order))
local macro "paidPeriodicMod" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.periodic_mod))
local macro "paidSupportDet" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.support_det_nonneg))

private theorem facet_aligned_residual_step {S A : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S)
    (B : AlignedBoundary C A) (r : ℤ) :
    ∃ k : ℤ, 0 ≤ k ∧
      (B.vertex (r+1) - C.vertex (r+1)) - (B.vertex r - C.vertex r) =
        k • C.direction r := by
  obtain ⟨s, hs, he⟩ := C.edge_length r
  have hcard := paidSourceRowLength C hS r s (by omega) he
  have hle := B.source_length_le r
  have hk : s ≤ (B.length r : ℤ) := by omega
  refine ⟨(B.length r : ℤ)-s, by omega, ?_⟩
  calc
    _ = (B.vertex (r+1)-B.vertex r) - (C.vertex (r+1)-C.vertex r) := by abel
    _ = _ := by rw [B.edge_eq, he, sub_smul]

private theorem facet_half_det_nonneg {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (r k : ℤ) (hr : r ≤ k) (hk : k ≤ r+m) :
    0 ≤ det (C.direction r) (C.direction k) := by
  by_cases h : k=r
  · subst k; simp [det, mul_comm]
  by_cases h' : k=r+m
  · rw [h',C.antipodal]; simp [det, mul_comm]
  exact (paidHalfOrder C r k (by omega) (by omega)).le

private theorem facet_cyclic_residual_support {S A : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S)
    (B : AlignedBoundary C A) (r k : ℤ) :
    det (C.direction r) (B.vertex r-C.vertex r) ≤
      det (C.direction r) (B.vertex k-C.vertex k) := by
  let R (t : ℤ) := B.vertex t-C.vertex t
  have hperiod (t : ℤ) : R (t+2*(m : ℤ))=R t := by
    dsimp [R]; rw [B.vertex_periodic,C.vertex_periodic]
  have hfwd : ∀ n : ℕ, n ≤ m →
      det (C.direction r) (R r) ≤ det (C.direction r) (R (r+n)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      obtain ⟨a, ha, he⟩ := facet_aligned_residual_step C hS B (r+n)
      have hdet := facet_half_det_nonneg C r (r+n) (by omega) (by omega)
      have hd : det (C.direction r) (R (r+(n+1 : ℕ))) -
          det (C.direction r) (R (r+n)) = a*det (C.direction r) (C.direction (r+n)) := by
        have he' : R (r+(n+1 : ℕ))-R (r+n)=a • C.direction (r+n) := by
          simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using he
        calc
          _ = det (C.direction r) (R (r+(n+1 : ℕ))-R (r+n)) := by dsimp [det]; ring
          _ = _ := by rw [he']; dsimp [det]; ring
      have hnon := mul_nonneg ha hdet
      omega
  have hbwd : ∀ n : ℕ, n ≤ m →
      det (C.direction r) (R r) ≤ det (C.direction r) (R (r+2*m-n)) := by
    intro n
    induction n with
    | zero => intro _; simp only [Nat.cast_zero,sub_zero,hperiod,le_refl]
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      let t : ℤ := r+2*m-(n+1 : ℕ)
      obtain ⟨a, ha, he⟩ := facet_aligned_residual_step C hS B t
      have hdet : det (C.direction r) (C.direction t) ≤ 0 := by
        have hp := facet_half_det_nonneg C r (t-m) (by dsimp [t]; omega)
          (by dsimp [t]; omega)
        have hdir : C.direction t = -C.direction (t-m) := by
          convert C.antipodal (t-m) using 1 <;> congr 1 <;> omega
        rw [hdir]
        have hh : det (C.direction r) (-C.direction (t-m)) =
            -det (C.direction r) (C.direction (t-m)) := by dsimp [det]; ring
        rw [hh]; omega
      have hd : det (C.direction r) (R (r+2*m-n)) -
          det (C.direction r) (R (r+2*m-(n+1 : ℕ))) =
            a*det (C.direction r) (C.direction t) := by
        have ht : t+1=r+2*m-n := by dsimp [t]; omega
        change R (t+1)-R t = _ at he
        rw [ht] at he
        calc
          _ = det (C.direction r) (R (r+2*m-n)-R (r+2*m-(n+1 : ℕ))) := by dsimp [det]; ring
          _ = _ := by rw [he]; dsimp [det]; ring
      have hnon := mul_nonpos_of_nonneg_of_nonpos ha hdet
      omega
  let n : ℕ := ((k-r) % (2*m : ℕ)).toNat
  have hn0 : 0 ≤ (k-r) % (2*m : ℕ) := Int.emod_nonneg _ (by have h := C.at_least_two; omega)
  have hn : n < 2*m := by
    have hlt := Int.emod_lt_of_pos (k-r) (show (0 : ℤ)<(2*m : ℕ) by have h := C.at_least_two; omega)
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hn0 hlt
    dsimp [n]; omega
  have hR : R (r+n)=R k := by
    have hm := paidPeriodicMod (fun t => R (r+t)) (2*m)
      (by have h := C.at_least_two; omega)
      (fun t => by simpa only [Nat.cast_mul,Nat.cast_ofNat,add_assoc] using hperiod (r+t)) (k-r)
    change R (r+(((k-r) % (2*m : ℕ)).toNat : ℤ))=R k
    rw [Int.toNat_of_nonneg hn0]
    simpa using hm
  change det (C.direction r) (R r) ≤ det (C.direction r) (R k)
  rw [← hR]
  by_cases hnm : n ≤ m
  · exact hfwd n hnm
  · have h := hbwd (2*m-n) (by omega)
    have he : r+2*m-((2*m-n : ℕ) : ℤ)=r+n := by omega
    rwa [he] at h

private theorem facet_aligned_vertex_source_fit {S A : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S)
    (hA : LatticeConvex A) (B : AlignedBoundary C A) (k : ℤ) :
    (windowTranslate S (B.vertex k-C.vertex k) : Set Lattice) ⊆ (A : Set Lattice) := by
  intro z hz
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  apply (hA _).mp
  rw [B.hull_eq]
  intro r
  have hs := paidSupportDet (C.initial_mem r) hq
  have hr := facet_cyclic_residual_support C hS B r k
  have hd : 0 ≤ det (C.direction r) (q+(B.vertex k-C.vertex k)-B.vertex r) := by
    dsimp [det] at *
    linarith
  have he : realDet (embed (C.direction r))
      (embed (q+(B.vertex k-C.vertex k))-embed (B.vertex r)) =
      (det (C.direction r) (q+(B.vertex k-C.vertex k)-B.vertex r) : ℝ) := by
    simp [realDet,embed,det]
  rw [he]
  exact_mod_cast hd

local macro "paidNoMiddle" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.support_pair_forbids_middle))
local macro "paidParallel" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.primitive_parallel_eq_or_neg))
local macro "paidCycleMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.cycle_direction_mem))
local macro "paidCycleTurn" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.cycle_turn_positive))

private theorem facet_backward_direction {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (J r : ℤ)
    (h : det (C.direction r) (C.direction J) ≤ 0)
    (hne : C.direction r ≠ C.direction J) :
    det (C.direction r) (C.direction (J+1)) ≤ 0 := by
  by_contra hn
  have hpos : 0 < det (C.direction r) (C.direction (J+1)) := by omega
  have hturn := paidCycleTurn C J
  have hw : 0 ≤ det (C.direction J) (C.direction r) := by
    have he : det (C.direction J) (C.direction r) =
        -det (C.direction r) (C.direction J) := by dsimp [det]; ring
    rw [he]; omega
  by_cases hzero : det (C.direction J) (C.direction r)=0
  · rcases paidParallel _ _ (C.primitive J) (C.primitive r) hzero with he | he
    · exact hne he
    · rw [he] at hpos
      have he' : det (-C.direction J) (C.direction (J+1)) =
          -det (C.direction J) (C.direction (J+1)) := by dsimp [det]; ring
      rw [he'] at hpos
      omega
  · exact paidNoMiddle (C.terminal_mem J) (C.initial_mem (J+1)) hturn
      (by omega) hpos (paidCycleMem C r)

private theorem facet_terminal_negative_support {S A : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hS : LatticeConvex S)
    (hA : LatticeConvex A) (B : AlignedBoundary C A)
    (J r : ℤ) (u z q : Lattice) (hq : q ∈ S)
    (hw : det (C.direction J) z ≤ det (C.direction J) (B.vertex (J+1)-u))
    (hd : det (C.direction (J+1)) (B.vertex (J+1)-u) ≤
      det (C.direction (J+1)) z)
    (hr : det (C.direction r) (C.direction J) ≤ 0)
    (hne : C.direction r ≠ C.direction J) :
    det (C.direction r) (B.vertex r-u) ≤
      det (C.direction r) (z+(q-C.vertex (J+1))) := by
  have hdir := facet_backward_direction C J r hr hne
  have hturn := paidCycleTurn C J
  have hid : det (C.direction J) (C.direction (J+1)) *
      det (C.direction r) (z-(B.vertex (J+1)-u)) =
      det (C.direction r) (C.direction (J+1)) *
        det (C.direction J) (z-(B.vertex (J+1)-u)) -
      det (C.direction r) (C.direction J) *
        det (C.direction (J+1)) (z-(B.vertex (J+1)-u)) := by
    dsimp [det]; ring
  have hw' : det (C.direction J) (z-(B.vertex (J+1)-u)) ≤ 0 := by
    dsimp [det] at *; linarith
  have hd' : 0 ≤ det (C.direction (J+1)) (z-(B.vertex (J+1)-u)) := by
    dsimp [det] at *; linarith
  have hnon : 0 ≤ det (C.direction r) (z-(B.vertex (J+1)-u)) := by
    have hm := mul_nonneg_of_nonpos_of_nonpos hdir hw'
    have hm' := mul_nonpos_of_nonpos_of_nonneg hr hd'
    nlinarith
  have hfit : q+(B.vertex (J+1)-C.vertex (J+1)) ∈ A :=
    facet_aligned_vertex_source_fit C hS hA B (J+1) (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hsupport := paidSupportDet (B.initial r) hfit
  dsimp [det] at *
  linarith

private theorem facet_forward_support_bound (p w δ a z e : Lattice) (D M : ℤ)
    (hβ : 0 < det p w) (hδ : 0 < det δ w)
    (hD : 0 ≤ D) (hzlo : -D ≤ det w (z-a)) (hzhi : det w (z-a) ≤ 0)
    (hM : D * |det δ p| + det p w * |det δ e| ≤ M)
    (hz : M ≤ det p (z-a)) : 0 ≤ det δ (z+e-a) := by
  have hM0 : 0 ≤ M := (add_nonneg (mul_nonneg hD (abs_nonneg _))
    (mul_nonneg hβ.le (abs_nonneg _))).trans hM
  have hδ1 : 1 ≤ det δ w := hδ
  have hβ0 := hβ.le
  have ha : |det w (z-a)| ≤ D := abs_le.mpr ⟨hzlo,hzhi.trans hD⟩
  have he : det δ e ≥ -|det δ e| := neg_abs_le _
  have hp : det δ p * det w (z-a) ≤ |det δ p| * D := by
    calc
      _ ≤ |det δ p * det w (z-a)| := le_abs_self _
      _ = |det δ p| * |det w (z-a)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  have hscale : M ≤ det δ w * det p (z-a) := by nlinarith
  have hid : det p w * det δ (z+e-a) =
      det δ w * det p (z-a) - det δ p * det w (z-a) + det p w * det δ e := by
    dsimp [det]; ring
  have hh := mul_le_mul_of_nonneg_left he hβ0
  nlinarith

private theorem facet_uniform_support_bound {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (J : ℤ) (D : ℤ) (hD : 0 ≤ D) :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ r : ℤ, ∀ q ∈ S,
      D * |det (C.direction r) (C.direction (J-1))| +
        det (C.direction (J-1)) (C.direction J) *
          |det (C.direction r) (q-C.vertex (J+1))| ≤ M := by
  classical
  let costs := ((Finset.range (2*m)).product S).image fun rq =>
    D * |det (C.direction (rq.1 : ℤ)) (C.direction (J-1))| +
      det (C.direction (J-1)) (C.direction J) *
        |det (C.direction (rq.1 : ℤ)) (rq.2-C.vertex (J+1))|
  obtain ⟨M,hM⟩ := costs.exists_le
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro r q hq
  let t := r % (2*m : ℕ)
  have ht0 : 0 ≤ t := Int.emod_nonneg _ (by have h := C.at_least_two; omega)
  have htlt : t < (2*m : ℕ) := Int.emod_lt_of_pos _ (by have h := C.at_least_two; omega)
  have he : C.direction (t.toNat : ℤ) = C.direction r := by
    rw [Int.toNat_of_nonneg ht0]
    exact paidPeriodicMod C.direction (2*m) (by have h := C.at_least_two; omega)
      (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using C.direction_periodic) r
  have hh := hM _ (Finset.mem_image.mpr ⟨(t.toNat,q),Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega),hq⟩,rfl⟩)
  dsimp only at hh
  rw [he] at hh
  exact hh.trans (le_max_right _ _)

private theorem facet_det_rectangle_finite (p w a : Lattice) (h : det p w ≠ 0)
    (D M : ℤ) :
    {z : Lattice | -D ≤ det w (z-a) ∧ det w (z-a) ≤ 0 ∧
      0 ≤ det p (z-a) ∧ det p (z-a) ≤ M}.Finite := by
  let f : Lattice → ℤ × ℤ := fun z => (det w (z-a),det p (z-a))
  have hf : Function.Injective f := by
    intro x y hxy
    have hw := congrArg Prod.fst hxy
    have hp := congrArg Prod.snd hxy
    change det w (x-a)=det w (y-a) at hw
    change det p (x-a)=det p (y-a) at hp
    have h₁ : det p w * (x.1-y.1) = 0 := by
      dsimp [det] at *
      linear_combination w.1 * hp - p.1 * hw
    have h₂ : det p w * (x.2-y.2) = 0 := by
      dsimp [det] at *
      linear_combination w.2 * hp - p.2 * hw
    have e₁ := (mul_eq_zero.mp h₁).resolve_left h
    have e₂ := (mul_eq_zero.mp h₂).resolve_left h
    exact Prod.ext (by omega) (by omega)
  have hfinite := ((Finset.Icc (-D) 0).product (Finset.Icc 0 M)).finite_toSet.preimage hf.injOn
  apply hfinite.subset
  intro z hz
  change f z ∈ ((Finset.Icc (-D) 0).product (Finset.Icc 0 M) : Finset (ℤ × ℤ))
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hz.1,hz.2.1⟩,
    Finset.mem_Icc.mpr ⟨hz.2.2.1,hz.2.2.2⟩⟩

local macro "paidRowMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.row_mem))
local macro "facetU" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetShiftData).num 0 ++ `ConvexNivat.Colle.facetShiftLattice))
local macro "facetD" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetShiftData).num 0 ++ `ConvexNivat.Colle.facetShiftDepth))

private theorem facet_row_translate_support {S A : Finset Lattice} {m : ℕ}
    {C : AntipodalEdgeCycle S m} (B : AlignedBoundary C A)
    (r : ℤ) (u z : Lattice) (hz : z ∈ windowTranslate A (-u)) :
    det (C.direction r) (B.vertex r-u) ≤ det (C.direction r) z := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  have h := paidSupportDet (B.initial r) hq
  dsimp [det] at *
  linarith

private theorem facet_same_row_height {S A : Finset Lattice} {m : ℕ}
    {C : AntipodalEdgeCycle S m} (B : AlignedBoundary C A)
    (r k : ℤ) (u : Lattice) (h : C.direction r=C.direction k) :
    det (C.direction r) (B.vertex r-u)=det (C.direction k) (B.vertex k-u) := by
  have hr := (paidRowMem A _ _).mp (B.initial r)
  have hk := (paidRowMem A _ _).mp (B.initial k)
  have h1 := hr.2 _ hk.1
  have h2 := hk.2 _ hr.1
  rw [h] at h1 ⊢
  dsimp [det] at *
  linarith

private theorem facet_shift_new_point_bounds {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (j : ℕ) (z : Lattice)
    (hz : z ∈ facetU W G L j)
    (hnot : z ∉ W.normalised (G.subsequence (L.index j))) :
    let u := (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i
    let B := W.boundary (G.subsequence (L.index j))
    let a := B.vertex G.J-u;
    -facetD C G.J ≤ det (C.direction G.J) (z-a) ∧
      det (C.direction G.J) (z-a) < 0 ∧
      0 ≤ det (C.direction (G.J-1)) (z-a) := by
  dsimp only
  let t := G.subsequence (L.index j)
  let u := (W.normalise t : ℤ) • C.direction i
  let B := W.boundary t
  let a := B.vertex G.J-u
  have hz' := hz
  change ∀ r : ℤ, _ ≤ _ at hz'
  have hw := hz' G.J
  simp only [ite_true] at hw
  have hlow : -facetD C G.J ≤ det (C.direction G.J) (z-a) := by
    dsimp [a,B,u,t,det] at *
    linarith
  have hhi : det (C.direction G.J) (z-a) < 0 := by
    by_contra hn
    have hzero : det (C.direction G.J) a ≤ det (C.direction G.J) z := by
      dsimp [det] at *; linarith
    apply hnot
    change z ∈ windowTranslate (W.A t) (-u)
    apply Finset.mem_image.mpr
    refine ⟨z+u, ?_, by abel⟩
    apply ((W.A_enveloped t).2.1 _).mp
    rw [B.hull_eq]
    intro r
    have hr : det (C.direction r) (B.vertex r-u) ≤ det (C.direction r) z := by
      by_cases he : C.direction r=C.direction G.J
      · rw [facet_same_row_height B r G.J u he,he]
        exact hzero
      · have hh := hz' r
        simpa only [he,ite_false,sub_zero] using hh
    have he : realDet (embed (C.direction r)) (embed (z+u)-embed (B.vertex r)) =
        (det (C.direction r) z-det (C.direction r) (B.vertex r-u) : ℤ) := by
      simp [realDet,embed,det]; ring
    rw [he]
    exact_mod_cast sub_nonneg.mpr hr
  have hturn := paidCycleTurn C (G.J-1)
  have hturn' : 0 < det (C.direction (G.J-1)) (C.direction G.J) := by simpa using hturn
  have hne : C.direction (G.J-1) ≠ C.direction G.J := by
    intro he; rw [he] at hturn'; simp [det,mul_comm] at hturn'
  have hp := hz' (G.J-1)
  simp only [hne,ite_false,sub_zero] at hp
  have hedge := B.edge_eq (G.J-1)
  have heheight : det (C.direction (G.J-1)) (B.vertex (G.J-1)-u) =
      det (C.direction (G.J-1)) a := by
    have he' : B.vertex G.J-B.vertex (G.J-1)=
        (B.length (G.J-1) : ℤ) • C.direction (G.J-1) := by simpa using hedge
    have hd := congrArg (det (C.direction (G.J-1))) he'
    dsimp [a,det] at *
    nlinarith
  change _ ≤ det (C.direction (G.J-1)) z at hp
  rw [heheight] at hp
  refine ⟨hlow,hhi,?_⟩
  dsimp [a,B,u,t,det] at *
  linarith

private theorem facet_shift_terminal_confined {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (hS : LatticeConvex S)
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (j : ℕ) (M : ℤ)
    (hM : ∀ r : ℤ, ∀ q ∈ S,
      facetD C G.J * |det (C.direction r) (C.direction (G.J-1))| +
        det (C.direction (G.J-1)) (C.direction G.J) *
          |det (C.direction r) (q-C.vertex (G.J+1))| ≤ M)
    (z : Lattice) (hz : z ∈ facetU W G L j)
    (hnot : z ∉ W.normalised (G.subsequence (L.index j)))
    (hfar : M ≤ det (C.direction (G.J-1))
      (z-((W.boundary (G.subsequence (L.index j))).vertex G.J-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i))) :
    ∀ q ∈ S.erase (C.vertex (G.J+1)), z+(q-C.vertex (G.J+1)) ∈ facetU W G L j := by
  intro q hq
  have hqS := Finset.mem_of_mem_erase hq
  let t := G.subsequence (L.index j)
  let u := (W.normalise t : ℤ) • C.direction i
  let B := W.boundary t
  let a := B.vertex G.J-u
  have hβ : 0 < det (C.direction (G.J-1)) (C.direction G.J) := by
    simpa using paidCycleTurn C (G.J-1)
  have hα := paidCycleTurn C G.J
  have hD : 0 ≤ facetD C G.J := (mul_pos hβ hα).le
  have hbds := facet_shift_new_point_bounds W G L j z hz hnot
  change -facetD C G.J ≤ det (C.direction G.J) (z-a) ∧
    det (C.direction G.J) (z-a)<0 ∧ 0≤det (C.direction (G.J-1)) (z-a) at hbds
  change ∀ r : ℤ, _ ≤ _ at hz ⊢
  intro r
  by_cases he : C.direction r=C.direction G.J
  · have hsup := paidSupportDet (C.terminal_mem G.J) hqS
    have hzr := hz r
    rw [he] at hzr ⊢
    dsimp [det] at *
    linarith
  simp only [he,ite_false,sub_zero]
  by_cases hr : det (C.direction r) (C.direction G.J) ≤ 0
  · have hne : C.direction (G.J+1) ≠ C.direction G.J := by
      intro he; rw [he] at hα; simp [det,mul_comm] at hα
    have hd := hz (G.J+1)
    simp only [hne,ite_false,sub_zero] at hd
    have hw : det (C.direction G.J) z ≤ det (C.direction G.J) (B.vertex (G.J+1)-u) := by
      have hedge := B.edge_eq G.J
      have hdg := congrArg (det (C.direction G.J)) hedge
      dsimp [a,det] at hbds hdg ⊢
      nlinarith
    exact facet_terminal_negative_support C hS (W.A_enveloped t).2.1 B G.J r u z q hqS hw hd hr he
  · have hpos : 0 < det (C.direction r) (C.direction G.J) := by omega
    have hb := facet_forward_support_bound (C.direction (G.J-1)) (C.direction G.J)
      (C.direction r) a z (q-C.vertex (G.J+1)) (facetD C G.J) M
      hβ hpos hD hbds.1 hbds.2.1.le (hM r q hqS) hfar
    have hamem : a ∈ windowTranslate (W.A t) (-u) :=
      Finset.mem_image.mpr ⟨B.vertex G.J,((paidRowMem _ _ _).mp (B.initial G.J)).1,by dsimp [a]; abel⟩
    have hsupport := facet_row_translate_support B r u a hamem
    apply hsupport.trans
    dsimp [det] at hb ⊢
    linarith

local macro "paidFixedVertex" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcUnion).num 0 ++ `ConvexNivat.Colle.arc_fixed_vertex))
local macro "paidAnchorMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.eg_second_anchor_mem))
local macro "paidSecondSupport" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_second_support))
local macro "paidPredecessorSupport" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.eg_predecessor_support))
local macro "paidCollarMembership" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.eg_collar_membership))
local macro "paidConfinedSweep" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FiniteSweepLocalisation).num 0 ++ `ConvexNivat.Colle.cycle_terminal_confined_sweep))

private theorem facet_anchor_matches_region_height {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice=normalisedUnion W G) :
    let a := (W.boundary (G.subsequence 0)).vertex G.J-
      (W.normalise (G.subsequence 0) : ℤ) • C.direction i
    a ∈ P.lattice ∧ det (C.direction G.J) a=det (C.direction G.J) P.secondAnchor := by
  dsimp only
  let a := (W.boundary (G.subsequence 0)).vertex G.J-
    (W.normalise (G.subsequence 0) : ℤ) • C.direction i
  have haA : a ∈ W.normalised (G.subsequence 0) :=
    Finset.mem_image.mpr ⟨(W.boundary (G.subsequence 0)).vertex G.J,
      ((paidRowMem _ _ _).mp ((W.boundary (G.subsequence 0)).initial G.J)).1,by dsimp [a]; abel⟩
  have haP : a ∈ P.lattice := by
    rw [hP]
    exact Set.mem_iUnion.mpr ⟨0,haA⟩
  have hlo := paidSecondSupport P haP
  have hanchor : P.secondAnchor ∈ P.lattice := paidAnchorMem P
  rw [hP] at hanchor
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hanchor
  have hhi := facet_row_translate_support (W.boundary (G.subsequence k)) G.J
    ((W.normalise (G.subsequence k) : ℤ) • C.direction i) P.secondAnchor hk
  have hfixed := paidFixedVertex W G G.J G.lower le_rfl k
  rw [hfixed] at hhi
  exact ⟨haP,le_antisymm hhi hlo⟩

private theorem facet_rectangle_in_enlargement {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice=normalisedUnion W G) (harc : RegionCompleteArc C i G.J P)
    (z : Lattice)
    (hlo : -facetD C G.J ≤ det (C.direction G.J)
      (z-((W.boundary (G.subsequence 0)).vertex G.J-
        (W.normalise (G.subsequence 0) : ℤ) • C.direction i)))
    (hhi : det (C.direction G.J)
      (z-((W.boundary (G.subsequence 0)).vertex G.J-
        (W.normalise (G.subsequence 0) : ℤ) • C.direction i)) ≤ 0)
    (hp : 0 ≤ det (C.direction (G.J-1))
      (z-((W.boundary (G.subsequence 0)).vertex G.J-
        (W.normalise (G.subsequence 0) : ℤ) • C.direction i))) :
    z ∈ P.enlargement (facetD C G.J).toNat := by
  let a := (W.boundary (G.subsequence 0)).vertex G.J-
    (W.normalise (G.subsequence 0) : ℤ) • C.direction i
  obtain ⟨ha,he⟩ := facet_anchor_matches_region_height W G P hP
  change a ∈ P.lattice at ha
  change det (C.direction G.J) a=det (C.direction G.J) P.secondAnchor at he
  have hβ : 0 < det (C.direction (G.J-1)) (C.direction G.J) := by
    simpa using paidCycleTurn C (G.J-1)
  have hD : 0 ≤ facetD C G.J := (mul_pos hβ (paidCycleTurn C G.J)).le
  have hdcast : ((facetD C G.J).toNat : ℤ)=facetD C G.J := Int.toNat_of_nonneg hD
  have hupper : det (C.direction G.J) z ≤ det (C.direction G.J) P.secondAnchor := by
    change det (C.direction G.J) (z-a) ≤ 0 at hhi
    dsimp [det] at he hhi ⊢; linarith
  apply (paidCollarMembership P (facetD C G.J).toNat z hupper).mpr
  constructor
  · rw [hdcast]
    change -facetD C G.J ≤ det (C.direction G.J) (z-a) at hlo
    dsimp [det] at he hlo ⊢; linarith
  · have hs := paidPredecessorSupport P (embed a) ha
    have heq : realDet (embed P.predecessor) (embed a-embed P.secondAnchor) =
        (det P.predecessor a-det P.predecessor P.secondAnchor : ℤ) := by
      simp [realDet,embed,det]; ring
    change 0 ≤ realDet (embed P.predecessor) (embed a-embed P.secondAnchor) at hs
    rw [heq] at hs
    have hsZ : 0 ≤ det P.predecessor a-det P.predecessor P.secondAnchor := by exact_mod_cast hs
    rw [region_complete_arc_predecessor harc] at hsZ ⊢
    change 0 ≤ det (C.direction (G.J-1)) (z-a) at hp
    dsimp [det] at hp hsZ ⊢; linarith

private theorem independent_facet_uniform_sweep
(ξ xper : Configuration ℤ)
(alphabet : Finset ℤ) (halphabet : ∀ z, ξ z ∈ alphabet)
(S : Finset Lattice) (hS : GeneratingSet ξ S)
(m : ℕ) (C : AntipodalEdgeCycle S m) (i : ℤ)
(hxper : xper ∈ OrbitClosure ξ)
(hperiod : ∃ a : ℤ, a ≠ 0 ∧ HasPeriod xper (a • C.direction i))
(W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
(P : Region (C.direction i) (C.direction G.J))
(hP : P.lattice = normalisedUnion W G)
(hcarrier : P.carrier = closedRealHull (normalisedUnion W G))
(hweak : WeaklyEnveloped S P) (harc : RegionCompleteArc C i G.J P)
(hanchor : det (C.direction i) P.firstAnchor = -1)
(L : NormalisedWindowLimit W G)
(hall : ∀ r : ℕ, AgreesOn L.field
  (translate ((G.phase : ℤ) • C.direction i) xper) (P.enlargement r))
    (E : ℕ → Finset Lattice)
    (hE : ∀ j : ℕ, (E j : Set Lattice) = facetU W G L j)
    (jG : ℕ)
    (hgeometry : ∀ j ≥ jG, EnvelopedWindow S (E j) ∧
      W.normalised (G.subsequence (L.index j)) ⊂ E j) :
    ∃ N : ℕ, ∃ K : Finset Lattice,
      (K : Set Lattice) ⊆ P.enlargement N ∧
      ∃ jS : ℕ, ∀ j ≥ jS, HasFiniteSweep S
        ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
          (K : Set Lattice)) (E j) := by
  classical
  let p := C.direction (G.J-1)
  let w := C.direction G.J
  let a := (W.boundary (G.subsequence 0)).vertex G.J-
    (W.normalise (G.subsequence 0) : ℤ) • C.direction i
  have hβ : 0 < det p w := by simpa [p,w] using paidCycleTurn C (G.J-1)
  have hD : 0 ≤ facetD C G.J := (mul_pos hβ (paidCycleTurn C G.J)).le
  obtain ⟨M,hM0,hM⟩ := facet_uniform_support_bound C G.J (facetD C G.J) hD
  let R := {z : Lattice | -facetD C G.J ≤ det w (z-a) ∧ det w (z-a) ≤ 0 ∧
    0 ≤ det p (z-a) ∧ det p (z-a) ≤ M}
  have hR : R.Finite := facet_det_rectangle_finite p w a hβ.ne' (facetD C G.J) M
  let K := hR.toFinset
  have hK : (K : Set Lattice) ⊆ P.enlargement (facetD C G.J).toNat := by
    intro z hz
    have hzR : z ∈ R := hR.mem_toFinset.mp hz
    exact facet_rectangle_in_enlargement W G P hP harc z hzR.1 hzR.2.1 hzR.2.2.1
  refine ⟨(facetD C G.J).toNat,K,hK,0,?_⟩
  intro j hj
  apply paidConfinedSweep C hS.2.1 G.J
  intro z hz hznot q hq
  have hzU : z ∈ facetU W G L j := by rw [← hE j]; exact hz
  have hzA : z ∉ W.normalised (G.subsequence (L.index j)) := fun h => hznot (Or.inl h)
  have hzK : z ∉ K := fun h => hznot (Or.inr h)
  have hfix := paidFixedVertex W G G.J G.lower le_rfl (L.index j)
  have hbds := facet_shift_new_point_bounds W G L j z hzU hzA
  dsimp only at hbds
  rw [hfix] at hbds
  have hfar : M ≤ det p (z-a) := by
    by_contra hn
    apply hzK
    apply hR.mem_toFinset.mpr
    exact ⟨hbds.1,hbds.2.1.le,hbds.2.2,by omega⟩
  have hconf := facet_shift_terminal_confined hS.2.1 W G L j M hM z hzU hzA
    (by rw [hfix]; exact hfar) q hq
  change z+(q-C.vertex (G.J+1)) ∈ (E j : Set Lattice)
  rw [hE j]
  exact hconf

end
end ConvexNivat.Colle
