import ConvexNivat.Colle.Shared.SequenceDefinitions
import ConvexNivat.CorePeriods
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.Filter.AtTopBot.Finite

namespace ConvexNivat.Colle
noncomputable section

private theorem realDet_embed_sub (d z q : Lattice) :
    realDet (embed d) (embed z - embed q) = (det d (z - q) : ℝ) := by
  simp [realDet, embed, det]

private theorem aligned_lattice_mem_iff {S A : Finset Lattice} {m : ℕ}
    {C : AntipodalEdgeCycle S m} (hA : EnvelopedWindow S A)
    (D : AlignedBoundary C A) (z : Lattice) :
    z ∈ A ↔ ∀ d : ℤ, 0 ≤ det (C.direction d) (z - D.vertex d) := by
  rw [← hA.2.1 z, D.hull_eq]
  change (∀ d : ℤ, 0 ≤ realDet (embed (C.direction d)) (embed z - embed (D.vertex d))) ↔ _
  simp only [realDet_embed_sub]
  constructor <;> intro h d <;> exact_mod_cast h d

private theorem normalised_mem_iff {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) (z : Lattice) :
    z ∈ W.normalised j ↔ ∀ d : ℤ, 0 ≤ det (C.direction d)
      (z - ((W.boundary j).vertex d - (W.normalise j : ℤ) • C.direction i)) := by
  have hm : z ∈ W.normalised j ↔ z + (W.normalise j : ℤ) • C.direction i ∈ W.A j := by
    constructor
    · intro hz
      obtain ⟨q, hq, hqz⟩ := Finset.mem_image.mp hz
      simpa [← hqz] using hq
    · intro hz
      exact Finset.mem_image.mpr ⟨z + (W.normalise j : ℤ) • C.direction i, hz,
        by simp⟩
  rw [hm, aligned_lattice_mem_iff (W.A_enveloped j) (W.boundary j)]
  simp only [sub_eq_add_neg, neg_add, neg_neg, add_assoc, add_comm]

private theorem normalised_anchor_mem {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (j : ℕ) : W.anchor ∈ W.normalised j := by
  have hv : (W.boundary j).vertex (i + 1) ∈ W.A j :=
    (Finset.mem_filter.mp ((W.boundary j).terminal i)).1
  apply Finset.mem_image.mpr
  refine ⟨(W.boundary j).vertex (i + 1), hv, ?_⟩
  simpa [sub_eq_add_neg] using W.terminal j

private theorem periodic_integer_representative {α : Type*} {f : ℤ → α} {p : ℤ}
    (_hp : 0 < p) (hf : Function.Periodic f p) (d : ℤ) :
    f d = f (d % p) := by
  have h := hf.int_mul (d / p) (d % p)
  have hd : d % p + d / p * p = d := by
    simpa [Int.mul_comm] using Int.emod_add_ediv_mul d p
  simpa [hd] using h

private theorem normalised_support_subsequence {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (f : ℕ → ℕ) :
    ∃ g : ℕ → ℕ, StrictMono g ∧
      ∀ j k, j ≤ k → W.normalised (f (g j)) ⊆ W.normalised (f (g k)) := by
  let vertex (j : ℕ) (d : ℤ) :=
    (W.boundary (f j)).vertex d - (W.normalise (f j) : ℤ) • C.direction i
  let slack (j : ℕ) (d : Fin (2 * m)) : ℕ :=
    (det (C.direction (d.val : ℤ)) (W.anchor - vertex j (d.val : ℤ))).toNat
  have hslack (j : ℕ) (d : ℤ) : 0 ≤ det (C.direction d) (W.anchor - vertex j d) :=
    (normalised_mem_iff W (f j) W.anchor).mp (normalised_anchor_mem W (f j)) d
  obtain ⟨g, hg⟩ := (wellQuasiOrdered_le (α := Fin (2 * m) → ℕ)).exists_monotone_subseq slack
  refine ⟨g, g.strictMono, ?_⟩
  intro j k hjk z hz
  apply (normalised_mem_iff W (f (g k)) z).mpr
  intro d
  have hp : 0 < 2 * (m : ℤ) := by
    have := C.at_least_two
    omega
  let r := d % (2 * (m : ℤ))
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hp.ne'
  have hrp : r < 2 * (m : ℤ) := Int.emod_lt_of_pos _ hp
  have hdir : C.direction d = C.direction r :=
    periodic_integer_representative hp C.direction_periodic d
  have hver (q : ℕ) : vertex q d = vertex q r := by
    have hper : Function.Periodic (vertex q) (2 * (m : ℤ)) := by
      intro t
      simp only [vertex, (W.boundary (f q)).vertex_periodic]
    exact periodic_integer_representative hp hper d
  let R : Fin (2 * m) := ⟨r.toNat, by omega⟩
  have hR : (R.val : ℤ) = r := Int.toNat_of_nonneg hr0
  have hmono := hg j k hjk R
  have hmonoZ : det (C.direction r) (W.anchor - vertex (g j) r) ≤
      det (C.direction r) (W.anchor - vertex (g k) r) := by
    have hcast := Int.ofNat_le.mpr hmono
    simpa only [slack, hR, Int.toNat_of_nonneg (hslack (g j) r),
      Int.toNat_of_nonneg (hslack (g k) r)] using hcast
  have hzj := (normalised_mem_iff W (f (g j)) z).mp hz d
  change 0 ≤ det (C.direction d) (z - vertex (g j) d) at hzj
  change 0 ≤ det (C.direction d) (z - vertex (g k) d)
  rw [hdir, hver (g k)]
  have hzj' : 0 ≤ det (C.direction r) (z - vertex (g j) r) := by
    simpa only [hdir, hver (g j)] using hzj
  have halgebra : det (C.direction r) (z - vertex (g k) r) =
      det (C.direction r) (z - vertex (g j) r) +
        det (C.direction r) (W.anchor - vertex (g k) r) -
        det (C.direction r) (W.anchor - vertex (g j) r) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [halgebra]
  omega

private theorem aligned_sector_height_sum {S A : Finset Lattice} {m : ℕ}
    {C : AntipodalEdgeCycle S m} (D : AlignedBoundary C A)
    (v : Lattice) (b : ℤ) (N : ℕ) :
    det v (D.vertex (b + (N : ℤ))) = det v (D.vertex b) +
      ∑ k ∈ Finset.range N, (D.length (b + (k : ℤ)) : ℤ) * det v (C.direction (b + (k : ℤ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hvertex : D.vertex (b + (N : ℤ) + 1) =
        D.vertex (b + (N : ℤ)) + (D.length (b + (N : ℤ)) : ℤ) • C.direction (b + (N : ℤ)) := by
      have h := D.edge_eq (b + (N : ℤ))
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, hvertex]
    change height v _ = _
    rw [height_add, height_zsmul]
    change det v (D.vertex (b + (N : ℤ))) +
      (D.length (b + (N : ℤ)) : ℤ) * det v (C.direction (b + (N : ℤ))) = _
    rw [ih, Finset.sum_range_succ]
    ring

private theorem alternating_sector_unbounded {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (f : ℕ → ℕ) (hf : StrictMono f) :
    ∃ d : Fin (m - 1), ∀ N : ℕ, ∃ j : ℕ,
      N < (W.boundary (f j)).length (i + 1 + (d.val : ℤ)) := by
  by_contra! hbounded
  choose L hL using hbounded
  let T : ℤ := det (C.direction i) W.anchor +
    ∑ d : Fin (m - 1), (L d : ℤ) * |det (C.direction i) (C.direction (i + 1 + (d.val : ℤ)))|
  have htop (j : ℕ) : det (C.direction i) ((W.boundary (f j)).vertex (i + (m : ℤ))) ≤ T := by
    have hsum := aligned_sector_height_sum (W.boundary (f j)) (C.direction i) (i + 1) (m - 1)
    have hind : i + 1 + ((m - 1 : ℕ) : ℤ) = i + (m : ℤ) := by
      have := C.at_least_two
      omega
    rw [hind, ← Fin.sum_univ_eq_sum_range] at hsum
    have hanchor : det (C.direction i) ((W.boundary (f j)).vertex (i + 1)) =
        det (C.direction i) W.anchor := by
      rw [← W.terminal (f j)]
      change (C.direction i).1 * ((W.boundary (f j)).vertex (i + 1)).2 -
        (C.direction i).2 * ((W.boundary (f j)).vertex (i + 1)).1 =
        (C.direction i).1 * (((W.boundary (f j)).vertex (i + 1)).2 -
          (W.normalise (f j) : ℤ) * (C.direction i).2) -
        (C.direction i).2 * (((W.boundary (f j)).vertex (i + 1)).1 -
          (W.normalise (f j) : ℤ) * (C.direction i).1)
      ring
    rw [hsum, hanchor]
    dsimp only [T]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro d _
    have hd : ((W.boundary (f j)).length (i + 1 + (d.val : ℤ)) : ℤ) ≤ L d := by
      exact_mod_cast hL d j
    calc
      _ ≤ ((W.boundary (f j)).length (i + 1 + (d.val : ℤ)) : ℤ) *
          |det (C.direction i) (C.direction (i + 1 + (d.val : ℤ)))| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
  obtain ⟨z, hz⟩ := primitive_height_surjective (C.direction i) (C.primitive i) (max T 0 + 1)
  let R : ℕ := max z.1.natAbs z.2.natAbs
  have hR : z ∈ integerSquare (f R) := by
    have hRle : R ≤ f R := hf.id_le R
    have h₁ : z.1.natAbs ≤ f R := (le_max_left _ _).trans hRle
    have h₂ : z.2.natAbs ≤ f R := (le_max_right _ _).trans hRle
    have habs₁ : |z.1| ≤ (f R : ℤ) := by
      simpa only [Int.natCast_natAbs] using Int.ofNat_le.mpr h₁
    have habs₂ : |z.2| ≤ (f R : ℤ) := by
      simpa only [Int.natCast_natAbs] using Int.ofNat_le.mpr h₂
    simpa only [integerSquare, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] using
      And.intro (abs_le.mp habs₁) (abs_le.mp habs₂)
  have hzheight : -1 ≤ det (C.direction i) z := by
    change height (C.direction i) z = _ at hz
    change -1 ≤ height (C.direction i) z
    rw [hz]
    omega
  have hzA : z ∈ W.A (f R) := W.base_in_maximal (f R) (W.exhaustion (f R) z hR hzheight)
  have hdet := (aligned_lattice_mem_iff (W.A_enveloped (f R)) (W.boundary (f R)) z).mp hzA
    (i + (m : ℤ))
  rw [C.antipodal] at hdet
  have hzle : det (C.direction i) z ≤ det (C.direction i) ((W.boundary (f R)).vertex (i + (m : ℤ))) := by
    simp only [det, Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub] at hdet ⊢
    nlinarith
  have ht := hzle.trans (htop R)
  change height (C.direction i) z ≤ T at ht
  rw [hz] at ht
  omega

private theorem finite_monotone_first_growth {r : ℕ} (F : ℕ → Fin r → ℕ)
    (hmono : Monotone F) (hunbounded : ∃ d : Fin r, ∀ N : ℕ, ∃ j : ℕ, N < F j d) :
    ∃ d : Fin r, ∃ g : ℕ → ℕ, StrictMono g ∧ StrictMono (fun j => F (g j) d) ∧
      ∀ e : Fin r, e < d → ∃ L : ℕ, ∀ j : ℕ, F (g j) e = L := by
  classical
  let unbounded : Finset (Fin r) := Finset.univ.filter (fun d => ∀ N : ℕ, ∃ j : ℕ, N < F j d)
  have hn : unbounded.Nonempty := by
    obtain ⟨d, hd⟩ := hunbounded
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd⟩⟩
  let d := unbounded.min' hn
  have hd : ∀ N : ℕ, ∃ j : ℕ, N < F j d := (Finset.mem_filter.mp (unbounded.min'_mem hn)).2
  have heventual (e : Fin r) : ∃ L N : ℕ, ∀ j ≥ N, e < d → F j e = L := by
    by_cases he : e < d
    · have hebounded : ∃ b : ℕ, ∀ j : ℕ, F j e ≤ b := by
        by_contra! heunbounded
        have hmem : e ∈ unbounded := Finset.mem_filter.mpr ⟨Finset.mem_univ e, heunbounded⟩
        exact (unbounded.min'_le e hmem).not_gt he
      obtain ⟨b, hb⟩ := hebounded
      obtain ⟨L, N, hLN⟩ := converges_of_monotone_of_bounded (fun j k hjk => hmono hjk e) hb
      exact ⟨L, N, fun j hj _ => hLN j hj⟩
    · exact ⟨0, 0, fun _ _ h => (he h).elim⟩
  choose L N hLN using heventual
  let start := Finset.univ.sup N
  have hstart (e : Fin r) : N e ≤ start := Finset.le_sup (Finset.mem_univ e)
  have hlim : Filter.Tendsto (fun j => F (j + start) d) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    obtain ⟨j, hj⟩ := hd b
    exact Filter.eventually_atTop.2 ⟨j, fun k hk => hj.le.trans (hmono (by omega) d)⟩
  obtain ⟨g, hg, hgF⟩ := Filter.strictMono_subseq_of_tendsto_atTop hlim
  refine ⟨d, fun j => g j + start, ?_, hgF, ?_⟩
  · intro j k hjk
    exact Nat.add_lt_add_right (hg hjk) start
  · intro e he
    exact ⟨L e, fun j => hLN e (g j + start) (by have := hstart e; omega) he⟩

private theorem translate_period_remainder (x : Configuration ℤ) (v : Lattice)
    (N n : ℕ) (hp : HasPeriod x ((N : ℤ) • v)) :
    translate ((n : ℤ) • v) x = translate (((n % N : ℕ) : ℤ) • v) x := by
  funext z
  have h := hasPeriod_zsmul x ((N : ℤ) • v) hp ((n / N : ℕ) : ℤ)
    (z + (((n % N : ℕ) : ℤ) • v))
  have hn : (n : ℤ) = ((n % N : ℕ) : ℤ) + ((n / N : ℕ) : ℤ) * (N : ℤ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.mod_add_div n N).symm :
      n = n % N + n / N * N)
  change x (z + (n : ℤ) • v) = x (z + (((n % N : ℕ) : ℤ) • v))
  have heq : z + (n : ℤ) • v =
      (z + (((n % N : ℕ) : ℤ) • v)) + ((n / N : ℕ) : ℤ) • ((N : ℤ) • v) := by
    conv_lhs => rw [hn]
    simp only [add_smul, mul_smul, add_assoc]
  rw [heq]
  exact h

private theorem normalisation_common_phase_subsequence {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (a : ℤ) (ha : a ≠ 0)
    (hperiod : HasPeriod xper (a • C.direction i)) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ phase : ℕ, ∀ j,
      translate ((W.normalise (f j) : ℤ) • C.direction i) xper =
        translate ((phase : ℤ) • C.direction i) xper := by
  classical
  let N := a.natAbs
  have hN : 0 < N := Int.natAbs_pos.mpr ha
  have hp : HasPeriod xper ((N : ℤ) • C.direction i) := by
    rcases lt_or_gt_of_ne ha with han | hap
    · have hn : (N : ℤ) = -a := by
        simp [N, abs_of_neg han]
      rw [hn, neg_smul]
      exact hasPeriod_neg _ _ hperiod
    · have hn : (N : ℤ) = a := by
        simp [N, abs_of_pos hap]
      simpa [hn] using hperiod
  let colour : ℕ → Fin N := fun j => ⟨W.normalise j % N, Nat.mod_lt _ hN⟩
  obtain ⟨r, hr⟩ := Finite.exists_infinite_fiber colour
  have hfiber : (colour ⁻¹' {r}).Infinite := Set.infinite_coe_iff.mp hr
  obtain ⟨f, hf, heq⟩ := Nat.exists_strictMono_subsequence (P := fun j => colour j = r) (by
    intro n
    obtain ⟨j, hj, hnj⟩ := hfiber.exists_gt n
    exact ⟨j, hnj, hj⟩)
  refine ⟨f, hf, r.val, ?_⟩
  intro j
  have hj : W.normalise (f j) % N = r.val := congrArg Fin.val (heq j)
  simpa [hj] using translate_period_remainder xper (C.direction i) N (W.normalise (f j)) hp

/-- RC19: phase selection, first growth, and nesting are separate outputs. -/
theorem residue_and_first_growing_edge_subsequence {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (a : ℤ) (ha : a ≠ 0)
    (hperiod : HasPeriod xper (a • C.direction i)) :
    Nonempty (GrowingSubsequence W) := by
  obtain ⟨f, hf, phase, hphase⟩ := normalisation_common_phase_subsequence W a ha hperiod
  obtain ⟨g, hg, hnested⟩ := normalised_support_subsequence W f
  let lengths (j : ℕ) (d : Fin (m - 1)) := (W.boundary (f (g j))).length (i + 1 + (d.val : ℤ))
  obtain ⟨q, hq⟩ := (wellQuasiOrdered_le (α := Fin (m - 1) → ℕ)).exists_monotone_subseq lengths
  let h : ℕ → ℕ := fun j => f (g (q j))
  have hh : StrictMono h := hf.comp (hg.comp q.strictMono)
  let F (j : ℕ) (d : Fin (m - 1)) := (W.boundary (h j)).length (i + 1 + (d.val : ℤ))
  have hF : Monotone F := fun j k hjk => hq j k hjk
  obtain ⟨d, p, hp, hgrowth, hearlier⟩ := finite_monotone_first_growth F hF (alternating_sector_unbounded W h hh)
  refine ⟨{
    subsequence := fun j => h (p j)
    strict := hh.comp hp
    phase := phase
    J := i + 1 + (d.val : ℤ)
    lower := by omega
    upper := by have := d.isLt; have := C.at_least_two; omega
    same_phase := fun j => hphase (g (q (p j)))
    earlier_fixed := ?_
    growing := hgrowth
    nested := ?_
  }⟩
  · intro eZ heZ hdZ
    let e : Fin (m - 1) := ⟨(eZ - i - 1).toNat, by have := d.isLt; omega⟩
    have he : e < d := by
      change (eZ - i - 1).toNat < d.val
      omega
    have hei : i + 1 + (e.val : ℤ) = eZ := by
      change i + 1 + (((eZ - i - 1).toNat : ℕ) : ℤ) = eZ
      omega
    obtain ⟨L, hL⟩ := hearlier e he
    exact ⟨L, fun j => by simpa only [F, hei] using hL j⟩
  · intro j
    exact hnested (q (p j)) (q (p (j + 1))) (q.monotone (hp.monotone (Nat.le_succ j)))

end
end ConvexNivat.Colle
