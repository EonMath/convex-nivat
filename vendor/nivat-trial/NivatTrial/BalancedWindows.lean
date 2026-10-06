import NivatTrial.LatticePolygon
import NivatTrial.Dynamics

/-! Actual horizontal rows and balanced lattice-convex windows (Appendix D). -/

namespace NivatTrial.BalancedWindows

open NivatTrial.Zonotope NivatTrial.LatticePolygon NivatTrial.Dynamics
open scoped Classical

noncomputable section

def row (B : Finset Lattice) (t : ℤ) : Finset Lattice := B.filter (fun z => z.2 = t)

def lower (B : Finset Lattice) : ℤ :=
  if h : B.Nonempty then (B.image Prod.snd).min' (h.image _) else 0

def upper (B : Finset Lattice) : ℤ :=
  if h : B.Nonempty then (B.image Prod.snd).max' (h.image _) else 0

def topEdge (B : Finset Lattice) : Finset Lattice := row B (upper B)
def bottomEdge (B : Finset Lattice) : Finset Lattice := row B (lower B)
def base (B : Finset Lattice) : Finset Lattice := B \ topEdge B
def upperBase (B : Finset Lattice) : Finset Lattice := B \ bottomEdge B

@[simp] theorem mem_row (B : Finset Lattice) (t : ℤ) (z : Lattice) :
    z ∈ row B t ↔ z ∈ B ∧ z.2 = t := Finset.mem_filter

theorem row_subset (B : Finset Lattice) (t : ℤ) : row B t ⊆ B :=
  Finset.filter_subset _ _

theorem lower_le_of_mem {B : Finset Lattice} {z : Lattice} (hz : z ∈ B) :
    lower B ≤ z.2 := by
  rw [lower, dif_pos ⟨z, hz⟩]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

theorem le_upper_of_mem {B : Finset Lattice} {z : Lattice} (hz : z ∈ B) :
    z.2 ≤ upper B := by
  rw [upper, dif_pos ⟨z, hz⟩]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

theorem bottomEdge_nonempty {B : Finset Lattice} (hB : B.Nonempty) :
    (bottomEdge B).Nonempty := by
  have h := Finset.min'_mem (B.image Prod.snd) (hB.image Prod.snd)
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp h
  exact ⟨z, (mem_row B (lower B) z).mpr ⟨hz, by simpa [lower, hB] using he⟩⟩

theorem topEdge_nonempty {B : Finset Lattice} (hB : B.Nonempty) :
    (topEdge B).Nonempty := by
  have h := Finset.max'_mem (B.image Prod.snd) (hB.image Prod.snd)
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp h
  exact ⟨z, (mem_row B (upper B) z).mpr ⟨hz, by simpa [upper, hB] using he⟩⟩

theorem lower_le_upper {B : Finset Lattice} (hB : B.Nonempty) : lower B ≤ upper B := by
  obtain ⟨z, hz⟩ := hB
  exact (lower_le_of_mem hz).trans (le_upper_of_mem hz)

/-- A horizontal segment is contained in any convex set containing its endpoints. -/
theorem horizontal_between {C : Set Plane} (hC : Convex ℝ C)
    {l r x t : ℝ} (hl : (l, t) ∈ C) (hr : (r, t) ∈ C)
    (hlx : l ≤ x) (hxr : x ≤ r) : (x, t) ∈ C := by
  by_cases he : l = r
  · have hx : x = l := by linarith
    simpa [hx] using hl
  have hd : 0 < r - l := sub_pos.mpr (lt_of_le_of_ne (hlx.trans hxr) he)
  have ha : 0 ≤ (r - x) / (r - l) := div_nonneg (by linarith) hd.le
  have hb : 0 ≤ (x - l) / (r - l) := div_nonneg (by linarith) hd.le
  have hab : (r - x) / (r - l) + (x - l) / (r - l) = 1 := by
    field_simp; ring
  have h := hC hl hr ha hb hab
  have heq : ((r - x) / (r - l)) • (l, t) + ((x - l) / (r - l)) • (r, t) = (x, t) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    · field_simp; ring
    · field_simp; ring
  simpa only [heq] using h

theorem row_interval {B : Finset Lattice} (hB : IsLatticeConvex B)
    {l r x t : ℤ} (hl : (l, t) ∈ B) (hr : (r, t) ∈ B)
    (hlx : l ≤ x) (hxr : x ≤ r) : (x, t) ∈ B := by
  apply (hB (x, t)).mp
  exact horizontal_between (l := (l : ℝ)) (r := (r : ℝ))
    (windowHull_convex B) (mem_windowHull_of_mem B hl)
    (mem_windowHull_of_mem B hr) (by exact_mod_cast hlx) (by exact_mod_cast hxr)

theorem row_eq_interval {B : Finset Lattice} (hB : IsLatticeConvex B)
    (t : ℤ) (hne : (row B t).Nonempty) :
    ∃ l r : ℤ, l ≤ r ∧ row B t = (Finset.Icc l r).image (fun x => (x, t)) := by
  let X := (row B t).image Prod.fst
  have hX : X.Nonempty := hne.image _
  let l := X.min' hX
  let r := X.max' hX
  have hlmem : (l, t) ∈ B := by
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp (Finset.min'_mem X hX)
    obtain ⟨hzB, hzt⟩ := (mem_row B t z).mp hz
    have hz : z = (l,t) := Prod.ext he hzt
    simpa only [hz] using hzB
  have hrmem : (r, t) ∈ B := by
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp (Finset.max'_mem X hX)
    obtain ⟨hzB, hzt⟩ := (mem_row B t z).mp hz
    have hz : z = (r,t) := Prod.ext he hzt
    simpa only [hz] using hzB
  refine ⟨l, r, Finset.min'_le_max' X hX, ?_⟩
  ext z
  constructor
  · intro hz
    have hx : z.1 ∈ X := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    refine Finset.mem_image.mpr ⟨z.1, Finset.mem_Icc.mpr
      ⟨Finset.min'_le X _ hx, Finset.le_max' X _ hx⟩, ?_⟩
    exact Prod.ext rfl ((mem_row B t z).mp hz).2.symm
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_row B t (x,t)).mpr
      ⟨row_interval hB hlmem hrmem (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2, rfl⟩

/-- Every nonempty row consists of exactly its cardinality of consecutive sites. -/
theorem row_run {B : Finset Lattice} (hB : IsLatticeConvex B)
    (t : ℤ) (hne : (row B t).Nonempty) :
    ∃ x : ℤ, row B t = (Finset.range (row B t).card).image (fun j : ℕ => (x + (j : ℤ), t)) := by
  obtain ⟨l, r, hlr, he⟩ := row_eq_interval hB t hne
  have hc : (row B t).card = (r - l + 1).toNat := by
    rw [he, Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h)]
    simpa only [sub_add_eq_add_sub] using Int.card_Icc l r
  refine ⟨l, ?_⟩
  rw [hc, he]
  ext z
  simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x-l).toNat, by omega, ?_⟩
    apply Prod.ext <;> simp only
    omega
  · rintro ⟨j, hj, rfl⟩
    exact ⟨l + (j : ℤ), by omega, rfl⟩

structure PlusBalanced {A : Type*} [Fintype A] (θ : Lattice → A)
    (B : Finset Lattice) : Prop where
  nonempty : B.Nonempty
  latticeConvex : IsLatticeConvex B
  low : patternComplexity θ B ≤ B.card
  edge_budget : patternComplexity θ B < patternComplexity θ (base B) + (topEdge B).card
  row_card : ∀ t, lower B ≤ t → t ≤ upper B → (topEdge B).card - 1 ≤ (row B t).card

structure MinusBalanced {A : Type*} [Fintype A] (θ : Lattice → A)
    (B : Finset Lattice) : Prop where
  nonempty : B.Nonempty
  latticeConvex : IsLatticeConvex B
  low : patternComplexity θ B ≤ B.card
  edge_budget : patternComplexity θ B < patternComplexity θ (upperBase B) + (bottomEdge B).card
  row_card : ∀ t, lower B ≤ t → t ≤ upper B → (bottomEdge B).card - 1 ≤ (row B t).card

theorem latticeConvex_filter {B : Finset Lattice} (hB : IsLatticeConvex B)
    (p : Lattice → Prop) (C : Set Plane) (hC : Convex ℝ C)
    (hp : ∀ z, p z ↔ embed z ∈ C) : IsLatticeConvex (B.filter p) := by
  apply (isLatticeConvex_iff _).mpr
  intro z hz
  have hzB : z ∈ B := (hB z).mp
    (convexHull_mono (Set.image_mono (Finset.filter_subset p B)) hz)
  have hzC : embed z ∈ C := by
    apply convexHull_min _ hC hz
    rintro _ ⟨w, hw, rfl⟩
    exact (hp w).mp (Finset.mem_filter.mp hw).2
  exact Finset.mem_filter.mpr ⟨hzB, (hp z).mpr hzC⟩

theorem base_eq_filter (B : Finset Lattice) :
    base B = B.filter (fun z => z.2 < upper B) := by
  ext z
  simp only [base, topEdge, Finset.mem_sdiff, mem_row, Finset.mem_filter]
  have hz := le_upper_of_mem (B := B) (z := z)
  constructor <;> rintro ⟨h, h'⟩ <;> refine ⟨h, ?_⟩
  · have := hz h
    have hn : z.2 ≠ upper B := fun he => h' ⟨h, he⟩
    omega
  · rintro ⟨_, he⟩
    omega

theorem upperBase_eq_filter (B : Finset Lattice) :
    upperBase B = B.filter (fun z => lower B < z.2) := by
  ext z
  simp only [upperBase, bottomEdge, Finset.mem_sdiff, mem_row, Finset.mem_filter]
  have hz := lower_le_of_mem (B := B) (z := z)
  constructor <;> rintro ⟨h, h'⟩ <;> refine ⟨h, ?_⟩
  · have := hz h
    have hn : z.2 ≠ lower B := fun he => h' ⟨h, he⟩
    omega
  · rintro ⟨_, he⟩
    omega

theorem latticeConvex_base {B : Finset Lattice} (hB : IsLatticeConvex B) :
    IsLatticeConvex (base B) := by
  rw [base_eq_filter]
  convert latticeConvex_filter hB (fun z => z.2 < upper B)
    {z : Plane | z.2 < (upper B : ℝ)}
    ((convex_Iio (upper B : ℝ) : Convex ℝ (Set.Iio (upper B : ℝ))).linear_preimage
      (LinearMap.snd ℝ ℝ ℝ)) ?_ using 1
  · ext z; simp only [Finset.mem_filter]
  · intro z
    change z.2 < upper B ↔ (z.2 : ℝ) < (upper B : ℝ)
    exact_mod_cast Iff.rfl

theorem latticeConvex_upperBase {B : Finset Lattice} (hB : IsLatticeConvex B) :
    IsLatticeConvex (upperBase B) := by
  rw [upperBase_eq_filter]
  convert latticeConvex_filter hB (fun z => lower B < z.2)
    {z : Plane | (lower B : ℝ) < z.2}
    ((convex_Ioi (lower B : ℝ) : Convex ℝ (Set.Ioi (lower B : ℝ))).linear_preimage
      (LinearMap.snd ℝ ℝ ℝ)) ?_ using 1
  · ext z; simp only [Finset.mem_filter]
  · intro z
    change lower B < z.2 ↔ (lower B : ℝ) < (z.2 : ℝ)
    exact_mod_cast Iff.rfl

/-- A horizontal segment of integer length n contains at least n lattice sites. -/
theorem row_card_of_segment {B : Finset Lattice} (hB : IsLatticeConvex B)
    (t : ℤ) (n : ℕ) (l : ℝ)
    (hl : (l, (t : ℝ)) ∈ windowHull B)
    (hr : (l + (n : ℝ), (t : ℝ)) ∈ windowHull B) : n ≤ (row B t).card := by
  let f : Fin n → row B t := fun j => ⟨(⌈l⌉ + (j.val : ℤ), t), by
    apply (mem_row _ _ _).mpr
    refine ⟨(hB _).mp ?_, rfl⟩
    apply horizontal_between (l := l) (r := l + (n : ℝ))
      (windowHull_convex B) hl hr
    · change l ≤ ((⌈l⌉ + (j.val : ℤ) : ℤ) : ℝ)
      have hj : (0 : ℝ) ≤ j.val := by positivity
      push_cast
      linarith [Int.le_ceil l]
    · change (((⌈l⌉ + (j.val : ℤ)) : ℤ) : ℝ) ≤ l + (n : ℝ)
      have hj : (j.val : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
      push_cast
      linarith [Int.ceil_lt_add_one l]⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have h := congrArg (fun x : row B t => x.val.1) hij
    dsimp [f] at h
    apply Fin.ext
    omega
  simpa using Fintype.card_le_of_injective f hinj

/-- Interpolation of two equally long horizontal segments in a convex hull. -/
theorem interpolate_row_card {B : Finset Lattice} (hB : IsLatticeConvex B)
    (a b t l r : ℤ) (n : ℕ) (hab : a < b) (hat : a ≤ t) (htb : t ≤ b)
    (hla : (l,a) ∈ B) (hra : (l + (n : ℤ),a) ∈ B)
    (hlb : (r,b) ∈ B) (hrb : (r + (n : ℤ),b) ∈ B) :
    n ≤ (row B t).card := by
  let s : ℝ := ((t : ℝ) - a) / ((b : ℝ) - a)
  have hden : (0 : ℝ) < (b : ℝ) - a := by exact_mod_cast sub_pos.mpr hab
  have hs : 0 ≤ s := div_nonneg (by exact_mod_cast sub_nonneg.mpr hat) hden.le
  have hs1 : s ≤ 1 := (div_le_one hden).mpr (by exact_mod_cast sub_le_sub_right htb a)
  have hheight : (1-s) * (a : ℝ) + s * (b : ℝ) = (t : ℝ) := by
    dsimp [s]
    field_simp
    ring
  let L : ℝ := (1-s) * l + s * r
  have hl : (L, (t : ℝ)) ∈ windowHull B := by
    have h := (windowHull_convex B) (mem_windowHull_of_mem B hla)
      (mem_windowHull_of_mem B hlb) (show 0 ≤ 1-s by linarith) hs (by ring : 1-s+s=1)
    convert h using 1 <;> ext <;> simp [embed, L, hheight]
  have hr : (L + (n : ℝ), (t : ℝ)) ∈ windowHull B := by
    have h := (windowHull_convex B) (mem_windowHull_of_mem B hra)
      (mem_windowHull_of_mem B hrb) (show 0 ≤ 1-s by linarith) hs (by ring : 1-s+s=1)
    convert h using 1 <;> ext <;> simp [embed, L, hheight] <;> ring
  exact row_card_of_segment hB t n L hl hr

/-- The shorter extreme row controls every intermediate integer row. -/
theorem row_card_ge_min_edges {B : Finset Lattice} (hB : IsLatticeConvex B)
    (hne : B.Nonempty) (t : ℤ) (htl : lower B ≤ t) (htu : t ≤ upper B) :
    min (topEdge B).card (bottomEdge B).card - 1 ≤ (row B t).card := by
  let n := min (topEdge B).card (bottomEdge B).card
  have hn : 0 < n := lt_min (Finset.card_pos.mpr (topEdge_nonempty hne))
    (Finset.card_pos.mpr (bottomEdge_nonempty hne))
  by_cases he : lower B = upper B
  · have ht : t = upper B := by omega
    subst t
    change n-1 ≤ (topEdge B).card
    exact (Nat.sub_le _ _).trans (min_le_left _ _)
  have hab : lower B < upper B := lt_of_le_of_ne (lower_le_upper hne) he
  obtain ⟨l, hl⟩ := row_run hB (lower B) (bottomEdge_nonempty hne)
  obtain ⟨r, hr⟩ := row_run hB (upper B) (topEdge_nonempty hne)
  have hbottom : ∀ j : ℕ, j < n → (l + (j : ℤ), lower B) ∈ B := by
    intro j hj
    apply row_subset B (lower B)
    rw [hl]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le hj (min_le_right _ _)), rfl⟩
  have htop : ∀ j : ℕ, j < n → (r + (j : ℤ), upper B) ∈ B := by
    intro j hj
    apply row_subset B (upper B)
    rw [hr]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le hj (min_le_left _ _)), rfl⟩
  exact interpolate_row_card hB (lower B) (upper B) t l r (n-1) hab htl htu
    (by simpa using hbottom 0 hn) (hbottom (n-1) (by omega))
    (by simpa using htop 0 hn) (htop (n-1) (by omega))

/-- Lemma D.5, with its chosen orientation kept explicit. -/
theorem exists_balanced_subset {A : Type*} [Fintype A] (θ : Lattice → A)
    (S : Finset Lattice) (hne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card) :
    ∃ B ⊆ S, PlusBalanced θ B ∨ MinusBalanced θ B := by
  classical
  induction S using Finset.strongInductionOn with
  | _ B ih =>
    by_cases hchoice : (topEdge B).card ≤ (bottomEdge B).card
    · have hsub : base B ⊂ B := Finset.sdiff_ssubset
        (row_subset B (upper B)) (topEdge_nonempty hne)
      by_cases hnext : patternComplexity θ (base B) ≤ (base B).card
      · have hbne : (base B).Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty.mp hempty, patternComplexity_empty] at hnext
          simp at hnext
        obtain ⟨C, hCB, hC⟩ := ih (base B) hsub hbne (latticeConvex_base hS) hnext
        exact ⟨C, hCB.trans hsub.le, hC⟩
      · refine ⟨B, Finset.Subset.refl _, Or.inl ⟨hne, hS, hlow, ?_, ?_⟩⟩
        · have hc := Finset.card_sdiff_add_card_eq_card (row_subset B (upper B))
          change (base B).card + (topEdge B).card = B.card at hc
          omega
        · intro t htl htu
          simpa [min_eq_left hchoice] using row_card_ge_min_edges hS hne t htl htu
    · have hchoice' : (bottomEdge B).card ≤ (topEdge B).card := by omega
      have hsub : upperBase B ⊂ B := Finset.sdiff_ssubset
        (row_subset B (lower B)) (bottomEdge_nonempty hne)
      by_cases hnext : patternComplexity θ (upperBase B) ≤ (upperBase B).card
      · have hbne : (upperBase B).Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty.mp hempty, patternComplexity_empty] at hnext
          simp at hnext
        obtain ⟨C, hCB, hC⟩ := ih (upperBase B) hsub hbne (latticeConvex_upperBase hS) hnext
        exact ⟨C, hCB.trans hsub.le, hC⟩
      · refine ⟨B, Finset.Subset.refl _, Or.inr ⟨hne, hS, hlow, ?_, ?_⟩⟩
        · have hc := Finset.card_sdiff_add_card_eq_card (row_subset B (lower B))
          change (upperBase B).card + (bottomEdge B).card = B.card at hc
          omega
        · intro t htl htu
          simpa [min_eq_right hchoice'] using row_card_ge_min_edges hS hne t htl htu

end
end NivatTrial.BalancedWindows
