import NivatTrial.Geometry

/-! Integer points in a lattice zonotope and in its difference body.

The argument is specific to zonotopes and works without any dimension,
primitivity, nondegeneracy, or triangulation hypothesis. For a signed coefficient
in `[-1,1]`, select the endpoint `1` if the coefficient is nonnegative, and `0`
otherwise. Subtracting the signed coefficient leaves a coefficient in `[0,1]`.
-/

namespace NivatTrial.Zonotope

open scoped BigOperators Pointwise

abbrev Lattice := ℤ × ℤ
abbrev Plane := ℝ × ℝ

def embed (z : Lattice) : Plane := (z.1, z.2)

@[simp] theorem embed_zero : embed 0 = 0 := by
  ext <;> simp [embed]

@[simp] theorem embed_add (x y : Lattice) : embed (x + y) = embed x + embed y := by
  ext <;> simp [embed]

@[simp] theorem embed_neg (x : Lattice) : embed (-x) = -embed x := by
  ext <;> simp [embed]

@[simp] theorem embed_sub (x y : Lattice) : embed (x - y) = embed x - embed y := by
  ext <;> simp [embed]

def embedHom : Lattice →+ Plane where
  toFun := embed
  map_zero' := embed_zero
  map_add' := embed_add

theorem embed_injective : Function.Injective embed := by
  intro x y h
  apply Prod.ext
  · have hx : (x.1 : ℝ) = y.1 := congrArg Prod.fst h
    exact_mod_cast hx
  · have hy : (x.2 : ℝ) = y.2 := congrArg Prod.snd h
    exact_mod_cast hy

@[simp] theorem embed_nsmul (n : ℕ) (x : Lattice) :
    embed (n • x) = (n : ℝ) • embed x := by
  ext <;> simp [embed, nsmul_eq_mul, smul_eq_mul]

@[simp] theorem embed_zsmul (n : ℤ) (x : Lattice) :
    embed (n • x) = (n : ℝ) • embed x := by
  ext <;> simp [embed, zsmul_eq_mul, smul_eq_mul]

@[simp] theorem embed_sum {ι : Type*} (s : Finset ι) (g : ι → Lattice) :
    embed (∑ i ∈ s, g i) = ∑ i ∈ s, embed (g i) :=
  map_sum embedHom g s

noncomputable section

variable {ι : Type*} [Fintype ι]

def coeffPoint (g : ι → Lattice) (t : ι → ℝ) : Plane :=
  ∑ i, t i • embed (g i)

def zonotope (g : ι → Lattice) : Set Plane :=
  {x | ∃ t : ι → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ coeffPoint g t = x}

@[simp] theorem mem_zonotope (g : ι → Lattice) (x : Plane) :
    x ∈ zonotope g ↔
      ∃ t : ι → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ coeffPoint g t = x := Iff.rfl

theorem coeffPoint_add (g : ι → Lattice) (t u : ι → ℝ) :
    coeffPoint g (fun i => t i + u i) = coeffPoint g t + coeffPoint g u := by
  simp only [coeffPoint, add_smul, Finset.sum_add_distrib]

theorem coeffPoint_sub (g : ι → Lattice) (t u : ι → ℝ) :
    coeffPoint g (fun i => t i - u i) = coeffPoint g t - coeffPoint g u := by
  simp only [coeffPoint, sub_smul, Finset.sum_sub_distrib]

theorem coeffPoint_smul (g : ι → Lattice) (a : ℝ) (t : ι → ℝ) :
    coeffPoint g (fun i => a * t i) = a • coeffPoint g t := by
  simp only [coeffPoint, mul_smul, Finset.smul_sum]

theorem zero_mem (g : ι → Lattice) : (0 : Plane) ∈ zonotope g := by
  refine ⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩, ?_⟩
  simp [coeffPoint]

theorem coeffPoint_one (g : ι → Lattice) :
    coeffPoint g (fun _ => 1) = embed (∑ i, g i) := by
  simp [coeffPoint]

theorem total_mem (g : ι → Lattice) : embed (∑ i, g i) ∈ zonotope g := by
  exact ⟨fun _ => 1, fun _ => ⟨zero_le_one, le_rfl⟩, coeffPoint_one g⟩

/-- The coefficient-image definition is the usual Minkowski sum of segments. -/
theorem eq_sum_segments (g : ι → Lattice) :
    zonotope g = ∑ i, segment ℝ (0 : Plane) (embed (g i)) := by
  ext x
  rw [Set.mem_fintype_sum]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => t i • embed (g i), ?_, rfl⟩
    intro i
    rw [segment_eq_image]
    exact ⟨t i, ht i, by simp⟩
  · rintro ⟨f, hf, hsum⟩
    have hrepr : ∀ i, ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧ t • embed (g i) = f i := by
      intro i
      have hi := hf i
      rw [segment_eq_image] at hi
      obtain ⟨t, ht, heq⟩ := hi
      exact ⟨t, ht, by simpa using heq⟩
    choose t ht heq using hrepr
    exact ⟨t, ht, by simp only [coeffPoint, heq]; exact hsum⟩

theorem convex (g : ι → Lattice) : Convex ℝ (zonotope g) := by
  rw [eq_sum_segments]
  exact convex_sum _ (fun _ _ => convex_segment _ _)

/-- Membership in the difference body has the actual signed coefficient form. -/
theorem diff_mem_iff_coeff (g : ι → Lattice) (x : Plane) :
    x ∈ zonotope g - zonotope g ↔
      ∃ s : ι → ℝ, (∀ i, -1 ≤ s i ∧ s i ≤ 1) ∧ coeffPoint g s = x := by
  rw [Set.mem_sub]
  constructor
  · rintro ⟨a, ⟨t, ht, rfl⟩, b, ⟨u, hu, rfl⟩, h⟩
    refine ⟨fun i => t i - u i, ?_, ?_⟩
    · intro i
      obtain ⟨ht0, ht1⟩ := ht i
      obtain ⟨hu0, hu1⟩ := hu i
      constructor <;> linarith
    · exact (coeffPoint_sub g t u).trans h
  · rintro ⟨s, hs, rfl⟩
    let t : ι → ℝ := fun i => max (s i) 0
    let u : ι → ℝ := fun i => max (-s i) 0
    have ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1 := by
      intro i
      exact ⟨le_max_right _ _, max_le (hs i).2 zero_le_one⟩
    have hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1 := by
      intro i
      exact ⟨le_max_right _ _, max_le (by linarith [(hs i).1]) zero_le_one⟩
    have htu : (fun i => t i - u i) = s := by
      funext i
      dsimp [t, u]
      by_cases hi : 0 ≤ s i
      · rw [max_eq_left hi, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right (le_of_not_ge hi), max_eq_left (by linarith)]
        ring
    refine ⟨coeffPoint g t, ⟨t, ht, rfl⟩, coeffPoint g u, ⟨u, hu, rfl⟩, ?_⟩
    rw [← coeffPoint_sub, htu]

/-- Every integer point in the difference of an integer zonotope is the
difference of two integer points of that same zonotope. -/
theorem diff_points (g : ι → Lattice) (d : Lattice)
    (hd : embed d ∈ zonotope g - zonotope g) :
    ∃ q₀ q₁ : Lattice, embed q₀ ∈ zonotope g ∧ embed q₁ ∈ zonotope g ∧ d = q₁ - q₀ := by
  classical
  obtain ⟨s, hs, hsum⟩ := (diff_mem_iff_coeff g (embed d)).mp hd
  let ε : ι → ℝ := fun i => if 0 ≤ s i then 1 else 0
  let p : Lattice := ∑ i, if 0 ≤ s i then g i else 0
  have hε : ∀ i, 0 ≤ ε i ∧ ε i ≤ 1 := by
    intro i
    dsimp [ε]
    split_ifs <;> norm_num
  have hp : coeffPoint g ε = embed p := by
    simp only [p, embed_sum, coeffPoint]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [ε]
    split_ifs <;> simp
  have ht : ∀ i, 0 ≤ ε i - s i ∧ ε i - s i ≤ 1 := by
    intro i
    dsimp [ε]
    split_ifs with hi
    · constructor <;> linarith [(hs i).2]
    · constructor <;> linarith [(hs i).1]
  have hq : embed (p - d) ∈ zonotope g := by
    refine ⟨fun i => ε i - s i, ht, ?_⟩
    rw [coeffPoint_sub, hp, hsum, embed_sub]
  exact ⟨p - d, p, hq, ⟨ε, hε, hp⟩, by abel⟩

theorem diff_points_iff (g : ι → Lattice) (d : Lattice) :
    embed d ∈ zonotope g - zonotope g ↔
      ∃ q₀ q₁ : Lattice, embed q₀ ∈ zonotope g ∧ embed q₁ ∈ zonotope g ∧ d = q₁ - q₀ := by
  constructor
  · exact diff_points g d
  · rintro ⟨q₀, q₁, h₀, h₁, rfl⟩
    exact Set.mem_sub.mpr ⟨embed q₁, h₁, embed q₀, h₀, (embed_sub q₁ q₀).symm⟩

def latticePoints (Z : Set Plane) : Set Lattice := embed ⁻¹' Z

/-- The set equality of Lemma 6.1, with intersections with the lattice
represented by inverse images under its embedding. -/
theorem latticePoints_diff (g : ι → Lattice) :
    latticePoints (zonotope g - zonotope g) =
      latticePoints (zonotope g) - latticePoints (zonotope g) := by
  ext d
  change embed d ∈ zonotope g - zonotope g ↔ _
  rw [diff_points_iff, Set.mem_sub]
  constructor
  · rintro ⟨q₀, q₁, h₀, h₁, hd⟩
    exact ⟨q₁, h₁, q₀, h₀, hd.symm⟩
  · rintro ⟨q₁, h₁, q₀, h₀, hd⟩
    exact ⟨q₀, q₁, h₀, h₁, hd.symm⟩

/-- Scalar normalization allows generators of length zero. -/
theorem exists_unit_mul {d c : ℝ} (hd : 0 ≤ d) (hc : 0 ≤ c ∧ c ≤ d) :
    ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧ t * d = c := by
  by_cases hd0 : d = 0
  · have hc0 : c = 0 := by linarith
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [hd0, hc0]⟩
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    exact ⟨c / d, ⟨div_nonneg hc.1 hd, (div_le_one hdpos).mpr hc.2⟩,
      div_mul_cancel₀ c hd0⟩

/-- Match the paper's coefficients in `[0,d_i]` to unit-interval generators. -/
theorem scaled_coeff_mem (v : ι → Lattice) (d : ι → ℕ) (x : Plane) :
    x ∈ zonotope (fun i => d i • v i) ↔
      ∃ c : ι → ℝ, (∀ i, 0 ≤ c i ∧ c i ≤ (d i : ℝ)) ∧
        (∑ i, c i • embed (v i)) = x := by
  constructor
  · rintro ⟨t, ht, hsum⟩
    refine ⟨fun i => t i * d i, ?_, ?_⟩
    · intro i
      have hd : 0 ≤ (d i : ℝ) := Nat.cast_nonneg _
      constructor
      · exact mul_nonneg (ht i).1 hd
      · nlinarith [(ht i).2]
    · simpa only [coeffPoint, embed_nsmul, smul_smul] using hsum
  · rintro ⟨c, hc, hsum⟩
    have hrepr : ∀ i, ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧ t * (d i : ℝ) = c i :=
      fun i => exists_unit_mul (Nat.cast_nonneg _) (hc i)
    choose t ht heq using hrepr
    refine ⟨t, ht, ?_⟩
    simpa only [coeffPoint, embed_nsmul, smul_smul, heq] using hsum

/-- Match the signed region used by the quotient algebra to the difference body. -/
theorem scaled_diff_mem (v : ι → Lattice) (d : ι → ℕ) (x : Plane) :
    x ∈ zonotope (fun i => d i • v i) - zonotope (fun i => d i • v i) ↔
      ∃ s : ι → ℝ, (∀ i, -(d i : ℝ) ≤ s i ∧ s i ≤ (d i : ℝ)) ∧
        (∑ i, s i • embed (v i)) = x := by
  rw [Set.mem_sub]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨c, hc, hca⟩ := (scaled_coeff_mem v d a).mp ha
    obtain ⟨e, he, heb⟩ := (scaled_coeff_mem v d b).mp hb
    refine ⟨fun i => c i - e i, ?_, ?_⟩
    · intro i
      constructor <;> linarith [(hc i).1, (hc i).2, (he i).1, (he i).2]
    · simp only [sub_smul, Finset.sum_sub_distrib, hca, heb]
      exact hab
  · rintro ⟨s, hs, hsum⟩
    let c : ι → ℝ := fun i => max (s i) 0
    let e : ι → ℝ := fun i => max (-s i) 0
    have hc : ∀ i, 0 ≤ c i ∧ c i ≤ (d i : ℝ) := by
      intro i
      exact ⟨le_max_right _ _, max_le (hs i).2 (Nat.cast_nonneg _)⟩
    have he : ∀ i, 0 ≤ e i ∧ e i ≤ (d i : ℝ) := by
      intro i
      exact ⟨le_max_right _ _, max_le (by linarith [(hs i).1]) (Nat.cast_nonneg _)⟩
    have hce : (fun i => c i - e i) = s := by
      funext i
      dsimp [c, e]
      by_cases hi : 0 ≤ s i
      · rw [max_eq_left hi, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right (le_of_not_ge hi), max_eq_left (by linarith)]
        ring
    refine ⟨∑ i, c i • embed (v i), (scaled_coeff_mem v d _).mpr ⟨c, hc, rfl⟩,
      ∑ i, e i • embed (v i), (scaled_coeff_mem v d _).mpr ⟨e, he, rfl⟩, ?_⟩
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_smul]
    change coeffPoint v (fun i => c i - e i) = x
    rw [hce]
    exact hsum

end

end NivatTrial.Zonotope
