import ConvexNivat.Geometry.Definitions

namespace ConvexNivat

open scoped BigOperators Pointwise

private theorem embed_add_aux (a b : Lattice) : embed (a + b) = embed a + embed b := by
  ext <;> simp [embed]

private theorem embed_sub_aux (a b : Lattice) : embed (a - b) = embed a - embed b := by
  ext <;> simp [embed]

private theorem embed_nsmul_aux (n : ℕ) (a : Lattice) :
    embed (n • a) = (n : ℝ) • embed a := by
  ext <;> simp [embed, nsmul_eq_mul]

theorem embed_finset_sum {ι : Type*} (I : Finset ι) (f : ι → Lattice) :
    embed (∑ i ∈ I, f i) = ∑ i ∈ I, embed (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [embed]
  | @insert i I hi ih => simp only [Finset.sum_insert hi, embed_add_aux, ih]

theorem residual_coeff_bounds (D a : ℝ) (hD : 0 ≤ D)
    (ha0 : 0 ≤ a) (haD : a ≤ 2 * D) :
    0 ≤ a - (if D ≤ a then D else 0) ∧
      a - (if D ≤ a then D else 0) ≤ D := by
  split_ifs with h <;> constructor <;> linarith

theorem IntegralZonotope.twofold_integer_decomposition {m : ℕ}
    (Z : IntegralZonotope m) (x : Lattice)
    (hx : (1 / 2 : ℝ) • embed x ∈ Z.carrier) :
    ∃ p ∈ Z.subsetSums, ∃ q ∈ latticePoints Z.carrier, x = p + q := by
  classical
  rcases hx with ⟨t, ht, hxt⟩
  let a : Fin m → ℝ := fun i => 2 * t i
  let I := Finset.univ.filter (fun i : Fin m => (Z.degree i : ℝ) ≤ a i)
  let p : Lattice := ∑ i ∈ I, Z.endpoint i
  have hp : p ∈ Z.subsetSums := by
    apply Finset.mem_image.mpr
    exact ⟨I, Finset.mem_powerset.mpr (Finset.subset_univ _), rfl⟩
  have hxa : embed x = ∑ i : Fin m, a i • embed (Z.direction i) := by
    calc
      embed x = (2 : ℝ) • ((1 / 2 : ℝ) • embed x) := by
        simp [smul_smul]
      _ = (2 : ℝ) • ∑ i : Fin m, t i • embed (Z.direction i) := by rw [hxt]
      _ = ∑ i : Fin m, a i • embed (Z.direction i) := by
        rw [Finset.smul_sum]
        simp only [smul_smul, a]
  have hpembed : embed p = ∑ i : Fin m,
      (if (Z.degree i : ℝ) ≤ a i then (Z.degree i : ℝ) else 0) •
        embed (Z.direction i) := by
    rw [show p = ∑ i ∈ I, Z.endpoint i from rfl, embed_finset_sum]
    simp only [I, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs
    · exact embed_nsmul_aux _ _
    · simp only [zero_smul]
  refine ⟨p, hp, x - p, ?_, ?_⟩
  · change embed (x - p) ∈ Z.carrier
    refine ⟨fun i => a i - (if (Z.degree i : ℝ) ≤ a i then (Z.degree i : ℝ) else 0),
      ?_, ?_⟩
    · intro i
      apply residual_coeff_bounds _ _ (Nat.cast_nonneg _)
      · dsimp [a]; linarith [(ht i).1]
      · dsimp [a]; linarith [(ht i).2]
    · rw [embed_sub_aux, hxa, hpembed, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact (sub_smul _ _ _).symm
  · abel

namespace IntegralZonotope

private theorem subsetSum_mem_aux {m : ℕ} (Z : IntegralZonotope m) {q : Lattice}
    (hq : q ∈ Z.subsetSums) : embed q ∈ Z.carrier := by
  classical
  rcases Finset.mem_image.mp hq with ⟨I, hI, rfl⟩
  refine ⟨fun i => if i ∈ I then (Z.degree i : ℝ) else 0, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs <;> exact ⟨by positivity, by simp⟩
  · rw [embed_finset_sum]
    simp only [endpoint, embed_nsmul_aux]
    symm
    calc
      (∑ i : Fin m, (if i ∈ I then (Z.degree i : ℝ) else 0) •
        embed (Z.direction i)) =
        ∑ i : Fin m, if i ∈ I then (Z.degree i : ℝ) • embed (Z.direction i) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          split_ifs <;> simp only [zero_smul]
      _ = ∑ i ∈ I, (Z.degree i : ℝ) • embed (Z.direction i) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]

private theorem centerSum_embed {m : ℕ} (Z : IntegralZonotope m) :
    embed Z.centerSum = ∑ i : Fin m, (Z.degree i : ℝ) • embed (Z.direction i) := by
  rw [centerSum, embed_finset_sum]
  simp only [endpoint, embed_nsmul_aux]

private theorem reflected_mem {m : ℕ} (Z : IntegralZonotope m) {x : RealPlane}
    (hx : x ∈ Z.carrier) : embed Z.centerSum - x ∈ Z.carrier := by
  rcases hx with ⟨t, ht, hxt⟩
  refine ⟨fun i => (Z.degree i : ℝ) - t i, ?_, ?_⟩
  · intro i
    constructor <;> linarith [(ht i).1, (ht i).2]
  · rw [centerSum_embed, hxt, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (sub_smul _ _ _).symm

theorem central_reflection {m : ℕ} (Z : IntegralZonotope m) :
    (fun x => embed Z.centerSum - x) '' Z.carrier = Z.carrier := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact reflected_mem Z hx
  · intro x hx
    exact ⟨embed Z.centerSum - x, reflected_mem Z hx, by abel⟩

theorem reflect_latticePoint {m : ℕ} (Z : IntegralZonotope m) {q : Lattice}
    (hq : q ∈ latticePoints Z.carrier) :
    Z.centerSum - q ∈ latticePoints Z.carrier := by
  change embed (Z.centerSum - q) ∈ Z.carrier
  rw [embed_sub_aux]
  exact reflected_mem Z hq

theorem differenceBody_eq_doubled_translate {m : ℕ} (Z : IntegralZonotope m) :
    Z.carrier - Z.carrier =
      (fun x => (2 : ℝ) • x - embed Z.centerSum) '' Z.carrier := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases Set.mem_sub.mp hz with ⟨u, hu, v, hv, rfl⟩
    rcases hu with ⟨a, ha, hua⟩
    rcases hv with ⟨b, hb, hvb⟩
    refine ⟨∑ i : Fin m, ((a i + (Z.degree i : ℝ) - b i) / 2) •
      embed (Z.direction i), ?_, ?_⟩
    · refine ⟨fun i => (a i + (Z.degree i : ℝ) - b i) / 2, ?_, rfl⟩
      intro i
      constructor <;> linarith [(ha i).1, (ha i).2, (hb i).1, (hb i).2]
    · dsimp only
      rw [hua, hvb, centerSum_embed, Finset.smul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [smul_smul, ← sub_smul]
      congr 1
      ring
  · rintro z ⟨y, hy, rfl⟩
    apply Set.mem_sub.mpr
    refine ⟨y, hy, embed Z.centerSum - y, reflected_mem Z hy, ?_⟩
    dsimp only
    rw [two_smul]
    abel

theorem differenceBody_mem_iff_half_mem {m : ℕ} (Z : IntegralZonotope m)
    (d : Lattice) :
    embed d ∈ Z.carrier - Z.carrier ↔
      (1 / 2 : ℝ) • embed (d + Z.centerSum) ∈ Z.carrier := by
  rw [differenceBody_eq_doubled_translate]
  constructor
  · rintro ⟨x, hx, hxd⟩
    have he : (1 / 2 : ℝ) • embed (d + Z.centerSum) = x := by
      rw [embed_add_aux, ← hxd]
      simp [smul_smul]
    simpa only [he] using hx
  · intro hx
    refine ⟨(1 / 2 : ℝ) • embed (d + Z.centerSum), hx, ?_⟩
    dsimp only
    rw [smul_smul, embed_add_aux]
    norm_num

end IntegralZonotope

theorem lemma6_1 {m : ℕ} (Z : IntegralZonotope m) (hm : 2 ≤ m)
    (hdir : Nonparallel (Z.firstDirection hm) (Z.secondDirection hm)) :
    latticePoints (Z.carrier - Z.carrier) =
      latticePoints Z.carrier - latticePoints Z.carrier := by
  apply Set.Subset.antisymm
  · intro d hd
    have hhalf := (Z.differenceBody_mem_iff_half_mem d).mp hd
    rcases Z.twofold_integer_decomposition (d + Z.centerSum) hhalf with
      ⟨p, hp, q, hq, he⟩
    have hpZ : p ∈ latticePoints Z.carrier := by
      exact IntegralZonotope.subsetSum_mem_aux Z hp
    apply Set.mem_sub.mpr
    refine ⟨p, hpZ, Z.centerSum - q, Z.reflect_latticePoint hq, ?_⟩
    have h : d = p - (Z.centerSum - q) := by
      calc
        d = (d + Z.centerSum) - Z.centerSum := by abel
        _ = (p + q) - Z.centerSum := by rw [he]
        _ = p - (Z.centerSum - q) := by abel
    exact h.symm
  · intro d hd
    rcases Set.mem_sub.mp hd with ⟨p, hp, q, hq, rfl⟩
    change embed (p - q) ∈ Z.carrier - Z.carrier
    rw [embed_sub_aux]
    exact Set.mem_sub.mpr ⟨embed p, hp, embed q, hq, rfl⟩

theorem lemma6_1_pair {m : ℕ} (Z : IntegralZonotope m) (hm : 2 ≤ m)
    (hdir : Nonparallel (Z.firstDirection hm) (Z.secondDirection hm))
    (d : Lattice) (hd : embed d ∈ Z.carrier - Z.carrier) :
    ∃ q₀ ∈ latticePoints Z.carrier,
      ∃ q₁ ∈ latticePoints Z.carrier, d = q₁ - q₀ := by
  have hd' : d ∈ latticePoints Z.carrier - latticePoints Z.carrier := by
    rw [← lemma6_1 Z hm hdir]
    exact hd
  rcases Set.mem_sub.mp hd' with ⟨q₁, hq₁, q₀, hq₀, he⟩
  exact ⟨q₀, hq₀, q₁, hq₁, he.symm⟩

theorem corollary6_2 {m : ℕ} (Z : IntegralZonotope m) (hm : 2 ≤ m)
    (hdir : Nonparallel (Z.firstDirection hm) (Z.secondDirection hm))
    (d : Lattice) (hd : embed d ∈ Z.carrier - Z.carrier) :
    ∃ q : Lattice, q ∈ latticePoints Z.carrier ∧
      q + d ∈ latticePoints Z.carrier := by
  rcases lemma6_1_pair Z hm hdir d hd with ⟨q₀, hq₀, q₁, hq₁, he⟩
  refine ⟨q₀, hq₀, ?_⟩
  have h : q₀ + d = q₁ := by rw [he]; abel
  simpa only [h] using hq₁

end ConvexNivat
