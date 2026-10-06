import ConvexNivat.ExternalDynamicsHelpers.BoyleLindGeometry

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

private theorem split_abs_bound (r q a : ℝ) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (ha : |a| ≤ r + q) : ∃ b c : ℝ, |b| ≤ r ∧ |c| ≤ q ∧ a = b + c := by
  rw [abs_le] at ha
  by_cases hlo : a < -r
  · refine ⟨-r, a + r, ?_, ?_, by ring⟩
    · simpa [abs_of_nonneg hr]
    · rw [abs_le]
      constructor <;> linarith
  · by_cases hhi : r < a
    · refine ⟨r, a - r, ?_, ?_, by ring⟩
      · simpa [abs_of_nonneg hr]
      · rw [abs_le]
        constructor <;> linarith
    · refine ⟨a, 0, ?_, by simpa, by ring⟩
      rw [abs_le]
      constructor <;> linarith

private theorem realDot_add (x y n : RealPlane) :
    realDot (x + y) n = realDot x n + realDot y n := by
  simp only [realDot, Prod.fst_add, Prod.snd_add]
  ring

private theorem inverse_normal_coordinates (n : RealPlane)
    (hs : n.1 ^ 2 + n.2 ^ 2 = 1) (a b : ℝ) :
    realDot (b * n.1 - a * n.2, b * n.2 + a * n.1) (realQuarterTurn n) = a ∧
    realDot (b * n.1 - a * n.2, b * n.2 + a * n.1) n = b := by
  simp only [realDot, realQuarterTurn]
  constructor <;> nlinarith [congrArg (fun z : ℝ => a * z) hs,
    congrArg (fun z : ℝ => b * z) hs]

private theorem reconstruct_normal_coordinates (n x : RealPlane)
    (hs : n.1 ^ 2 + n.2 ^ 2 = 1) :
    x = (realDot x n * n.1 - realDot x (realQuarterTurn n) * n.2,
      realDot x n * n.2 + realDot x (realQuarterTurn n) * n.1) := by
  apply Prod.ext <;> simp only [realDot, realQuarterTurn]
  · nlinarith [congrArg (fun z : ℝ => x.1 * z) hs]
  · nlinarith [congrArg (fun z : ℝ => x.2 * z) hs]

/-- Exact Euclidean orthogonal-box identity (3--1). -/
theorem lineBox_minkowski_sum (n : RealPlane) (hn : n ∈ unitNormals)
    (r t q s : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    realMinkowskiSum (lineBox n r t) (lineBox n q s) = lineBox n (r + q) (t + s) := by
  have hn2 : n.1 ^ 2 + n.2 ^ 2 = 1 := by
    have hp := planeNorm_sq n
    change planeNorm n = 1 at hn
    rw [hn] at hp
    nlinarith
  ext x
  constructor
  · rintro ⟨e, he, f, hf, rfl⟩
    change |realDot (e + f) (realQuarterTurn n)| ≤ r + q ∧
      |realDot (e + f) n| ≤ t + s
    change |realDot e (realQuarterTurn n)| ≤ r ∧ |realDot e n| ≤ t at he
    change |realDot f (realQuarterTurn n)| ≤ q ∧ |realDot f n| ≤ s at hf
    simp only [realDot_add]
    constructor
    · exact (abs_add_le _ _).trans (add_le_add he.1 hf.1)
    · exact (abs_add_le _ _).trans (add_le_add he.2 hf.2)
  · intro hx
    change |realDot x (realQuarterTurn n)| ≤ r + q ∧ |realDot x n| ≤ t + s at hx
    obtain ⟨a, c, ha, hc, hac⟩ := split_abs_bound r q _ hr hq hx.1
    obtain ⟨b, d, hb, hd, hbd⟩ := split_abs_bound t s _ ht hs hx.2
    refine ⟨(b * n.1 - a * n.2, b * n.2 + a * n.1), ?_,
      (d * n.1 - c * n.2, d * n.2 + c * n.1), ?_, ?_⟩
    · have he := inverse_normal_coordinates n hn2 a b
      change |realDot _ (realQuarterTurn n)| ≤ r ∧ |realDot _ n| ≤ t
      rw [he.1, he.2]
      exact ⟨ha, hb⟩
    · have hf := inverse_normal_coordinates n hn2 c d
      change |realDot _ (realQuarterTurn n)| ≤ q ∧ |realDot _ n| ≤ s
      rw [hf.1, hf.2]
      exact ⟨hc, hd⟩
    · rw [reconstruct_normal_coordinates n x hn2, hac, hbd]
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

end
end ConvexNivat.ExternalDynamicsHelpers
