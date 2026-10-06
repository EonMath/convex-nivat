import Mathlib

namespace NivatTrial

abbrev Lattice := ℤ × ℤ

section Patterns

variable {A : Type*} [Fintype A]

/-- The pattern seen in the finite window `S`, translated by `u`. -/
def patternAt (θ : Lattice → A) (S : Finset Lattice) (u : Lattice) : S → A :=
  fun s => θ (u + s)

/-- All patterns that actually occur in the configuration. -/
def patternSet (θ : Lattice → A) (S : Finset Lattice) : Set (S → A) :=
  Set.range (patternAt θ S)

/-- The number of distinct patterns that actually occur. -/
noncomputable def patternComplexity (θ : Lattice → A) (S : Finset Lattice) : ℕ :=
  Nat.card (patternSet θ S)

noncomputable instance patternSetFintype (θ : Lattice → A) (S : Finset Lattice) :
    Fintype (patternSet θ S) :=
  Fintype.ofFinite _

/-- The constant and coordinate observations, regarded as functions on occurring patterns. -/
noncomputable def affinePatternMap (θ : Lattice → A) (S : Finset Lattice)
    (w : A → ℂ) : (Option S → ℂ) →ₗ[ℂ] (patternSet θ S → ℂ) where
  toFun c p := c none + ∑ s : S, c (some s) * w (p.val s)
  map_add' c d := by
    funext p
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r c := by
    funext p
    simp [smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

/-- Low pattern complexity forces a nontrivial affine relation between coordinate
observations. The dependence is deduced from the actual pattern count. -/
theorem exists_affine_pattern_relation (θ : Lattice → A) (S : Finset Lattice)
    (w : A → ℂ) (hcomplexity : patternComplexity θ S ≤ S.card) :
    ∃ c : S → ℂ, c ≠ 0 ∧ ∃ b : ℂ,
      ∀ u : Lattice, ∑ s : S, c s * w (θ (u + s)) = b := by
  classical
  let T := affinePatternMap θ S w
  have hnot : ¬Function.Injective T := by
    intro hinj
    have hdim := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_option,
      Fintype.card_coe] at hdim
    have hcard : Fintype.card (patternSet θ S) ≤ S.card := by
      simpa only [patternComplexity, Nat.card_eq_fintype_card] using hcomplexity
    omega
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnot
  let d : Option S → ℂ := x - y
  have hd : d ≠ 0 := sub_ne_zero.mpr hne
  have hTd : T d = 0 := by
    rw [show d = x - y from rfl, map_sub, hxy, sub_self]
  let c : S → ℂ := fun s => d (some s)
  have hc : c ≠ 0 := by
    intro hzero
    have hs : ∀ s : S, d (some s) = 0 := fun s => congrFun hzero s
    let p : patternSet θ S := ⟨patternAt θ S 0, ⟨0, rfl⟩⟩
    have hnone : d none = 0 := by
      have hp := congrFun hTd p
      simpa [T, affinePatternMap, hs] using hp
    apply hd
    funext i
    cases i with
    | none => exact hnone
    | some s => exact hs s
  refine ⟨c, hc, -d none, ?_⟩
  intro u
  let p : patternSet θ S := ⟨patternAt θ S u, ⟨u, rfl⟩⟩
  have hu : d none + ∑ s : S, c s * w (θ (u + s)) = 0 := by
    have hp := congrFun hTd p
    simpa [T, affinePatternMap, p, patternAt, c] using hp
  linear_combination hu

open scoped Classical

/-- Proposition 1.3's affine relation for the indicator of a chosen letter. -/
theorem exists_indicator_affine_relation (θ : Lattice → A) (S : Finset Lattice)
    (a : A) (hcomplexity : patternComplexity θ S ≤ S.card) :
    ∃ c : S → ℂ, c ≠ 0 ∧ ∃ b : ℂ,
      ∀ u : Lattice,
        ∑ s : S, c s * (if θ (u + s) = a then (1 : ℂ) else 0) = b := by
  classical
  exact exists_affine_pattern_relation θ S
    (fun x => if x = a then 1 else 0) hcomplexity

end Patterns

end NivatTrial
