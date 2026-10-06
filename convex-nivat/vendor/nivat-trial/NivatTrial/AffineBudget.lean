import NivatTrial.Quadratic

/-! The linear-algebra part of Lemma 2.5, over the complex numbers throughout.

The bounded factorization premise is exactly the algebraic-geometric input:
affine relations factor by a fixed polynomial, with quotient support in `R`.
The Newton-polygon theorem producing that premise is not asserted here.
-/

namespace NivatTrial.AffineBudget

open NivatTrial.Algebra NivatTrial.Quadratic
open scoped Classical

noncomputable section

def windowLinear (S : Finset G) : (S → ℂ) →ₗ[ℂ] Laurent where
  toFun := windowPolynomial S
  map_add' c d := by
    simp [windowPolynomial, AddMonoidAlgebra.single_add, Finset.sum_add_distrib]
  map_smul' a c := by
    simp [windowPolynomial, Finset.smul_sum, AddMonoidAlgebra.smul_single]

theorem windowLinear_injective (S : Finset G) : Function.Injective (windowLinear S) := by
  intro c d h
  funext s
  have hs := congrArg (fun f : Laurent => f.coeff (s : G)) h
  change (windowPolynomial S c).coeff s = (windowPolynomial S d).coeff s at hs
  simpa only [windowPolynomial_coeff] using hs

theorem windowPolynomial_from_support (R : Finset G) (g : Laurent)
    (hg : g.coeff.support ⊆ R) : windowPolynomial R (fun r => g.coeff r) = g := by
  ext z
  by_cases hz : z ∈ R
  · exact windowPolynomial_coeff R (fun r => g.coeff r) ⟨z, hz⟩
  · have hz' : g.coeff z = 0 := by
      by_contra h
      exact hz (hg (Finsupp.mem_support_iff.mpr h))
    have hs : ∀ r : R, (r : G) ≠ z := by
      intro r heq
      exact hz (heq ▸ r.property)
    simp [windowPolynomial, Finsupp.single_apply, hs, hz']

def multiplyWindow (A : Laurent) (R : Finset G) : (R → ℂ) →ₗ[ℂ] Laurent where
  toFun c := A * windowLinear R c
  map_add' c d := by rw [map_add, mul_add]
  map_smul' a c := by rw [map_smul, mul_smul_comm]; rfl

theorem multiplyWindow_finrank_range (A : Laurent) (R : Finset G) :
    Module.finrank ℂ (multiplyWindow A R).range ≤ R.card := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
    (multiplyWindow A R).finrank_range_le

variable {A : Type*} [Fintype A]

def relationPolynomial (S : Finset G) : (Option S → ℂ) →ₗ[ℂ] Laurent where
  toFun c := windowPolynomial S (fun s => c (some s))
  map_add' c d := (windowLinear S).map_add _ _
  map_smul' a c := (windowLinear S).map_smul a _

theorem affinePatternMap_eq_combination (θ : G → A) (S : Finset G) (w : A → ℂ)
    (c : Option S → ℂ) :
    affinePatternMap θ S w c =
      c none • (fun _ => 1) + ∑ s : S, c (some s) • coordinateObservation θ S w s := by
  funext p
  simp [affinePatternMap, coordinateObservation, smul_eq_mul]

theorem affinePatternMap_range (θ : G → A) (S : Finset G) (w : A → ℂ) :
    (affinePatternMap θ S w).range = affineSpace θ S w := by
  apply le_antisymm
  · rintro f ⟨c, rfl⟩
    rw [affinePatternMap_eq_combination]
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      exact Submodule.subset_span (Set.mem_insert _ _)
    · apply Submodule.sum_mem
      intro s _
      apply Submodule.smul_mem
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self s))
  · apply Submodule.span_le.mpr
    intro f hf
    rcases hf with rfl | ⟨s, rfl⟩
    · refine ⟨Pi.single none 1, ?_⟩
      funext p
      simp [affinePatternMap]
    · refine ⟨Pi.single (some s) 1, ?_⟩
      funext p
      simp [affinePatternMap, coordinateObservation, Pi.single_apply]

theorem relationPolynomial_support (S : Finset G) (c : Option S → ℂ) :
    (relationPolynomial S c).coeff.support ⊆ S := by
  intro z hz
  by_contra hnot
  have hs : ∀ s : S, (s : G) ≠ z := fun s h => hnot (h ▸ s.property)
  have hzero : (relationPolynomial S c).coeff z = 0 := by
    simp [relationPolynomial, windowPolynomial, Finsupp.single_apply, hs]
  exact (Finsupp.mem_support_iff.mp hz) hzero

theorem kernel_affine_relation (θ : G → A) (S : Finset G) (w : A → ℂ)
    (c : (affinePatternMap θ S w).ker) :
    act (relationPolynomial S c.val) (fun z => w (θ z)) = fun _ => -c.val none := by
  funext z
  have hp := congrFun c.property (⟨patternAt θ S z, ⟨z, rfl⟩⟩ : patternSet θ S)
  have h : c.val none + ∑ s : S, c.val (some s) * w (θ (z + s)) = 0 := hp
  change act (windowPolynomial S (fun s => c.val (some s))) (fun z => w (θ z)) z = _
  rw [act_windowPolynomial]
  linear_combination h

theorem relationPolynomial_kernel_injective (θ : G → A) (S : Finset G) (w : A → ℂ) :
    Function.Injective (fun c : (affinePatternMap θ S w).ker => relationPolynomial S c.val) := by
  intro c d h
  have hs : ∀ s : S, c.val (some s) = d.val (some s) := by
    intro s
    have hcoeff := congrArg (fun f : Laurent => f.coeff (s : G)) h
    change (windowPolynomial S (fun t => c.val (some t))).coeff s =
      (windowPolynomial S (fun t => d.val (some t))).coeff s at hcoeff
    simpa only [windowPolynomial_coeff] using hcoeff
  have hnone : c.val none = d.val none := by
    let p : patternSet θ S := ⟨patternAt θ S 0, ⟨0, rfl⟩⟩
    have hc := congrFun c.property p
    have hd := congrFun d.property p
    change c.val none + ∑ s : S, c.val (some s) * w (p.val s) = 0 at hc
    change d.val none + ∑ s : S, d.val (some s) * w (p.val s) = 0 at hd
    simp only [hs] at hc
    exact add_right_cancel (hc.trans hd.symm)
  apply Subtype.ext
  funext i
  cases i with
  | none => exact hnone
  | some s => exact hs s

/-- The dimension estimate is unconditional once the explicitly stated bounded
factorization property has been supplied; no division map is postulated. -/
theorem affine_dimension_budget (θ : G → A) (S R : Finset G) (w : A → ℂ)
    (a : Laurent)
    (hfactor : ∀ f : Laurent, f.coeff.support ⊆ S →
      (∃ b : ℂ, act f (fun z => w (θ z)) = fun _ => b) →
      ∃ g : Laurent, g.coeff.support ⊆ R ∧ f = a * g) :
    S.card + 1 ≤ Module.finrank ℂ (affineSpace θ S w) + R.card := by
  let T := affinePatternMap θ S w
  let F : T.ker →ₗ[ℂ] Laurent := (relationPolynomial S).comp T.ker.subtype
  have hFrange : ∀ c : T.ker, F c ∈ (multiplyWindow a R).range := by
    intro c
    obtain ⟨g, hg, heq⟩ := hfactor (relationPolynomial S c.val)
      (relationPolynomial_support S c.val) ⟨-c.val none, kernel_affine_relation θ S w c⟩
    refine ⟨fun r => g.coeff r, ?_⟩
    change a * windowPolynomial R (fun r => g.coeff r) = relationPolynomial S c.val
    rw [windowPolynomial_from_support R g hg]
    exact heq.symm
  let F' : T.ker →ₗ[ℂ] (multiplyWindow a R).range := F.codRestrict _ hFrange
  have hF' : Function.Injective F' := by
    intro c d h
    apply relationPolynomial_kernel_injective θ S w
    exact congrArg Subtype.val h
  have hker : Module.finrank ℂ T.ker ≤ R.card :=
    (LinearMap.finrank_le_finrank_of_injective hF').trans
      (multiplyWindow_finrank_range a R)
  have hrank := T.finrank_range_add_finrank_ker
  have hrange : T.range = affineSpace θ S w := affinePatternMap_range θ S w
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option,
    Fintype.card_coe] at hrank
  calc
    S.card + 1 = Module.finrank ℂ T.range + Module.finrank ℂ T.ker := hrank.symm
    _ ≤ Module.finrank ℂ T.range + R.card := Nat.add_le_add_left hker _
    _ = Module.finrank ℂ (affineSpace θ S w) + R.card := by rw [hrange]

/-- The final dimension cancellation, with both geometric inputs exposed:
bounded division and placement of the two witness sites in every window.
This does not assert that these inputs hold for an arbitrary convex window. -/
theorem complexity_of_bounded_factorization_and_witness
    (θ : G → A) (S R : Finset G) (w : A → ℂ) (a D : Laurent) (q₀ q₁ : G)
    (hfactor : ∀ f : Laurent, f.coeff.support ⊆ S →
      (∃ b : ℂ, act f (fun z => w (θ z)) = fun _ => b) →
      ∃ g : Laurent, g.coeff.support ⊆ R ∧ f = a * g)
    (h₀ : ∀ r : R, (r : G) + q₀ ∈ S) (h₁ : ∀ r : R, (r : G) + q₁ ∈ S)
    (hconstant : ∀ b : ℂ, act D (fun _ => b) = 0)
    (hlinear : act D (fun z => w (θ z)) = 0)
    (hfinite : (Function.support (act D (twoPoint (fun x => w (θ x)) q₀ q₁))).Finite)
    (hnonzero : act D (twoPoint (fun x => w (θ x)) q₀ q₁) ≠ 0) :
    S.card + 1 ≤ patternComplexity θ S := by
  exact (affine_dimension_budget θ S R w a hfactor).trans
    (quadratic_dimension_bound θ S R w D q₀ q₁ h₀ h₁ hconstant hlinear hfinite hnonzero)

end

end NivatTrial.AffineBudget
