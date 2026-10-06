import NivatTrial.Strips
import NivatTrial.Quadratic

/-! The nonzero two-point witness argument of Lemma 4.2. -/

namespace NivatTrial.Witness

open NivatTrial.Algebra NivatTrial.Geometry NivatTrial.Quadratic
open scoped Classical

noncomputable section

def SupportedInStrip (f : G → ℂ) (v : G) (a b : ℤ) : Prop :=
  ∀ z, f z ≠ 0 → a ≤ det v z ∧ det v z ≤ b

theorem strip_support_translate (f : G → ℂ) (v t : G) (a b : ℤ)
    (hf : SupportedInStrip f v a b) :
    SupportedInStrip (fun z => f (z + t)) v (a - det v t) (b - det v t) := by
  intro z hz
  have h := hf (z + t) hz
  rw [det_add_right] at h
  omega

theorem finite_support_product (f g : G → ℂ) (v w : G) (a b c d : ℤ)
    (hindependent : det v w ≠ 0)
    (hf : SupportedInStrip f v a b) (hg : SupportedInStrip g w c d) :
    (Function.support (fun z => f z * g z)).Finite := by
  apply (finite_strip_intersection v w hindependent a b c d).subset
  intro z hz
  have hne : f z * g z ≠ 0 := hz
  exact ⟨hf z (mul_ne_zero_iff.mp hne).1, hg z (mul_ne_zero_iff.mp hne).2⟩

theorem finite_support_shifted_product (f g : G → ℂ) (v w t : G) (a b c d : ℤ)
    (hindependent : det v w ≠ 0)
    (hf : SupportedInStrip f v a b) (hg : SupportedInStrip g w c d) :
    (Function.support (fun z => f z * g (z + t))).Finite := by
  exact finite_support_product f (fun z => g (z + t)) v w a b
    (c - det w t) (d - det w t) hindependent hf (strip_support_translate g w t c d hg)

theorem exists_nonzero_shifted_product (f g : G → ℂ) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ t : G, (fun z => f z * g (z + t)) ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := Function.ne_iff.mp hf
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := Function.ne_iff.mp hg
  refine ⟨y - x, ?_⟩
  intro hzero
  have h := congrFun hzero x
  have hxy : x + (y - x) = y := by abel
  simp only [hxy, Pi.zero_apply] at h
  exact mul_ne_zero hx hy h

theorem twoPoint_translate (η : G → ℂ) (u v : G) :
    twoPoint η u v = fun z => twoPoint η 0 (v - u) (z + u) := by
  funext z
  have h : z + u + (v - u) = z + v := by abel
  simp [twoPoint, h]

theorem all_pairs_annihilated (D : Laurent) (η : G → ℂ)
    (h : ∀ d : G, act D (twoPoint η 0 d) = 0) (u v : G) :
    act D (twoPoint η u v) = 0 := by
  rw [twoPoint_translate]
  funext z
  rw [NivatTrial.Differences.act_translate, h]
  rfl

/-- Expanding a product of two polynomial observations produces only two-point
observations. No multiplication rule for finite differences is assumed. -/
theorem polynomial_product_expansion (f g : Laurent) (η : G → ℂ) (t : G) :
    (fun z => act f η z * act g η (z + t)) =
      ∑ u ∈ f.coeff.support, ∑ v ∈ g.coeff.support,
        (f.coeff u * g.coeff v) • twoPoint η u (t + v) := by
  funext z
  simp [act, Finsupp.sum, twoPoint, Finset.mul_sum,
    smul_eq_mul, add_assoc, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]

theorem annihilate_product_of_pair_annihilation (D f g : Laurent) (η : G → ℂ)
    (h : ∀ d : G, act D (twoPoint η 0 d) = 0) (t : G) :
    act D (fun z => act f η z * act g η (z + t)) = 0 := by
  change actLinear D (fun z => act f η z * act g η (z + t)) = 0
  rw [polynomial_product_expansion]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  change (f.coeff u * g.coeff v) • act D (twoPoint η u (t + v)) = 0
  rw [all_pairs_annihilated D η h]
  simp

/-- Lemma 4.2's nonvanishing argument, supplied with the strip-supported
nonzero components established in Lemma 4.1. -/
theorem exists_twoPoint_witness (D f g : Laurent) (η : G → ℂ)
    (hD : D ≠ 0) (v w : G) (a b c d : ℤ) (hindependent : det v w ≠ 0)
    (hf : act f η ≠ 0) (hg : act g η ≠ 0)
    (hstripf : SupportedInStrip (act f η) v a b)
    (hstripg : SupportedInStrip (act g η) w c d) :
    ∃ t : G, act D (twoPoint η 0 t) ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_nonzero_shifted_product (act f η) (act g η) hf hg
  have hfinite := finite_support_shifted_product (act f η) (act g η)
    v w t a b c d hindependent hstripf hstripg
  have hnonzero := lemma1_2 hD ht hfinite
  by_contra h
  have hall : ∀ t : G, act D (twoPoint η 0 t) = 0 := by simpa using h
  exact hnonzero (annihilate_product_of_pair_annihilation D f g η hall t)

/-- A diagonal witness is impossible in the paper's second case. -/
theorem witness_ne_zero_of_all_single_site_annihilated {A : Type*}
    (θ : G → A) (w : A → ℂ) (D : Laurent)
    (hall : ∀ w' : A → ℂ, act D (fun z => w' (θ z)) = 0)
    {t : G} (ht : act D (twoPoint (fun z => w (θ z)) 0 t) ≠ 0) : t ≠ 0 := by
  intro hzero
  subst t
  apply ht
  have heq : twoPoint (fun z => w (θ z)) 0 0 = fun z => w (θ z) * w (θ z) := by
    funext z
    simp [twoPoint]
  rw [heq]
  exact hall (fun a => w a * w a)

section PeriodicTails

variable {ι A : Type*} [Fintype ι] [Nonempty ι] [AddCommGroup A]

/-- The finite-support part of Lemma 4.2 follows from the fully proved Lemma 1.1. -/
theorem finite_support_twoPoint_difference (T : Strips.StripSystem ι A)
    (w : A → ℂ) (q₀ q₁ : G) :
    (Function.support (act T.operator (twoPoint (fun z => w (T.total z)) q₀ q₁))).Finite := by
  let W : Finset G := {q₀, q₁}
  let φ : (W → A) → ℂ := fun p =>
    w (p ⟨q₀, by simp [W]⟩) * w (p ⟨q₁, by simp [W]⟩)
  have h := T.finite_support_local_difference W φ
  have heq : T.localObservation W φ = twoPoint (fun z => w (T.total z)) q₀ q₁ := by
    funext z
    rfl
  rw [heq] at h
  exact h

end PeriodicTails

end

end NivatTrial.Witness
