import NivatTrial.FirstCase

/-! Linear independence of quadratic witnesses (the mechanism of §7). -/

namespace NivatTrial.Quadratic

open NivatTrial.Algebra
open scoped Classical

noncomputable section

/-- The polynomial action, viewed as a linear operator on all configurations. -/
def actLinear (D : Laurent) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := act D
  map_add' := act_add_config D
  map_smul' c J := by
    funext z
    simp [act, smul_eq_mul, Finsupp.mul_sum, mul_left_comm]

@[simp] theorem actLinear_apply (D : Laurent) (J : G → ℂ) : actLinear D J = act D J := rfl

/-- Distinct translates of a nonzero finite-support configuration are independent. -/
theorem independent_translates (J : G → ℂ) (hJ : J ≠ 0)
    (hfinite : (Function.support J).Finite) (R : Finset G) :
    LinearIndependent ℂ (fun r : R => fun z : G => J (z + r)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  by_cases hc : c = 0
  · simp [hc]
  · have hact : act (windowPolynomial R c) J = 0 := by
      funext z
      have hz := congrFun hsum z
      simpa [act_windowPolynomial, smul_eq_mul] using hz
    exact False.elim (lemma1_2 (windowPolynomial_ne_zero R hc) hJ hfinite hact)

/-- A rank-nullity form of independence modulo a known subspace. -/
theorem dimension_budget {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] [AddCommGroup N] [Module ℂ N]
    {ι : Type*} [Fintype ι] (T : M →ₗ[ℂ] N) (U : Submodule ℂ M)
    (hU : U ≤ T.ker) (v : ι → M) (hv : LinearIndependent ℂ (fun i => T (v i))) :
    Module.finrank ℂ U + Fintype.card ι ≤ Module.finrank ℂ M := by
  let vr : ι → T.range := fun i => ⟨T (v i), ⟨v i, rfl⟩⟩
  have hir : LinearIndependent ℂ vr := by
    apply LinearIndependent.of_comp T.range.subtype
    exact hv
  have hcard := hir.fintype_card_le_finrank
  have hker := Submodule.finrank_mono hU
  have hrank := T.finrank_range_add_finrank_ker
  omega

variable {A : Type*} [Fintype A]

abbrev ObservationSpace (θ : Lattice → A) (S : Finset Lattice) := patternSet θ S → ℂ

/-- Read an observation on every translate of the actual configuration. -/
def evaluate (θ : Lattice → A) (S : Finset Lattice) :
    ObservationSpace θ S →ₗ[ℂ] (G → ℂ) where
  toFun f z := f ⟨patternAt θ S z, ⟨z, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluate_injective (θ : Lattice → A) (S : Finset Lattice) :
    Function.Injective (evaluate θ S) := by
  intro f g h
  funext p
  obtain ⟨z, hz⟩ := p.property
  have heq : (⟨patternAt θ S z, ⟨z, rfl⟩⟩ : patternSet θ S) = p := by
    apply Subtype.ext
    exact hz
  have hfg := congrFun h z
  change f ⟨patternAt θ S z, ⟨z, rfl⟩⟩ = g ⟨patternAt θ S z, ⟨z, rfl⟩⟩ at hfg
  simpa only [heq] using hfg

theorem observation_finrank (θ : Lattice → A) (S : Finset Lattice) :
    Module.finrank ℂ (ObservationSpace θ S) = patternComplexity θ S := by
  simp [ObservationSpace, patternComplexity, Nat.card_eq_fintype_card]

def coordinateObservation (θ : Lattice → A) (S : Finset Lattice)
    (w : A → ℂ) (s : S) : ObservationSpace θ S := fun p => w (p.val s)

def affineSpace (θ : Lattice → A) (S : Finset Lattice) (w : A → ℂ) :
    Submodule ℂ (ObservationSpace θ S) :=
  Submodule.span ℂ (insert (fun _ => 1) (Set.range (coordinateObservation θ S w)))

def detector (θ : Lattice → A) (S : Finset Lattice) (D : Laurent) :
    ObservationSpace θ S →ₗ[ℂ] (G → ℂ) := (actLinear D).comp (evaluate θ S)

@[simp] theorem detector_apply (θ : Lattice → A) (S : Finset Lattice) (D : Laurent)
    (f : ObservationSpace θ S) : detector θ S D f = act D (evaluate θ S f) := rfl

@[simp] theorem evaluate_coordinate (θ : Lattice → A) (S : Finset Lattice)
    (w : A → ℂ) (s : S) :
    evaluate θ S (coordinateObservation θ S w s) = fun z => w (θ (z + s)) := rfl

theorem detector_coordinate (θ : Lattice → A) (S : Finset Lattice)
    (w : A → ℂ) (D : Laurent) (s : S) (z : G) :
    detector θ S D (coordinateObservation θ S w s) z =
      act D (fun x => w (θ x)) (z + s) := by
  simp [detector_apply, act, add_assoc, add_comm, add_left_comm]

/-- The finite difference kills the entire affine-observation space. -/
theorem affineSpace_le_ker_detector (θ : Lattice → A) (S : Finset Lattice)
    (w : A → ℂ) (D : Laurent) (hconstant : ∀ b : ℂ, act D (fun _ => b) = 0)
    (hlinear : act D (fun z => w (θ z)) = 0) :
    affineSpace θ S w ≤ (detector θ S D).ker := by
  apply Submodule.span_le.mpr
  intro f hf
  rcases hf with rfl | ⟨s, rfl⟩
  · change act D (fun _ => 1) = 0
    exact hconstant 1
  · change detector θ S D (coordinateObservation θ S w s) = 0
    funext z
    rw [detector_coordinate, hlinear]
    rfl

def twoPoint (η : G → ℂ) (q₀ q₁ : G) : G → ℂ :=
  fun z => η (z + q₀) * η (z + q₁)

/-- The positions, rather than only their labels, are constrained to the window. -/
def quadraticObservation (θ : Lattice → A) (S R : Finset Lattice)
    (w : A → ℂ) (q₀ q₁ : G)
    (h₀ : ∀ r : R, (r : G) + q₀ ∈ S) (h₁ : ∀ r : R, (r : G) + q₁ ∈ S)
    (r : R) : ObservationSpace θ S :=
  fun p => w (p.val ⟨r + q₀, h₀ r⟩) * w (p.val ⟨r + q₁, h₁ r⟩)

theorem evaluate_quadratic (θ : Lattice → A) (S R : Finset Lattice)
    (w : A → ℂ) (q₀ q₁ : G)
    (h₀ : ∀ r : R, (r : G) + q₀ ∈ S) (h₁ : ∀ r : R, (r : G) + q₁ ∈ S)
    (r : R) :
    evaluate θ S (quadraticObservation θ S R w q₀ q₁ h₀ h₁ r) =
      fun z => twoPoint (fun x => w (θ x)) q₀ q₁ (z + r) := by
  funext z
  simp [evaluate, quadraticObservation, patternAt, twoPoint, add_assoc]

theorem detector_quadratic (θ : Lattice → A) (S R : Finset Lattice)
    (w : A → ℂ) (D : Laurent) (q₀ q₁ : G)
    (h₀ : ∀ r : R, (r : G) + q₀ ∈ S) (h₁ : ∀ r : R, (r : G) + q₁ ∈ S)
    (r : R) (z : G) :
    detector θ S D (quadraticObservation θ S R w q₀ q₁ h₀ h₁ r) z =
      act D (twoPoint (fun x => w (θ x)) q₀ q₁) (z + r) := by
  rw [detector_apply, evaluate_quadratic]
  simp [act, add_comm, add_left_comm]

/-- The quadratic witnesses are independent after applying a detector that kills
the affine space. This is the substantive independence argument of Lemma 7.2. -/
theorem independent_detected_quadratics (θ : Lattice → A) (S R : Finset Lattice)
    (w : A → ℂ) (D : Laurent) (q₀ q₁ : G)
    (h₀ : ∀ r : R, (r : G) + q₀ ∈ S) (h₁ : ∀ r : R, (r : G) + q₁ ∈ S)
    (hfinite : (Function.support (act D (twoPoint (fun x => w (θ x)) q₀ q₁))).Finite)
    (hnonzero : act D (twoPoint (fun x => w (θ x)) q₀ q₁) ≠ 0) :
    LinearIndependent ℂ (fun r : R =>
      detector θ S D (quadraticObservation θ S R w q₀ q₁ h₀ h₁ r)) := by
  have heq : (fun r : R => detector θ S D
      (quadraticObservation θ S R w q₀ q₁ h₀ h₁ r)) =
      (fun r : R => fun z => act D (twoPoint (fun x => w (θ x)) q₀ q₁) (z + r)) := by
    funext r z
    exact detector_quadratic θ S R w D q₀ q₁ h₀ h₁ r z
  rw [heq]
  exact independent_translates _ hnonzero hfinite R

/-- The exact dimension compensation used in Theorem 7.3, once a witness and
its placements have been supplied. -/
theorem quadratic_dimension_bound (θ : Lattice → A) (S R : Finset Lattice)
    (w : A → ℂ) (D : Laurent) (q₀ q₁ : G)
    (h₀ : ∀ r : R, (r : G) + q₀ ∈ S) (h₁ : ∀ r : R, (r : G) + q₁ ∈ S)
    (hconstant : ∀ b : ℂ, act D (fun _ => b) = 0)
    (hlinear : act D (fun z => w (θ z)) = 0)
    (hfinite : (Function.support (act D (twoPoint (fun x => w (θ x)) q₀ q₁))).Finite)
    (hnonzero : act D (twoPoint (fun x => w (θ x)) q₀ q₁) ≠ 0) :
    Module.finrank ℂ (affineSpace θ S w) + R.card ≤ patternComplexity θ S := by
  have hbudget := dimension_budget (detector θ S D) (affineSpace θ S w)
    (affineSpace_le_ker_detector θ S w D hconstant hlinear)
    (quadraticObservation θ S R w q₀ q₁ h₀ h₁)
    (independent_detected_quadratics θ S R w D q₀ q₁ h₀ h₁ hfinite hnonzero)
  simpa only [Fintype.card_coe, observation_finrank] using hbudget

end

end NivatTrial.Quadratic
