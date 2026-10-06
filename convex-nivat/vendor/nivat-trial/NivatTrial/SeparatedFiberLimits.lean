import NivatTrial.FiniteIncrementFibers

/-! Joint limits of a maximal difference fiber can be chosen with a uniform
finite-window separation that survives all later orbit limits. -/

namespace NivatTrial.SeparatedFiberLimits

open NivatTrial.Nonexpansive NivatTrial.Dynamics NivatTrial.PeriodicDifference
open NivatTrial.FiniteIncrementFibers NivatTrial.NonexpansiveExistence
open Set Filter Topology
open scoped Classical
noncomputable section

variable {A : Type*}

section Topology

variable [TopologicalSpace A] [DiscreteTopology A]

theorem eventually_pattern_eq {f : ℕ → Lattice → A} {x : Lattice → A}
    (hf : Tendsto f atTop (𝓝 x)) (S : Finset Lattice) (u : Lattice) :
    ∀ᶠ n in atTop, patternAt (f n) S u = patternAt x S u := by
  have heach (s : S) : ∀ᶠ n in atTop, f n (u+s.val) = x (u+s.val) :=
    eventually_coordinate_eq hf _
  filter_upwards [eventually_all.mpr heach] with n hn
  exact funext hn

theorem continuous_increment_encode (w : A → ℤ) (h : Lattice) :
    Continuous (fun x : Lattice → A => increment (encode w x) h) := by
  apply continuous_pi
  intro z
  have hw : Continuous w := continuous_of_discreteTopology
  exact (hw.comp (continuous_apply (z+h))).sub (hw.comp (continuous_apply z))

theorem increment_eq_of_tendsto (w : A → ℤ) (h : Lattice)
    {x y : ℕ → Lattice → A} {a b : Lattice → A}
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b))
    (he : ∀ n, increment (encode w (x n)) h = increment (encode w (y n)) h) :
    increment (encode w a) h = increment (encode w b) h := by
  have hxl := (continuous_increment_encode w h).continuousAt.tendsto.comp hx
  have hyl := (continuous_increment_encode w h).continuousAt.tendsto.comp hy
  exact tendsto_nhds_unique hxl (hyl.congr (fun n => (he n).symm))

end Topology

variable [Fintype A]

theorem exists_separated_fiber_limit (θ : Lattice → A) (w : A → ℤ)
    (h d : Lattice) (v : Plane) (hd : 0 < score v d) (B : Finset Lattice)
    (hcode : ∀ x ∈ languageHull θ, ∀ y ∈ languageHull θ,
      increment (encode w x) h = increment (encode w y) h →
      (∀ b ∈ B, x b = y b) → ∀ z, score v z ≤ 0 → x z = y z)
    (n : ℕ) (F : Fin n → Lattice → A) (hF : ∀ i, F i ∈ languageHull θ)
    (hinj : Function.Injective F)
    (hinc : ∀ i j, increment (encode w (F i)) h = increment (encode w (F j)) h) :
    ∃ G : Fin n → Lattice → A, (∀ i, G i ∈ languageHull θ) ∧
      (∀ i j, increment (encode w (G i)) h = increment (encode w (G j)) h) ∧
      ∀ i j, i ≠ j → ∀ u, patternAt (G i) B u ≠ patternAt (G j) B u := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  let seq (k : ℕ) (i : Fin n) := shift (k•d) (F i)
  have hc : IsCompact {G : Fin n → Lattice → A | ∀ i, G i ∈ languageHull θ} := by
    simpa only [Set.pi,Set.mem_univ,true_imp_iff] using
      isCompact_univ_pi (fun _ : Fin n => isCompact_languageHull θ)
  have hmem (k : ℕ) : seq k ∈ {G : Fin n → Lattice → A | ∀ i, G i ∈ languageHull θ} :=
    fun i => shift_mem_languageHull (hF i) (k•d)
  obtain ⟨G,hG,φ,hφ,hlim⟩ := hc.tendsto_subseq hmem
  have hi (i : Fin n) : Tendsto (fun k => seq (φ k) i) atTop (𝓝 (G i)) :=
    tendsto_pi_nhds.mp hlim i
  refine ⟨G,hG,?_,?_⟩
  · intro i j
    apply increment_eq_of_tendsto w h (hi i) (hi j)
    intro k
    simp only [seq,increment_encode_shift,hinc i j]
  · intro i j hij u heq
    have hsep := hφ.tendsto_atTop.eventually
      (eventually_shifted_patterns_ne θ w h d v hd B hcode (F i) (F j)
        (hF i) (hF j) (fun he => hij (hinj he)) (hinc i j) u)
    have hpi := eventually_pattern_eq (hi i) B u
    have hpj := eventually_pattern_eq (hi j) B u
    obtain ⟨k,hki,hkj,hkne⟩ := (hpi.and (hpj.and hsep)).exists
    exact hkne (hki.trans (heq.trans hkj.symm))

end
end NivatTrial.SeparatedFiberLimits
