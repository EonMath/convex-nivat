import NivatTrial.SeparatedFiberLimits

/-! Lift a limit of one member of a separated fiber to a joint limit of the
whole fiber. Pairwise finite-window separation is preserved at every site. -/

namespace NivatTrial.JointFiberLimits

open NivatTrial.Dynamics NivatTrial.PeriodicDifference
open NivatTrial.FiniteIncrementFibers NivatTrial.SeparatedFiberLimits
open NivatTrial.NonexpansiveExistence
open Set Filter Topology
open scoped Classical
noncomputable section

variable {A : Type*} [Fintype A]

theorem lift_fiber_limit (θ : Lattice → A) (w : A → ℤ) (h : Lattice)
    (n : ℕ) (G : Fin n → Lattice → A) (hG : ∀ i, G i ∈ languageHull θ)
    (hinc : ∀ i j, increment (encode w (G i)) h = increment (encode w (G j)) h)
    (B : Finset Lattice)
    (hsep : ∀ i j, i ≠ j → ∀ u, patternAt (G i) B u ≠ patternAt (G j) B u)
    (i₀ : Fin n) (x : Lattice → A) (hx : x ∈ languageHull (G i₀)) :
    ∃ E : Fin n → Lattice → A, (∀ i, E i ∈ languageHull θ) ∧ E i₀ = x ∧
      (∀ i j, increment (encode w (E i)) h = increment (encode w (E j)) h) ∧
      ∀ i j, i ≠ j → ∀ u, patternAt (E i) B u ≠ patternAt (E j) B u := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have hxcl : x ∈ closure (orbit (G i₀)) := languageHull_subset_orbitClosure _ hx
  obtain ⟨xs,hxs,hxlim⟩ := mem_closure_iff_seq_limit.mp hxcl
  choose u hu using hxs
  let seq (k : ℕ) (i : Fin n) := shift (u k) (G i)
  have hc : IsCompact {E : Fin n → Lattice → A | ∀ i, E i ∈ languageHull θ} := by
    simpa only [Set.pi,Set.mem_univ,true_imp_iff] using
      isCompact_univ_pi (fun _ : Fin n => isCompact_languageHull θ)
  have hmem (k : ℕ) : seq k ∈ {E : Fin n → Lattice → A | ∀ i, E i ∈ languageHull θ} :=
    fun i => shift_mem_languageHull (hG i) (u k)
  obtain ⟨E,hE,φ,hφ,hlim⟩ := hc.tendsto_subseq hmem
  have hi (i : Fin n) : Tendsto (fun k => seq (φ k) i) atTop (𝓝 (E i)) :=
    tendsto_pi_nhds.mp hlim i
  have hfirst : E i₀ = x := by
    have hh : Tendsto (fun k => seq (φ k) i₀) atTop (𝓝 x) := by
      have hl := hxlim.comp hφ.tendsto_atTop
      exact hl.congr (fun k => (hu (φ k)).symm)
    exact tendsto_nhds_unique (hi i₀) hh
  refine ⟨E,hE,hfirst,?_,?_⟩
  · intro i j
    apply increment_eq_of_tendsto w h (hi i) (hi j)
    intro k
    simp only [seq,increment_encode_shift,hinc i j]
  · intro i j hij t heq
    have hpi := eventually_pattern_eq (hi i) B t
    have hpj := eventually_pattern_eq (hi j) B t
    obtain ⟨k,hki,hkj⟩ := (hpi.and hpj).exists
    have he : patternAt (seq (φ k) i) B t = patternAt (seq (φ k) j) B t :=
      hki.trans (heq.trans hkj.symm)
    apply hsep i j hij (u (φ k)+t)
    simpa only [seq,patternAt_shift] using he

end
end NivatTrial.JointFiberLimits
