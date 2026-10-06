import NivatTrial.NonexpansiveExistence
import NivatTrial.GeneratingWindows

/-! Compactness turns determination by an infinite region into a finite local
rule. This supplies the finite coding window in the direction-symmetry proof. -/

namespace NivatTrial.FiniteDetermination

open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.NonexpansiveExistence
open NivatTrial.AmbiguityPropagation
open Set Filter Topology
open scoped Classical
noncomputable section

variable {A : Type*}

section Topology

variable [TopologicalSpace A] [DiscreteTopology A]

theorem finite_determining_subset (Ω : Set (Lattice → A)) (hΩ : IsCompact Ω)
    (R : Set Lattice) (z : Lattice)
    (hdet : ∀ x ∈ Ω, ∀ y ∈ Ω, AgreeOn x y R → x z = y z) :
    ∃ S : Finset Lattice, (↑S : Set Lattice) ⊆ R ∧
      ∀ x ∈ Ω, ∀ y ∈ Ω, (∀ s ∈ S, x s = y s) → x z = y z := by
  let K : Set ((Lattice → A) × (Lattice → A)) :=
    (Ω ×ˢ Ω) ∩ {p | p.1 z ≠ p.2 z}
  have hclosed : IsClosed {p : (Lattice → A) × (Lattice → A) | p.1 z ≠ p.2 z} := by
    have hc : Continuous (fun p : (Lattice → A) × (Lattice → A) => (p.1 z,p.2 z)) := by
      fun_prop
    exact (isClosed_discrete {q : A × A | q.1 ≠ q.2}).preimage hc
  have hK : IsCompact K := (hΩ.prod hΩ).inter_right hclosed
  let U (s : R) : Set ((Lattice → A) × (Lattice → A)) := {p | p.1 s.val ≠ p.2 s.val}
  have hopen (s : R) : IsOpen (U s) := by
    exact (isClosed_eq (show Continuous (fun p : (Lattice → A) × (Lattice → A) => p.1 s.val) by fun_prop)
      (by fun_prop)).isOpen_compl
  have hcover : K ⊆ ⋃ s : R, U s := by
    rintro ⟨x,y⟩ ⟨⟨hx,hy⟩,hne⟩
    apply mem_iUnion.mpr
    by_contra h
    apply hne
    apply hdet x hx y hy
    intro s hs
    by_contra he
    exact h ⟨⟨s,hs⟩,he⟩
  obtain ⟨T,hT⟩ := hK.elim_finite_subcover U hopen hcover
  refine ⟨T.image Subtype.val,?_,?_⟩
  · intro s hs
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hs
    exact t.property
  · intro x hx y hy hagree
    by_contra hne
    have hmem := hT (show (x,y) ∈ K from ⟨⟨hx,hy⟩,hne⟩)
    obtain ⟨s,hs⟩ := mem_iUnion.mp hmem
    obtain ⟨hst,hbad⟩ := mem_iUnion.mp hs
    exact hbad (hagree s.val (Finset.mem_image.mpr ⟨s,hst,rfl⟩))

end Topology

theorem open_halfPlane_determines [Fintype A] {θ : Lattice → A} {v : Plane}
    (hv : v ≠ 0) (hexp : OneSidedExpansive θ v)
    {x y : Lattice → A} (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (hagree : ∀ z, 0 < score v z → x z = y z) : x = y := by
  obtain ⟨g,hg⟩ := exists_positive_score hv
  apply shift_injective g
  by_contra hne
  apply hexp
  refine ⟨shift g x,shift_mem_languageHull hx g,
    shift g y,shift_mem_languageHull hy g,hne,?_⟩
  intro z hz
  apply hagree (g+z)
  change 0 ≤ score v z at hz
  rw [score_add]
  linarith

/-- Every expansive oriented half-plane supplies a finite determining patch
strictly on its positive side. Translates of this same patch code each site. -/
theorem exists_finite_positive_coding [Fintype A] {θ : Lattice → A} {v : Plane}
    (hv : v ≠ 0) (hexp : OneSidedExpansive θ v) :
    ∃ S : Finset Lattice, (∀ s ∈ S, 0 < score v s) ∧ Determines θ S 0 := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨S,hS,hdet⟩ := finite_determining_subset (languageHull θ)
    (isCompact_languageHull θ) {s | 0 < score v s} 0 (by
      intro x hx y hy hagree
      exact congrFun (open_halfPlane_determines hv hexp hx hy hagree) 0)
  refine ⟨S,hS,?_⟩
  intro x hx y hy u w hpat
  have he := hdet (shift u x) (shift_mem_languageHull hx u)
    (shift w y) (shift_mem_languageHull hy w) (by
      intro s hs
      exact congrFun hpat ⟨s,hs⟩)
  simpa using he

end
end NivatTrial.FiniteDetermination
