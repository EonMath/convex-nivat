import NivatTrial.Dynamics
import Mathlib.Topology.Sequences

/-! Minimal orbit closures for finite alphabets. The existence proof uses
compactness and the intersection of a decreasing chain of invariant closed
sets. The conclusion is phrased entirely in the finite-window language. -/

namespace NivatTrial.MinimalHull

open NivatTrial.Dynamics Set Filter Topology
open scoped Classical
noncomputable section

variable {A : Type*}

def IsMinimalHull (θ : Lattice → A) : Prop :=
  ∀ x ∈ languageHull θ, languageHull x = languageHull θ

theorem mem_iff_hull_eq {θ x : Lattice → A} (hm : IsMinimalHull θ) :
    x ∈ languageHull θ ↔ languageHull x = languageHull θ := by
  constructor
  · exact hm x
  · intro he
    rw [← he]
    exact self_mem_languageHull x

theorem isMinimalHull_of_mem {θ x : Lattice → A} (hm : IsMinimalHull θ)
    (hx : x ∈ languageHull θ) : IsMinimalHull x := by
  intro y hy
  rw [hm x hx] at hy ⊢
  exact hm y hy

section Topology

variable [TopologicalSpace A] [DiscreteTopology A]

theorem languageHull_subset_of_closed_invariant (Ω : Set (Lattice → A))
    (hclosed : IsClosed Ω) (hshift : ∀ x ∈ Ω, ∀ u, shift u x ∈ Ω)
    {x : Lattice → A} (hx : x ∈ Ω) : languageHull x ⊆ Ω := by
  rw [← orbitClosure_eq_languageHull]
  apply closure_minimal _ hclosed
  rintro y ⟨u,rfl⟩
  exact hshift x hx u

theorem exists_minimal_closed_invariant [Fintype A] (θ : Lattice → A) :
    ∃ Ω : Set (Lattice → A), Ω ⊆ languageHull θ ∧ Ω.Nonempty ∧ IsClosed Ω ∧
      (∀ x ∈ Ω, ∀ u, shift u x ∈ Ω) ∧
      ∀ x ∈ Ω, languageHull x = Ω := by
  let C : Set (Set (Lattice → A)) := {Ω | Ω ⊆ languageHull θ ∧ Ω.Nonempty ∧
    IsClosed Ω ∧ ∀ x ∈ Ω, ∀ u, shift u x ∈ Ω}
  have hbase : languageHull θ ∈ C := by
    refine ⟨Subset.rfl,⟨θ,self_mem_languageHull θ⟩,?_,?_⟩
    · rw [← orbitClosure_eq_languageHull]
      exact isClosed_orbitClosure θ
    · intro x hx u
      exact shift_mem_languageHull hx u
  have hchain (c : Set (Set (Lattice → A))) (hc : c ⊆ C)
      (hlinear : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
      ∃ Ω ∈ C, ∀ s ∈ c, Ω ⊆ s := by
    let Ω : Set (Lattice → A) := ⋂ s : c, s.val
    have : Nonempty c := hne.to_subtype
    have hdir : Directed (· ⊇ ·) (fun s : c => s.val) := by
      intro s t
      rcases hlinear.total s.property t.property with hst | hts
      · exact ⟨s,Subset.rfl,hst⟩
      · exact ⟨t,hts,Subset.rfl⟩
    have hΩne : Ω.Nonempty :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ hdir
        (fun s => (hc s.property).2.1)
        (fun s => (hc s.property).2.2.1.isCompact)
        (fun s => (hc s.property).2.2.1)
    have hsub (s : c) : Ω ⊆ s.val := iInter_subset _ s
    obtain ⟨s,hs⟩ := hne
    refine ⟨Ω,⟨(hsub ⟨s,hs⟩).trans (hc hs).1,hΩne,?_,?_⟩,?_⟩
    · exact isClosed_iInter (fun s => (hc s.property).2.2.1)
    · intro x hx u
      apply mem_iInter.mpr
      intro s
      exact (hc s.property).2.2.2 x (hsub s hx) u
    · intro s hs
      exact hsub ⟨s,hs⟩
  obtain ⟨Ω,_,hmin⟩ := zorn_superset_nonempty C hchain (languageHull θ) hbase
  have hΩ := hmin.prop
  refine ⟨Ω,hΩ.1,hΩ.2.1,hΩ.2.2.1,hΩ.2.2.2,?_⟩
  intro x hx
  have hsub := languageHull_subset_of_closed_invariant Ω hΩ.2.2.1 hΩ.2.2.2 hx
  have hxC : languageHull x ∈ C := by
    refine ⟨hsub.trans hΩ.1,⟨x,self_mem_languageHull x⟩,?_,?_⟩
    · rw [← orbitClosure_eq_languageHull]
      exact isClosed_orbitClosure x
    · intro y hy u
      exact shift_mem_languageHull hy u
  exact (hmin.eq_of_subset hxC hsub)

end Topology

theorem exists_minimal_hull [Fintype A] (θ : Lattice → A) :
    ∃ x ∈ languageHull θ, IsMinimalHull x := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨Ω,hsub,hne,_,_,hull⟩ := exists_minimal_closed_invariant θ
  obtain ⟨x,hx⟩ := hne
  refine ⟨x,hsub hx,?_⟩
  intro y hy
  rw [hull x hx] at hy ⊢
  exact hull y hy

end
end NivatTrial.MinimalHull
