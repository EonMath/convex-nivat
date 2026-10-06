import NivatTrial.ColleSecondBoundaryCoordinates

/-! Actual ambiguity, expressed by two occurring extensions, is preserved by
integer coordinate changes. This transports the second-boundary witness back
to the first-direction coordinates used by the parallelogram argument. -/

namespace NivatTrial.ColleSemiAmbiguityTransport

open NivatTrial.Dynamics NivatTrial.ColleAmbiguity
open NivatTrial.ColleSemiAmbiguity NivatTrial.ColleDirectionalPropagation
open NivatTrial.LatticeCoordinates
open scoped Classical

noncomputable section
abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ
variable {A : Type*} [Fintype A]

theorem ambiguous_at_iff_two_occurrences (θ : G → A) (S : Finset G)
    (v : Plane) {x : G → A} (hx : x ∈ languageHull θ) (a : G) :
    AmbiguousPattern θ S v
      ⟨patternAt x (supportBase S v) a,
        patternSet_subset_of_mem_languageHull hx _ ⟨a,rfl⟩⟩ ↔
    ∃ b c : G,
      (∀ s ∈ supportBase S v, θ (b+s)=x (a+s)) ∧
      (∀ s ∈ supportBase S v, θ (c+s)=x (a+s)) ∧
      ∃ s ∈ S, θ (b+s)≠θ (c+s) := by
  let p : patternSet θ (supportBase S v) :=
    ⟨patternAt x (supportBase S v) a,
      patternSet_subset_of_mem_languageHull hx _ ⟨a,rfl⟩⟩
  constructor
  · intro h
    have hc : 1 < Fintype.card {q : patternSet θ S // restriction θ S v q=p} := by
      have hh : 2 ≤ Fintype.card {q : patternSet θ S // restriction θ S v q=p} := by
        simpa only [AmbiguousPattern,ColleAmbiguity.multiplicity,extensionCount,
          Nat.card_eq_fintype_card] using h
      omega
    obtain ⟨q,r,hqr⟩ := Fintype.one_lt_card_iff.mp hc
    obtain ⟨b,hb⟩ := q.val.property
    obtain ⟨c,hc⟩ := r.val.property
    refine ⟨b,c,?_,?_,?_⟩
    · intro s hs
      have hh := congrFun (congrArg Subtype.val q.property) ⟨s,hs⟩
      change q.val.val ⟨s,supportBase_subset S v hs⟩=x (a+s) at hh
      rw [← hb] at hh
      exact hh
    · intro s hs
      have hh := congrFun (congrArg Subtype.val r.property) ⟨s,hs⟩
      change r.val.val ⟨s,supportBase_subset S v hs⟩=x (a+s) at hh
      rw [← hc] at hh
      exact hh
    · by_contra h
      apply hqr
      apply Subtype.ext
      apply Subtype.ext
      rw [← hb,← hc]
      funext s
      by_contra hn
      exact h ⟨s,s.property,hn⟩
  · rintro ⟨b,c,hb,hc,s,hs,hne⟩
    let q : patternSet θ S := ⟨patternAt θ S b,⟨b,rfl⟩⟩
    let r : patternSet θ S := ⟨patternAt θ S c,⟨c,rfl⟩⟩
    have hq : restriction θ S v q=p := by
      apply Subtype.ext
      funext t
      exact hb t t.property
    have hr : restriction θ S v r=p := by
      apply Subtype.ext
      funext t
      exact hc t t.property
    exact two_extensions_imply_count hq hr (fun he =>
      hne (congrFun (congrArg Subtype.val he) ⟨s,hs⟩))

theorem ambiguous_at_mapWindow (e : G ≃+ G) (θ : G → A)
    (S : Finset G) (v : Plane) {x : G → A}
    (hx : x ∈ languageHull θ) (a : G)
    (h : AmbiguousPattern θ S (dualNormal e v)
      ⟨patternAt x (supportBase S (dualNormal e v)) a,
        patternSet_subset_of_mem_languageHull hx _ ⟨a,rfl⟩⟩) :
    AmbiguousPattern (θ ∘ e.symm) (mapWindow e S) v
      ⟨patternAt (x ∘ e.symm) (supportBase (mapWindow e S) v) (e a),
        patternSet_subset_of_mem_languageHull
          (mem_languageHull_comp_equiv e.symm hx) _ ⟨e a,rfl⟩⟩ := by
  obtain ⟨b,c,hb,hc,s,hs,hne⟩ :=
    (ambiguous_at_iff_two_occurrences θ S (dualNormal e v) hx a).mp h
  apply (ambiguous_at_iff_two_occurrences (θ ∘ e.symm) (mapWindow e S)
    v (mem_languageHull_comp_equiv e.symm hx) (e a)).mpr
  refine ⟨e b,e c,?_,?_,e s,by simpa using hs,?_⟩
  · intro t ht
    rw [supportBase_mapWindow] at ht
    have hh := hb (e.symm t) ((mem_mapWindow _ _ _).mp ht)
    simpa only [Function.comp_apply,map_add,e.symm_apply_apply] using hh
  · intro t ht
    rw [supportBase_mapWindow] at ht
    have hh := hc (e.symm t) ((mem_mapWindow _ _ _).mp ht)
    simpa only [Function.comp_apply,map_add,e.symm_apply_apply] using hh
  · simpa only [Function.comp_apply,map_add,e.symm_apply_apply] using hne

theorem semiAmbiguous_mapWindow (e : G ≃+ G) (θ : G → A)
    (S : Finset G) (v : Plane) (u : G) {x : G → A}
    (hx : x ∈ languageHull θ) (τ : ℤ)
    (h : SemiAmbiguous θ S (dualNormal e v) u x hx τ) :
    SemiAmbiguous (θ ∘ e.symm) (mapWindow e S) v (e u)
      (x ∘ e.symm) (mem_languageHull_comp_equiv e.symm hx) τ := by
  intro i hi
  simpa only [map_zsmul] using
    ambiguous_at_mapWindow e θ S v hx (i•u) (h i hi)

end
end NivatTrial.ColleSemiAmbiguityTransport
