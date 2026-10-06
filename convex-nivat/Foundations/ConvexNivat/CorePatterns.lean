import ConvexNivat.Core

/-! Pattern counting, injective encodings, and finite-window orbit closure. -/

namespace ConvexNivat

theorem patternSet_finite {A : Type*} [Finite A] (f : Configuration A)
    (S : Finset Lattice) : (patternSet f S).Finite := by
  exact Set.toFinite _

theorem patternSet_nonempty {A : Type*} (f : Configuration A) (S : Finset Lattice) :
    (patternSet f S).Nonempty := by
  exact ⟨pattern f S 0, ⟨0, rfl⟩⟩

theorem complexity_empty {A : Type*} (f : Configuration A) :
    complexity f ∅ = 1 := by
  have h : patternSet f ∅ = {pattern f ∅ 0} := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      apply Set.mem_singleton_iff.mpr
      funext z
      exact (Finset.notMem_empty _ z.property).elim
    · intro hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      exact ⟨0, rfl⟩
  simp [complexity, h]

theorem complexity_pos {A : Type*} [Finite A] (f : Configuration A)
    (S : Finset Lattice) : 0 < complexity f S := by
  exact (Set.ncard_pos (patternSet_finite f S)).mpr (patternSet_nonempty f S)

theorem complexity_le_alphabet_pow {A : Type*} [Finite A] (f : Configuration A)
    (S : Finset Lattice) : complexity f S ≤ Nat.card A ^ S.card := by
  calc
    complexity f S ≤ Nat.card (Pattern A S) := Set.ncard_le_card _
    _ = Nat.card A ^ S.card := by
      rw [Nat.card_fun, Nat.card_eq_finsetCard]

theorem complexity_mono {A : Type*} [Finite A] (f : Configuration A)
    (S T : Finset Lattice) (hST : S ⊆ T) : complexity f S ≤ complexity f T := by
  let restrict : Pattern A T → Pattern A S := fun p z => p ⟨z.val, hST z.property⟩
  have h : patternSet f S = restrict '' patternSet f T := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨pattern f T u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
  unfold complexity
  rw [h]
  exact Set.ncard_image_le (patternSet_finite f T)

theorem complexity_translate {A : Type*} (f : Configuration A)
    (u : Lattice) (S : Finset Lattice) :
    complexity (translate u f) S = complexity f S := by
  have h : patternSet (translate u f) S = patternSet f S := by
    ext p
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨v + u, ?_⟩
      funext z
      simp only [pattern, translate]
      congr 1
      abel
    · rintro ⟨v, rfl⟩
      refine ⟨v - u, ?_⟩
      funext z
      simp only [pattern, translate]
      congr 1
      abel
  exact congrArg Set.ncard h

/-- Injective alphabet encoding preserves complexity (§8.6). -/
theorem complexity_injective_encoding {A B : Type*} (f : Configuration A)
    (ι : A → B) (hι : Function.Injective ι) (S : Finset Lattice) :
    complexity (ι ∘ f) S = complexity f S := by
  let encode : Pattern A S → Pattern B S := fun p => ι ∘ p
  have h : patternSet (ι ∘ f) S = encode '' patternSet f S := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨pattern f S u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
  have hencode : Function.Injective encode := by
    intro p q hpq
    funext z
    exact hι (congrFun hpq z)
  unfold complexity
  rw [h]
  exact Set.ncard_image_of_injective _ hencode

theorem periodic_injective_encoding_iff {A B : Type*} (f : Configuration A)
    (ι : A → B) (hι : Function.Injective ι) :
    Periodic (ι ∘ f) ↔ Periodic f := by
  constructor
  · rintro ⟨h, hne, hh⟩
    exact ⟨h, hne, fun z => hι (hh z)⟩
  · rintro ⟨h, hne, hh⟩
    exact ⟨h, hne, fun z => congrArg ι (hh z)⟩

theorem orbitClosure_self {A : Type*} (f : Configuration A) : f ∈ OrbitClosure f := by
  intro S
  exact ⟨0, fun z _ => by simp⟩

theorem orbitClosure_translate {A : Type*} (f : Configuration A) (u : Lattice) :
    translate u f ∈ OrbitClosure f := by
  intro S
  exact ⟨u, fun z _ => by simp [translate, add_comm]⟩

/-- Source §8.6(5), the finite-window orbit-closure inclusion. -/
theorem orbitClosure_patternSet_subset {A : Type*} (f g : Configuration A)
    (hg : g ∈ OrbitClosure f) (S : Finset Lattice) :
    patternSet g S ⊆ patternSet f S := by
  rintro p ⟨v, rfl⟩
  obtain ⟨u, hu⟩ := hg (S.image (fun z => v + z))
  refine ⟨u + v, ?_⟩
  funext z
  change f ((u + v) + z.val) = g (v + z.val)
  rw [add_assoc]
  exact (hu _ (Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩)).symm

theorem orbitClosure_complexity_le {A : Type*} [Finite A] (f g : Configuration A)
    (hg : g ∈ OrbitClosure f) (S : Finset Lattice) :
    complexity g S ≤ complexity f S := by
  exact Set.ncard_le_ncard (orbitClosure_patternSet_subset f g hg S)
    (patternSet_finite f S)

end ConvexNivat
