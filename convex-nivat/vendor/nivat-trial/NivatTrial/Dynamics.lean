import NivatTrial.Patterns

/-! Finite-window symbolic dynamics for the configurations in the paper. -/

namespace NivatTrial.Dynamics

variable {A B C : Type*}

/-- The translation convention agrees with the Laurent action in the paper. -/
def shift (u : Lattice) (θ : Lattice → A) : Lattice → A :=
  fun z => θ (u + z)

@[simp] theorem shift_apply (u : Lattice) (θ : Lattice → A) (z : Lattice) :
    shift u θ z = θ (u + z) := rfl

@[simp] theorem shift_zero (θ : Lattice → A) : shift 0 θ = θ := by
  funext z
  simp [shift]

theorem shift_add (u v : Lattice) (θ : Lattice → A) :
    shift (u + v) θ = shift u (shift v θ) := by
  funext z
  simp [shift, add_assoc, add_comm, add_left_comm]

theorem shift_comm (u v : Lattice) (θ : Lattice → A) :
    shift u (shift v θ) = shift v (shift u θ) := by
  rw [← shift_add, ← shift_add, add_comm]

@[simp] theorem shift_neg_shift (u : Lattice) (θ : Lattice → A) :
    shift (-u) (shift u θ) = θ := by
  rw [← shift_add, neg_add_cancel, shift_zero]

@[simp] theorem shift_shift_neg (u : Lattice) (θ : Lattice → A) :
    shift u (shift (-u) θ) = θ := by
  rw [← shift_add, add_neg_cancel, shift_zero]

theorem shift_injective (u : Lattice) : Function.Injective (shift u :
    (Lattice → A) → Lattice → A) := by
  intro θ η h
  simpa using congrArg (shift (-u)) h

theorem shift_surjective (u : Lattice) : Function.Surjective (shift u :
    (Lattice → A) → Lattice → A) := by
  intro θ
  exact ⟨shift (-u) θ, shift_shift_neg u θ⟩

/-- Translation is an invertible transformation of the whole configuration space. -/
def shiftEquiv (u : Lattice) : (Lattice → A) ≃ (Lattice → A) where
  toFun := shift u
  invFun := shift (-u)
  left_inv := shift_neg_shift u
  right_inv := shift_shift_neg u

/-- The orbit consists of the actual translates, before taking any limit. -/
def orbit (θ : Lattice → A) : Set (Lattice → A) := Set.range (fun u => shift u θ)

theorem mem_orbit_iff (θ η : Lattice → A) : η ∈ orbit θ ↔ ∃ u, shift u θ = η := Iff.rfl

theorem self_mem_orbit (θ : Lattice → A) : θ ∈ orbit θ := ⟨0, shift_zero θ⟩

theorem shift_mem_orbit (θ : Lattice → A) (u : Lattice) : shift u θ ∈ orbit θ :=
  ⟨u, rfl⟩

theorem orbit_shift (θ : Lattice → A) (u : Lattice) : orbit (shift u θ) = orbit θ := by
  ext η
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v + u, shift_add v u θ⟩
  · rintro ⟨v, rfl⟩
    refine ⟨v - u, ?_⟩
    change shift (v - u) (shift u θ) = shift v θ
    rw [← shift_add, sub_add_cancel]

theorem orbit_eq_of_mem {θ η : Lattice → A} (h : η ∈ orbit θ) : orbit η = orbit θ := by
  rcases h with ⟨u, rfl⟩
  exact orbit_shift θ u

theorem orbit_subset_of_mem {θ η : Lattice → A} (h : η ∈ orbit θ) : orbit η ⊆ orbit θ :=
  (orbit_eq_of_mem h).subset

/-- Pointwise recoding of the alphabet. -/
def encode (f : A → B) (θ : Lattice → A) : Lattice → B := f ∘ θ

@[simp] theorem encode_apply (f : A → B) (θ : Lattice → A) (z : Lattice) :
    encode f θ z = f (θ z) := rfl

@[simp] theorem encode_id (θ : Lattice → A) : encode id θ = θ := rfl

theorem encode_comp (f : A → B) (g : B → C) (θ : Lattice → A) :
    encode g (encode f θ) = encode (g ∘ f) θ := rfl

theorem encode_shift (f : A → B) (θ : Lattice → A) (u : Lattice) :
    encode f (shift u θ) = shift u (encode f θ) := rfl

theorem encode_injective {f : A → B} (hf : Function.Injective f) :
    Function.Injective (encode f : (Lattice → A) → Lattice → B) := by
  intro θ η h
  funext z
  exact hf (congrFun h z)

section Counting

variable [Fintype A] [Fintype B]

theorem patternAt_shift (θ : Lattice → A) (S : Finset Lattice) (u v : Lattice) :
    patternAt (shift u θ) S v = patternAt θ S (u + v) := by
  funext s
  simp [patternAt, shift, add_assoc]

theorem patternSet_shift (θ : Lattice → A) (S : Finset Lattice) (u : Lattice) :
    patternSet (shift u θ) S = patternSet θ S := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨u + v, (patternAt_shift θ S u v).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨v - u, ?_⟩
    rw [patternAt_shift]
    congr 1
    abel

theorem patternComplexity_shift (θ : Lattice → A) (S : Finset Lattice) (u : Lattice) :
    patternComplexity (shift u θ) S = patternComplexity θ S := by
  unfold patternComplexity
  rw [patternSet_shift]

theorem patternSet_nonempty (θ : Lattice → A) (S : Finset Lattice) :
    (patternSet θ S).Nonempty := ⟨patternAt θ S 0, ⟨0, rfl⟩⟩

theorem patternComplexity_pos (θ : Lattice → A) (S : Finset Lattice) :
    0 < patternComplexity θ S := by
  classical
  haveI : Nonempty (patternSet θ S) := (patternSet_nonempty θ S).to_subtype
  simpa [patternComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_pos (α := patternSet θ S)

theorem patternComplexity_le_all (θ : Lattice → A) (S : Finset Lattice) :
    patternComplexity θ S ≤ (Fintype.card A) ^ S.card := by
  classical
  have h := Fintype.card_le_of_injective
    (Subtype.val : patternSet θ S → S → A) Subtype.val_injective
  simpa [patternComplexity, Nat.card_eq_fintype_card] using h

theorem patternComplexity_empty (θ : Lattice → A) : patternComplexity θ ∅ = 1 := by
  classical
  haveI : Nonempty (patternSet θ ∅) := (patternSet_nonempty θ ∅).to_subtype
  haveI : Subsingleton (patternSet θ ∅) := inferInstance
  letI : Unique (patternSet θ ∅) :=
    { default := ⟨patternAt θ ∅ 0, ⟨0, rfl⟩⟩
      uniq := fun _ => Subsingleton.elim _ _ }
  rw [patternComplexity, Nat.card_eq_fintype_card]
  exact Fintype.card_unique

/-- Restrict an actual large-window pattern to a contained window. -/
def restrictPattern {S T : Finset Lattice} (hST : S ⊆ T) (p : T → A) : S → A :=
  fun s => p ⟨s, hST s.property⟩

theorem restrictPattern_patternAt (θ : Lattice → A) {S T : Finset Lattice}
    (hST : S ⊆ T) (u : Lattice) :
    restrictPattern hST (patternAt θ T u) = patternAt θ S u := rfl

/-- Restriction is onto the actual smaller-window pattern set. -/
def patternRestriction (θ : Lattice → A) {S T : Finset Lattice} (hST : S ⊆ T) :
    patternSet θ T → patternSet θ S := fun p =>
  ⟨restrictPattern hST p.val, by
    rcases p.property with ⟨u, hu⟩
    exact ⟨u, by rw [← hu]; rfl⟩⟩

theorem patternRestriction_surjective (θ : Lattice → A) {S T : Finset Lattice}
    (hST : S ⊆ T) : Function.Surjective (patternRestriction θ hST) := by
  rintro ⟨p, u, rfl⟩
  exact ⟨⟨patternAt θ T u, ⟨u, rfl⟩⟩, rfl⟩

theorem patternComplexity_mono (θ : Lattice → A) {S T : Finset Lattice}
    (hST : S ⊆ T) : patternComplexity θ S ≤ patternComplexity θ T := by
  classical
  simpa [patternComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_surjective _ (patternRestriction_surjective θ hST)

/-- Equal complexity means that every occurring small pattern determines its extension. -/
theorem patternRestriction_injective_of_card_eq (θ : Lattice → A)
    {S T : Finset Lattice} (hST : S ⊆ T)
    (hcard : patternComplexity θ S = patternComplexity θ T) :
    Function.Injective (patternRestriction θ hST) := by
  classical
  exact ((Fintype.bijective_iff_surjective_and_card _).2
    ⟨patternRestriction_surjective θ hST,
      by simpa [patternComplexity, Nat.card_eq_fintype_card] using hcard.symm⟩).1

theorem unique_pattern_extension (θ : Lattice → A) {S T : Finset Lattice}
    (hST : S ⊆ T) (hcard : patternComplexity θ S = patternComplexity θ T)
    {u v : Lattice} (h : patternAt θ S u = patternAt θ S v) :
    patternAt θ T u = patternAt θ T v := by
  have hinj := patternRestriction_injective_of_card_eq θ hST hcard
  have h' : patternRestriction θ hST ⟨patternAt θ T u, ⟨u, rfl⟩⟩ =
      patternRestriction θ hST ⟨patternAt θ T v, ⟨v, rfl⟩⟩ := Subtype.ext h
  exact congrArg Subtype.val (hinj h')

/-- Recoding is onto the actual encoded pattern set, even when colours merge. -/
def patternEncoding (f : A → B) (θ : Lattice → A) (S : Finset Lattice) :
    patternSet θ S → patternSet (encode f θ) S := fun p =>
  ⟨fun s => f (p.val s), by
    rcases p.property with ⟨u, hu⟩
    exact ⟨u, by rw [← hu]; rfl⟩⟩

theorem patternEncoding_surjective (f : A → B) (θ : Lattice → A)
    (S : Finset Lattice) : Function.Surjective (patternEncoding f θ S) := by
  rintro ⟨p, u, rfl⟩
  exact ⟨⟨patternAt θ S u, ⟨u, rfl⟩⟩, rfl⟩

theorem patternEncoding_injective {f : A → B} (hf : Function.Injective f)
    (θ : Lattice → A) (S : Finset Lattice) :
    Function.Injective (patternEncoding f θ S) := by
  intro p q h
  apply Subtype.ext
  funext s
  exact hf (congrFun (congrArg Subtype.val h) s)

theorem patternComplexity_encode_le (f : A → B) (θ : Lattice → A)
    (S : Finset Lattice) : patternComplexity (encode f θ) S ≤ patternComplexity θ S := by
  classical
  simpa [patternComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_surjective _ (patternEncoding_surjective f θ S)

theorem patternComplexity_encode_eq {f : A → B} (hf : Function.Injective f)
    (θ : Lattice → A) (S : Finset Lattice) :
    patternComplexity (encode f θ) S = patternComplexity θ S := by
  classical
  apply le_antisymm (patternComplexity_encode_le f θ S)
  simpa [patternComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective _ (patternEncoding_injective hf θ S)

end Counting

/-- A finite-window cylinder: the configurations agreeing with `ξ` on `S`. -/
def cylinder (ξ : Lattice → A) (S : Finset Lattice) : Set (Lattice → A) :=
  {η | ∀ z ∈ S, η z = ξ z}

theorem self_mem_cylinder (ξ : Lattice → A) (S : Finset Lattice) : ξ ∈ cylinder ξ S :=
  fun _ _ => rfl

theorem cylinder_mono (ξ : Lattice → A) {S T : Finset Lattice} (hST : S ⊆ T) :
    cylinder ξ T ⊆ cylinder ξ S := fun _ h z hz => h z (hST hz)

theorem cylinder_inter (ξ : Lattice → A) (S T : Finset Lattice) :
    cylinder ξ (S ∪ T) = cylinder ξ S ∩ cylinder ξ T := by
  classical
  ext η
  simp [cylinder, Finset.mem_union, or_imp, forall_and]

theorem cylinder_empty (ξ : Lattice → A) : cylinder ξ ∅ = Set.univ := by
  ext η
  simp [cylinder]

/-- The language hull is defined using finite agreement with actual translates. -/
def languageHull (θ : Lattice → A) : Set (Lattice → A) :=
  {ξ | ∀ S : Finset Lattice, ∃ u : Lattice, ∀ z ∈ S, θ (u + z) = ξ z}

theorem self_mem_languageHull (θ : Lattice → A) : θ ∈ languageHull θ := by
  intro S
  exact ⟨0, by simp⟩

theorem orbit_subset_languageHull (θ : Lattice → A) : orbit θ ⊆ languageHull θ := by
  rintro _ ⟨u, rfl⟩ S
  exact ⟨u, by simp⟩

theorem shift_mem_languageHull {θ ξ : Lattice → A} (hξ : ξ ∈ languageHull θ)
    (u : Lattice) : shift u ξ ∈ languageHull θ := by
  classical
  intro S
  obtain ⟨v, hv⟩ := hξ (S.image (fun z => u + z))
  refine ⟨v + u, ?_⟩
  intro z hz
  have h := hv (u + z) (Finset.mem_image_of_mem _ hz)
  simpa [shift, add_assoc] using h

theorem languageHull_shift (θ : Lattice → A) (u : Lattice) :
    languageHull (shift u θ) = languageHull θ := by
  ext ξ
  constructor
  · intro h S
    obtain ⟨v, hv⟩ := h S
    exact ⟨u + v, by simpa [shift, add_assoc] using hv⟩
  · intro h S
    obtain ⟨v, hv⟩ := h S
    refine ⟨v - u, ?_⟩
    intro z hz
    change θ (u + ((v - u) + z)) = ξ z
    convert hv z hz using 1 <;> congr 1 <;> abel

theorem languageHull_trans {θ ξ η : Lattice → A} (hξ : ξ ∈ languageHull θ)
    (hη : η ∈ languageHull ξ) : η ∈ languageHull θ := by
  intro S
  obtain ⟨u, hu⟩ := hη S
  obtain ⟨v, hv⟩ := shift_mem_languageHull hξ u S
  exact ⟨v, fun z hz => (hv z hz).trans (hu z hz)⟩

theorem languageHull_subset_of_mem {θ ξ : Lattice → A} (hξ : ξ ∈ languageHull θ) :
    languageHull ξ ⊆ languageHull θ := fun _ hη => languageHull_trans hξ hη

theorem encode_mem_languageHull (f : A → B) {θ ξ : Lattice → A}
    (hξ : ξ ∈ languageHull θ) : encode f ξ ∈ languageHull (encode f θ) := by
  intro S
  obtain ⟨u, hu⟩ := hξ S
  exact ⟨u, fun z hz => congrArg f (hu z hz)⟩

section LanguageCounting

variable [Fintype A]

theorem mem_languageHull_iff_patterns (θ ξ : Lattice → A) :
    ξ ∈ languageHull θ ↔ ∀ S : Finset Lattice, patternAt ξ S 0 ∈ patternSet θ S := by
  constructor
  · intro h S
    obtain ⟨u, hu⟩ := h S
    exact ⟨u, by funext z; simpa [patternAt] using hu z z.property⟩
  · intro h S
    obtain ⟨u, hu⟩ := h S
    exact ⟨u, fun z hz => by
      have h' := congrFun hu ⟨z, hz⟩
      simpa [patternAt] using h'⟩

theorem patternSet_subset_of_mem_languageHull {θ ξ : Lattice → A}
    (hξ : ξ ∈ languageHull θ) (S : Finset Lattice) : patternSet ξ S ⊆ patternSet θ S := by
  rintro p ⟨u, rfl⟩
  have h := (mem_languageHull_iff_patterns θ (shift u ξ)).mp
    (shift_mem_languageHull hξ u) S
  simpa [patternAt_shift] using h

theorem patternComplexity_le_of_mem_languageHull {θ ξ : Lattice → A}
    (hξ : ξ ∈ languageHull θ) (S : Finset Lattice) :
    patternComplexity ξ S ≤ patternComplexity θ S := by
  classical
  let f : patternSet ξ S → patternSet θ S := fun p =>
    ⟨p.val, patternSet_subset_of_mem_languageHull hξ S p.property⟩
  have hf : Function.Injective f := by
    intro p q h
    exact Subtype.ext (congrArg (fun p : patternSet θ S => p.val) h)
  simpa [patternComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective f hf

theorem local_constraint_of_mem_languageHull {θ ξ : Lattice → A}
    (hξ : ξ ∈ languageHull θ) (S : Finset Lattice) (P : (S → A) → Prop)
    (hP : ∀ u, P (patternAt θ S u)) : ∀ u, P (patternAt ξ S u) := by
  intro u
  obtain ⟨v, hv⟩ := patternSet_subset_of_mem_languageHull hξ S ⟨u, rfl⟩
  rw [← hv]
  exact hP v

end LanguageCounting

section Topology

variable [TopologicalSpace A] [DiscreteTopology A]

theorem continuous_shift (u : Lattice) : Continuous (shift u :
    (Lattice → A) → Lattice → A) := by
  exact continuous_pi (fun z => continuous_apply (u + z))

/-- The product-topology orbit closure, rather than a formal language surrogate. -/
def orbitClosure (θ : Lattice → A) : Set (Lattice → A) := closure (orbit θ)

theorem isOpen_cylinder (ξ : Lattice → A) (S : Finset Lattice) : IsOpen (cylinder ξ S) := by
  have heq : cylinder ξ S = ⋂ z ∈ S, {η : Lattice → A | η z = ξ z} := by
    ext η
    simp [cylinder]
  rw [heq]
  apply isOpen_biInter_finset
  intro z _
  have h : IsOpen ((fun η : Lattice → A => η z) ⁻¹' ({ξ z} : Set A)) :=
    (continuous_apply z).isOpen_preimage _ (isOpen_discrete _)
  convert h using 1
  ext η
  simp

theorem orbitClosure_subset_languageHull (θ : Lattice → A) :
    orbitClosure θ ⊆ languageHull θ := by
  intro ξ hξ S
  obtain ⟨η, hηc, u, hu⟩ := mem_closure_iff.mp hξ (cylinder ξ S)
    (isOpen_cylinder ξ S) (self_mem_cylinder ξ S)
  exact ⟨u, fun z hz => by simpa [← hu, shift] using hηc z hz⟩

theorem languageHull_subset_orbitClosure (θ : Lattice → A) :
    languageHull θ ⊆ orbitClosure θ := by
  intro ξ hξ
  apply mem_closure_iff.mpr
  intro U hU hξU
  have hn := hU.mem_nhds hξU
  rw [nhds_pi] at hn
  obtain ⟨S, t, ht, hsub⟩ := Filter.mem_pi'.mp hn
  obtain ⟨u, hu⟩ := hξ S
  refine ⟨shift u θ, hsub ?_, ⟨u, rfl⟩⟩
  intro z hz
  change θ (u + z) ∈ t z
  rw [hu z hz]
  exact mem_of_mem_nhds (ht z)

theorem orbitClosure_eq_languageHull (θ : Lattice → A) :
    orbitClosure θ = languageHull θ :=
  Set.Subset.antisymm (orbitClosure_subset_languageHull θ)
    (languageHull_subset_orbitClosure θ)

theorem mem_orbitClosure_iff_finite_agreement (θ ξ : Lattice → A) :
    ξ ∈ orbitClosure θ ↔ ∀ S : Finset Lattice,
      ∃ u : Lattice, ∀ z ∈ S, θ (u + z) = ξ z := by
  rw [orbitClosure_eq_languageHull]
  rfl

theorem orbit_subset_orbitClosure (θ : Lattice → A) : orbit θ ⊆ orbitClosure θ :=
  subset_closure

theorem self_mem_orbitClosure (θ : Lattice → A) : θ ∈ orbitClosure θ :=
  orbit_subset_orbitClosure θ (self_mem_orbit θ)

theorem shift_mem_orbitClosure {θ ξ : Lattice → A} (hξ : ξ ∈ orbitClosure θ)
    (u : Lattice) : shift u ξ ∈ orbitClosure θ := by
  rw [orbitClosure_eq_languageHull] at hξ ⊢
  exact shift_mem_languageHull hξ u

theorem orbitClosure_shift (θ : Lattice → A) (u : Lattice) :
    orbitClosure (shift u θ) = orbitClosure θ := by
  simp [orbitClosure, orbit_shift]

theorem orbitClosure_subset_of_mem {θ ξ : Lattice → A} (hξ : ξ ∈ orbitClosure θ) :
    orbitClosure ξ ⊆ orbitClosure θ := by
  rw [orbitClosure_eq_languageHull] at hξ ⊢
  rw [orbitClosure_eq_languageHull]
  exact languageHull_subset_of_mem hξ

theorem isClosed_orbitClosure (θ : Lattice → A) : IsClosed (orbitClosure θ) :=
  isClosed_closure

theorem patternSet_subset_of_mem_orbitClosure [Fintype A] {θ ξ : Lattice → A}
    (hξ : ξ ∈ orbitClosure θ) (S : Finset Lattice) : patternSet ξ S ⊆ patternSet θ S := by
  rw [orbitClosure_eq_languageHull] at hξ
  exact patternSet_subset_of_mem_languageHull hξ S

theorem patternComplexity_le_of_mem_orbitClosure [Fintype A] {θ ξ : Lattice → A}
    (hξ : ξ ∈ orbitClosure θ) (S : Finset Lattice) :
    patternComplexity ξ S ≤ patternComplexity θ S := by
  rw [orbitClosure_eq_languageHull] at hξ
  exact patternComplexity_le_of_mem_languageHull hξ S

theorem local_constraint_of_mem_orbitClosure [Fintype A] {θ ξ : Lattice → A}
    (hξ : ξ ∈ orbitClosure θ) (S : Finset Lattice) (P : (S → A) → Prop)
    (hP : ∀ u, P (patternAt θ S u)) : ∀ u, P (patternAt ξ S u) := by
  rw [orbitClosure_eq_languageHull] at hξ
  exact local_constraint_of_mem_languageHull hξ S P hP

end Topology

section TranslatedWindows

variable [Fintype A]

def translateWindow (u : Lattice) (S : Finset Lattice) : Finset Lattice :=
  S.map ⟨fun z => u + z, add_right_injective u⟩

def translateWindowEquiv (u : Lattice) (S : Finset Lattice) : S ≃ translateWindow u S where
  toFun s := ⟨u + s, Finset.mem_map.mpr ⟨s, s.property, rfl⟩⟩
  invFun t := ⟨t - u, by
    rcases Finset.mem_map.mp t.property with ⟨s, hs, heq⟩
    rw [← heq]
    simpa [add_sub_cancel_left] using hs⟩
  left_inv s := by
    apply Subtype.ext
    change u + s - u = s
    abel
  right_inv t := by
    apply Subtype.ext
    change u + (t - u) = t
    abel

def translatedPatternMap (θ : Lattice → A) (u : Lattice) (S : Finset Lattice) :
    patternSet θ (translateWindow u S) → patternSet θ S := fun p =>
  ⟨fun s => p.val (translateWindowEquiv u S s), by
    rcases p.property with ⟨v, hv⟩
    refine ⟨v + u, ?_⟩
    rw [← hv]
    funext s
    simp [patternAt, translateWindowEquiv, add_assoc]⟩

theorem translatedPatternMap_injective (θ : Lattice → A) (u : Lattice)
    (S : Finset Lattice) : Function.Injective (translatedPatternMap θ u S) := by
  intro p q hpq
  apply Subtype.ext
  funext t
  obtain ⟨s, rfl⟩ := (translateWindowEquiv u S).surjective t
  exact congrFun (congrArg (fun p : patternSet θ S => p.val) hpq) s

theorem translatedPatternMap_surjective (θ : Lattice → A) (u : Lattice)
    (S : Finset Lattice) : Function.Surjective (translatedPatternMap θ u S) := by
  rintro ⟨p, v, rfl⟩
  refine ⟨⟨patternAt θ (translateWindow u S) (v - u), ⟨v - u, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  funext s
  change θ ((v - u) + (u + s)) = θ (v + s)
  congr 1
  abel

theorem patternComplexity_translateWindow (θ : Lattice → A) (u : Lattice)
    (S : Finset Lattice) :
    patternComplexity θ (translateWindow u S) = patternComplexity θ S := by
  classical
  rw [patternComplexity, patternComplexity, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.ofBijective _
    ⟨translatedPatternMap_injective θ u S, translatedPatternMap_surjective θ u S⟩)

theorem card_translateWindow (u : Lattice) (S : Finset Lattice) :
    (translateWindow u S).card = S.card := Finset.card_map _

theorem low_complexity_translateWindow_iff (θ : Lattice → A) (u : Lattice)
    (S : Finset Lattice) :
    patternComplexity θ (translateWindow u S) ≤ (translateWindow u S).card ↔
      patternComplexity θ S ≤ S.card := by
  rw [patternComplexity_translateWindow, card_translateWindow]

end TranslatedWindows

section ProductCounting

variable [Fintype A] [Fintype B]

def pairConfiguration (θ : Lattice → A) (η : Lattice → B) : Lattice → A × B :=
  fun z => (θ z, η z)

def pairPatternMap (θ : Lattice → A) (η : Lattice → B) (S : Finset Lattice) :
    patternSet (pairConfiguration θ η) S → patternSet θ S × patternSet η S := fun p =>
  (⟨fun s => (p.val s).1, by
    rcases p.property with ⟨u, hu⟩
    exact ⟨u, by rw [← hu]; rfl⟩⟩,
   ⟨fun s => (p.val s).2, by
    rcases p.property with ⟨u, hu⟩
    exact ⟨u, by rw [← hu]; rfl⟩⟩)

theorem pairPatternMap_injective (θ : Lattice → A) (η : Lattice → B)
    (S : Finset Lattice) : Function.Injective (pairPatternMap θ η S) := by
  intro p q h
  apply Subtype.ext
  funext s
  apply Prod.ext
  · exact congrFun (congrArg (fun x : patternSet θ S × patternSet η S => x.1.val) h) s
  · exact congrFun (congrArg (fun x : patternSet θ S × patternSet η S => x.2.val) h) s

theorem patternComplexity_pair_le (θ : Lattice → A) (η : Lattice → B)
    (S : Finset Lattice) : patternComplexity (pairConfiguration θ η) S ≤
      patternComplexity θ S * patternComplexity η S := by
  classical
  simpa [patternComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective _ (pairPatternMap_injective θ η S)

theorem patternComplexity_le_pair_left (θ : Lattice → A) (η : Lattice → B)
    (S : Finset Lattice) : patternComplexity θ S ≤ patternComplexity (pairConfiguration θ η) S :=
  patternComplexity_encode_le Prod.fst (pairConfiguration θ η) S

theorem patternComplexity_le_pair_right (θ : Lattice → A) (η : Lattice → B)
    (S : Finset Lattice) : patternComplexity η S ≤ patternComplexity (pairConfiguration θ η) S :=
  patternComplexity_encode_le Prod.snd (pairConfiguration θ η) S

def unionPatternMap (θ : Lattice → A) (S T : Finset Lattice) :
    patternSet θ (S ∪ T) → patternSet θ S × patternSet θ T := fun p =>
  (patternRestriction θ Finset.subset_union_left p,
    patternRestriction θ Finset.subset_union_right p)

theorem unionPatternMap_injective (θ : Lattice → A) (S T : Finset Lattice) :
    Function.Injective (unionPatternMap θ S T) := by
  intro p q h
  apply Subtype.ext
  funext s
  rcases Finset.mem_union.mp s.property with hs | ht
  · exact congrFun (congrArg (fun x : patternSet θ S × patternSet θ T => x.1.val) h) ⟨s, hs⟩
  · exact congrFun (congrArg (fun x : patternSet θ S × patternSet θ T => x.2.val) h) ⟨s, ht⟩

theorem patternComplexity_union_le (θ : Lattice → A) (S T : Finset Lattice) :
    patternComplexity θ (S ∪ T) ≤ patternComplexity θ S * patternComplexity θ T := by
  classical
  simpa [patternComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective _ (unionPatternMap_injective θ S T)

end ProductCounting

section FiberCounting

variable {M N : Type*} [Fintype M] [Fintype N]

/-- The exact number of extensions of a value under a finite restriction map. -/
noncomputable def extensionCount (f : M → N) (y : N) : ℕ :=
  Nat.card {x : M // f x = y}

theorem sum_extensionCount (f : M → N) : ∑ y : N, extensionCount f y = Fintype.card M := by
  classical
  simp only [extensionCount, Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

theorem extensionCount_pos {f : M → N} (hf : Function.Surjective f) (y : N) :
    0 < extensionCount f y := by
  classical
  obtain ⟨x, hx⟩ := hf y
  haveI : Nonempty {x : M // f x = y} := ⟨⟨x, hx⟩⟩
  simpa [extensionCount, Nat.card_eq_fintype_card] using
    Fintype.card_pos (α := {x : M // f x = y})

/-- The surplus over one extension per value is exactly the cardinality difference. -/
theorem extension_surplus (f : M → N) (hf : Function.Surjective f) :
    (∑ y : N, (extensionCount f y - 1)) + Fintype.card N = Fintype.card M := by
  classical
  calc
    (∑ y : N, (extensionCount f y - 1)) + Fintype.card N =
        ∑ y : N, ((extensionCount f y - 1) + 1) := by
      simp [Finset.sum_add_distrib]
    _ = ∑ y : N, extensionCount f y := by
      apply Finset.sum_congr rfl
      intro y _
      exact Nat.sub_add_cancel (extensionCount_pos hf y)
    _ = Fintype.card M := sum_extensionCount f

/-- Each value with two distinct extensions consumes at least one surplus unit. -/
theorem multiextension_card_bound (f : M → N) (hf : Function.Surjective f)
    (Γ : Finset N) (hΓ : ∀ y ∈ Γ, 2 ≤ extensionCount f y) :
    Γ.card + Fintype.card N ≤ Fintype.card M := by
  classical
  have hsum : Γ.card ≤ ∑ y : N, (extensionCount f y - 1) := by
    calc
      Γ.card = ∑ _y ∈ Γ, 1 := by simp
      _ ≤ ∑ y ∈ Γ, (extensionCount f y - 1) := by
        apply Finset.sum_le_sum
        intro y hy
        have h := hΓ y hy
        omega
      _ ≤ ∑ y : N, (extensionCount f y - 1) :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hs := extension_surplus f hf
  omega

theorem two_extensions_imply_count {f : M → N} {y : N} {x x' : M}
    (hx : f x = y) (hx' : f x' = y) (hne : x ≠ x') : 2 ≤ extensionCount f y := by
  classical
  let a : {x : M // f x = y} := ⟨x, hx⟩
  let b : {x : M // f x = y} := ⟨x', hx'⟩
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
  have hcard : 2 ≤ Fintype.card {x : M // f x = y} :=
    Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
  simpa [extensionCount, Nat.card_eq_fintype_card] using hcard

end FiberCounting

section PatternAmbiguity

variable [Fintype A]

theorem ambiguous_pattern_card_bound (θ : Lattice → A) {S T : Finset Lattice}
    (hST : S ⊆ T) (Γ : Finset (patternSet θ S))
    (hΓ : ∀ p ∈ Γ, ∃ q q' : patternSet θ T,
      patternRestriction θ hST q = p ∧ patternRestriction θ hST q' = p ∧ q ≠ q') :
    Γ.card + patternComplexity θ S ≤ patternComplexity θ T := by
  classical
  have h := multiextension_card_bound (patternRestriction θ hST)
    (patternRestriction_surjective θ hST) Γ (fun p hp => by
      obtain ⟨q, q', hq, hq', hne⟩ := hΓ p hp
      exact two_extensions_imply_count hq hq' hne)
  simpa [patternComplexity, Nat.card_eq_fintype_card] using h

theorem ambiguity_budget (θ : Lattice → A) {S T : Finset Lattice}
    (hST : S ⊆ T) (n : ℕ) (Γ : Finset (patternSet θ S))
    (hbudget : patternComplexity θ T < patternComplexity θ S + n)
    (hΓ : ∀ p ∈ Γ, ∃ q q' : patternSet θ T,
      patternRestriction θ hST q = p ∧ patternRestriction θ hST q' = p ∧ q ≠ q') :
    Γ.card < n := by
  have h := ambiguous_pattern_card_bound θ hST Γ hΓ
  omega

end PatternAmbiguity

section LocalObservables

variable [Fintype A]

/-- An arbitrary observable of a fixed finite pattern. -/
def localObservable (S : Finset Lattice) (f : (S → A) → B) (ξ : Lattice → A)
    (u : Lattice) : B := f (patternAt ξ S u)

theorem localObservable_shift (S : Finset Lattice) (f : (S → A) → B)
    (ξ : Lattice → A) (u v : Lattice) :
    localObservable S f (shift u ξ) v = localObservable S f ξ (u + v) := by
  unfold localObservable
  rw [patternAt_shift]

theorem localObservable_eq_of_pattern_eq (S : Finset Lattice) (f : (S → A) → B)
    {ξ η : Lattice → A} {u v : Lattice}
    (h : patternAt ξ S u = patternAt η S v) :
    localObservable S f ξ u = localObservable S f η v := congrArg f h

theorem localObservable_range_subset {θ ξ : Lattice → A} (hξ : ξ ∈ languageHull θ)
    (S : Finset Lattice) (f : (S → A) → B) :
    Set.range (localObservable S f ξ) ⊆ Set.range (localObservable S f θ) := by
  rintro y ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := patternSet_subset_of_mem_languageHull hξ S ⟨u, rfl⟩
  exact ⟨v, congrArg f hv⟩

theorem localObservable_constant_of_mem_languageHull {θ ξ : Lattice → A}
    (hξ : ξ ∈ languageHull θ) (S : Finset Lattice) (f : (S → A) → B) (b : B)
    (hf : ∀ u, localObservable S f θ u = b) :
    ∀ u, localObservable S f ξ u = b :=
  local_constraint_of_mem_languageHull hξ S (fun p => f p = b) hf

theorem localObservable_predicate_of_mem_languageHull {θ ξ : Lattice → A}
    (hξ : ξ ∈ languageHull θ) (S : Finset Lattice) (f : (S → A) → B) (P : B → Prop)
    (hf : ∀ u, P (localObservable S f θ u)) : ∀ u, P (localObservable S f ξ u) :=
  local_constraint_of_mem_languageHull hξ S (fun p => P (f p)) hf

variable [TopologicalSpace A] [DiscreteTopology A]

theorem continuous_patternAt (S : Finset Lattice) (u : Lattice) :
    Continuous (fun ξ : Lattice → A => patternAt ξ S u) :=
  continuous_pi (fun s => continuous_apply (u + s))

theorem continuous_localObservable [TopologicalSpace B] (S : Finset Lattice)
    (f : (S → A) → B) (u : Lattice) :
    Continuous (fun ξ : Lattice → A => localObservable S f ξ u) :=
  continuous_of_discreteTopology.comp (continuous_patternAt S u)

theorem localObservable_constant_of_mem_orbitClosure {θ ξ : Lattice → A}
    (hξ : ξ ∈ orbitClosure θ) (S : Finset Lattice) (f : (S → A) → B) (b : B)
    (hf : ∀ u, localObservable S f θ u = b) :
    ∀ u, localObservable S f ξ u = b := by
  rw [orbitClosure_eq_languageHull] at hξ
  exact localObservable_constant_of_mem_languageHull hξ S f b hf

end LocalObservables

section LinearObservables

variable [Fintype A] {R : Type*} [Semiring R]

/-- Evaluation of a finitely supported convolution against a scalar encoding. -/
def finiteLinearObservable (c : Lattice →₀ R) (w : A → R) (ξ : Lattice → A)
    (u : Lattice) : R := ∑ z ∈ c.support, c z * w (ξ (u + z))

theorem finiteLinearObservable_eq_local (c : Lattice →₀ R) (w : A → R)
    (ξ : Lattice → A) (u : Lattice) :
    finiteLinearObservable c w ξ u =
      localObservable c.support (fun p => ∑ z : c.support, c z * w (p z)) ξ u := by
  classical
  simp only [finiteLinearObservable, localObservable, patternAt]
  exact (Finset.sum_attach _ _).symm

theorem finiteLinearObservable_shift (c : Lattice →₀ R) (w : A → R)
    (ξ : Lattice → A) (u v : Lattice) :
    finiteLinearObservable c w (shift u ξ) v = finiteLinearObservable c w ξ (u + v) := by
  simp only [finiteLinearObservable, shift]
  apply Finset.sum_congr rfl
  intro z _
  congr 2
  abel

theorem linear_relation_passes_to_languageHull {θ ξ : Lattice → A}
    (hξ : ξ ∈ languageHull θ) (c : Lattice →₀ R) (w : A → R) (b : R)
    (hc : ∀ u, finiteLinearObservable c w θ u = b) :
    ∀ u, finiteLinearObservable c w ξ u = b := by
  simp only [finiteLinearObservable_eq_local] at hc ⊢
  exact localObservable_constant_of_mem_languageHull hξ _ _ b hc

theorem annihilation_passes_to_languageHull {θ ξ : Lattice → A}
    (hξ : ξ ∈ languageHull θ) (c : Lattice →₀ R) (w : A → R)
    (hc : ∀ u, finiteLinearObservable c w θ u = 0) :
    ∀ u, finiteLinearObservable c w ξ u = 0 :=
  linear_relation_passes_to_languageHull hξ c w 0 hc

variable [TopologicalSpace A] [DiscreteTopology A]

theorem linear_relation_passes_to_orbitClosure {θ ξ : Lattice → A}
    (hξ : ξ ∈ orbitClosure θ) (c : Lattice →₀ R) (w : A → R) (b : R)
    (hc : ∀ u, finiteLinearObservable c w θ u = b) :
    ∀ u, finiteLinearObservable c w ξ u = b := by
  rw [orbitClosure_eq_languageHull] at hξ
  exact linear_relation_passes_to_languageHull hξ c w b hc

theorem annihilation_passes_to_orbitClosure {θ ξ : Lattice → A}
    (hξ : ξ ∈ orbitClosure θ) (c : Lattice →₀ R) (w : A → R)
    (hc : ∀ u, finiteLinearObservable c w θ u = 0) :
    ∀ u, finiteLinearObservable c w ξ u = 0 :=
  linear_relation_passes_to_orbitClosure hξ c w 0 hc

end LinearObservables

section PointwiseLimits

variable [TopologicalSpace A] [DiscreteTopology A]

/-- Pointwise eventual stabilization of translates yields an orbit-closure point. -/
theorem mem_orbitClosure_of_eventually_equal {θ ξ : Lattice → A} (u : ℕ → Lattice)
    (hlim : ∀ z, ∀ᶠ n in Filter.atTop, θ (u n + z) = ξ z) : ξ ∈ orbitClosure θ := by
  classical
  rw [mem_orbitClosure_iff_finite_agreement]
  intro S
  have hfinite : ∀ᶠ n in Filter.atTop, ∀ z ∈ S, θ (u n + z) = ξ z :=
    (S.eventually_all).mpr (fun z _ => hlim z)
  obtain ⟨n, hn⟩ := hfinite.exists
  exact ⟨u n, hn⟩

theorem mem_orbitClosure_of_finite_stabilization {θ ξ : Lattice → A}
    (u : ℕ → Lattice)
    (hlim : ∀ S : Finset Lattice, ∃ N : ℕ, ∀ n ≥ N,
      ∀ z ∈ S, θ (u n + z) = ξ z) : ξ ∈ orbitClosure θ := by
  rw [mem_orbitClosure_iff_finite_agreement]
  intro S
  obtain ⟨N, hN⟩ := hlim S
  exact ⟨u N, hN N le_rfl⟩

theorem encode_mem_orbitClosure_iff [TopologicalSpace B] [DiscreteTopology B]
    {f : A → B} (hf : Function.Injective f) (θ ξ : Lattice → A) :
    encode f ξ ∈ orbitClosure (encode f θ) ↔ ξ ∈ orbitClosure θ := by
  rw [orbitClosure_eq_languageHull, orbitClosure_eq_languageHull]
  constructor
  · intro h S
    obtain ⟨u, hu⟩ := h S
    exact ⟨u, fun z hz => hf (hu z hz)⟩
  · intro h
    exact encode_mem_languageHull f h

end PointwiseLimits

section DeficitSelection

variable [Fintype A]

/-- Signed complexity deficit is needed when the deletion process reaches the empty set. -/
noncomputable def complexityDefect (θ : Lattice → A) (S : Finset Lattice) : ℤ :=
  (patternComplexity θ S : ℤ) - S.card

theorem complexityDefect_empty (θ : Lattice → A) : complexityDefect θ ∅ = 1 := by
  simp [complexityDefect, patternComplexity_empty]

/-- A finite chain going from nonpositive to positive has a first crossing edge. -/
theorem exists_defect_crossing (f : ℕ → ℤ) {N : ℕ} (hzero : f 0 ≤ 0)
    (hN : 0 < f N) : ∃ i < N, f i ≤ 0 ∧ 0 < f (i + 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hprev : f N ≤ 0
    · exact ⟨N, Nat.lt_succ_self N, hprev, hN⟩
    · obtain ⟨i, hi, hlow, hhigh⟩ := ih (lt_of_not_ge hprev)
      exact ⟨i, Nat.lt_succ_of_lt hi, hlow, hhigh⟩

/-- The numerical part of balanced-set selection: a deletion chain supplies both budgets. -/
theorem exists_window_budget_crossing (θ : Lattice → A) (D : ℕ → Finset Lattice)
    (N : ℕ) (hstart : patternComplexity θ (D 0) ≤ (D 0).card) (hend : D N = ∅)
    (hdelete : ∀ i < N, D (i + 1) ⊆ D i) :
    ∃ i < N, (D i).Nonempty ∧ patternComplexity θ (D i) ≤ (D i).card ∧
      (D (i + 1)).card < patternComplexity θ (D (i + 1)) ∧
      patternComplexity θ (D i) <
        patternComplexity θ (D (i + 1)) + (D i \ D (i + 1)).card := by
  classical
  have hzero : complexityDefect θ (D 0) ≤ 0 := by
    unfold complexityDefect
    omega
  have hN : 0 < complexityDefect θ (D N) := by
    rw [hend, complexityDefect_empty]
    norm_num
  obtain ⟨i, hi, hlow, hhigh⟩ := exists_defect_crossing
    (fun i => complexityDefect θ (D i)) hzero hN
  unfold complexityDefect at hlow hhigh
  have hlow' : patternComplexity θ (D i) ≤ (D i).card := by omega
  have hhigh' : (D (i + 1)).card < patternComplexity θ (D (i + 1)) := by omega
  have hcard := Finset.card_sdiff_of_subset (hdelete i hi)
  have hsubsetCard := Finset.card_le_card (hdelete i hi)
  have hnonempty : (D i).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro heq
    simpa [heq, patternComplexity_empty] using hlow'
  exact ⟨i, hi, hnonempty, hlow', hhigh', by omega⟩

/-- A bounded total increase forces one restriction edge to be a bijection. -/
theorem exists_plateau_from_growth_budget (p : ℕ → ℕ) {N : ℕ}
    (hstep : ∀ i < N, p i ≤ p (i + 1)) (hbudget : p N < p 0 + N) :
    ∃ i < N, p i = p (i + 1) := by
  by_contra hn
  have hstrict : ∀ i < N, p i + 1 ≤ p (i + 1) := by
    intro i hi
    have hle := hstep i hi
    have hne : p i ≠ p (i + 1) := fun h => hn ⟨i, hi, h⟩
    omega
  have hgrow : ∀ i ≤ N, p 0 + i ≤ p i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hp := ih (Nat.le_of_succ_le hi)
      have hs := hstrict i (Nat.lt_of_succ_le hi)
      omega
  have h := hgrow N le_rfl
  omega

/-- The two determination rules of Appendix D arise by applying this to the two row orders. -/
theorem exists_determining_window_step (θ : Lattice → A) (D : ℕ → Finset Lattice)
    (N : ℕ) (hadd : ∀ i < N, D i ⊆ D (i + 1))
    (hbudget : patternComplexity θ (D N) < patternComplexity θ (D 0) + N) :
    ∃ i, ∃ hi : i < N, ∀ u v : Lattice,
      patternAt θ (D i) u = patternAt θ (D i) v →
        patternAt θ (D (i + 1)) u = patternAt θ (D (i + 1)) v := by
  obtain ⟨i, hi, hplateau⟩ := exists_plateau_from_growth_budget
    (fun i => patternComplexity θ (D i))
    (fun i hi => patternComplexity_mono θ (hadd i hi)) hbudget
  exact ⟨i, hi, fun u v h => unique_pattern_extension θ (hadd i hi) hplateau h⟩

end DeficitSelection

end NivatTrial.Dynamics
