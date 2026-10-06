import NivatTrial.ColleMaximalSeedDefect
import NivatTrial.ColleFiniteDefectLimits
import NivatTrial.ColleEnvelopeRays

/-! Maximal agreement survives a growing-window limit in the precise
finite-window form needed at a second boundary. The ambient half-strips
eventually cover every finite part of the original bottom half-plane. -/

namespace NivatTrial.ColleMaximalAgreementLimit

open NivatTrial.Geometry NivatTrial.LatticePolygon NivatTrial.RegionGeometry
open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.NonexpansiveExistence
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeExpansion NivatTrial.ColleEnvelopeLimits
open NivatTrial.ColleFiniteEnvelope NivatTrial.ColleHalfStripEnvelope
open NivatTrial.ColleEnvelopeRays NivatTrial.ColleHullCoding
open NivatTrial.ColleMaximalSeedDefect NivatTrial.ColleEnvelopeGeometry
open NivatTrial.OneSidedRecurrence Filter
open scoped Classical
noncomputable section

def FiniteExtensionMaximal {A : Type*} (D : Finset Lattice)
    (x p : Lattice → A) (R Q : Set Lattice) : Prop :=
  ∀ S W : Finset Lattice,
    IsLatticeConvex S → LongFaces D (S : Set Lattice) →
    W.Nonempty → IsLatticeConvex W → LongFaces D (W : Set Lattice) →
    W ⊆ S → (W : Set Lattice) ⊆ R → (S : Set Lattice) ⊆ Q →
    AgreeOn x p (S : Set Lattice) → (S : Set Lattice) ⊆ R

theorem halfStrip_mono {T S : Finset Lattice} (u : Lattice) (hTS : T ⊆ S) :
    halfStrip T u ⊆ halfStrip S u := by
  rintro z ⟨b,hb,n,rfl⟩
  exact ⟨b,hTS hb,n,rfl⟩

/-- The sweep of the limiting envelope proves actual eventual coverage,
not an additional exhaustion assumption. -/
theorem eventually_mem_ambient_of_bottom_halfPlane
    (D : Finset Lattice) (V : ℕ → Finset Lattice)
    (hmono : ∀ m n, m ≤ n → V m ⊆ V n)
    (hR : IsEnvelope D (increasingRegion V))
    (u k : Lattice) (huk : 0 < det u k)
    (hzero : 0 ∈ increasingRegion V)
    (hback : ∀ n : ℕ, -(n•u) ∈ increasingRegion V)
    (hheight : ∀ N : ℤ, ∃ z ∈ increasingRegion V, N ≤ det u z)
    (Q : ℕ → Set Lattice) (hVQ : ∀ n, (V n : Set Lattice) ⊆ Q n)
    (hforward : ∀ n, ForwardInvariant (Q n) u)
    (z : Lattice) (hz : 0 ≤ det u z) : ∀ᶠ n : ℕ in atTop, z ∈ Q n := by
  obtain ⟨m,hm⟩ := (eventually_mem_bottom_halfPlane D (increasingRegion V) hR
    u k huk hzero hback hheight z hz).exists
  obtain ⟨N,hN⟩ := hm
  have hzstrip : z ∈ halfStrip (V N) u := by
    refine ⟨z+m•(-u),hN,m,?_⟩
    rw [smul_neg]
    abel
  filter_upwards [eventually_ge_atTop N] with n hn
  exact halfStrip_subset_of_forward (hVQ n) (hforward n)
    (halfStrip_mono u (hmono N n hn) hzstrip)

theorem eventually_finite_subset_ambient
    (D : Finset Lattice) (V : ℕ → Finset Lattice)
    (hmono : ∀ m n, m ≤ n → V m ⊆ V n)
    (hR : IsEnvelope D (increasingRegion V))
    (u k : Lattice) (huk : 0 < det u k)
    (hzero : 0 ∈ increasingRegion V)
    (hback : ∀ n : ℕ, -(n•u) ∈ increasingRegion V)
    (hheight : ∀ N : ℤ, ∃ z ∈ increasingRegion V, N ≤ det u z)
    (Q : ℕ → Set Lattice) (hVQ : ∀ n, (V n : Set Lattice) ⊆ Q n)
    (hforward : ∀ n, ForwardInvariant (Q n) u)
    (S : Finset Lattice) (hS : ∀ z ∈ S, 0 ≤ det u z) :
    ∀ᶠ n : ℕ in atTop, (S : Set Lattice) ⊆ Q n := by
  apply S.eventually_all.mpr
  intro z hz
  exact eventually_mem_ambient_of_bottom_halfPlane D V hmono hR u k huk
    hzero hback hheight Q hVQ hforward z (hS z hz)

theorem finite_extension_maximal_of_coordinate_limit {A : Type*}
    (θ p : Lattice → A) (code : A → ℤ) (hcode : Function.Injective code)
    (hs : List Lattice) (hne : ∀ d ∈ hs, d ≠ 0)
    (hind : hs.Pairwise (fun d e => det d e ≠ 0))
    (hann : iteratedIncrement hs (encode code θ) = 0)
    (hp : p ∈ languageHull θ)
    (D : Finset Lattice) (hdirs : ∀ d ∈ hs, d ∈ D ∧ -d ∈ D)
    (V : ℕ → Finset Lattice) (hmono : ∀ m n, m ≤ n → V m ⊆ V n)
    (henv : ∀ n, IsEnvelope D (V n : Set Lattice))
    (hfaces : ∀ n, LongFaces D (V n : Set Lattice))
    (Q : ℕ → Set Lattice) (hQenv : ∀ n, IsEnvelope D (Q n))
    (hVQ : ∀ n, (V n : Set Lattice) ⊆ Q n)
    (K : Set Lattice)
    (hcover : ∀ S : Finset Lattice, (S : Set Lattice) ⊆ K →
      ∀ᶠ n : ℕ in atTop, (S : Set Lattice) ⊆ Q n)
    (X : ℕ → Lattice → A) (hX : ∀ n, X n ∈ languageHull θ)
    (hagree : ∀ n, AgreeOn (X n) p (V n : Set Lattice))
    (hmax : ∀ n, ∀ R : Set Lattice, (V n : Set Lattice) ⊆ R → R ⊆ Q n →
      IsEnvelope D R → LongFaces D R → AgreeOn (X n) p R → R = (V n : Set Lattice))
    (y : Lattice → A) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : ∀ z, ∀ᶠ n : ℕ in atTop, X (φ n) z = y z) :
    FiniteExtensionMaximal D y p (increasingRegion V) K := by
  intro S W hSc hSf hW hWc hWf hWS hWR hSK hSag
  obtain ⟨N,hN⟩ := finite_subset_in_increasing_region V hmono W hWR
  have hlarge : ∀ᶠ n : ℕ in atTop, N ≤ φ n :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
  have hSQ : ∀ᶠ n : ℕ in atTop, (S : Set Lattice) ⊆ Q (φ n) :=
    hφ.tendsto_atTop.eventually (hcover S hSK)
  have hSeq : ∀ᶠ n : ℕ in atTop, ∀ z ∈ S, X (φ n) z = y z :=
    S.eventually_all.mpr (fun z _ => hlim z)
  obtain ⟨n,hn,hSQn,hSeqn⟩ := (hlarge.and (hSQ.and hSeq)).exists
  have hWV : W ⊆ V (φ n) := hN.trans (hmono N (φ n) hn)
  let R := supportHull D ((V (φ n) : Set Lattice) ∪ (S : Set Lattice))
  have hVR : (V (φ n) : Set Lattice) ⊆ R :=
    fun _ hz => subset_supportHull D _ (Or.inl hz)
  have hRQ : R ⊆ Q (φ n) := by
    intro z hz
    rw [← hQenv (φ n)]
    exact supportHull_mono D (Set.union_subset (hVQ (φ n)) hSQn) hz
  have hRf : LongFaces D R := (longFaces_union (hfaces (φ n)) hSf).supportHull
  have hRag : AgreeOn (X (φ n)) p R :=
    agreement_supportHull_union_of_common_window θ code hcode hs hne hind hann
      (X (φ n)) p (hX (φ n)) hp D (V (φ n)) S W hdirs
      (latticeConvex_finset_of_region _ (henv (φ n)).latticeConvex) hSc
      (factor_faces_of_directions hs D hdirs _ (hfaces (φ n)))
      (factor_faces_of_directions hs D hdirs _ hSf) hW hWc
      (factor_faces_of_directions hs D hdirs _ hWf) hWV hWS (hagree (φ n))
      (fun z hz => (hSeqn z hz).trans (hSag z hz))
  have heq := hmax (φ n) R hVR hRQ (supportHull_idempotent D _) hRf hRag
  intro z hz
  have hzR : z ∈ R := subset_supportHull D _ (Or.inr hz)
  rw [heq] at hzR
  exact ⟨φ n,hzR⟩

theorem limit_with_finite_defect_and_maximality {A : Type*} [Fintype A]
    (θ p : Lattice → A) (code : A → ℤ) (hcode : Function.Injective code)
    (hs : List Lattice) (hne : ∀ d ∈ hs, d ≠ 0)
    (hind : hs.Pairwise (fun d e => det d e ≠ 0))
    (hann : iteratedIncrement hs (encode code θ) = 0)
    (hp : p ∈ languageHull θ)
    (D : Finset Lattice) (hdirs : ∀ d ∈ hs, d ∈ D ∧ -d ∈ D)
    (V : ℕ → Finset Lattice) (hmono : ∀ m n, m ≤ n → V m ⊆ V n)
    (henv : ∀ n, IsEnvelope D (V n : Set Lattice))
    (hfaces : ∀ n, LongFaces D (V n : Set Lattice))
    (Q : ℕ → Set Lattice) (hQenv : ∀ n, IsEnvelope D (Q n))
    (hVQ : ∀ n, (V n : Set Lattice) ⊆ Q n)
    (K : Set Lattice)
    (hcover : ∀ S : Finset Lattice, (S : Set Lattice) ⊆ K →
      ∀ᶠ n : ℕ in atTop, (S : Set Lattice) ⊆ Q n)
    (X : ℕ → Lattice → A) (hX : ∀ n, X n ∈ languageHull θ)
    (hagree : ∀ n, AgreeOn (X n) p (V n : Set Lattice))
    (hmax : ∀ n, ∀ R : Set Lattice, (V n : Set Lattice) ⊆ R → R ⊆ Q n →
      IsEnvelope D R → LongFaces D R → AgreeOn (X n) p R → R = (V n : Set Lattice))
    (E : Finset Lattice) (hbad : ∀ n, ∃ z ∈ E, X n z ≠ p z) :
    ∃ y ∈ languageHull θ, AgreeOn y p (increasingRegion V) ∧
      (∃ z ∈ E, y z ≠ p z) ∧ FiniteExtensionMaximal D y p (increasingRegion V) K := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨y,hy,φ,hφ,hlim⟩ := (isCompact_languageHull θ).tendsto_subseq hX
  have hcoord : ∀ z, ∀ᶠ n : ℕ in atTop, X (φ n) z = y z := by
    intro z
    simpa only [Function.comp_apply] using eventually_coordinate_eq hlim z
  refine ⟨y,hy,?_,?_,finite_extension_maximal_of_coordinate_limit θ p code hcode
    hs hne hind hann hp D hdirs V hmono henv hfaces Q hQenv hVQ K hcover X hX
    hagree hmax y φ hφ hcoord⟩
  · rintro z ⟨m,hz⟩
    have hlarge : ∀ᶠ n : ℕ in atTop, m ≤ φ n :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop m)
    obtain ⟨n,hn,heq⟩ := (hlarge.and (hcoord z)).exists
    exact heq.symm.trans (hagree (φ n) z (hmono m (φ n) hn hz))
  · by_contra hn
    have hall : ∀ z ∈ E, y z = p z := by
      intro z hz
      by_contra he
      exact hn ⟨z,hz,he⟩
    have hevent : ∀ᶠ n : ℕ in atTop, ∀ z ∈ E, X (φ n) z = y z :=
      E.eventually_all.mpr (fun z _ => hcoord z)
    obtain ⟨n,heq⟩ := hevent.exists
    obtain ⟨z,hz,hbadz⟩ := hbad (φ n)
    exact hbadz ((heq z hz).trans (hall z hz))

end
end NivatTrial.ColleMaximalAgreementLimit
