import ConvexNivat.ReductionDefinitions

/-! Actual objects of published Colle §§2–4. Normals use the reviewed
ReductionDefinitions; Colle's polynomial action has the opposite exponent sign.
These definitions store geometry and source hypotheses, never conclusions of
the requested periodicity or nonexpansiveness producers. -/

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

/-- Left normal of a positively oriented rational lattice direction. -/
def normal (v : Lattice) : RealPlane := (-(v.2 : ℝ), (v.1 : ℝ))

/-- Actual support face of a finite window, including irrational normals. -/
def supportFace (S : Finset Lattice) (n : RealPlane) : Finset Lattice :=
  S.filter (fun z => ∀ q ∈ S, realDot (embed z) n ≤ realDot (embed q) n)

def supportRow (S : Finset Lattice) (v : Lattice) : Finset Lattice :=
  supportFace S (normal v)

def offFace (S : Finset Lattice) (n : RealPlane) : Finset Lattice :=
  S \ supportFace S n

/-- Source Definition 2.3's literal vertex test. -/
def WindowVertex (S : Finset Lattice) (z : Lattice) : Prop :=
  z ∈ S ∧ LatticeConvex (S.erase z)

/-- Source Definition 2.3, using the existing actual pattern-determination API. -/
def GeneratingSet (ξ : Configuration ℤ) (S : Finset Lattice) : Prop :=
  S.Nonempty ∧ LatticeConvex S ∧
    ∀ z, WindowVertex S z → PatternDetermines ξ (S.erase z) z

/-- A finite polygon's positively oriented primitive edge directions.
Colle defines edges only for hulls of positive area. -/
def edgeDirections (S : Finset Lattice) : Set Lattice :=
  {v | Primitive v ∧ (interior (windowHull S)).Nonempty ∧ 2 ≤ (supportRow S v).card}

/-- Strict extension-count bound of Lemmas 2.6 and 4.2. Keeping the +1
avoids weakening the source inequality by truncated subtraction. -/
def SmallExtensionCount (ξ : Configuration ℤ) (S : Finset Lattice)
    (n : RealPlane) : Prop :=
  complexity ξ S + 1 ≤ complexity ξ (offFace S n) + (supportFace S n).card

/-- Actual extensions of a pattern on S minus the support face. -/
def extensionSet (ξ : Configuration ℤ) (S : Finset Lattice) (n : RealPlane)
    (γ : Pattern ℤ (offFace S n)) : Set (Pattern ℤ S) :=
  {δ | δ ∈ patternSet ξ S ∧ ∀ z : {z : Lattice // z ∈ offFace S n},
    δ ⟨z.val, (Finset.mem_sdiff.mp z.property).1⟩ = γ z}

def extensionCount (ξ : Configuration ℤ) (S : Finset Lattice) (n : RealPlane)
    (γ : Pattern ℤ (offFace S n)) : ℕ := (extensionSet ξ S n γ).ncard

/-- Actual (ℓ,S,η)-ambiguity from Colle §2.3. -/
def Ambiguous (ξ : Configuration ℤ) (S : Finset Lattice) (v : Lattice)
    (x : Configuration ℤ) : Prop :=
  x ∈ OrbitClosure ξ ∧ ∀ t : ℤ,
    1 < extensionCount ξ S (normal v) (pattern x (offFace S (normal v)) (t • v))

/-- Actual positive semi-ambiguity, retaining the existential integer threshold. -/
def SemiAmbiguous (ξ : Configuration ℤ) (S : Finset Lattice) (v : Lattice)
    (x : Configuration ℤ) : Prop :=
  x ∈ OrbitClosure ξ ∧ ∃ τ : ℤ, ∀ t : ℤ, τ ≤ t →
    1 < extensionCount ξ S (normal v) (pattern x (offFace S (normal v)) (t • v))

/-- Source Definition 3.4; ℤ_+ contains zero. -/
def halfStrip (S : Finset Lattice) (v : Lattice) : Set Lattice :=
  {z | ∃ g ∈ S, ∃ t : ℕ, z = g + (t : ℤ) • v}

def saturateRay (U : Set Lattice) (v : Lattice) : Set Lattice :=
  {z | ∃ g ∈ U, ∃ t : ℕ, z = g + (t : ℤ) • v}

/-- Colle Definition 2.12 uses overlap periods, without forward invariance. -/
def OverlapHasPeriod (x : Configuration ℤ) (U : Set Lattice) (h : Lattice) : Prop :=
  ∀ z ∈ U, z + h ∈ U → x (z + h) = x z

def DirectionalPeriod (x : Configuration ℤ) (U : Set Lattice) (v : Lattice) : Prop :=
  U.Nonempty ∧ ∃ k : ℤ, k ≠ 0 ∧ OverlapHasPeriod x U (k • v)

def FullyOverlapPeriodic (x : Configuration ℤ) (U : Set Lattice) : Prop :=
  U.Nonempty ∧ ∃ h k : Lattice, Nonparallel h k ∧
    OverlapHasPeriod x U h ∧ OverlapHasPeriod x U k

/-- Exact E(S)-enveloped finite polygons (Definition 3.3). -/
def EnvelopedWindow (S B : Finset Lattice) : Prop :=
  B.Nonempty ∧ LatticeConvex B ∧ (interior (windowHull B)).Nonempty ∧
    (∀ v ∈ edgeDirections B, v ∈ edgeDirections S ∧
      (supportRow S v).card ≤ (supportRow B v).card) ∧
    (edgeDirections B).ncard = (edgeDirections S).ncard

/-- Counterclockwise cyclic enumeration of actual antiparallel polygon edges.
Integers permit precisely the source's cyclic inequalities i+1≤J≤i+m−1. -/
structure AntipodalEdgeCycle (S : Finset Lattice) (m : ℕ) where
  at_least_two : 2 ≤ m
  direction : ℤ → Lattice
  vertex : ℤ → Lattice
  direction_periodic : ∀ i, direction (i + 2 * (m : ℤ)) = direction i
  vertex_periodic : ∀ i, vertex (i + 2 * (m : ℤ)) = vertex i
  antipodal : ∀ i, direction (i + (m : ℤ)) = -direction i
  primitive : ∀ i, Primitive (direction i)
  distinct : Function.Injective (fun i : Fin (2 * m) => direction (i.val : ℤ))
  covers : ∀ v, v ∈ edgeDirections S ↔ ∃ i : Fin (2 * m), direction (i.val : ℤ) = v
  initial_mem : ∀ i, vertex i ∈ supportRow S (direction i)
  terminal_mem : ∀ i, vertex (i + 1) ∈ supportRow S (direction i)
  edge_length : ∀ i, ∃ k : ℤ, 1 ≤ k ∧ vertex (i + 1) - vertex i = k • direction i
  support_segment : ∀ i, ∀ z : Lattice,
    z ∈ supportRow S (direction i) ↔
      z ∈ S ∧ embed z ∈ segment ℝ (embed (vertex i)) (embed (vertex (i + 1)))

/-- Actual positively oriented rational two-ray polygon (Definition 3.1).
The first boundary ray is traversed toward its finite endpoint; the second
is traversed away from its finite endpoint. Finite edges join those endpoints. -/
structure Region (v w : Lattice) where
  carrier : Set RealPlane
  closed : IsClosed carrier
  convex : Convex ℝ carrier
  interior_nonempty : (interior carrier).Nonempty
  first_primitive : Primitive v
  second_primitive : Primitive w
  turn_positive : 0 < det v w
  boundedCount : ℕ
  vertex : Fin (boundedCount + 1) → Lattice
  boundedDirection : Fin boundedCount → Lattice
  bounded_primitive : ∀ i, Primitive (boundedDirection i)
  bounded_length : ∀ i : Fin boundedCount, ∃ k : ℤ, 1 ≤ k ∧
    vertex i.succ - vertex i.castSucc = k • boundedDirection i
  first_turn : ∀ i : Fin boundedCount, i.val = 0 → 0 < det v (boundedDirection i)
  bounded_turn : ∀ i j : Fin boundedCount, j.val = i.val + 1 →
    0 < det (boundedDirection i) (boundedDirection j)
  second_turn : ∀ i : Fin boundedCount, i.val + 1 = boundedCount →
    0 < det (boundedDirection i) w
  first_support : ∀ x ∈ carrier,
    0 ≤ realDet (embed v) (x - embed (vertex ⟨0, Nat.zero_lt_succ _⟩))
  second_support : ∀ x ∈ carrier,
    0 ≤ realDet (embed w) (x - embed (vertex ⟨boundedCount, Nat.lt_succ_self _⟩))
  bounded_support : ∀ i : Fin boundedCount, ∀ x ∈ carrier,
    0 ≤ realDet (embed (boundedDirection i)) (x - embed (vertex i.castSucc))
  boundary_eq : frontier carrier =
    {x | ∃ t : ℝ, 0 ≤ t ∧
      x = embed (vertex ⟨0, Nat.zero_lt_succ _⟩) - t • embed v} ∪
    {x | ∃ t : ℝ, 0 ≤ t ∧
      x = embed (vertex ⟨boundedCount, Nat.lt_succ_self _⟩) + t • embed w} ∪
    {x | ∃ i : Fin boundedCount,
      x ∈ segment ℝ (embed (vertex i.castSucc)) (embed (vertex i.succ))}

def Region.lattice {v w : Lattice} (P : Region v w) : Set Lattice := embed ⁻¹' P.carrier

def Region.firstAnchor {v w : Lattice} (P : Region v w) : Lattice :=
  P.vertex ⟨0, Nat.zero_lt_succ _⟩

def Region.secondAnchor {v w : Lattice} (P : Region v w) : Lattice :=
  P.vertex ⟨P.boundedCount, Nat.lt_succ_self _⟩

def Region.predecessor {v w : Lattice} (P : Region v w) : Lattice :=
  if h : 0 < P.boundedCount then
    P.boundedDirection ⟨P.boundedCount - 1, Nat.sub_lt h Nat.zero_lt_one⟩ else v

/-- Source Definition 3.2, using the actual predecessor direction and the first
n adjacent exterior integer rows of the second edge. -/
def Region.enlargement {v w : Lattice} (P : Region v w) (n : ℕ) : Set Lattice :=
  {z | ∃ g ∈ P.lattice, ∃ t : ℕ, z = g + (t : ℤ) • P.predecessor ∧
    (z ∈ P.lattice ∨
      det w P.secondAnchor - (n : ℤ) ≤ det w z ∧ det w z ≤ det w P.secondAnchor)}

/-- Actual primitive directions and lattice-point sets of boundary edges. -/
def Region.BoundaryEdge {v w : Lattice} (P : Region v w)
    (d : Lattice) (E : Set Lattice) : Prop :=
  (d = v ∧ E = {z | ∃ t : ℝ, 0 ≤ t ∧ embed z = embed P.firstAnchor - t • embed v}) ∨
  (d = w ∧ E = {z | ∃ t : ℝ, 0 ≤ t ∧ embed z = embed P.secondAnchor + t • embed w}) ∨
  ∃ i : Fin P.boundedCount, d = P.boundedDirection i ∧
    E = {z | embed z ∈ segment ℝ (embed (P.vertex i.castSucc)) (embed (P.vertex i.succ))}

/-- Weak enveloping compares finite polygon edges to the actual region edges.
Extended cardinality treats semi-infinite edges as infinite, as the source does. -/
def WeaklyEnveloped (S : Finset Lattice) {v w : Lattice} (P : Region v w) : Prop :=
  ∀ d E, P.BoundaryEdge d E → d ∈ edgeDirections S ∧
    ((supportRow S d).card : ℕ∞) ≤ E.encard

/-- Genuine case distinction in §4.2: an actual translate agrees on a half-strip. -/
def HalfStripMatch (ξ xper : Configuration ℤ) (S : Finset Lattice) (v : Lattice) : Prop :=
  ∃ B : Finset Lattice, EnvelopedWindow S B ∧ ∃ u : Lattice,
    AgreesOn (translate u ξ) xper (halfStrip B v)

/-- Actual all-window mismatch premise of Lemma 3.5, retaining enlargement. -/
def UnboundedHalfStripMismatch (ξ xper : Configuration ℤ)
    (S : Finset Lattice) (v : Lattice) : Prop :=
  ∀ B₀ : Finset Lattice, EnvelopedWindow S B₀ →
    (∀ z ∈ supportRow B₀ v, det v z = -1) →
    ∃ B : Finset Lattice, B₀ ⊆ B ∧ EnvelopedWindow S B ∧
      (∀ z ∈ supportRow B v, det v z = -1) ∧ ∃ u : Lattice,
      AgreesOn (translate u ξ) xper (B : Set Lattice) ∧
        ¬ AgreesOn (translate u ξ) xper (halfStrip B v)

/-- §3.1 Case 2 keeps the support row for v and fails on the opposite
half-strip. Reflection reverses the polygon boundary orientation. -/
def UnboundedOppositeHalfStripMismatch (ξ xper : Configuration ℤ)
    (S : Finset Lattice) (v : Lattice) : Prop :=
  ∀ B₀ : Finset Lattice, EnvelopedWindow S B₀ →
    (∀ z ∈ supportRow B₀ v, det v z = -1) →
    ∃ B : Finset Lattice, B₀ ⊆ B ∧ EnvelopedWindow S B ∧
      (∀ z ∈ supportRow B v, det v z = -1) ∧ ∃ u : Lattice,
      AgreesOn (translate u ξ) xper (B : Set Lattice) ∧
        ¬ AgreesOn (translate u ξ) xper (halfStrip B (-v))

/-- Equal order is the actual published hypothesis on nonperiodic orbit members. -/
def SameOrbitOrder (ξ : Configuration ℤ) (m : ℕ) : Prop :=
  MinimalPeriodicOrder ℤ ξ m ∧ ∀ x ∈ OrbitClosure ξ,
    ¬ Periodic x → MinimalPeriodicOrder ℤ x m

/-- Kari–Moutot primary source §2 uses the open half-plane u·z<0. -/
def StrictDeterministic (ξ : Configuration ℤ) (u : Lattice) : Prop :=
  ∀ x ∈ OrbitClosure ξ, ∀ y ∈ OrbitClosure ξ,
    AgreesOn x y {z | realDot (embed z) (embed u) < 0} → x = y

/-- Kari–Moutot's definition of uniform recurrence via equality of orbit closures. -/
def UniformlyRecurrent (ξ : Configuration ℤ) : Prop :=
  ∀ x ∈ OrbitClosure ξ, OrbitClosure x = OrbitClosure ξ

/-- Published action (1), with the source's minus sign on exponents. -/
def laurentAction (φ : IntegerLaurent) (ξ : Configuration ℤ) (z : Lattice) : ℤ :=
  φ.sum (fun u c => c * ξ (z - u))

def Annihilates (φ : IntegerLaurent) (ξ : Configuration ℤ) : Prop :=
  ∀ z, laurentAction φ ξ z = 0

def reflectedSupport (φ : IntegerLaurent) : Finset Lattice := φ.support.image Neg.neg

/-- Integer lattice convex closure, a finite-set construction with a separately
recorded geometric finiteness obligation. -/
theorem lattice_windowHull_finite (S : Finset Lattice) :
    (embed ⁻¹' windowHull S).Finite := by
  classical
  let M : ℕ := S.sup (fun z => max z.1.natAbs z.2.natAbs)
  have hbounds : ∀ z ∈ S, -(M : ℤ) ≤ z.1 ∧ z.1 ≤ M ∧
      -(M : ℤ) ≤ z.2 ∧ z.2 ≤ M := by
    intro z hz
    have hm : max z.1.natAbs z.2.natAbs ≤ M := Finset.le_sup (f := fun z : Lattice => max z.1.natAbs z.2.natAbs) hz
    have h1 : z.1.natAbs ≤ M := (le_max_left _ _).trans hm
    have h2 : z.2.natAbs ≤ M := (le_max_right _ _).trans hm
    have ha : |z.1| ≤ (M : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h1
    have hb : |z.2| ≤ (M : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h2
    exact ⟨(abs_le.mp ha).1, (abs_le.mp ha).2,
      (abs_le.mp hb).1, (abs_le.mp hb).2⟩
  have hHull : windowHull S ⊆ Set.Icc ((-(M : ℝ), -(M : ℝ)) : RealPlane)
      ((M : ℝ), (M : ℝ)) := by
    apply convexHull_min
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨h1, h2, h3, h4⟩ := hbounds z hz
      change (-(M : ℝ) ≤ (z.1 : ℝ) ∧ -(M : ℝ) ≤ (z.2 : ℝ)) ∧
        ((z.1 : ℝ) ≤ M ∧ (z.2 : ℝ) ≤ M)
      exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h3⟩,
        ⟨by exact_mod_cast h2, by exact_mod_cast h4⟩⟩
    · exact convex_Icc _ _
  apply (Set.finite_Icc ((-(M : ℤ), -(M : ℤ)) : Lattice)
    ((M : ℤ), (M : ℤ))).subset
  intro z hz
  obtain ⟨⟨h1,h2⟩,h3,h4⟩ := hHull hz
  dsimp [embed] at h1 h2 h3 h4
  change (-(M : ℤ) ≤ z.1 ∧ -(M : ℤ) ≤ z.2) ∧ (z.1 ≤ M ∧ z.2 ≤ M)
  exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
    ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩⟩

def convexLatticeWindow (S : Finset Lattice) : Finset Lattice :=
  (lattice_windowHull_finite S).toFinset

def supportWindow (φ : IntegerLaurent) : Finset Lattice :=
  convexLatticeWindow (reflectedSupport φ)

/-- The actual product polynomial from source Lemma 2.8; all support
cancellations remain represented by the ring multiplication. -/
def differenceFactors (m : ℕ) (h : Fin m → Lattice) : IntegerLaurent :=
  (∏ i : Fin m, (AddMonoidAlgebra.single (h i) (1 : ℤ) -
    AddMonoidAlgebra.single (0 : Lattice) (1 : ℤ))).coeff

/-- The source's actual family Γ of off-face patterns along a positive tail. -/
def tailPatterns (x : Configuration ℤ) (S : Finset Lattice) (v : Lattice)
    (τ : ℤ) : Set (Pattern ℤ (offFace S (normal v))) :=
  {γ | ∃ t : ℤ, τ ≤ t ∧ γ = pattern x (offFace S (normal v)) (t • v)}

/-- Initial/final endpoints of the actual consecutive support-row run. -/
def BoundaryRun (S : Finset Lattice) (v g₀ g₁ : Lattice) : Prop :=
  (∀ z, z ∈ supportRow S v ↔ ∃ t : ℕ, t < (supportRow S v).card ∧
    z = g₀ + (t : ℤ) • v) ∧
  g₁ = g₀ + (((supportRow S v).card - 1 : ℕ) : ℤ) • v

/-- Actual four-vertex Q from the proof of Lemma 4.2, in its shorter-first-edge case. -/
def witnessParallelogram (S : Finset Lattice) (v g₀ g₁ : Lattice) : Finset Lattice :=
  convexLatticeWindow {g₀, g₀ - (((supportRow S v).card - 1 : ℕ) : ℤ) • v,
    g₁, g₁ - (((supportRow S v).card - 1 : ℕ) : ℤ) • v}

def shiftedWitnessOffFace (S : Finset Lattice) (v w g₀ g₁ : Lattice)
    (τ : ℤ) : Finset Lattice :=
  (offFace (witnessParallelogram S v g₀ g₁) (normal w)).image
    (fun z => z + (τ + (((supportRow S w).card - 1 : ℕ) : ℤ)) • w)

def shiftedWitness (S : Finset Lattice) (v w g₀ g₁ : Lattice)
    (τ : ℤ) : Finset Lattice :=
  (witnessParallelogram S v g₀ g₁).image
    (fun z => z + (τ + (((supportRow S w).card - 1 : ℕ) : ℤ)) • w)

/-- Actual saturation chain R_ι, R_{ι−1}, ... in Lemma 4.6 Case 1. -/
def saturationChain {S : Finset Lattice} {m : ℕ} (C : AntipodalEdgeCycle S m)
    (i : ℤ) (B : Finset Lattice) : ℕ → Set Lattice
  | 0 => halfStrip B (C.direction i)
  | k + 1 => saturateRay (saturationChain C i B k) (C.direction (i - (k + 1 : ℕ)))

def windowTranslate (S : Finset Lattice) (u : Lattice) : Finset Lattice :=
  S.image (fun z => z + u)

/-- Source Claim 4.7's actual factor deletion and difference configuration. -/
def differenceWithout (m : ℕ) (h : Fin m → Lattice) (k : Fin m) : IntegerLaurent :=
  (∏ j ∈ (Finset.univ.erase k),
    (AddMonoidAlgebra.single (h j) (1 : ℤ) -
      AddMonoidAlgebra.single (0 : Lattice) (1 : ℤ))).coeff

def periodDifference (ξ : Configuration ℤ) (h : Lattice) : Configuration ℤ :=
  fun z => ξ (z - h) - ξ z

/-- The strict inward-ray condition is stated against every actual supporting
edge. It does not presuppose a periodic accumulation point. -/
def Region.PointsInward {v w : Lattice} (P : Region v w) (d : Lattice) : Prop :=
  0 < det v d ∧ 0 < det w d ∧
    ∀ i : Fin P.boundedCount, 0 < det (P.boundedDirection i) d

end
end ConvexNivat.Colle
