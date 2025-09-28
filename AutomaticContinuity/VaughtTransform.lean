import Mathlib
import AutomaticContinuity.Baire
import AutomaticContinuity.Homeomorph

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped Pointwise

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]
variable {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G] [IsTopologicalGroup G]
variable [MulAction G X] [ContinuousSMul G X]

instance : HSMul (Set G) G (Set G) where
  hSMul U g := {u • g | u ∈ U}

instance : HSMul (Set G) X (Set X) where
  hSMul U x := {u • x | u ∈ U}

instance : HSMul (Set G) (Set X) (Set X) where
  hSMul U A := image2 (· • ·) U A

abbrev VaughtTransformStar (A : Set X) (U : Set G) : Set X :=
  {x : X | ∀ᵇ (g : G), g ∈ U → g • x ∈ A}

abbrev VaughtTransformDelta (A : Set X) (U : Set G) : Set X :=
  {x : X | ∃ᵇ (g : G), g ∈ U ∧ g • x ∈ A}

-- Did I choose right values here?
notation:75 A "^{*" U "}" => VaughtTransformStar A U
notation:75 A "^{Δ" U "}" => VaughtTransformDelta A U

namespace VaughtTransform

variable {A B : Set X} {x : X}
variable {U V : Set G} {g : G}

lemma star_monotonic (h : A ⊆ B) : A^{*U} ⊆ B^{*U} := by
  intro x hx
  dsimp
  filter_upwards [hx] with g hgU_to_gxA hgU
  exact h (hgU_to_gxA hgU)

lemma star_monotonic2 (h : U ⊆ V) : A^{*V} ⊆ A^{*U} := by
  intro x hx
  dsimp
  filter_upwards [hx] with g hgV_to_gxA hgU
  exact hgV_to_gxA (h hgU)

lemma star_inter : (A ∩ B)^{*U} = A^{*U} ∩ B^{*U} := by
  ext x
  constructor
  · intro hx
    constructor
    · have : A ∩ B ⊆ A := by exact inter_subset_left
      have : (A ∩ B)^{*U} ⊆ A^{*U} := by exact star_monotonic this
      exact this hx
    · have : A ∩ B ⊆ B := by exact inter_subset_right
      have : (A ∩ B)^{*U} ⊆ B^{*U} := by exact star_monotonic this
      exact this hx
  · intro ⟨hxA, hxB⟩
    dsimp
    filter_upwards [hxA, hxB] with g gUA gUB
    exact fun a ↦ mem_inter (gUA a) (gUB a)

-- needs to be a countable intersection
lemma star_iInter {ι : Type*} (s : ι → Set X) : (⋂ i, s i)^{*U} = ⋂ i, (s i)^{*U} := by
  ext x
  constructor
  · intro hx
    refine mem_iInter.mpr ?_
    intro i
    have : ⋂ i, s i ⊆ s i := by exact iInter_subset_of_subset i fun ⦃a⦄ a ↦ a
    have : (⋂ i, s i)^{*U} ⊆ (s i)^{*U} := by exact star_monotonic this
    exact this hx
  · intro hx
    dsimp
    apply mem_iInter.mp at hx
    sorry

lemma star_union : A^{* U ∪ V} = A^{*U} ∩ A^{*V} := by
  sorry

lemma star_compl : (Aᶜ)^{*U} = (A^{ΔU})ᶜ := by
  ext x
  simp

@[simp]
lemma star_empty (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) : (∅ : Set X)^{*U} = ∅ := by
  ext x
  simp
  sorry

lemma star_univ (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) : (univ : Set X)^{*U} = univ := by
  sorry

lemma delta_compl : A^{ΔU} = ((Aᶜ)^{*U})ᶜ := by sorry

lemma delta_monotonic (h : A ⊆ B) : A^{ΔU} ⊆ B^{ΔU} := by
  rw [delta_compl, delta_compl]
  intro x hx
  by_contra hxB

  simp at hx ⊢

  sorry

lemma delta_monotonic2 (h : U ⊆ V) : A^{ΔV} ⊆ A^{ΔU} := by
  sorry

lemma delta_union : (A ∪ B)^{ΔU} = A^{ΔU} ∪ B^{ΔU} :=
  by sorry

lemma delta_iUnion {ι : Type*} (s : ι → Set X) : (⋃ i, s i)^{ΔU} = ⋃ i, (s i)^{ΔU} := by
  sorry

lemma delta_sUnion {s : Set (Set X)} : (⋃₀ s)^{*U} = ⋃₀ {A^{ΔU} | A ∈ s} := by
  sorry

lemma delta_compl2 : (Aᶜ)^{ΔU} = (A^{*U})ᶜ := by
  ext x
  simp

lemma star_subset_delta [BaireSpace G] : A^{*U} ⊆ A^{ΔU} := by
  sorry

lemma star_smul_iff : g • x ∈ A^{*U} ↔ x ∈ A^{*U • g} := by
  constructor
  · intro hgxA
    dsimp
    dsimp at hgxA
    dsimp [Filter.Eventually] at hgxA ⊢
    have : {a | a ∈ U → a • g • x ∈ A} • g = {a | a ∈ U • g → a • x ∈ A}:= by
      ext a
      constructor
      · simp [HSMul.hSMul, SMul.smul]
        rw [SMul.smul_eq_hSMul]
        intro b h1 h2 c hc hd
        have hb1 : b = a * g⁻¹ := by exact eq_mul_inv_of_mul_eq h2
        have hc1 : c = a * g⁻¹ := by exact eq_mul_inv_of_mul_eq hd
        rw [←hc1] at hb1
        rw [←hb1] at hc
        apply h1 at hc
        rw [←hb1] at hc1
        rw [hc1] at hc
        have : (a * g⁻¹) • (g • x) = ((a * g⁻¹) * g) • x := by
          rw [smul_smul]
        rw [this] at hc
        simp at hc
        assumption
      · simp [HSMul.hSMul, SMul.smul]
        rw [SMul.smul_eq_hSMul]
        intro h
        use a * g⁻¹
        simp
        intro h2
        specialize h (a * g⁻¹)
        simp at h
        apply h at h2
        have : (a * g⁻¹) • (g • x) = ((a * g⁻¹) * g) • x := by
          rw [smul_smul]
        rw [this]
        simp
        exact h2
    rw [←this]
    sorry
    --rw [←this] at hgxA
    --exact hgxA
  · sorry

lemma delta_smul_iff : g • x ∈ A^{ΔU} ↔ x ∈ A^{ΔU • g} := by
  sorry

lemma delta_lem1 (hVU : V ⊆ U) (hVxA : V • x ⊆ A) : x ∈ A^{*V} := by
  dsimp
  filter_upwards
  intro a ha
  have : a • x ∈ V • x := by
    use a
  exact hVxA this

lemma delta_lem2 (hU2 : IsOpen U) : x ∈ A^{ΔU} → ∃ u ∈ U, u • x ∈ A := by
  intro hx
  dsimp at hx
  exact Frequently.exists hx

lemma delta_open_open (hA : IsOpen A) (hU : IsOpen U) : IsOpen (A^{Δ U}) := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro x hx
  have ⟨u, huU, huxA⟩ : ∃ u ∈ U, u • x ∈ A := by exact delta_lem2 hU hx
  let f : G × X → X := fun (⟨g, x⟩ : G × X) ↦ (g • x : X)
  have : Continuous f := by
    exact continuous_smul
  let Z := f ⁻¹' A
  have h4: IsOpen Z := by
    exact this.isOpen_preimage A hA

  have h5: ⟨u, x⟩ ∈ Z := by sorry

  have ⟨V, B, hV, hB, huV, hxB, VBZ⟩
    : ∃ (V : Set G) (B : Set X), IsOpen V ∧ IsOpen B ∧ u ∈ V ∧ x ∈ B ∧ V ×ˢ B ⊆ Z := by
    exact isOpen_prod_iff.mp h4 u x h5

  refine ⟨B, ?_, hB, hxB⟩

  intro y hy
  sorry



end VaughtTransform
