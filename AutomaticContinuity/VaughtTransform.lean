import Mathlib
import AutomaticContinuity.Baire
import AutomaticContinuity.Homeomorph

open Set Filter Topology TopologicalSpace
open scoped Pointwise

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
variable {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
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

lemma star_compl2 : A^{*U} = ((Aᶜ)^{ΔU})ᶜ := by
  rw [←star_compl]
  simp

@[simp]
lemma star_empty (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) : (∅ : Set X)^{*U} = ∅ := by
  ext x
  simp
  sorry

lemma star_univ (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) : (univ : Set X)^{*U} = univ := by
  sorry

lemma delta_compl : A^{ΔU} = ((Aᶜ)^{*U})ᶜ := by sorry

lemma delta_iff_star (hA : MeasurableSet A) (hUopen : IsOpen U) (hUne : U.Nonempty)
  (x : X)
  : x ∈ A^{Δ U} ↔ ∃ V ⊆ U, (IsOpen V) ∧ (V.Nonempty) ∧ x ∈ A^{*V} := by
  constructor
  · intro hx
    dsimp at hx
    let f : G → X := (· • x)
    have hf : Measurable f := by
      exact MeasurableSMul.measurable_smul_const x
    have h5 : MeasurableSet ((f⁻¹' A) : Set G) := by
      exact MeasurableSet.preimage hA hf
    let S := {g : G | g ∈ U ∧ g • x ∈ A}
    have h6 : MeasurableSet U := by
      exact IsOpen.measurableSet hUopen
    have : MeasurableSet S := by
      exact MeasurableSet.inter h6 h5
    have : BaireMeasurableSet S := by exact MeasurableSet.baireMeasurableSet this
    have h2 : ¬ IsMeagre S := by
      exact hx
    have h3 := BaireMeasurableSet.nonMeagre_residualEq_isOpen_Nonempty this h2
    obtain ⟨V, hVopen, hVne, hVS⟩ := h3
    have hSVne : (S ∩ V).Nonempty := by
      have : ∀ᵇ (g : G), g ∈ S ↔ g ∈ V := by
        exact EventuallyEq.mem_iff hVS
      have : ∃ᵇ (g : G), (g ∈ U ∧ g • x ∈ A) ∧ (g ∈ S ↔ g ∈ V) := by
        exact Frequently.and_eventually hx this
      simp at this
      have : ∃ g : G, ((g ∈ U ∧ g • x ∈ A) ∧ (g ∈ S ↔ g ∈ V)) := by
        exact Frequently.exists this
      obtain ⟨g, ⟨hgU, hgxA⟩, hgSV⟩ := this
      have h8 : g ∈ S := by exact mem_sep hgU hgxA
      have h9 : g ∈ V := by exact hgSV.mp h8
      exact ⟨g, h8, h9⟩

    let W := U ∩ V
    refine ⟨W, ?_, ?_, ?_, ?_⟩
    · exact inter_subset_left
    · exact IsOpen.inter hUopen hVopen
    · obtain ⟨g1, ⟨hg1, hg11⟩, hg2⟩ := hSVne
      use g1
      exact mem_inter hg1 hg2
    · dsimp
      dsimp [EventuallyEq] at hVS
      filter_upwards [hVS]
      intro a hSaVa haW
      have : a ∈ V := by exact mem_of_mem_inter_right haW
      have : a ∈ S := by
        have : V a := by exact this
        have : S a := by
          rwa [←hSaVa] at this
        exact this
      exact this.2
  · intro ⟨V, hV, hVopen, hVne, hxAV⟩
    dsimp at hxAV
    --have : ∃ᵇ (g : G), g ∈ V := by
    --  exact residual_frequently_nonempty_open V hVopen hVne
    --have : ∃ᵇ (g : G), g ∈ V ∧ (g ∈ V → g • x ∈ A) := by
    --  exact Frequently.and_eventually this hxAV



    sorry

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

lemma delta_lem12 (hV : V.Nonempty) :  A^{*V} ⊆ A^{ΔV} := by
  intro x hx
  dsimp at hx ⊢
  have : ∃ᵇ (g : G), g ∈ V := by sorry
  have : ∃ᵇ (g : G), (g ∈ V) ∧ (g ∈ V → g • x ∈ A) := by
    exact Frequently.and_eventually this hx
  simp at this

  sorry

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
  let V2 := U ∩ V
  have hV2 : V2 ⊆ U := by exact inter_subset_left
  have hVyA : V2 • y ⊆ A := by sorry
  exact delta_lem1

  sorry

lemma star_closed_closed (hA : IsClosed A) (hU : IsOpen U) : IsClosed (A^{* U}) := by
  rw [star_compl2]
  refine isClosed_compl_iff.mpr ?_
  have : IsOpen Aᶜ := by exact IsClosed.isOpen_compl
  exact delta_open_open this hU

end VaughtTransform
