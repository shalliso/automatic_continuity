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

lemma star_iInter {ι : Type*} (hι : Countable ι) (s : ι → Set X) : (⋂ i, s i)^{*U} = ⋂ i, (s i)^{*U} := by
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
    dsimp at hx
    have : ∀ᵇ (g : G), ∀ (i : ι), g ∈ U → g • x ∈ s i := by
      exact eventually_countable_forall.mpr hx
    filter_upwards [this]
    intro a hUs haU
    have : ∀ (i : ι), a • x ∈ s i := by
      exact fun i ↦ hUs i haU
    exact mem_iInter.mpr this

lemma star_compl : (Aᶜ)^{*U} = (A^{ΔU})ᶜ := by
  ext x
  simp

lemma star_compl2 : A^{*U} = ((Aᶜ)^{ΔU})ᶜ := by
  rw [←star_compl]
  simp

@[simp]
lemma star_empty [BaireSpace G] [Nonempty G] (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) : (∅ : Set X)^{*U} = ∅ := by
  ext x
  simp only [mem_setOf_eq, mem_empty_iff_false, imp_false, iff_false, not_eventually, not_not]
  exact residual_frequently_nonempty_open U hU_open hU_nonempty

@[simp]
lemma star_univ : (univ : Set X)^{*U} = univ := by
  ext x
  simp

lemma delta_compl : A^{ΔU} = ((Aᶜ)^{*U})ᶜ := by
  ext x
  constructor
  · intro h
    simp at h ⊢
    assumption
  · intro h
    simp at h ⊢
    assumption

lemma delta_monotonic (h : A ⊆ B) : A^{ΔU} ⊆ B^{ΔU} := by
  intro x hx
  have : ∀ g : G, (g ∈ U ∧ g • x ∈ A) → (g ∈ U ∧ g • x ∈ B) := by
    exact fun g ⟨hg, hg2⟩ ↦ ⟨hg, h hg2⟩
  exact Frequently.mono hx this

lemma delta_monotonic2 (h : U ⊆ V) : A^{ΔU} ⊆ A^{ΔV} := by
  intro x hx
  have : ∀ g : G, (g ∈ U ∧ g • x ∈ A) → (g ∈ V ∧ g • x ∈ A) := by
    exact fun g ⟨hg, hg2⟩ ↦ ⟨h hg, hg2⟩
  exact Frequently.mono hx this

lemma delta_iff_star [BaireSpace G] [Nonempty G] (hA : MeasurableSet A) (hUopen : IsOpen U) (hUne : U.Nonempty)
  (x : X)
  : x ∈ A^{ΔU} ↔ ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ x ∈ A^{*V} := by
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
    have h5 : ∃ᵇ (g : G), g ∈ V := by
      exact residual_frequently_nonempty_open V hVopen hVne
    have h6 : ∃ᵇ (g : G), g ∈ V ∧ (g ∈ V → g • x ∈ A) := by
      exact Frequently.and_eventually h5 hxAV
    have h7 : ∀ (g : G), (g ∈ V ∧ (g ∈ V → g • x ∈ A)) → (g ∈ V ∧ g • x ∈ A) := by
      intro g hg
      exact ⟨hg.1, hg.2 hg.1⟩
    have : ∃ᵇ (g : G), g ∈ V ∧ g • x ∈ A := by
      exact Frequently.mono h6 h7
    have h4 : x ∈ A^{Δ V} := by exact this
    have : A^{Δ V} ⊆ A^{Δ U} := by exact delta_monotonic2 hV
    exact this h4

lemma delta_compl2 : (Aᶜ)^{ΔU} = (A^{*U})ᶜ := by
  ext x
  simp

lemma star_subset_delta [BaireSpace G] (hUopen : IsOpen U) (hUne : U.Nonempty) : A^{*U} ⊆ A^{ΔU} := by
  intro x h
  dsimp at h ⊢
  have h1 : ∃ᵇ (g : G), g ∈ U := by
    exact residual_frequently_nonempty_open U hUopen hUne
  have h2 : ∃ᵇ (g : G), g ∈ U ∧ (g ∈ U → g • x ∈ A) := by
    exact Frequently.and_eventually h1 h
  have h3 : ∀ (g : G), (g ∈ U ∧ (g ∈ U → g • x ∈ A)) → (g ∈ U ∧ g • x ∈ A) := by
    intro g hg
    simp at hg ⊢
    exact ⟨hg.1, hg.2 hg.1⟩
  exact Frequently.mono h2 h3

lemma delta_union : (A ∪ B)^{ΔU} = A^{ΔU} ∪ B^{ΔU} := by
  ext x
  constructor
  · intro hx
    simp at hx ⊢
    have : ∀ (g : G), (g ∈ U ∧ (g • x ∈ A ∨ g • x ∈ B))
      → ((g ∈ U ∧ g • x ∈ A) ∨ (g ∈ U ∧ g • x ∈ B)) := by
      intro g hg
      exact and_or_left.mp hg
    have : ∃ᵇ (g : G), (g ∈ U ∧ g • x ∈ A) ∨ (g ∈ U ∧ g • x ∈ B) := by
      exact Frequently.mono hx this
    exact frequently_or_distrib.mp this
  · have hA2 : A ⊆ A ∪ B := by exact subset_union_left
    have hB2 : B ⊆ A ∪ B := by exact subset_union_right
    have hA : A^{ΔU} ⊆ (A ∪ B)^{ΔU} := by
      exact delta_monotonic hA2
    have hB : B^{ΔU} ⊆ (A ∪ B)^{ΔU} := by
      exact delta_monotonic hB2
    have : A^{ΔU} ∪ B^{ΔU} ⊆ (A ∪ B)^{ΔU} := by exact union_subset hA hB
    exact fun a ↦ this a

lemma delta_iUnion {ι : Type*} (s : ι → Set X) : (⋃ i, s i)^{ΔU} = ⋃ i, (s i)^{ΔU} := by
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
