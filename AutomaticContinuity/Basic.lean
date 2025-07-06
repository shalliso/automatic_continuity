import Mathlib

open Filter Set Topology
variable {X : Type*} [TopologicalSpace X]

/-- A set is residual iff it includes an intersection over Nat of dense open sets. -/
theorem mem_residual_iff_iInter_nat {s : Set X} :
    s ∈ residual X ↔
      ∃ (f : ℕ → Set X), (∀ n, IsOpen (f n)) ∧ (∀ n, Dense (f n)) ∧ ⋂ n, f n ⊆ s := by
  rw [mem_residual_iff]
  constructor
  intro ⟨S, h_open, h_dense, h_ctbl, h_s⟩
  by_cases h_S : S.Nonempty
  . obtain ⟨f, h_f⟩ := Countable.exists_surjective h_S h_ctbl
    let f' : ℕ → Set X := fun n ↦ (f n : Set X)
    have f_surj : range f' = S := by
      ext x
      constructor
      intro h
      obtain ⟨n, hn⟩ := h
      rw [← hn]
      exact Subtype.coe_prop (f n)

      intro h
      simp [f']
      have hxS : x ∈ S := h
      obtain ⟨n, hn⟩ := h_f ⟨x, hxS⟩
      use n
      rw [hn]
    use f'
    constructor
    intro n
    have : f' n ∈ S := by exact Subtype.coe_prop (f n)
    exact h_open (f' n) this

    constructor
    intro n
    have : f' n ∈ S := by exact Subtype.coe_prop (f n)
    exact h_dense (f' n) this

    have asdf : ⋂ n, f' n = ⋂₀ S := by
      simp [f']
      ext x
      exact
        Iff.symm
          (Eq.to_iff (congrFun (congrArg Membership.mem (congrArg sInter (id (Eq.symm f_surj)))) x))
    rw [asdf]
    assumption

  rw [not_nonempty_iff_eq_empty] at h_S
  rw [h_S] at h_s
  simp at h_s
  set g := Function.const ℕ s
  use g
  simp [g, h_s]
  . intro ⟨f, h_open, h_dense, h_inter⟩
    use range f
    refine ⟨by simpa, by simpa, countable_range f, by simpa⟩

/-- A countable union of meagre sets is meagre. -/
lemma isMeagre_iUnion' {ι : Type*} [Countable ι] {f : ι → Set X} (hs : ∀ i, IsMeagre (f i))
    : IsMeagre (⋃ i, f i) := by
  rw [IsMeagre, compl_iUnion]
  exact countable_iInter_mem.mpr hs

/-
lemma isMeagre_bUnion {ι : Type*} {S : Set ι} (hS: S.Countable) {f : ∀ i ∈ S, Set X}
  (hs : ∀ i ∈ S, IsMeagre (f i ‹_›)) : IsMeagre (⋂ i, ⋂ hi : i ∈ S, f i ‹_›) := by

  sorry
-/

variable {G : Type*} [Group G] [MulAction G X] [ContinuousConstSMul G X]

open Pointwise

theorem residual_smul' {A : Set X} {g : G} : A ∈ residual X → g • A ∈ residual X := by
  intro h
  obtain ⟨S, h_open, h_dense, h_ctbl, h_inter⟩ := mem_residual_iff.mp h
  set S' := g • S
  refine mem_residual_iff.mpr ⟨S', ?_, ?_, ?_, ?_⟩

  simp [S']
  intro U hU
  have h1 : g⁻¹ • U ∈ S := by exact mem_smul_set_iff_inv_smul_mem.mp hU
  have h2 : U = g • (g⁻¹ • U) := by exact Eq.symm (smul_inv_smul g U)
  have h3 := h_open (g⁻¹ • U) h1
  have h4 : IsOpen (g • (g⁻¹ • U)) := by exact IsOpen.smul (h_open (g⁻¹ • U) h1) g
  rw [←h2] at h4
  assumption

  simp [S']
  intro U hU
  have h1 : g⁻¹ • U ∈ S := by exact mem_smul_set_iff_inv_smul_mem.mp hU
  have h2 : U = g • (g⁻¹ • U) := by exact Eq.symm (smul_inv_smul g U)
  have h3 := h_dense (g⁻¹ • U) h1
  have h4 : Dense (g • (g⁻¹ • U)) := by exact Dense.smul g (h_dense (g⁻¹ • U) h1)
  rw [←h2] at h4
  assumption

  rcases Set.eq_empty_or_nonempty S with rfl|hS
  . have : S' = ∅ := by
      exact smul_set_empty
    rwa [this]

  obtain ⟨f, hf⟩ : ∃ (f : ℕ → Set X), S = range f := Countable.exists_eq_range h_ctbl hS
  set h := fun (n : ℕ) ↦ (g • f n)
  rw [countable_iff_exists_subset_range]
  use h
  intro s hs
  obtain ⟨s', hs1, hs2⟩ := hs
  simp at hs2
  rw [hf] at hs1
  obtain ⟨n, hfn⟩ := hs1
  use n
  simp [h, hfn, hs2]


  have : ⋂₀ S' = g • (⋂₀ S) := by
    simp [S']
    ext x
    constructor

    intro h
    simp [HSMul.hSMul, SMul.smul]
    use g⁻¹ • x
    constructor
    intro t ht
    have : g • t ∈ g • S := by exact smul_mem_smul_set ht
    have : x ∈ g • t := by exact h (g • t) this
    (expose_names; exact mem_smul_set_iff_inv_smul_mem.mp (h (g • t) this_1))

    exact smul_inv_smul g x

    intro h
    intro t ht
    have h453 : g⁻¹ • t ∈ S := by exact mem_smul_set_iff_inv_smul_mem.mp ht
    simp [HSMul.hSMul, SMul.smul] at h
    obtain ⟨x_1, hx_1t, hx2⟩ := h
    rw [←hx2]
    have h12 : x_1 ∈ g⁻¹ • t := by exact hx_1t (g⁻¹ • t) h453
    have : g • x_1 ∈ t := by exact mem_inv_smul_set_iff.mp (hx_1t (g⁻¹ • t) h453)
    exact this

  intro x hx
  rw [this] at hx
  have : g • ⋂₀ S ⊆ g • A := by exact smul_set_mono h_inter
  exact this hx



theorem residual_smul {A : Set X} {g : G} : A ∈ residual X → g • A ∈ residual X := by
  intro h
  obtain ⟨f, h_open, h_dense, h_inter⟩ := mem_residual_iff_iInter_nat.mp h
  set f' := g • f
  refine mem_residual_iff_iInter_nat.mpr ⟨
    f',
    fun n ↦ IsOpen.smul (h_open n) g,
    fun n ↦ Dense.smul g (h_dense n),
    ?_⟩
  dsimp [f']
  rw [←smul_set_iInter]
  exact smul_set_mono h_inter

theorem isMeagre_smul {A : Set X} {g : G} : IsMeagre A → IsMeagre (g • A) := by
  dsimp [IsMeagre]
  rw [←smul_set_compl]
  exact residual_smul

/-- A union of two meagre sets is meagre. -/
lemma isMeagre_union {s t : Set X} (hs : IsMeagre s) (ht : IsMeagre t)
    : IsMeagre (s ∪ t) := by
  rw [IsMeagre, compl_union]
  exact inter_mem hs ht



theorem isGδ_smul (v : G) (A : Set X) (hA : IsGδ A) : IsGδ (v • A) := by
  rw [isGδ_iff_eq_iInter_nat] at hA ⊢
  obtain ⟨f, hctbl, hunionA⟩ := hA

  set g := v • f
  refine ⟨g, ?_, ?_⟩
  . intro n
    simp [g]
    exact IsOpen.smul (hctbl n) v
  rw [hunionA]
  rw [Set.smul_set_iInter]
  simp [g]

open symmDiff

/-- A set is Baire measurable if and only if it differs from some open set by a meager set. -/
theorem BaireMeasurableSet.iff_meagre_symmDiff_isOpen {s : Set X} :
    BaireMeasurableSet s ↔ ∃ u : Set X, (IsOpen u) ∧ (IsMeagre (symmDiff s u)) := by
  constructor
  intro h
  obtain ⟨u, hu, hus⟩ := BaireMeasurableSet.iff_residualEq_isOpen.mp h
  use u
  constructor
  use hu
  dsimp [IsMeagre]

  simp [EventuallyEq, Filter.Eventually] at hus
  have : {x | s x ↔ u x} = (s ∆ u)ᶜ := by
    ext x
    simp [bihimp]
    tauto
  rwa [←this]

  intro ⟨u, hopen, hmeagre⟩
  rw [BaireMeasurableSet.iff_residualEq_isOpen]
  refine ⟨u, hopen, ?_⟩
  simp [EventuallyEq, Filter.Eventually]
  simp only [IsMeagre] at hmeagre
  have : {x | s x ↔ u x} = (s ∆ u)ᶜ := by
    ext x
    simp [bihimp]
    tauto
  rwa [this]



/-- A residual set is nonempty.
    Put this in Topology/Baire/Lemmas.lean
-/
theorem nonempty_of_residual [Nonempty X] [BaireSpace X] {s : Set X} : s ∈ residual X → s.Nonempty := by
  exact (fun h ↦ (dense_of_mem_residual h).nonempty)

theorem empty_IsMeagre [BaireSpace X] : IsMeagre (∅ : Set X) := by
  by_contra h
  simp only [IsMeagre, compl_empty, univ_mem, not_true_eq_false] at h




variable [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G] [MeasurableSpace G] [BorelSpace G]


example {A : Set G} (hA : A ∈ residual G) : A * A⁻¹ = ⊤ := by
  ext g
  constructor
  . intro _
    trivial
  intro _
  have : g • A ∈ residual G := by exact residual_smul hA
  have : A ∩ (g • A) ∈ residual G := Filter.inter_mem hA this
  have hy : ∃ y, y ∈ A ∩ (g • A) := nonempty_of_residual this
  obtain ⟨y, hy1, hy2⟩ := hy
  have hy22 : g⁻¹ * y ∈ A := by
    simpa [HSMul.hSMul, SMul.smul] using hy2
  have hy222 : (g⁻¹ * y)⁻¹ ∈ A⁻¹ := by simpa using hy22
  have h1: y * (g⁻¹ * y)⁻¹ ∈ A * A⁻¹ := by exact Set.mul_mem_mul hy1 hy222
  simpa using h1

example {U : Set G} {g : G} (hgU : g ∈ U) (hU_open : IsOpen U)
    : ∃ V : Set G, (IsOpen V) ∧ (1 ∈ V) ∧ ({g} * (V * V⁻¹) ⊆ U) := by
  -- Since multiplication and inversion are continuous, and U is open and contains g,
    -- there exists an open neighborhood V of 1 such that g * (V * V⁻¹) ⊆ U.
  let m := fun (⟨x, y⟩ : G × G) ↦ g * x * y⁻¹
  have hm : Continuous m := by
    continuity
  have h1 : m ⟨1, 1⟩ ∈ U := by simpa [m]
  have h2 : IsOpen (m ⁻¹' U) := by exact hm.isOpen_preimage U hU_open
  rw [isOpen_prod_iff] at h2
  specialize h2 1 1 h1
  obtain ⟨V1, V2, hV1open, hV2open, h1V1, h1V2, hV1V2⟩ := h2
  let V := V1 ∩ V2
  have hV2invopen : IsOpen V2⁻¹ := by exact IsOpen.inv hV2open
  have hV2inv1 : 1 ∈ V2⁻¹ := by simpa
  use V
  refine ⟨IsOpen.inter hV1open hV2open, Set.mem_inter h1V1 h1V2, ?_⟩
  have h11 : V ⊆ V1 := by exact Set.inter_subset_left
  have h12 : V ⊆ V2 := by exact Set.inter_subset_right
  intro x hx
  obtain ⟨x1, hx1, hx2, hx3, hx4⟩ := hx
  simp at hx4
  simp at hx1
  rw [hx1] at hx4
  obtain ⟨v1, v2, v3, v4, v5⟩ := hx3
  simp at v5
  rw [←v5] at hx4
  rw [←hx4]
  have : ⟨v1, v3⁻¹⟩ ∈ V1 ×ˢ V2 := by exact Set.mk_mem_prod (h11 v2) (h12 v4)
  have : ⟨v1, v3⁻¹⟩ ∈ m ⁻¹' U := by exact hV1V2 this
  have : m ⟨v1, v3⁻¹⟩ ∈ U := by exact this
  simp [m] at this
  rw [←mul_assoc]
  exact this

lemma mImg {g : G} (V1 V2 : Set G) :
    let m := fun p : G × G ↦ g * (p.1 * p.2⁻¹)
    m '' V1 ×ˢ V2 = g • (V1 * V2⁻¹) := by
  ext x
  constructor

  intro h
  simp at h
  obtain ⟨a, b, ⟨ha, hb⟩, himg⟩ := h
  simp [HSMul.hSMul, SMul.smul, HMul.hMul, Mul.mul]
  rw [← himg]
  use a
  use ha
  use b⁻¹
  constructor
  simpa
  rfl

  intro h
  simp
  simp [HSMul.hSMul, SMul.smul, HMul.hMul, Mul.mul] at h
  obtain ⟨a, ha, b, hb, hab⟩ := h
  use a
  use b⁻¹
  use ⟨ha, hb⟩
  simpa


lemma small_nbhd {U : Set G} {g : G} (hgU : U ∈ 𝓝 g)
    : ∃ V ∈ 𝓝 1, g • (V * V⁻¹) ⊆ U := by
  set m := fun p : G × G => g * (p.1 * p.2⁻¹)
  have h_cont' : Continuous m := by continuity
  have h_cont : ContinuousAt m ⟨1, 1⟩ := by exact Continuous.continuousAt h_cont'
  have h_image : m ⟨1, 1⟩ = g := by simp [m]
  simp only [ContinuousAt, h_image] at h_cont

  have t := h_cont hgU
  simp at t
  obtain ⟨V1, hV1, V2, hV2, hV_sub⟩ :=  mem_nhds_prod_iff.mp t
  use V1 ∩ V2
  refine ⟨Filter.inter_mem hV1 hV2, ?_⟩
  have hmV_sub : m '' V1 ×ˢ V2 ⊆ U := by simpa
  have hmV_def: m '' V1 ×ˢ V2 = g • (V1 * V2⁻¹) := by exact mImg V1 V2
  have h100 : (V1 ∩ V2 * (V1 ∩ V2)⁻¹) ⊆ V1 * V2⁻¹ := by
    exact
      Set.mul_subset_mul Set.inter_subset_left
      (by simp only [Set.inter_inv, Set.inter_subset_right])
  have : g • (V1 ∩ V2 * (V1 ∩ V2)⁻¹) ⊆ g • (V1 * V2⁻¹) := by exact smul_set_mono h100
  rw [←hmV_def] at this
  exact fun ⦃a⦄ a_1 ↦ hmV_sub (this a_1)

lemma asdf234 {s1 s2 t1 t2 : Set G} : (s1 ∩ s2) ∆ (t1 ∩ t2) ⊆ (s1 ∆ t1) ∪ (s2 ∆ t2) := by
  simp [symmDiff] at *
  constructor
  intro x hx
  simp at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  by_cases h4: x ∈ t1
  right
  left
  exact mem_diff_of_mem h2 (h3 h4)
  left
  left
  exact mem_diff_of_mem h1 h4

  intro x hx
  simp at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  by_cases h4: x ∈ s1
  right
  right
  exact mem_diff_of_mem h2 (h3 h4)
  left
  right
  exact mem_diff_of_mem h1 h4


theorem pettis {A : Set G} (hBM : BaireMeasurableSet A) (hA : ¬ IsMeagre A)
    : A * A⁻¹ ∈ nhds 1 := by
  rw [BaireMeasurableSet.iff_meagre_symmDiff_isOpen] at hBM
  obtain ⟨U, h_open, h_meager_diff⟩ := hBM

  have hU_nonempty : U.Nonempty := by
    by_contra hUempty
    simp at hUempty
    have : U = ∅ := by exact Set.not_nonempty_iff_eq_empty.mp hUempty
    rw [this] at h_open
    simp [this, symmDiff] at h_meager_diff
    contradiction

  obtain ⟨g, hgU⟩ := hU_nonempty
  have h5 : U ∈ 𝓝 g := by exact IsOpen.mem_nhds h_open hgU
  have h57 : IsOpen U⁻¹ := by exact IsOpen.inv h_open
  have h435 : g⁻¹ ∈ U⁻¹ := by exact Set.inv_mem_inv.mpr hgU
  have h567 : U⁻¹ ∈ 𝓝 g⁻¹ := by
    exact IsOpen.mem_nhds h57 h435
  have ⟨V, hV1, hVU⟩ := small_nbhd h567
  refine Filter.mem_of_superset hV1 ?_
  intro v hvV
  have h54 : 1 ∈ V⁻¹ := by
    simp
    exact mem_of_mem_nhds hV1
  have h2345 : v ∈ V * V⁻¹ := by
    exact ⟨v, hvV, 1, h54, MulOneClass.mul_one v⟩
  have h234324 : g⁻¹ • v ∈ g⁻¹ • (V * V⁻¹) := by
    exact smul_mem_smul_set h2345
  have h23456 : g⁻¹ • v ∈ U⁻¹ := by
    exact hVU h234324
  have h234567 : v⁻¹ * g ∈ U := by
    simpa using h23456
  have h2345678 : g ∈ v • U := by
    exact mem_smul_set_iff_inv_smul_mem.mpr h234567
  have h99 : IsMeagre ((v • A) ∆ (v • U)) := by
    rw [←smul_set_symmDiff]
    exact isMeagre_smul h_meager_diff
  have h101 : IsMeagre ((A ∆ U) ∪ ((v • A) ∆ (v • U))) := by
    exact isMeagre_union h_meager_diff h99
  have h102 : ((A ∩ v • A) ∆ (U ∩ v • U)) ⊆ ((A ∆ U) ∪ ((v • A) ∆ (v • U))) := by
    exact asdf234
  have h100 : IsMeagre ((A ∩ v • A) ∆ (U ∩ v • U)) := by
    exact IsMeagre.mono h101 h102
  have h200 : (U ∩ v • U).Nonempty := by
    use g
    exact mem_inter hgU h2345678
  have h2034 : IsOpen (v • U) := by exact IsOpen.smul h_open v
  have h201 : IsOpen (U ∩ v • U) := by
    exact IsOpen.inter h_open h2034
  have h204 : IsClosed (U ∩ v • U)ᶜ := by
    exact isClosed_compl_iff.mpr h201
  have h205 : closure (U ∩ v • U)ᶜ = (U ∩ v • U)ᶜ := by
    exact closure_eq_iff_isClosed.mpr h204
  have h206 : closure (U ∩ v • U)ᶜ ≠ univ := by
    simp
    exact nonempty_iff_ne_empty.mp h200
  have h202 : ¬ Dense (U ∩ v • U)ᶜ := by
    by_contra h
    rw [dense_iff_closure_eq] at h
    contradiction
  have h101 : (A ∩ v • A).Nonempty := by
    by_contra h_empty
    have : (A ∩ v • A) = ∅ := by exact not_nonempty_iff_eq_empty.mp h_empty
    rw [this] at h100
    simp [symmDiff] at h100
    dsimp [IsMeagre] at h100
    apply dense_of_mem_residual at h100
    contradiction
  obtain ⟨g, hgA, hgAv⟩ := h101
  simp at hgAv
  have : g⁻¹ * v ∈ A⁻¹ := by
    obtain ⟨a, ha, ha2⟩ := hgAv
    simp at ha2
    rw [← ha2]
    simpa
  have : g * (g⁻¹ * v) ∈ A * A⁻¹ := by
    exact Set.mul_mem_mul hgA this
  simpa using this

theorem pettis' {A : Set G} (hBM : BaireMeasurableSet A) (hA : ¬ IsMeagre A)
    : A⁻¹ * A ∈ nhds 1 := by
  have h0 : BaireMeasurableSet A⁻¹ := by
    set m : G → G := fun g ↦ g⁻¹
    have h1 : Continuous m := by exact continuous_inv
    have h2 : IsOpenMap m := by exact isOpenMap_inv G
    have h3 : BaireMeasurableSet (m ⁻¹' A) := by exact BaireMeasurableSet.preimage h1 h2 hBM
    simp [m] at h3
    assumption
  have h1 : ¬ (IsMeagre A⁻¹) := by
    by_contra h
    set m : G → G := fun g ↦ g⁻¹
    have h1 : Continuous m := by exact continuous_inv
    have h2 : IsOpenMap m := by exact isOpenMap_inv G
    have h3 : IsMeagre (m ⁻¹' A⁻¹) := by exact IsMeagre.preimage_of_isOpenMap h1 h2 h
    simp [m] at h3
    contradiction
  have h2 : A⁻¹⁻¹ = A := by exact DivisionMonoid.inv_inv A
  nth_rw 2 [← h2]
  exact pettis h0 h1

variable {H: Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [BaireSpace H]
  [MeasurableSpace H] [BorelSpace H]


lemma lem3 {U : Set H} (hU : U ∈ 𝓝 1)
  : ∃ V ∈ 𝓝 1, V⁻¹ * V ⊆ U := by
    set m : H × H → H := fun p ↦ p.1⁻¹ * p.2
    have h_cont' : Continuous m := by continuity
    have h_cont : ContinuousAt m ⟨1, 1⟩ := by exact Continuous.continuousAt h_cont'
    have h_image : m ⟨1, 1⟩ = 1 := by simp [m]
    simp only [ContinuousAt, h_image] at h_cont

    have t := h_cont hU
    simp at t
    obtain ⟨V1, hV1, V2, hV2, hV_sub⟩ :=  mem_nhds_prod_iff.mp t
    use V1 ∩ V2
    refine ⟨Filter.inter_mem hV1 hV2, ?_⟩
    have hmV_sub : m '' V1 ×ˢ V2 ⊆ U := by simpa
    have hmV_def: m '' V1 ×ˢ V2 = V1⁻¹ * V2 := by
      simp [m]

      ext x
      constructor

      intro h
      simp at h
      obtain ⟨a, b, ⟨ha, hb⟩, himg⟩ := h
      simp [HSMul.hSMul, SMul.smul, HMul.hMul, Mul.mul]
      rw [← himg]
      use a⁻¹
      constructor
      simpa
      use b
      constructor
      assumption
      rfl

      intro h
      simp
      simp [HSMul.hSMul, SMul.smul, HMul.hMul, Mul.mul] at h
      obtain ⟨a, ha, b, hb, hab⟩ := h
      use a⁻¹
      use b
      use ⟨ha, hb⟩
      simpa
    have h100 : ((V1 ∩ V2)⁻¹ * (V1 ∩ V2)) ⊆ V1⁻¹ * V2 := by
      apply Set.mul_subset_mul
      simp
      simp
    rw [←hmV_def] at h100

    exact fun ⦃a⦄ a_1 ↦ hmV_sub (h100 a_1)

lemma lem3' {U : Set H} (hU : U ∈ 𝓝 1)
    : ∃ V, IsOpen V ∧ 1 ∈ V ∧ V⁻¹ * V ⊆ U := by
  obtain ⟨V, h_1_V, hVU⟩ := lem3 hU
  obtain ⟨W, hWV, hW_open, hW_1⟩ := eventually_nhds_iff.mp h_1_V
  use W
  refine ⟨hW_open, hW_1, ?_⟩
  have : W⁻¹ ⊆ V⁻¹ := by exact fun ⦃a⦄ ↦ hWV a⁻¹
  have : W⁻¹ * W ⊆ V⁻¹ * V := by exact mul_subset_mul this hWV
  exact fun ⦃a⦄ a_1 ↦ hVU (this a_1)

lemma lem4 (D : Set H) (h_D_dense : Dense D) (V : Set H) (h_V_open : IsOpen V)
  (h_V_nonempty : V.Nonempty)
  : ⋃ d ∈ D, d • V = ⊤ := by
    ext x
    constructor
    . intro h
      simp at h
      obtain ⟨i, hi⟩ := h
      trivial
    intro h
    obtain ⟨v, hv⟩ := h_V_nonempty
    have V_inv_open : IsOpen V⁻¹ := by exact IsOpen.inv h_V_open
    have h_V_open' : IsOpen (x • V⁻¹) := by exact IsOpen.smul V_inv_open x
    have h_nonempty : (x • V⁻¹).Nonempty := by
      use x • v⁻¹
      simpa [HSMul.hSMul, SMul.smul]
    have h1 : ∃ d ∈ D, d ∈ x • V⁻¹ := by
      exact Dense.exists_mem_open h_D_dense h_V_open' h_nonempty
    obtain ⟨d, hdD, hdxV⟩ := h1
    have h2 : x ∈ d • V := by
      simp at hdxV
      assumption
    simp
    exact ⟨d, hdD, h2⟩


open TopologicalSpace

variable [SeparableSpace H]

theorem automatic_continuity {φ : G →* H} (h: Measurable φ)
  : Continuous φ := by
  constructor
  intro U hU
  have h0 : MeasurableSet U := by exact IsOpen.measurableSet hU
  set preU := φ ⁻¹' U
  have h10 : MeasurableSet preU := by
    exact h h0
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have h_Im_g_in_U: φ g ∈ U := by exact hg
  have h_1_in_ginvU : 1 ∈ (φ g)⁻¹ • U := by
    use φ g
    refine ⟨h_Im_g_in_U, ?_⟩
    simp
  have h_ginvU_open : IsOpen ((φ g)⁻¹ • U) := by
    exact IsOpen.smul hU (φ g)⁻¹

  have : (φ g)⁻¹ • U ∈ 𝓝 1 := by exact IsOpen.mem_nhds h_ginvU_open h_1_in_ginvU
  have ⟨V, h_V_open, h_1_in_V, h_V_U⟩ := lem3' this

  have h_V_nonempty : V.Nonempty := by exact Set.nonempty_of_mem h_1_in_V

  have ⟨D, hD_countable, hD_dense⟩ := exists_countable_dense H

  have h1 : ⋃ h ∈ D, h • V = ⊤ := by exact lem4 D hD_dense V h_V_open h_V_nonempty
  have h11 : φ⁻¹' (⋃ h ∈ D, h • V) = ⋃ h ∈ D, φ⁻¹' (h • V) := by
    exact preimage_iUnion₂
  have h2 : ⋃ h ∈ D, φ⁻¹' (h • V) = ⊤ := by
    rw [←h11, h1]
    rfl
  have h100 : ¬ (IsMeagre (⊤ : Set G)) := by
    by_contra h
    simp [IsMeagre] at h
    apply nonempty_of_residual at h
    simp at h
  have h101 : ∃ d ∈ D, ¬ IsMeagre (φ⁻¹' (d • V)) := by
    by_contra h_contra
    simp at h_contra
    have : Countable ↑D := by exact hD_countable
    have : IsMeagre (⋃ h ∈ D, φ⁻¹' (h • V)) := by
      rw [biUnion_eq_iUnion]
      apply isMeagre_iUnion'
      simpa
    rw [h2] at this
    contradiction
  obtain ⟨d, hd, hnonmeagre⟩ := h101
  set A := φ⁻¹' (d • V)
  have h38 : IsOpen (d • V) := by exact IsOpen.smul h_V_open d
  have h83 : MeasurableSet (d • V) := by exact IsOpen.measurableSet h38
  have h385 : MeasurableSet A := by exact h h83
  have h39 : BaireMeasurableSet A := by
    exact MeasurableSet.baireMeasurableSet h385
  have h4 : A⁻¹ * A ∈ nhds 1 := by exact pettis' h39 hnonmeagre
  have h222: g • (A⁻¹ * A) ∈ nhds g := by exact smul_mem_nhds_self.mpr h4
  have h23 : φ '' (g • (A⁻¹ * A)) ⊆ U := by
    intro x hx
    simp at hx
    obtain ⟨x_1, hx_1, hx_2⟩ := hx
    simp [HSMul.hSMul, SMul.smul] at hx_1
    obtain ⟨a_1, ha_1, a_2, ha_2, ha_x⟩ := hx_1
    simp at ha_x
    rw [← hx_2]
    have h143 : x_1 = g * (a_1 * a_2) := by exact eq_mul_of_inv_mul_eq (id (Eq.symm ha_x))
    rw [h143]
    simp
    have h123 : φ a_2 ∈ d • V := by exact ha_2
    have h12340 : φ '' A ⊆ d • V := by
      dsimp [A]
      exact image_preimage_subset (⇑φ) (d • V)
    have h1232 : φ a_1 ∈ (φ '' A)⁻¹ := by
      simp
      use a_1⁻¹
      constructor
      assumption
      simp
    have h124 : φ a_1 ∈ (d • V)⁻¹ := by
      exact h12340 h1232
    have h2323 : φ a_1 * φ a_2 ∈ V⁻¹ * V := by
      obtain ⟨v_1, h_v_1, h_v_12⟩ := h123
      obtain ⟨v_2, h_v_2, h_v_22⟩ := h124
      simp at h_v_12 h_v_22
      have h_v_222 : (d * v_2)⁻¹ = φ a_1 := by exact inv_eq_iff_eq_inv.mpr h_v_22
      rw [←h_v_12, ←h_v_222]
      have h_v_2111 : v_2⁻¹ ∈ V⁻¹ := by exact Set.inv_mem_inv.mpr h_v_2
      use v_2⁻¹
      constructor
      exact h_v_2111
      use v_1
      constructor
      exact h_v_1
      simp
      group

    have h_V_U_2 : (φ g) • (V⁻¹ * V) ⊆ U := by
      exact Set.smul_set_subset_iff_subset_inv_smul_set.mpr h_V_U
    have h3213 : φ g * (φ a_1 * φ a_2) ∈ φ g • (V⁻¹ * V) := by
      exact mem_leftCoset (φ g) h2323
    exact h_V_U_2 h3213
  have h234 : g • (A⁻¹ * A) ⊆ preU := by
    simp at h23
    simpa [preU]
  exact mem_of_superset h222 h234

#print axioms automatic_continuity
