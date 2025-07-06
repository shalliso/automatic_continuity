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

theorem BaireTheorem.nonMeagre_of_univ [Nonempty X] [BaireSpace X]
    : ¬ (IsMeagre (univ : Set X)) := by sorry


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
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]



-- Add this next to exists_closed_nhds_one_inv_eq_mul_subset in
-- Topology/Algebra/Group/Pointwise.lean
/-- Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the identity which
is open, symmetric, and satisfies `V * V ⊆ U`. -/
@[to_additive "Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the
identity which is open, symmetric, and satisfies `V + V ⊆ U`."]
theorem exists_open_nhds_one_inv_eq_mul_subset {U : Set G} (hU : U ∈ 𝓝 1) :
    ∃ V ∈ 𝓝 1, IsOpen V ∧ V⁻¹ = V ∧ V * V ⊆ U := by
  rcases exists_open_nhds_one_mul_subset hU with ⟨V, V_open, V_one, hV⟩
  --rcases exists_mem_nhds_isClosed_subset (V_open.mem_nhds V_mem) with ⟨W, W_mem, W_closed, hW⟩
  have V_mem : V ∈ 𝓝 1 := V_open.mem_nhds V_one
  refine ⟨V ∩ V⁻¹, Filter.inter_mem V_mem (inv_mem_nhds_one G V_mem), V_open.inter V_open.inv,
    by simp [inter_comm], ?_⟩
  calc
  V ∩ V⁻¹ * (V ∩ V⁻¹)
  _ ⊆ V * V := mul_subset_mul inter_subset_left inter_subset_left
  _ ⊆ U := hV


open TopologicalSpace

variable [SeparableSpace H] [BorelSpace H]

example {φ : G →* H} (h : ContinuousAt φ 1) : (Continuous φ) := continuous_of_continuousAt_one φ h

lemma automatic_continuity {φ : G →* H} (h: Measurable φ) : Continuous φ := by
  -- Enough to show continuous at 1
  apply continuous_of_continuousAt_one

  rw [continuousAt_def, map_one]
  intro U hU
  obtain ⟨V, h_V_mem, h_V_open, h_V_symm, h_V_U⟩ := exists_open_nhds_one_inv_eq_mul_subset hU

  set m : H → Set H := fun h ↦ h • V
  have hasdf : ∀ h, m h ∈ nhds h := by
    intro h
    dsimp [m]
    exact smul_mem_nhds_self.mpr h_V_mem

  obtain ⟨D, hD_countable, h1⟩ : ∃ (D : Set H), D.Countable ∧ ⋃ d ∈ D, m d = univ
    := TopologicalSpace.countable_cover_nhds hasdf

  have h2 : ⋃ h ∈ D, φ⁻¹' (h • V) = univ := by
    rw [←preimage_iUnion₂, h1]
    rfl

  have h101 : ∃ d ∈ D, ¬ IsMeagre (φ⁻¹' (d • V)) := by
    by_contra h_contra
    simp at h_contra

    --have : Countable ↑D := by exact hD_countable
    have : IsMeagre (⋃ h ∈ D, φ⁻¹' (h • V)) := by
      rw [IsMeagre, compl_iUnion]
      dsimp [IsMeagre] at h_contra
      simp
      exact (countable_bInter_mem hD_countable).mpr h_contra

    rw [h2] at this
    have a : ¬ IsMeagre (univ : Set G) := BaireTheorem.nonMeagre_of_univ
    contradiction

  obtain ⟨d, hd, hnonmeagre⟩ : ∃ d ∈ D, ¬ IsMeagre (φ⁻¹' (d • V)) := h101

  set A := φ⁻¹' (d • V)
  have : BaireMeasurableSet A := (h (h_V_open.smul d).measurableSet).baireMeasurableSet
  have h4 : A⁻¹ * A ∈ nhds 1 := by exact pettis' this hnonmeagre

  have h234 : φ '' A ⊆ d • V := by
    dsimp [A]
    exact image_preimage_subset (⇑φ) (d • V)
  have h23 : φ '' (A⁻¹ * A) ⊆ U := by
    calc
      φ '' (A⁻¹ * A)
        = (φ '' A⁻¹) * (φ '' A) := by
          exact image_mul φ
      _ = (φ '' A)⁻¹ * (φ '' A) := by
          exact congrFun (congrArg HMul.hMul (image_inv φ A)) (φ '' A)
      _ ⊆ (d • V)⁻¹ * (d • V) := by
          have : φ '' A ⊆ d • V := by
            dsimp [A]
            exact image_preimage_subset (⇑φ) (d • V)
          refine mul_subset_mul (inv_subset_inv.mpr h234) h234
      _ ⊆ V⁻¹ * V := by

          sorry
      _ ⊆ U := by
          rw [h_V_symm]
          exact h_V_U


  have h234 : A⁻¹ * A ⊆ φ ⁻¹' U := by
    simpa using h23

  exact mem_of_superset h4 h234

#print axioms automatic_continuity
