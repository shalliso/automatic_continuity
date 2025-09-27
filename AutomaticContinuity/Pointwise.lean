import Mathlib

open Set Topology Pointwise
variable {X : Type*} {G : Type*} [Group G] [MulAction G X]

variable [TopologicalSpace G] [IsTopologicalGroup G]

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
