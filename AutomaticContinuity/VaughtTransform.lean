import Mathlib
import AutomaticContinuity.Baire

/-!
# Vaught Transform

This file defines the Vaught transform in the context of continuous actions of Polish groups
on Polish spaces, following the classical definition from descriptive set theory.

## Main definitions

* `VaughtTransformStar`: The A^{*U} transform using comeager sets
* `VaughtTransformDelta`: The A^{ΔU} transform using nonmeager sets

## Main results

* Basic properties of both transforms including monotonicity and measurability preservation
* Relationship between the two transforms
* Behavior under composition and intersection

## References

* Vaught, R. L. "Invariant sets in topology and logic"
* Kechris, A. S. "Classical Descriptive Set Theory"
* Becker, H. and Kechris, A. S. "The Descriptive Set Theory of Polish Group Actions"
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped Pointwise

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]
variable {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G] [IsTopologicalGroup G]
variable [MulAction G X] [ContinuousConstSMul G X]

-- Right action of G on Set G
instance : HSMul (Set G) G (Set G) where
  hSMul U g := {u • g | u ∈ U}

abbrev VaughtTransformStar (A : Set X) (U : Set G) : Set X :=
  {x : X | ∀ᵇ (g : G), g ∈ U → g • x ∈ A}

abbrev VaughtTransformDelta (A : Set X) (U : Set G) : Set X :=
  {x : X | ∃ᵇ (g : G), g ∈ U ∧ g • x ∈ A}

-- Notation for the transforms
notation:70 A "^{*" U "}" => VaughtTransformStar A U
notation:70 A "^{Δ" U "}" => VaughtTransformDelta A U

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

lemma star_inter : (A ∩ B)^{*U} = A^{*U} ∩ B^{*U} :=
  by sorry

lemma star_iInter {ι : Type*} (s : ι → Set X) : (⋂ i, s i)^{*U} = ⋂ i, (s i)^{*U} := by
  sorry

lemma star_sInter {s : Set (Set X)} : (⋂₀ s)^{*U} = ⋂₀ {A^{*U} | A ∈ s} := by
  sorry

lemma star_union : A^{* U ∪ V} = A^{*U} ∩ A^{*V} := by
  sorry

lemma star_iUnion {ι : Type*} (s : ι → Set G) : A^{* ⋃ i, s i} = ⋂ i, (A)^{* s i} := by
  sorry

lemma star_sUnion {s : Set (Set G)} : A^{* ⋃₀ s} = ⋂₀ {A^{*U} | U ∈ s} := by
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
  sorry

lemma delta_smul_iff : g • x ∈ A^{ΔU} ↔ x ∈ A^{ΔU • g} := by
  sorry

end VaughtTransform
