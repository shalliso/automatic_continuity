import Mathlib

/-!
# Cantor-Bendixson Derivative and Rank

The Cantor-Bendixson Theorem says that in a second countable space, every set is the union of a
countable set and a perfect set. This is already proved in mathlib directly, but I wanted to
write up a proof using the derivative operation as it requires recursion and induction over the
ordinals, which is something I want to have practice with.

-/

open Set Filter Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

section LimitPoints

def limitPoints (A : Set X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, ((U ∩ A) \ {x}).Nonempty}

lemma mem_limitPoints_iff {A : Set X} {x : X} :
    x ∈ limitPoints A ↔ ∀ U ∈ 𝓝 x, ((U ∩ A) \ {x}).Nonempty := by
  rfl

lemma limitPoints_iff_nhds_inter {A : Set X} {x : X} :
    x ∈ limitPoints A ↔ ∀ U ∈ 𝓝 x, ∃ y ∈ A, y ∈ U ∧ y ≠ x := by
  simp [mem_limitPoints_iff]
  constructor
  · intro h U hU
    obtain ⟨y, hy⟩ := h U hU
    obtain ⟨⟨hU, hA⟩, hnx⟩ := hy
    refine ⟨y, hA, hU, hnx⟩
  · intro h U hU
    obtain ⟨y, hyA, hyU, hyx⟩ := h U hU
    exact ⟨y, ⟨hyU, hyA⟩, hyx⟩

end LimitPoints

section CBDerivative

def cbDerivative (A : Set X) : Set X := limitPoints A ∩ A

lemma cbDerivative_subset (A : Set X) : cbDerivative A ⊆ A := by
  dsimp [cbDerivative]
  exact inter_subset_right

lemma mem_cbDerivative_iff {A : Set X} {x : X} :
    x ∈ cbDerivative A ↔ x ∈ limitPoints A ∧ x ∈ A := by
  rfl

lemma cbDerivative_empty : cbDerivative (∅ : Set X) = ∅ := by
  simp [cbDerivative]

lemma cbDerivative_singleton (x : X) : cbDerivative {x} = ∅ := by
  dsimp [cbDerivative, limitPoints]
  by_contra h
  simp at h
  specialize h ⊤
  simp at h

lemma cbDerivative_mono {A B : Set X} (h : A ⊆ B) : cbDerivative A ⊆ cbDerivative B := by
  intro x hx
  rw [mem_cbDerivative_iff] at hx
  obtain ⟨hxlim, hxA⟩ := hx
  constructor
  · intro U hU
    rw [mem_limitPoints_iff] at hxlim
    obtain ⟨y, hy⟩ := hxlim U hU
    have : (U ∩ A) \ {x} ⊆ ((U ∩ B) \ {x}) := by
      exact diff_subset_diff_left (inter_subset_inter_right U h)
    exact Set.nonempty_of_mem (this hy)
  · exact h hxA

def cbDerivativeOrd (A : Set X) (o : Ordinal) : Set X :=
  Ordinal.limitRecOn o
    A
    (fun _ B => cbDerivative B)
    (fun β _ f => ⋂ x : Iio β, f x.1 x.2)

lemma cbDerivativeOrd_zero (A : Set X) : cbDerivativeOrd A 0 = A := by
  rw [cbDerivativeOrd]
  simp [Ordinal.limitRecOn_zero]

lemma cbDerivativeOrd_succ (A : Set X) (α : Ordinal) :
    cbDerivativeOrd A (Order.succ α) = cbDerivative (cbDerivativeOrd A α) := by
  rw [cbDerivativeOrd]
  rw [Ordinal.limitRecOn_succ]
  rw [cbDerivativeOrd]

lemma cbDerivativeOrd_limit (A : Set X) {α : Ordinal} (hα : Order.IsSuccLimit α) :
    cbDerivativeOrd A α = ⋂ β : Iio α, cbDerivativeOrd A β.val := by
  rw [cbDerivativeOrd]
  rw [Ordinal.limitRecOn_limit]
  · rfl
  · assumption

lemma cbDerivativeOrd_subset (A : Set X) (α : Ordinal) : cbDerivativeOrd A α ⊆ A := by
  induction α using Ordinal.limitRecOn with
  | zero => rw [cbDerivativeOrd_zero A]
  | succ β hβ =>
    rw [cbDerivativeOrd_succ]
    intro x hx
    exact cbDerivative_subset A (cbDerivative_mono hβ hx)
  | limit β hβ hβ2 =>
    rw [cbDerivativeOrd_limit A hβ]
    obtain ⟨γ, hγ⟩ := not_isMin_iff.mp (Order.IsSuccLimit.not_isMin hβ)
    exact iInter_subset_of_subset ⟨γ, hγ⟩ (hβ2 γ hγ)

lemma cbDerivativeOrd_antitone (A : Set X) : Antitone (cbDerivativeOrd A) := by
  sorry

def cbKernel (A : Set X) : Set X :=
  ⋂ α : Ordinal.{0}, cbDerivativeOrd A α

lemma cbKernel_isPerfect (A : Set X) : Perfect (cbKernel A) := by
  sorry

lemma cbDerivativeOrd_eventually_eq_kernel (A : Set X) :
    ∃ α : Ordinal, ∀ β ≥ α, cbDerivativeOrd A β = cbKernel A := by
  sorry

end CBDerivative

section Examples

/-- In a discrete space, every set has empty derivative. -/
lemma cbDerivative_of_discrete [DiscreteTopology X] (A : Set X) :
    cbDerivative A = ∅ := by
  rw [cbDerivative, limitPoints]
  ext x
  simp
  intro h
  have : x ∈ ({x} : Set X) := by exact rfl
  specialize h {x} this
  obtain ⟨y, hy⟩ := h
  sorry

end Examples
