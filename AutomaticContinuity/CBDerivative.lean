import Mathlib

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]

def CBDerivative (A : Set X) : Set X :=
