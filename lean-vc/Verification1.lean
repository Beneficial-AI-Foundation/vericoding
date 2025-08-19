import Lean

-- Define a simple constant
constant x : Nat

definition exampleDefinition : Nat := x + 1

-- Prove a simple theorem
theorem exampleTheorem : exampleDefinition = x + 1 :=
  unfold exampleDefinition
