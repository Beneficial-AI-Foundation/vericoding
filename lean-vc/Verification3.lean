import Lean

-- Define a simple inductive type
inductive Color
| red
| green
| blue

-- Prove a simple theorem about the type
theorem colorCount : List.length [Color.red, Color.green, Color.blue] = 3 :=
  rfl
