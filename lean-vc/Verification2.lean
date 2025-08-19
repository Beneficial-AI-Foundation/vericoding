import Lean

-- Define a simple function
def double (n : Nat) : Nat := n * 2

-- Prove a property of the function
theorem doubleProperty : double 2 = 4 :=
  rfl
