/-!
# Matrix Type Definition

Simple Matrix type for numpy specs that don't need full mathlib matrices.
-/

/-- Simple Matrix type as a function from indices to values -/
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

/-- Simple 3D array type -/
def Array3 (l m n : Nat) (α : Type) := Fin l → Fin m → Fin n → α