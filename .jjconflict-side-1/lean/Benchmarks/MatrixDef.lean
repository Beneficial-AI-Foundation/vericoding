/-!
# Matrix Type Definition

Simple Matrix type for numpy specs that don't need full mathlib matrices.
-/

/-- Simple Matrix type as a function from indices to values -/
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

/-- Simple 3D array type -/
def Array3 (l m n : Nat) (α : Type) := Fin l → Fin m → Fin n → α

namespace Matrix

/-- Convert matrix to list in row-major order -/
def toList {m n : Nat} {α : Type} (mat : Matrix m n α) : List α :=
  (List.finRange m).flatMap fun i => List.finRange n |>.map fun j => mat i j

/-- Get element notation for matrices -/
instance {m n : Nat} {α : Type} : GetElem (Matrix m n α) (Fin m) (Fin n → α) (fun _ _ => True) where
  getElem mat i _ := mat i

end Matrix