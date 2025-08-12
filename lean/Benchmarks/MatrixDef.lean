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

/-- Get element notation for matrices with Nat indices (returns whole row) -/
instance {m n : Nat} {α : Type} : GetElem (Matrix m n α) Nat (Fin n → α) (fun _ i => i < m) where
  getElem mat i h := mat ⟨i, h⟩

/-- Get element notation for row functions with Nat indices -/
instance {n : Nat} {α : Type} : GetElem (Fin n → α) Nat α (fun _ j => j < n) where
  getElem row j h := row ⟨j, h⟩

/-- Alias for Array2 type -/
abbrev Array2 (m n : Nat) (α : Type) := Matrix m n α