/-!
# Benchmarks.MatrixDef

Lightweight matrix definitions used by older numpy specs. This mirrors
the minimal helper introduced upstream (see commit 5ea12041a) so that
files importing `Benchmarks.MatrixDef` continue to compile.
-/

/-- Simple Matrix type as a function from indices to values. -/
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

/-- Simple 3D array type. -/
def Array3 (l m n : Nat) (α : Type) := Fin l → Fin m → Fin n → α

