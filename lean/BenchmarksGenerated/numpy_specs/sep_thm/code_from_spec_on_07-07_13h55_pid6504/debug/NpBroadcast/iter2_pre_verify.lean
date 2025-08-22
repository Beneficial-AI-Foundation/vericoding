/-
# NumPy Broadcast Specification

Port of np_broadcast.dfy to Lean 4
-/

namespace DafnySpecs.NpBroadcast

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Vector (Vector α n) m

-- LLM HELPER
def Vector.get! {α : Type*} {n : Nat} (v : Vector α n) (i : Nat) : α := 
  if h : i < n then v.get ⟨i, h⟩ else v.get ⟨0, Nat.zero_lt_succ (n - 1)⟩

-- LLM HELPER
def Matrix.get! {α : Type*} {m n : Nat} (mat : Matrix α m n) (i : Nat) : Vector α n := 
  if h : i < m then mat.get ⟨i, h⟩ else mat.get ⟨0, Nat.zero_lt_succ (m - 1)⟩

-- LLM HELPER
def Matrix.toList {α : Type*} {m n : Nat} (mat : Matrix α m n) : List α := 
  (mat.toList.map (·.toList)).join

-- LLM HELPER
def Vector.natGet! {n : Nat} (v : Vector Int n) (i : Nat) : Int := 
  if h : i < n then v.get ⟨i, h⟩ else 0

/-- Broadcast a vector to a 2D shape -/
def broadcast {n : Nat} (a : Vector Int n) (shape : Vector Int 2) : Matrix Int (shape.natGet! 0) (shape.natGet! 1) := 
  Vector.ofFn fun i => 
    Vector.ofFn fun j => 
      if shape.natGet! 0 = n then a.natGet! i else a.natGet! j

/-- Specification: The result has the correct dimensions -/
theorem broadcast_length {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape.natGet! 0 = n ∨ shape.natGet! 1 = n) :
  let ret := broadcast a shape
  ret.toList.length = shape.natGet! 0 * shape.natGet! 1 := by
  simp [broadcast, Matrix.toList]
  rw [Vector.toList_ofFn, List.map_length, Vector.toList_ofFn]
  simp [List.join_length, List.sum_replicate]
  ring

/-- Specification: Elements are correctly broadcasted -/
theorem broadcast_spec {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape.natGet! 0 = n ∨ shape.natGet! 1 = n) :
  let ret := broadcast a shape
  ∀ i j : Nat, i < shape.natGet! 0 → j < shape.natGet! 1 →
    if shape.natGet! 0 = n then ret.get!  i .get! j = a.natGet! i else ret.get! i .get! j = a.natGet! j := by
  intro i j hi hj
  simp [broadcast, Matrix.get!, Vector.get!]
  split_ifs with h_eq
  · simp [Vector.get_ofFn, Vector.natGet!]
  · simp [Vector.get_ofFn, Vector.natGet!]

end DafnySpecs.NpBroadcast