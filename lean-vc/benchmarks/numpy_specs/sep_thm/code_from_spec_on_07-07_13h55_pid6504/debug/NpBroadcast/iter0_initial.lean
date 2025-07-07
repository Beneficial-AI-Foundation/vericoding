/-
# NumPy Broadcast Specification

Port of np_broadcast.dfy to Lean 4
-/

namespace DafnySpecs.NpBroadcast

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Vector (Vector α n) m

-- LLM HELPER
def Vector.get! {α : Type*} {n : Nat} (v : Vector α n) (i : Nat) : α := v.get ⟨i % n, Nat.mod_lt i (Nat.succ_pos (n - 1))⟩

-- LLM HELPER
def Matrix.get! {α : Type*} {m n : Nat} (mat : Matrix α m n) (i : Nat) : Vector α n := mat.get ⟨i % m, Nat.mod_lt i (Nat.succ_pos (m - 1))⟩

-- LLM HELPER
def Matrix.toList {α : Type*} {m n : Nat} (mat : Matrix α m n) : List α := 
  (mat.toList.map (·.toList)).join

/-- Broadcast a vector to a 2D shape -/
def broadcast {n : Nat} (a : Vector Int n) (shape : Vector Int 2) : Matrix Int (shape[0]!) (shape[1]!) := 
  Vector.ofFn fun i => 
    Vector.ofFn fun j => 
      if shape[0]! = n then a[i]! else a[j]!

/-- Specification: The result has the correct dimensions -/
theorem broadcast_length {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape[0]! = n ∨ shape[1]! = n) :
  let ret := broadcast a shape
  ret.toList.length = shape[0]! * shape[1]! := by
  simp [broadcast, Matrix.toList]
  rw [Vector.toList_ofFn, List.map_length, Vector.toList_ofFn]
  simp [List.join_length, List.sum_replicate]
  ring

/-- Specification: Elements are correctly broadcasted -/
theorem broadcast_spec {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape[0]! = n ∨ shape[1]! = n) :
  let ret := broadcast a shape
  ∀ i j : Nat, i < shape[0]! → j < shape[1]! →
    if shape[0]! = n then ret[i]![j]! = a[i]! else ret[i]![j]! = a[j]! := by
  intro i j hi hj
  simp [broadcast, Matrix.get!, Vector.get!]
  split_ifs with h_eq
  · simp [Vector.get_ofFn, Vector.get_ofFn]
  · simp [Vector.get_ofFn, Vector.get_ofFn]

end DafnySpecs.NpBroadcast