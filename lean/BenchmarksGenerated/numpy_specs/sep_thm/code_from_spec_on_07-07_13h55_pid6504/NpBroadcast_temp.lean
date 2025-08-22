/-
# NumPy Broadcast Specification

Port of np_broadcast.dfy to Lean 4
-/

namespace DafnySpecs.NpBroadcast

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Vector (Vector α n) m

-- LLM HELPER
def Vector.natGet! {n : Nat} (v : Vector Int n) (i : Nat) : Int := 
  if h : i < n then v.get ⟨i, h⟩ else 0

-- LLM HELPER
def Matrix.get! {α : Type*} {m n : Nat} (mat : Matrix α m n) (i : Nat) : Vector α n := 
  if h : i < m then mat.get ⟨i, h⟩ else Vector.replicate n (Classical.arbitrary α)

-- LLM HELPER
def Matrix.toList {α : Type*} {m n : Nat} (mat : Matrix α m n) : List α := 
  (mat.toList.map (·.toList)).join

/-- Broadcast a vector to a 2D shape -/
def broadcast {n : Nat} (a : Vector Int n) (shape : Vector Int 2) : Matrix Int (Int.natAbs (shape.natGet! 0)) (Int.natAbs (shape.natGet! 1)) := 
  Vector.ofFn fun i => 
    Vector.ofFn fun j => 
      if shape.natGet! 0 = n then a.natGet! i else a.natGet! j

/-- Specification: The result has the correct dimensions -/
theorem broadcast_length {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape.natGet! 0 = n ∨ shape.natGet! 1 = n) :
  let ret := broadcast a shape
  ret.toList.length = Int.natAbs (shape.natGet! 0) * Int.natAbs (shape.natGet! 1) := by
  simp only [broadcast, Matrix.toList]
  rw [Vector.toList_ofFn, List.map_length, Vector.toList_ofFn]
  simp only [List.join_length, List.sum_replicate]
  ring

/-- Specification: Elements are correctly broadcasted -/
theorem broadcast_spec {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape.natGet! 0 = n ∨ shape.natGet! 1 = n) :
  let ret := broadcast a shape
  ∀ i j : Nat, i < Int.natAbs (shape.natGet! 0) → j < Int.natAbs (shape.natGet! 1) →
    if shape.natGet! 0 = n then (ret.get! i).natGet! j = a.natGet! i else (ret.get! i).natGet! j = a.natGet! j := by
  intro i j hi hj
  simp only [broadcast, Matrix.get!, Vector.natGet!]
  split_ifs with h_eq h_i h_j
  · simp only [Vector.get_ofFn]
    split_ifs with h_i_bound h_j_bound
    · rfl
    · rfl
  · simp only [Vector.get_ofFn] 
    split_ifs with h_i_bound h_j_bound
    · rfl
    · rfl
  · simp only [Vector.get_ofFn]
    split_ifs with h_i_bound h_j_bound
    · rfl
    · rfl
  · simp only [Vector.get_ofFn]
    split_ifs with h_i_bound h_j_bound
    · rfl
    · rfl

end DafnySpecs.NpBroadcast