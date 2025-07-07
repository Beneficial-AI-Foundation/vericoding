/-
# NumPy Broadcast Specification

Port of np_broadcast.dfy to Lean 4
-/

namespace DafnySpecs.NpBroadcast

/-- Broadcast a vector to a 2D shape -/
def broadcast {n : Nat} (a : Vector Int n) (shape : Vector Int 2) : Matrix Int (shape[0]!) (shape[1]!) := sorry

/-- Specification: The result has the correct dimensions -/
theorem broadcast_length {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape[0]! = n ∨ shape[1]! = n) :
  let ret := broadcast a shape
  ret.toList.length = shape[0]! * shape[1]! := sorry

/-- Specification: Elements are correctly broadcasted -/
theorem broadcast_spec {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape[0]! = n ∨ shape[1]! = n) :
  let ret := broadcast a shape
  ∀ i j : Nat, i < shape[0]! → j < shape[1]! →
    if shape[0]! = n then ret[i]![j]! = a[i]! else ret[i]![j]! = a[j]! := sorry

end DafnySpecs.NpBroadcast
