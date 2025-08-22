/-
# NumPy Left Shift Specification

Port of np_left_shift.dfy to Lean 4
-/

namespace DafnySpecs.NpLeftShift

/-- Left shift operation for integers -/
def shiftLeftInt (x : Int) (n : Nat) : Int :=
  if x ≥ 0 then
    Int.ofNat (x.natAbs <<< n)
  else
    -(Int.ofNat ((-x).natAbs <<< n))

/-- Element-wise left shift of integers by natural numbers -/
def leftShift {n : Nat} (a : Vector Int n) (b : Vector Nat n) 
  (h : ∀ i : Fin n, b[i] < 64) : Vector Int n := 
  Vector.ofFn (fun i => shiftLeftInt (a[i]) (b[i]))

/-- Specification: The result has the same length as inputs -/
theorem leftShift_length {n : Nat} (a : Vector Int n) (b : Vector Nat n) 
  (h : ∀ i : Fin n, b[i] < 64) :
  (leftShift a b h).toList.length = n := by
  simp [leftShift, Vector.toList_ofFn]

/-- Specification: Each element is the left shift of corresponding input elements -/
theorem leftShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) 
  (h : ∀ i : Fin n, b[i] < 64) :
  ∀ i : Fin n, (leftShift a b h)[i] = shiftLeftInt (a[i]) (b[i]) := by
  intro i
  simp [leftShift, Vector.ofFn_get]

end DafnySpecs.NpLeftShift