/-
  Port of Clover_update_array_spec.dfy
  
  This specification describes a function that updates specific elements in an array:
  - Element at index 4 is incremented by 3
  - Element at index 7 is set to 516
  - All other elements remain unchanged
-/

namespace DafnyBenchmarks

/-- Updates specific elements in an array according to the specification -/
def updateElements (a : Array Int) : Array Int :=
  if a.size < 8 then a
  else
    a |>.set! 4 (a[4]! + 3) |>.set! 7 516

/-- Specification for updateElements -/
theorem updateElements_spec (a : Array Int) 
    (h : a.size ≥ 8) :
    let result := updateElements a
    result[4]! = a[4]! + 3 ∧
    result[7]! = 516 ∧
    ∀ i, 0 ≤ i ∧ i < a.size → i ≠ 7 ∧ i ≠ 4 → result[i]! = a[i]! := by
  sorry

end DafnyBenchmarks