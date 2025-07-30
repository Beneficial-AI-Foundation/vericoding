/-
# NumPy Polyder Specification

Port of np_polyder.dfy to Lean 4
-/

namespace DafnySpecs.NpPolyder

/-- Compute polynomial derivative -/
def polyder {n : Nat} (poly : Vector Float n) (m : Int) : Vector Float (n - m.natAbs) := sorry

/-- Specification: The result has correct length -/
theorem polyder_length {n : Nat} (poly : Vector Float n) (m : Int)
  (h : m > 0) :
  let ret := polyder poly m
  ret.toList.length = n - m.natAbs := sorry

end DafnySpecs.NpPolyder
