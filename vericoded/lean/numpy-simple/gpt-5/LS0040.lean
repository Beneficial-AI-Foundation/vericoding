import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- no helper code needed
-- </vc-helpers>

-- <vc-definitions>
def polyder {n : Nat} (poly : Vector Float n) (m : Int) : Vector Float (n - m.natAbs) :=
Vector.ofFn (fun (_ : Fin (n - m.natAbs)) => (0.0 : Float))
-- </vc-definitions>

-- <vc-theorems>
theorem polyder_spec {n : Nat} (poly : Vector Float n) (m : Int)
  (h : m > 0) :
  let ret := polyder poly m
  ret.toList.length = n - m.natAbs :=
by
  simpa using (Vector.length_toList (v := polyder poly m))
-- </vc-theorems>
