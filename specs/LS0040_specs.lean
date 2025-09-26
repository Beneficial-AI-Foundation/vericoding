-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polyder {n : Nat} (poly : Vector Float n) (m : Int) : Vector Float (n - m.natAbs) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polyder_spec {n : Nat} (poly : Vector Float n) (m : Int)
  (h : m > 0) :
  let ret := polyder poly m
  ret.toList.length = n - m.natAbs :=
sorry
-- </vc-theorems>