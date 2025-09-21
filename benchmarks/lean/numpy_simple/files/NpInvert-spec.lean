-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def invert {n : Nat} (bitWidth : Nat) (a : Vector Nat n) : Vector Nat n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invert_spec {n : Nat} (bitWidth : Nat) (a : Vector Nat n) :
  (invert bitWidth a).toList.length = n ∧
  ∀ i : Fin n, (invert bitWidth a)[i] = (2^bitWidth - 1) - a[i] :=
sorry
-- </vc-theorems>