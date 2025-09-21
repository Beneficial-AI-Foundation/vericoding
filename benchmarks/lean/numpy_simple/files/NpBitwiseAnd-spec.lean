-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bitwiseAnd {n : Nat} (a b : Vector Nat n) : Vector Nat n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bitwiseAnd_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseAnd a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseAnd a b)[i] = a[i] &&& b[i] :=
sorry
-- </vc-theorems>