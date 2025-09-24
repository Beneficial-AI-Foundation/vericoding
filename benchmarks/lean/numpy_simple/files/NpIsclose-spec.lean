-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def np_isclose {n : Nat} (a b : Vector Int n) (tol : Int) : Vector Bool n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem np_isclose_spec {n : Nat} (a b : Vector Int n) (tol : Int)
  (h1 : n > 0)
  (h2 : tol > 0) :
  let ret := np_isclose a b tol
  (ret.toList.length = n) ∧
  (∀ i : Fin n, if -tol < a[i] - b[i] ∧ a[i] - b[i] < tol then ret[i] = true else ret[i] = false) :=
sorry
-- </vc-theorems>