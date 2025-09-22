-- <vc-preamble>
def absInt (x : Int) : Int := if x < 0 then -x else x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs {n : Nat} (a : Vector Int n) : Vector Int n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem abs_spec {n : Nat} (a : Vector Int n) :
  (abs a).toList.length = n ∧
  (∀ i : Fin n, (abs a)[i] = Int.natAbs (a[i])) ∧
  (∀ i : Fin n, (abs a)[i] ≥ 0) :=
sorry
-- </vc-theorems>