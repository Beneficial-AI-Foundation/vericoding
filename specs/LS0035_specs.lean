-- <vc-preamble>
def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mod {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mod_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (mod a b).toList.length = n ∧
  ∀ i : Fin n, (mod a b)[i] = a[i] % (b.val[i]) :=
sorry
-- </vc-theorems>