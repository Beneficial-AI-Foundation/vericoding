-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def prod {n : Nat} (a : Vector Int n) : Int :=
sorry

def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n ∧
  (∀ i : Fin n, a[i] = 0 → prod a = 0) :=
sorry
-- </vc-theorems>