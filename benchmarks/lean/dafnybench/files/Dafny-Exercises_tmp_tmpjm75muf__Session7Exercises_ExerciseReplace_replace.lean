-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replace (v : Array Int) (x : Int) (y : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem replace_spec (v : Array Int) (x y : Int) :
let v' := replace v x y
∀ k, 0 ≤ k ∧ k < v.size →
((v[k]! = x → v'[k]! = y) ∧
(v[k]! ≠ x → v'[k]! = v[k]!)) :=
sorry
-- </vc-theorems>