-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAlpha {n : Nat} (input : Vector String n) : Vector Bool n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isAlpha_spec {n : Nat} (input : Vector String n) :
  let ret := isAlpha input
  (ret.toList.length = n) ∧
  (∀ i : Fin n, ret[i] = (input[i].length > 0 ∧
    input[i].all fun c => ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z'))) :=
sorry
-- </vc-theorems>