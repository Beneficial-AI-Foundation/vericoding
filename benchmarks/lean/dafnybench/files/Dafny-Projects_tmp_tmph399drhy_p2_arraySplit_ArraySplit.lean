-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ArraySplit (a : Array Int) : Array Int × Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ArraySplit_spec (a : Array Int) (res : Array Int × Array Int) :
let (b, c) := res

-- Note: fresh arrays concept simplified

(a.size = b.size + c.size) ∧

-- Note: array concatenation simplified

(a.size > 1 → a.size > b.size) ∧

(a.size > 1 → a.size > c.size) :=
sorry
-- </vc-theorems>