-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def M (N : Int) (a : Array Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem M_spec (N : Int) (a : Array Int) :
(N ≥ 0 ∧ a.size = N ∧ (∀ k:Fin a.size, 0 ≤ a[k]!)) →
let (sum, max) := M N a
sum ≤ N * max :=
sorry
-- </vc-theorems>