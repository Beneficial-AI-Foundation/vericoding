-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_efficiency_workgroup (n : Nat) (superiors : List Int) (efficiencies : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_node_case (efficiency : Int) (h : -100 ≤ efficiency ∧ efficiency ≤ 100) :
  max_efficiency_workgroup 1 [-1] [efficiency] = efficiency :=
sorry
-- </vc-theorems>