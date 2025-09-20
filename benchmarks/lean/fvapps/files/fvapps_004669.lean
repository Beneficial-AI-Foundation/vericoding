-- <vc-preamble>
def sum_list : List Float → Float
  | [] => 0
  | x::xs => x + sum_list xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def resistor_parallel (r : List Float) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem parallel_resistance_positive {r : List Float} (h : ∀ x ∈ r, x > 0) :
  resistor_parallel r > 0 :=
sorry

theorem single_resistor_identity {r : Float} (h : r > 0) :
  resistor_parallel [r] = r :=
sorry

theorem parallel_symmetric {r1 r2 : Float} (h1 : r1 > 0) (h2 : r2 > 0) :
  resistor_parallel [r1, r2] = resistor_parallel [r2, r1] :=
sorry

theorem inverse_sum_relationship {r : List Float} (h : ∀ x ∈ r, x > 0) :
  1 / (resistor_parallel r) = sum_list (r.map (λ x => 1/x)) :=
sorry
-- </vc-theorems>