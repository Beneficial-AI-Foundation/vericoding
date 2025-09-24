-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_road_cost (n : Nat) (populations : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_road_cost_non_negative 
  {n : Nat} {populations : List Nat}
  (h1 : n = populations.length)
  (h2 : n ≥ 2)
  (h3 : ∀ x ∈ populations, 1 ≤ x ∧ x ≤ 1000) :
  min_road_cost n populations ≥ 0 :=
sorry

theorem min_road_cost_symmetric
  {n : Nat} {populations : List Nat}
  (h1 : n = populations.length)
  (h2 : n ≥ 2)
  (h3 : ∀ x ∈ populations, 1 ≤ x ∧ x ≤ 1000) :
  min_road_cost n populations = min_road_cost n populations.reverse :=
sorry

theorem min_road_cost_formula
  {n : Nat} {populations : List Nat}
  (h1 : n = populations.length)
  (h2 : n ≥ 2)
  (h3 : ∀ x ∈ populations, 1 ≤ x ∧ x ≤ 1000)
  (min max : Nat)
  (hmin : min ∈ populations)
  (hmax : max ∈ populations)
  (hmin_least : ∀ x ∈ populations, min ≤ x)
  (hmax_most : ∀ x ∈ populations, x ≤ max) :
  let total := populations.foldl (· + ·) 0
  min_road_cost n populations ≤ min * (total - min) ∧
  min_road_cost n populations ≤ max * (total - max) :=
sorry
-- </vc-theorems>