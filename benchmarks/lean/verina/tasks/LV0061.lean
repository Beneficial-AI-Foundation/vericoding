-- <vc-preamble>
@[reducible]
def rain_precond (heights : List (Int)) : Prop :=
  heights.all (fun h => h >= 0)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rain (heights : List (Int)) (h_precond : rain_precond (heights)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def rain_postcond (heights : List (Int)) (result: Int) (h_precond : rain_precond (heights)) : Prop :=
  -- The result is the total amount of rainwater trapped by the given terrain
  -- If there are fewer than 3 elements, no water can be trapped
  result >= 0 ∧
  -- The result is non-negative
  if heights.length < 3 then result = 0 else
    -- Water trapped at each position is min(maxLeft, maxRight) - height
    result =
      let max_left_at := λ i =>
        let rec ml (j : Nat) (max_so_far : Int) : Int :=
          if j > i then max_so_far
          else ml (j+1) (max max_so_far (heights[j]!))
          termination_by i + 1 - j
        ml 0 0

      let max_right_at := λ i =>
        let rec mr (j : Nat) (max_so_far : Int) : Int :=
          if j >= heights.length then max_so_far
          else mr (j+1) (max max_so_far (heights[j]!))
          termination_by heights.length - j
        mr i 0

      let water_at := λ i =>
        max 0 (min (max_left_at i) (max_right_at i) - heights[i]!)

      let rec sum_water (i : Nat) (acc : Int) : Int :=
        if i >= heights.length then acc
        else sum_water (i+1) (acc + water_at i)
        termination_by heights.length - i

      sum_water 0 0

theorem rain_spec_satisfied (heights: List (Int)) (h_precond : rain_precond (heights)) :
    rain_postcond (heights) (rain (heights) h_precond) h_precond := by
  sorry
-- </vc-theorems>