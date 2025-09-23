-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def statsDiscDistr (distrib : List (Int × Float)) : List Float := sorry

theorem valid_distribution_properties
  (distrib : ProbDistr) :
  let result := statsDiscDistr distrib.dist
  -- result is list of length 3
  result.length = 3 ∧
  -- mean, var, std_dev destructuring
  let mean := result[0]!
  let var := result[1]!  
  let std_dev := result[2]!
  -- properties
  var = std_dev * std_dev ∧
  var ≥ 0 ∧
  std_dev ≥ 0 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: [1.5, 0.75, 0.8660254037844386]
-/
-- #guard_msgs in
-- #eval stats_disc_distr [[0, 0.125], [1, 0.375], [2, 0.375], [3, 0.125]]

/-
info: "It's not a valid distribution"
-/
-- #guard_msgs in
-- #eval stats_disc_distr [[0, 0.425], [1, 0.375], [2, 0.375], [3, 0.125]]

/-
info: "It's not a valid distribution and furthermore, one or more variable value are not integers"
-/
-- #guard_msgs in
-- #eval stats_disc_distr [[0.1, 0.425], [1.1, 0.375], [2, 0.375], [3, 0.125]]
-- </vc-theorems>