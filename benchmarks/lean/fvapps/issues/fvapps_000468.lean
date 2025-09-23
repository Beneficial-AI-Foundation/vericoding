-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def single_number (nums : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_number_minimal (val : Int) :
  val ≥ -1000 → val ≤ 1000 →
  single_number ([val, val, val, val + 1]) = val + 1 :=
sorry

theorem single_number_reorder_invariant (single_val : Int) (others : List Int) :
  single_number (single_val :: (others.map (λ x => [x,x,x])).join) = 
  single_number ((others.map (λ x => [x,x,x])).join ++ [single_val]) :=
sorry

theorem single_number_triple_plus_one (val : Int) :
  val ≥ -1000 → val ≤ 1000 →
  let nums := (List.replicate 3 val) ++ [val + 1]
  (single_number nums = val + 1) ∧ 
  (nums.count (single_number nums) = 1) ∧
  (∀ x, x ∈ nums → x ≠ single_number nums → nums.count x = 3) :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval single_number [2, 2, 3, 2]

/-
info: 99
-/
-- #guard_msgs in
-- #eval single_number [0, 1, 0, 1, 0, 1, 99]

/-
info: 5
-/
-- #guard_msgs in
-- #eval single_number [1, 1, 1, 5]
-- </vc-theorems>