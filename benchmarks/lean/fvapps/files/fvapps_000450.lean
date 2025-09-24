-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arrayNesting (nums : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_nesting_bounds {nums : List Nat} (h : nums.length > 0) :
  let normalized := nums.map (fun x => x % nums.length)
  1 ≤ arrayNesting normalized ∧ arrayNesting normalized ≤ nums.length :=
  sorry

theorem array_nesting_positive {nums : List Nat} (h : nums.length > 0) :
  let normalized := nums.map (fun x => x % nums.length)
  arrayNesting normalized > 0 :=
  sorry

theorem array_nesting_simple_cases :
  arrayNesting [0] = 1 ∧ 
  arrayNesting [1, 0] ≤ 2 ∧
  arrayNesting [0, 1] ≤ 2 :=
  sorry
-- </vc-theorems>