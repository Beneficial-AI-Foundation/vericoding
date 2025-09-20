-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find132pattern (nums : List Int) : Bool :=
  sorry

def has_132_pattern_brute_force (nums : List Int) : Bool :=
  sorry

def isSorted (nums : List Int) (cmp : Int → Int → Bool) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find132pattern_matches_bruteforce {nums : List Int} :
  find132pattern nums = has_132_pattern_brute_force nums :=
sorry

theorem short_sequences_return_false {nums : List Int} :
  List.length nums ≤ 2 → find132pattern nums = false :=
sorry

theorem monotonic_increasing_no_pattern {nums : List Int} :
  isSorted nums (fun x y => x ≤ y) → find132pattern nums = false :=
sorry

theorem monotonic_decreasing_no_pattern {nums : List Int} :
  isSorted nums (fun x y => x ≥ y) → find132pattern nums = false :=
sorry

theorem same_elements_no_pattern {nums : List Int} {x : Int} :
  nums.length ≥ 3 → nums = List.replicate nums.length x → find132pattern nums = false :=
sorry
-- </vc-theorems>