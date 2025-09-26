-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_pattern (k: Nat) : Array String := sorry

theorem solve_pattern_length (k: Nat) (h: k > 0) (h2: k ≤ 100) :
  (solve_pattern k).size = k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_pattern_all_digits (k: Nat) (h: k > 0) (h2: k ≤ 100) (i: Nat) (h3: i < k) :
  let result := solve_pattern k
  result[i]!.all Char.isDigit = true := sorry
-- </vc-theorems>