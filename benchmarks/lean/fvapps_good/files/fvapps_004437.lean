-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : Array Nat := sorry

theorem solve_returns_four_nonnegative : ∀ s : String,
  let result := solve s
  (result.size = 4) ∧ 
  (∀ i, i < result.size → 0 ≤ result[i]!) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_categorizes_correctly : ∀ s : String,
  let result := solve s;
  result.size = 4 ∧
  (result[0]! = (s.data.filter Char.isUpper).length) ∧
  (result[1]! = (s.data.filter Char.isLower).length) ∧
  (result[2]! = (s.data.filter Char.isDigit).length) ∧
  (result[3]! = (s.data.filter (fun c => !(Char.isAlphanum c))).length) := sorry

theorem solve_all_uppercase : ∀ s : String,
  s.data.all Char.isUpper →
  let result := solve s;
  result.size = 4 ∧
  (result[0]! = s.length) ∧
  (result[1]! = 0) ∧
  (result[2]! = 0) ∧
  (result[3]! = 0) := sorry

theorem solve_all_lowercase : ∀ s : String,
  s.data.all Char.isLower →
  let result := solve s;
  result.size = 4 ∧
  (result[0]! = 0) ∧
  (result[1]! = s.length) ∧
  (result[2]! = 0) ∧
  (result[3]! = 0) := sorry

theorem solve_all_numbers : ∀ s : String,
  s.data.all Char.isDigit →
  let result := solve s;
  result.size = 4 ∧
  (result[0]! = 0) ∧
  (result[1]! = 0) ∧
  (result[2]! = s.length) ∧
  (result[3]! = 0) := sorry
-- </vc-theorems>