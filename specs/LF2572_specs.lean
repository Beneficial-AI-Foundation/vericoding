-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_integers (m n : Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem generate_integers_property (m n : Int) 
  (h : m ≤ n) :
  let result := generate_integers m n
  (result ≠ []) ∧ 
  (result.length = n - m + 1) ∧
  (result.head! = m) ∧
  (result.getLast! = n) ∧
  (∀ i, i < result.length - 1 → result[i+1]! - result[i]! = 1) :=
  sorry

theorem generate_integers_same_number (n : Int) :
  generate_integers n n = [n] :=
  sorry
-- </vc-theorems>