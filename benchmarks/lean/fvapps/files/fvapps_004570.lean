-- <vc-preamble>
def sorted (s : String) : Bool := 
  let chars := s.data
  chars.zip (chars.drop 1) |>.all (fun (a, b) => a ≤ b)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solved (s : String) : String := sorry

theorem solved_returns_sorted (s : String) :
  sorted (solved s) = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solved_maintains_even_length (s : String) :
  s.length % 2 = 0 → (solved s).length = s.length := sorry

theorem solved_reduces_odd_length (s : String) :
  s.length % 2 = 1 → (solved s).length = s.length - 1 := sorry

theorem solved_maintains_character_set (s : String) :
  ∀ c ∈ (solved s).data, c ∈ s.data := sorry

theorem solved_reduces_char_set_odd (s : String) :
  s.length % 2 = 1 → (solved s).length = s.length - 1 ∧ 
  (∀ c ∈ (solved s).data, c ∈ s.data) := sorry

theorem solved_idempotent (s : String) :
  solved (solved s) = solved s := sorry
-- </vc-theorems>