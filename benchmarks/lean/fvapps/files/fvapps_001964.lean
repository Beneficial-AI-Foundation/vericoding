-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_string_game (n k : Nat) (strings : List String) : String := sorry

theorem solve_string_game_result_valid (n k : Nat) (strings : List String) 
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : k > 0) (h4 : k ≤ 100) 
  (h5 : strings.length > 0) (h6 : strings.length ≤ 100) :
  solve_string_game n k strings = "First" ∨ solve_string_game n k strings = "Second" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_strings_deterministic (n k : Nat) (strings : List String)
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : k > 0)
  (h4 : strings.length > 0) (h5 : strings.length ≤ 100)
  (h6 : ∀ s ∈ strings, s = "a") :
  solve_string_game n k strings = solve_string_game n k strings := sorry

theorem k_parity_invariant (n k : Nat) (strings : List String)
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : k > 0)
  (h4 : strings.length > 0) (h5 : strings.length ≤ 100) :
  solve_string_game n k strings = solve_string_game n (k + 2) strings := sorry

theorem single_letter_strings_deterministic (n k : Nat) (strings : List String)
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : k > 0)
  (h4 : strings.length > 0) (h5 : strings.length ≤ 100)
  (h6 : ∀ s ∈ strings, s.length = 1) :
  solve_string_game n k strings = "First" ∨ solve_string_game n k strings = "Second" := sorry
-- </vc-theorems>