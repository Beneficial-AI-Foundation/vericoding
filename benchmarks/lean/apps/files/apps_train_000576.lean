-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_string_game (s : String) (dict : List String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_output (s : String) (dict : List String) :
  let result := solve_string_game s dict
  result = "Teddy" ∨ result = "Tracy" :=
sorry

theorem empty_dict_tracy (s : String) :
  solve_string_game s [] = "Tracy" :=
sorry

theorem full_string_valid (s : String) :
  let result := solve_string_game s [s]
  result = "Teddy" ∨ result = "Tracy" :=
sorry

theorem single_char_valid :
  let result := solve_string_game "a" ["a"]
  result = "Teddy" ∨ result = "Tracy" :=
sorry

theorem dict_order_invariant : 
  solve_string_game "abcd" ["ab", "cd"] = solve_string_game "abcd" ["cd", "ab"] :=
sorry

/-
info: 'Tracy'
-/
-- #guard_msgs in
-- #eval solve_string_game "codechef" ["code", "chef"]

/-
info: 'Tracy'
-/
-- #guard_msgs in
-- #eval solve_string_game "foo" ["bar"]

/-
info: 'Teddy'
-/
-- #guard_msgs in
-- #eval solve_string_game "mississippi" ["ssissi", "mippi", "mi", "ppi"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded