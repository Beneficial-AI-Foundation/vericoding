-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def words_to_object (s : String) : String := sorry

theorem empty_string_to_object :
  words_to_object "" = "[]" := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_pairs_object {n : Nat} (h : 0 < n ∧ n ≤ 10) :
  let input := String.join (List.map (fun i => "color" ++ toString i ++ " " ++ toString i ++ " ") (List.range n))
  let result := words_to_object input
  let expected_substring (i : Nat) := "{name : 'color" ++ toString i ++ "', id : '" ++ toString i ++ "'}"
  -- Result has correct brackets
  (result.startsWith "[" ∧ result.endsWith "]") ∧
  -- Each pair exists in result
  (∀ i, i < n → (expected_substring i).all (fun c => result.contains c)) := by sorry
-- </vc-theorems>