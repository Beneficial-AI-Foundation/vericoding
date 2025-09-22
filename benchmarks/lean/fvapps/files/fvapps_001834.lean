-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def moves_to_stamp (stamp : String) (target : String) : List Nat := sorry

theorem moves_to_stamp_single_stamp
  (stamp : String)
  (h₁ : stamp.length > 0)
  (h₂ : ∀ c ∈ stamp.data, c = 'a' ∨ c = 'b' ∨ c = 'c') :
  moves_to_stamp stamp stamp = [0] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem moves_to_stamp_basic_cases_1 :
  moves_to_stamp "abc" "ababc" = [0, 2] ∨ moves_to_stamp "abc" "ababc" = [1, 0, 2] := sorry

theorem moves_to_stamp_basic_cases_2 :
  moves_to_stamp "abca" "aabcaca" = [3, 0, 1] := sorry

theorem moves_to_stamp_impossible_cases_1 :
  moves_to_stamp "abc" "xyz" = [] := sorry

theorem moves_to_stamp_impossible_cases_2 :
  moves_to_stamp "abc" "ab" = [] := sorry

theorem moves_to_stamp_impossible_cases_3 :
  moves_to_stamp "abc" "abcd" = [] := sorry
-- </vc-theorems>