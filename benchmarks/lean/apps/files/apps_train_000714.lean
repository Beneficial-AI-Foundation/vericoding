-- <vc-preamble>
def find_smallest_palindrome (len: Nat) (s: String) : String := sorry

theorem find_smallest_palindrome_result_length 
  (len: Nat) (s: String) (h₁: len > 0) (h₂: s.length > 0) :
  (find_smallest_palindrome len s).length = 1 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lexMin (s: String) : String :=
  s.data.foldl (fun acc c => if c < acc.get! 0 then String.mk [c] else acc) (String.mk [s.get! 0])
-- </vc-definitions>

-- <vc-theorems>
theorem find_smallest_palindrome_in_original 
  (len: Nat) (s: String) (h₁: len > 0) (h₂: s.length > 0) :
  s.contains ((find_smallest_palindrome len s).get! 0) = true := sorry 

theorem find_smallest_palindrome_lexmin 
  (len: Nat) (s: String) (h₁: len > 0) (h₂: s.length > 0) :
  find_smallest_palindrome len s = lexMin s := sorry

/-
info: 'y'
-/
-- #guard_msgs in
-- #eval find_smallest_palindrome 2 "zy"

/-
info: 'c'
-/
-- #guard_msgs in
-- #eval find_smallest_palindrome 1 "cd"

/-
info: 'm'
-/
-- #guard_msgs in
-- #eval find_smallest_palindrome 3 "mom"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded