-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_odd_char_string (n : Nat) : String := sorry

def String.countChar (s : String) (c : Char) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_matches_input (n : Nat) (h : 0 < n) (h2 : n ≤ 1000) : 
  (generate_odd_char_string n).length = n := sorry

theorem chars_appear_odd_times (n : Nat) (h : 0 < n) (h2 : n ≤ 1000) (c : Char) :
  c ∈ (generate_odd_char_string n).data → 
  (String.countChar (generate_odd_char_string n) c) % 2 = 1 := sorry

theorem uses_valid_chars (n : Nat) (h : 0 < n) (h2 : n ≤ 1000) (c : Char) :
  c ∈ (generate_odd_char_string n).data →
  c = 'a' ∨ c = 'b' ∨ c = 'c' := sorry

theorem single_char_case :
  generate_odd_char_string 1 = "a" := sorry

theorem string_structure (n : Nat) (h : 0 < n) (h2 : n ≤ 1000) :
  (n = 1 → generate_odd_char_string n = "a") ∧
  (n % 2 = 0 → generate_odd_char_string n = String.mk (List.replicate (n-1) 'a' ++ ['b'])) ∧
  (n ≠ 1 ∧ n % 2 = 1 → generate_odd_char_string n = String.mk (List.replicate (n-2) 'a' ++ ['b', 'c'])) := sorry
-- </vc-theorems>