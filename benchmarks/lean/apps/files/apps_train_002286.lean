-- <vc-preamble>
def find_median_binary_string (n m : Nat) (removed : List String) : String := sorry

def isAllZeros (s : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stringInList (s : String) (l : List String) : Bool := sorry

def isBinaryChar (c : Char) : Bool :=
  c = '0' || c = '1'

/- The length of the output string matches the input length m -/
-- </vc-definitions>

-- <vc-theorems>
theorem find_median_binary_string_length_matches_input
  {n m : Nat} {removed : List String}
  (h₁ : n < 2^m)
  (h₂ : n = removed.length) :
  (find_median_binary_string n m removed).length = m := sorry

/- The output string only contains '0' and '1' characters -/

theorem find_median_binary_string_binary_chars
  {n m : Nat} {removed : List String}
  (h₁ : n < 2^m)
  (h₂ : n = removed.length) :
  ∀ c, c ∈ (find_median_binary_string n m removed).data → isBinaryChar c := sorry

/- The output string is not in the list of removed strings -/

theorem find_median_binary_string_not_in_removed
  {n m : Nat} {removed : List String}
  (h₁ : n < 2^m)
  (h₂ : n = removed.length) :
  stringInList (find_median_binary_string n m removed) removed = false := sorry

/- For the minimal case with a single all-zeros string removed,
    the output string has correct length and is not all zeros -/

theorem find_median_binary_string_minimal_case
  {m : Nat} (h : m > 0) :
  let zeros := String.mk (List.replicate m '0')
  let result := find_median_binary_string 1 m [zeros]
  (result.length = m) ∧ (isAllZeros result = false) := sorry

/-
info: '100'
-/
-- #guard_msgs in
-- #eval find_median_binary_string 3 3 ["010", "001", "111"]

/-
info: '010'
-/
-- #guard_msgs in
-- #eval find_median_binary_string 4 3 ["000", "111", "100", "011"]

/-
info: '0'
-/
-- #guard_msgs in
-- #eval find_median_binary_string 1 1 ["1"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded