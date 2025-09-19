-- <vc-preamble>
def isSorted (l : List Char) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findSmallestSubstring (m : Nat) (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_smallest_substring_lowercase (m : Nat) (s : String) :
  let r := findSmallestSubstring m s
  ∀ c ∈ r.data, c.isLower ∨ r = "" :=
sorry

theorem find_smallest_substring_sorted (m : Nat) (s : String) :
  let r := findSmallestSubstring m s
  isSorted r.data ∨ r = "" :=
sorry

theorem find_smallest_substring_length (m : Nat) (s : String) :
  let r := findSmallestSubstring m s
  r.length ≤ s.length :=
sorry

theorem find_smallest_substring_chars_subset (m : Nat) (s : String) :
  let r := findSmallestSubstring m s
  ∀ c ∈ r.data, c ∈ s.data :=
sorry

theorem find_smallest_substring_alternating (m : Nat) :
  let s := "ababab"
  let r := findSmallestSubstring m s
  ∀ c ∈ r.data, c = 'a' ∨ c = 'b' :=
sorry
-- </vc-theorems>