-- <vc-preamble>
def two_sort (strings : List String) : String := sorry

def countSubstring (haystack : String) (needle : String) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum (xs : List String) : String := sorry 

def splitString (s : String) (sep : String) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem two_sort_separator_count (strings : List String) 
  (h : strings.length > 0) : 
  (countSubstring (two_sort strings) "***") = (minimum strings).length - 1 := 
  sorry

theorem two_sort_recovers_min (strings : List String)
  (h : strings.length > 0) :
  let result := two_sort strings
  let parts := splitString result "***"
  (String.join parts) = minimum strings :=
  sorry

/-
info: 'b***i***t***c***o***i***n'
-/
-- #guard_msgs in
-- #eval two_sort ["bitcoin", "take", "over", "the", "world", "maybe", "who", "knows", "perhaps"]

/-
info: 'a***r***e'
-/
-- #guard_msgs in
-- #eval two_sort ["turns", "out", "random", "test", "cases", "are", "easier", "than", "writing", "out", "basic", "ones"]

/-
info: 'L***e***t***s'
-/
-- #guard_msgs in
-- #eval two_sort ["Lets", "all", "go", "on", "holiday", "somewhere", "very", "cold"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded