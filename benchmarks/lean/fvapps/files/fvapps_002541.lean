-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def two_sort (strings : List String) : String :=
sorry

def countSubstring (haystack : String) (needle : String) : Nat :=
sorry

def minimum (xs : List String) : String :=
sorry

def splitString (s : String) (sep : String) : List String :=
sorry
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
-- </vc-theorems>