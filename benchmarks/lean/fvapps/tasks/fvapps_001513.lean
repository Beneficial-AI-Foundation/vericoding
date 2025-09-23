-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSubstring (sub : String) (orig : String) : Bool :=
sorry

def hasAllChars (sub : String) (orig : String) : Bool :=
sorry

def substr (s : String) (i j : Nat) : String :=
sorry

def findSubString (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_sub_string_is_substring
  (s : String) (h : s.length > 0) :
  isSubstring (findSubString s) s :=
sorry

theorem find_sub_string_has_all_chars
  (s : String) (h : s.length > 0) :
  hasAllChars (findSubString s) s :=
sorry

theorem find_sub_string_is_minimal
  (s : String) (h : s.length > 0)
  (i j : Nat) (h1 : i < s.length) (h2 : j ≤ s.length) (h3 : i < j) :
  let sub := substr s i j
  let result := findSubString s
  sub.length < result.length → ¬(hasAllChars sub s) :=
sorry
-- </vc-theorems>