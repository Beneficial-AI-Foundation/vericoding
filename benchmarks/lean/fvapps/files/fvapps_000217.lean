-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_dup_substring (s : String) : String :=
sorry

def isSubstringOf (sub str : String) : Bool :=
sorry

def countOccurrences (needle haystack : String) (start : Nat) : Nat :=
sorry

def hasLongerDuplicate (s : String) (len : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longest_dup_occurs_twice {s : String} (h : s.length > 0) :
  let result := longest_dup_substring s
  if result.length > 0 then
    countOccurrences result s 0 ≥ 2
  else True :=
sorry

theorem no_longer_duplicate_exists {s : String} (h : s.length > 0) :
  let result := longest_dup_substring s
  ∀ len, len > result.length →
  hasLongerDuplicate s len = false :=
sorry

theorem longest_dup_is_substring {s : String} (h : s.length > 0) :
  let result := longest_dup_substring s
  isSubstringOf result s = true :=
sorry
-- </vc-theorems>