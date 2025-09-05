Given a string S, consider all duplicated substrings: (contiguous) substrings of S that occur 2 or more times.  (The occurrences may overlap.)
Return any duplicated substring that has the longest possible length.  (If S does not have a duplicated substring, the answer is "".)

Example 1:
Input: "banana"
Output: "ana"

Example 2:
Input: "abcd"
Output: ""

Note:

2 <= S.length <= 10^5
S consists of lowercase English letters.

def longest_dup_substring (s : String) : String := sorry

def isSubstringOf (sub str : String) : Bool := sorry

def countOccurrences (needle haystack : String) (start : Nat) : Nat := sorry

theorem longest_dup_occurs_twice {s : String} (h : s.length > 0) :
  let result := longest_dup_substring s
  if result.length > 0 then
    countOccurrences result s 0 ≥ 2
  else True := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded