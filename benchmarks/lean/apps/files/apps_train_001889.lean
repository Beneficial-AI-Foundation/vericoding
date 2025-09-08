/-
S and T are strings composed of lowercase letters. In S, no letter occurs more than once.

S was sorted in some custom order previously. We want to permute the characters of T so that they match the order that S was sorted. More specifically, if x occurs before y in S, then x should occur before y in the returned string.

Return any permutation of T (as a string) that satisfies this property.

Example :
Input: 
S = "cba"
T = "abcd"
Output: "cbad"
Explanation: 
"a", "b", "c" appear in S, so the order of "a", "b", "c" should be "c", "b", and "a". 
Since "d" does not appear in S, it can be at any position in T. "dcba", "cdba", "cbda" are also valid outputs.

Note:

       S has length at most 26, and no character is repeated in S.
       T has length at most 200.
       S and T consist of lowercase letters only.
-/

def List.sort (l : List α) (f : α → α → Bool) : List α :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def custom_sort_string (s t : String) : String :=
  sorry

theorem length_preserved {s t : String} (h : s.length > 0) :
  (custom_sort_string s t).length = t.length :=
sorry

theorem chars_preserved {s t : String} (h : s.length > 0) :
  List.sort (custom_sort_string s t).data (· ≤ ·) = List.sort t.data (· ≤ ·) :=
sorry

theorem single_char_pattern {s t : String} (h1 : s.length = 1) (h2 : t.length > 0) :
  s.get 0 ∈ t.data →
  (custom_sort_string s t).startsWith (String.mk (List.replicate (t.data.count (s.get 0)) (s.get 0))) :=
sorry

theorem idempotent {s t : String} (h : s.length > 0) :
  custom_sort_string s (custom_sort_string s t) = custom_sort_string s t :=
sorry

/-
info: 'kqeep'
-/
-- #guard_msgs in
-- #eval custom_sort_string "kqep" "pekeq"

/-
info: 'zyxw'
-/
-- #guard_msgs in
-- #eval custom_sort_string "abc" "zyxw"

-- Apps difficulty: interview
-- Assurance level: unguarded