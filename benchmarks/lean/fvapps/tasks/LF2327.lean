-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_str (haystack : String) (needle : String) : Int :=
  sorry

def containsString (haystack needle : String) : Bool :=
  sorry

def stringSlice (s : String) (start : Int) (last : Int) : String :=
  sorry

def stringRepeat (s : String) (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_needle_returns_zero {haystack : String} :
  find_str haystack "" = 0 := by
sorry

theorem empty_haystack_nonempty_needle_returns_minus_one {needle : String} (h : needle ≠ "") :
  find_str "" needle = -1 := by
sorry

theorem needle_not_found_returns_minus_one {haystack needle : String}
  (h : containsString haystack needle = false) :
  find_str haystack needle = -1 := by
sorry

theorem result_is_valid_index {haystack needle : String}
  (h1 : needle ≠ "") (h2 : containsString haystack needle = true) :
  let r := find_str haystack needle;
  0 ≤ r ∧ r < String.length haystack := by
sorry

theorem result_points_to_needle {haystack needle : String}
  (h1 : needle ≠ "") (h2 : containsString haystack needle = true) :
  let r := find_str haystack needle;
  (stringSlice haystack r (r + String.length needle)) = needle := by
sorry

theorem no_earlier_occurrence {haystack needle : String}
  (h1 : needle ≠ "") (h2 : containsString haystack needle = true) :
  let r := find_str haystack needle;
  containsString (stringSlice haystack 0 r) needle = false := by
sorry

theorem repeated_needle_returns_zero {s : String} {n : Nat}
  (h1 : s ≠ "") (h2 : n > 0) :
  find_str (stringRepeat s n) s = 0 := by
sorry
-- </vc-theorems>