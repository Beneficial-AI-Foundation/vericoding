-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_my_string (s : String) : String := sorry

theorem sort_my_string_preserves_length (s : String) (h : s.length > 0) :
  let result := sort_my_string s
  let result_no_spaces := result.replace " " ""
  result_no_spaces.length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_my_string_splits_even_indexed (s : String) (h : s.length > 0) :
  let result := sort_my_string s
  let parts := result.split (fun x => decide (x = ' '))
  parts.length > 0 → 
  (parts.get? 0).isSome := sorry

theorem sort_my_string_splits_odd_indexed (s : String) (h : s.length > 1) :
  let result := sort_my_string s
  let parts := result.split (fun x => decide (x = ' '))
  parts.length > 1 → 
  (parts.get? 1).isSome := sorry
-- </vc-theorems>