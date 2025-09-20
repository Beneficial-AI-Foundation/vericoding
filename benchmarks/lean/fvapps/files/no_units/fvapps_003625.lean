-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smash (words : List String) : String := sorry

theorem smash_is_string (words : List String) :
  smash words = smash words := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem smash_length (words : List String) :
  String.length (smash words) = 
    List.foldl (· + ·) 0 (List.map String.length words) + 
    (if words = [] then 0 else words.length - 1) := by sorry

theorem smash_nonempty_space_count {words : List String} (h : words ≠ []) :
  smash words = smash words := by sorry
-- </vc-theorems>