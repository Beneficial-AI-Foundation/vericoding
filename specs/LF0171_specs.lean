-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lengthLongestPath (input : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem root_level_file_or_dir
  (name : String)
  (h_nonempty : name.length > 0) :
  if name.contains '.' then
    lengthLongestPath name = name.length 
  else 
    lengthLongestPath name = 0 :=
sorry
-- </vc-theorems>