-- <vc-helpers>
-- </vc-helpers>

def lengthLongestPath (input : String) : Nat :=
  sorry

theorem root_level_file_or_dir
  (name : String)
  (h_nonempty : name.length > 0) :
  if name.contains '.' then
    lengthLongestPath name = name.length 
  else 
    lengthLongestPath name = 0 :=
sorry

/-
info: 20
-/
-- #guard_msgs in
-- #eval lengthLongestPath "dir\n\tsubdir1\n\tsubdir2\n\t\tfile.ext"

/-
info: 32
-/
-- #guard_msgs in
-- #eval lengthLongestPath "dir\n\tsubdir1\n\t\tfile1.ext\n\t\tsubsubdir1\n\tsubdir2\n\t\tsubsubdir2\n\t\t\tfile2.ext"

/-
info: 0
-/
-- #guard_msgs in
-- #eval lengthLongestPath ""

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible