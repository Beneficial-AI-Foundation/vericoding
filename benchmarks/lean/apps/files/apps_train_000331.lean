def simplify_path (s : String) : String := sorry

def is_valid_path_segment (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def splitString (s : String) (c : Char) : List String := sorry

theorem dot_references_resolve 
  {segments : List String}
  (valid_segs : ∀ s ∈ segments, s = "." ∨ s = ".." ∨ is_valid_path_segment s) :
  let path := "/" ++ String.intercalate "/" segments
  let result := simplify_path path
  result.startsWith "/" ∧ "." ∉ splitString result '/'
  := sorry

theorem redundant_slashes
  (slashes : String)
  (h : ∀ c ∈ slashes.toList, c = '/') : 
  simplify_path slashes = "/"
  := sorry

theorem idempotent
  {segments : List String}
  (valid_segs : ∀ s ∈ segments, is_valid_path_segment s) :
  let path := "/" ++ String.intercalate "/" segments
  let once := simplify_path path
  simplify_path once = once
  := sorry

theorem root_path :
  simplify_path "/" = "/"
  := sorry

/-
info: '/home'
-/
-- #guard_msgs in
-- #eval simplify_path "/home/"

/-
info: '/c'
-/
-- #guard_msgs in
-- #eval simplify_path "/a/./b/../../c/"

/-
info: '/home/foo'
-/
-- #guard_msgs in
-- #eval simplify_path "/home//foo/"

-- Apps difficulty: interview
-- Assurance level: unguarded