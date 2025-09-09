def multiple_split (s : String) (delims : List String) : List String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def containsString (s : String) (sub : String) : Bool :=
  sorry

theorem multiple_split_nonempty_parts
  (s : String) (delims : List String)
  : ∀ (x : String), x ∈ multiple_split s delims → x.length > 0
  := by sorry

theorem multiple_split_no_delims_in_result
  (s : String) (delims : List String)
  : ∀ (x : String) (d : String), 
    x ∈ multiple_split s delims → 
    d ∈ delims → 
    ¬ containsString x d
  := by sorry

theorem multiple_split_empty_string
  (delims : List String)
  : multiple_split "" delims = []
  := by sorry

theorem multiple_split_empty_delims
  (s : String)
  : multiple_split s [] = if s = "" then [] else [s]
  := by sorry

theorem multiple_split_single_delim
  (s : String) (delim : String)
  (h : delim.length > 0)
  : multiple_split s [delim] = (s.split (· == '.')).filter (fun x => x ≠ "") -- placeholder split
  := by sorry

/-
info: ['Hi', 'everybody']
-/
-- #guard_msgs in
-- #eval multiple_split "Hi everybody!" [" ", "!"]

/-
info: ['1', '2', '3']
-/
-- #guard_msgs in
-- #eval multiple_split "1+2-3" ["+", "-"]

/-
info: []
-/
-- #guard_msgs in
-- #eval multiple_split "" []

-- Apps difficulty: introductory
-- Assurance level: unguarded