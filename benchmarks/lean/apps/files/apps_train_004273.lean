-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def endlessString (s : String) (start length : Int) : String := sorry

theorem endless_string_length
  (s : String)
  (start : Int)
  (length : Int)
  (h : length ≠ 0) :
  (endlessString s start length).length = Int.natAbs length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem endless_string_chars_subset
  (s : String)
  (start : Int)
  (length : Int)
  (h : length ≠ 0) :
  ∀ c, c ∈ (endlessString s start length).data → c ∈ s.data := sorry

theorem endless_string_start_period
  (s : String)
  (start : Int)
  (length : Int)
  (h : length > 0) :
  endlessString s start length = endlessString s (start + s.length) length := sorry

/-
info: 'yzxyzx'
-/
-- #guard_msgs in
-- #eval endless_string "xyz" -23 6

/-
info: 'xyzx'
-/
-- #guard_msgs in
-- #eval endless_string "xyz" 0 4

/-
info: 'zxyz'
-/
-- #guard_msgs in
-- #eval endless_string "xyz" -4 -4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded