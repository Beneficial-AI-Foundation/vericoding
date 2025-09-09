-- <vc-helpers>
-- </vc-helpers>

def Char.isValidUnicode (c : Char) : Bool := sorry

def letterCount (s : String) : Char → Nat := sorry

theorem letterCount_all_counts_positive {s : String} {c : Char} :
  letterCount s c > 0 → c ∈ s.data := by sorry

theorem letterCount_keys_in_string {s : String} {c : Char} :
  letterCount s c > 0 → c ∈ s.data := by sorry

theorem letterCount_sum_equals_length {s : String} :
  (s.data.foldl (fun acc c => acc + letterCount s c) 0) = s.length := by sorry

theorem letterCount_count_correct {s : String} {c : Char} :
  letterCount s c = (s.data.filter (· = c)).length := by sorry 

theorem letterCount_nonempty_result {s : String} :
  s ≠ "" → ∃ c, letterCount s c > 0 := by sorry

theorem letterCount_valid_chars {s : String} {c : Char} :
  letterCount s c > 0 → Char.isValidUnicode c := by sorry

/-
info: {'a': 1, 'c': 1, 'd': 1, 'e': 1, 'o': 1, 'r': 1, 's': 1, 'w': 1}
-/
-- #guard_msgs in
-- #eval letter_count "codewars"

/-
info: {'a': 1, 'c': 1, 'i': 2, 't': 2, 'v': 1, 'y': 1}
-/
-- #guard_msgs in
-- #eval letter_count "activity"

/-
info: {'a': 1, 'c': 1, 'e': 1, 'h': 1, 'i': 2, 'm': 1, 'r': 1, 's': 1, 't': 2}
-/
-- #guard_msgs in
-- #eval letter_count "arithmetics"

-- Apps difficulty: introductory
-- Assurance level: unguarded