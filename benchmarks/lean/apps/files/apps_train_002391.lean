def String.count (s : String) (c : Char) : Nat := sorry

def countCharacters : List String → String → Nat
  | words, chars => sorry

-- <vc-helpers>
-- </vc-helpers>

def canForm (w : String) (chars : String) : Bool :=
  let check (c : Char) := w.count c ≤ chars.count c
  w.data.all check

theorem count_characters_nonnegative (words : List String) (chars : String) :
  countCharacters words chars ≥ 0 := by sorry

theorem count_characters_bounded_by_total_length (words : List String) (chars : String) :
  countCharacters words chars ≤ (words.map String.length).foldl (· + ·) 0 := by sorry

theorem count_characters_empty_chars (words : List String) :
  countCharacters words "" = 0 := by sorry

theorem count_characters_monotone (words : List String) (chars s : String) :
  countCharacters words (chars ++ s) ≥ countCharacters words chars := by sorry

theorem count_characters_substring_property (words : List String) (chars : String) :
  countCharacters words chars = 
    (List.map String.length 
      (List.filter (fun w => canForm w chars) words)).foldl (· + ·) 0 := by sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval countCharacters ["cat", "bt", "hat", "tree"] "atach"

/-
info: 10
-/
-- #guard_msgs in
-- #eval countCharacters ["hello", "world", "leetcode"] "welldonehoneyr"

/-
info: 8
-/
-- #guard_msgs in
-- #eval countCharacters ["good", "best", "word"] "bestword"

-- Apps difficulty: introductory
-- Assurance level: guarded