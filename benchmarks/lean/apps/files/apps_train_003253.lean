def word_square (s : String) : Bool := sorry

theorem non_square_length_strings_are_false {s : String} 
  (h : ∃ n : Nat, n * n ≠ s.length) : 
  word_square s = false := sorry

def countChar (c : Char) (s : List Char) : Nat :=
  (s.filter (fun x => x = c)).length

-- <vc-helpers>
-- </vc-helpers>

def count_odd_occurrences (s : String) : Nat :=
  let chars := s.toList
  let counts := chars.map (fun c => countChar c chars)
  (counts.filter (fun n => n % 2 = 1)).length

theorem all_same_letter_square_strings_are_valid (n : Nat) :
  word_square (String.mk (List.replicate (n*n) 'A')) = true := sorry

theorem alternating_letters_within_bounds (n : Nat) (h : n ≥ 2) :
  let letters := List.replicate (n*n) 'A'
  word_square (String.mk letters) = true := sorry

theorem odd_count_characters_within_bounds (s : String) :
  let n := s.length
  if n*n ≠ s.length then
    word_square s = false
  else 
    word_square s = (count_odd_occurrences s ≤ n) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval word_square "SATORAREPOTENETOPERAROTAS"

/-
info: False
-/
-- #guard_msgs in
-- #eval word_square "NOTSQUARE"

/-
info: True
-/
-- #guard_msgs in
-- #eval word_square "CARDAREAREARDART"

-- Apps difficulty: introductory
-- Assurance level: unguarded