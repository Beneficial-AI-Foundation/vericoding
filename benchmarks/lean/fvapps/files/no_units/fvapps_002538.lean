-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cat_mouse (s : String) (jump_dist : Nat) : String := sorry

def findPos (s : String) (c : Char) : Nat :=
  String.length (s.takeWhile (· ≠ c))
-- </vc-definitions>

-- <vc-theorems>
theorem output_always_valid (s : String) (jump_dist : Nat) : 
  cat_mouse s jump_dist = "Caught!" ∨ 
  cat_mouse s jump_dist = "Escaped!" ∨ 
  cat_mouse s jump_dist = "Protected!" ∨
  cat_mouse s jump_dist = "boring without all three" := sorry

theorem valid_game_string_output (s : String) (jump_dist : Nat) 
  (h1 : s.contains 'C')
  (h2 : s.contains 'D')  
  (h3 : s.contains 'm') :
  cat_mouse s jump_dist = "Caught!" ∨
  cat_mouse s jump_dist = "Escaped!" ∨
  cat_mouse s jump_dist = "Protected!" := sorry

theorem distance_property (s : String) (jump_dist : Nat)
  (h1 : s.contains 'C')
  (h2 : s.contains 'D')
  (h3 : s.contains 'm') :
  let c := findPos s 'C'
  let d := findPos s 'D'
  let m := findPos s 'm'
  (if c ≤ m then
    if m - c ≤ jump_dist then
      if c < d ∧ d < m then
        cat_mouse s jump_dist = "Protected!"
      else
        cat_mouse s jump_dist = "Caught!"
    else
      cat_mouse s jump_dist = "Escaped!"
  else
    if c - m ≤ jump_dist then
      if m < d ∧ d < c then
        cat_mouse s jump_dist = "Protected!"
      else
        cat_mouse s jump_dist = "Caught!"
    else
      cat_mouse s jump_dist = "Escaped!") := sorry

theorem missing_chars (s : String) :
  ¬(s.contains 'C' ∧ s.contains 'D' ∧ s.contains 'm') →
  cat_mouse s 5 = "boring without all three" := sorry
-- </vc-theorems>