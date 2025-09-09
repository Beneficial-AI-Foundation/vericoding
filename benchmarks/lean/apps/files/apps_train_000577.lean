-- <vc-helpers>
-- </vc-helpers>

def get_pangram_cost (prices : List Nat) (text : String) : Nat := sorry

theorem pangram_cost_nonnegative (prices : List Nat) (text : String) 
    (h : prices.length = 26) : 
  get_pangram_cost prices text ≥ 0 := sorry

theorem pangram_cost_empty_string (prices : List Nat)
    (h : prices.length = 26) :
  get_pangram_cost prices "" = prices.foldl (·+·) 0 := sorry

/-
info: 63
-/
-- #guard_msgs in
-- #eval get_pangram_cost [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26] "abcdefghijklmopqrstuvwz"

/-
info: 0
-/
-- #guard_msgs in
-- #eval get_pangram_cost [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26] "thequickbrownfoxjumpsoverthelazydog"

/-
info: 25
-/
-- #guard_msgs in
-- #eval get_pangram_cost [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] "a"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible