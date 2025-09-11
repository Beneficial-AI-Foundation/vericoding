-- <vc-preamble>
def count_anagrams (s : String) : Nat := sorry

def manual_count_anagrams (s : String) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorial (n : Nat) : Nat := sorry

theorem count_anagrams_positive (s : String) (h : s.length > 0) : 
  count_anagrams s ≥ 0 ∧ count_anagrams s < 10^9 + 7 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_anagrams_letter_order_invariant (s : String) (h : s.length > 0) :
  count_anagrams s = count_anagrams s := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_anagrams "ab"

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_anagrams "aa"

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_anagrams "aA"

/-
info: 60
-/
-- #guard_msgs in
-- #eval count_anagrams "AAbaz"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible