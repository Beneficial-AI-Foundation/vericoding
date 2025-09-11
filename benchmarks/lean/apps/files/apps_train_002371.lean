-- <vc-preamble>
def repeatedSubstringPattern (s: String) : Bool := sorry

theorem repeatedSubstringPattern_single_char {s: String} :
  s.length = 1 → ¬repeatedSubstringPattern s := sorry

def rotateString (s: String) : String := sorry

theorem repeatedSubstringPattern_rotation {s: String} (h: s.length ≥ 2) :
  repeatedSubstringPattern s → 
  repeatedSubstringPattern (rotateString s) := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrime (n: Nat) : Bool := sorry

def allCharsSame (s: String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeatedSubstringPattern_doubled {s: String} (h: s.length > 0) :
  repeatedSubstringPattern (s ++ s) := sorry  

theorem repeatedSubstringPattern_n_times {s: String} (n: Nat) 
    (h1: s.length > 0) (h2: n ≥ 3) (h3: n ≤ 10) :
  repeatedSubstringPattern (String.append s (String.append s s)) := sorry

theorem repeatedSubstringPattern_prime_length {s: String} (h1: s.length > 1) :
  isPrime s.length →
  ¬allCharsSame s →
  ¬repeatedSubstringPattern s := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval repeatedSubstringPattern "abab"

/-
info: False
-/
-- #guard_msgs in
-- #eval repeatedSubstringPattern "aba"

/-
info: True
-/
-- #guard_msgs in
-- #eval repeatedSubstringPattern "abcabcabcabc"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded