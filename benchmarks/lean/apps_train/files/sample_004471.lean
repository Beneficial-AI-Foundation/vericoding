/-
Impliment the reverse function, which takes in input n and reverses it. For instance, `reverse(123)` should return `321`. You should do this without converting the inputted number into a string.
-/

-- <vc-helpers>
-- </vc-helpers>

def String.reverse (s : String) : String := sorry

def reverse (n : Nat) : Nat := sorry

theorem reverse_non_negative (n : Nat) : 
  reverse n ≥ 0 := sorry

theorem reverse_length_leq (n : Nat) :
  n > 0 → n ≤ 10^9 → 
  (toString (reverse n)).length ≤ (toString n).length := sorry

theorem reverse_single_digit (n : Nat) :
  n ≤ 9 → reverse n = n := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible