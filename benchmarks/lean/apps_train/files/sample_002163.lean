/-
You are given a string S consisting of a,b and c. Find the number of strings that can be possibly obtained by repeatedly performing the following operation zero or more times, modulo 998244353:
 - Choose an integer i such that 1\leq i\leq |S|-1 and the i-th and (i+1)-th characters in S are different. Replace each of the i-th and (i+1)-th characters in S with the character that differs from both of them (among a, b and c).

-----Constraints-----
 - 2 \leq |S| \leq 2 × 10^5
 - S consists of a, b and c.

-----Input-----
Input is given from Standard Input in the following format:
S

-----Output-----
Print the number of strings that can be possibly obtained by repeatedly performing the operation, modulo 998244353.

-----Sample Input-----
abc

-----Sample Output-----
3

abc, aaa and ccc can be obtained.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_abc_strings (s : String) : Nat :=
  sorry

theorem output_range (s : String) 
  (h : ∀ c ∈ s.data, c = 'a' ∨ c = 'b' ∨ c = 'c') 
  (h2 : s ≠ "") : 
  let result := solve_abc_strings s
  0 ≤ result ∧ result < 998244353 := sorry

theorem single_char_repeated (n : Nat) (c : Char)
  (h : c = 'a' ∨ c = 'b' ∨ c = 'c')
  (h2 : n > 0) :
  solve_abc_strings (String.mk (List.replicate n c)) = 1 := sorry

theorem alternating_pattern (n : Nat)
  (h : n > 0) :
  solve_abc_strings (String.mk (List.join (List.replicate n ['a', 'b']))) ≠ 1 ∧
  solve_abc_strings (String.mk (List.join (List.replicate n ['b', 'c']))) ≠ 1 ∧ 
  solve_abc_strings (String.mk (List.join (List.replicate n ['a', 'c']))) ≠ 1 := sorry

theorem empty_string :
  solve_abc_strings "" = 0 := sorry

theorem single_char (c : Char)
  (h : c = 'a' ∨ c = 'b' ∨ c = 'c') :
  solve_abc_strings (String.mk [c]) = 1 := sorry

theorem valid_chars (s : String) :
  ∀ c ∈ s.data, c = 'a' ∨ c = 'b' ∨ c = 'c' := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_abc_strings "abc"

/-
info: 65
-/
-- #guard_msgs in
-- #eval solve_abc_strings "abbac"

/-
info: 6310
-/
-- #guard_msgs in
-- #eval solve_abc_strings "babacabac"

-- Apps difficulty: competition
-- Assurance level: unguarded