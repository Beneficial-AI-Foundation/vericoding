/-
Zookeeper is playing a game. In this game, Zookeeper must use bombs to bomb a string that consists of letters 'A' and 'B'. He can use bombs to bomb a substring which is either "AB" or "BB". When he bombs such a substring, the substring gets deleted from the string and the remaining parts of the string get concatenated.

For example, Zookeeper can use two such operations: AABABBA $\to$ AABBA $\to$ AAA.

Zookeeper wonders what the shortest string he can make is. Can you help him find the length of the shortest string?

-----Input-----

Each test contains multiple test cases. The first line contains a single integer $t$ $(1 \leq t \leq 20000)$  — the number of test cases. The description of the test cases follows.

Each of the next $t$ lines contains a single test case each, consisting of a non-empty string $s$: the string that Zookeeper needs to bomb. It is guaranteed that all symbols of $s$ are either 'A' or 'B'.

It is guaranteed that the sum of $|s|$ (length of $s$) among all test cases does not exceed $2 \cdot 10^5$.

-----Output-----

For each test case, print a single integer: the length of the shortest string that Zookeeper can make.

-----Example-----
Input
3
AAA
BABA
AABBBABBBB

Output
3
2
0

-----Note-----

For the first test case, you can't make any moves, so the answer is $3$.

For the second test case, one optimal sequence of moves is BABA $\to$ BA. So, the answer is $2$.

For the third test case, one optimal sequence of moves is AABBBABBBB $\to$ AABBBABB $\to$ AABBBB $\to$ ABBB $\to$ AB $\to$ (empty string). So, the answer is $0$.
-/

-- <vc-helpers>
-- </vc-helpers>

def get_shortest_string_length (s : String) : Nat := sorry

theorem shortest_length_non_negative (s : String) : 
  get_shortest_string_length s ≥ 0 := sorry

theorem shortest_length_at_most_input (s : String) :
  get_shortest_string_length s ≤ String.length s := sorry

theorem AB_reduces_length (s : String) (i : Nat) :
  i + 1 < s.length →
  (h1 : i < s.length) →
  (h2 : i + 1 < s.length) →
  s.data[i]'h1 = 'A' →
  s.data[i + 1]'h2 = 'B' →
  get_shortest_string_length s < String.length s := sorry

theorem BB_reduces_length (s : String) (i : Nat) :
  i + 1 < s.length →
  (h1 : i < s.length) →
  (h2 : i + 1 < s.length) →
  s.data[i]'h1 = 'B' →
  s.data[i + 1]'h2 = 'B' →
  get_shortest_string_length s < String.length s := sorry

theorem repeated_B_reduces_to_zero_or_one (n : Nat) :
  let s := String.mk (List.replicate n 'B')
  get_shortest_string_length s = 0 ∨ get_shortest_string_length s = 1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval get_shortest_string_length "AAA"

/-
info: 2
-/
-- #guard_msgs in
-- #eval get_shortest_string_length "BABA"

/-
info: 0
-/
-- #guard_msgs in
-- #eval get_shortest_string_length "AABBBABBBB"

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible