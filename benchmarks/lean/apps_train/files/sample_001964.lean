/-
Andrew, Fedor and Alex are inventive guys. Now they invent the game with strings for two players.

Given a group of n non-empty strings. During the game two players build the word together, initially the word is empty. The players move in turns. On his step player must add a single letter in the end of the word, the resulting word must be prefix of at least one string from the group. A player loses if he cannot move.

Andrew and Alex decided to play this game k times. The player who is the loser of the i-th game makes the first move in the (i + 1)-th game. Guys decided that the winner of all games is the player who wins the last (k-th) game. Andrew and Alex already started the game. Fedor wants to know who wins the game if both players will play optimally. Help him.

-----Input-----

The first line contains two integers, n and k (1 ≤ n ≤ 10^5; 1 ≤ k ≤ 10^9).

Each of the next n lines contains a single non-empty string from the given group. The total length of all strings from the group doesn't exceed 10^5. Each string of the group consists only of lowercase English letters.

-----Output-----

If the player who moves first wins, print "First", otherwise print "Second" (without the quotes).

-----Examples-----
Input
2 3
a
b

Output
First

Input
3 1
a
b
c

Output
First

Input
1 2
ab

Output
Second
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_string_game (n k : Nat) (strings : List String) : String := sorry

theorem solve_string_game_result_valid (n k : Nat) (strings : List String) 
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : k > 0) (h4 : k ≤ 100) 
  (h5 : strings.length > 0) (h6 : strings.length ≤ 100) :
  solve_string_game n k strings = "First" ∨ solve_string_game n k strings = "Second" := sorry

theorem identical_strings_deterministic (n k : Nat) (strings : List String)
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : k > 0)
  (h4 : strings.length > 0) (h5 : strings.length ≤ 100)
  (h6 : ∀ s ∈ strings, s = "a") :
  solve_string_game n k strings = solve_string_game n k strings := sorry

theorem k_parity_invariant (n k : Nat) (strings : List String)
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : k > 0)
  (h4 : strings.length > 0) (h5 : strings.length ≤ 100) :
  solve_string_game n k strings = solve_string_game n (k + 2) strings := sorry

theorem single_letter_strings_deterministic (n k : Nat) (strings : List String)
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : k > 0)
  (h4 : strings.length > 0) (h5 : strings.length ≤ 100)
  (h6 : ∀ s ∈ strings, s.length = 1) :
  solve_string_game n k strings = "First" ∨ solve_string_game n k strings = "Second" := sorry

-- Apps difficulty: competition
-- Assurance level: guarded