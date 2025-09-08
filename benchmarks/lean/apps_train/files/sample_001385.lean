/-
Harrenhal is the largest castle in the Seven Kingdoms and is the seat of House Whent in the Riverlands, on the north shore of the Gods Eye lake. Since the War of Conquest, however, it has become a dark and ruinous place.
(c) A Wiki of Ice and Fire

Now Harrenhal is too dangerous since it's a nice place for bandits to hide, or even for rebels to start planning overthrowing of the king. So, the current Lord of the Seven Kingdoms has decided, that it's time to completely ruin the castle. For that puposes, he's planning to send some military troops.
In this problem we assume, that Harrenhal can be described as a string H, which consists only of symbols 'a' and 'b'. Harrenhal is completely ruined if and only if the length of H is equal to zero.
So, how to make H empty? Send a military troop! When a military troop of the king reach the castle, they delete some palindromic subsequence S of H. For example, let H = 'abbabaab'. Then the current military troop can choose S = 'ababa'(Let's make symbols of S bold in H: 'abbabaab'). After deleting S, H will be equal to 'bab'. Military troops are free to choose any possible palindromic subsequence of H.
Your task is pretty simple: determine the minimal number of military troops, that the Lord of the Seven Kingdoms has to send in order to ruin Harrenhal.

-----Note-----

Maybe, some of you aren't familiar with definitions from the statement. Here're some articles that could help you to understand the problem correctly:

- Subsequence: http://en.wikipedia.org/wiki/Subsequence
- Palindrome: http://en.wikipedia.org/wiki/Palindrome

-----Input-----
The first line of the input contains an integer T, denoting the number of test cases.
The next T lines contain a string H each, denoting the string, that describes the current state of Harrenhal for the corresponding test cases.
It's guaranteed, that each H consists only of symbols 'a' and 'b'.

-----Output-----
The output should contain exactly T lines. i'th line of the output should contain the only integer: the minimal number of military troops, that the Lord of the Seven Kingdoms has to send in order to ruin Harrenhal for the corresponding test cases.

-----Constraints-----
- 1 ≤ |H| ≤ 100000, for each H.
- Subtask 1(30 points): each H in the input is a palindrome, 1 ≤ T ≤ 6;
- Subtask 2(70 points): 1 ≤ T ≤ 9.

-----Example-----
Input:
1
abbabaab

Output:
2

-----Explanation-----
There're multiple ways to ruin Harrenhal in the example test. Let's consider one of them.
The first troop can delete S = 'ababa'('abbabaab'). After that, H = 'bab'.
The second troop can delete S = 'bab'('bab'). After that, H is empty and that's it.
-/

def find_min_troops_to_ruin (s: String) : Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def isPalindrome (s: String) : Bool :=
sorry

theorem min_troops_bounds (s: String) :
  let result := find_min_troops_to_ruin s
  0 ≤ result ∧ result ≤ 2 :=
sorry

theorem empty_string_troops (s: String) :
  s = "" → find_min_troops_to_ruin s = 0 :=
sorry

theorem palindrome_troops (s: String) :
  s ≠ "" ∧ isPalindrome s → find_min_troops_to_ruin s = 1 :=
sorry

theorem non_palindrome_troops (s: String) :
  s ≠ "" ∧ ¬isPalindrome s → find_min_troops_to_ruin s = 2 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_troops_to_ruin "abbabaab"

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_min_troops_to_ruin "abba"

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_troops_to_ruin "ab"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible