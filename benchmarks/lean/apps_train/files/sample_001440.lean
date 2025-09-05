Devu is a disastrous oracle: his predictions about various events of your life are horrifying. Instead of providing good luck, he "blesses" you with bad luck. The secret behind his wickedness is a hidden omen which is a string of length m. On your visit to him, you can ask a lot of questions about your future, each of which should be a string of length m. In total you asked him n such questions, denoted by strings s1, s2, ... , sn of length m each. Each of the question strings is composed of the characters 'a' and 'b' only.

Amount of bad luck this visit will bring you is equal to the length of longest common subsequence (LCS) of all the question strings and the hidden omen string. Of course, as the omen string is hidden, you are wondering what could be the least value of bad luck you can get.

Can you find out what could be the least bad luck you can get? Find it fast, before Devu tells you any bad omens.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
First line of each test case contains a single integer n denoting number of strings.
For each of next n lines, the ith line contains the string si.

-----Output-----
For each test case, output a single integer corresponding to the answer of the problem. 

-----Constraints-----
- All the strings (including the hidden omen) contain the characters 'a' and 'b' only.

Subtask #1: (40 points) 

- 1 ≤ T, n, m ≤ 14

Subtask #2: (60 points) 

- 1 ≤ T, n, m ≤ 100

-----Example-----
Input:3
2
ab
ba
2
aa
bb
3
aabb
abab
baab

Output:1
0
2

-----Explanation-----
In the first example, the minimum value of LCS of all the strings is 1, the string by oracle can be one of these {aa, ab, ba, bb}. 

In the second example, whatever string oracle has does not matter, LCS will always be zero.

def find_min_bad_luck (strings : List String) : Nat := sorry

theorem find_min_bad_luck_non_negative (strings : List String) :
  find_min_bad_luck strings ≥ 0 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible