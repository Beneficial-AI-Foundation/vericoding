/-
The EEE classes are so boring that the students play games rather than paying attention during the lectures. Harsha and Dubey are playing one such game.

The game involves counting the number of anagramic pairs of a given string (you can read about anagrams from here). Right now Harsha is winning. Write a program to help Dubey count this number quickly and win the game!

-----Input-----
The first line has an integer T which is the number of strings. Next T lines each contain a strings. Each string consists of lowercase english alphabets only.

-----Output-----
For each string, print the answer in a newline.

-----Constraints-----
- 1 ≤ T ≤ 1000
- 1 ≤ length of each string ≤ 100

-----Example-----
Input:
3
rama
abba
abcd
Output:
2
4
0

-----Explanation-----
rama has the following substrings:

- r
- ra
- ram
- rama
- a
- am
- ama
- m
- ma
- a
Out of these, {5,10} and {6,9} are anagramic pairs.

Hence the answer is 2.

Similarly for other strings as well.
-/

def find_anagram_pairs (s : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def reverseString (s : String) : String :=
  sorry

theorem find_anagram_pairs_nonneg (s : String) :
  find_anagram_pairs s ≥ 0 := 
  sorry

theorem find_anagram_pairs_empty_or_single (s : String) : 
  s.length ≤ 1 → find_anagram_pairs s = 0 :=
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible