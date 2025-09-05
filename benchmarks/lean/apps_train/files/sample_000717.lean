Gargi is thinking of a solution to a problem. Meanwhile, her friend asks her to solve another problem. Since Gargi is busy in her own problem, she seeks your help to solve the new problem.

You are given a string S containing characters a-z (lower case letters) only. You need to change the string to a new string consisting of only one letter from a-z.

For a given character S[i] in the string, if you change it to a character having lower ASCII value than the character S[i], you gain points equal to the difference in ASCII value of the old character and the new character. Similarly, for a given character S[j] in the string, if you change it to a character having higher ASCII value than the character S[j], you lose points equal to the difference in ASCII value of the old character and the new character.

However, Gargi does not like gaining or losing points. She has asked you to change the string in such a way that the total losing or gaining of points at the end of the string conversion is minimum.

Give Gargi the absolute value of the points you have at the end of the string conversion.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.

The first line of each of the T test case contains a string S containing only lower case characters (a-z)

-----Output-----
For each test case, output a single line containing the answer.

-----Constraints-----
- 1 ≤ T ≤ 10
- 1 ≤ |S| ≤ 100000

-----Example-----
Input:
1
abba

Output:
2

-----Explanation-----
Example case 1. The new string can be aaaa where you have +2 points at the end of string conversion or it can be bbbb where you have -2 points at the end of string conversion. Hence the output is 2.

def minPointsForStringConversion (s : String) : Nat := sorry

theorem minPoints_nonNegative (s : String) (h : s.length > 0) : 
  minPointsForStringConversion s ≥ 0 := sorry

def allSameChar (s : String) : Bool := sorry 

theorem minPoints_zero_for_same_chars (s : String) (h1 : s.length > 0) (h2 : allSameChar s = true) :
  minPointsForStringConversion s = 0 := sorry

def minCharOfString (s : String) : Char := sorry
def maxCharOfString (s : String) : Char := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
