Given a string consisting of only lowercase English alphabets, your task is to find the smallest palindromic substring.
In case there are multiple palindromic substrings of the same length present, print the lexicographically smallest substring. 
Formally, a substring is a contiguous sequence of characters within a string. So in a string "abcdef", "abc" is a substring whereas "adf" is not a substring.
A palindrome is a word, phrase, or sequence that reads the same backwards as forwards, e.g. madam or mom.

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains of two lines of input, two integers.
- First, we have a single integer $N$ which signifies the length of the substring.
- Next, we have a string of length $N$ that only has lowercase English alphabets.

-----Output:-----
For each testcase, output in a single line the shortest palindromic substring.

-----Constraints-----
- $1 \leq T \leq 100$
- $2 \leq N \leq 10^5$

-----Sample Input:-----
2
2
zy
1
cd

-----Sample Output:-----
y
c

-----EXPLANATION:-----
There are only two possibilities. "z" and "y". Since both of them have the same length. We print the lexicographically smaller substring which is y.

def find_smallest_palindrome (len: Nat) (s: String) : String := sorry

theorem find_smallest_palindrome_result_length 
  (len: Nat) (s: String) (h₁: len > 0) (h₂: s.length > 0) :
  (find_smallest_palindrome len s).length = 1 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
