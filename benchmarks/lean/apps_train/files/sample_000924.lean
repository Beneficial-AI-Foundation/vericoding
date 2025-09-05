Chef has a string of size $N$ which consists only lowercase English alphabet. The chef doesn't like the consonant alphabet at all. So he is thinking of changing every single consonant alphabet to any vowel alphabet. There is some cost for performing this operation.
- Number all alphabet [a,b,c,……,z] as [1,2,3,…..,26]
- So if you want to change c to e then cost will be |e-c| = |5-3| = 2
You need the answer at what minimum cost chef can change every single consonant alphabet to any vowel alphabet. 

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains of a single line of input, a string of lowercase alphabet. 

-----Output:-----
For each test case, output in a single line answer.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq |s| \leq 10^2$

-----Sample Input:-----
2
aeiou
dbcc  

-----Sample Output:-----
0
6

-----EXPLANATION:-----
In the first test case, all characters are already vowel so we don't need to change.
In the second tect case
|e-d|=|5-4|=1
|a-b|=|1-2|=1
|a-c|=|1-3|=2
|a-c|=|1-3|=2
1+1+2+2=6

def isVowel (c : Char) : Bool := 
  c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u'

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
