Stuart is obsessed to numbers. He like all type of numbers in fact he is having a great collection of numbers in his room. His collection includes N different large numbers. But today he is searching for a number which is having maximum frequency of digit X. Numbers are large so he can’t do the task on his own. Help him to find a number having maximum frequency of digit X.

-----Input-----
First Line contains number of test cases T. First Line of each test case contains N. Next line contains N space separated integers A1,A2,A3,....,AN. Where Ai integer indicates ith number in Stuart's room. Next Line contains digit X.

-----Output-----
Output the number which is having maximum frequency of digit X. If two or more numbers are having same maximum frequency then output the first occurred number among them in A1,A2,A3,....,AN

-----Constraints-----
- 1 ≤ T ≤ 30
- 1 ≤ N ≤ 100
- 1 ≤ Ai ≤ 10200
- 0 ≤ X ≤ 9

-----Example-----
Input:
2
5
345 1323 165 98 456
3
5
335 876 98 1323 349
3

Output:
1323
335

-----Explanation-----
Example case 1. 1323 number is having maximum occurrence of digit 3.
Example case 2. 335 & 1323 are having maximum occurrence of digit 3 so output must be first occurred number in the array i.e. 335.

def countDigit (n : Nat) (d : Nat) : Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
