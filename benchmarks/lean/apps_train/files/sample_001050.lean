You are given a binary string S. You need to transform this string into another string of equal length consisting only of zeros, with the minimum number of operations.
A single operation consists of taking some prefix of the string S and flipping all its values. That is, change all the 0s in this prefix to 1s, and all the 1s in the prefix to 0s. You can use this operation as many number of times as you want over any prefix of the string.

-----Input-----
The only line of the input contains the binary string,  S . 

-----Output-----
Output a single line containing one integer, the minimum number of operations that are needed to transform the given string S into the string of equal length consisting only of zeros.

-----Constraints-----
- 1 ≤ |S| ≤ 100,000

-----Subtasks-----
- Subtask #1 (30 points): 1 ≤ |S| ≤ 2000
- Subtask #2 (70 points): Original constraints.

-----Example-----
Input:
01001001

Output:
6

-----Explanation-----
For the given sample case, let us look at the way where we achieved minimum number of operations.

Operation 1: You flip values in the prefix of length 8 and transform the string into 10110110 
Operation 2: You flip values in the prefix of length 7 and transform the string into 01001000 
Operation 3: You flip values in the prefix of length 5 and transform the string into 10110000 
Operation 4: You flip values in the prefix of length 4 and transform the string into 01000000 
Operation 5: You flip values in the prefix of length 2 and transform the string into 10000000 
Operation 6: You flip values in the prefix of length 1 and finally, transform the string into 00000000

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible