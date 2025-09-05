The Head Chef is receiving a lot of orders for cooking the best of the problems lately. For this, he organized an hiring event to hire some talented Chefs. He gave the following problem to test the skills of the participating Chefs. Can you solve this problem and be eligible for getting hired by Head Chef.

A non-negative number n is said to be magical if it satisfies the following property. Let S denote the multi-set of numbers corresponding to the non-empty subsequences of the digits of the number n in decimal representation. Please note that the numbers in the set S can have leading zeros. Let us take an element s of the multi-set S, prod(s) denotes the product of all the digits of number s in decimal representation. 
The number n will be called magical if sum of prod(s) for all elements s in S, is even. 

For example, consider a number 246, its all possible non-empty subsequence will be S = {2, 4, 6, 24, 46, 26, 246}. Products of digits of these subsequences will be {prod(2) = 2, prod(4) = 4, prod(6) = 6, prod(24) = 8, prod(46) = 24, prod(26) = 12, prod(246) = 48, i.e. {2, 4, 6, 8, 24, 12, 48}. Sum of all of these is 104, which is even. Hence 246 is a magical number.

Please note that multi-set S can contain repeated elements, e.g. if number is 55, then S = {5, 5, 55}. Products of digits of these subsequences will be {prod(5) = 5, prod(5) = 5, prod(55) = 25}, i.e. {5, 5, 25}. Sum of all of these is 35 which is odd. Hence 55 is not a 
magical number.

Consider a number 204, then S = {2, 0, 4, 20, 04, 24, 204}. Products of digits of these subsequences will be {2, 0, 4, 0, 0, 8, 0}. Sum of all these elements will be 14 which is even. So 204 is a magical number.

The task was to simply find the Kth magical number.

-----Input-----
- First line of the input contains an integer T denoting the number of test cases.
- Each of the next T lines contains a single integer K.

-----Output-----
For each test case, print a single integer corresponding to the Kth magical number.

-----Constraints-----
- 1 ≤ T ≤ 105
- 1 ≤ K ≤ 1012.

-----Subtasks-----
Subtask #1 : (20 points)
- 1 ≤ T ≤ 100
- 1 ≤ K ≤ 104.

Subtask 2 : (80 points) Original Constraints

-----Example-----
Input:
2
2
5

Output:
2
8

-----Explanation-----
Example case 1.
2 is the 2nd magical number, since it satisfies the property of the magical number. The first magical number will be of course 0.

def base5 (n : Nat) : List Nat := sorry

def seq (n : Nat) : Nat := sorry

def get_kth_magical_number (k : Nat) : Nat := sorry 

def digitList (n : Nat) : List Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible