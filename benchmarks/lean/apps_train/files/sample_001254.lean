Batman is about to face Superman so he decides to prepare for the battle by upgrading his Batmobile. He manufactures multiple duplicates of his standard Batmobile each tweaked in a different way such that the maximum speed of each is never less than that of the standard model.
After carrying out this process, he wishes to know how many of his prototypes are faster than his standard Batmobile?

-----Input-----
- The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follow: 
- The first line of each test case contains a single integer N denoting the number of copies of the standard Batmobile.
- The second line contains a sequence of N+1 space-separated integers, S0 to SN, sorted in non-decreasing order separated by space. S0 is the maximum speed of the standard Batmobile. S1 to SN denote the maximum speeds of the prototypes.

-----Output-----
- For each test case, output a single line containing an integer denoting the answer.

-----Constraints-----
- 1 ≤ T ≤ 1000
- 1 ≤ N ≤ 1000
- 1 ≤ Si ≤ 109

-----Example-----
Input:
2
4
1 2 3 4 5
5
1 10 100 1000 10000 100000

Output:
4
5

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
