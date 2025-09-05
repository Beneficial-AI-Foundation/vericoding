Sereja is hosting his birthday dinner. He invited his N close friends. Let us number the people from 1 to N according to the order in which they arrive at the event. The dinner is being held in long straight corridor in which people sit in a way such that they won't leave any empty space in between two consecutive persons at any given time. 

When a person number i arrives at the corridor, he must go and stand to the immediate right of the person numbered A[i] (if A[i] = 0, then this person just stands at the leftmost end of the line). 

But there is a problem, as there is no space between two consecutive persons at any given time, so for this person to sit, space must be created by moving either all the persons to left of the place to the left one step each, or all the persons to right of the place to the right one step each.  

Now, Sereja is wondering about what could be the minimum number of steps people will take so as to sit in the dinner party. Please find it fast, so that Sereja can peacefully entertain his guests.

-----Input-----
First line of input contain an integer T — the number of test cases. T tests follow.
First line of each test case contain the integer N, and the next line contains N integers — A[1], A[2], ... , A[N].

-----Output-----
For each test case, output a single line with the answer — the minimal number of steps required.

-----Constraints-----
- 1 ≤ T ≤ 100
- 1 ≤ N ≤ 100
- 0 ≤ A[i] < i

-----Example-----
Input:
3
1
0
3
0 0 0
5
0 1 2 1 4

Output:
0
0
3

-----Explanation-----
Example case 3.
- First three persons don't need any steps to sit. The line after the arrangement of these persons will look like [1, 2, 3].  

- When person #4 comes in, he wants to sit to the right of person 1, so we need to either move the first person to the left, or the second and third persons to the right. The first case is clearly better. Now the line will look like [1, 4, 2, 3].  

- When person #5 arrives, he will need to move 2 persons in either case. The final arrangement will be [1, 4, 5, 2, 3]. 

So total number of steps people moved during the entire process is 1 + 2 = 3. So the answer is 3.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded