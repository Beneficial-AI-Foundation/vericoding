Using his tip-top physique, Kim has now climbed up the mountain where the base is located. Kim has found the door to the (supposedly) super secret base. Well, it is super secret, but obviously no match for Kim's talents. 
The door is guarded by a row of $N$ buttons. Every button has a single number $A_i$ written on it. Surprisingly, more than one button can have the same number on it. Kim recognises this as Soum's VerySafe door, for which you need to press two buttons to enter the password. More importantly, the sum of the two numbers on the buttons you press must be odd. Kim can obviously break through this door easily, but he also wants to know how many different pairs of buttons he can pick in order to break through the door.
Can you help Kim find the number of different pairs of buttons he can press to break through the door? 
Note: Two pairs are considered different if any of the buttons pressed in the pair is different (by position of the button pressed). Two pairs are not considered different if they're the same position of buttons, pressed in a different order. 
Please refer to the samples for more details.

-----Input:-----
- The first line contains a single integer $T$, representing the number of testcases. $2T$ lines follow, 2 for each testcase.
- For each testcase, the first line contains a single integer $N$, the number of buttons.
- The second line of each testcase contains $N$ space-separated integers, $A_1, A_2, \ldots, A_N$, representing the numbers written on each button.

-----Output:-----
Print a single number, $K$, representing the number of pairs of buttons in $A$ which have an odd sum.

-----Subtasks-----
For all subtasks,  $1 \leq T \leq 10$, $1 \leq N \leq 100000$, and $1 \leq A_i \leq 100000$ for all $A_i$.
Subtask 1 [15 points] : $N \leq 2$, There are at most 2 buttons
Subtask 2 [45 points] : $N \leq 1000$, There are at most 1000 buttons
Subtask 3 [40 points] : No additional constraints.

-----Sample Input:-----
3
4
3 5 3 4
2
5 7
1
4

-----Sample Output:-----
3
0
0

-----EXPLANATION:-----
This section uses 1-indexing.
In the first sample, the buttons are: $[3, 5, 3, 4]$
$A[1] +  A[4] = 3 + 4 = 7$ which is odd.
$A[2] +  A[4] = 5 + 4 = 9$ which is odd.
$A[3] +  A[4] = 3 + 4 = 7$ which is odd.
In total, there are 3 pairs with an odd sum, so the answer is 3.
In the second sample, the buttons are: $[5, 7]$. There are no odd pairs, so the answer is $0$.
In the third sample, the buttons are: $[4]$. There are no pairs at all, so the answer is $0$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
