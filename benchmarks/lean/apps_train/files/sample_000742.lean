Chef spent N days working really hard! He planned loads of tasks: as many as Ai tasks to do on the ith day! Chef's work was brutal, so he only managed to finish Bi tasks on the ith day.
The good news is that Chef has a Time Machine! 
The Time Machine has K white buttons and M black buttons. Each button has a positive integer printed on it. Now Chef goes through all N days consequently and presses buttons. Each day Chef can only press one button (either white or black). After using a button once, it becomes inactive.
Pressing a white button with integer x printed on it reduces the number of planned tasks on the day it was pressed by exactly x. Note that this white button can only be pressed if number of planned tasks on the day are greater than or equal to x.
Pressing a black button with integer x printed on it increases the number of completed tasks on the day it was pressed by exactly x. Note that this black button can only be pressed if after pressing it, number of completed tasks don't exceed the number of tasks.
Chef is interested in finding the minimum possible amount of total uncompleted tasks he will still be left with after N days using the Machine in the best way?
Be careful! Time is sensitive! Chef cannot make a day when he completed more tasks then planned, as this may result in a more-work-than-planned paradox, killing all lazy people on the planet!

-----Input-----
- The first line of input contains a single integer T, denoting the number of test cases. Description of T test cases follows.
- The first line of each test case contains three integers — N, K, M — denoting the number of days, white and black buttons appropriately.
- The second line contains N space-separated integers A1, A2, … , AN, denoting the number of planned tasks.
- The third line contains N space-separated integers B1, B2, … , BN, denoting the number of completed tasks.
- The fourth line contains K space-separated integers C1, C2, … , CK, denoting the integers on white buttons.
- The fifth and last line contains M space-separated integers D1, D2, … , DM, denoting the integers on black buttons.

-----Output-----
- In a single line, output an integer — the minimum possible amount of uncompleted tasks.

-----Constraints-----
- 1 ≤ T ≤ 4
- 1 ≤ N, K, M ≤ 10^5
- 1 ≤ Bi ≤ Ai  ≤ 10^5
- 1 ≤ Ci, Di  ≤ 10^5

-----Subtasks-----
- Subtask N ≤ 10, K, M ≤ 5. Points: 30 
- Subtask Original constraints. Points: 70 

-----Example-----
Input:
1
4 2 2 
5 7 6 1
3 3 1 1
6 3
1 4

Output:
3

-----Explanation-----
Example case 1.
In this example Chef goes through the following steps:
Use black button 1 on the first day.
Use black button 4 on the second day.
Use white button 3 on the third day.
The arrays A and B are now effectively changed to:
5 7 3 1
4 7 1 1
So he will have 3 uncompleted tasks.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded