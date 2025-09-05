Probably everyone has experienced an awkward situation due to shared armrests between seats in cinemas. A highly accomplished cinema manager named "Chef" decided to solve this problem.

When a customer wants to buy a ticket, the clerk at the ticket window asks the visitor if they need the armrests, and if so, which of them: left, right, or both. We know that out of the audience expected to show up, L of them only need the left armrest, R of them need just the right one, Z need none and B need both. Your task is to calculate the maximum number of people that can attend the show. In the cinema hall there are N rows with M seats each. There is only one armrest between two adjacent seats. Seats at the beginning and at the end of the row have two armrests

-----Input-----

Input begins with an integer T: the number of test cases.

Each test case consists of a single line with 6 space-separated integers: N, M, Z, L, R, B.

-----Output-----

For each test case, output a line containing the answer for the task.

-----Constraints and Subtasks-----
- 1 ≤ T ≤ 105 
Subtask 1 : 10 points 
- 1 ≤ N, M ≤ 3 
- 0 ≤ Z, L, R, B ≤ 3 
Subtask 2 : 20 points 
- 1 ≤ N, M ≤ 30 
- 0 ≤ Z, L, R ≤ 30 
- 0 ≤ B ≤ 109 
Subtask 3 : 30 points
- 1 ≤ N, M ≤ 106 
- 0 ≤ Z, L, R ≤ 106 
- 0 ≤ B ≤ 1016 
Subtask 4 : 40 points
- 1 ≤ N, M ≤ 108 
- 0 ≤ Z, L, R, B ≤ 1016 

-----Example-----
Input:2
2 2 3 2 1 1
3 3 1 2 0 9

Output:4
8

-----Explanation-----
'L' - needs left

'R - needs right

'Z' - doesn't need any

'B' - needs both

'-' - empty place

Example case 1.
ZZ

ZB
Example case 2.
LLB

BZB

B-B

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded