Indian National Olympiad in Informatics 2016
	Boing Inc, has N employees, numbered 1 ... N. Every employee other than Mr. Hojo (the head of the company) has a manager (P[i] denotes the manager of employee i). Thus an employee may manage any number of other employees but he reports only to one manager, so that the organization forms a tree with Mr. Hojo at the root. We say that employee B is a subordinate of employee A if B appears in the subtree rooted at A.

	Mr. Hojo, has hired Nikhil to analyze data about the employees to suggest how to identify faults in Boing Inc. Nikhil, who is just a clueless consultant, has decided to examine wealth disparity in the company. He has with him the net wealth of every employee (denoted A[i] for employee i). Note that this can be negative if the employee is in debt. He has already decided that he will present evidence that wealth falls rapidly as one goes down the organizational tree. He plans to identify a pair of employees i and j, j a subordinate of i, such A[i] - A[j] is maximum. Your task is to help him do this.

	Suppose, Boing Inc has 4 employees and the parent (P[i]) and wealth information (A[i]) for each employee are as follows:

i		1	2	3	4
A[i]		5	10	6	12
P[i]		2	-1	4	2

P[2] = -1 indicates that employee 2 has no manager, so employee 2 is Mr. Hojo.

In this case, the possible choices to consider are (2,1) with a difference in wealth of 5, (2,3) with 4, (2,4) with -2 and (4,3) with 6. So the answer is 6.

-----Input format-----
	There will be one line which contains (2*N + 1) space-separate integers. The first integer is N, giving the number of employees in the company. The next N integers A[1], .., A[N] give the wealth of the N employees. The last N integers are P[1], P[2], .., P[N], where P[i] identifies the manager of employee i. If Mr. Hojo is employee i then, P[i] = -1, indicating that he has no manager.

-----Output format-----
	One integer, which is the needed answer.

-----Test data-----
-108 ≤ A[i] ≤ 108, for all i.
Subtask 1 (30 Marks) 1 ≤ N ≤ 500.
Subtask 2 (70 Marks) 1 ≤ N ≤ 105.

-----Sample Input-----
4 5 10 6 12 2 -1 4 2

-----Sample Output-----
6

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
