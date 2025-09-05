Dr. S. De teaches computer architecture in NIT Patna. Whenever he comes across any good question(with complexity $k$), he gives that question to students within roll number range $i$ and $j$
At the start of semester he assigns score of $10$ to every student in his class if a student submits a question of complexity $k$, his score gets multiplied by $k$
This month he gave $M$ questions and he is wondering what will be mean of maximum scores of all the student. He is busy in improving his finger print attendance module, can you help him?
Input file may be large so try to use fast input output

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a First line of input, two integers $N, M$ i.e. Number of students in the class and number of questions given in this month. 
- Next $M$ lines contains 3 integers -$i, j, k$ i.e. starting roll number, end roll number and complexity of the question

-----Output:-----
For each testcase, output in a single line answer - $floor$ value of Mean of maximum possible score for all students.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq N, M \leq 10^5$
- $1 \leq i \leq j \leq N$
- $1 \leq k \leq 100$

-----Subtasks-----
Subtask1 
- 
$1 \leq T \leq 10$
- 
$1 \leq N, M \leq 10^4$
Subtask2
- 
Original Constraints 

-----Sample Input:-----
1
5 3
1 3 5
2 5 2
3 4 7

-----Sample Output:-----
202

-----EXPLANATION:-----
Initial score of students will be : $[10, 10, 10, 10, 10]$
after solving question 1 scores will be: $[50, 50, 50, 10, 10]$
after solving question 2 scores will be: $[50, 100, 100, 20, 20]$
after solving question 1 scores will be: $[50, 100, 700, 140, 20]$
Hence after all questions mean of maximum scores will $(50+100+700+140+20)/5 = 202$

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
