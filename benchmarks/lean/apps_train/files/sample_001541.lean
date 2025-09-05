Mr. Das is a teacher teaching for several years in a school. He is not computer savvy. Due to lockdown, now he has to take classes online. Recently he took an online exam for students of different classes. Now, he will call parents of all the students who scored lower than average marks for the class. He has requested you to give the name $X$, parent's phone number $P$, and marks obtained $M$ to him.

-----Input:-----
- First line contains $T$ no. of test cases
- for every test case, first line contains an integer $N$, no. of students of his class 
- Next $N$ lines contain $X$, $P$ , and $M$ separated by space

-----Output:-----
For every test case, find details of the students who scored below average, then print $X, P, M$  separated by space on a new line as per the increasing order of their marks. In case there are multiple students with the same marks, print them as per the order of their occurrence in the input

-----Constraints-----
- $1 \leq T \leq 20$
- X contains characters between a-z and A-Z  with a maximum length of 20
- $1 \leq N \leq 100$
- P is 10 digits
- $0 \leq M \leq 100$

-----Sample Input:-----
2  
3
Rahul 1345964789 47
Rupendra 1457856987 58
Priya 1478569820 45
2
Tanuja 4310779415 97
Akash 3689781245 43

-----Sample Output:-----
Priya 1478569820 45
Rahul 1345964789 47
Akash 3689781245 43

-----EXPLANATION:-----
In #1, Priya and Rahul's number was lower than average.
In #2, Akash's number was lower than average

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded