The "BerCorp" company has got n employees. These employees can use m approved official languages for the formal correspondence. The languages are numbered with integers from 1 to m. For each employee we have the list of languages, which he knows. This list could be empty, i. e. an employee may know no official languages. But the employees are willing to learn any number of official languages, as long as the company pays their lessons. A study course in one language for one employee costs 1 berdollar.

Find the minimum sum of money the company needs to spend so as any employee could correspond to any other one (their correspondence can be indirect, i. e. other employees can help out translating).

-----Input-----

The first line contains two integers n and m (2 ≤ n, m ≤ 100) — the number of employees and the number of languages.

Then n lines follow — each employee's language list. At the beginning of the i-th line is integer k_{i} (0 ≤ k_{i} ≤ m) — the number of languages the i-th employee knows. Next, the i-th line contains k_{i} integers — a_{ij} (1 ≤ a_{ij} ≤ m) — the identifiers of languages the i-th employee knows. It is guaranteed that all the identifiers in one list are distinct. Note that an employee may know zero languages.

The numbers in the lines are separated by single spaces.

-----Output-----

Print a single integer — the minimum amount of money to pay so that in the end every employee could write a letter to every other one (other employees can help out translating).

-----Examples-----
Input
5 5
1 2
2 2 3
2 3 4
2 4 5
1 5

Output
0

Input
8 7
0
3 1 2 3
1 1
2 5 4
2 6 7
1 3
2 7 4
1 1

Output
2

Input
2 2
1 2
0

Output
1

-----Note-----

In the second sample the employee 1 can learn language 2, and employee 8 can learn language 4.

In the third sample employee 2 must learn language 2.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded