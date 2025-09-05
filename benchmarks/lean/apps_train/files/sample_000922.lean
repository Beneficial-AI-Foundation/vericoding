A repetition-free number is one in which each digit $\{1,2,3,…,9\}$ appears at most once and the digit $0$ does not appear. A repetition-free number can have at most nine digits, but may also have fewer than nine digits. Some examples of repetition-free numbers are $9, 32, 489, 98761$ and $983245$.
You will be given an integer $N$ with at most nine digits. Your task is to print out the smallest repetition-free number bigger than $N$. For example, for $99$ the answer is $123$, for $881$ the answer is $891$, and for $133$ the answer is $134$.

-----Input:-----
A single line with a single integer with at most $9$ digits.

-----Output:-----
A single line containing the smallest repetition-free number bigger than the given number. If there is no repetition-free number bigger than the given number, print $0$.

-----Constraints:-----
- $N$ consists of atmost $9$ digits

-----Sample input-----
99

-----Sample output-----
123

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible