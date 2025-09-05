-----Problem Statement-----
Harry Potter has one biscuit and zero rupee in his pocket. He will perform the following operations exactly $K$ times in total, in the order he likes:
- Hit his pocket, which magically increases the number of biscuits by one.
- Exchange $A$ biscuits to $1$ rupee.
- Exchange $1$ rupee to $B$ biscuits.
Find the maximum possible number of biscuits in Harry's pocket after $K$ operations.

-----Input-----
Input is given in the following format:
K A B

-----Output-----
Print the maximum possible number of biscuits in Harry's pocket after $K$operations.

-----Constraints-----
- $1 \leq K, A, B \leq 10^9$
- $K$, $A$ and  are integers.

-----Sample Input-----
4 2 6

-----Sample Output-----
7

-----EXPLANATION-----
The number of biscuits in Harry's pocket after $K$ operations is maximized as follows:
- Hit his pocket. Now he has $2$ biscuits and $0$ rupee.
- Exchange $2$ biscuits to $1$ rupee in his pocket .Now he has $0$ biscuits and $1$ rupee.
- Hit his pocket. Now he has $1$ biscuits and $1$ rupee.
- Exchange $1$ rupee to $6$ biscuits. his pocket. Now he has $7$ biscuits and $0$ rupee.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
