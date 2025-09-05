It is an interesting exercise to write a program to print out all permutations of $1, 2, …, n$. However, since there are $6227020800$ permutations of $1, 2, …, 13$, it is unlikely that we would ever run this program on an input of size more than $10$.
However, here is another interesting problem whose solution can also be used to generate permutations. We can order the permutations of $1, 2, …, n$ under the lexicographic (or dictionary) order. Here are the permutations of $1,2,3$ in lexicographic order:
123132213231312321123132213231312321 1 \, 2 \, 3 \quad    1 \, 3 \, 2 \quad     2 \, 1 \, 3 \quad     2 \, 3 \, 1 \quad     3 \, 1 \, 2 \quad     3 \, 2 \, 1 
The problem we have is the following: given a permutation of $1,2, …, n$, generate the next permutation in lexicographic order. For example, for $2 3 1 4$ the answer is $2 3 4 1$.

-----Input:-----
The first line of the input contains two integers, $N$ and $K$. This is followed by $K$ lines, each of which contains one permutation of $1, 2,…,N$.

-----Output:-----
The output should consist of $K$ lines. Line $i$ should contain the lexicographically next permutation correponding to the permutation on line $i+1$ in the input.

-----Constraints:-----
- $1 \leq N \leq 1000$.
- $1 \leq K \leq 10$.

-----Sample input-----
3 2
3 1 2
2 3 1

-----Sample output-----
3 2 1
3 1 2

def nextPermutation (arr : List Int) : List Int := sorry

def solve (n k : Nat) (perms : List (List Int)) : List (List Int) := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
