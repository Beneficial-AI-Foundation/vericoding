Zaikia has $N$ sticks of distinct positive lengths $A_1,A_2,\dots,A_N$. For no good reason at all, he wants to know if there is a triplet of sticks which when connected end-to-end will form a non-trivial triangle. Here non-trivial refers to a triangle with positive area.
Help Zaikia know if such a triplet exists or not. If such a triplet exists, help him find the lexicographically largest applicable triplet.Input
- The first line contains an integer $N$.
- The second line contains $N$ space-seperated integers $A_1,A_2,\dots,A_N$. Output
- In the first line print YES if a triplet exists or NO if it doesn't.
- If such a triplet exists, then in the second line print the lexicographically largest applicable triplet.Constraints
- $3 \leq N \leq {2}\times{10}^{5}$
- $1 \leq A_i \leq {10}^{9}$ for each valid $i$Sample Input 1
5
4 2 10 3 5
Sample Output 1
YES
5 4 3
Explanation 1
There are three unordered triplets of sticks which can be used to create a triangle:
- $4,2,3$
- $4,2,5$
- $4,3,5$
Arranging them in lexicographically largest fashion
- $4,3,2$
- $5,4,2$
- $5,4,3$
Here $5,4,3$ is the lexicographically largest so it is the triplet which dristiron wantsSample Input 2
5
1 2 4 8 16
Sample Output 2
NO
Explanation 2
There are no triplets of sticks here that can be used to create a triangle.

def find_largest_triangle (n : Nat) (nums : List Nat) : String × List Nat := sorry

def is_valid_triangle (sides : List Nat) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded