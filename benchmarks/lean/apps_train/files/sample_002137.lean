You are given a permutation $p_1, p_2, \ldots, p_n$.

In one move you can swap two adjacent values.

You want to perform a minimum number of moves, such that in the end there will exist a subsegment $1,2,\ldots, k$, in other words in the end there should be an integer $i$, $1 \leq i \leq n-k+1$ such that $p_i = 1, p_{i+1} = 2, \ldots, p_{i+k-1}=k$.

Let $f(k)$ be the minimum number of moves that you need to make a subsegment with values $1,2,\ldots,k$ appear in the permutation.

You need to find $f(1), f(2), \ldots, f(n)$.

-----Input-----

The first line of input contains one integer $n$ ($1 \leq n \leq 200\,000$): the number of elements in the permutation.

The next line of input contains $n$ integers $p_1, p_2, \ldots, p_n$: given permutation ($1 \leq p_i \leq n$).

-----Output-----

Print $n$ integers, the minimum number of moves that you need to make a subsegment with values $1,2,\ldots,k$ appear in the permutation, for $k=1, 2, \ldots, n$.

-----Examples-----
Input
5
5 4 3 2 1

Output
0 1 3 6 10 

Input
3
1 2 3

Output
0 0 0

def BinaryIndexedTree : Type := Unit
def BinaryIndexedTree.mk (n : Nat) : BinaryIndexedTree := sorry 

def BinaryIndexedTree.add (self : BinaryIndexedTree) (i : Nat) (x : Int) : Unit := sorry
def BinaryIndexedTree.sum (self : BinaryIndexedTree) (i : Nat) : Int := sorry

def BinaryIndexedTree.sum_range (self : BinaryIndexedTree) (l r : Nat) : Int := sorry
def BinaryIndexedTree.data (self : BinaryIndexedTree) : List Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
