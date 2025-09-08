/-
A permutation of length $n$ is an array consisting of $n$ distinct integers from $1$ to $n$ in arbitrary order. For example, $[2,3,1,5,4]$ is a permutation, but $[1,2,2]$ is not a permutation ($2$ appears twice in the array) and $[1,3,4]$ is also not a permutation ($n=3$ but there is $4$ in the array).

Let $p$ be any permutation of length $n$. We define the fingerprint $F(p)$ of $p$ as the sorted array of sums of adjacent elements in $p$. More formally,

$$F(p)=\mathrm{sort}([p_1+p_2,p_2+p_3,\ldots,p_{n-1}+p_n]).$$

For example, if $n=4$ and $p=[1,4,2,3],$ then the fingerprint is given by $F(p)=\mathrm{sort}([1+4,4+2,2+3])=\mathrm{sort}([5,6,5])=[5,5,6]$.

You are given a permutation $p$ of length $n$. Your task is to find a different permutation $p'$ with the same fingerprint. Two permutations $p$ and $p'$ are considered different if there is some index $i$ such that $p_i \ne p'_i$.

-----Input-----

Each test contains multiple test cases. The first line contains the number of test cases $t$ ($1 \le t \le 668$). Description of the test cases follows.

The first line of each test case contains a single integer $n$ ($2\le n\le 100$)  — the length of the permutation.

The second line of each test case contains $n$ integers $p_1,\ldots,p_n$ ($1\le p_i\le n$). It is guaranteed that $p$ is a permutation.

-----Output-----

For each test case, output $n$ integers $p'_1,\ldots, p'_n$ — a permutation such that $p'\ne p$ and $F(p')=F(p)$.

We can prove that for every permutation satisfying the input constraints, a solution exists.

If there are multiple solutions, you may output any.

-----Example-----
Input
3
2
1 2
6
2 1 6 5 4 3
5
2 4 3 1 5

Output
2 1
1 2 5 6 3 4
3 1 5 2 4

-----Note-----

In the first test case, $F(p)=\mathrm{sort}([1+2])=[3]$.

And $F(p')=\mathrm{sort}([2+1])=[3]$.

In the second test case, $F(p)=\mathrm{sort}([2+1,1+6,6+5,5+4,4+3])=\mathrm{sort}([3,7,11,9,7])=[3,7,7,9,11]$.

And $F(p')=\mathrm{sort}([1+2,2+5,5+6,6+3,3+4])=\mathrm{sort}([3,7,11,9,7])=[3,7,7,9,11]$.

In the third test case, $F(p)=\mathrm{sort}([2+4,4+3,3+1,1+5])=\mathrm{sort}([6,7,4,6])=[4,6,6,7]$.

And $F(p')=\mathrm{sort}([3+1,1+5,5+2,2+4])=\mathrm{sort}([4,6,7,6])=[4,6,6,7]$.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_fingerprint (n : Nat) (p : List Nat) : List Nat :=
  sorry

theorem solve_fingerprint_length {n : Nat} {p : List Nat} (h : n ≥ 2) : 
  (solve_fingerprint n p).length = p.length :=
  sorry

theorem solve_fingerprint_elements {n : Nat} {p : List Nat} (h : n ≥ 2) :
  ∀ x, x ∈ p ↔ x ∈ solve_fingerprint n p :=
  sorry

theorem solve_fingerprint_reverses {n : Nat} {p : List Nat} (h : n ≥ 2) :
  solve_fingerprint n p = p.reverse :=
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible