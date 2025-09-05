Harsh, like usual, started studying 6 months before for his end semester examinations. He was going to complete his 8th revision of the whole syllabus, when suddenly Pranav showed up in his room with the last year's question paper for their algorithms course. This paper contains a problem which both of them couldn't solve. Frustrated he asked you for help. But you declined him and instead try to do this problem instead:
You are given an array $A_1,A_2,\dots,A_N$, a positive integer $K$, and a function $F(x)=\displaystyle\sum_{i=1}^{N}{\left|{\left({x-A_i}\right)^K}\right|}$. Find the smallest integer $x$ such that $F(x)$ is minimum.Input
- The first line contains two space-seperated integers , $N$ and $K$
- The second line contains $N$ space-seperated integers $A_1,A_2,\dots,A_N$. Output
In the first and only line print the smallest integer $x$ such that $F(x)$ is minimumConstraints
- $1 \leq N \leq {10}^{5}$
- $1 \leq K \leq {3}$
- $1 \leq A_i \leq {5}\times{10}^{4}$ for each valid $i$Sample Input 1
3 1
6 1 7
Sample Output 1
6
Explanation 1
$F(6) = \displaystyle\sum_{i=1}^{N}{\left|{\left({6-A_i}\right)^K}\right|} \\ F(6) = \left|{\left({6-6}\right)^1}\right| + \left|{\left({6-1}\right)^1}\right| + \left|{\left({6-7}\right)^1}\right| \\ F(6)  = 0 + 5+ 1 \\ F(6)  = 6 $
Here $6$ is the minumum value for $F(x)$ for any integer value of $x$.Sample Input 2
3 2
6 1 7
Sample Output 2
5
Explanation 2
$F(5) = \displaystyle\sum_{i=1}^{N}{\left|{\left({5-A_i}\right)^K}\right|} \\F(5) = \left|{\left({5-6}\right)^2}\right| + \left|{\left({5-1}\right)^2}\right| + \left|{\left({5-7}\right)^2}\right| \\F(5) = 1 + 16 + 4 \\F(5) = 21$ 
Here $21$ is the minumum value for $F(x)$ for any integer value of $x$.Sample Input 3
3 3
6 1 7
Sample Output 3
4
Explanation 3
$F(4) = \displaystyle\sum_{i=1}^{N}{\left|{\left({4-A_i}\right)^K}\right|} \\F(4) = \left|{\left({4-6}\right)^3}\right| + \left|{\left({4-1}\right)^3}\right| + \left|{\left({4-7}\right)^3}\right| \\F(4) = 8 + 27 + 27 \\F(4) = 62 $
Here $62$ is the minumum value for $F(x)$ for any integer value of $x$.

def find_min_x (n k : Nat) (arr : List Int) : Int := sorry

def compute_cost (x : Int) (k : Nat) (arr : List Int) : Int := sorry

def list_min (l : List Int) : Int :=
  match l with
  | [] => 0
  | (x::xs) => List.foldl min x xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded