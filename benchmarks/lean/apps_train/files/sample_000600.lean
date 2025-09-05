We all know that Share market is place where drastic change occurs within moments. So we have one Stockholder, Isabella, who wants to maximize her profit by selling her shares. She has $N$ shares of a Doofenshmirtz Corporation which is represented by $N$ different lines where each line contains two space separated integers $a_i$ , $b_i$ corresponding to initial and final values of the share prize. Isabella can sell any number of shares. But, she will sell those shares only if the following condition is satisfied - 
- for any pair $(i,j)$ of shares that she choses to sell, $a_i \leq a_j$  and $b_i < b_j$ must be satisfied. 
You need to tell Isabella the maximum number of Shares she can sell.

-----Input:-----
- First line will contain $T$, number of test cases. 
- Each test case has the following format:
- First line of each test case contain single integer $N$, the number of shares of Isabella.  
- Next $N$ lines of each test case contain two space separated integers $a_i$, $b_i$ (initial and final value of share prize respectively) for each $1 \leq i \leq N$.

-----Output:-----
For each test case output a single integer: the maximum number of shares that can be sold by Isabella.

-----Constraints-----
- $1 \leq T \leq 5$
- $1 \leq N \leq 10^5$
- $1 \leq a_i , b_i \leq 10^9 , for  each $1$ \leq $i$ \leq $N 

-----Sample Input:-----
$1$
$4$ 
$1$ $2$
$4$ $3$
$3$ $5$ 
$2$ $4$ 

-----Sample Output:-----
$3$   

-----Explanation:-----
Here, Isabella decided to sell share 1, share 3 and share 4 as any two pair of 
chosen share hold the given condition.

def find_max_shares_to_sell (shares: List Share) : Nat :=
  sorry

def is_unique_shares (shares: List Share) : Bool :=
  sorry

def is_strictly_increasing (l: List Nat) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: xs => x < y && is_strictly_increasing (y :: xs)

def is_strictly_decreasing (l: List Nat) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: xs => x > y && is_strictly_decreasing (y :: xs)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded