Given a positive integer K > 2, with prime
factorization:

K = p1^a1 * p2^a2 ... * pn^an

Compute the following:

S = a1*p1 + a2*p2 ... + an*pn.

-----Input-----
A list of <100 integers, one on each line,
all less than $2*10^{18}$.

-----Output-----
For each integer compute the super factor
sum and output it on a single line.

-----Example-----
Input:
6
7
Output:
5
7

def compute_super_factor_sum (n : Nat) : Nat := sorry

def is_prime (n : Nat) : Bool := sorry

def list_product : List Nat → Nat 
  | [] => 1
  | x :: xs => x * list_product xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
