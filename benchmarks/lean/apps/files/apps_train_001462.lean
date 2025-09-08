/-
Consider a number X on which K Mag-Inc operations are to be performed. In a Mag-Inc operation, the number X undergoes an increment of A/B times of X where A and B are two integers.

There is a numerator and a denominator array of size K which contain the ith values of A and B. After K Mag-Inc operations, the number X turns to M.

Now your job is to find what percentage of M is to be decremented from M if it has to be converted back to X. Let this percentage be denoted by Z.

Print the integral part of Z.

-----Input:-----

First line contains an integer T denoting the number of test cases.

First line of every test case contains two space separated integers X and K.

The second and third line of every test case will contain K space separated integers 

denoting the Numerator and Denominator array.

-----Output:-----

For each test case, print the required result in a single line.

-----Constraints:-----
1 ≤ T ≤ 100
1 ≤ K, A, B ≤ 40000
1≤X≤10^100

-----Example:-----Input:
2
100 1
1 
4
100 2
1 1
2 3Output:
20
50

-----Explanation:-----

Case 2: 100 undergoes an increment of (1/2)*100. Therefore M = 100 + 50.

Now M = 150.

Now again, 

M undergoes an increment of (1/3)*150. Therefore, M = 150 + 50. 

Now as we want to revert back M = 200 to X i.e. 100, we need to decrement it by a value 

of 100 and we know that 100 is 50% of 200.

Hence, we print 50.
-/

-- <vc-helpers>
-- </vc-helpers>

def calculate_magnification_percentage (x : Float) (k : Nat) (nums : List Nat) (denoms : List Nat) : Nat :=
  sorry

theorem result_between_zero_and_hundred
  (x : Float) (k : Nat) (nums denoms : List Nat)
  (hx : x > 0)
  (hk : k > 0) 
  (hnums : nums.length = k)
  (hdenoms : denoms.length = k)
  (hall_pos : ∀ n ∈ nums ++ denoms, n > 0) :
  let result := calculate_magnification_percentage x k nums denoms
  0 ≤ result ∧ result ≤ 100 :=
sorry

theorem result_scale_invariant
  (x : Float) (k : Nat) (nums denoms : List Nat)
  (hx : x > 0)
  (hk : k > 0)
  (hnums : nums.length = k)
  (hdenoms : denoms.length = k)
  (hall_pos : ∀ n ∈ nums ++ denoms, n > 0) :
  let result₁ := calculate_magnification_percentage x k nums denoms
  let result₂ := calculate_magnification_percentage (2 * x) k nums denoms
  if result₁ ≥ result₂ then result₁ - result₂ ≤ 1 else result₂ - result₁ ≤ 1 :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded