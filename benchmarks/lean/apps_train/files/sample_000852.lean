/-
Rachel has some candies and she decided to distribute them among $N$ kids. The ith kid receives $A_i$ candies. The kids are happy iff the difference between the highest and lowest number of candies received is less than $X$.
Find out if the children are happy or not.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- The first line contains $N$ and $X$. 
- The second line contains $N$ integers $A_1,A_2,...,A_N$. 

-----Output:-----
For each test case print either "YES"(without quotes) if the kids are happy else "NO"(without quotes)

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq N, X \leq 10^5$
- $1 \leq A_i \leq 10^5$

-----Sample Input:-----
2

5 6

3 5 6 8 1

3 10

5 2 9

-----Sample Output:-----
NO

YES

-----EXPLANATION:-----
- Example 1: Difference between maximum and minimum candies received is 8-1=7. 7 is greater than 6, therefore, the kids are not happy.
-/

-- <vc-helpers>
-- </vc-helpers>

def areKidsHappy (n : Nat) (x : Nat) (candies : List Nat) : String := sorry

theorem output_is_yes_or_no {n x : Nat} {candies : List Nat}
  (h1 : n ≥ 2) (h2 : n ≤ 100) 
  (h3 : x ≥ 1) (h4 : x ≤ 1000)
  (h5 : candies.length ≥ 2) (h6 : candies.length ≤ 100)
  (h7 : ∀ c ∈ candies, c ≥ 1 ∧ c ≤ 1000) :
  areKidsHappy n x candies = "YES" ∨ areKidsHappy n x candies = "NO" := sorry

theorem happy_condition {n x : Nat} {candies : List Nat}
  (h1 : n ≥ 2) (h2 : n ≤ 100)
  (h3 : x ≥ 1) (h4 : x ≤ 1000)
  (h5 : candies.length ≥ 2) (h6 : candies.length ≤ 100)
  (h7 : ∀ c ∈ candies, c ≥ 1 ∧ c ≤ 1000) :
  (candies.maximum? >>= λ max => candies.minimum? >>= λ min => some (max - min < x)) = some true ↔ 
  areKidsHappy n x candies = "YES" := sorry

theorem identical_candies_are_happy {candies : List Nat} {n x : Nat}
  (h1 : candies.length ≥ 2) (h2 : candies.length ≤ 100)
  (h3 : ∀ c ∈ candies, c ≥ 1 ∧ c ≤ 1000)
  (h4 : ∀ i : Fin candies.length, ∀ j : Fin candies.length, candies.get i = candies.get j)
  (h5 : x = 1)
  (h6 : n = candies.length) :
  areKidsHappy n x candies = "YES" := sorry

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval are_kids_happy 5 6 [3, 5, 6, 8, 1]

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval are_kids_happy 3 10 [5, 2, 9]

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval are_kids_happy 4 5 [1, 2, 3, 4]

-- Apps difficulty: interview
-- Assurance level: unguarded