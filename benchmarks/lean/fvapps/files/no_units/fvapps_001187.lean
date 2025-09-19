-- <vc-preamble>
def can_tomu_win (n : Nat) (k : Nat) (arr : List Nat) : String := sorry

def getOddElements (l : List Nat) : List Nat :=
  l.zipWith (fun i x => if i % 2 = 1 then some x else none) (List.range l.length)
   |>.filterMap id
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getEvenElements (l : List Nat) : List Nat :=
  l.zipWith (fun i x => if i % 2 = 0 then some x else none) (List.range l.length)
   |>.filterMap id

-- Property: Result is always either "YES" or "NO"
-- </vc-definitions>

-- <vc-theorems>
theorem can_tomu_win_valid_output (n k : Nat) (arr : List Nat) :
  can_tomu_win n k arr = "YES" ∨ can_tomu_win n k arr = "NO" := sorry

-- Property: When k=0, if Tomu's initial sum ≤ Motu's initial sum, result is "NO" 

theorem k_zero_no_improvement (n : Nat) (arr : List Nat) 
  (h1 : arr.length = n)
  (h2 : (getOddElements arr).foldl (· + ·) 0 ≤ (getEvenElements arr).foldl (· + ·) 0) :
  can_tomu_win n 0 arr = "NO" := sorry

-- Property: With k ≥ n, if array has distinct values, Tomu can win

theorem large_k_wins (n : Nat) (arr : List Nat)
  (h1 : arr.length = n)
  (h2 : n > 1)
  (h3 : ∃ (x y : Nat), x ∈ arr ∧ y ∈ arr ∧ x > y) :
  can_tomu_win n n arr = "YES" := sorry

-- Property: Base cases work correctly

theorem base_cases :
  can_tomu_win 1 0 [1] = "NO" ∧
  can_tomu_win 2 1 [1, 2] = "YES" := sorry
-- </vc-theorems>