-- <vc-preamble>
def calc_total_niceness (n : Nat) (target_sum : Nat) (nums : List Int) : Nat :=
sorry

def gcd (a b : Nat) : Nat :=
sorry

def list_sum (xs : List Int) : Int :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum_nat (xs : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_within_mod (n : Nat) (target_sum : Nat) (nums : List Int)
  (h1 : 1 ≤ n ∧ n ≤ 50)
  (h2 : 1 ≤ target_sum ∧ target_sum ≤ 1000)
  (h3 : ∀ x ∈ nums, -1 ≤ x ∧ x ≤ 1000)
  (h4 : 1 ≤ nums.length ∧ nums.length ≤ 50) :
  let result := calc_total_niceness n target_sum nums
  0 ≤ result ∧ result < 10^9 + 7 :=
sorry

theorem zero_sum_no_missing (n : Nat) (h : 1 ≤ n ∧ n ≤ 50) :
  let ones := List.replicate n 1
  let expected := list_sum_nat ((List.range n).bind (fun i =>
    (List.range (n - i - 1)).map (fun j =>
      gcd 1 1
    )))
  calc_total_niceness n n ones = expected % (10^9 + 7) :=
sorry

theorem impossible_cases (n : Nat) (target_sum : Nat) (nums : List Int)
  (h1 : 1 ≤ n ∧ n ≤ 50)
  (h2 : 1 ≤ target_sum ∧ target_sum ≤ 1000)
  (h3 : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000) :
  (list_sum nums ≠ target_sum → calc_total_niceness nums.length target_sum nums = 0) ∧
  (let nums_with_missing := nums ++ [-1]
   target_sum < list_sum (nums_with_missing.filter (· ≠ -1)) →
   calc_total_niceness nums_with_missing.length target_sum nums_with_missing = 0) :=
sorry

theorem order_invariance (n : Nat) (target_sum : Nat) (nums : List Int)
  (h1 : 1 ≤ n ∧ n ≤ 10)
  (h2 : 1 ≤ target_sum ∧ target_sum ≤ 20)
  (h3 : ∀ x ∈ nums, -1 ≤ x ∧ x ≤ 10)
  (h4 : 1 ≤ nums.length ∧ nums.length ≤ 10) :
  ∀ perm : List Int,
  List.Perm nums perm →
  calc_total_niceness nums.length target_sum nums = 
  calc_total_niceness perm.length target_sum perm :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval calc_total_niceness 3 3 [1, 1, -1]

/-
info: 23
-/
-- #guard_msgs in
-- #eval calc_total_niceness 4 8 [1, -1, -1, 3]

/-
info: 150
-/
-- #guard_msgs in
-- #eval calc_total_niceness 3 10 [-1, -1, -1]
-- </vc-theorems>