-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_square_even_root_odd (nums : List Nat) : Float := sorry

theorem sum_square_even_root_odd_nonneg (nums : List Nat) :
  sum_square_even_root_odd nums ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_square_even_root_odd_equals_sum (nums : List Nat) :
  let expected := nums.foldr (fun n acc => 
    acc + if n % 2 = 0 
      then Float.ofNat (n * n)
      else Float.sqrt (Float.ofNat n)) (0 : Float);
  Float.abs (sum_square_even_root_odd nums - expected) < 0.1 := sorry

theorem large_evens_dominate (nums : List Nat) (max_even : Nat) :
  max_even = (nums.filter (fun n => n % 2 = 0)).maximum?.getD 0 →
  max_even > 10 → 
  sum_square_even_root_odd nums ≥ Float.ofNat max_even := sorry

/-
info: 91.61
-/
-- #guard_msgs in
-- #eval sum_square_even_root_odd [4, 5, 7, 8, 1, 2, 3, 0]

/-
info: 272.71
-/
-- #guard_msgs in
-- #eval sum_square_even_root_odd [1, 14, 9, 8, 17, 21]
-- </vc-theorems>