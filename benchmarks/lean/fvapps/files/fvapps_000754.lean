-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_smallest_good_perm (n: Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem good_perm_single_element :
  find_smallest_good_perm 1 = "1" :=
  sorry

theorem good_perm_two_elements :  
  find_smallest_good_perm 2 = "2 1" :=
  sorry 

theorem good_perm_three_elements : 
  find_smallest_good_perm 3 = "2 3 1" :=  
  sorry

theorem good_perm_five_elements :
  find_smallest_good_perm 5 = "2 1 4 5 3" :=
  sorry

theorem good_perm_six_elements :
  find_smallest_good_perm 6 = "2 1 4 3 6 5" :=
  sorry

theorem good_perm_basic_properties (n: Nat) (h: n > 0) (h2: n ≤ 100) :
  let result := find_smallest_good_perm n
  let nums := (result.split (· = ' ')).map String.toNat!
  nums.length = n ∧ 
  nums.Nodup ∧
  nums.all (λ x => 1 ≤ x ∧ x ≤ n) ∧
  (n > 1 → nums.get! 0 = 2) ∧
  (n = 1 → result = "1") :=
  sorry
-- </vc-theorems>