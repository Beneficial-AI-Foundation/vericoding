-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_form_army (g t w : Nat) : String := sorry

def sorted_list (a b c : Nat) : List Nat :=
  let list := [a, b, c]
  if a ≤ b then
    if b ≤ c then [a, b, c]
    else if a ≤ c then [a, c, b]
    else [c, a, b]
  else if a ≤ c then [b, a, c]
  else if b ≤ c then [b, c, a]
  else [c, b, a]
-- </vc-definitions>

-- <vc-theorems>
theorem can_form_army_valid_output (g t w : Nat) :
  can_form_army g t w = "Yes" ∨ can_form_army g t w = "No" := sorry

theorem can_form_army_commutative_1 (g t w : Nat) :
  can_form_army g t w = can_form_army t g w := sorry

theorem can_form_army_commutative_2 (g t w : Nat) :
  can_form_army g t w = can_form_army w t g := sorry

theorem can_form_army_equal_positive (n : Nat) (h : n > 0) :
  can_form_army n n n = "Yes" := sorry

theorem can_form_army_sum_criterion {g t w : Nat} :
  let nums := sorted_list g t w
  (nums[0]! + nums[1]! ≥ nums[2]!) → can_form_army g t w = "Yes" := sorry

theorem can_form_army_sum_criterion_converse {g t w : Nat} :
  let nums := sorted_list g t w
  can_form_army g t w = "Yes" → (nums[0]! + nums[1]! ≥ nums[2]!) := sorry

theorem can_form_army_boundary_1 : 
  can_form_army 1 1 1 = "Yes" := sorry

theorem can_form_army_boundary_2 :
  can_form_army 100 100 100 = "Yes" := sorry
-- </vc-theorems>