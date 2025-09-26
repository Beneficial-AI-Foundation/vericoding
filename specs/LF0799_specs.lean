-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_complete_task (x y : Nat) : String := sorry

theorem can_complete_task_output_valid (x y : Nat) 
    (hx : x > 0) (hy : y > 0) :
    can_complete_task x y = "YES" ∨ can_complete_task x y = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_complete_task_coprime (x y : Nat) 
    (hx : x > 0) (hy : y > 0) :
    can_complete_task x y = "YES" ↔ Nat.gcd x y = 1 := sorry

theorem can_complete_task_not_coprime (x y : Nat)
    (hx : x > 0) (hy : y > 0) :
    can_complete_task x y = "NO" ↔ Nat.gcd x y > 1 := sorry

theorem can_complete_task_with_one (n : Nat) (h : n > 0) :
    can_complete_task n 1 = "YES" ∧ can_complete_task 1 n = "YES" := sorry

theorem can_complete_task_same_number (n : Nat) (h : n > 0) :
    can_complete_task n n = (if n = 1 then "YES" else "NO") := sorry
-- </vc-theorems>