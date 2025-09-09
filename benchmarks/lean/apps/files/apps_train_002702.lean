-- <vc-helpers>
-- </vc-helpers>

def withdraw (n : Int) : (Int × Int × Int) := sorry

/- The withdraw function returns a valid solution for multiples of 10 -/

theorem withdraw_valid (amount : Int) (h : amount ≥ 20) (h2 : amount % 10 = 0) : 
  let (hundreds, fifties, twenties) := withdraw amount
  hundreds ≥ 0 ∧ fifties ≥ 0 ∧ twenties ≥ 0 ∧ 
  hundreds * 100 + fifties * 50 + twenties * 20 = amount := sorry

/- The withdraw function returns optimal solutions with limited 20s -/

theorem withdraw_optimal (amount : Int) (h : amount ≥ 20) (h2 : amount % 10 = 0) :
  let (hundreds, fifties, twenties) := withdraw amount
  twenties ≤ 4 := sorry

/- The withdraw function uses fifties efficiently -/

theorem withdraw_fifty_efficient (amount : Int) (h : amount ≥ 20) (h2 : amount % 10 = 0) :
  let (hundreds, fifties, twenties) := withdraw amount
  fifties > 0 →
  let remainder := amount - (hundreds * 100 + fifties * 50)
  remainder ≥ 0 ∧ remainder % 20 = 0 := sorry

/-
info: [0, 0, 2]
-/
-- #guard_msgs in
-- #eval withdraw 40

/-
info: [2, 1, 0]
-/
-- #guard_msgs in
-- #eval withdraw 250

/-
info: [2, 0, 3]
-/
-- #guard_msgs in
-- #eval withdraw 260

-- Apps difficulty: introductory
-- Assurance level: guarded