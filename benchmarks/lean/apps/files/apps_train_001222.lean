def base5 (n : Nat) : List Nat := sorry

def seq (n : Nat) : Nat := sorry

def get_kth_magical_number (k : Nat) : Nat := sorry 

def digitList (n : Nat) : List Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def isEvenDigit (n : Nat) : Bool := sorry

theorem base5_zero :
  base5 0 = [] := sorry

theorem base5_digits_bounded (n : Nat) :
  ∀ d ∈ base5 n, 0 ≤ d ∧ d ≤ 4 := sorry

theorem magical_increasing (k : Nat) :
  k > 1 →
  get_kth_magical_number (k-1) < get_kth_magical_number k := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval get_kth_magical_number 2

/-
info: 8
-/
-- #guard_msgs in
-- #eval get_kth_magical_number 5

/-
info: 0
-/
-- #guard_msgs in
-- #eval get_kth_magical_number 1

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible