def countDigit (n : Nat) (d : Nat) : Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def find_max_digit_frequency (nums : List Nat) (target : Nat) : Nat :=
sorry

theorem max_digit_freq_in_list (nums : List Nat) (target : Nat) 
  (h : nums ≠ []) :
  find_max_digit_frequency nums target ∈ nums :=
sorry

theorem max_digit_freq_is_max (nums : List Nat) (target : Nat) 
  (h : nums ≠ []) : 
  ∀ n ∈ nums, countDigit (find_max_digit_frequency nums target) target ≥ 
              countDigit n target :=
sorry

theorem no_target_returns_first (nums : List Nat) (target : Nat)
  (h : nums ≠ []) 
  (h2 : ∀ n ∈ nums, countDigit n target = 0) :
  find_max_digit_frequency nums target = nums.head! :=
sorry

theorem same_freq_returns_first (nums : List Nat) (target : Nat)
  (h : nums ≠ []) (n : Nat) (hn : n ∈ nums) :
  countDigit n target = countDigit (find_max_digit_frequency nums target) target →
  n = find_max_digit_frequency nums target ∨ 
  nums.findIdx (. = n) > nums.findIdx (. = find_max_digit_frequency nums target) :=
sorry

/-
info: '1323'
-/
-- #guard_msgs in
-- #eval find_max_digit_frequency ["345", "1323", "165", "98", "456"] "3"

/-
info: '335'
-/
-- #guard_msgs in
-- #eval find_max_digit_frequency ["335", "876", "98", "1323", "349"] "3"

-- Apps difficulty: interview
-- Assurance level: unguarded