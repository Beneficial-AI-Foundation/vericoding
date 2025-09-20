-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countDigit (n : Nat) (d : Nat) : Nat :=
sorry

def find_max_digit_frequency (nums : List Nat) (target : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>