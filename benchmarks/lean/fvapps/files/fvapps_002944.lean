-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_digit (n : Nat) (d : Nat) : Prop := sorry

def compute_depth (n : Nat) : Nat :=
sorry

def list_product (nums : List Nat) (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def has_all_digits (n : Nat) : Prop :=
  ∀ d, d < 10 → has_digit n d

theorem compute_depth_positive (n : Nat) (h : n > 0) :
  compute_depth n > 0 :=
sorry

theorem compute_depth_contains_all_digits (n : Nat) (h : n > 0) :
  ∃ nums : List Nat,
    nums.length = compute_depth n ∧
    has_all_digits (list_product nums n) :=
sorry

theorem compute_depth_is_minimal (n : Nat) (h : n > 0) :
  ∀ k < compute_depth n,
    ¬∃ nums : List Nat,
      nums.length = k ∧
      has_all_digits (list_product nums n) :=
sorry

theorem compute_depth_upper_bound (n : Nat) (h : n > 0) (h2 : n ≤ 100) :
  compute_depth n ≤ n * 100 :=
sorry

theorem powers_of_ten_depth_positive :
  ∀ i : Nat, compute_depth (10^i) > 0 :=
sorry
-- </vc-theorems>