-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_binary_flips (n k : Nat) (s : String) : Nat × String :=
sorry

def is_alternating (s : String) : Bool :=
sorry

def check_consecutive (s : String) (k : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binary_flips_basic_properties {n k : Nat} {s : String}
  (h1 : n > 0) (h2 : k > 0) (h3 : s.length = n) (h4 : ∀ c ∈ s.data, c = '0' ∨ c = '1') :
  let (flips, result) := solve_binary_flips n k s

  flips ≥ 0 ∧
  result.length = n ∧
  (∀ c ∈ result.data, c = '0' ∨ c = '1') :=
sorry

theorem k_one_alternating {n : Nat} {s : String}
  (h1 : n > 0) (h2 : s.length = n) (h3 : ∀ c ∈ s.data, c = '0' ∨ c = '1') :
  let (_, result) := solve_binary_flips n 1 s
  is_alternating result = true :=
sorry

theorem k_gt_one_consecutive {n k : Nat} {s : String}
  (h1 : n > 0) (h2 : k > 1) (h3 : s.length = n) (h4 : ∀ c ∈ s.data, c = '0' ∨ c = '1') :
  let (_, result) := solve_binary_flips n k s
  check_consecutive result k = true :=
sorry

theorem k_equals_n_no_flips {n : Nat} {s : String}
  (h1 : n > 0) (h2 : s.length = n) (h3 : ∀ c ∈ s.data, c = '0' ∨ c = '1') :
  let (flips, result) := solve_binary_flips n n s
  flips = 0 ∧ result = s :=
sorry
-- </vc-theorems>