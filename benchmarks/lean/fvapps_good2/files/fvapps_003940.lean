-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
instance : ToString Nat where
  toString := sorry

def solve (x y : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_nonneg {x y : Nat} (h : x ≤ y) :
  solve x y ≥ 0 :=
sorry

theorem solve_le_range {x y : Nat} (h : x ≤ y) :
  solve x y ≤ y - x :=
sorry

theorem solve_empty_range (n : Nat) :
  solve n n = 0 :=
sorry

theorem solve_split_range {x y z : Nat}
  (h1 : x ≤ y) (h2 : y ≤ z) :
  solve x z = solve x y + solve y z :=
sorry

theorem valid_rotation_digits (n : Nat) :
  solve n (n+1) = 1 → ∀ c, c ∈ (ToString.toString n).data → c ∈ ['0', '1', '8', '6', '9'] :=
sorry

theorem odd_len_middle_digit (n : Nat) (h1 : solve n (n+1) = 1)
  (h2 : (ToString.toString n).length % 2 = 1) :
  let mid := (ToString.toString n).length / 2
  let c := ((ToString.toString n).data.get! mid)
  c ≠ '6' ∧ c ≠ '9' :=
sorry
-- </vc-theorems>