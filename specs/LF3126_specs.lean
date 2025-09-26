-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (k : Nat) : Nat := sorry

theorem solve_k_zero (num_str : String) (h : num_str.all (fun c => '0' <= c ∧ c <= '9')) :
  num_str.length > 0 → solve num_str 0 = num_str.toNat! := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_k_bounds (num_str : String) (k : Nat) 
  (h1 : num_str.all (fun c => '0' <= c ∧ c <= '9'))
  (h2 : num_str.length > 1) :
  let k' := min k (num_str.length - 1)
  let result := solve num_str k'
  toString result |>.length = num_str.length - k' := sorry

theorem solve_returns_largest (num_str : String) (k : Nat)
  (h1 : num_str.all (fun c => '0' <= c ∧ c <= '9'))
  (h2 : num_str.length > 1) :
  let k' := min k (num_str.length - 1)
  let result := solve num_str k'
  let partition_size := num_str.length - k'
  ∀ i, i + partition_size ≤ num_str.length →
    let substr := (num_str.take (i + partition_size)).drop i
    result ≥ substr.toNat! := sorry
-- </vc-theorems>