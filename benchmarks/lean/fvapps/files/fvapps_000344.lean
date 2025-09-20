-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numSubseq (nums : List Nat) (target : Nat) : Nat := sorry

def minimum (l : List Nat) : Option Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numSubseq_non_negative (nums : List Nat) (target : Nat) :
  target ≥ 2 →
  nums.length ≥ 1 →
  ∀ x ∈ nums, x ≥ 1 ∧ x ≤ 1000 →
  numSubseq nums target ≥ 0 := sorry

theorem numSubseq_modulo_bound (nums : List Nat) (target : Nat) :
  target ≥ 2 →
  nums.length ≥ 1 →
  ∀ x ∈ nums, x ≥ 1 ∧ x ≤ 1000 →
  numSubseq nums target < 10^9 + 7 := sorry

theorem numSubseq_single_element (x : Nat) :
  x ≥ 1 →
  x ≤ 100 →
  numSubseq [x] (x * 3) = if x * 2 ≤ x * 3 then 1 else 0 := sorry
-- </vc-theorems>